# blockchain_server.py
# Modified blockchain node to support "certificate" transactions and verification endpoints.

from flask import Flask, request, jsonify, render_template
from time import time
from flask_cors import CORS
from collections import OrderedDict
import binascii
import Crypto
from Crypto.PublicKey import RSA
from Crypto.Signature import PKCS1_v1_5
from Crypto.Hash import SHA
from uuid import uuid4
import json
import hashlib
import requests
from urllib.parse import urlparse

MINING_SENDER = "The Blockchain"
MINING_REWARD = 1
MINING_DIFFICULTY = 2


def normalize_transaction(tx):
    """
    Return an OrderedDict with keys sorted so JSON/hashing is deterministic.
    Works for any transaction shape (regular payment OR certificate).
    """
    # If tx is already OrderedDict, ensure sorted keys
    return OrderedDict(sorted(tx.items(), key=lambda t: t[0]))


class Blockchain:

    def __init__(self):
        self.transactions = []
        self.chain = []
        self.nodes = set()
        self.node_id = str(uuid4()).replace('-', '')
        # Create the genesis block
        self.create_block(0, '00')

    def register_node(self, node_url):
        parsed_url = urlparse(node_url)
        if parsed_url.netloc:
            self.nodes.add(parsed_url.netloc)
        elif parsed_url.path:
            self.nodes.add(parsed_url.path)
        else:
            raise ValueError('Invalid URL')

    def create_block(self, nonce, previous_hash):
        """
        Add a block of transactions to the blockchain
        """
        block = {'block_number': len(self.chain) + 1,
                 'timestamp': time(),
                 'transactions': self.transactions,
                 'nonce': nonce,
                 'previous_hash': previous_hash}

        # Reset the current list of transactions
        self.transactions = []
        self.chain.append(block)
        return block

    def verify_transaction_signature(self, sender_public_key, signature, transaction):
        """
        Verify signature for a transaction (transaction is a dict).
        The transaction is normalized (ordered) before hashing.
        If sender_public_key == MINING_SENDER, no signature required.
        """
        if sender_public_key == MINING_SENDER:
            return True  # system-supplied

        try:
            public_key = RSA.importKey(binascii.unhexlify(sender_public_key))
        except (TypeError, binascii.Error, ValueError):
            return False

        verifier = PKCS1_v1_5.new(public_key)
        # normalize transaction for deterministic hashing
        normalized = normalize_transaction(transaction)
        h = SHA.new(json.dumps(normalized, sort_keys=False).encode('utf8'))
        try:
            verifier.verify(h, binascii.unhexlify(signature))
            return True
        except (ValueError, TypeError, binascii.Error):
            return False

    @staticmethod
    def valid_proof(transactions, last_hash, nonce, difficulty=MINING_DIFFICULTY):
        """
        Create a deterministic serialization of transactions, last_hash and nonce
        and check whether hash has `difficulty` leading zeros.
        """
        # Normalize transactions list: each tx -> OrderedDict sorted by key
        normalized = [normalize_transaction(tx) for tx in transactions]
        guess = (json.dumps(normalized, sort_keys=True) + str(last_hash) + str(nonce)).encode('utf8')
        h = hashlib.new('sha256')
        h.update(guess)
        guess_hash = h.hexdigest()
        return guess_hash[:difficulty] == '0' * difficulty

    def proof_of_work(self):
        last_block = self.chain[-1]
        last_hash = self.hash(last_block)
        nonce = 0
        while self.valid_proof(self.transactions, last_hash, nonce) is False:
            nonce += 1

        return nonce

    @staticmethod
    def hash(block):
        # We must ensure that the Dictionary is ordered, otherwise we'll get inconsistent hashes
        block_string = json.dumps(block, sort_keys=True).encode('utf8')
        h = hashlib.new('sha256')
        h.update(block_string)
        return h.hexdigest()

    def resolve_conflicts(self):
        neighbours = self.nodes
        new_chain = None

        max_length = len(self.chain)
        for node in neighbours:
            response = requests.get('http://' + node + '/chain')
            if response.status_code == 200:
                length = response.json()['length']
                chain = response.json()['chain']

                if length > max_length and self.valid_chain(chain):
                    max_length = length
                    new_chain = chain

        if new_chain:
            self.chain = new_chain
            return True

        return False

    def valid_chain(self, chain):
        """
        Validate a chain. Uses the same normalization as above.
        Note: This only checks the integrity/hashing/PoW. It does not re-verify
        every signature (because signatures are not stored alongside transactions
        in this simple design). This matches the original project behavior.
        """
        last_block = chain[0]
        current_index = 1

        while current_index < len(chain):
            block = chain[current_index]
            # check previous hash
            if block['previous_hash'] != self.hash(last_block):
                return False

            # take all transactions except the mining reward at the end (common pattern)
            transactions = block['transactions'][:]  # copy
            # If you assume last transaction is mining reward, you can skip for TX signature checks; keep it here for proof hashing consistency.

            if not self.valid_proof(transactions, block['previous_hash'], block['nonce'], MINING_DIFFICULTY):
                return False

            last_block = block
            current_index += 1

        return True

    def submit_transaction(self, transaction, signature, sender_public_key=None):
        """
        Accept a transaction (arbitrary dict). If transaction is a mining reward (sender_public_key==MINING_SENDER),
        accept without signature. Otherwise verify signature using sender_public_key (or issuer_public_key for certificate).
        Returns the block number the tx will be added to.
        """
        # Determine which public key to check for signature depending on transaction type
        if isinstance(transaction, dict) is False:
            return False

        # Mining reward
        if sender_public_key == MINING_SENDER:
            self.transactions.append(transaction)
            return len(self.chain) + 1
        else:
            # choose key to verify: prefer explicit 'sender_public_key', then 'issuer_public_key' (certificate case), else provided sender_public_key
            key_to_check = transaction.get('sender_public_key') or transaction.get('issuer_public_key') or sender_public_key

            if key_to_check is None:
                return False

            signature_verification = self.verify_transaction_signature(key_to_check, signature, transaction)
            if signature_verification:
                self.transactions.append(transaction)
                return len(self.chain) + 1
            else:
                return False

    def find_certificate(self, certificate_hash=None, student_id=None, degree=None, year=None):
        """
        Search the chain for certificate transactions matching given attributes.
        Returns list of matching transactions with block_number and timestamp.
        """
        results = []
        for block in self.chain:
            for tx in block['transactions']:
                if tx.get('type') != 'certificate':
                    continue
                match = True
                if certificate_hash and tx.get('certificate_hash') != certificate_hash:
                    match = False
                if student_id and tx.get('student_id') != student_id:
                    match = False
                if degree and tx.get('degree') != degree:
                    match = False
                if year and tx.get('year') != year:
                    match = False
                if match:
                    item = tx.copy()
                    item['_block_number'] = block['block_number']
                    item['_timestamp'] = block['timestamp']
                    results.append(item)
        return results


# Instantiate the Blockchain
blockchain = Blockchain()

# Instantiate the Node
app = Flask(__name__)
CORS(app)


@app.route('/')
def index():
    return render_template('./index.html')


@app.route('/configure')
def configure():
    return render_template('./configure.html')


@app.route('/transactions/get', methods=['GET'])
def get_transactions():
    transactions = blockchain.transactions
    response = {'transactions': transactions}
    return jsonify(response), 200


@app.route('/chain', methods=['GET'])
def get_chain():
    response = {
        'chain': blockchain.chain,
        'length': len(blockchain.chain)
    }

    return jsonify(response), 200


@app.route('/mine', methods=['GET'])
def mine():
    # We run the proof of work algorithm
    nonce = blockchain.proof_of_work()

    # Reward the miner
    blockchain.submit_transaction({'sender_public_key': MINING_SENDER,
                                   'recipient_public_key': blockchain.node_id,
                                   'amount': MINING_REWARD,
                                   'type': 'reward'},
                                  signature='',
                                  sender_public_key=MINING_SENDER)

    last_block = blockchain.chain[-1]
    previous_hash = blockchain.hash(last_block)
    block = blockchain.create_block(nonce, previous_hash)

    response = {
        'message': 'New block created',
        'block_number': block['block_number'],
        'transactions': block['transactions'],
        'nonce': block['nonce'],
        'previous_hash': block['previous_hash'],
    }
    return jsonify(response), 200


@app.route('/transactions/new', methods=['POST'])
def new_transaction():
    # expects form fields for a normal transaction (sender_public_key, recipient_public_key, amount, signature)
    values = request.form
    required = ['sender_public_key', 'recipient_public_key', 'transaction_signature', 'amount']
    if not all(k in values for k in required):
        return 'Missing values', 400

    transaction = {
        'sender_public_key': values['sender_public_key'],
        'recipient_public_key': values['recipient_public_key'],
        'amount': values['amount'],
        'type': 'transfer'
    }

    transaction_results = blockchain.submit_transaction(transaction,
                                                        values['transaction_signature'],
                                                        sender_public_key=values['sender_public_key'])
    if transaction_results == False:
        response = {'message': 'Invalid transaction/signature'}
        return jsonify(response), 406
    else:
        response = {'message': 'Transaction will be added to the Block ' + str(transaction_results)}
        return jsonify(response), 201


@app.route('/certificates/new', methods=['POST'])
def new_certificate():
    """
    Submit a certificate record to the chain.
    Expected form fields:
      - student_name
      - student_id
      - degree
      - year
      - university
      - issuer_public_key
      - signature  (signature by issuer_private_key over the transaction dict)
      - certificate_hash  (sha256 of the certificate PDF or data)
    """
    values = request.form
    required = ['student_name', 'student_id', 'degree', 'year', 'university', 'issuer_public_key', 'signature',
                'certificate_hash']
    if not all(k in values for k in required):
        return 'Missing values', 400

    transaction = {
        'type': 'certificate',
        'student_name': values['student_name'],
        'student_id': values['student_id'],
        'degree': values['degree'],
        'year': values['year'],
        'university': values['university'],
        'issuer_public_key': values['issuer_public_key'],
        'certificate_hash': values['certificate_hash']
    }

    result = blockchain.submit_transaction(transaction, values['signature'], sender_public_key=values['issuer_public_key'])
    if result == False:
        return jsonify({'message': 'Invalid certificate signature or data'}), 406
    else:
        return jsonify({'message': 'Certificate transaction will be added to Block ' + str(result)}), 201


@app.route('/certificates/verify', methods=['GET'])
def verify_certificate():
    """
    Verify certificate on chain. Query parameters:
      - certificate_hash (preferred)
    Or:
      - student_id, degree, year  (alternative)
    """
    certificate_hash = request.args.get('certificate_hash')
    student_id = request.args.get('student_id')
    degree = request.args.get('degree')
    year = request.args.get('year')

    if not (certificate_hash or (student_id and degree and year)):
        return 'Provide certificate_hash or (student_id & degree & year)', 400

    matches = blockchain.find_certificate(certificate_hash=certificate_hash, student_id=student_id, degree=degree,
                                          year=year)
    if matches:
        return jsonify({'valid': True, 'matches': matches}), 200
    else:
        return jsonify({'valid': False, 'matches': []}), 200


@app.route('/nodes/get', methods=['GET'])
def get_nodes():
    nodes = list(blockchain.nodes)
    response = {'nodes': nodes}
    return jsonify(response), 200


@app.route('/nodes/resolve', methods=['GET'])
def consensus():
    replaced = blockchain.resolve_conflicts()

    if replaced:
        response = {
            'message': 'Our chain was replaced',
            'new_chain': blockchain.chain
        }
    else:
        response = {
            'message': 'Our chain is authoritative',
            'chain': blockchain.chain
        }
    return jsonify(response), 200


@app.route('/nodes/register', methods=['POST'])
def register_node():
    values = request.form
    # 127.0.0.1:5002,127.0.0.1:5003,127.0.0.1:5004
    nodes = values.get('nodes')
    if not nodes:
        return 'Error: Please supply a valid list of nodes', 400

    nodes = nodes.replace(' ', '').split(',')

    for node in nodes:
        blockchain.register_node(node)

    response = {
        'message': 'Nodes have been added',
        'total_nodes': [node for node in blockchain.nodes]
    }
    return jsonify(response), 200


if __name__ == '__main__':
    from argparse import ArgumentParser

    parser = ArgumentParser()
    parser.add_argument('-p', '--port', default=5001, type=int, help="port to listen to")
    args = parser.parse_args()
    port = args.port

    app.run(host='127.0.0.1', port=port, debug=True)
