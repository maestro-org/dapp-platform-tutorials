from flask import Flask, request, json
app = Flask(__name__)

@app.route('/maestro-monitor', methods=['POST'])
def return_response():
    resp = app.response_class(
        response=json.dumps({"testing": "123"}),
        status=200,
        mimetype='application/json'
    )
    return resp

if __name__ == "__main__": app.run()
