"""
    Quick generation of contracts: as fast validation

    This script allows for quickly generating the code contracts for a Java method
    that you paste as input to the source code of this script.
"""

from transformers import AutoTokenizer, AutoModelForSeq2SeqLM


def generateContractsFromModel(input, modelName, tokenizerModelName):
    text = input
    mname = modelName
    tokenizer = AutoTokenizer.from_pretrained(tokenizerModelName)
    model = AutoModelForSeq2SeqLM.from_pretrained(mname)
    input_ids = tokenizer.encode(text=text, return_tensors="pt")
    outputs = model.generate(input_ids, max_length=256)
    decoded = tokenizer.decode(outputs[0], skip_special_tokens=True)
    return decoded


myInput = """public static void main(String[] args) {
        System.out.println("Hello, World!"); 
    }"""
print(
    generateContractsFromModel(
        input=myInput,
        modelName="saved_models/codet5p-contracts/checkpoint-1890",
        tokenizerModelName="Salesforce/codet5p-220m",
    )
)
