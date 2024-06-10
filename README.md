This repo provides dataset, code, and documentations for the paper 
"Towards General Loop Invariant Generation: A Benchmark of Programs with Memory Manipulation", 
which is submitted to the thirty-eight conference on neural information processing systems (NeurIPS 2024) datasets and benchmarks track.

## Benchmark Dataset
The benchmark dataset proposed in our paper is under the `dataset` folder.

## Source Code
The source code of the proposed LLM-SE framework is under the `src` folder.

## Test an Example

```bash
cd src
python invgen.py
```
We can find the log file in this directory: `/log/<example_path>/log.log`

The `invgen.py` script accepts the following arguments:

```bash
optional arguments:
  -h, --help            show this help message and exit
  --path                the path of the example
  --epochs              the number of training epochs
  --size                data size
  --op                  the name of model
  --log_method          method of logging
```

For example, you can run the following command:

```bash
python invgen.py --path Course/list/0data0/append --log_method time
```

We can find the log file in this directory: `/log/Course/list/0data0/append/<time>.log`.