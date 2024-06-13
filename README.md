This repo provides dataset, code, and documentations for the paper 
"Towards General Loop Invariant Generation: A Benchmark of Programs with Memory Manipulation", 
which is submitted to the thirty-eight conference on neural information processing systems (NeurIPS 2024) datasets and benchmarks track.

## Benchmark Dataset LIG-MM
The benchmark dataset proposed in our paper is under the `dataset` folder.

---

As we mentioned before, the benchmark programs in existing papers mostly contain numerical programs. To fill the lack of benchmarks for general loop invariant generation, we propose LIG-MM, a loop invariant generation benchmark of memory manipulation programs. Table 1 below shows the basics of the code in LIG-MM. Our programs come from four main sources: course codes, competition codes, previous relevant work, and actual system codes. The programs are modified into a unified format for better usage. Multiple examples, license of datasets and maintenance plans can be found in the supplementary materials.

- **Course codes.** The course code is mainly derived from homework programs on the data structure course and programming language course. The detailed course number and college name are covered due to the anonymity of this paper. These programs contain the most diverse data structures and multi-level pointer operations among the sources of our benchmark.
- **Competition codes.** SV-COMP is a competition on software verification, which provides a benchmark for verification tasks for comparing verification tools. Originating from competition, this dataset encompasses various verification tasks, providing a comprehensive set of real-world and synthetic examples for testing the effectiveness and efficiency of verification techniques. In our LIG-MM, we select programs from the 2022 competition benchmark.
- **Previous relevant work.** SLING uses traditional dynamic analysis techniques to generate invariants. Other than loop invariants, SLING can also generate preconditions and post-conditions for functions. Therefore, not all their benchmarks include the inference of loop invariant or even contain a loop (they use function calls to replace loops). After selection, we choose some of the programs in its benchmark and turn them into a uniform code style.
- **Real-world system codes.** To make the data in LIG-MM closer to real-world software environments, we decide to select more programs from several well-known software and systems. Among them, GlibC is the GNU implementation of the C standard library, providing essential functionalities for numerous applications. Additionally, we have incorporated programs from the Linux Kernel, a widely used and highly-regarded operating system kernel that serves as the foundation for countless devices and systems worldwide. To further enhance the diversity of our dataset, we have included LiteOS, a lightweight operating system designed for IoT devices, and Zephyr, another versatile operating system known for its applicability in resource-constrained environments.

---

**Table 1: Statistics of our proposed LIG-MM benchmark.**

|                     | Concrete Resources               | Number of Programs | Data Structure Types     |
|---------------------|----------------------------------|---------------------|--------------------------|
| Course codes        | Course homework programs         | 187                 | sll, dll, tree, hash-table |
| Competition codes   | SV-COMP                          | 27                  | sll, dll, tree, hash-table |
| Previous benchmark  | SLING                            | 15                  | sll, dll, tree           |
| Real-world programs | Linux Kernel                     | 23                  | sll, dll, hash-table     |
| Real-world programs | GlibC                            | 13                  | dll, hash-table          |
| Real-world programs | LiteOS                           | 12                  | dll                      |
| Real-world programs | Zephyr                           | 35                  | sll, dll, hash-table     |
| **Overall**         | -                                | **312**             | **sll, dll, tree, hash-table** |

---

By integrating these varied sources, LIG-MM captures a broad spectrum of programming practices and challenges and ensures that our benchmark is robust and representative of the complexities encountered in multiple scenarios, such as real-world software development and verification. Unlike the numerical program benchmark in previous works, our benchmark does not contain pure numerical procedures, all of our programs are related to at least one certain data structure. The data structures we have selected include singly linked lists(sll), doubly linked lists(dll), trees, and hash-tables. In addition, our benchmark includes the usage of multi-level pointers and various pointer arithmetic. 

## Source Code of LLM-SE Framework
The source code of the proposed LLM-SE framework is under the `src` folder.

### Installation

- Environment (tested on)
  - numpy==1.21.6
  - requests==2.31.0
  - scipy==1.7.3
  - torch==1.13.1+cu117
  - torchvision==0.14.1+cu117
  - torchaudio==0.13.1
  - transformers==4.30.2
  - pandas==1.3.5
  - datasets==2.13.1
  - evaluate==0.4.0
  - z3-solver==4.12.2.0
  - wandb==0.15.8

### Test an Example

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

The model after fine-tuned can be downloaded from [here](https://mega.nz/file/M9FEWCjD#QkAQLu7UERPk4Xgb-Rer4U7lfKy7P3rdQeY_p-b8nhM).

