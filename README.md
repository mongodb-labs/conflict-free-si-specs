# Specifying Snapshot Isolation

This repository contains TLA+ specifications for snapshot isolation along with analysis tools for processing model checker outputs and visualizing transaction conflict graphs. These specs were originally developed to explore ideas around alternate snapshot isolation definitions that are based around prevention of G-nonadjacent cycles, a special case of G2 anomalies that generalize SI beyond classic write-write conflict based implementations.

You can interactively explore a model of the spec [here](https://will62794.github.io/spectacle/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fmongodb-labs%2Fconflict-free-si-specs%2Frefs%2Fheads%2Fmain%2FSnapshotIsolation.tla&constants%5BtxnIds%5D=%7Bt1%2Ct2%2Ct3%2Ct4%7D&constants%5Bkeys%5D=%7Bk1%2Ck2%7D&constants%5Bvalues%5D=%7Bv1%2Cv2%7D&constants%5BEmpty%5D=Empty) (4 transactions).

To check a model and generate a visualization of the counterexample and its serialization graph, you can run the `check.sh` script, which will output a visualization into the `ccgraph.png` file.