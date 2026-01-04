# LISA-CoC: Calculus of Constructions in Set Theory

[![Scala](https://img.shields.io/badge/scala-3.x-red.svg)](https://www.scala-lang.org/)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](LICENSE)

**LISA-CoC** is a module within the [LISA Proof Assistant](https://github.com/lisa-proof-assistant/lisa) framework. It implements a **Dependent Type Theory** (specifically the Calculus of Constructions with Universes) embedded within **First-Order Logic and Set Theory** (ZFC/Tarski-Grothendieck).

This project aims to bridge the gap between type-theoretic proof assistants (like Coq/Lean) and set-theoretic foundations (like Isabelle/ZF, Mizar) by providing a rigorous translation and verification pipeline.

## 🚀 Key Features

* **Set-Theoretic Semantics**: Formally models $\lambda$-terms, $\Pi$-types, and Universes as sets within the Tarski-Grothendieck hierarchy.
* **Bidirectional Type Checking**: Implements a robust type checker that alternates between *inference* and *checking* modes to handle dependent types.
* **Universe Polymorphism**: Supports a hierarchy of universes ($Type_0 \in Type_1 \in \dots$) validated by set-theoretic containment ($U_0 \in U_1 \in \dots$).
* **Proof Reconstruction**: Automatically generates LISA kernel proofs (in FOL/Set Theory) for valid type-theoretic judgments.

## 🛠 Prerequisites

To run this project, you need:

* **Java Development Kit (JDK)**: Version 17 or higher.
* **sbt**: The Scala Build Tool.

## 🏃‍♂️ Quick Start

To run the examples and verify the implementation:

1.  Start the sbt shell:
    ```bash
    sbt
    ```

2.  Switch to the `lisa-coc` project:
    ```bash
    project lisa-coc
    ```

3.  Run the main application (executes the examples defined in `Main`):
    ```bash
    run
    ```