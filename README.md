# Natural Language Constraint Parser in Prolog

A Definite Clause Grammar (DCG) parser built in Prolog that translates high-level, English-like sentences into Constraint Logic Programming (CLP) restrictions over finite domains.

## Features

* **Natural Language Processing:** Parses textual sentences to define variables and apply strict mathematical boundaries or constraints (e.g., ranges, equalities, inequalities).
* **Context Awareness:** Supports contextual keywords like "it" (referring to the last defined variable) and "all variables" (applying a rule globally to all known variables).
* **Mathematical Operations:** Understands both symbols and textual math operations ("the product of", "plus", "divided by") while respecting standard operator precedence.
* **Automated Analysis:** Evaluates the generated constraints to detect infinite domains, solve finite domains, and output unresolved surviving constraints.

## Prerequisites

* SWI-Prolog must be installed on your machine.
* The `clpfd` (Constraint Logic Programming over Finite Domains) and `lists` libraries, which are included by default in standard SWI-Prolog installations.

## How to Use

1. Clone this repository and open your terminal in the project folder.
2. Launch the interactive SWI-Prolog environment:
   ```bash
   swipl
