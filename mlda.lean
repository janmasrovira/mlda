import mlda.Base
import mlda.Section2
import mlda.Section3
import mlda.Section4
import mlda.Section5

/-!
# Modal Logic for Declarative Distributed Algorithms

A full Lean 4 formalisation of the paper *"Declarative distributed algorithms
as axiomatic theories in three-valued modal logic over semitopologies"* by Murdoch J. Gabbay.

## Overview

- **Section 2** (`mlda.Section2`): Three-valued logic (`𝟯`) with connectives and
  predicates. Finite semitopologies with modal operators `□` (everywhere), `◇`
  (somewhere), `⊡` (quorum), `⟐` (contraquorum). Quorum properties including the
  twined semitopology condition.
- **Section 3** (`mlda.Section3`): Expression syntax, semantic models, and three-valued denotation.
- **Section 4** (`mlda.Section4`): Bracha Broadcast specification and
  correctness proofs.
- **Section 5** (`mlda.Section5`): Crusader Agreement specification and
  correctness proofs.
-/
