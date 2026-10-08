import Submission.OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible
import Submission.OddOrder.GroupTheory.RepresentationTheory.CyclotomicCharacterCongruence
import Submission.OddOrder.GroupTheory.RepresentationTheory.LinearCharacter

/-!
# Area BG: character-theory imports of the FT closure

Aggregator module.  Every §1 claim of Bender–Glauberman 1981 is proved on top of the
character library of the Feit–Thompson closure (`Submission/OddOrder/**`, Apache-2.0,
third-party, not edited).  This module exposes that library to area `BG` in one import,
so that statements written in area `BG` can name it through a single local path.

Available here (selection; see the individual modules for the full API):

* `OddOrder.RepresentationTheory.ClassFunction` — class functions, restriction
  (`restrict`), induction (`ClassFunction.induce`), the inner product
  (`ClassFunction.inner`), conjugation (`ClassFunction.conjBy`), supports,
  `ClassFunction.supportedSubmodule`;
* `ClassFunction.inner_induce_eq_inner_restrict` — Frobenius reciprocity;
* `ClassFunction.inner_induce_eq_of_isTISubset`,
  `ClassFunction.induce_apply_coe_of_isTISubset` — the Brauer–Suzuki TI isometry
  (BG Lemma 1.3);
* `ClassFunction.card_smul_restrict_induce` — Mackey restriction (normal subgroup);
* `OddOrder.RepresentationTheory.IsIrreducibleCharacter`, `irreducibleCharacters`,
  `ZIrr`, `IrreducibleCharacter` — `Irr(G)` and `ℤ[Irr G]`;
* `irreducibleCharacter_inner_eq_ite` — orthonormality of `Irr(G)`;
* `mem_ZIrr_inner_self_eq_sum_sq`, `mem_ZIrr_repr`, `inner_eq_coeff_of_repr` — Fourier
  coefficients of a virtual character;
* `exists_irr_sub_irr_of_inner_self_two` — the norm-2 structure lemma;
* `isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos` — norm-one irreducibility
  criterion;
* `ClassFunction.induce_mem_ZIrr`, `ClassFunction.restrict_mem_ZIrr`;
* `IsIrreducibleCharacter.exists_linearIrreducibleCharacter_eq_of_isMulCommutative` —
  irreducibles of a commutative group are linear characters (used for Lemma 1.6);
* `OddOrder.RepresentationTheory.character_isIntegral` and the cyclotomic-integrality
  API of `ClassSumAlgebra` / `CyclotomicCharacterCongruence`.
-/
