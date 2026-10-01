import Mathlib
import Submission.Work.LinnikAreas.CorrAllR.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.primitive_factor_coprime
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_moment_squarefree_r2
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation_global_sharp_aux
import Submission.Commons.NumberTheory.DirichletCharacter.weil_local_bound
import Submission.Commons.Algebra.Polynomial.mult_modEq_of_const_mul_pow

/-!
# `Prelude` — shared imports for the general-`r` correlation development

This module exists so that lemmas about the general-`r` correlation sum
(`Work.LinnikAreas.corrSumV`, defined in `Submission.Work.LinnikAreas.CorrAllR.Defs`) can be
stated with the Chinese-remainder vocabulary (`factorLeft`, `factorRight`, `chi_eq_factors`),
the arithmetic splitting lemmas (`gcd_mul_gcd_of_coprime`, `card_primeFactors_mul_of_coprime`,
`exists_coprime_factorization`) and the local Weil bound (`weil_local_bound`) in scope, by
importing this module.

It contains no declarations.
-/
