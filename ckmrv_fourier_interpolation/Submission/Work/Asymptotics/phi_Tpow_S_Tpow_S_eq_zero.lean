/-
# The vanishing `φ (T^n · S · T^j · S) = 0` for `n = ±1` and odd `j`

`Work.Residues.phi` is the functional `φ(x) = (σ_R x) 0 1` of CKMRV (3.12)
(`Work.Residues.phi_eq_sigmaR`), with `σ_R` the six-dimensional representation of
`R = ℂ[SL(2,ℤ)]` of `Submission/Work/Modular/GroupAlgebra.lean`.  This file computes the
eight cases `n ∈ {1,-1}`, `j ∈ {1,-1,3,-3}` needed for the tile principal-part window: the
value is `0` (in general `φ (T^n S T^j S) = n · [j even]`, so these are exactly the odd cases).

The relevance: for `τ = n +ᵥ w` (`n = ±1`) and the "crossed" orbit point
`ζ = (S T^{-j} S) • w`, the group element `δ = T^n S T^j S` satisfies `δ • ζ = τ`, so
`φ(δ) = 0` gives `KfunClear ℓ d τ ζ = 0` (`Work.Asymptotics.KfunClear_vanish_of_phiPair`),
i.e. `AfunFun ℓ d τ ζ = 0`: the crossed points carry no pole of the kernel.
-/
import Mathlib
import Submission.Work.Residues.Quotient
import Submission.Work.Residues.IdealImDefs
import Submission.Work.Residues.IdealImRowDiffAll
import Submission.Work.Residues.phi_Tpow_mul_inv_eq_zero

noncomputable section

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra

namespace Work.Residues

private lemma single_mul_single_one (a b : SL(2, ℤ)) :
    MonoidAlgebra.single (a * b) (1 : ℂ)
      = MonoidAlgebra.single a (1 : ℂ) * MonoidAlgebra.single b (1 : ℂ) := by
  rw [MonoidAlgebra.single_mul_single, mul_one]

private lemma group_pow_three (a : SL(2, ℤ)) :
    a ^ (3 : ℤ) = a ^ (1 : ℤ) * a ^ (1 : ℤ) * a ^ (1 : ℤ) := by
  rw [show (3 : ℤ) = 1 + 1 + 1 by norm_num, _root_.zpow_add, _root_.zpow_add]

private lemma group_pow_neg_three (a : SL(2, ℤ)) :
    a ^ (-3 : ℤ) = a ^ (-1 : ℤ) * a ^ (-1 : ℤ) * a ^ (-1 : ℤ) := by
  rw [show (-3 : ℤ) = -1 + -1 + -1 by norm_num, _root_.zpow_add, _root_.zpow_add]

theorem phi_Tpow_S_Tpow_S_eq_zero (n j : ℤ) (hn : n = 1 ∨ n = -1)
    (hj : j = 1 ∨ j = -1 ∨ j = 3 ∨ j = -3) :
    Work.Residues.phi
      (MonoidAlgebra.single
        (ModularGroup.T ^ n * ModularGroup.S * ModularGroup.T ^ j * ModularGroup.S) (1 : ℂ)) = 0 := by
  have hsplit : MonoidAlgebra.single
        (ModularGroup.T ^ n * ModularGroup.S * ModularGroup.T ^ j * ModularGroup.S) (1 : ℂ)
      = MonoidAlgebra.single (ModularGroup.T ^ n) (1 : ℂ)
        * MonoidAlgebra.single ModularGroup.S (1 : ℂ)
        * MonoidAlgebra.single (ModularGroup.T ^ j) (1 : ℂ)
        * MonoidAlgebra.single ModularGroup.S (1 : ℂ) := by
    rw [single_mul_single_one, single_mul_single_one, single_mul_single_one]
  rw [hsplit, phi_eq_sigmaR, map_mul, map_mul, map_mul]
  clear hsplit
  have hS : sigmaR (MonoidAlgebra.single ModularGroup.S (1 : ℂ)) = Work.Modular.sigmaS :=
    sigmaR_R_S
  have hone : sigmaR (MonoidAlgebra.single (ModularGroup.T ^ (1 : ℤ)) (1 : ℂ)) =
      Work.Modular.sigmaT := by
    rw [_root_.zpow_one]; exact sigmaR_R_T
  have hneg : sigmaR (MonoidAlgebra.single (ModularGroup.T ^ (-1 : ℤ)) (1 : ℂ)) =
      Work.Modular.sigmaTinv := by
    rw [_root_.zpow_neg_one]; exact sigmaR_single_T_inv
  have hthree : sigmaR (MonoidAlgebra.single (ModularGroup.T ^ (3 : ℤ)) (1 : ℂ))
      = Work.Modular.sigmaT * Work.Modular.sigmaT * Work.Modular.sigmaT := by
    rw [group_pow_three, single_mul_single_one, single_mul_single_one, map_mul, map_mul, hone]
  have hnegthree : sigmaR (MonoidAlgebra.single (ModularGroup.T ^ (-3 : ℤ)) (1 : ℂ))
      = Work.Modular.sigmaTinv * Work.Modular.sigmaTinv * Work.Modular.sigmaTinv := by
    rw [group_pow_neg_three, single_mul_single_one, single_mul_single_one, map_mul, map_mul, hneg]
  rcases hn with hn | hn <;> rcases hj with hj | hj | hj | hj <;>
    subst hn <;> subst hj <;>
    simp only [hone, hneg, hthree, hnegthree, hS] <;>
    simp [Matrix.mul_apply, Fin.sum_univ_six, Work.Modular.sigmaT, Work.Modular.sigmaS,
      Work.Modular.sigmaTinv]

end Work.Residues
