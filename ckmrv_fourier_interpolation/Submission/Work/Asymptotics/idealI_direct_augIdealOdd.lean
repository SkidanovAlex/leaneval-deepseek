/-
# Directness of the odd-weight defect ideal `𝓘_odd = (T-I)²R + S(T-I)²R + (1+z)R`

For **odd** weight `k` the central element `z = -I` acts on functions on `ℍ` by `(-1)^k = -1`,
so the element acting trivially is `1 + z` and the relevant defect ideal is
`𝓘_odd = (T-I)²R + S(T-I)²R + (1+z)R` (`Work.Asymptotics.idealIOdd`), with
`augIdealOdd = (1+z)R` (`Work.Asymptotics.augIdealOdd`).

Proved here is the odd-weight analogue of CKMRV Proposition 3.1: the sum of the two defect
ideals is direct modulo the collapse ideal `(1+z)R`, i.e.

  `(T-I)²A + S(T-I)²B ∈ (1+z)R  →  A ∈ (1+z)R ∧ B ∈ (1+z)R`.

## Proof outline

`R = ℂ[SL(2,ℤ)]`, `z = Rneg = single (-I) 1` is central with `z² = 1`, so `R = R₊ × R₋` with
`R₊ = (1+z)R`, `R₋ = (1-z)R`, `e± = 2⁻¹(1 ± z)`.  Multiplication by `z` preserves both factors,
`A ∈ R₊ ⟺ A z = A` (`augIdealOdd_mem_iff`) and `A ∈ R₋ ⟺ A z = -A` (computed in this file).

* The hypothesis `C ∈ R₊` is `C z = C`, i.e. `(1-z) C = 0`, which rewrites to
  `(T-1)² A' + S (T-1)² B' = 0` with `A' = (1-z)A ∈ R₋`, `B' = (1-z)B ∈ R₋`.
* The directness statement on `R₋` is transported (`Work.Asymptotics.oddDirect_of_shiftedDirect`)
  from the shifted free-product directness statement in `RR = ℂ[ℤ/2∗ℤ/3]`
  (`Work.FreeProduct.shifted_direct`, proved from `shifted_orbit_corollary`,
  `shifted_core_plus`, `shifted_core_minus` and `Tnu_mul_eq_zero`).
* `(1-z)A = 0` is equivalent to `A ∈ R₊ = (1+z)R`.
-/
import Mathlib
import Submission.Work.Asymptotics.OddIdeal
import Submission.Work.Asymptotics.augIdealOddMem
import Submission.Work.Asymptotics.oddDirect_of_shiftedDirect
import Submission.Work.Residues.idealI_direct_augIdeal
import Submission.Work.FreeProduct.idealI_direct
import Submission.Work.FreeProduct.IdealImDirect
import Submission.Work.FreeProduct.claim_L3
import Submission.Work.FreeProduct.Tools
import Submission.Work.FreeProduct.Length
import Submission.Work.FreeProduct.LengthFacts
import Submission.Work.FreeProduct.Basic
import Submission.Work.Modular.presentedGroup_equiv_PSL
import Submission.Work.FreeProduct.shiftedDefs
import Submission.Work.FreeProduct.shifted_orbit_corollary
import Submission.Work.FreeProduct.shifted_core_plus
import Submission.Work.FreeProduct.shifted_core_minus
import Submission.Work.FreeProduct.Tnu_mul_eq_zero
import Submission.Work.FreeProduct.shifted_direct

noncomputable section

namespace Work.Asymptotics

open Work.Kernels
open Work.FreeProduct (RR X Tnu)

/-- The shifted free-product directness statement, deduced from `Work.FreeProduct.shifted_direct`
(available for `ν ≠ 0` with `1 ± ν³ ≠ 0`). -/
lemma shifted_direct' {ν : ℂ} (hν : ν ≠ 0) (h1 : ν ^ 3 ≠ 1) (hm : ν ^ 3 ≠ -1)
    {a b : RR}
    (h : Tnu ν ^ 2 * a + X * Tnu ν ^ 2 * b = 0) : a = 0 ∧ b = 0 := by
  refine Work.FreeProduct.shifted_direct hν ?_ ?_ h
  · intro hc
    exact hm (by linear_combination hc)
  · intro hc
    exact h1 (sub_eq_zero.mp hc).symm

/-- **The odd-weight directness of `𝓘_odd`.**  The sum `(T-I)²R + S(T-I)²R` is direct modulo the
collapse ideal `(1+z)R`, `z = -I`: the only way for `(T-I)²A + S(T-I)²B` to lie in `(1+z)R` is
`A, B ∈ (1+z)R`. -/
theorem idealI_direct_augIdealOdd {A B : Work.Kernels.R}
    (h : (Work.Kernels.R_T - 1) ^ 2 * A + Work.Kernels.R_S * (Work.Kernels.R_T - 1) ^ 2 * B
      ∈ Work.Asymptotics.augIdealOdd) :
    A ∈ Work.Asymptotics.augIdealOdd ∧ B ∈ Work.Asymptotics.augIdealOdd := by
  have hRR : ∀ {ν : ℂ}, ν ≠ 0 → ν ^ 3 ≠ 1 → ν ^ 3 ≠ -1 →
      ∀ a b : RR, Tnu ν ^ 2 * a + X * Tnu ν ^ 2 * b = 0 → a = 0 ∧ b = 0 :=
    fun hν h1 hm a b hab => shifted_direct' hν h1 hm hab
  have hodd := oddDirect_of_shiftedDirect hRR
  -- `C ∈ R₊` gives `C * Rneg = C`, hence `(1 - Rneg) * C = 0`
  set C : R := (R_T - 1) ^ 2 * A + R_S * (R_T - 1) ^ 2 * B with hCdef
  have hC : C * Rneg = C := augIdealOdd_mem_iff.mp (hCdef ▸ h)
  have h0 : (1 - Rneg) * C = 0 := by
    rw [sub_mul, one_mul, Rneg_comm' C, hC, sub_self]
  have hcomm1 : (1 - Rneg) * (R_T - 1) ^ 2 = (R_T - 1) ^ 2 * (1 - Rneg) := by
    rw [sub_mul, one_mul]
    congr 1
    rw [mul_sub, mul_one, Rneg_comm' ((R_T - 1) ^ 2)]
  have hcomm2 : (1 - Rneg) * R_S = R_S * (1 - Rneg) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, Rneg_comm' R_S]
  have hEq : (R_T - 1) ^ 2 * ((1 - Rneg) * A)
      + R_S * (R_T - 1) ^ 2 * ((1 - Rneg) * B) = 0 := by
    have h' : (1 - Rneg) * ((R_T - 1) ^ 2 * A + R_S * (R_T - 1) ^ 2 * B) = 0 := hCdef ▸ h0
    have h1 : (1 - Rneg) * ((R_T - 1) ^ 2 * A) = (R_T - 1) ^ 2 * ((1 - Rneg) * A) := by
      rw [← mul_assoc, hcomm1, mul_assoc]
    have h2 : (1 - Rneg) * (R_S * (R_T - 1) ^ 2 * B)
        = R_S * (R_T - 1) ^ 2 * ((1 - Rneg) * B) := by
      calc (1 - Rneg) * (R_S * (R_T - 1) ^ 2 * B)
          = ((1 - Rneg) * R_S) * ((R_T - 1) ^ 2 * B) := by noncomm_ring
        _ = (R_S * (1 - Rneg)) * ((R_T - 1) ^ 2 * B) := by rw [hcomm2]
        _ = R_S * ((1 - Rneg) * ((R_T - 1) ^ 2 * B)) := by noncomm_ring
        _ = R_S * (((1 - Rneg) * (R_T - 1) ^ 2) * B) := by noncomm_ring
        _ = R_S * (((R_T - 1) ^ 2 * (1 - Rneg)) * B) := by rw [hcomm1]
        _ = R_S * ((R_T - 1) ^ 2 * ((1 - Rneg) * B)) := by noncomm_ring
        _ = R_S * (R_T - 1) ^ 2 * ((1 - Rneg) * B) := by noncomm_ring
    rw [mul_add, h1, h2] at h'
    exact h'
  have hA' : ((1 - Rneg) * A) * Rneg = -((1 - Rneg) * A) := by
    rw [mul_assoc, ← Rneg_comm' A, ← mul_assoc, Rneg_sub_mul_self, neg_mul]
  have hB' : ((1 - Rneg) * B) * Rneg = -((1 - Rneg) * B) := by
    rw [mul_assoc, ← Rneg_comm' B, ← mul_assoc, Rneg_sub_mul_self, neg_mul]
  obtain ⟨hA0, hB0⟩ := hodd ((1 - Rneg) * A) ((1 - Rneg) * B) hA' hB' hEq
  have key : ∀ Y : R, (1 - Rneg) * Y = 0 → Y * Rneg = Y := by
    intro Y hY
    rw [sub_mul, one_mul, sub_eq_zero] at hY
    rw [← Rneg_comm' Y]
    exact hY.symm
  exact ⟨augIdealOdd_mem_iff.mpr (key A hA0), augIdealOdd_mem_iff.mpr (key B hB0)⟩

end Work.Asymptotics
