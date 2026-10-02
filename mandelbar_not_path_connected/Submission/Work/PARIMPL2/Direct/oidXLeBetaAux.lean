import Mathlib
import Submission.Work.PARIMPL2.Direct.oidAux
import Submission.Work.PARIMPL2.Direct.orbitCrossBound
import Submission.Work.PARIMPL2.Direct.oidDefs
import Submission.Work.PARIMPL2.Direct.oidcnHelpers
import Submission.Work.PARIMPL2.Direct.oidCfSign

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

open Finset

/-! ## Auxiliary sign/product facts for the `S_n ≥ 0` crossing bound

These are the elementary facts shared by `oidXLeBeta` and its two correction-term
lemmas `oidXLeBeta_Pbnd` / `oidXLeBeta_Qbnd`.  They are placed in this module so that
the correction-term lemmas do not need to import `oidXLeBeta` itself. -/

/-- On the negative arc `j < j0` (where `λ x j > π/2`) the drift term `ocA` is `≤ 0`. -/
theorem oidXLeBeta_ocA_nonpos (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) (n : ℕ) (x y : ℕ → ℝ)
    (hx2 : ∀ j ≤ n, x j ≤ Real.pi / lam - R / 4)
    (hDpos : ∀ j ≤ n, 0 < ocDen lam x y j)
    (j0 : ℕ) (hj0 : j0 ≤ n) (hneg : ∀ j < j0, Real.pi / 2 < lam * x j)
    (j : ℕ) (hj : j < j0) :
    ocA lam x y j ≤ 0 := by
  have hjn : j ≤ n := le_trans (le_of_lt hj) hj0
  have htx : lam * x j < Real.pi := by
    have h1 := mul_le_mul_of_nonneg_left (hx2 j hjn) hlam.le
    have he : lam * (Real.pi / lam - R / 4) = Real.pi - lam * R / 4 := by field_simp
    rw [he] at h1
    have h2 : 0 < lam * R / 4 := by positivity
    linarith
  have hs : 0 < Real.sin (lam * x j) := Real.sin_pos_of_pos_of_lt_pi (by
      have := hneg j hj; linarith [Real.pi_pos, hlam]) (by linarith)
  have hcos : Real.cos (lam * x j) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (hneg j hj) (by linarith [htx, Real.pi_pos])
  rw [ocA]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hlam.le hs.le) hcos.le) (hDpos j hjn).le

/-- `1 + oidCf i ∈ [0,1]` for `i < n`. -/
theorem oidXLeBeta_one_add_mem (lam cr : ℝ) (hlam : 0 < lam) (hcr : cr ≤ 0)
    (n : ℕ) (x y : ℕ → ℝ)
    (hCabs : ∀ i < n, |oidCf lam cr x y i| ≤ 1)
    (hCn : ∀ i < n, oidCf lam cr x y i ≤ 0) :
    ∀ i < n, 0 ≤ 1 + oidCf lam cr x y i ∧ 1 + oidCf lam cr x y i ≤ 1 := by
  intro i hi
  have h1 := (abs_le.mp (hCabs i hi)).1
  have h2 := hCn i hi
  exact ⟨by linarith, by linarith⟩

/-- A product of the factors `1 + oidCf i` over `Ico (j0+1) n` is `≤ 1`. -/
theorem oidXLeBeta_prod_le_one (lam cr : ℝ) (hlam : 0 < lam) (hcr : cr ≤ 0)
    (n j0 : ℕ) (x y : ℕ → ℝ)
    (hCabs : ∀ i < n, |oidCf lam cr x y i| ≤ 1)
    (hCn : ∀ i < n, oidCf lam cr x y i ≤ 0) :
    (∏ i ∈ Finset.Ico (j0 + 1) n, (1 + oidCf lam cr x y i)) ≤ 1 := by
  refine oidcn_prod_le_one _ _ ?_ ?_
  · intro i hi
    exact (oidXLeBeta_one_add_mem lam cr hlam hcr n x y hCabs hCn i
      (Finset.mem_Ico.mp hi).2).1
  · intro i hi
    exact (oidXLeBeta_one_add_mem lam cr hlam hcr n x y hCabs hCn i
      (Finset.mem_Ico.mp hi).2).2

end Work.PARIMPL2.Direct
