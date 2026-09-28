import Mathlib

/-!
# Shared definitions for the `𝔡₃ > A^{1/20}` part of the case-`I` sum (`(d,n) = (4,4)`)

This file isolates the numerical objects that appear both in the per-pair lattice bound
(`Submission/Work/HP/MDEstimates/hiparts/pairS0_hi_bound.lean`) and in the dyadic cell-sum
estimate (`Submission/Work/HP/MDEstimates/hiparts/hi_cell_sum.lean`), so that neither has to
import the other.

* `hiLZ B Δ M` is the right-hand side of the convenient `ℓ^{(1)}` bound of
  `MDEstimates.ell44_convenient` at `Z = B`, i.e.
  `B^{9/2} Δ² (B^{3/2} + Δ^{3/2}) (log 2Δ)² min{Δ, M^{53}}`.
* `hiCell A B d l R0` is the `R0`-th term of the Lemma-R0 bound for a pair with
  `𝔡₃ = d`, `λ₁(Γ) = l`: `A^{68-R0} B^{2 R0-8} d^{-R0} + (2A/l)^{67-R0}`
  (here `N_{4,4} - 2 = 68`).
* `hiMin A B d l` is the minimum of `hiCell A B d l R0` over `R0 ∈ {4, …, 67}`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.MDEstimates

open Finset
open scoped BigOperators

/-- The convenient `ℓ^{(1)}` bound at `Z = B`, as a function of the cutoffs `Δ` (for `𝔡₃`) and
`M` (for `λ₁`). -/
def hiLZ (B Δ M : ℝ) : ℝ :=
  B ^ ((9 : ℝ) / 2) * Δ ^ 2 * (B ^ ((3 : ℝ) / 2) + Δ ^ ((3 : ℝ) / 2)) *
    (Real.log (2 * Δ)) ^ 2 * min Δ (M ^ 53)

/-- The `R0`-th term of the Lemma-R0 bound for a pair with `𝔡₃ = d` and `λ₁(Γ) = l`. -/
def hiCell (A B d l : ℝ) (R0 : ℕ) : ℝ :=
  A ^ (68 - R0) * B ^ (2 * R0 - 8) * d ^ (-(R0 : ℝ)) + (2 * A / l) ^ (67 - R0)

/-- The minimum of `hiCell A B d l R0` over `R0 ∈ {4, …, 67}`. -/
def hiMin (A B d l : ℝ) : ℝ :=
  (Finset.Icc 4 67).inf' ⟨4, by decide⟩ (fun R0 => hiCell A B d l R0)

/-- `hiMin` is at most each `hiCell`. -/
lemma hiMin_le_cell (A B d l : ℝ) {R0 : ℕ} (h4 : 4 ≤ R0) (h67 : R0 ≤ 67) :
    hiMin A B d l ≤ hiCell A B d l R0 :=
  Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨h4, h67⟩)

/-- The defining property of `hiMin`. -/
lemma le_hiMin (A B d l : ℝ) {x : ℝ} (h : ∀ R0 ∈ Finset.Icc 4 67, x ≤ hiCell A B d l R0) :
    x ≤ hiMin A B d l :=
  Finset.le_inf' _ _ h

/-- `hiCell A B d l R0` is antitone in `d`. -/
lemma hiCell_anti_d (A B d l : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hl : 0 < l) (R0 : ℕ)
    {d' : ℝ} (hd : 0 < d) (hdd : d ≤ d') :
    hiCell A B d' l R0 ≤ hiCell A B d l R0 := by
  have hd' : 0 < d' := lt_of_lt_of_le hd hdd
  have hnonpos : -(R0 : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg R0)
  have h1 : (d' : ℝ) ^ (-(R0 : ℝ)) ≤ d ^ (-(R0 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hd hdd hnonpos
  have h2 : (0 : ℝ) ≤ A ^ (68 - R0) := pow_nonneg hA _
  have h3 : (0 : ℝ) ≤ B ^ (2 * R0 - 8) := pow_nonneg hB _
  have h4 : (0 : ℝ) ≤ (2 * A / l) ^ (67 - R0) :=
    pow_nonneg (div_nonneg (by linarith) hl.le) _
  unfold hiCell
  exact add_le_add (mul_le_mul_of_nonneg_left h1 (mul_nonneg h2 h3)) le_rfl

/-- `hiCell A B d l R0` is antitone in `l`. -/
lemma hiCell_anti_l (A B d l l' : ℝ) (hA : 0 ≤ A) (hl : 0 < l) (hll : l ≤ l') (R0 : ℕ) :
    hiCell A B d l' R0 ≤ hiCell A B d l R0 := by
  have hl' : 0 < l' := lt_of_lt_of_le hl hll
  have h1 : 2 * A / l' ≤ 2 * A / l := div_le_div_of_nonneg_left (by linarith) hl hll
  have h2 : (2 * A / l') ^ (67 - R0) ≤ (2 * A / l) ^ (67 - R0) :=
    pow_le_pow_left₀ (div_nonneg (by linarith) hl'.le) h1 _
  unfold hiCell
  exact add_le_add le_rfl h2

/-- `hiMin` is antitone in the two cutoffs. -/
lemma hiMin_anti (A B d l d' l' : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 < d)
    (hdd : d ≤ d') (hl : 0 < l) (hll : l ≤ l') :
    hiMin A B d' l' ≤ hiMin A B d l := by
  refine le_hiMin A B d l (fun R0 hR0 => ?_)
  exact le_trans (hiMin_le_cell A B d' l' (Finset.mem_Icc.mp hR0).1 (Finset.mem_Icc.mp hR0).2)
    (le_trans (hiCell_anti_d A B d l' hA hB (lt_of_lt_of_le hl hll) R0 hd hdd)
      (hiCell_anti_l A B d l l' hA hl hll R0))

/-- `hiMin` is nonnegative. -/
lemma hiMin_nonneg (A B d l : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 ≤ d) (hl : 0 < l) :
    0 ≤ hiMin A B d l := by
  refine le_hiMin A B d l (fun R0 hR0 => ?_)
  unfold hiCell
  have h1 : (0 : ℝ) ≤ A ^ (68 - R0) := pow_nonneg hA _
  have h2 : (0 : ℝ) ≤ B ^ (2 * R0 - 8) := pow_nonneg hB _
  have h3 : (0 : ℝ) ≤ (d : ℝ) ^ (-(R0 : ℝ)) := Real.rpow_nonneg hd _
  have h4 : (0 : ℝ) ≤ (2 * A / l) ^ (67 - R0) :=
    pow_nonneg (div_nonneg (by linarith) hl.le) _
  positivity

end Work.HP.MDEstimates
