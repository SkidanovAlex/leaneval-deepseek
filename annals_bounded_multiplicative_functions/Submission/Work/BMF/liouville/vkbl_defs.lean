import Mathlib
import Submission.Work.BMF.zpt.vk_pre
import Submission.Work.BMF.zpt.vkbn_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for `Work.BMF.liouville.vk_bounded_lambda`

The bounded-`λ` Vinogradov–Korobov bound (`λ = log t / log N ≤ 88`) is proved by the
*Weyl shift + Taylor expansion + Weyl inequality* route:

* `Trel M n u t = Σ_{m ≤ M} (1+m/(n+u))^{-it}` — the shifted sum at `n` (written with the
  additive character `eC`);
* `TrelP k M n u t = Σ_{m ≤ M} e(Σ_{j≤k} γ_j m^j)` — its Taylor polynomial replacement
  (`γ_j` the Taylor coefficients of `-(t/2π) log(1+m/(n+u))`, from `Work.BMF.zpt`);
* the block sum `ESb` is recovered from the `Trel` by the shift (see `vkbl_shift`),
  the polynomial sums `TrelP` are estimated by Weyl's inequality (see `vkbl_weyl`).
-/

set_option maxHeartbeats 800000

namespace Work.BMF.liouville

open Finset

noncomputable section

/-- `(1 + m/(n+u))^{-it}` written with the additive character `eC`. -/
def relT (u t : ℝ) (n m : ℕ) : ℂ :=
  Work.BMF.eC (-(t / (2 * Real.pi)) * Real.log (1 + (m : ℝ) / ((n : ℝ) + u)))

/-- The "relative" sum `Σ_{m ≤ M}(1+m/(n+u))^{-it}`. -/
def Trel (M : ℕ) (n : ℕ) (u t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, relT u t n m

/-- The Taylor-polynomial phase summand. -/
def tayRel (k : ℕ) (u t : ℝ) (n m : ℕ) : ℂ :=
  Work.BMF.eC (Work.BMF.zpt.tayPhase k t (n : ℝ) u m)

/-- The Taylor-polynomial exponential sum `Σ_{m ≤ M} e(Σ_{j≤k} γ_j m^j)`. -/
def TrelP (k M : ℕ) (n : ℕ) (u t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, tayRel k u t n m

/-- `(x)^{-it} = eC(-(t/2π) log x)` for `x > 0`. -/
lemma cpow_eq_eC (x t : ℝ) (hx : 0 < x) :
    ((x : ℂ)) ^ (-(Complex.I * (t : ℂ))) = Work.BMF.eC (-(t / (2 * Real.pi)) * Real.log x) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt hx)]
  rw [← Complex.ofReal_log hx.le]
  unfold Work.BMF.eC
  congr 1
  push_cast
  field_simp

/-- `(x)^{-it}` with `x > 0` has modulus one. -/
lemma norm_cpow_eq_one (x t : ℝ) (hx : 0 < x) :
    ‖((x : ℂ)) ^ (-(Complex.I * (t : ℂ)))‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp

/-- Unfolding of the Taylor polynomial in evaluation form. -/
lemma eval_tayPoly (k : ℕ) (t u : ℝ) (n : ℕ) (x : ℝ) :
    (Work.BMF.zpt.tayPoly k t (n : ℝ) u).eval x
      = ∑ j ∈ Finset.Icc 1 k, Work.BMF.zpt.gam j t (n : ℝ) u * x ^ j := by
  unfold Work.BMF.zpt.tayPoly
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- `TrelP` is the polynomial exponential sum of `tayPoly`. -/
lemma TrelP_eq_sum_eval (k M : ℕ) (n : ℕ) (u t : ℝ) :
    TrelP k M n u t
      = ∑ m ∈ Finset.Icc 1 M,
          Work.BMF.eC ((Work.BMF.zpt.tayPoly k t (n : ℝ) u).eval (m : ℝ)) := by
  unfold TrelP tayRel Work.BMF.zpt.tayPhase
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [eval_tayPoly]

/-- The coefficient of `X^m` in the Taylor polynomial. -/
lemma coeff_tayPoly (k : ℕ) (t u : ℝ) (n : ℕ) (m : ℕ) :
    (Work.BMF.zpt.tayPoly k t (n : ℝ) u).coeff m
      = ∑ j ∈ Finset.Icc 1 k, Work.BMF.zpt.gam j t (n : ℝ) u * (if j = m then 1 else 0) := by
  unfold Work.BMF.zpt.tayPoly
  rw [Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : j = m
  · subst h; simp
  · have h' : ¬ (m = j) := fun hh => h hh.symm
    simp [h, h']

/-- The Taylor polynomial of degree `k` has degree at most `k`. -/
lemma natDegree_tayPoly_le (k : ℕ) (t u : ℝ) (n : ℕ) :
    (Work.BMF.zpt.tayPoly k t (n : ℝ) u).natDegree ≤ k := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [coeff_tayPoly]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjle : j ≤ k := (Finset.mem_Icc.mp hj).2
  have : j ≠ m := by omega
  simp [this]

/-- The coefficient of `X^k` in the Taylor polynomial is `γ_k`. -/
lemma coeff_tayPoly_self (k : ℕ) (hk : 1 ≤ k) (t u : ℝ) (n : ℕ) :
    (Work.BMF.zpt.tayPoly k t (n : ℝ) u).coeff k = Work.BMF.zpt.gam k t (n : ℝ) u := by
  rw [coeff_tayPoly]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j hj hjk
    simp [hjk]
  · intro hk'
    exact absurd (Finset.mem_Icc.mpr ⟨hk, le_refl k⟩) hk'

/-- The leading coefficient of the Taylor polynomial is `γ_k` (for `k ≥ 1` and `γ_k ≠ 0`). -/
lemma leadingCoeff_tayPoly (k : ℕ) (hk : 1 ≤ k) (t u : ℝ) (n : ℕ)
    (hγ : Work.BMF.zpt.gam k t (n : ℝ) u ≠ 0) :
    (Work.BMF.zpt.tayPoly k t (n : ℝ) u).leadingCoeff
      = Work.BMF.zpt.gam k t (n : ℝ) u := by
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_tayPoly_le k t u n) (by rw [coeff_tayPoly_self k hk]; exact hγ)]
  exact coeff_tayPoly_self k hk t u n

/-- `γ_k ≠ 0` for `k ≥ 1`, `t > 0`, `u > 0`. -/
lemma gam_ne_zero (k : ℕ) (hk : 1 ≤ k) (t u : ℝ) (n : ℕ) (ht : 0 < t) (hu : 0 < u) :
    Work.BMF.zpt.gam k t (n : ℝ) u ≠ 0 := by
  unfold Work.BMF.zpt.gam
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hnum : (-1 : ℝ) ^ k * t ≠ 0 := by
    simp [ne_of_gt ht]
  exact div_ne_zero hnum (by positivity)

/-- The Taylor polynomial of degree `k` has natDegree exactly `k` when `γ_k ≠ 0`. -/
lemma natDegree_tayPoly (k : ℕ) (hk : 1 ≤ k) (t u : ℝ) (n : ℕ)
    (hγ : Work.BMF.zpt.gam k t (n : ℝ) u ≠ 0) :
    (Work.BMF.zpt.tayPoly k t (n : ℝ) u).natDegree = k :=
  Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (natDegree_tayPoly_le k t u n)
    (by rw [coeff_tayPoly_self k hk]; exact hγ)

/-- Each summand of `ESb` has modulus one, so the block sum is bounded by its number of terms. -/
lemma norm_ESb_le_card (N R u t : ℝ) (hu : 0 < u) :
    ‖Work.BMF.zpt.ESb N R u t‖ ≤ ((Finset.Ioc ⌊N⌋₊ ⌊R⌋₊).card : ℝ) := by
  have h1 : ‖Work.BMF.zpt.ESb N R u t‖ ≤ ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊,
      ‖((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ := norm_sum_le _ _
  have h2 : ∀ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊,
      ‖((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ (1 : ℝ) := by
    intro n hn
    have hn1 : 1 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
    have hpos : (0 : ℝ) < (n : ℝ) + u := by
      have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      linarith
    exact le_of_eq (norm_cpow_eq_one _ _ hpos)
  calc ‖Work.BMF.zpt.ESb N R u t‖
      ≤ ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊, ‖((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ := h1
    _ ≤ ∑ _n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊, (1 : ℝ) := Finset.sum_le_sum h2
    _ = ((Finset.Ioc ⌊N⌋₊ ⌊R⌋₊).card : ℝ) := by simp

/-- `λ = log t / log N`. -/
def vlam (N t : ℝ) : ℝ := Real.log t / Real.log N

/-- The auxiliary `δ₂ = λ/178`. -/
def vd2 (N t : ℝ) : ℝ := vlam N t / 178

/-- `μ = 1 - (λ+δ₂)/90`, the exponent of the Weyl-shift parameter `M = ⌊N^μ⌋`. -/
def vmu (N t : ℝ) : ℝ := 1 - (vlam N t + vd2 N t) / 90

/-- The Weyl `ε`. -/
def epsw : ℝ := (1 / 2 : ℝ) ^ 200

/-- The saving exponent delivered by the bracket bound `1/q + 1/M + 1/M^88 + q/M^89`:
`min(λ/180, μ)`.  The term `1/M ~ N^{-μ}` dominates for large `λ`. -/
def vtv (N t : ℝ) : ℝ := min (vlam N t / 180) (vmu N t)

end

end Work.BMF.liouville
