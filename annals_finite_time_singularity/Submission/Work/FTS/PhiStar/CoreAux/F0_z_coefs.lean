/-
# `FTS/PhiStar/CoreAux/F0_z_coefs.lean` — the two radial coefficients of the flat class

`Work.FTS.PhiStar.F0 n K f` (see `CoreAux/Defs.lean`) says that all the mixed weighted
derivatives `(z+1)^k ∂_z^k D_θ^i f` with `k + i ≤ n` are bounded by `K` on the open
quadrant.  This file supplies the two *radial* coefficients which the flat calculus of
`StarPkgo2` multiplies its angular data with:

* `z/(1+z)`,
* `1/(1+z)` (written `(1+z)⁻¹`),

with the uniform constant `m!` for the class of order `m` (the loss `k!` in the derivative
order is harmless since every constant here is existential).

**The mathematics.**  Both functions depend on `z` only, so `D_θ i f = 0` for `i ≥ 1`
(`∂_θ` of a `θ`-independent function vanishes); the whole content is therefore the radial
statement

`|(1+z)^k ∂_z^k φ z| ≤ k!   (z > 0, k ≥ 0)`

for `φ ∈ {z/(1+z), (1+z)⁻¹}`.  For `φ₁ = (1+z)⁻¹` this is the classical formula

`∂_z^k (1+z)⁻¹ = (-1)^k k! (1+z)^{-1-k}`,

which is `iter_deriv_inv_linear` of Mathlib (the shift `z ↦ 1+z` is moved inside with
`iteratedDeriv_comp_const_add`); multiplying by `(1+z)^k` leaves `± k! (1+z)⁻¹ ≤ k!`.
For `φ₂ = z/(1+z)` (which is *not* of the form `(c z + d)⁻¹`) we use
`z/(1+z) = 1 - (1+z)⁻¹` on the open half line: the congruence of `iteratedDeriv` on an open
set (`Set.EqOn.iteratedDeriv_of_isOpen`) and the additivity of `iteratedDeriv`
(`iteratedDeriv_sub`) give

`∂_z^k (z/(1+z)) = [k = 0] - ∂_z^k (1+z)⁻¹`,

so the bound for `φ₁` transfers verbatim (the `k = 0` case is `0 ≤ z/(1+z) ≤ 1`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.CoreAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false

/-! ## `D_θ` of a function of `z` alone -/

/-- `D_θ` of a function which does not depend on `θ` is zero. -/
private lemma Dth_thetaOnly_aux (φ : ℝ → ℝ) :
    Work.Spaces.Dth (fun z _ => φ z) = fun _ _ => 0 := by
  funext z θ
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [deriv_const]
  ring

/-- All the higher `D_θ`-iterates of a `θ`-independent function vanish. -/
private lemma DthIter_thetaOnly_succ (φ : ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter (i+1) (fun z _ => φ z) = fun _ _ => 0 := by
  induction i with
  | zero =>
    funext z θ
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.Dth,
      Work.Spaces.pth]
    rw [deriv_const]; ring
  | succ i ih =>
    rw [Work.Spaces.DthIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rw [deriv_const]; ring

/-- `∂_z^k` of the zero function is zero. -/
private lemma pzIter_zero_fun (k : ℕ) :
    Work.Spaces.pzIter k (fun _ _ : ℝ => (0:ℝ)) = fun _ _ => 0 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; rfl
  · exact Work.FTS.PhiStar.pzIter_const_of_theta_only 0 k hk

/-- For a function of `z` alone the iterated operator `∂_z^k` acts on the `z`-variable. -/
private lemma pzIter_thetaOnly (φ : ℝ → ℝ) (k : ℕ) :
    Work.Spaces.pzIter k (fun z _ => φ z) = fun z _ => (deriv^[k]) φ z := by
  induction k with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.pzIter_succ, ih, Function.iterate_succ_apply']; rfl

/-! ## The radial bounds -/

/-- `|(1+z)^k ∂_z^k (1+z)⁻¹| ≤ k!` for `z > 0`. -/
private lemma inv_bound (k : ℕ) (z : ℝ) (hz : 0 < z) :
    |(1+z)^k * (deriv^[k] (fun z => (1+z)⁻¹)) z| ≤ (k.factorial : ℝ) := by
  have h1z : (0:ℝ) < 1 + z := by linarith
  have hformula : (deriv^[k] (fun z => (1+z)⁻¹)) z
      = (-1)^k * (k.factorial : ℝ) * (1+z)^(-1 - (k:ℤ)) := by
    rw [← iteratedDeriv_eq_iterate]
    rw [iteratedDeriv_comp_const_add k Inv.inv 1]
    simp only []
    rw [iteratedDeriv_eq_iterate, iter_deriv_inv]
  have hzpow : (1+z)^k * (1+z)^(-1 - (k:ℤ)) = (1+z)⁻¹ := by
    rw [← zpow_natCast (1+z) k, ← zpow_add₀ (ne_of_gt h1z)]
    rw [show ((k:ℤ) + (-1 - (k:ℤ))) = -1 by ring, zpow_neg_one]
  have hkey : (1+z)^k * (deriv^[k] (fun z => (1+z)⁻¹)) z
      = (-1)^k * (k.factorial : ℝ) * (1+z)⁻¹ := by
    rw [hformula]
    rw [show (1+z)^k * ((-1)^k * (k.factorial : ℝ) * (1+z)^(-1 - (k:ℤ)))
        = (-1)^k * (k.factorial : ℝ) * ((1+z)^k * (1+z)^(-1 - (k:ℤ))) by ring, hzpow]
  rw [hkey, abs_mul, abs_mul]
  rw [show |(-1:ℝ)^k| = 1 by simp, abs_of_nonneg (Nat.cast_nonneg k.factorial),
      abs_of_pos (inv_pos.mpr h1z), one_mul]
  calc (k.factorial : ℝ) * (1+z)⁻¹ ≤ (k.factorial : ℝ) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        rw [inv_le_one₀ (by linarith)]; linarith
    _ = (k.factorial : ℝ) := by ring

/-- `|(1+z)^k ∂_z^k (z/(1+z))| ≤ k!` for `z > 0`.

Since `z/(1+z) = 1 - (1+z)⁻¹` on the open half line, `∂_z^k` of it is `[k = 0] - ∂_z^k(1+z)⁻¹`
(the two functions agree on the open set `(-1,∞)`, and `iteratedDeriv` is additive). -/
private lemma div_bound (k : ℕ) (z : ℝ) (hz : 0 < z) :
    |(1+z)^k * (deriv^[k] (fun z => z/(1+z))) z| ≤ (k.factorial : ℝ) := by
  have h1z : (0:ℝ) < 1 + z := by linarith
  have hne : (1:ℝ) + z ≠ 0 := ne_of_gt h1z
  have heqon : Set.EqOn (fun z : ℝ => z/(1+z)) (fun z : ℝ => 1 - (1+z)⁻¹)
      (Set.Ioi (-1)) := by
    intro w hw
    simp only [Set.mem_Ioi] at hw
    have hw1 : (1:ℝ) + w ≠ 0 := by linarith
    rw [div_eq_iff hw1, sub_mul, one_mul, inv_mul_cancel₀ hw1]
    ring
  have hc1 : ContDiffAt ℝ k (fun z : ℝ => (1+z)⁻¹) z := by
    have h : ContDiffAt ℝ k (fun z : ℝ => 1 + z) z := by fun_prop
    exact h.inv hne
  have hc0 : ContDiffAt ℝ k (fun z : ℝ => (1:ℝ)) z := contDiffAt_const
  have hfe : ((fun _ : ℝ => (1:ℝ)) - fun z : ℝ => (1+z)⁻¹)
      = (fun z : ℝ => 1 - (1+z)⁻¹) := by
    funext w; rfl
  have hsub : iteratedDeriv k (fun z : ℝ => 1 - (1+z)⁻¹) z
      = (if k = 0 then (1:ℝ) else 0) - iteratedDeriv k (fun z : ℝ => (1+z)⁻¹) z := by
    have h := iteratedDeriv_sub (f := fun _ : ℝ => (1:ℝ)) (g := fun z : ℝ => (1+z)⁻¹)
      hc0 hc1
    rw [iteratedDeriv_const, hfe] at h
    exact h
  have hiter : iteratedDeriv k (fun z : ℝ => z/(1+z)) z
      = iteratedDeriv k (fun z : ℝ => 1 - (1+z)⁻¹) z :=
    heqon.iteratedDeriv_of_isOpen isOpen_Ioi k (by simp only [Set.mem_Ioi]; linarith)
  have hmain : iteratedDeriv k (fun z : ℝ => z/(1+z)) z
      = (if k = 0 then (1:ℝ) else 0) - iteratedDeriv k (fun z : ℝ => (1+z)⁻¹) z := by
    rw [hiter, hsub]
  rw [← iteratedDeriv_eq_iterate, hmain]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, iteratedDeriv_zero]
    norm_num
    have hval : (1:ℝ) - (1+z)⁻¹ = z/(1+z) := by
      rw [eq_div_iff hne, sub_mul, one_mul, inv_mul_cancel₀ hne]; ring
    rw [hval, abs_of_nonneg (by positivity), div_le_iff₀ h1z]
    linarith
  · rw [ite_eq_right (by omega), zero_sub, mul_neg, abs_neg, iteratedDeriv_eq_iterate]
    exact inv_bound k z hz

/-! ## From the radial bounds to `F0` -/

/-- A `θ`-independent function whose radial bounds are all `k!` lies in the flat class
`F0 m` with the constant `m!`: for `i ≥ 1` the integrand is `0`, and for `i = 0` we use
`k! ≤ m!`. -/
private lemma F0_thetaOnly (φ : ℝ → ℝ) (m : ℕ)
    (h : ∀ k, ∀ z, 0 < z → |(1+z)^k * (deriv^[k] φ) z| ≤ (k.factorial : ℝ)) :
    Work.FTS.PhiStar.F0 m (m.factorial : ℝ) (fun z _ => φ z) := by
  intro k i hki z θ hz hθ hθ'
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rw [Work.Spaces.DthIter_zero, pzIter_thetaOnly]
    simp only []
    rw [show z + 1 = 1 + z by ring]
    exact le_trans (h k z hz) (by exact_mod_cast Nat.factorial_le (by omega : k ≤ m))
  · have hz0 : Work.Spaces.DthIter i (fun z _ => φ z) = fun _ _ => 0 := by
      conv_lhs => rw [← Nat.sub_add_cancel hi]
      exact DthIter_thetaOnly_succ φ (i-1)
    rw [hz0, pzIter_zero_fun]
    simp only [mul_zero, abs_zero]
    exact Nat.cast_nonneg _

theorem F0_z_coefs (m : ℕ) : ∃ C : ℝ, 0 < C ∧ Work.FTS.PhiStar.F0 m C (fun z _ => z / (1 + z)) ∧ Work.FTS.PhiStar.F0 m C (fun z _ => (1 + z)⁻¹) := by
  refine ⟨(m.factorial : ℝ), Nat.cast_pos.mpr (Nat.factorial_pos m), ?_, ?_⟩
  · exact F0_thetaOnly (fun z => z/(1+z)) m div_bound
  · exact F0_thetaOnly (fun z => (1+z)⁻¹) m inv_bound

end Work.FTS.PhiStar.CoreAux
