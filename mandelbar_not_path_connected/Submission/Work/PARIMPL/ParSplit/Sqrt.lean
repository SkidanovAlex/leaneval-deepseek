/-
Copyright: subproject `Submission/Work/PARIMPL/ParSplit/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.ParSplit.Sqrt` — turning a *real* factorization into a continuous square root

The chart scale of the parameter normal form is the *half-difference* `Δ` of the two fixed points
into which the simple parabolic point `z₁` of `F c = (T_c)^[10]` splits.  Since `Δ² = G` is a
single-valued (real-analytic) function but `Δ` itself is only a two-valued function of `c`, the
continuity of `Δ` is a genuine statement: in a *holomorphic* family the two roots have nontrivial
monodromy around the parabolic parameter (ℂ has no room for a "wall"), while in the tricorn the
parameter dependence is only real analytic and the collision locus

  `Z = {c : the two split fixed points coincide}`

is a real curve through `c₀`, so that a continuous single-valued choice of `Δ` exists.

The precise mechanism is the following.  `G = Δ²` vanishes exactly on `Z`; if one can write

  `G = A · h`  on a ball `B` around `c₀`,

with `A : B → ℝ` real-valued and `h` continuous and nowhere vanishing on `B` (so that the zero set
of `A` is exactly `Z`, with the same order of vanishing as `G`), then

  `Δ := √A · √h`

is a *continuous, single-valued* square root of `G` on `B`: `√A` is the real-or-imaginary square
root of the real function `A` (`realSqrt` below), and `√h` is the continuous square root of the
nowhere-vanishing function `h` on the simply connected ball `B`, which Mathlib provides
(`Complex.exists_continuousOn_pow_eq`).

This module contains exactly that reduction, plus the elementary fact that balls are simply
connected.  The real mathematics of the tricorn (the construction of `A`, i.e. the "wall"
`A = (1 - ρ₊)(1 - ρ₋)` where `ρ±` are the multipliers of `F c` at the two split fixed points) is
*not* here; see `Submission/Work/PARIMPL/ParSplit/NOTES.md`.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

/-- A chosen square root of a real number: real for `a ≥ 0`, purely imaginary for `a ≤ 0`. -/
def realSqrt (a : ℝ) : ℂ := (Real.sqrt ‖a‖ : ℂ) * (if 0 ≤ a then 1 else Complex.I)

theorem realSqrt_zero : realSqrt 0 = 0 := by simp [realSqrt]

/-- `realSqrt a` really is a square root of `a`. -/
theorem realSqrt_sq (a : ℝ) : realSqrt a ^ 2 = (a : ℂ) := by
  have hsq : (Real.sqrt ‖a‖ : ℂ) ^ 2 = (‖a‖ : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (norm_nonneg a)]
  unfold realSqrt
  rw [mul_pow, hsq]
  by_cases h : 0 ≤ a
  · rw [if_pos h, one_pow, mul_one, Real.norm_eq_abs, abs_of_nonneg h]
  · rw [if_neg h, sq, Complex.I_mul_I, mul_neg, mul_one, Real.norm_eq_abs, abs_of_neg (not_le.mp h)]
    push_cast; ring

theorem norm_realSqrt (a : ℝ) : ‖realSqrt a‖ = Real.sqrt ‖a‖ := by
  unfold realSqrt
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  by_cases h : 0 ≤ a
  · rw [if_pos h, norm_one, mul_one]
  · rw [if_neg h, Complex.norm_I, mul_one]

theorem continuous_realSqrt : Continuous realSqrt := by
  rw [continuous_iff_continuousAt]
  intro a
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have hmem : {b : ℝ | b < 0} ∈ 𝓝 a := (isOpen_lt continuous_id continuous_const).mem_nhds ha
    have hEq : realSqrt =ᶠ[𝓝 a] fun b => Complex.I * Complex.ofReal (Real.sqrt (-b)) := by
      filter_upwards [hmem] with b hb
      simp only [realSqrt, Real.norm_eq_abs, abs_of_neg hb, if_neg (not_le.mpr hb)]
      ring
    exact ContinuousAt.congr ((continuous_const.mul (Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp continuous_neg))).continuousAt) hEq.symm
  · subst ha
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε ^ 2, pow_pos hε 2, fun b hb => ?_⟩
    rw [realSqrt_zero, dist_zero_right, norm_realSqrt]
    have h1 : ‖b‖ < ε ^ 2 := by rw [← dist_zero_right]; exact hb
    rw [Real.sqrt_lt' hε]
    exact h1
  · have hmem : {b : ℝ | 0 < b} ∈ 𝓝 a := (isOpen_lt continuous_const continuous_id).mem_nhds ha
    have hEq : realSqrt =ᶠ[𝓝 a] fun b => Complex.ofReal (Real.sqrt b) := by
      filter_upwards [hmem] with b hb
      simp only [realSqrt, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hb), if_pos (le_of_lt hb),
        mul_one]
    exact ContinuousAt.congr ((Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousAt)
      hEq.symm

theorem continuousOn_realSqrt_comp {X : Type*} [TopologicalSpace X] {U : Set X} {A : X → ℝ}
    (hA : ContinuousOn A U) : ContinuousOn (fun x => realSqrt (A x)) U :=
  continuous_realSqrt.comp_continuousOn hA

/-- **Square root of a factorization by a real function.**  If `G = A · h` on the open simply
connected set `U`, with `A` real-valued and `h` continuous and nowhere zero, then `G` has a
continuous square root on `U`. -/
theorem exists_continuousOn_sq_eq_mul_of_real {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] {U : Set X} (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    {A : X → ℝ} (hA : ContinuousOn A U) {h : X → ℂ} (hh : ContinuousOn h U)
    (hh0 : ∀ x ∈ U, h x ≠ 0) :
    ∃ Δ : X → ℂ, ContinuousOn Δ U ∧ ∀ x ∈ U, Δ x ^ 2 = (A x : ℂ) * h x := by
  obtain ⟨s, hs, hspow⟩ := Complex.exists_continuousOn_pow_eq (X := X) hUc hUo hh (by
      rintro ⟨x, hx, hx0⟩
      exact hh0 x hx hx0) (n := 2) (by norm_num)
  refine ⟨fun x => realSqrt (A x) * s x, ?_, ?_⟩
  · exact (continuousOn_realSqrt_comp hA).mul hs
  · intro x hx
    rw [mul_pow, realSqrt_sq, hspow x]

/-- A ball in `ℂ` is simply connected: it is convex, hence contractible. -/
theorem isSimplyConnected_ball (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    IsSimplyConnected (ball z ρ) :=
  letI : ContractibleSpace (ball z ρ) :=
    (convex_ball z ρ).contractibleSpace ⟨z, mem_ball_self hρ⟩
  SimplyConnectedSpace.ofContractible (ball z ρ)

/-- **Square root of a nowhere-vanishing continuous function on a ball.** -/
theorem exists_continuousOn_sq_eq_ball {g : ℂ → ℂ} {c₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : ContinuousOn g (ball c₀ ρ)) (hg0 : ∀ c ∈ ball c₀ ρ, g c ≠ 0) :
    ∃ s : ℂ → ℂ, ContinuousOn s (ball c₀ ρ) ∧ ∀ c : ℂ, s c ^ 2 = g c :=
  Complex.exists_continuousOn_pow_eq (isSimplyConnected_ball c₀ hρ) isOpen_ball hg
    (by rintro ⟨c, hc, hc0⟩; exact hg0 c hc hc0) (n := 2) (by norm_num)

end Work.PARIMPL.ParSplit
