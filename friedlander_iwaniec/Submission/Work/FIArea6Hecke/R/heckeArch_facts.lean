import Mathlib
import Submission.Work.FITop4.Bridge.area5_6_defs

/-!
# The archimedean factor `heckeArch d 0` on the right half-plane

The archimedean factor of the completed Hecke `L`-function of weight `m` is

  `heckeArch d m s = (4d/π)^s · Γ(s + |m|/2)`

(`Work.FITop4.Bridge.heckeArch`).  For the weight `m = 0` it specialises to
`(4d/π)^s · Γ(s)`, and here we record the two elementary facts that the `§16` argument of
Friedlander–Iwaniec needs on the half-plane `re s > 0`:

* it never vanishes there, so that on the right half-plane the continuation
  `L(s) = Lam s / heckeArch d 0 s` vanishes exactly where the completion `Lam` does
  (`Lval d 0 Lam s = 0 ↔ Lam s = 0`);
* it is holomorphic there, so that `Lam / heckeArch d 0` is meromorphic wherever `Lam` is.

Both are immediate from `(4d/π)^s = exp(s log(4d/π)) ≠ 0` and the fact that the poles `0, -1, -2, …`
are the *only* zeros of `Γ`: on `re s > 0` the argument `s` of `Γ` stays at distance `> 0` from
every pole.
-/

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- At `m = 0` the archimedean factor is the function `s ↦ (4d/π)^s · Γ(s)`. -/
private lemma heckeArch_zero_eq (d : ℕ) :
    Work.FITop4.Bridge.heckeArch d 0
      = fun s : ℂ => (((4 * (d : ℝ)) / Real.pi : ℝ) : ℂ) ^ s * Complex.Gamma s := by
  funext s
  unfold Work.FITop4.Bridge.heckeArch
  norm_num

/-- The base `4d/π` of the exponential factor is non-zero as soon as `d ≥ 1`. -/
private lemma base_ne_zero {d : ℕ} (hd : 1 ≤ d) :
    (((4 * (d : ℝ)) / Real.pi : ℝ) : ℂ) ≠ 0 := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h : (0 : ℝ) < 4 * (d : ℝ) / Real.pi := by positivity
  exact_mod_cast (ne_of_gt h)

/-- **`heckeArch d 0` does not vanish on `re s > 0` and is holomorphic there.**

Non-vanishing: `(4d/π)^s = exp(s log(4d/π))` is an exponential, hence non-zero, and `Γ(s) ≠ 0`
because the poles `0, -1, -2, …` of `Γ` are its only singularities and `re s > 0` excludes them.

Holomorphy: both factors are differentiable at every point of the open half-plane
(`z ↦ c^z` for `c ≠ 0` and `Γ` at a point at distance `> 0` from the poles `-k`), and a function
differentiable on an *open* set is analytic there. -/
theorem heckeArch_facts {d : ℕ} (hd : 1 ≤ d) :
    (∀ s : ℂ, 0 < s.re → Work.FITop4.Bridge.heckeArch d 0 s ≠ 0) ∧
    (∀ s : ℂ, 0 < s.re → AnalyticAt ℂ (Work.FITop4.Bridge.heckeArch d 0) s) := by
  constructor
  · intro s hs
    rw [heckeArch_zero_eq d]
    refine mul_ne_zero ?_ (Complex.Gamma_ne_zero_of_re_pos hs)
    rw [Complex.cpow_def_of_ne_zero (base_ne_zero hd)]
    exact Complex.exp_ne_zero _
  · intro s hs
    have hdiff :
        DifferentiableOn ℂ (Work.FITop4.Bridge.heckeArch d 0) {z : ℂ | 0 < z.re} := by
      intro z hz
      have hz' : (0 : ℝ) < z.re := hz
      have hzat : DifferentiableAt ℂ (Work.FITop4.Bridge.heckeArch d 0) z := by
        rw [heckeArch_zero_eq d]
        refine DifferentiableAt.mul
          (DifferentiableAt.const_cpow differentiableAt_id (Or.inl (base_ne_zero hd))) ?_
        apply Complex.differentiableAt_Gamma
        intro k hk
        have hre : z.re = -(k : ℝ) := by
          simpa using congrArg Complex.re hk
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith
      exact hzat.differentiableWithinAt
    have hopen : IsOpen {z : ℂ | 0 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    exact (hdiff.analyticOn hopen).analyticAt (hopen.mem_nhds hs)

end

end Work.FIArea6Hecke.R
