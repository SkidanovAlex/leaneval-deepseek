import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Ball
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.OddCurveB.Existence.KdiagForm
import Submission.Work.OddCurveB.Est.differentiableAt_Godd

/-!
# Differentiability of the odd Volterra map in the state, for `n ≥ 1`

`Work.OddExistence.Estimates.godd_differentiable`: on a compact slope interval
`[a,b] ⊆ (0,1]`, on a ball of radius `ρ ≤ 1/2` around the unperturbed state
`baseState s`, and for a perturbation `h` which is supported in the transition
window `[1 - 2τ, 1 - τ]` with `|h| ≤ 1/100` and `|h'| ≤ 1/100`, the odd
transition-slope map

`w ↦ Godd n h s w`

is differentiable at every point of that ball, **for every `n ≥ 1`**.

## How the hypothesis `n ≥ 1` is enough

`Godd` depends on `h` only through the two numbers `(h s, h'(s))`: on the diagonal
`σ = s` the Abel average collapses (`Godd_eq_GoddDiag`) to the explicit system
`GoddDiag n s (h s) (h' s)` built from the two diagonal kernels

`Kdiag1 n s hs hp t = C₁ (D^n √D)`,   `Kdiag2 n s hs hp t = C₂ (D^{n-1} √D) (t + hp)`,
`D = Drad s hs hp t = (t + hp) (s t + hs)`.

* `Kdiag1` is differentiable everywhere as soon as `n ≥ 1`, because `x ↦ x^n √x`
  is differentiable everywhere for `n ≥ 1` (`differentiableAt_pow_mul_sqrt`).
* `Kdiag2` is differentiable at every point where `D ≠ 0`: where `D > 0` the
  square root is smooth, and where `D < 0` the function vanishes identically on a
  neighbourhood.  (At a *simple* zero of `D` with `t + hp ≠ 0`, `n = 1` genuinely
  fails — `Work.OddCurveB.Est.not_differentiableAt_Godd_one` — so the two
  side conditions `Drad s (h s) (h' s) (-(z 0)) ≠ 0`, `Drad s (h s) (h' s) (z 1) ≠ 0`
  are exactly what the proof has to supply here.)

The hypotheses on `h` give them: if `D = 0` at one of the two arguments
`t = -(z 0)`, `t = z 1`, then either `|t| = |h'(s)| ≤ 1/100`, or `t = -h s/s`;
in the second case `h s = 0` gives `t = 0` while `h s ≠ 0` forces
`s ∈ Function.support h ⊆ [4/5, 9/10]`, hence `|t| ≤ (1/100)/(4/5) = 1/80`.
But `|t| ≥ 1/5`: both arguments lie in the ball of radius `ρ ≤ 1/2` around
`profileX s ≥ 7/10`, and `7/10 - 1/2 = 1/5 > 1/80`.
-/

namespace Work.OddExistence.Estimates

open Work.OddVolterra
open Work.OddCurveB.Existence
open scoped Topology

noncomputable section

/-! ## Differentiability of the two diagonal kernels -/

/-- The second diagonal kernel is differentiable at every point where the radicand
`Drad` of its denominator does not vanish.  This version has no restriction on `n`
beyond `1 ≤ n`: it replaces the everywhere-differentiability result for `n ≥ 2`
(`Work.OddCurveB.Est.differentiableAt_Kdiag2`), which fails for `n = 1` at a simple
zero of `Drad`. -/
lemma gd_Kdiag2_diff (n : ℕ) (hn : 1 ≤ n) (s hs hp t : ℝ) (hD : Drad s hs hp t ≠ 0) :
    DifferentiableAt ℝ (fun u : ℝ => Kdiag2 n s hs hp u) t := by
  have hfun : (fun u : ℝ => Kdiag2 n s hs hp u) = fun u : ℝ =>
      ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (-1) ^ n / Real.sqrt 2) *
        (Drad s hs hp u ^ (n - 1) * Real.sqrt (Drad s hs hp u)) * (u + hp) := by
    funext u; exact Kdiag2_eq n hn s hs hp u
  rw [hfun]
  have hDrad : DifferentiableAt ℝ (fun u : ℝ => Drad s hs hp u) t := by
    unfold Drad; fun_prop
  have hsqrt : DifferentiableAt ℝ (fun u : ℝ => Real.sqrt (Drad s hs hp u)) t :=
    hDrad.sqrt hD
  exact DifferentiableAt.mul (DifferentiableAt.const_mul
    (DifferentiableAt.mul (hDrad.pow _) hsqrt) _)
    (by fun_prop : DifferentiableAt ℝ (fun u : ℝ => u + hp) t)

/-- The explicit diagonal system `GoddDiag` is differentiable in the state, as soon as
`1 ≤ n` and the two radicands `Drad s hs hp (-(z 0))`, `Drad s hs hp (z 1)` do not
vanish. -/
lemma gd_GoddDiag_diff (n : ℕ) (hn : 1 ≤ n) (s hs hp : ℝ) (z : St)
    (h0 : Drad s hs hp (-(z 0)) ≠ 0) (h1 : Drad s hs hp (z 1) ≠ 0) :
    DifferentiableAt ℝ (fun w : St => GoddDiag n s hs hp w) z := by
  rw [show (fun w : St => GoddDiag n s hs hp w) = fun w : St =>
      ![w 0, w 1,
        -(abelMass * (-(Kdiag1 n s hs hp (-(w 0)) * w 2 + Kdiag1 n s hs hp (w 1) * w 3))),
        -(abelMass * (-(Kdiag2 n s hs hp (-(w 0)) * w 2 + Kdiag2 n s hs hp (w 1) * w 3)))]
      from rfl]
  have hD0 : DifferentiableAt ℝ (fun w : St => w 0) z :=
    (differentiable_apply (𝕜 := ℝ) (0 : Fin 4)).differentiableAt
  have hD1 : DifferentiableAt ℝ (fun w : St => w 1) z :=
    (differentiable_apply (𝕜 := ℝ) (1 : Fin 4)).differentiableAt
  have hD2 : DifferentiableAt ℝ (fun w : St => w 2) z :=
    (differentiable_apply (𝕜 := ℝ) (2 : Fin 4)).differentiableAt
  have hD3 : DifferentiableAt ℝ (fun w : St => w 3) z :=
    (differentiable_apply (𝕜 := ℝ) (3 : Fin 4)).differentiableAt
  have hneg0 : DifferentiableAt ℝ (fun w : St => -(w 0)) z := hD0.neg
  have hK1a : DifferentiableAt ℝ (fun w : St => Kdiag1 n s hs hp (-(w 0))) z := by
    have h := (Work.OddCurveB.Est.differentiableAt_Kdiag1 n hn s hs hp (-(z 0))).comp z hneg0
    rw [Function.comp_def] at h; exact h
  have hK1b : DifferentiableAt ℝ (fun w : St => Kdiag1 n s hs hp (w 1)) z := by
    have h := (Work.OddCurveB.Est.differentiableAt_Kdiag1 n hn s hs hp (z 1)).comp z hD1
    rw [Function.comp_def] at h; exact h
  have hK2a : DifferentiableAt ℝ (fun w : St => Kdiag2 n s hs hp (-(w 0))) z := by
    have h := (gd_Kdiag2_diff n hn s hs hp (-(z 0)) h0).comp z hneg0
    rw [Function.comp_def] at h; exact h
  have hK2b : DifferentiableAt ℝ (fun w : St => Kdiag2 n s hs hp (w 1)) z := by
    have h := (gd_Kdiag2_diff n hn s hs hp (z 1) h1).comp z hD1
    rw [Function.comp_def] at h; exact h
  refine differentiableAt_pi.mpr (fun i => ?_)
  fin_cases i
  · simpa using hD0
  · simpa using hD1
  · simpa using ((((hK1a.mul hD2).add (hK1b.mul hD3)).neg.const_mul abelMass).neg)
  · simpa using ((((hK2a.mul hD2).add (hK2b.mul hD3)).neg.const_mul abelMass).neg)

/-! ## The two numerical inputs -/

/-- `profileX s ≥ 7/10` for `0 ≤ s ≤ 1`, i.e. `1/√(1+s²) ≥ 1/√2 ≥ 7/10`. -/
lemma gd_profileX_ge {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (7 : ℝ) / 10 ≤ Commons.Geometry.Ulam.profileX s := by
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hsqrt2 : Real.sqrt 2 ≤ 10 / 7 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2]
  have hsqrt : Real.sqrt (1 + s ^ 2) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by linarith)
  have hpos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hpos2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : (7 : ℝ) / 10 ≤ 1 / Real.sqrt 2 := by
    rw [le_div_iff₀ hpos2]
    nlinarith
  have h3 : 1 / Real.sqrt 2 ≤ 1 / Real.sqrt (1 + s ^ 2) := one_div_le_one_div_of_le hpos hsqrt
  have hprof : Commons.Geometry.Ulam.profileX s = 1 / Real.sqrt (1 + s ^ 2) := rfl
  rw [hprof]
  linarith

/-- Away from the two points `t = -h'(s)` and `t = -h s / s`, the radicand `Drad` of the
diagonal denominators does not vanish.  The hypotheses on `h` (support in the transition
window, `|h| ≤ 1/100`, `|h'| ≤ 1/100`) put both exceptional points inside `|t| < 1/80`,
while the arguments arising from the state ball satisfy `|t| ≥ 1/5`. -/
lemma gd_Drad_ne_zero {h : ℝ → ℝ} {s t : ℝ} (hs : 0 < s)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (h0 : |h s| ≤ 1 / 100) (h1 : |deriv h s| ≤ 1 / 100) (ht : 1 / 5 ≤ |t|) :
    Drad s (h s) (deriv h s) t ≠ 0 := by
  intro hcon
  unfold Drad at hcon
  rcases mul_eq_zero.mp hcon with hA | hB
  · -- `t = -h'(s)`, so `|t| ≤ 1/100 < 1/5`
    have hteq : t = -(deriv h s) := by linarith
    have hteq2 : |t| = |deriv h s| := by rw [hteq]; simp
    rw [hteq2] at ht
    linarith
  · rcases eq_or_ne (h s) 0 with hz | hne
    · -- `h s = 0` forces `t = 0`
      have ht0 : t = 0 := by
        have hs0' : s * t = 0 := by rw [hz] at hB; simpa using hB
        exact (mul_eq_zero.mp hs0').resolve_left (ne_of_gt hs)
      rw [ht0] at ht
      simp at ht
      norm_num at ht
    · -- `h s ≠ 0` puts `s` in the transition window `[4/5, 9/10]`
      have hmem := hsupp hne
      unfold Work.OddVolterra.tau at hmem
      norm_num at hmem
      have hs45 : (4 : ℝ) / 5 ≤ s := hmem.1
      have hst : s * t = - h s := by linarith
      have htabs : |t| = |h s| / s := by
        have ht' : t = -(h s) / s := by
          rw [eq_div_iff (ne_of_gt hs)]
          linarith
        rw [ht']; simp only [abs_div, abs_neg, abs_of_pos hs]
      rw [htabs] at ht
      have hbound : |h s| / s ≤ 1 / 80 := by
        rw [div_le_iff₀ hs]
        nlinarith [abs_nonneg (h s)]
      linarith

/-! ## The main statement -/

theorem godd_differentiable (n : ℕ) (hn : 1 ≤ n) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState s) ρ,
      DifferentiableAt ℝ (fun w => Work.OddVolterra.Godd n h s w) z := by
  intro s hs z hz
  have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
  have hs1 : s ≤ 1 := le_trans hs.2 hb
  have hbase0 : Work.OddVolterra.baseState s 0 = Commons.Geometry.Ulam.profileX s := by
    simp [Work.OddVolterra.baseState]
  have hbase1 : Work.OddVolterra.baseState s 1 = Commons.Geometry.Ulam.profileX s := by
    simp [Work.OddVolterra.baseState]
  have hdist : dist z (Work.OddVolterra.baseState s) ≤ ρ := Metric.mem_closedBall.mp hz
  have hcoord : ∀ i : Fin 4, |z i - Work.OddVolterra.baseState s i| ≤ ρ := by
    intro i
    have h := norm_le_pi_norm (z - Work.OddVolterra.baseState s) i
    rw [Real.norm_eq_abs, Pi.sub_apply] at h
    rw [dist_eq_norm] at hdist
    exact le_trans h hdist
  have hprof : (7 : ℝ) / 10 ≤ Commons.Geometry.Ulam.profileX s :=
    gd_profileX_ge (le_of_lt hs0) hs1
  -- the reverse triangle inequality: a coordinate at distance `≤ ρ` from `profileX s`
  -- has absolute value `≥ profileX s - ρ`
  have htri : ∀ t : ℝ, |t - Commons.Geometry.Ulam.profileX s| ≤ ρ →
      Commons.Geometry.Ulam.profileX s - ρ ≤ |t| := by
    intro t ht
    have hle := abs_abs_sub_abs_le_abs_sub (Commons.Geometry.Ulam.profileX s) t
    have hle' : Commons.Geometry.Ulam.profileX s - |t|
        ≤ |Commons.Geometry.Ulam.profileX s - t| := by
      have hp : |Commons.Geometry.Ulam.profileX s| = Commons.Geometry.Ulam.profileX s :=
        abs_of_nonneg (le_of_lt (Commons.Geometry.Ulam.profileX_pos s hs0))
      have h := (abs_le.mp hle).2
      rwa [hp] at h
    rw [abs_sub_comm] at hle'
    linarith
  -- both arguments `-(z 0)` and `z 1` are at distance `≥ 1/5` from `0`
  have hz0 : (1 : ℝ) / 5 ≤ |-(z 0)| := by
    have h1 : Commons.Geometry.Ulam.profileX s - ρ ≤ |z 0| :=
      htri (z 0) (by simpa [hbase0] using hcoord 0)
    have h2 : (1 : ℝ) / 5 ≤ |z 0| := by linarith
    simpa using h2
  have hz1 : (1 : ℝ) / 5 ≤ |z 1| := by
    have h1 : Commons.Geometry.Ulam.profileX s - ρ ≤ |z 1| :=
      htri (z 1) (by simpa [hbase1] using hcoord 1)
    linarith
  have hhs : |h s| ≤ 1 / 100 := by
    have h := hsmall 0 (by norm_num) s
    simpa [iteratedDeriv_zero] using h
  have hhs' : |deriv h s| ≤ 1 / 100 := by
    have h := hsmall 1 (by norm_num) s
    simpa [iteratedDeriv_one] using h
  rw [show (fun w : Work.OddVolterra.St => Work.OddVolterra.Godd n h s w)
      = fun w => GoddDiag n s (h s) (deriv h s) w from
    funext fun w => Godd_eq_GoddDiag n h s w]
  refine gd_GoddDiag_diff n hn s (h s) (deriv h s) z ?_ ?_
  · exact gd_Drad_ne_zero hs0 hsupp hhs hhs' hz0
  · exact gd_Drad_ne_zero hs0 hsupp hhs hhs' hz1

end

end Work.OddExistence.Estimates
