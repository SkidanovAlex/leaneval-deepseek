import Mathlib
import Submission.Work.LinnikAreas.DhRepel.l52Hyp_defs
import Submission.Commons.NumberTheory.Linnik.partialFraction_eq
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_ne_zero_of_one_lt_re
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_one_sub
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_conj

/-!
# The limit of the truncated symmetric partial-fraction sum `kernSum`

For a non-principal primitive character `χ` mod `N` and a point `s` with `1 < Re s` we prove that

`kernSum χ s R = Σ_{|u| ≤ R} ord(u)·(Re (1/(s-u)) + Re (1/(conj s + u - 1)))`

tends, as `R → ∞`, to `2·Re (Λ'/Λ)(s) + log N`, where `Λ = completedLFunction χ`.

The proof is a two-point Hadamard partial fraction.  Writing `w = 1 - conj s`, the kernel is a
*difference* of two simple poles:

`Re (1/(s-u)) + Re (1/(conj s + u - 1)) = Re (1/(s-u) - 1/(w-u))`,

so the recentred partial-fraction identity (the difference of `partialFraction_eq` at `s` and at
`w`, in which the constants `Λ'(0)/Λ(0)` cancel) gives the limit
`Re ((Λ'/Λ)(s) - (Λ'/Λ)(w))`.  Finally the logarithmic-derivative functional equation
`logDeriv Λ (1 - z) = -log N - logDeriv Λ (conj z)` (functional equation combined with the
conjugation symmetry `Λ(χ⁻¹, conj z) = conj (Λ(χ, z))`) gives
`Re ((Λ'/Λ)(w)) = -log N - Re ((Λ'/Λ)(s))`, whence the claim.
-/

open Complex DirichletCharacter Metric Filter
open scoped Real Topology BigOperators

namespace Work.LinnikAreas.DhRepel

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Finite support of `u ↦ d u · (1/(z-u) - 1/(z'-u))`. -/
private lemma finiteSupport_kernel_sub {d : ℂ → ℤ} (hd : (Function.support d).Finite) (z z' : ℂ) :
    Function.HasFiniteSupport (fun u : ℂ => ((d u : ℤ) : ℂ) * (1 / (z - u) - 1 / (z' - u))) :=
  hd.subset (by
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by rw [h0]; simp))

/-- Finite support of `u ↦ d u · (1/(z-u) + 1/u)`. -/
private lemma finiteSupport_kernel_add {d : ℂ → ℤ} (hd : (Function.support d).Finite) (z : ℂ) :
    Function.HasFiniteSupport (fun u : ℂ => ((d u : ℤ) : ℂ) * (1 / (z - u) + 1 / u)) :=
  hd.subset (by
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by rw [h0]; simp))

theorem tendsto_kernSum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto (fun R : ℝ => kernSum χ s R) Filter.atTop
      (nhds (2 * (logDeriv (DirichletCharacter.completedLFunction χ) s).re + Real.log N)) := by
  classical
  set w : ℂ := 1 - (starRingEnd ℂ) s with hwdef
  have hΛdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction hχ
  have hΛs : DirichletCharacter.completedLFunction χ s ≠ 0 :=
    Commons.NumberTheory.DirichletCharacter.completedLFunction_ne_zero_of_one_lt_re χ hs
  have hwre : w.re < 0 := by
    rw [hwdef]
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have hΛw : DirichletCharacter.completedLFunction χ w ≠ 0 := by
    intro h0
    have h1 := (Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim w h0).1
    linarith
  have h1w : 1 - w = (starRingEnd ℂ) s := by rw [hwdef]; ring
  have hΛinv : DirichletCharacter.completedLFunction χ⁻¹ (1 - w) ≠ 0 := by
    rw [h1w]
    exact Commons.NumberTheory.DirichletCharacter.completedLFunction_ne_zero_of_one_lt_re χ⁻¹
      (by simpa [Complex.conj_re] using hs)
  -- ### Hadamard partial fractions at `s` and at `w`
  have hA := Commons.NumberTheory.Linnik.partialFraction_eq χ hχ hχprim s hΛs
  have hB := Commons.NumberTheory.Linnik.partialFraction_eq χ hχ hχprim w hΛw
  have hdiff0 : Filter.Tendsto (fun R : ℝ =>
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u))
        - (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (w - u) + 1 / u)))
      Filter.atTop (nhds (logDeriv (DirichletCharacter.completedLFunction χ) s
        - logDeriv (DirichletCharacter.completedLFunction χ) w)) := by
    have h := hA.sub hB
    have hlim : (deriv (DirichletCharacter.completedLFunction χ) s /
          DirichletCharacter.completedLFunction χ s
          - deriv (DirichletCharacter.completedLFunction χ) 0 /
            DirichletCharacter.completedLFunction χ 0)
        - (deriv (DirichletCharacter.completedLFunction χ) w /
            DirichletCharacter.completedLFunction χ w
            - deriv (DirichletCharacter.completedLFunction χ) 0 /
              DirichletCharacter.completedLFunction χ 0)
        = logDeriv (DirichletCharacter.completedLFunction χ) s
          - logDeriv (DirichletCharacter.completedLFunction χ) w := by
      simp only [← logDeriv_apply]
      ring
    rw [hlim] at h
    exact h
  -- ### finite support of the divisor
  have hdivfin : ∀ R : ℝ, (Function.support (fun u : ℂ =>
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 R) u)).Finite := by
    intro R
    exact MeromorphicOn.divisor_support_finite_of_subset
      (f := DirichletCharacter.completedLFunction χ)
      (U := Metric.closedBall (0 : ℂ) R) (V := Metric.closedBall (0 : ℂ) R)
      (fun z _ => (hΛdiff.analyticAt z).meromorphicAt) (isCompact_closedBall 0 R) subset_rfl
  -- ### the recentred kernel is a single finsum
  have hS_eq : ∀ R : ℝ,
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u))
        - (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (w - u) + 1 / u))
      = ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) - 1 / (w - u)) := by
    intro R
    rw [← finsum_sub_distrib (finiteSupport_kernel_add (hdivfin R) s)
      (finiteSupport_kernel_add (hdivfin R) w)]
    exact finsum_congr (fun u => by ring)
  have hS : Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) - 1 / (w - u)))
      Filter.atTop (nhds (logDeriv (DirichletCharacter.completedLFunction χ) s
        - logDeriv (DirichletCharacter.completedLFunction χ) w)) :=
    hdiff0.congr' (Eventually.of_forall hS_eq)
  have hSre : Filter.Tendsto (fun R : ℝ =>
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) - 1 / (w - u))).re)
      Filter.atTop (nhds ((logDeriv (DirichletCharacter.completedLFunction χ) s
        - logDeriv (DirichletCharacter.completedLFunction χ) w).re)) :=
    (Complex.continuous_re.tendsto _).comp hS
  -- ### identify `kernSum` with the real part of that finsum
  have hkern : ∀ R : ℝ, kernSum χ s R =
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) - 1 / (w - u))).re := by
    intro R
    have hfin : Function.HasFiniteSupport (fun u : ℂ =>
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) - 1 / (w - u))) :=
      finiteSupport_kernel_sub (hdivfin R) s w
    simp only [kernSum]
    rw [show (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) - 1 / (w - u))).re
        = Complex.reCLM.toAddMonoidHom
            (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) - 1 / (w - u))) from rfl]
    rw [map_finsum Complex.reCLM.toAddMonoidHom hfin]
    refine finsum_congr (fun u => ?_)
    have h1 : 1 / (w - u) = -(1 / ((starRingEnd ℂ) s + u - 1)) := by
      have hw' : w - u = -((starRingEnd ℂ) s + u - 1) := by rw [hwdef]; ring
      rw [hw', one_div, inv_neg, ← one_div]
    rw [h1, show (1 : ℂ) / (s - u) - -(1 / ((starRingEnd ℂ) s + u - 1))
        = 1 / (s - u) + 1 / ((starRingEnd ℂ) s + u - 1) from by ring]
    show ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R) u : ℤ) : ℝ)
          * ((1 / (s - u)).re + (1 / ((starRingEnd ℂ) s + u - 1)).re)
        = ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R) u : ℤ) : ℂ))
          * (1 / (s - u) + 1 / ((starRingEnd ℂ) s + u - 1))).re
    rw [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_re]
    ring
  -- ### the functional equation at `w`
  have hQ : logDeriv (DirichletCharacter.completedLFunction χ) w
      = -((Real.log (N : ℝ) : ℂ))
        - star (logDeriv (DirichletCharacter.completedLFunction χ) s) := by
    have hfe := Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_one_sub
      χ hχprim (s := w) hΛw hΛinv
    have hcj : logDeriv (DirichletCharacter.completedLFunction χ⁻¹) ((starRingEnd ℂ) s)
        = star (logDeriv (DirichletCharacter.completedLFunction χ) s) :=
      Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_conj χ hχ s
    rw [hfe, h1w, hcj]
  have hre : (logDeriv (DirichletCharacter.completedLFunction χ) s
      - logDeriv (DirichletCharacter.completedLFunction χ) w).re
      = 2 * (logDeriv (DirichletCharacter.completedLFunction χ) s).re + Real.log N := by
    rw [hQ]
    simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]
    simp [Complex.conj_re]
    ring
  rw [hre] at hSre
  exact hSre.congr' (Eventually.of_forall (fun R => (hkern R).symm))

end Work.LinnikAreas.DhRepel
