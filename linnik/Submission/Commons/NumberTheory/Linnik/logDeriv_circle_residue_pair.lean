import Mathlib
import Submission.Commons.NumberTheory.Linnik.logDeriv_circle_residue

open Complex Filter Function Metric MeromorphicOn Set Topology
open scoped Real Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Linnik

lemma continuousOn_deriv_div_self {f : ℂ → ℂ} {R : ℝ} (hfdiff : Differentiable ℂ f)
    (hfc : ∀ w : ℂ, ‖w‖ = R → f w ≠ 0) :
    ContinuousOn (fun w : ℂ => deriv f w / f w) (sphere (0 : ℂ) R) := by
  intro w hw
  have hf_an : AnalyticAt ℂ f w := hfdiff.analyticAt w
  have hder_an : AnalyticAt ℂ (deriv f) w := hf_an.deriv
  have hdiv_an : AnalyticAt ℂ (fun z : ℂ => deriv f z / f z) w :=
    AnalyticAt.div hder_an hf_an (hfc w (mem_sphere_zero_iff_norm.mp hw))
  exact hdiv_an.continuousAt.continuousWithinAt

lemma finsum_sub_div_one_sub {d : ℂ → ℤ} (hsupp : (support d).Finite) (s c : ℂ) :
    ((∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * (1 / (s - u))) -
      (∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * (1 / (c - u)))) =
    (∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * (1 / (s - u) - 1 / (c - u))) := by
  classical
  let S : Finset ℂ := hsupp.toFinset
  let a : ℂ → ℂ := fun u => ((d u : ℤ) : ℂ) * (1 / (s - u))
  let b : ℂ → ℂ := fun u => ((d u : ℤ) : ℂ) * (1 / (c - u))
  let e : ℂ → ℂ := fun u => ((d u : ℤ) : ℂ) * (1 / (s - u) - 1 / (c - u))
  have hsub_a : support a ⊆ (S : Set ℂ) := by
    intro u hu
    have hdne : d u ≠ 0 := by
      intro hd0
      have : a u = 0 := by
        dsimp [a]
        simp [hd0]
      exact hu this
    simpa [S] using (hsupp.mem_toFinset).2 hdne
  have hsub_b : support b ⊆ (S : Set ℂ) := by
    intro u hu
    have hdne : d u ≠ 0 := by
      intro hd0
      have : b u = 0 := by
        dsimp [b]
        simp [hd0]
      exact hu this
    simpa [S] using (hsupp.mem_toFinset).2 hdne
  have hsub_e : support e ⊆ (S : Set ℂ) := by
    intro u hu
    have hdne : d u ≠ 0 := by
      intro hd0
      have : e u = 0 := by
        dsimp [e]
        simp [hd0]
      exact hu this
    simpa [S] using (hsupp.mem_toFinset).2 hdne
  calc
    (∑ᶠ u : ℂ, a u) - (∑ᶠ u : ℂ, b u) = (∑ u ∈ S, a u) - (∑ u ∈ S, b u) := by
      rw [finsum_eq_sum_of_support_subset a hsub_a]
      rw [finsum_eq_sum_of_support_subset b hsub_b]
    _ = ∑ u ∈ S, (a u - b u) := by
      rw [Finset.sum_sub_distrib]
    _ = ∑ u ∈ S, e u := by
      apply Finset.sum_congr rfl
      intro u hu
      dsimp [a, b, e]
      ring
    _ = (∑ᶠ u : ℂ, e u) := by
      rw [finsum_eq_sum_of_support_subset e hsub_e]

lemma circleIntegral_sub_one_sub {R : ℝ} (hR : 0 ≤ R) {g : ℂ → ℂ}
    (hg : ContinuousOn g (sphere (0 : ℂ) R)) {s c : ℂ} (hsR : ‖s‖ < R) (hcR : ‖c‖ < R) :
    ((∮ w in C(0, R), g w * (1 / (s - w))) -
      (∮ w in C(0, R), g w * (1 / (c - w)))) =
    (∮ w in C(0, R), g w * (1 / (s - w) - 1 / (c - w))) := by
  have hdiv_s : ContinuousOn (fun w : ℂ => (1 : ℂ) / (s - w)) (sphere (0 : ℂ) R) := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact continuousOn_const.sub continuousOn_id
    · intro w hw
      exact sub_ne_zero.mpr (norm_ne_of_lt' (mem_sphere_zero_iff_norm.mp hw) hsR)
  have hdiv_c : ContinuousOn (fun w : ℂ => (1 : ℂ) / (c - w)) (sphere (0 : ℂ) R) := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact continuousOn_const.sub continuousOn_id
    · intro w hw
      exact sub_ne_zero.mpr (norm_ne_of_lt' (mem_sphere_zero_iff_norm.mp hw) hcR)
  have hA_int : CircleIntegrable (fun w : ℂ => g w * (1 / (s - w))) (0 : ℂ) R :=
    (hg.mul hdiv_s).circleIntegrable hR
  have hB_int : CircleIntegrable (fun w : ℂ => g w * (1 / (c - w))) (0 : ℂ) R :=
    (hg.mul hdiv_c).circleIntegrable hR
  calc
    (∮ w in C(0, R), g w * (1 / (s - w))) - (∮ w in C(0, R), g w * (1 / (c - w)))
        = (∮ w in C(0, R), g w * (1 / (s - w)) - g w * (1 / (c - w))) := by
          exact (circleIntegral.integral_sub hA_int hB_int).symm
    _ = (∮ w in C(0, R), g w * (1 / (s - w) - 1 / (c - w))) := by
          refine circleIntegral.integral_congr hR ?_
          intro w hw
          change g w * (1 / (s - w)) - g w * (1 / (c - w)) =
            g w * (1 / (s - w) - 1 / (c - w))
          rw [← mul_sub]

lemma logDeriv_circle_residue_pair_of {f : ℂ → ℂ} {R : ℝ} (hRpos : 0 < R)
    (hfdiff : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    {s c : ℂ} (hsR : ‖s‖ < R) (hcR : ‖c‖ < R)
    (hfs : f s ≠ 0) (hfc0 : f c ≠ 0)
    (hfc : ∀ w : ℂ, ‖w‖ = R → f w ≠ 0) :
    deriv f s / f s - deriv f c / f c =
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (closedBall (0 : ℂ) R)) u : ℤ) : ℂ) * (1 / (s - u) - 1 / (c - u))) -
      (((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) •
        circleIntegral (fun w : ℂ => (deriv f w / f w) * (1 / (s - w) - 1 / (c - w))) (0 : ℂ) R) := by
  classical
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor f (closedBall (0 : ℂ) R) u
  have hfB : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R) := by
    intro z hz
    exact hfdiff.analyticAt z
  have hsupp : (support d).Finite := by
    dsimp [d]
    exact MeromorphicOn.divisor_support_finite_of_subset (f := f) (V := closedBall (0 : ℂ) R)
      hfB.meromorphicOn (isCompact_closedBall (0 : ℂ) R) (by simp)
  have h_s := logDeriv_circle_residue_of (f := f) (R := R) hRpos hfdiff hf0 (s := s) hsR hfs hfc
  have h_c := logDeriv_circle_residue_of (f := f) (R := R) hRpos hfdiff hf0 (s := c) hcR hfc0 hfc
  have hfin := finsum_sub_div_one_sub (d := d) hsupp s c
  have hg_cont : ContinuousOn (fun w : ℂ => deriv f w / f w) (sphere (0 : ℂ) R) :=
    continuousOn_deriv_div_self hfdiff hfc
  have hint := circleIntegral_sub_one_sub hRpos.le (g := fun w : ℂ => deriv f w / f w) hg_cont hsR hcR
  calc
    deriv f s / f s - deriv f c / f c
        = ((∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * (1 / (s - u))) -
            (((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) •
              (∮ w in C(0, R), (deriv f w / f w) * (1 / (s - w))))) -
          ((∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * (1 / (c - u))) -
            (((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) •
              (∮ w in C(0, R), (deriv f w / f w) * (1 / (c - w))))) := by
            rw [h_s, h_c]
    _ = ((∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * (1 / (s - u))) - (∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * (1 / (c - u)))) -
          ((((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) •
              (∮ w in C(0, R), (deriv f w / f w) * (1 / (s - w)))) -
            (((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) •
              (∮ w in C(0, R), (deriv f w / f w) * (1 / (c - w))))) := by
            rw [smul_eq_mul]
            ring
    _ = (∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * (1 / (s - u) - 1 / (c - u))) -
          (((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) •
            (∮ w in C(0, R), (deriv f w / f w) * (1 / (s - w) - 1 / (c - w)))) := by
            rw [← smul_sub]
            rw [hfin, hint]

/-- log-derivative circle residue identity for two interior points of the completed
Dirichlet L-function (difference form). -/
theorem logDeriv_circle_residue_pair {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (s c : ℂ) (R : ℝ)
    (hRpos : 0 < R) (hsR : ‖s‖ < R) (hcR : ‖c‖ < R)
    (hΛs : DirichletCharacter.completedLFunction χ s ≠ 0)
    (hΛc : DirichletCharacter.completedLFunction χ c ≠ 0)
    (hcirc : ∀ w : ℂ, ‖w‖ = R → DirichletCharacter.completedLFunction χ w ≠ 0) :
    deriv (DirichletCharacter.completedLFunction χ) s /
        DirichletCharacter.completedLFunction χ s -
      deriv (DirichletCharacter.completedLFunction χ) c /
        DirichletCharacter.completedLFunction χ c =
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) - 1 / (c - u))) -
      (((1 : ℂ) / (2 * (Real.pi : ℂ) * Complex.I)) •
        circleIntegral (fun w : ℂ =>
          (deriv (DirichletCharacter.completedLFunction χ) w /
            DirichletCharacter.completedLFunction χ w) *
            (1 / (s - w) - 1 / (c - w))) 0 R) := by
  let f : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hfdiff : Differentiable ℂ f := by
    dsimp [f]
    exact DirichletCharacter.differentiable_completedLFunction hχ
  have hf0 : f 0 ≠ 0 := by
    dsimp [f]
    exact Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero χ hχ hχprim
  have hfs : f s ≠ 0 := by simpa [f] using hΛs
  have hfc0 : f c ≠ 0 := by simpa [f] using hΛc
  have hfcirc : ∀ w : ℂ, ‖w‖ = R → f w ≠ 0 := by
    intro w hw
    simpa [f] using hcirc w hw
  have h := logDeriv_circle_residue_pair_of (f := f) (R := R) hRpos hfdiff hf0 (s := s) (c := c)
    hsR hcR hfs hfc0 hfcirc
  simpa [f] using h

end Commons.NumberTheory.Linnik
