import Mathlib
import Submission.Work.Drive.liftedOPrime
import Submission.Work.Drive.oPrime_directWitness
import Submission.Commons.Analysis.Analytic.finite_zeros_of_analytic_periodic
import Submission.Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul

namespace Work.Drive

open Filter
open scoped Topology
open LeanEval.KnotTheory.Quadrisecant

/-- A point lying in the open segment from `x` to `y` differs from `x` by a positive
multiple of the difference `y - x`. -/
private lemma sub_eq_smul_sub_of_mem_openSegment {x y z : Space}
    (h : z ∈ openSegment ℝ x y) : ∃ θ : ℝ, 0 < θ ∧ z - x = θ • (y - x) := by
  rw [openSegment_eq_image] at h
  obtain ⟨θ, hθ, hz⟩ := h
  refine ⟨θ, hθ.1, ?_⟩
  rw [← hz]
  show ((1 - θ) • x + θ • y) - x = θ • (y - x)
  module

/-- The `cross3` of a point of the open segment from `x` to `y` (with `x` subtracted) and
the chord direction vanishes: the three points are collinear. -/
private lemma cross3_sub_eq_zero_of_mem_openSegment {x y z : Space}
    (h : z ∈ openSegment ℝ x y) : cross3 (z - x) (y - x) = 0 := by
  obtain ⟨θ, _hθ, hz⟩ := sub_eq_smul_sub_of_mem_openSegment h
  rw [hz, cross3_smul_left, cross3_self, smul_zero]

/-- The squared distance of the knot `r` from the affine line through `A` with direction `v`
(with `v = 0` read as `A` itself) is analytic on `ℝ`. -/
private lemma analyticOnNhd_cross3_sq {r : ℝ → Space} (hr : IsSmoothKnot r) (A v : Space) :
    AnalyticOnNhd ℝ (fun t : ℝ => ‖cross3 (r t - A) v‖ ^ 2) Set.univ := by
  have hG : ContDiff ℝ ⊤ (fun t : ℝ => (r t - A, v)) :=
    (hr.smooth.sub contDiff_const).prodMk contDiff_const
  have hc : ContDiff ℝ ⊤ (fun p : Space × Space => cross3 p.1 p.2) := by
    simpa [cross3] using Commons.Analysis.CrossProduct.cross3_contDiff
  have hcomp : ContDiff ℝ ⊤ (fun t : ℝ => cross3 (r t - A) v) := hc.comp hG
  have hns : ContDiff ℝ ⊤ (fun x : Space => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  exact contDiff_omega_iff_analyticOnNhd.mp (hns.comp hcomp)

/-- The same expression is `period`-periodic. -/
private lemma periodic_cross3_sq {r : ℝ → Space} (hr : IsSmoothKnot r) (A v : Space) :
    Function.Periodic (fun t : ℝ => ‖cross3 (r t - A) v‖ ^ 2) period := by
  intro t
  show ‖cross3 (r (t + period) - A) v‖ ^ 2 = ‖cross3 (r t - A) v‖ ^ 2
  rw [hr.periodic t]

/-- If `s ↦ cross3 (r s - A) v` vanishes in a neighbourhood of `t`, then
`cross3 (deriv r t) v = 0`. -/
private lemma cross3_deriv_eq_zero_of_eventuallyEq {r : ℝ → Space} (hr : IsSmoothKnot r)
    (A v : Space) {t : ℝ}
    (hevent : (fun s : ℝ => cross3 (r s - A) v) =ᶠ[𝓝 t] (fun _ : ℝ => (0 : Space))) :
    cross3 (deriv r t) v = 0 := by
  have hu : HasDerivAt (fun s : ℝ => r s - A) (deriv r t) t :=
    ((hr.smooth.differentiable (by simp)).differentiableAt).hasDerivAt.sub_const A
  have hv0 : HasDerivAt (fun _ : ℝ => v) (0 : Space) t := hasDerivAt_const t v
  have hd : HasDerivAt (fun s : ℝ => cross3 (r s - A) v) (cross3 (deriv r t) v) t := by
    have h := Commons.Analysis.CrossProduct.hasDerivAt_cross3 (fun s : ℝ => r s - A)
      (fun _ : ℝ => v) hu hv0
    simpa [cross3, cross3_zero_right] using h
  have hd0 : HasDerivAt (fun _ : ℝ => (0 : Space)) (0 : Space) t := hasDerivAt_const t 0
  exact (hd0.unique (hd.congr_of_eventuallyEq hevent.symm)).symm

/-- **Finitely many middles on a chord.**  For a smooth knot `r` with no inflection points
(velocity and acceleration linearly independent at every parameter) and any two parameters
`a b`, only finitely many parameters `m` put `r m` strictly inside the chord from `r a` to
`r b`.

(Proof: the squared distance to the line through the two chord endpoints is a real-analytic,
`period`-periodic function of the parameter; being analytic and periodic it either has
finitely many zeros in one period or vanishes identically, and the second alternative forces
the whole knot onto the chord line, where velocity and acceleration are both parallel and
hence linearly dependent, contradicting the no-inflection hypothesis.) -/
theorem finite_middles_of_chord {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    (a b : AddCircle period) :
    {m : AddCircle period | IsMiddleOnChord r a b m}.Finite := by
  classical
  let A : Space := knotMap r a
  let B : Space := knotMap r b
  let v : Space := B - A
  change {m : AddCircle period | knotMap r m ∈ openSegment ℝ A B}.Finite
  by_cases hv : v = 0
  · -- the chord is degenerate: `r a = r b`
    have hBA : B = A := sub_eq_zero.mp hv
    have hsub : {m : AddCircle period | knotMap r m ∈ openSegment ℝ A B} ⊆ {a} := by
      intro m hm
      have hmA : knotMap r m = A := by
        have h1 : knotMap r m ∈ openSegment ℝ A A := by
          simpa only [hBA, Set.mem_ofPred_eq] using hm
        rw [openSegment_same] at h1
        simpa using h1
      have hma : m = a := knotMap_injective hr (by rw [hmA])
      simpa using hma
    exact Set.Finite.subset (Set.finite_singleton a) hsub
  · have hvne : v ≠ 0 := hv
    let F : ℝ → ℝ := fun t => ‖cross3 (r t - A) v‖ ^ 2
    have hFan : AnalyticOnNhd ℝ F Set.univ := analyticOnNhd_cross3_sq hr A v
    have hFper : Function.Periodic F period := periodic_cross3_sq hr A v
    by_cases hne : ∃ x ∈ Set.Icc (0 : ℝ) period, F x ≠ 0
    · -- analytic alternative: finitely many zeros in one period
      have hfin :=
        Commons.Analysis.Analytic.finite_zeros_of_analytic_periodic period_pos hFan hFper hne
      refine Set.Finite.subset (hfin.image (fun t : ℝ => (t : AddCircle period))) ?_
      intro m hm
      obtain ⟨t, ht, htm⟩ := knotMap_representative m
      have hrt : knotMap r m = r t := by rw [← htm]; exact knotMap_coe r ht
      have hcross : cross3 (r t - A) v = 0 := by
        have hz : r t ∈ openSegment ℝ A B := by rw [← hrt]; exact hm
        exact cross3_sub_eq_zero_of_mem_openSegment hz
      refine ⟨t, ⟨⟨ht.1, ht.2.le⟩, ?_⟩, htm⟩
      dsimp only [F]
      rw [hcross]
      simp
    · -- vanishing alternative: the knot lies on the chord line, contradicting `hinfl`
      push Not at hne
      exfalso
      have hcross_zero : ∀ t ∈ Set.Ioo (0 : ℝ) period, cross3 (r t - A) v = 0 := by
        intro t ht
        have hFt : F t = 0 := hne t ⟨ht.1.le, ht.2.le⟩
        have h1 : ‖cross3 (r t - A) v‖ = 0 := sq_eq_zero_iff.mp hFt
        exact norm_eq_zero.mp h1
      have hd1 : ∀ t ∈ Set.Ioo (0 : ℝ) period, cross3 (deriv r t) v = 0 := by
        intro t ht
        refine cross3_deriv_eq_zero_of_eventuallyEq hr A v ?_
        filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
        exact hcross_zero s hs
      have ht0 : (0 : ℝ) < period / 2 := by linarith [period_pos]
      have ht1 : period / 2 < period := by linarith [period_pos]
      have ht0mem : period / 2 ∈ Set.Ioo (0 : ℝ) period := ⟨ht0, ht1⟩
      have hd2 : cross3 (deriv (deriv r) (period / 2)) v = 0 := by
        have hderiv : HasDerivAt (fun s : ℝ => deriv r s) (deriv (deriv r) (period / 2))
            (period / 2) := by
          have h1 : (⊤ : WithTop ℕ∞) + 1 = ⊤ := by simp
          have hvel : ContDiff ℝ ⊤ (deriv r) := h1 ▸ hr.smooth.deriv'
          exact ((hvel.differentiable (by simp)).differentiableAt).hasDerivAt
        have hv0 : HasDerivAt (fun _ : ℝ => v) (0 : Space) (period / 2) :=
          hasDerivAt_const _ v
        have hd : HasDerivAt (fun s : ℝ => cross3 (deriv r s) v)
            (cross3 (deriv (deriv r) (period / 2)) v) (period / 2) := by
          have h := Commons.Analysis.CrossProduct.hasDerivAt_cross3 (fun s : ℝ => deriv r s)
            (fun _ : ℝ => v) hderiv hv0
          simpa [cross3, cross3_zero_right] using h
        have hevent : (fun s : ℝ => cross3 (deriv r s) v) =ᶠ[𝓝 (period / 2)]
            (fun _ : ℝ => (0 : Space)) := by
          filter_upwards [isOpen_Ioo.mem_nhds ht0mem] with s hs
          exact hd1 s hs
        have hd0 : HasDerivAt (fun _ : ℝ => (0 : Space)) (0 : Space) (period / 2) :=
          hasDerivAt_const _ _
        exact (hd0.unique (hd.congr_of_eventuallyEq hevent.symm)).symm
      have hLI := hinfl (period / 2)
      have hr' : deriv r (period / 2) ≠ 0 := hr.regular (period / 2)
      have hd1' : cross3 (deriv r (period / 2)) v = 0 := hd1 (period / 2) ht0mem
      rcases (Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul (deriv r (period / 2)) v).mp
        hd1' with hz | ⟨s, hs⟩
      · exact hr' hz
      · have hsne : s ≠ 0 := by
          rintro rfl
          rw [zero_smul] at hs
          exact hvne hs
        have hα : deriv r (period / 2) = s⁻¹ • v := by
          rw [hs, smul_smul, inv_mul_cancel₀ hsne, one_smul]
        rcases
          (Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul
            (deriv (deriv r) (period / 2)) v).mp hd2 with hz2 | ⟨s', hs'⟩
        · exact (LinearIndependent.pair_iff' hr').mp hLI 0 (by rw [zero_smul, hz2])
        · have hs'ne : s' ≠ 0 := by
            rintro rfl
            rw [zero_smul] at hs'
            exact hvne hs'
          have hβ : deriv (deriv r) (period / 2) = s'⁻¹ • v := by
            rw [hs', smul_smul, inv_mul_cancel₀ hs'ne, one_smul]
          refine (LinearIndependent.pair_iff' hr').mp hLI (s'⁻¹ * s) ?_
          rw [hα, hβ, smul_smul, mul_assoc, mul_inv_cancel₀ hsne, mul_one]

end Work.Drive
