import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.chebyshevPsiChi_explicit_formula_mult

open Complex MeasureTheory intervalIntegral Filter
open scoped Real Topology BigOperators

set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

/-! ## Auxiliary contour integrals for the `1/s`-free kernel `x^s` -/

/-- The contour integral of the entire function `s ↦ x^s` over a rectangle vanishes. -/
lemma rectInt_cpow_eq_zero {x : ℝ} (hx : 0 < x) {z w : ℂ} :
    rectInt z w (fun s : ℂ => (x : ℂ) ^ s) = 0 :=
  rectInt_eq_zero_of_differentiableOn
    (fun s _ => ((cpow_differentiable_of_pos hx) s).differentiableWithinAt)

/-- The contour integral of the "`1/s`-free" kernel `(1/(s-u)+1/u) x^s` when `u ≠ 0` lies
strictly inside the rectangle: `x^u · 2πi`. -/
lemma rectInt_kernel_mul_cpow_inside {x : ℝ} {z w u : ℂ} (hx : 0 < x) (hu0 : u ≠ 0)
    (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huin : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im) :
    rectInt z w (fun s => (1 / (s - u) + 1 / u) * (x : ℂ) ^ s) =
      (x : ℂ) ^ u * (2 * (Real.pi : ℂ) * Complex.I) := by
  have hds : Differentiable ℂ (dslope (fun s : ℂ => (x : ℂ) ^ s) u) :=
    dslope_cpow_differentiable hx u
  have hd : DifferentiableOn ℂ
      (fun s : ℂ => dslope (fun t : ℂ => (x : ℂ) ^ t) u s + (x : ℂ) ^ s / u)
      (rectSet z w) := by
    apply DifferentiableOn.add
    · exact fun s _ => (hds s).differentiableWithinAt
    · exact DifferentiableOn.div
        (fun s _ => ((cpow_differentiable_of_pos hx) s).differentiableWithinAt)
        (differentiableOn_const u) (fun s _ => hu0)
  have hcont : ContinuousOn
      (fun s : ℂ => dslope (fun t : ℂ => (x : ℂ) ^ t) u s + (x : ℂ) ^ s / u)
      (rectSet z w) := hd.continuousOn
  have hcont_div : ContinuousOn (fun s : ℂ => ((x : ℂ) ^ u) / (s - u)) {s : ℂ | s ≠ u} :=
    continuousOn_const.div (by fun_prop) (fun s hs => sub_ne_zero.mpr hs)
  have hcongr : rectInt z w (fun s => (1 / (s - u) + 1 / u) * (x : ℂ) ^ s) =
      rectInt z w (fun s => ((x : ℂ) ^ u) / (s - u) +
        (dslope (fun t : ℂ => (x : ℂ) ^ t) u s + (x : ℂ) ^ s / u)) := by
    apply rectInt_congr_boundary'
    intro s hs
    have hsune : s ≠ u := ne_of_mem_rectBoundary_of_inside huin hs
    rw [dslope_cpow_eq (x := x) (u := u) (s := s) hsune]
    field_simp
    ring
  obtain ⟨a1, a2, a3, a4⟩ := edgeIntegrable_of_continuousOn_ne huin hcont_div
  obtain ⟨d1, d2, d3, d4⟩ := edgeIntegrable_of_continuousOn hcont
  rw [hcongr, rectInt_add'' a1 d1 a2 d2 a3 d3 a4 d4,
      rectInt_eq_zero_of_differentiableOn hd,
      rectInt_const_div_sub_inside ((x : ℂ) ^ u) hzre hzim huin]
  ring

/-- The contour integral of `(1/(s-u)+1/u) x^s` when `u` lies outside the rectangle: `0`. -/
lemma rectInt_kernel_mul_cpow_outside {x : ℝ} {z w u : ℂ} (hx : 0 < x) (hu0 : u ≠ 0)
    (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huout : u.re < z.re ∨ w.re < u.re ∨ u.im < z.im ∨ w.im < u.im) :
    rectInt z w (fun s => (1 / (s - u) + 1 / u) * (x : ℂ) ^ s) = 0 := by
  have hne : ∀ s ∈ rectSet z w, s - u ≠ 0 := by
    intro s hs hzero
    rcases huout with h | h | h | h
    · have h1 := (Complex.mem_reProdIm.mp hs).1
      rw [Set.uIcc_of_le (le_of_lt hzre)] at h1
      rw [sub_eq_zero.mp hzero] at h1
      linarith [h1.1]
    · have h1 := (Complex.mem_reProdIm.mp hs).1
      rw [Set.uIcc_of_le (le_of_lt hzre)] at h1
      rw [sub_eq_zero.mp hzero] at h1
      linarith [h1.2]
    · have h1 := (Complex.mem_reProdIm.mp hs).2
      rw [Set.uIcc_of_le (le_of_lt hzim)] at h1
      rw [sub_eq_zero.mp hzero] at h1
      linarith [h1.1]
    · have h1 := (Complex.mem_reProdIm.mp hs).2
      rw [Set.uIcc_of_le (le_of_lt hzim)] at h1
      rw [sub_eq_zero.mp hzero] at h1
      linarith [h1.2]
  have hd : DifferentiableOn ℂ
      (fun s : ℂ => (1 / (s - u) + 1 / u) * (x : ℂ) ^ s) (rectSet z w) := by
    apply DifferentiableOn.mul
    · apply DifferentiableOn.add
      · exact DifferentiableOn.div (differentiableOn_const (1 : ℂ)) (by fun_prop) hne
      · exact differentiableOn_const (1 / u)
    · exact fun s _ => ((cpow_differentiable_of_pos hx) s).differentiableWithinAt
  exact rectInt_eq_zero_of_differentiableOn hd

/-- The contour integral of a finite linear combination of the `1/s`-free kernels. -/
lemma rectInt_kernel_finset_mul_cpow {x : ℝ} (hx : 0 < x) {z w : ℂ} (hzre : z.re < w.re)
    (hzim : z.im < w.im)
    (S : Finset ℂ) (hS_ne : ∀ u ∈ S, u ≠ 0) (hS_nb : ∀ u ∈ S, u ∉ rectBoundary z w)
    (d : ℂ → ℂ) :
    rectInt z w (fun s => (∑ u ∈ S, d u * (1 / (s - u) + 1 / u)) * (x : ℂ) ^ s) =
      ∑ u ∈ S, d u * (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then
        (x : ℂ) ^ u * (2 * (Real.pi : ℂ) * Complex.I) else 0) := by
  have hcont : ∀ u ∈ S, ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ =>
      d u * ((1 / (s - u) + 1 / u) * (x : ℂ) ^ s)) s := by
    intro u hu s hs
    have hsu : s - u ≠ 0 := sub_ne_zero.mpr (fun h => hS_nb u hu (h ▸ hs))
    exact ContinuousAt.mul continuousAt_const
      ((ContinuousAt.add (ContinuousAt.div continuousAt_const
        (continuousAt_id.sub continuousAt_const) hsu) continuousAt_const).mul
        ((cpow_differentiable_of_pos hx) s).continuousAt)
  have hsplit : rectInt z w (fun s => (∑ u ∈ S, d u * (1 / (s - u) + 1 / u)) * (x : ℂ) ^ s) =
      rectInt z w (fun s => ∑ u ∈ S, d u * ((1 / (s - u) + 1 / u) * (x : ℂ) ^ s)) := by
    apply rectInt_congr_boundary'
    intro s hs
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun u hu => by ring)
  rw [hsplit, rectInt_finset_sum_of_boundary S hcont]
  refine Finset.sum_congr rfl ?_
  intro u hu
  have h1 : rectInt z w (fun s : ℂ => d u * ((1 / (s - u) + 1 / u) * (x : ℂ) ^ s)) =
      d u * rectInt z w (fun s : ℂ => (1 / (s - u) + 1 / u) * (x : ℂ) ^ s) :=
    rectInt_const_mul' (d u) _
  rw [h1]
  by_cases huin : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
  · rw [if_pos huin, rectInt_kernel_mul_cpow_inside hx (hS_ne u hu) hzre hzim huin]
  · rw [if_neg huin, rectInt_kernel_mul_cpow_outside hx (hS_ne u hu) hzre hzim
      (outside_of_not_inside hzre hzim huin (hS_nb u hu)), mul_zero]

theorem rectInt_logDeriv_completed_cpow_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {x : ℝ} (hx : 0 < x)
    {z w : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (h0in : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im)
    (hins : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
      z.re < ρ.re ∧ ρ.re < w.re)
    (hnz : ∀ s ∈ Commons.NumberTheory.DirichletCharacter.rectBoundary z w,
      DirichletCharacter.completedLFunction χ s ≠ 0) :
    Commons.NumberTheory.DirichletCharacter.rectInt z w
        (fun s => logDeriv (DirichletCharacter.completedLFunction χ) s * (x : ℂ) ^ s) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        ∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then
            ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) *
              (x : ℂ) ^ ρ else 0) := by

  obtain ⟨c, hc0, hc⟩ := partialFraction_limit_bound χ hχ hχprim
  have hzre' : z.re < 0 := h0in.1
  have hwre' : 0 < w.re := h0in.2.1
  have hzim' : z.im < 0 := h0in.2.2.1
  have hwim' : 0 < w.im := h0in.2.2.2
  have hnorm_le : ∀ s ∈ rectSet z w,
      ‖s‖ ≤ |z.re| + |w.re| + |z.im| + |w.im| + 1 := by
    intro s hs
    obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hs
    rw [Set.uIcc_of_le (le_of_lt hzre)] at hre
    rw [Set.uIcc_of_le (le_of_lt hzim)] at him
    have h1 : |s.re| ≤ |z.re| + |w.re| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le z.re, hre.1, abs_nonneg w.re]
      · linarith [le_abs_self w.re, hre.2, abs_nonneg z.re]
    have h2 : |s.im| ≤ |z.im| + |w.im| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le z.im, him.1, abs_nonneg w.im]
      · linarith [le_abs_self w.im, him.2, abs_nonneg z.im]
    have h3 : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    linarith
  have hnorm_cpow : ∀ s ∈ rectSet z w, ‖(x : ℂ) ^ s‖ ≤ max (x ^ z.re) (x ^ w.re) := by
    intro s hs
    obtain ⟨hre, -⟩ := Complex.mem_reProdIm.mp hs
    rw [Set.uIcc_of_le (le_of_lt hzre)] at hre
    rw [cpow_norm_ofReal_mul x hx s]
    by_cases h1x : 1 ≤ x
    · exact (Real.rpow_le_rpow_of_exponent_le h1x hre.2).trans (le_max_right _ _)
    · have hb : x ^ s.re ≤ x ^ z.re :=
        Real.rpow_le_rpow_of_exponent_ge hx (le_of_lt (not_le.mp h1x)) hre.1
      exact hb.trans (le_max_left _ _)
  have hinside_norm : ∀ ρ : ℂ, z.re < ρ.re → ρ.re < w.re → z.im < ρ.im → ρ.im < w.im →
      ‖ρ‖ ≤ |z.re| + |w.re| + |z.im| + |w.im| := by
    intro ρ h1 h2 h3 h4
    have hre : |ρ.re| ≤ |z.re| + |w.re| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le z.re, h1, abs_nonneg w.re]
      · linarith [le_abs_self w.re, h2, abs_nonneg z.re]
    have him : |ρ.im| ≤ |z.im| + |w.im| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le z.im, h3, abs_nonneg w.im]
      · linarith [le_abs_self w.im, h4, abs_nonneg z.im]
    have h5 : ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
    linarith
  have hkey : ∀ R : ℝ, 2 ≤ R → |z.re| + |w.re| + |z.im| + |w.im| + 1 ≤ R / 4 →
      ‖rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) s *
          (x : ℂ) ^ s) -
        (2 * (Real.pi : ℂ) * Complex.I) *
          (∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then
              ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) *
                ((x : ℂ) ^ ρ) else 0))‖ ≤
        2 * ((w.re - z.re) + (w.im - z.im)) *
          (c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
            (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) *
          (max (x ^ z.re) (x ^ w.re)) := by
    intro R hR hR4
    let dR : ℂ → ℤ := fun u => MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 R) u
    have hdRfin : dR.support.Finite := by
      simpa only [dR] using
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall (0 : ℂ) R)
    let S : Finset ℂ := hdRfin.toFinset
    have hS_mem : ∀ u : ℂ, u ∈ S ↔ dR u ≠ 0 := fun u => hdRfin.mem_toFinset
    have hS_zero : ∀ u ∈ S, DirichletCharacter.completedLFunction χ u = 0 := by
      intro u hu
      have hnorm : ‖u‖ ≤ R := by
        by_contra hcon
        refine (hS_mem u).mp hu ?_
        dsimp only [dR]
        exact (MeromorphicOn.divisor _ _).apply_eq_zero_of_notMem
          (fun hmem => hcon (by simpa [dist_eq_norm] using hmem))
      refine eq_zero_of_divisor_ne_zero
        (U := Metric.closedBall 0 R)
        (fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z)
        (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hnorm)) ?_
      simpa only [dR] using (hS_mem u).mp hu
    have hS_ne : ∀ u ∈ S, u ≠ 0 := by
      intro u hu h0
      exact Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero χ hχ hχprim
        (h0 ▸ hS_zero u hu)
    have hS_nb : ∀ u ∈ S, u ∉ rectBoundary z w := by
      intro u hu hb
      exact hnz u hb (hS_zero u hu)
    have hS_norm : ∀ u ∈ S, ‖u‖ ≤ R := by
      intro u hu
      by_contra hcon
      have h0 : dR u = 0 := by
        dsimp only [dR]
        exact (MeromorphicOn.divisor _ _).apply_eq_zero_of_notMem
          (fun hmem => hcon (by simpa [dist_eq_norm] using hmem))
      exact (hS_mem u).mp hu h0
    let FR : ℂ → ℂ := fun s => ∑ u ∈ S, ((dR u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)
    let TR : ℂ → ℂ := fun s => logDeriv (DirichletCharacter.completedLFunction χ) s -
      logDeriv (DirichletCharacter.completedLFunction χ) 0 - FR s
    have hFR_eq : ∀ s : ℂ, FR s =
        ∑ᶠ u : ℂ, ((dR u : ℤ) : ℂ) * (1 / (s - u) + 1 / u) := by
      intro s
      dsimp only [FR]
      refine (finsum_eq_sum_of_support_subset _ ?_).symm
      intro u hu
      rw [Function.mem_support] at hu
      exact (hS_mem u).mpr (fun hz => hu (by simp [hz]))
    have hFRint : rectInt z w (fun s => FR s * (x : ℂ) ^ s) =
        ∑ u ∈ S, ((dR u : ℤ) : ℂ) * (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then
          (x : ℂ) ^ u * (2 * (Real.pi : ℂ) * Complex.I) else 0) := by
      have h := rectInt_kernel_finset_mul_cpow (x := x) hx hzre hzim S hS_ne hS_nb
        (fun u => ((dR u : ℤ) : ℂ))
      simpa only [FR] using h
    have hFRfin : (∑ᶠ u : ℂ, ((dR u : ℤ) : ℂ) *
          (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
            then (x : ℂ) ^ u else 0)) =
        ∑ u ∈ S, ((dR u : ℤ) : ℂ) *
          (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
            then (x : ℂ) ^ u else 0) := by
      refine finsum_eq_sum_of_support_subset _ ?_
      intro u hu
      rw [Function.mem_support] at hu
      exact (hS_mem u).mpr (fun hz => hu (by simp [hz]))
    have hFRint' : rectInt z w (fun s => FR s * (x : ℂ) ^ s) =
        (2 * (Real.pi : ℂ) * Complex.I) *
          ∑ᶠ u : ℂ, ((dR u : ℤ) : ℂ) *
            (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
              then (x : ℂ) ^ u else 0) := by
      rw [hFRint, hFRfin, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro u hu
      by_cases huin : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
      · rw [if_pos huin, if_pos huin]; ring
      · rw [if_neg huin, if_neg huin]; ring
    have hdiv_eq : ∀ ρ : ℂ, (z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im) →
        ((dR ρ : ℤ) : ℂ) =
          ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) := by
      intro ρ hρ
      have hρR : ‖ρ‖ ≤ R := le_trans (hinside_norm ρ hρ.1 hρ.2.1 hρ.2.2.1 hρ.2.2.2) (by linarith)
      have h1 : dR ρ = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℤ) := by
        dsimp only [dR]
        exact divisor_eq_analyticOrderNatAt (U := Metric.closedBall 0 R)
          (fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z)
          (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hρR))
      rw [h1]; norm_num
    have hsum_eq : (∑ᶠ u : ℂ, ((dR u : ℤ) : ℂ) *
          (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im
            then (x : ℂ) ^ u else 0)) =
        ∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then
          ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) *
            ((x : ℂ) ^ ρ) else 0) := by
      refine finsum_congr ?_
      intro ρ
      by_cases hρ : z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im
      · rw [if_pos hρ, if_pos hρ, hdiv_eq ρ hρ]
      · rw [if_neg hρ, if_neg hρ, mul_zero]
    have hcontA1 : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ =>
        logDeriv (DirichletCharacter.completedLFunction χ) 0 * (x : ℂ) ^ s) s := by
      intro s hs
      exact continuousAt_const.mul ((cpow_differentiable_of_pos hx) s).continuousAt
    have hFRcont : ∀ s ∈ rectBoundary z w, ContinuousAt FR s := by
      intro s hs
      dsimp only [FR]
      refine tendsto_finsetSum _ ?_
      intro u hu
      have hsu : s - u ≠ 0 := sub_ne_zero.mpr (fun h => hS_nb u hu (h ▸ hs))
      exact ContinuousAt.mul continuousAt_const
        (ContinuousAt.add (ContinuousAt.div continuousAt_const
          (continuousAt_id.sub continuousAt_const) hsu) continuousAt_const)
    have hcontA2 : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ =>
        FR s * (x : ℂ) ^ s) s := by
      intro s hs
      exact (hFRcont s hs).mul ((cpow_differentiable_of_pos hx) s).continuousAt
    have hcontB : ∀ s ∈ rectBoundary z w, ContinuousAt (fun s : ℂ =>
        TR s * (x : ℂ) ^ s) s := by
      intro s hs
      have hΛs : DirichletCharacter.completedLFunction χ s ≠ 0 := hnz s hs
      have han : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) s :=
        (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt s
      have hlog : ContinuousAt (fun s : ℂ =>
          logDeriv (DirichletCharacter.completedLFunction χ) s) s := by
        rw [show (fun s : ℂ => logDeriv (DirichletCharacter.completedLFunction χ) s) =
            fun s => deriv (DirichletCharacter.completedLFunction χ) s /
              DirichletCharacter.completedLFunction χ s from
          funext (fun s => logDeriv_apply _ _)]
        exact (han.deriv.continuousAt).div han.continuousAt hΛs
      exact ((hlog.sub continuousAt_const).sub (hFRcont s hs)).mul
        ((cpow_differentiable_of_pos hx) s).continuousAt
    obtain ⟨a1, a2, a3, a4⟩ := intervalIntegrable_of_boundary_continuousAt hcontA1
    obtain ⟨a1', a2', a3', a4'⟩ := intervalIntegrable_of_boundary_continuousAt hcontA2
    obtain ⟨b1, b2, b3, b4⟩ := intervalIntegrable_of_boundary_continuousAt hcontB
    have htail_bound : ‖rectInt z w (fun s => TR s * (x : ℂ) ^ s)‖ ≤
        2 * ((w.re - z.re) + (w.im - z.im)) *
          (c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
            (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) *
          (max (x ^ z.re) (x ^ w.re)) := by
      rw [show 2 * ((w.re - z.re) + (w.im - z.im)) *
            (c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
              (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) *
          (max (x ^ z.re) (x ^ w.re)) =
          2 * ((w.re - z.re) + (w.im - z.im)) *
            ((c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
              (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) *
            (max (x ^ z.re) (x ^ w.re))) by ring]
      refine norm_rectInt_le (M := (c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
        (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) *
        (max (x ^ z.re) (x ^ w.re))) hzre hzim hcontB ?_
      intro s hs
      have hnorm_s : ‖s‖ ≤ |z.re| + |w.re| + |z.im| + |w.im| + 1 :=
        hnorm_le s (rectBoundary_subset_rectSet hzre hzim hs)
      have htail_le := hc s (hnz s hs) R hR (by linarith [hnorm_s, hR4])
      have hlog0 : (0 : ℝ) ≤ Real.log (R + 2) + Real.log (N : ℝ) + 2 := by
        have h3 : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg (by
          exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
        linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ R + 2)]
      have hnorm_h := hnorm_cpow s (rectBoundary_subset_rectSet hzre hzim hs)
      rw [norm_mul]
      have htr : TR s = logDeriv (DirichletCharacter.completedLFunction χ) s -
          logDeriv (DirichletCharacter.completedLFunction χ) 0 -
          ∑ᶠ u : ℂ, ((dR u : ℤ) : ℂ) * (1 / (s - u) + 1 / u) := by
        simp only [TR]
        rw [hFR_eq s]
      have e1 : ‖TR s‖ ≤ c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
          (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by
        rw [htr]
        calc ‖logDeriv (DirichletCharacter.completedLFunction χ) s -
              logDeriv (DirichletCharacter.completedLFunction χ) 0 -
              ∑ᶠ u : ℂ, ((dR u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)‖
              ≤ c * ‖s‖ * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := htail_le
          _ ≤ c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
              (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by
                have hmul : c * ‖s‖ ≤ c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) :=
                  mul_le_mul_of_nonneg_left hnorm_s hc0
                exact div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hmul hlog0) (by linarith)
      have h2 : (0 : ℝ) ≤ c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
          (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by positivity
      have h3' : (0 : ℝ) ≤ max (x ^ z.re) (x ^ w.re) :=
        le_trans (Real.rpow_nonneg hx.le _) (le_max_left _ _)
      exact mul_le_mul e1 hnorm_h (norm_nonneg _) h2
    have hcongr : rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) s *
        (x : ℂ) ^ s) =
        rectInt z w (fun s => (logDeriv (DirichletCharacter.completedLFunction χ) 0 *
          (x : ℂ) ^ s + FR s * (x : ℂ) ^ s) + TR s * (x : ℂ) ^ s) := by
      apply rectInt_congr_boundary'
      intro s hs
      simp only [TR]
      ring
    have h1 : rectInt z w (fun s => (logDeriv (DirichletCharacter.completedLFunction χ) 0 *
          (x : ℂ) ^ s + FR s * (x : ℂ) ^ s) + TR s * (x : ℂ) ^ s) =
        rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) 0 *
          (x : ℂ) ^ s + FR s * (x : ℂ) ^ s) +
        rectInt z w (fun s => TR s * (x : ℂ) ^ s) :=
      rectInt_add'' (a1.add a1') b1 (a2.add a2') b2 (a3.add a3') b3 (a4.add a4') b4
    have h2 : rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) 0 *
          (x : ℂ) ^ s + FR s * (x : ℂ) ^ s) =
        rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) 0 *
          (x : ℂ) ^ s) +
        rectInt z w (fun s => FR s * (x : ℂ) ^ s) :=
      rectInt_add'' a1 a1' a2 a2' a3 a3' a4 a4'
    have htotal : rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) s *
        (x : ℂ) ^ s) =
        (2 * (Real.pi : ℂ) * Complex.I) *
          (∑ᶠ u : ℂ, ((dR u : ℤ) : ℂ) *
              (if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then
                (x : ℂ) ^ u else 0)) +
        rectInt z w (fun s => TR s * (x : ℂ) ^ s) := by
      rw [hcongr, h1, h2,
        rectInt_const_mul' (logDeriv (DirichletCharacter.completedLFunction χ) 0)
          (fun s : ℂ => (x : ℂ) ^ s),
        rectInt_cpow_eq_zero hx, mul_zero, zero_add, hFRint']
    calc ‖rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) s *
          (x : ℂ) ^ s) -
        (2 * (Real.pi : ℂ) * Complex.I) *
          (∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then
              ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) *
                ((x : ℂ) ^ ρ) else 0))‖
        = ‖rectInt z w (fun s => TR s * (x : ℂ) ^ s)‖ := by
          rw [htotal, hsum_eq]
          simp only [add_sub_cancel_left]
      _ ≤ 2 * ((w.re - z.re) + (w.im - z.im)) *
          (c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
            (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) *
          (max (x ^ z.re) (x ^ w.re)) := htail_bound
  have hlim : Tendsto (fun R : ℝ => 2 * ((w.re - z.re) + (w.im - z.im)) *
      (c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
        (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) *
      (max (x ^ z.re) (x ^ w.re))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R)
        atTop (𝓝 0) := by
      have hlog := Commons.NumberTheory.Linnik.log_add_two_div_self_tendsto_zero
      have hc2 : Tendsto (fun R : ℝ => (Real.log (N : ℝ) + 2) / R) atTop (𝓝 0) := by
        have hnum : Tendsto (fun _ : ℝ => Real.log (N : ℝ) + 2) atTop
            (𝓝 (Real.log (N : ℝ) + 2)) := tendsto_const_nhds
        have hinv : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
        have := hnum.mul hinv
        simpa [div_eq_mul_inv] using this
      have := hlog.add hc2
      simpa [add_div, add_assoc] using this
    have h2 : Tendsto (fun R : ℝ => c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
        ((Real.log (R + 2) + Real.log (N : ℝ) + 2) / R)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := c * (|z.re| + |w.re| + |z.im| + |w.im| + 1))).mul h1
      simpa [mul_assoc, mul_comm, mul_left_comm] using this
    have h3 : Tendsto (fun R : ℝ => (2 * ((w.re - z.re) + (w.im - z.im)) *
        (max (x ^ z.re) (x ^ w.re))) *
        (c * (|z.re| + |w.re| + |z.im| + |w.im| + 1) *
          ((Real.log (R + 2) + Real.log (N : ℝ) + 2) / R))) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := 2 * ((w.re - z.re) + (w.im - z.im)) *
        (max (x ^ z.re) (x ^ w.re)))).mul h2
      simpa using this
    simpa [mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv] using h3
  have hzero : ‖rectInt z w (fun s => logDeriv (DirichletCharacter.completedLFunction χ) s *
      (x : ℂ) ^ s) -
      (2 * (Real.pi : ℂ) * Complex.I) *
        (∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then
          ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℕ) : ℂ) *
            ((x : ℂ) ^ ρ) else 0))‖ ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop
      (max 2 (4 * (|z.re| + |w.re| + |z.im| + |w.im| + 1)))] with R hR
    have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
    have hR4 : |z.re| + |w.re| + |z.im| + |w.im| + 1 ≤ R / 4 := by
      have := le_trans (le_max_right 2 (4 * (|z.re| + |w.re| + |z.im| + |w.im| + 1))) hR
      linarith
    exact hkey R hR2 hR4
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _)))

end

end Commons.NumberTheory.DirichletCharacter
