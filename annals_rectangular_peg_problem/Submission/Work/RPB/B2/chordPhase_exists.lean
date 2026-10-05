import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B2.PhaseDefs
import Submission.Work.RPB.B2.paramIntegral_contDiff_inf
import Submission.Work.RPB.B2.chordVec_eq_mul_chordW_inf
import Submission.Work.RPB.B2.chordW_contDiff_inf
import Submission.Work.RPB.B2.chordW_ne_zero_nhds_inf
import Submission.Work.RPB.B2.chordW_ne_zero_nhds
import Submission.Work.RPB.B2.chordVec_circle
import Submission.Work.RPB.B2.hasDerivAt_div_norm
import Submission.Work.RPB.B2.contDiff_mul_of_contDiffOn
import Submission.Work.RPB.B2.chordQ_contDiffOn_inf
import Submission.Work.RPB.B2.chordQ_eq_chordVec_inf
import Submission.Work.RPB.B2.chordQ_reflect_inf

/-!
# B2: existence of the chord phase

`Work.RPB.B2.chordPhase_exists`: every curve isotopy `CI` (a smooth `2π`-periodic family of
embedded closed plane curves with non-vanishing derivative, starting at the unit circle) admits a
`C^∞` lift `a` of `arg (c τ (t+r) - c τ (t-r))` on the strip `0 ≤ τ ≤ 1`, `0 < r ≤ π`, with the two
monodromies `a τ (t+2π) r = a τ t r + 2π` and `a τ (t+π) (π-r) = a τ t r + π`.

The construction is the `τ`-ray integral of the logarithmic derivative of the chord vector.  The
integrand `Im(conj v ∂_τ v)/‖v‖²` is singular where the chord vector vanishes (`r = 0` and `r = π`),
so it is replaced by the `τ`-cut-off combination `chordG` of the two charts `chordQ` (based at
`r = 0`) and `chordQ ∘ (t,r) ↦ (t+π, π-r)` (based at `r = π`) — see `PhaseDefs`.  The `τ`-cut-off
is chosen with a radius `δ` supplied by `chordW_ne_zero_nhds`, so that the assembled integrand is
globally smooth.

The argument property is verified by showing that
`σ ↦ exp (-a σ I) * (v σ / ‖v σ‖)` has vanishing derivative, hence is constant, with value `1` at
`σ = 0` (where the curve is the unit circle).
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff
open MeasureTheory intervalIntegral
open scoped Topology

set_option autoImplicit false

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.RPB.B2

/-! ## 1. The cut-offs -/

lemma cut1_eq_zero_of_le_one {r : ℝ} (h : r ≤ 1) : cut1 r = 0 := by
  rw [cut1, Real.smoothTransition.zero_of_nonpos (show r - 1 ≤ 0 by linarith), zero_mul]

lemma cut1_eq_zero_of_ge {r : ℝ} (h : 4.5 ≤ r) : cut1 r = 0 := by
  rw [cut1, Real.smoothTransition.zero_of_nonpos (show 4.5 - r ≤ 0 by linarith), mul_zero]

lemma cut1_eq_one {r : ℝ} (h1 : 2 ≤ r) (h2 : r ≤ 3.5) : cut1 r = 1 := by
  rw [cut1, Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ r - 1 by linarith),
    Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ 4.5 - r by linarith), mul_one]

lemma cutEta_eq_zero_of_le {r : ℝ} (h : r ≤ -2) : cutEta r = 0 := by
  rw [cutEta, Real.smoothTransition.zero_of_nonpos (show r + 2 ≤ 0 by linarith), zero_mul]

lemma cutEta_eq_zero_of_ge {r : ℝ} (h : 3 ≤ r) : cutEta r = 0 := by
  rw [cutEta, Real.smoothTransition.zero_of_nonpos (show 3 - r ≤ 0 by linarith), mul_zero]

lemma cutEta_eq_one {r : ℝ} (h1 : -1 ≤ r) (h2 : r ≤ 2) : cutEta r = 1 := by
  rw [cutEta, Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ r + 2 by linarith),
    Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ 3 - r by linarith), mul_one]

/-- the two cut-offs glue the two charts: they sum to `1` on `(0,π)`. -/
lemma cut0_add_cut1 {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) π) : cut0 r + cut1 r = 1 := by
  rcases le_or_gt r 2 with h | h
  · rw [cut0, cutEta_eq_one (by linarith [hr.1]) (by linarith), mul_one]
    ring
  · rw [cut0, cut1_eq_one (by linarith) (by linarith [hr.2, Real.pi_lt_d6])]
    ring

lemma cutTau_eq_one {δ : ℝ} (hδ : 0 < δ) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    cutTau δ τ = 1 := by
  rw [cutTau,
    Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ 1 + 2 * (τ / δ) by
      have h : 0 ≤ τ / δ := div_nonneg hτ.1 hδ.le
      linarith),
    Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ 1 + 2 * ((1 - τ) / δ) by
      have h : 0 ≤ (1 - τ) / δ := div_nonneg (by linarith [hτ.2]) hδ.le
      linarith),
    mul_one]

lemma cutTau_eq_zero_of_le {δ : ℝ} (hδ : 0 < δ) {τ : ℝ} (hτ : τ ≤ -δ / 2) :
    cutTau δ τ = 0 := by
  rw [cutTau, Real.smoothTransition.zero_of_nonpos (show 1 + 2 * (τ / δ) ≤ 0 by
    have h : τ / δ ≤ -(1 / 2) := by
      rw [div_le_iff₀ hδ]
      linarith
    linarith), zero_mul]

lemma cutTau_eq_zero_of_ge {δ : ℝ} (hδ : 0 < δ) {τ : ℝ} (hτ : 1 + δ / 2 ≤ τ) :
    cutTau δ τ = 0 := by
  rw [cutTau, Real.smoothTransition.zero_of_nonpos (show 1 + 2 * ((1 - τ) / δ) ≤ 0 by
    have h : (1 - τ) / δ ≤ -(1 / 2) := by
      rw [div_le_iff₀ hδ]
      linarith
    linarith), mul_zero]

lemma contDiff_cutTau (δ : ℝ) : ContDiff ℝ ∞ (cutTau δ) := by
  unfold cutTau
  fun_prop

lemma contDiff_cut0 : ContDiff ℝ ∞ (cut0 : ℝ → ℝ) := by
  unfold cut0 cut1 cutEta
  fun_prop

lemma contDiff_cut1 : ContDiff ℝ ∞ (cut1 : ℝ → ℝ) := by
  unfold cut1
  fun_prop

lemma contDiff_cutTau_proj (δ : ℝ) : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => cutTau δ z.1) :=
  (contDiff_cutTau δ).comp (by fun_prop)

lemma contDiff_cut0_proj : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => cut0 z.2.2) :=
  contDiff_cut0.comp (by fun_prop)

lemma contDiff_cut1_proj : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => cut1 z.2.2) :=
  contDiff_cut1.comp (by fun_prop)

lemma tsupport_cutTau_subset {δ : ℝ} (hδ : 0 < δ) :
    tsupport (cutTau δ : ℝ → ℝ) ⊆ Set.Ioo (-δ) (1 + δ) := by
  refine (closure_minimal (s := Function.support (cutTau δ))
    (t := Set.Icc (-δ / 2) (1 + δ / 2)) ?_ isClosed_Icc).trans ?_
  · intro r hr
    rw [Function.mem_support] at hr
    refine ⟨?_, ?_⟩
    · by_contra h
      exact hr (cutTau_eq_zero_of_le hδ (le_of_not_ge h))
    · by_contra h
      exact hr (cutTau_eq_zero_of_ge hδ (le_of_not_ge h))
  · intro r hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩

lemma tsupport_cutEta_subset : tsupport (cutEta : ℝ → ℝ) ⊆ Set.Icc (-2 : ℝ) 3 := by
  refine closure_minimal ?_ isClosed_Icc
  intro r hr
  rw [Function.mem_support] at hr
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hr (cutEta_eq_zero_of_le (le_of_not_ge h))
  · by_contra h
    exact hr (cutEta_eq_zero_of_ge (le_of_not_ge h))

lemma tsupport_cut0_subset : tsupport (cut0 : ℝ → ℝ) ⊆ Set.Icc (-2 : ℝ) 3 := by
  unfold cut0
  exact (tsupport_mul_subset_right (f := fun r : ℝ => 1 - cut1 r) (g := cutEta)).trans
    tsupport_cutEta_subset

lemma tsupport_smoothTransition_sub {a : ℝ} :
    tsupport (fun r : ℝ => Real.smoothTransition (r - a)) ⊆ Set.Ici a := by
  refine closure_minimal ?_ isClosed_Ici
  intro r hr
  rw [Function.mem_support] at hr
  by_contra h
  exact hr (Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr (le_of_lt (not_le.mp h))))

lemma tsupport_smoothTransition_sub' {b : ℝ} :
    tsupport (fun r : ℝ => Real.smoothTransition (b - r)) ⊆ Set.Iic b := by
  refine closure_minimal ?_ isClosed_Iic
  intro r hr
  rw [Function.mem_support] at hr
  by_contra h
  exact hr (Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr (le_of_lt (not_le.mp h))))

lemma tsupport_cut1_subset : tsupport (cut1 : ℝ → ℝ) ⊆ Set.Icc (1 : ℝ) 4.5 := by
  unfold cut1
  intro r hr
  refine ⟨?_, ?_⟩
  · exact tsupport_smoothTransition_sub (tsupport_mul_subset_left (f := fun r : ℝ =>
      Real.smoothTransition (r - 1)) (g := fun r : ℝ => Real.smoothTransition (4.5 - r)) hr)
  · exact tsupport_smoothTransition_sub' (tsupport_mul_subset_right (f := fun r : ℝ =>
      Real.smoothTransition (r - 1)) (g := fun r : ℝ => Real.smoothTransition (4.5 - r)) hr)

/-- the topological support of a product of a cut-off in `τ` and a cut-off in `r`. -/
lemma tsupport_cutTau_mul_cut (δ : ℝ) (ψ : ℝ → ℝ) :
    tsupport (fun z : ℝ × (ℝ × ℝ) => cutTau δ z.1 * ψ z.2.2) ⊆
      {z : ℝ × (ℝ × ℝ) | z.1 ∈ tsupport (cutTau δ) ∧ z.2.2 ∈ tsupport ψ} := by
  refine (Set.subset_inter
    (tsupport_mul_subset_left (f := fun z : ℝ × (ℝ × ℝ) => cutTau δ z.1)
      (g := fun z : ℝ × (ℝ × ℝ) => ψ z.2.2))
    (tsupport_mul_subset_right (f := fun z : ℝ × (ℝ × ℝ) => cutTau δ z.1)
      (g := fun z : ℝ × (ℝ × ℝ) => ψ z.2.2))).trans ?_
  rintro z ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · exact tsupport_comp_subset_preimage (cutTau δ) (f := fun z : ℝ × (ℝ × ℝ) => z.1)
      (by fun_prop) h1
  · exact tsupport_comp_subset_preimage ψ (f := fun z : ℝ × (ℝ × ℝ) => z.2.2)
      (by fun_prop) h2

/-! ## 2. The assembled integrand -/

/-- On the strip the assembled integrand is the logarithmic derivative of the chord. -/
theorem chordG_eq_chordQ (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2))
    (hper : ∀ τ t, c τ (t + 2 * π) = c τ t) {δ : ℝ} (hδ : 0 < δ) {τ t r : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) π) :
    chordG c δ τ t r = chordQ c τ t r := by
  rw [chordG, cutTau_eq_one hδ hτ]
  simp only [one_mul]
  rw [chordQ_reflect_inf c hc hper τ t r hr, ← add_mul, cut0_add_cut1 hr, one_mul]

/-- `chordQ` is `2π`-periodic in `t` (no smoothness of `c` is needed). -/
lemma chordQ_periodic_at (c : ℝ → ℝ → ℂ) (hper : ∀ τ t, c τ (t + 2 * π) = c τ t)
    (τ t r : ℝ) : chordQ c τ (t + 2 * π) r = chordQ c τ t r := by
  have hW : chordW c τ (t + 2 * π) r = chordW c τ t r := chordW_add_two_pi c hper τ t r
  have hWd : chordWd c τ (t + 2 * π) r = chordWd c τ t r := by
    simp only [chordWd]
    rw [show (fun σ : ℝ => chordW c σ (t + 2 * π) r) = (fun σ : ℝ => chordW c σ t r) from
      funext fun σ => chordW_add_two_pi c hper σ t r]
  simp only [chordQ, hW, hWd]

/-- `chordG` is `2π`-periodic in `t`. -/
theorem chordG_add_two_pi (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2))
    (hper : ∀ τ t, c τ (t + 2 * π) = c τ t) (δ τ t r : ℝ) :
    chordG c δ τ (t + 2 * π) r = chordG c δ τ t r := by
  simp only [chordG]
  rw [chordQ_periodic_at c hper τ t r]
  have h2 : chordQ c τ ((t + 2 * π) + π) (π - r) = chordQ c τ (t + π) (π - r) := by
    rw [show (t + 2 * π) + π = (t + π) + 2 * π from by ring,
      chordQ_periodic_at c hper τ (t + π) (π - r)]
  rw [h2]

/-- `chordW` is continuous (at the smooth level). -/
lemma chordW_continuous (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2)) :
    Continuous (fun z : ℝ × (ℝ × ℝ) => chordW c z.1 z.2.1 z.2.2) :=
  (chordW_contDiff_inf c hc).1.continuous

/-- the swap symmetry of the assembled integrand. -/
theorem chordG_symm (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2))
    (hper : ∀ τ t, c τ (t + 2 * π) = c τ t) {δ : ℝ} (hδ : 0 < δ) {s t r : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hr : r ∈ Set.Ioo (0 : ℝ) π) :
    chordG c δ s (t + π) (π - r) = chordG c δ s t r := by
  have hr' : π - r ∈ Set.Ioo (0 : ℝ) π := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  rw [chordG_eq_chordQ c hc hper hδ hs hr', chordQ_reflect_inf c hc hper s t r hr,
    ← chordG_eq_chordQ c hc hper hδ hs hr]

/-- the assembled integrand is smooth. -/
theorem chordG_contDiff (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2)) {δ : ℝ} (hδ : 0 < δ)
    (hgood0 : ∀ τ ∈ Set.Ioo (-δ) (1 + δ), ∀ t : ℝ, ∀ r ∈ Set.Icc (-2 : ℝ) 3,
      chordW c τ t r ≠ 0)
    (hgood1 : ∀ τ ∈ Set.Ioo (-δ) (1 + δ), ∀ t : ℝ, ∀ r ∈ Set.Icc (π - 4.5) (π - 1),
      chordW c τ t r ≠ 0) :
    ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => chordG c δ z.1 z.2.1 z.2.2) := by
  have hQ : ContDiffOn ℝ ∞
      (fun z : ℝ × (ℝ × ℝ) => chordQ c z.1 z.2.1 z.2.2)
      {z : ℝ × (ℝ × ℝ) | chordW c z.1 z.2.1 z.2.2 ≠ 0} := chordQ_contDiffOn_inf c hc
  have hU : IsOpen {z : ℝ × (ℝ × ℝ) | chordW c z.1 z.2.1 z.2.2 ≠ 0} :=
    (isClosed_singleton (x := (0 : ℂ))).isOpen_compl.preimage (chordW_continuous c hc)
  -- first chart
  have hterm1 : ContDiff ℝ ∞
      (fun z : ℝ × (ℝ × ℝ) => (cutTau δ z.1 * cut0 z.2.2) * chordQ c z.1 z.2.1 z.2.2) := by
    refine contDiff_mul_of_contDiffOn hU hQ ?_ ?_
    · exact (contDiff_cutTau_proj δ).mul contDiff_cut0_proj
    · intro z hz
      obtain ⟨hz1, hz2⟩ := tsupport_cutTau_mul_cut δ cut0 hz
      exact hgood0 z.1 (tsupport_cutTau_subset hδ hz1) z.2.1 z.2.2 (tsupport_cut0_subset hz2)
  -- second chart
  have hQ2 : ContDiffOn ℝ ∞
      (fun z : ℝ × (ℝ × ℝ) => chordQ c z.1 (z.2.1 + π) (π - z.2.2))
      {z : ℝ × (ℝ × ℝ) | chordW c z.1 (z.2.1 + π) (π - z.2.2) ≠ 0} := by
    refine hQ.comp ((by fun_prop : ContDiff ℝ ∞
      (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.1 + π, π - z.2.2)))).contDiffOn) ?_
    intro z hz
    exact hz
  have hU2 : IsOpen {z : ℝ × (ℝ × ℝ) | chordW c z.1 (z.2.1 + π) (π - z.2.2) ≠ 0} :=
    (isClosed_singleton (x := (0 : ℂ))).isOpen_compl.preimage
      ((chordW_continuous c hc).comp (by fun_prop : Continuous (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.1 + π, π - z.2.2)))))
  have hterm2 : ContDiff ℝ ∞
      (fun z : ℝ × (ℝ × ℝ) =>
        (cutTau δ z.1 * cut1 z.2.2) * chordQ c z.1 (z.2.1 + π) (π - z.2.2)) := by
    refine contDiff_mul_of_contDiffOn hU2 hQ2 ?_ ?_
    · exact (contDiff_cutTau_proj δ).mul contDiff_cut1_proj
    · intro z hz
      obtain ⟨hz1, hz2⟩ := tsupport_cutTau_mul_cut δ cut1 hz
      have hz2' := tsupport_cut1_subset hz2
      exact hgood1 z.1 (tsupport_cutTau_subset hδ hz1) (z.2.1 + π) (π - z.2.2)
        ⟨by linarith [hz2'.2], by linarith [hz2'.1]⟩
  have hsum := hterm1.add hterm2
  simpa only [chordG] using hsum

/-- the candidate phase is smooth. -/
theorem chordA_contDiff (c : ℝ → ℝ → ℂ) {δ : ℝ}
    (hG : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => chordG c δ z.1 z.2.1 z.2.2)) :
    ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => chordA c δ z.1 z.2.1 z.2.2) := by
  have h1 : ContDiff ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) => ∫ σ in (0 : ℝ)..1, chordG c δ (x.1 * σ) x.2.1 x.2.2) := by
    refine paramIntegral_contDiff_inf (fun σ (x : ℝ × (ℝ × ℝ)) =>
      chordG c δ (x.1 * σ) x.2.1 x.2.2) 0 1 ?_
    exact hG.comp (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × (ℝ × ℝ)) => ((p.2.1 * p.1, (p.2.2.1, p.2.2.2)) : ℝ × (ℝ × ℝ))))
  have h2 : ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => x.2.1 + π / 2) := by
    fun_prop
  simpa only [chordA] using h2.add (contDiff_fst.mul h1)

/-- `chordVec c · t r` is differentiable. -/
lemma chordVec_differentiableAt (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ∞ (fun z : ℝ × ℝ => c z.1 z.2)) (u t r : ℝ) :
    DifferentiableAt ℝ (fun s => Work.RPB.chordVec c s t r) u := by
  have hsub : ContDiff ℝ ∞ (fun s : ℝ => c s (t + r) - c s (t - r)) :=
    (hc.comp (by fun_prop : ContDiff ℝ ∞ (fun s : ℝ => ((s, t + r) : ℝ × ℝ)))).sub
      (hc.comp (by fun_prop : ContDiff ℝ ∞ (fun s : ℝ => ((s, t - r) : ℝ × ℝ))))
  have h := hsub.differentiable (by simp) u
  simpa only [Work.RPB.chordVec] using h

/-- rescaling a unit complex number. -/
lemma mul_div_norm (c : ℝ) (hc : 0 < c) (E : ℂ) (hE : ‖E‖ = 1) :
    ((c : ℂ) * E) / ‖(c : ℂ) * E‖ = E := by
  have hnorm : ‖(c : ℂ)‖ = c := by
    rw [show ‖(c : ℂ)‖ = |c| by simp, abs_of_pos hc]
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [norm_mul, hnorm, hE, mul_one]
  exact mul_div_cancel_left₀ E hc0

/-! ## 3. The `τ`-integral of `chordG` and its derivative -/

/-- rescaling of an interval integral to the unit interval. -/
lemma mul_integral_comp_mul (F : ℝ → ℝ) (τ : ℝ) :
    τ * ∫ ρ in (0 : ℝ)..1, F (τ * ρ) = ∫ s in (0 : ℝ)..τ, F s := by
  rcases eq_or_ne τ 0 with h | h
  · simp [h]
  · rw [intervalIntegral.integral_comp_mul_left F h]
    rw [show (τ * 0 : ℝ) = 0 from by ring, show (τ * 1 : ℝ) = τ from by ring]
    rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ h, one_mul]

theorem chordA_eq_integral (c : ℝ → ℝ → ℂ) (δ τ t r : ℝ) :
    chordA c δ τ t r = t + π / 2 + ∫ s in (0 : ℝ)..τ, chordG c δ s t r := by
  simp only [chordA]
  rw [mul_integral_comp_mul (fun s => chordG c δ s t r) τ]

/-- the derivative of the candidate phase. -/
theorem chordA_hasDerivAt (c : ℝ → ℝ → ℂ) {δ : ℝ}
    (hG : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => chordG c δ z.1 z.2.1 z.2.2))
    (σ t r : ℝ) :
    HasDerivAt (fun s => chordA c δ s t r) (chordG c δ σ t r) σ := by
  have hcont : Continuous (fun s : ℝ => chordG c δ s t r) :=
    hG.continuous.comp (by fun_prop : Continuous (fun s : ℝ => ((s, (t, r)) : ℝ × (ℝ × ℝ))))
  have hFTC : HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, chordG c δ s t r)
      (chordG c δ σ t r) σ :=
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
      (hcont.stronglyMeasurableAtFilter volume (𝓝 σ)) hcont.continuousAt
  refine (hFTC.add_const (t + π / 2)).congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall fun s => ?_
  show chordA c δ s t r = (∫ u in (0 : ℝ)..s, chordG c δ u t r) + (t + π / 2)
  rw [chordA_eq_integral c δ s t r]
  ring

/-! ## 4. The chord-phase theorem -/

theorem chordPhase_exists (CI : Work.RPV.CurveIsotopy) :
    ∃ a : ℝ → ℝ → ℝ → ℝ, Work.RPB.IsChordPhase CI.c a := by
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := chordW_ne_zero_nhds_inf CI.c CI.smooth CI.per CI.inj CI.imm
    (A := -2) (B := 3) (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three])
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := chordW_ne_zero_nhds_inf CI.c CI.smooth CI.per CI.inj CI.imm
    (A := π - 4.5) (B := π - 1) (by linarith [Real.pi_gt_three]) (by linarith)
  have hδpos : 0 < min δ₁ δ₂ := lt_min hδ₁pos hδ₂pos
  have hgood0 : ∀ τ ∈ Set.Ioo (-(min δ₁ δ₂)) (1 + min δ₁ δ₂), ∀ t : ℝ,
      ∀ r ∈ Set.Icc (-2 : ℝ) 3, chordW CI.c τ t r ≠ 0 := by
    intro τ hτ t r hr
    refine hδ₁ τ ⟨?_, ?_⟩ t r hr <;> linarith [min_le_left δ₁ δ₂, hτ.1, hτ.2]
  have hgood1 : ∀ τ ∈ Set.Ioo (-(min δ₁ δ₂)) (1 + min δ₁ δ₂), ∀ t : ℝ,
      ∀ r ∈ Set.Icc (π - 4.5) (π - 1), chordW CI.c τ t r ≠ 0 := by
    intro τ hτ t r hr
    refine hδ₂ τ ⟨?_, ?_⟩ t r hr <;> linarith [min_le_right δ₁ δ₂, hτ.1, hτ.2]
  have hG : ContDiff ℝ ∞
      (fun z : ℝ × (ℝ × ℝ) => chordG CI.c (min δ₁ δ₂) z.1 z.2.1 z.2.2) :=
    chordG_contDiff CI.c CI.smooth hδpos hgood0 hgood1
  have hAc : ContDiff ℝ ∞
      (fun z : ℝ × (ℝ × ℝ) => chordA CI.c (min δ₁ δ₂) z.1 z.2.1 z.2.2) :=
    chordA_contDiff CI.c hG
  refine ⟨chordA CI.c (min δ₁ δ₂), ?_, ?_, ?_, ?_⟩
  · exact hAc.contDiffOn
  · -- the argument property
    intro τ hτ t r hr
    -- the two curves `V` and the phase `A`, and the constancy function `F`
    set V : ℝ → ℂ := fun u => Work.RPB.chordVec CI.c u t r with hV
    set A : ℝ → ℝ := fun u => chordA CI.c (min δ₁ δ₂) u t r with hA
    set F : ℝ → ℂ := fun u => Complex.exp (-(A u) * Complex.I) * (V u / ‖V u‖) with hF
    have hVne : ∀ u ∈ Set.Icc (0 : ℝ) 1, V u ≠ 0 := by
      intro u hu
      rw [hV]
      exact chordVec_ne_zero_of CI.c CI.inj hu (by linarith [hr.1, Real.pi_pos]) hr.2
        (ne_of_gt hr.1)
    have hAdiff : ∀ u : ℝ, DifferentiableAt ℝ A u := by
      intro u
      have h := (chordA_hasDerivAt CI.c hG u t r).differentiableAt
      simpa only [hA] using h
    have hVdiff : ∀ u : ℝ, DifferentiableAt ℝ V u := by
      intro u
      have h := chordVec_differentiableAt CI.c CI.smooth u t r
      simpa only [hV] using h
    have hExpdiff : ∀ u : ℝ,
        DifferentiableAt ℝ (fun u : ℝ => Complex.exp (-(A u) * Complex.I)) u := fun u => by
      have h1 : DifferentiableAt ℝ (fun s : ℝ => ((↑(-(A s)) : ℂ)) * Complex.I) u :=
        ((hAdiff u).hasDerivAt.neg.ofReal_comp.mul_const Complex.I).differentiableAt
      have h2 : DifferentiableAt ℝ
          (fun s : ℝ => Complex.exp (((↑(-(A s)) : ℂ)) * Complex.I)) u := h1.cexp
      simpa only [Function.comp_def, Complex.ofReal_neg] using h2
    have hFdiff : ∀ u ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ F u := by
      intro u hu
      rw [hF]
      exact (hExpdiff u).mul (hasDerivAt_div_norm V (deriv V u) u
        (hVdiff u).hasDerivAt (hVne u hu)).differentiableAt
    -- the derivative of `F` vanishes on the strip
    have hderiv_zero : ∀ u ∈ Set.Icc (0 : ℝ) 1, deriv F u = 0 := by
      intro u hu
      have huV : V u ≠ 0 := hVne u hu
      have hVd : HasDerivAt V (deriv V u) u := (hVdiff u).hasDerivAt
      have hAd : HasDerivAt A (chordQ CI.c u t r) u := by
        rw [hA]
        have h := chordA_hasDerivAt CI.c hG u t r
        rwa [chordG_eq_chordQ CI.c CI.smooth CI.per hδpos hu hr] at h
      have hbridge : ((Work.RPV.ωC (V u) (deriv V u) / ‖V u‖ ^ 2 : ℝ) : ℂ)
          = ((chordQ CI.c u t r : ℝ) : ℂ) := by
        simp only [hV]
        rw [chordQ_eq_chordVec_inf CI.c CI.smooth u t r (ne_of_gt hr.1)]
      have hdir : HasDerivAt (fun s => V s / ‖V s‖)
          (Complex.I * (V u / ‖V u‖) * ((chordQ CI.c u t r : ℝ) : ℂ)) u := by
        rw [← hbridge]
        exact hasDerivAt_div_norm V (deriv V u) u hVd huV
      have hexp : HasDerivAt (fun s : ℝ => Complex.exp (-(A s) * Complex.I))
          (Complex.exp (-(A u) * Complex.I) * (-(chordQ CI.c u t r : ℝ) * Complex.I)) u := by
        have h1 : HasDerivAt (fun s : ℝ => ((↑(-(A s)) : ℂ)) * Complex.I)
            (((↑(-(chordQ CI.c u t r)) : ℂ)) * Complex.I) u :=
          hAd.neg.ofReal_comp.mul_const Complex.I
        have h2 := (Complex.hasDerivAt_exp (((↑(-(A u)) : ℂ)) * Complex.I)).comp u h1
        simpa only [Function.comp_def, Complex.ofReal_neg] using h2
      have hmul := hexp.mul hdir
      have hzero : Complex.exp (-(A u) * Complex.I)
            * (-(chordQ CI.c u t r : ℝ) * Complex.I) * (V u / ‖V u‖)
          + Complex.exp (-(A u) * Complex.I)
            * (Complex.I * (V u / ‖V u‖) * ((chordQ CI.c u t r : ℝ) : ℂ)) = 0 := by
        push_cast
        ring
      rw [hzero] at hmul
      have := hmul.deriv
      rwa [hF]
    -- `F` is constant: `F τ = F 0`
    have hpair : ∀ x ∈ Set.Ioc (0 : ℝ) 1, ∀ y ∈ Set.Icc x 1, F y = F x := by
      intro x hx y hy
      have hsub : Set.uIcc x y ⊆ Set.Icc (0 : ℝ) 1 := by
        intro z hz
        rw [Set.uIcc_of_le hy.1] at hz
        exact ⟨le_trans hx.1.le hz.1, le_trans hz.2 hy.2⟩
      have hint : ∫ z in x..y, deriv F z = F y - F x :=
        intervalIntegral.integral_deriv_eq_sub (fun z hz => hFdiff z (hsub hz))
          (intervalIntegrable_congr (fun z hz => hderiv_zero z (hsub (Set.uIoc_subset_uIcc hz))) |>.mpr
            intervalIntegrable_const)
      rw [intervalIntegral.integral_congr (fun z hz => hderiv_zero z (hsub hz))] at hint
      simp only [intervalIntegral.integral_zero] at hint
      exact sub_eq_zero.mp hint.symm
    -- value at `τ = 0`
    have hcircle : V 0 / ‖V 0‖ = Complex.exp ((t + π / 2) * Complex.I) := by
      have hsinpos : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr.1 hr.2
      have hcpos : (0 : ℝ) < 2 * Real.sin r := by linarith
      have hV0 : V 0 = ((2 * Real.sin r : ℝ) : ℂ) * Complex.exp ((t + π / 2) * Complex.I) := by
        have h := chordVec_circle CI.c CI.start t r
        simp only [hV]
        rw [h]
        rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul]
      rw [hV0]
      have hE1 : ‖Complex.exp ((t + π / 2) * Complex.I)‖ = 1 := by
        rw [Complex.norm_exp]
        simp [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
          Complex.div_re, Complex.div_im]
      exact mul_div_norm (2 * Real.sin r) hcpos _ hE1
    have hF0 : F 0 = 1 := by
      have hA0 : A 0 = t + π / 2 := by
        simp only [hA, chordA]
        ring
      have h1 : F 0 =
          Complex.exp (-(t + π / 2) * Complex.I) * Complex.exp ((t + π / 2) * Complex.I) := by
        simp only [hF, hA0, hcircle, Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_div,
          Complex.ofReal_ofNat]
      rw [h1, ← Complex.exp_add]
      rw [show (-(t + π / 2) * Complex.I + (t + π / 2) * Complex.I : ℂ) = 0 by ring]
      exact Complex.exp_zero
    -- continuity of `F` at `0`
    have hconst : F (1 / 2) = F 0 := by
      have hcont0 : ContinuousAt F 0 := by
        have hV0 : V 0 ≠ 0 := hVne 0 (by norm_num)
        have hcontV : ContinuousAt V 0 := (hVdiff 0).continuousAt
        have hcontA : ContinuousAt A 0 := (hAdiff 0).continuousAt
        have hcontExp : ContinuousAt (fun u : ℝ => Complex.exp (-(A u) * Complex.I)) 0 :=
          (hExpdiff 0).continuousAt
        have hcontDiv : ContinuousAt (fun u : ℝ => V u / ‖V u‖) 0 := by
          have := hasDerivAt_div_norm V (deriv V 0) 0 (hVdiff 0).hasDerivAt hV0
          exact this.continuousAt
        rw [hF]
        exact hcontExp.mul hcontDiv
      have hGT : (0 : ℝ) < 1 := by norm_num
      have hev : F =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => F (1 / 2)) := by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
        rcases le_or_gt s (1 / 2) with h | h
        · exact (hpair s ⟨hs.1, le_of_lt hs.2⟩ (1 / 2) ⟨h, by norm_num⟩).symm
        · exact hpair (1 / 2) ⟨by norm_num, by norm_num⟩ s ⟨le_of_lt h, le_of_lt hs.2⟩
      have h1 : Filter.Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (F (1 / 2))) :=
        tendsto_const_nhds.congr' hev.symm
      have h2 : Filter.Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) :=
        hcont0.tendsto.mono_left inf_le_left
      exact tendsto_nhds_unique h1 h2
    -- the conclusion
    have hFτ : F τ = F 0 := by
      rcases eq_or_ne τ 0 with h | h
      · rw [h]
      · rcases le_or_gt τ (1 / 2) with hle | hlt
        · rw [(hpair τ ⟨lt_of_le_of_ne hτ.1 (Ne.symm h), hτ.2⟩ (1 / 2)
            ⟨hle, by norm_num⟩).symm, hconst]
        · rw [hpair (1 / 2) ⟨by norm_num, by norm_num⟩ τ ⟨le_of_lt hlt, hτ.2⟩, hconst]
    have hexp1 : Complex.exp (-(A τ) * Complex.I) * (V τ / ‖V τ‖) = 1 := by
      have h : F τ = 1 := by rw [hFτ, hF0]
      simpa only [hF] using h
    have hquot : V τ / ‖V τ‖ = Complex.exp (A τ * Complex.I) := by
      have h := congrArg (fun w : ℂ => Complex.exp (A τ * Complex.I) * w) hexp1
      simp only [mul_one] at h
      rw [← mul_assoc, ← Complex.exp_add] at h
      simpa using h
    have hfinal : V τ = (‖V τ‖ : ℂ) * Complex.exp (A τ * Complex.I) := by
      have hVτ : V τ ≠ 0 := hVne τ hτ
      have hnorm : (‖V τ‖ : ℂ) ≠ 0 := by
        simpa using norm_ne_zero_iff.mpr hVτ
      have h := congrArg (fun w : ℂ => w * (‖V τ‖ : ℂ)) hquot
      rw [div_mul_cancel₀ _ hnorm] at h
      rw [mul_comm] at h
      exact h
    simpa only [hV, hA] using hfinal
  · -- monodromy in `t`
    intro τ hτ t r hr
    rw [chordA, chordA]
    rw [show (∫ σ in (0 : ℝ)..1, chordG CI.c (min δ₁ δ₂) (τ * σ) (t + 2 * π) r)
        = ∫ σ in (0 : ℝ)..1, chordG CI.c (min δ₁ δ₂) (τ * σ) t r from
      intervalIntegral.integral_congr
        (fun σ _ => chordG_add_two_pi CI.c CI.smooth CI.per (min δ₁ δ₂) (τ * σ) t r)]
    ring
  · -- monodromy in `r` under the swap
    intro τ hτ t r hr
    rw [chordA, chordA]
    rw [show (∫ σ in (0 : ℝ)..1, chordG CI.c (min δ₁ δ₂) (τ * σ) (t + π) (π - r))
        = ∫ σ in (0 : ℝ)..1, chordG CI.c (min δ₁ δ₂) (τ * σ) t r from
      intervalIntegral.integral_congr (fun σ hσ => ?_)]
    · ring
    · rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hσ
      refine chordG_symm CI.c CI.smooth CI.per hδpos ?_ hr
      exact ⟨mul_nonneg hτ.1 hσ.1, by nlinarith [hτ.1, hτ.2, hσ.1, hσ.2]⟩

end Work.RPB.B2
