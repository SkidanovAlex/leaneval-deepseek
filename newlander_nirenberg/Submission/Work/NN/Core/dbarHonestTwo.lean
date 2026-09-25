import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Polydisc.dbarCoord_add
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.bmRow
import Submission.Work.NN.Core.bmDefect_eq
import Submission.Work.NN.Core.bmRow_holder
import Submission.Work.NN.Final.bmRow_bound
import Submission.Work.CR.Flat.Cauchy.polydiscCutoff
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
import Submission.Work.CR.Flat.Cauchy.exists_dbar_solution_polydisc_Ck
import Submission.Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv
import Submission.Work.NN.Core.bmDefectClosed
import Submission.Work.NN.Core.TelTwoDF.Defs
import Submission.Work.NN.Core.TelTwoDF.Rec2
import Submission.Work.NN.Core.TelTwoDF.Solves
import Submission.Work.NN.Core.TelTwoDF.contDiff_dbarTransform_univ
import Submission.Work.NN.Core.TelTwoDF.S2Estimate
import Submission.Work.NN.Core.bmRowCutoffEstimate
import Submission.Work.NN.Core.bmPotCutoffEstimate
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.CR.Flat.Holder.holderNorm_neg

namespace Work.NN.Core

set_option maxHeartbeats 1000000

open scoped NNReal ENNReal ContDiff Topology
open Set MeasureTheory Filter
open Work.CR.Flat

noncomputable section

/-! ## Elementary helpers -/

/-- Additivity of `bmPot` for continuous compactly supported data. -/
lemma bmPot_add_of_cont {n : ℕ} (hn : 0 < n) {f g : Fin n → (Cn n → ℂ)}
    (hf : ∀ j, Continuous (f j)) (hg : ∀ j, Continuous (g j))
    (hfs : ∀ j, HasCompactSupport (f j)) (hgs : ∀ j, HasCompactSupport (g j)) :
    Work.CR.Flat.Cauchy.bmPot (f + g) = Work.CR.Flat.Cauchy.bmPot f + Work.CR.Flat.Cauchy.bmPot g := by
  funext z
  show Work.CR.Flat.Cauchy.bmPot (f + g) z
      = Work.CR.Flat.Cauchy.bmPot f z + Work.CR.Flat.Cauchy.bmPot g z
  simp only [Work.CR.Flat.Cauchy.bmPot, Pi.add_apply]
  trans ∑ j : Fin n, ((∫ x : Cn n, Work.CR.Flat.Cauchy.bmKernel j x * f j (z + x))
      + ∫ x : Cn n, Work.CR.Flat.Cauchy.bmKernel j x * g j (z + x))
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hi1 : Integrable (fun x : Cn n => Work.CR.Flat.Cauchy.bmKernel j x * f j (z + x)) :=
      integrable_bmKernel_mul hn j ((hf j).comp (continuous_const.add continuous_id))
        ((hfs j).comp_homeomorph (Homeomorph.addLeft z))
    have hi2 : Integrable (fun x : Cn n => Work.CR.Flat.Cauchy.bmKernel j x * g j (z + x)) :=
      integrable_bmKernel_mul hn j ((hg j).comp (continuous_const.add continuous_id))
        ((hgs j).comp_homeomorph (Homeomorph.addLeft z))
    rw [← MeasureTheory.integral_add hi1 hi2]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring_nf
  · rw [Finset.sum_add_distrib]

/-- Scalar linearity of `bmPot`. -/
lemma bmPot_smul_of_cont {n : ℕ} (f : Fin n → (Cn n → ℂ)) (c : ℝ) :
    Work.CR.Flat.Cauchy.bmPot (fun j => fun w => c • f j w) = c • Work.CR.Flat.Cauchy.bmPot f := by
  have h : (fun j => fun w => c • f j w) = fun j => c • f j := rfl
  rw [h]
  funext z
  show Work.CR.Flat.Cauchy.bmPot (fun j => c • f j) z = c • (Work.CR.Flat.Cauchy.bmPot f z)
  simp only [Work.CR.Flat.Cauchy.bmPot, Pi.smul_apply]
  trans ∑ j : Fin n, c • (∫ x : Cn n, Work.CR.Flat.Cauchy.bmKernel j x * f j (z + x))
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (fun x : Cn n => Work.CR.Flat.Cauchy.bmKernel j x * (c • f j (z + x)))
        = fun x : Cn n => c • (Work.CR.Flat.Cauchy.bmKernel j x * f j (z + x)) from by
      funext x; simp only [Complex.real_smul]; ring_nf]
    rw [MeasureTheory.integral_smul]
  · rw [Finset.smul_sum]

/-- `∂̄` of a pointwise negation. -/
lemma dbarCoord_neg_local {n : ℕ} (j : Fin n) (u : Cn n → ℂ) (z : Cn n) :
    dbarCoord j (- u) z = - dbarCoord j u z := by
  simp only [dbarCoord, fderiv_neg, neg_apply]
  ring_nf

/-- `∂̄` of a difference at a point where both are differentiable. -/
lemma dbarCoord_sub_local {n : ℕ} (j : Fin n) {u v : Cn n → ℂ} {z : Cn n}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dbarCoord j (fun y => u y - v y) z = dbarCoord j u z - dbarCoord j v z := by
  have hfun : (fun y : Cn n => u y - v y) = (fun y : Cn n => u y + (- v) y) := rfl
  rw [hfun, Work.CR.Flat.Polydisc.dbarCoord_add j u (- v) z hu hv.neg, dbarCoord_neg_local]
  ring_nf

/-- If two functions agree on an open neighbourhood of a point then their `∂̄`-derivatives agree. -/
lemma dbarCoord_congr_of_eventuallyEq_local {n : ℕ} {f g : Cn n → ℂ} {y : Cn n}
    (h : f =ᶠ[𝓝 y] g) (j : Fin n) : dbarCoord j f y = dbarCoord j g y := by
  rw [dbarCoord, dbarCoord, h.fderiv_eq]

/-- Closedness transfers from one function to another that agrees with it on an open set. -/
lemma closedOn_of_eq_on_open {n : ℕ} {U : Set (Cn n)} (hU : IsOpen U)
    {D E : Fin n → Fin n → Cn n → ℂ}
    (hDE : ∀ j k y, y ∈ U → D j k y = E j k y)
    (hE : ∀ i l k y, dbarCoord i (E l k) y - dbarCoord l (E i k) y
      + dbarCoord k (E i l) y = 0) :
    ∀ i l k y, y ∈ U →
      dbarCoord i (D l k) y - dbarCoord l (D i k) y + dbarCoord k (D i l) y = 0 := by
  intro i l k y hy
  have h1 : dbarCoord i (D l k) y = dbarCoord i (E l k) y :=
    dbarCoord_congr_of_eventuallyEq_local
      (Filter.eventuallyEq_of_mem (hU.mem_nhds hy) (fun z hz => hDE l k z hz)) i
  have h2 : dbarCoord l (D i k) y = dbarCoord l (E i k) y :=
    dbarCoord_congr_of_eventuallyEq_local
      (Filter.eventuallyEq_of_mem (hU.mem_nhds hy) (fun z hz => hDE i k z hz)) l
  have h3 : dbarCoord k (D i l) y = dbarCoord k (E i l) y :=
    dbarCoord_congr_of_eventuallyEq_local
      (Filter.eventuallyEq_of_mem (hU.mem_nhds hy) (fun z hz => hDE i l z hz)) k
  rw [h1, h2, h3, hE]

/-- A compactly supported function vanishes beyond a positive radius. -/
lemma radius_of_hasCompactSupport {n : ℕ} {f : Cn n → ℂ} (hf : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∀ z, R ≤ ‖z‖ → f z = 0 := by
  obtain ⟨C, hC⟩ := hf.isCompact.isBounded.exists_norm_le
  refine ⟨max C 0 + 1, by positivity, fun z hz => ?_⟩
  by_contra hne
  have hzmem : z ∈ tsupport f := subset_tsupport f (Function.mem_support.mpr hne)
  have h1 : ‖z‖ ≤ C := hC z hzmem
  have h2 : C ≤ max C 0 := le_max_left C 0
  have h3 : max C 0 + 1 ≤ ‖z‖ := hz
  linarith

/-- If a `C¹` function vanishes on the exterior of the open polydisc `polydisc 0 r` (in the sense
`∃ i, r i ≤ ‖z i‖`) then its `∂̄`-derivatives vanish there as well. -/
lemma dbarCoord_eq_zero_of_vanishing_exterior {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i)
    {f : Cn n → ℂ} (hf : ContDiff ℝ 1 f) (hsupp : ∀ z, (∃ i, r i ≤ ‖z i‖) → f z = 0)
    (j : Fin n) {z : Cn n} (hz : ∃ i, r i ≤ ‖z i‖) : dbarCoord j f z = 0 := by
  obtain ⟨i₀, hi₀⟩ := hz
  have hzi : z i₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hi₀; exact absurd hi₀ (not_le.mpr (hr i₀))
  set w : Cn n := Pi.single i₀ (z i₀) with hw
  have hw₀ : w i₀ = z i₀ := by rw [hw]; simp
  have hcont : Continuous (fun t : ℝ => dbarCoord j f (z + t • w)) :=
    (Work.CR.Flat.Cauchy.continuous_dbarCoord hf j).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hzero : ∀ t : ℝ, 0 < t → dbarCoord j f (z + t • w) = 0 := by
    intro t ht
    have hy : (z + t • w) i₀ = z i₀ * (1 + (t : ℂ)) := by
      rw [Pi.add_apply, Pi.smul_apply, hw₀, Complex.real_smul]; ring_nf
    have hnorm : r i₀ < ‖(z + t • w) i₀‖ := by
      rw [hy, norm_mul]
      have h1 : 1 + t ≤ ‖(1 : ℂ) + (t : ℂ)‖ := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + t)]
      have h2 : 0 < ‖z i₀‖ := lt_of_lt_of_le (hr i₀) hi₀
      nlinarith [norm_nonneg (z i₀), mul_nonneg h2.le (norm_nonneg ((1:ℂ) + (t:ℂ)))]
    have hnb : ∀ᶠ y in 𝓝 (z + t • w), f y = 0 := by
      have hop : IsOpen {y : Cn n | r i₀ < ‖y i₀‖} :=
        isOpen_lt continuous_const ((continuous_apply i₀).norm)
      filter_upwards [hop.mem_nhds hnorm] with y hy
      exact hsupp y ⟨i₀, le_of_lt hy⟩
    rw [dbarCoord_congr_of_eventuallyEq_local hnb j]
    simp [dbarCoord]
  have h1 : Filter.Tendsto (fun t : ℝ => dbarCoord j f (z + t • w)) (𝓝[>] (0 : ℝ))
      (𝓝 (dbarCoord j f z)) := by
    have h : Filter.Tendsto (fun t : ℝ => dbarCoord j f (z + t • w)) (𝓝 (0 : ℝ))
        (𝓝 (dbarCoord j f z)) := by
      have h := hcont.tendsto (0 : ℝ)
      rwa [zero_smul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun t : ℝ => dbarCoord j f (z + t • w)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact (hzero t ht).symm)
  exact tendsto_nhds_unique h1 h2

/-- A function vanishing on the exterior of a polydisc (in the sense `∃ i, r i ≤ ‖z i‖`) has
compact support. -/
lemma hasCompactSupport_of_vanishing_polydisc {n : ℕ} {r : Fin n → ℝ} (hr : ∀ j, 0 < r j)
    {f : Cn n → ℂ} (hf : ∀ z, (∃ i, r i ≤ ‖z i‖) → f z = 0) : HasCompactSupport f := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Cn n) (∑ i, r i)) ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hcon
  rw [not_le] at hcon
  rw [Function.mem_support] at hz
  have hex : ∃ i, r i ≤ ‖z i‖ := by
    by_contra h
    push_neg at h
    have h2 : ‖z‖ ≤ ∑ i, r i := by
      rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => (hr i).le)]
      intro i
      exact le_trans (le_of_lt (h i))
        (Finset.single_le_sum (fun i _ => (hr i).le) (Finset.mem_univ i))
    linarith
  exact hz (hf z hex)

/-- Continuity of `f · η` when `f` is continuous and vanishes outside a polydisc on which `η` is
continuous (and `f`'s support polydisc is strictly inside). -/
lemma continuous_mul_of_continuousOn_of_vanishing {n : ℕ} {f η : Cn n → ℂ} {r ρ : Fin n → ℝ}
    (hρr : ∀ j, r j < ρ j) (hη : ContDiffOn ℝ 1 η (polydisc 0 ρ))
    (hf : Continuous f) (hfzero : ∀ z, (∃ i, r i ≤ ‖z i‖) → f z = 0) :
    Continuous (fun w => f w * η w) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx : x ∈ polydisc 0 ρ
  · exact (hf.continuousAt.mul
      (hη.continuousOn.continuousAt ((isOpen_polydisc 0 ρ).mem_nhds hx)))
  · have hx' : ∃ i, r i < ‖x i‖ := by
      by_contra h; push_neg at h
      exact hx (fun i => by simpa using lt_of_le_of_lt (h i) (hρr i))
    obtain ⟨i, hi⟩ := hx'
    have hnb : ∀ᶠ y in 𝓝 x, f y = 0 := by
      have hop : IsOpen {y : Cn n | r i < ‖y i‖} :=
        isOpen_lt continuous_const ((continuous_apply i).norm)
      filter_upwards [hop.mem_nhds hi] with y hy
      exact hfzero y ⟨i, le_of_lt hy⟩
    exact (continuousAt_const (x := x)).congr (by
      filter_upwards [hnb] with y hy
      rw [hy, zero_mul])

/-- `∂̄` of a smooth function is smooth.

NOTE (import-walls session): the *canonical* public declaration of this name in namespace
`Work.NN.Core` is the more general one in `Core/holderNorm_fiberPot_of_vanishing.lean`
(`ContDiff ℝ (k+1) η → ContDiff ℝ k (∂̄ η)`, whose 7 closure-users dominate this file's 1).  This
copy is therefore *renamed* here (and in its five dependent users: `Core/dbarHonestTwoLocal`,
`Core/closedProjectionK`, `Core/closedProjectionKNoW`, `Core/closedProjection0_of_crux`,
`Core/exists_sourceSolverC1a`); the two chains then no longer declare the same constant.  Note
`private` would have been enough for the name clash but it hides the declaration from those five
dependents, which see it through this file.  See `NOTES_uniformDbarL2_session.md` §13. -/
lemma contDiff_dbarCoord_of_smooth_top {n : ℕ} {f : Cn n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (dbarCoord j f) := by
  rw [Work.CR.Flat.Polydisc.dbarCoord_eq_comp]
  exact (Work.CR.Flat.Polydisc.dbarCoordPhi j).contDiff.comp (hf.fderiv_right (by simp))

/-- The Bochner–Martinelli potential of smooth compactly supported data is smooth. -/
lemma contDiff_bmPot_top {n : ℕ} (hn : 0 < n) {f : Fin n → Cn n → ℂ}
    (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) (hcs : ∀ j, HasCompactSupport (f j)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => Work.CR.Flat.Cauchy.bmPot f y) := by
  have heq : (fun y => Work.CR.Flat.Cauchy.bmPot f y)
      = fun y => Work.CR.Flat.Cauchy.bmPotential f y := by
    funext y; exact (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot f y).symm
  rw [heq, contDiff_infty]
  intro m
  exact Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport hn (i := m)
    (fun j => (hf j).of_le (by simp)) hcs

/-- The Bochner–Martinelli potential of compactly supported data of class `C^m` (`m` finite). -/
lemma contDiff_bmPot_of {n : ℕ} (hn : 0 < n) {m : ℕ} {f : Fin n → Cn n → ℂ}
    (hf : ∀ j, ContDiff ℝ m (f j)) (hcs : ∀ j, HasCompactSupport (f j)) :
    ContDiff ℝ m (fun y => Work.CR.Flat.Cauchy.bmPot f y) := by
  have heq : (fun y => Work.CR.Flat.Cauchy.bmPot f y)
      = fun y => Work.CR.Flat.Cauchy.bmPotential f y := by
    funext y; exact (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot f y).symm
  rw [heq]
  exact Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport hn hf hcs

/-- `bmRow` of compactly supported data of class `C^m` (`m` finite) is of class `C^m`. -/
lemma contDiff_bmRow_of {n : ℕ} (hn : 0 < n) {m : ℕ} {f : Fin n → Fin n → Cn n → ℂ}
    (hf : ∀ j l, ContDiff ℝ m (f j l)) (hcs : ∀ j l, HasCompactSupport (f j l)) (j : Fin n) :
    ContDiff ℝ m (bmRow f j) := by
  have heq : (bmRow f j) = fun y => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
      * Work.CR.Flat.Cauchy.bmPot (fun l => f j l) y := rfl
  rw [heq]
  exact contDiff_const.mul (contDiff_bmPot_of hn (fun l => hf j l) (fun l => hcs j l))

/-- `bmRow` of smooth compactly supported data is smooth. -/
lemma contDiff_bmRow_top {n : ℕ} (hn : 0 < n) {f : Fin n → Fin n → Cn n → ℂ}
    (hf : ∀ j l, ContDiff ℝ (⊤ : ℕ∞) (f j l)) (hcs : ∀ j l, HasCompactSupport (f j l))
    (j : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (bmRow f j) := by
  have heq : (bmRow f j) = fun y => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
      * Work.CR.Flat.Cauchy.bmPot (fun l => f j l) y := rfl
  rw [heq]
  exact contDiff_const.mul (contDiff_bmPot_top hn (fun l => hf j l) (fun l => hcs j l))

/-- Associativity of `ENNReal.ofReal` with a product in the middle. -/
lemma ofReal_mul_mul_assoc {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (X : ℝ≥0∞) :
    ENNReal.ofReal a * (ENNReal.ofReal b * X) = ENNReal.ofReal (a * b) * X := by
  rw [ENNReal.ofReal_mul (q := b) ha, mul_assoc]

/-- Subadditivity of the `C^{k,α}` norm along a difference. -/
lemma holderNorm_sub_le {n : ℕ} {k : ℕ} {α : ℝ} {f g : Cn n → ℂ} {Ω : Set (Cn n)}
    (hf : ContDiffOn ℝ (k : ℕ∞) f Ω) (hg : ContDiffOn ℝ (k : ℕ∞) g Ω)
    (hΩ : UniqueDiffOn ℝ Ω) :
    holderNorm k α (f - g) Ω ≤ holderNorm k α f Ω + holderNorm k α g Ω := by
  have hfun : (f - g) = f + (-g) := rfl
  calc holderNorm k α (f - g) Ω
      = holderNorm k α (f + (-g)) Ω := by rw [hfun]
    _ ≤ holderNorm k α f Ω + holderNorm k α (-g) Ω :=
        Work.CR.Flat.Holder.holderNorm_add_le hf hg.neg hΩ
    _ = holderNorm k α f Ω + holderNorm k α g Ω := by
        rw [Work.CR.Flat.Holder.holderNorm_neg hg hΩ]

/-- A smooth function of compact support (vanishing outside a polydisc strictly inside) times a
function smooth on that polydisc is globally smooth. -/
lemma contDiff_mul_of_contDiffOn {n : ℕ} {r ρ : Fin n → ℝ} (hρr : ∀ j, r j < ρ j)
    (m : WithTop ℕ∞) {χ η : Cn n → ℂ} (hχ : ContDiff ℝ m χ)
    (hη : ContDiffOn ℝ m η (polydisc 0 ρ))
    (hχzero : ∀ z : Cn n, (∃ i, r i ≤ ‖z i‖) → χ z = 0) :
    ContDiff ℝ m (fun w => χ w * η w) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ polydisc 0 ρ
  · exact hχ.contDiffAt.mul (hη.contDiffAt ((isOpen_polydisc 0 ρ).mem_nhds hx))
  · have hx' : ∃ i, r i < ‖x i‖ := by
      by_contra h; push_neg at h
      exact hx (fun i => lt_of_le_of_lt (by simpa using h i) (hρr i))
    obtain ⟨i, hi⟩ := hx'
    have hnb : ∀ᶠ y in 𝓝 x, χ y = 0 := by
      have hop : IsOpen {y : Cn n | r i < ‖y i‖} :=
        isOpen_lt continuous_const ((continuous_apply i).norm)
      filter_upwards [hop.mem_nhds hi] with y hy
      exact hχzero y ⟨i, le_of_lt hy⟩
    have h2 : (fun w => χ w * η w) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
      filter_upwards [hnb] with y hy
      simp [hy]
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq h2

/-- **The analytic core of the `(0,2)` Poincaré lemma on a polydisc.** -/
theorem dbarHonestTwo {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j) (hlt : ∀ j, ρ' j < ρ j) :
    ∃ (T2 : (Fin n → Fin n → (Fin n → ℂ) → ℂ) →ₗ[ℝ] (Fin n → (Fin n → ℂ) → ℂ))
      (C : ℕ → ℝ),
      (∀ k, 0 < C k) ∧
      (∀ η, (∀ j l, ContDiff ℝ 1 (η j l)) →
        (∀ j l z, η j l z = -η l j z) →
        (∀ j l m z, Work.CR.Flat.dbarCoord j (η l m) z - Work.CR.Flat.dbarCoord l (η j m) z
          + Work.CR.Flat.dbarCoord m (η j l) z = 0) →
        ∀ j l (z : Fin n → ℂ), z ∈ Work.CR.Flat.polydisc 0 ρ' →
          Work.CR.Flat.dbarCoord j (T2 η l) z - Work.CR.Flat.dbarCoord l (T2 η j) z = η j l z) ∧
      (∀ (k : ℕ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
        (∀ j l, ContDiff ℝ (k + 1) (η j l)) →
        (∀ j l z, η j l z = -η l j z) →
        (∀ j l m z, Work.CR.Flat.dbarCoord j (η l m) z - Work.CR.Flat.dbarCoord l (η j m) z
          + Work.CR.Flat.dbarCoord m (η j l) z = 0) →
        (∀ j, ContDiffOn ℝ (k + 1) (T2 η j) (Work.CR.Flat.polydisc 0 ρ')) ∧
        (∀ j, Work.CR.Flat.holderNorm (k + 1) α (T2 η j) (Work.CR.Flat.polydisc 0 ρ')
          ≤ ENNReal.ofReal (C k) *
              ∑ j, ∑ l, Work.CR.Flat.holderNorm k α (η j l) (Work.CR.Flat.polydisc 0 ρ))) ∧
      (∀ η, (∀ j l, ContDiffOn ℝ (⊤ : ℕ∞) (η j l) (Work.CR.Flat.polydisc 0 ρ)) →
        (∀ j l z, η j l z = -η l j z) →
        (∀ j l m z, z ∈ Work.CR.Flat.polydisc 0 ρ →
          Work.CR.Flat.dbarCoord j (η l m) z - Work.CR.Flat.dbarCoord l (η j m) z
            + Work.CR.Flat.dbarCoord m (η j l) z = 0) →
        ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (T2 η j) (Work.CR.Flat.polydisc 0 ρ')) := by
  classical
  -- (0) the distinguished coordinate
  obtain ⟨m, -, hmle⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) (fun j => ρ' j)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  -- (1) intermediate multi-radii
  set ρ'' : Fin n → ℝ := fun j => (2 * ρ' j + ρ j) / 3 with hρ''def
  set ρ''' : Fin n → ℝ := fun j => (ρ' j + 2 * ρ j) / 3 with hρ'''def
  have hρ''pos : ∀ j, 0 < ρ'' j := fun j => by
    show 0 < (2 * ρ' j + ρ j) / 3; linarith [hρ' j, hρ j]
  have hρ'''pos : ∀ j, 0 < ρ''' j := fun j => by
    show 0 < (ρ' j + 2 * ρ j) / 3; linarith [hρ' j, hρ j]
  have hρ'ρ'' : ∀ j, ρ' j < ρ'' j := fun j => by
    show ρ' j < (2 * ρ' j + ρ j) / 3; linarith [hlt j]
  have hρ''ρ''' : ∀ j, ρ'' j < ρ''' j := fun j => by
    show (2 * ρ' j + ρ j) / 3 < (ρ' j + 2 * ρ j) / 3; linarith [hlt j]
  have hρ'''ρ : ∀ j, ρ''' j < ρ j := fun j => by
    show (ρ' j + 2 * ρ j) / 3 < ρ j; linarith [hlt j]
  have hρ''ρ : ∀ j, ρ'' j < ρ j := fun j => lt_trans (hρ''ρ''' j) (hρ'''ρ j)
  -- (2) the cutoff
  obtain ⟨u, hu_sm, _hu01, hu_one, hu_zero, hu_cs, _hu_dbar_sm, _hu_dbar_cs⟩ :=
    Work.CR.Flat.Cauchy.polydiscCutoff (n := n) (c := (0 : Cn n)) (r₁ := ρ'') (r₂ := ρ''') 0
      hρ''pos hρ''ρ'''
  set χ : Cn n → ℂ := fun z => (u z : ℂ) with hχdef
  have hχ_sm : ContDiff ℝ (⊤ : ℕ∞) χ := by
    rw [hχdef]; exact Complex.ofRealCLM.contDiff.comp hu_sm
  have hχ_cd1 : ContDiff ℝ 1 χ := hχ_sm.of_le (by simp)
  have hχ_cs : HasCompactSupport χ := hu_cs
  have hχ_one : ∀ z : Cn n, (∀ j, ‖z j‖ ≤ ρ'' j) → χ z = 1 := by
    intro z hz
    show (u z : ℂ) = 1
    rw [hu_one z (fun j => by simpa using hz j)]; norm_num
  have hχ_zero : ∀ z : Cn n, (∃ j, ρ''' j ≤ ‖z j‖) → χ z = 0 := by
    intro z hz
    show (u z : ℂ) = 0
    rw [hu_zero z (by obtain ⟨j, hj⟩ := hz; exact ⟨j, by simpa using hj⟩)]; norm_num
  have hχdbar_zero : ∀ (s : Fin n) (z : Cn n), (∃ j, ρ''' j ≤ ‖z j‖) → dbarCoord s χ z = 0 :=
    fun s z hz => dbarCoord_eq_zero_of_vanishing_exterior hρ'''pos hχ_cd1 hχ_zero s hz
  obtain ⟨Rχ, hRχpos, hRχsupp⟩ := radius_of_hasCompactSupport hχ_cs
  -- (3) the geometry of the telescoping
  set G : TelTwoDF.Geom n :=
    { e := ρ'
      a := fun j => (ρ' j + (ρ' j + ρ'' j) / 2) / 2
      b := fun j => (ρ' j + ρ'' j) / 2
      r := fun j => 2 * ((ρ' j + ρ'' j) / 2)
      he := hρ'
      hea := fun j => by linarith [hρ'ρ'' j]
      ha := fun j => by linarith [hρ' j, hρ''pos j]
      hab := fun j => by linarith [hρ'ρ'' j]
      hr := fun j => by linarith [hρ' j, hρ''pos j]
      hbr := fun j => by linarith } with hGdef
  have hGb : ∀ j, G.b j = (ρ' j + ρ'' j) / 2 := fun j => rfl
  have hGbg : ∀ j, G.b j < ρ'' j := fun j => by rw [hGb j]; linarith [hρ'ρ'' j]
  have hGe : G.e = ρ' := rfl
  -- (4) the defect and the operator
  set Ddef : (Fin n → Fin n → Cn n → ℂ) → Fin n → Fin n → Cn n → ℂ :=
    fun η j k y => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
      * Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ η j k l) y with hDdefdef
  have hDdef_apply : ∀ η j k y, Ddef η j k y = -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
      * Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ η j k l) y := fun _ _ _ _ => rfl
  have hopFun_apply : ∀ (η : Fin n → Fin n → Cn n → ℂ) l z,
      (bmRow (fun i l' w => χ w * η i l' w) l - TelTwoDF.S2 G (Ddef η) l) z
        = bmRow (fun i l' w => χ w * η i l' w) l z - TelTwoDF.S2 G (Ddef η) l z :=
    fun _ _ _ => rfl
  let opFun : (Fin n → Fin n → Cn n → ℂ) → (Fin n → Cn n → ℂ) :=
    fun η l => bmRow (fun i l' w => χ w * η i l' w) l - TelTwoDF.S2 G (Ddef η) l
  -- (5) the domain of the linear operator
  let V : Submodule ℝ (Fin n → Fin n → Cn n → ℂ) :=
    { carrier := {η | ∀ i l, ContDiffOn ℝ 1 (η i l) (polydisc 0 ρ)}
      zero_mem' := fun i l => contDiffOn_const
      add_mem' := fun {f g} hf hg => by
        intro i l
        exact (hf i l).add (hg i l)
      smul_mem' := fun c {f} hf => by
        intro i l
        exact (hf i l).const_smul c }
  have hVmem : ∀ η : Fin n → Fin n → Cn n → ℂ,
      η ∈ V ↔ ∀ i l, ContDiffOn ℝ 1 (η i l) (polydisc 0 ρ) := fun _ => Iff.rfl
  -- smoothness of the pieces
  have hbmH_cd : ∀ (i : ℕ) (η : Fin n → Fin n → Cn n → ℂ), (∀ j l, ContDiff ℝ i (η j l)) →
      ∀ j k l, ContDiff ℝ i (bmH χ η j k l) := by
    intro i η hη j k l
    have hd : ∀ s : Fin n, ContDiff ℝ i (dbarCoord s χ) := fun s =>
      (contDiff_dbarCoord_of_smooth_top hχ_sm s).of_le (by simp)
    show ContDiff ℝ i (fun w => dbarCoord l χ w * η j k w + dbarCoord j χ w * η k l w
      - dbarCoord k χ w * η j l w)
    exact (((hd l).mul (hη j k)).add ((hd j).mul (hη k l))).sub ((hd k).mul (hη j l))
  have hbmH_cs : ∀ (η : Fin n → Fin n → Cn n → ℂ), ∀ j k l, HasCompactSupport (bmH χ η j k l) := by
    intro η j k l
    refine hasCompactSupport_of_vanishing_polydisc hρ'''pos (fun z hz => ?_)
    show dbarCoord l χ z * η j k z + dbarCoord j χ z * η k l z - dbarCoord k χ z * η j l z = 0
    rw [hχdbar_zero l z hz, hχdbar_zero j z hz, hχdbar_zero k z hz]; ring_nf
  have hbmH_cont : ∀ (η : Fin n → Fin n → Cn n → ℂ),
      (∀ i l, ContDiffOn ℝ 1 (η i l) (polydisc 0 ρ)) →
      ∀ j k l, Continuous (bmH χ η j k l) := by
    intro η hη j k l
    have hd : ∀ s : Fin n, Continuous (dbarCoord s χ) := fun s =>
      Work.CR.Flat.Cauchy.continuous_dbarCoord hχ_cd1 s
    have h1 : Continuous (fun w => dbarCoord l χ w * η j k w) :=
      continuous_mul_of_continuousOn_of_vanishing hρ'''ρ (hη j k) (hd l) (hχdbar_zero l)
    have h2 : Continuous (fun w => dbarCoord j χ w * η k l w) :=
      continuous_mul_of_continuousOn_of_vanishing hρ'''ρ (hη k l) (hd j) (hχdbar_zero j)
    have h3 : Continuous (fun w => dbarCoord k χ w * η j l w) :=
      continuous_mul_of_continuousOn_of_vanishing hρ'''ρ (hη j l) (hd k) (hχdbar_zero k)
    show Continuous (fun w => dbarCoord l χ w * η j k w + dbarCoord j χ w * η k l w
      - dbarCoord k χ w * η j l w)
    exact (h1.add h2).sub h3
  -- additivity of the defect
  have hDdef_add : ∀ η₁ η₂ : Fin n → Fin n → Cn n → ℂ, η₁ ∈ V → η₂ ∈ V →
      Ddef (η₁ + η₂) = Ddef η₁ + Ddef η₂ := by
    intro η₁ η₂ h₁ h₂
    funext j k y
    have hc₁ : ∀ l, Continuous (fun y => bmH χ η₁ j k l y) :=
      fun l => hbmH_cont η₁ ((hVmem η₁).mp h₁) j k l
    have hc₂ : ∀ l, Continuous (fun y => bmH χ η₂ j k l y) :=
      fun l => hbmH_cont η₂ ((hVmem η₂).mp h₂) j k l
    have hsum : (fun l => bmH χ (η₁ + η₂) j k l)
        = (fun l => bmH χ η₁ j k l) + (fun l => bmH χ η₂ j k l) := by
      funext l y
      show dbarCoord l χ y * (η₁ + η₂) j k y + dbarCoord j χ y * (η₁ + η₂) k l y
          - dbarCoord k χ y * (η₁ + η₂) j l y
        = (dbarCoord l χ y * η₁ j k y + dbarCoord j χ y * η₁ k l y
            - dbarCoord k χ y * η₁ j l y)
          + (dbarCoord l χ y * η₂ j k y + dbarCoord j χ y * η₂ k l y
            - dbarCoord k χ y * η₂ j l y)
      simp only [Pi.add_apply]; ring
    show -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ (η₁ + η₂) j k l) y
        = -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ η₁ j k l) y
          + -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ η₂ j k l) y
    rw [hsum, bmPot_add_of_cont hn hc₁ hc₂ (fun l => hbmH_cs η₁ j k l)
      (fun l => hbmH_cs η₂ j k l)]
    simp only [Pi.add_apply]
    ring
  have hDdef_smul : ∀ (c : ℝ) (η : Fin n → Fin n → Cn n → ℂ), η ∈ V →
      Ddef (c • η) = c • Ddef η := by
    intro c η h
    funext j k y
    have hsum : (fun l => bmH χ (c • η) j k l) = fun l => c • bmH χ η j k l := by
      funext l y
      show dbarCoord l χ y * (c • η) j k y + dbarCoord j χ y * (c • η) k l y
          - dbarCoord k χ y * (c • η) j l y
        = c • (dbarCoord l χ y * η j k y + dbarCoord j χ y * η k l y
            - dbarCoord k χ y * η j l y)
      simp only [Pi.smul_apply, Complex.real_smul]; ring
    show -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ (c • η) j k l) y
        = c • (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ η j k l) y)
    rw [hsum]
    rw [show (fun l => c • bmH χ η j k l)
        = (fun l => fun w => c • bmH χ η j k l w) from rfl]
    rw [bmPot_smul_of_cont]
    simp only [Pi.smul_apply, Complex.real_smul]
    ring
  -- additivity of the operator
  have hopFun_add : ∀ η₁ η₂ : Fin n → Fin n → Cn n → ℂ, η₁ ∈ V → η₂ ∈ V →
      opFun (η₁ + η₂) = opFun η₁ + opFun η₂ := by
    intro η₁ η₂ h₁ h₂
    funext l z
    have hcont₁ : ∀ l', Continuous (fun w => χ w * η₁ l l' w) := fun l' =>
      continuous_mul_of_continuousOn_of_vanishing hρ'''ρ ((hVmem η₁).mp h₁ l l')
        hχ_sm.continuous hχ_zero
    have hcont₂ : ∀ l', Continuous (fun w => χ w * η₂ l l' w) := fun l' =>
      continuous_mul_of_continuousOn_of_vanishing hρ'''ρ ((hVmem η₂).mp h₂ l l')
        hχ_sm.continuous hχ_zero
    have hcs₁ : ∀ l', HasCompactSupport (fun w => χ w * η₁ l l' w) := fun l' =>
      hasCompactSupport_of_vanishing_polydisc hρ'''pos
        (fun z hz => by rw [hχ_zero z hz, zero_mul])
    have hcs₂ : ∀ l', HasCompactSupport (fun w => χ w * η₂ l l' w) := fun l' =>
      hasCompactSupport_of_vanishing_polydisc hρ'''pos
        (fun z hz => by rw [hχ_zero z hz, zero_mul])
    have hsum : (fun l' => fun w => χ w * (η₁ l l' w + η₂ l l' w))
        = (fun l' => fun w => χ w * η₁ l l' w) + (fun l' => fun w => χ w * η₂ l l' w) := by
      funext l' w; simp only [Pi.add_apply]; ring
    have hrow : bmRow (fun i l' w => χ w * (η₁ i l' w + η₂ i l' w)) l z
        = bmRow (fun i l' w => χ w * η₁ i l' w) l z
          + bmRow (fun i l' w => χ w * η₂ i l' w) l z := by
      simp only [Work.NN.Core.bmRow]
      rw [hsum, bmPot_add_of_cont hn hcont₁ hcont₂ hcs₁ hcs₂]
      simp only [Pi.add_apply]
      ring
    have hS2 : TelTwoDF.S2 G (Ddef (η₁ + η₂)) l z
        = TelTwoDF.S2 G (Ddef η₁) l z + TelTwoDF.S2 G (Ddef η₂) l z := by
      rw [show Ddef (η₁ + η₂) = Ddef η₁ + Ddef η₂ from hDdef_add η₁ η₂ h₁ h₂,
        TelTwoDF.S2_add]
      rfl
    show bmRow (fun i l' w => χ w * (η₁ i l' w + η₂ i l' w)) l z
        - TelTwoDF.S2 G (Ddef (η₁ + η₂)) l z
      = (bmRow (fun i l' w => χ w * η₁ i l' w) l z - TelTwoDF.S2 G (Ddef η₁) l z)
        + (bmRow (fun i l' w => χ w * η₂ i l' w) l z - TelTwoDF.S2 G (Ddef η₂) l z)
    rw [hrow, hS2]
    ring
  have hopFun_smul : ∀ (c : ℝ) (η : Fin n → Fin n → Cn n → ℂ), η ∈ V →
      opFun (c • η) = c • opFun η := by
    intro c η h
    funext l z
    have hcont : ∀ l', Continuous (fun w => χ w * η l l' w) := fun l' =>
      continuous_mul_of_continuousOn_of_vanishing hρ'''ρ ((hVmem η).mp h l l')
        hχ_sm.continuous hχ_zero
    have hsum : (fun l' => fun w => χ w * ((c • η) l l' w))
        = fun l' => fun w => c • (χ w * η l l' w) := by
      funext l' w; simp only [Pi.smul_apply, Complex.real_smul]; ring
    have hrow : bmRow (fun i l' w => χ w * ((c • η) i l' w)) l z
        = c • bmRow (fun i l' w => χ w * η i l' w) l z := by
      simp only [Work.NN.Core.bmRow]
      rw [hsum, bmPot_smul_of_cont]
      simp only [Pi.smul_apply, Complex.real_smul]
      ring
    have hS2 : TelTwoDF.S2 G (Ddef (c • η)) l z = c • TelTwoDF.S2 G (Ddef η) l z := by
      rw [show Ddef (c • η) = c • Ddef η from hDdef_smul c η h, TelTwoDF.S2_smul]
      rfl
    show bmRow (fun i l' w => χ w * ((c • η) i l' w)) l z
        - TelTwoDF.S2 G (Ddef (c • η)) l z
      = (c : ℂ) * (bmRow (fun i l' w => χ w * η i l' w) l z
          - TelTwoDF.S2 G (Ddef η) l z)
    rw [hrow, hS2]
    simp only [Complex.real_smul]
    ring
  -- (6) the linear operator
  let opLin : V →ₗ[ℝ] (Fin n → Cn n → ℂ) :=
    { toFun := fun η => opFun η.1
      map_add' := fun η₁ η₂ => hopFun_add η₁.1 η₂.1 η₁.2 η₂.2
      map_smul' := fun c η => hopFun_smul c η.1 η.2 }
  obtain ⟨T2, hT2⟩ := LinearMap.exists_extend opLin
  have hT2_apply : ∀ (η : Fin n → Fin n → Cn n → ℂ) (h : η ∈ V), T2 η = opFun η := by
    intro η h
    have hh := congrArg (fun (g : V →ₗ[ℝ] (Fin n → Cn n → ℂ)) => g ⟨η, h⟩) hT2
    have h1 : opLin ⟨η, h⟩ = opFun η := rfl
    rw [h1] at hh
    simpa [LinearMap.comp_apply] using hh
  obtain ⟨CS, hCSpos, hCSreg, hCSsm⟩ := Work.NN.Core.TelTwoDF.S2Estimate hα hα1 G
  have hρ'ρ''' : ∀ j, ρ' j < ρ''' j := fun j => lt_trans (hρ'ρ'' j) (hρ''ρ''' j)
  have hρ'''2ρ'' : ∀ j, ρ''' j < 2 * ρ'' j := fun j => by
    show (ρ' j + 2 * ρ j) / 3 < 2 * ((2 * ρ' j + ρ j) / 3)
    linarith [hρ' j]
  obtain ⟨Crow, hCrowpos, hCrowbd⟩ :=
    Work.NN.Core.bmRowCutoffEstimate hn hα hα1 hρ'''pos hρ'ρ''' hρ'''ρ χ hχ_sm hχ_cs hχ_zero
  obtain ⟨Cpot, hCpotpos, hCpotbd⟩ :=
    Work.NN.Core.bmPotCutoffEstimate hn hα hα1 hρ''pos hρ'''2ρ'' hρ'''ρ χ hχ_sm hχ_cs hχ_zero
  have hχη_cs_all : ∀ (η' : Fin n → Fin n → Cn n → ℂ) (i l : Fin n),
      HasCompactSupport (fun w => χ w * η' i l w) := fun η' i l =>
    hasCompactSupport_of_vanishing_polydisc hρ'''pos
      (fun z hz => by rw [hχ_zero z hz, zero_mul])
  have hbmH_cs_all : ∀ (η' : Fin n → Fin n → Cn n → ℂ) (j kk l : Fin n),
      HasCompactSupport (bmH χ η' j kk l) := fun η' j kk l =>
    hasCompactSupport_of_vanishing_polydisc hρ'''pos (fun z hz => by
      show dbarCoord l χ z * η' j kk z + dbarCoord j χ z * η' kk l z
          - dbarCoord kk χ z * η' j l z = 0
      rw [hχdbar_zero l z hz, hχdbar_zero j z hz, hχdbar_zero kk z hz]; ring_nf)
  refine ⟨T2, fun k => Crow k + CS (k + 1) * ((n : ℝ) * (n : ℝ)
      * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k)), ?_, ?_, ?_, ?_⟩
  · intro k
    have h2 : 0 ≤ CS (k + 1) * ((n : ℝ) * (n : ℝ)
        * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k)) := by
      have h1 := hCSpos (k + 1)
      have h3 := hCpotpos k
      positivity
    linarith [hCrowpos k]
  · -- clause (a)
    intro η hη hanti hcl
    intro j l z hz
    have hV : η ∈ V := by
      rw [hVmem]; intro i l; exact (hη i l).contDiffOn
    have hbmdef := Work.NN.Core.bmDefect_eq hn hRχpos χ hχ_cd1 hRχsupp η hη hcl
    have hχη_cs : ∀ i l, HasCompactSupport (fun w => χ w * η i l w) := fun i l =>
      hasCompactSupport_of_vanishing_polydisc hρ'''pos
        (fun z hz => by rw [hχ_zero z hz, zero_mul])
    have hD_cd1 : ∀ i l, ContDiff ℝ 1 (Ddef η i l) := by
      intro i l
      have hc : ∀ l', ContDiff ℝ 1 (bmH χ η i l l') := fun l' =>
        hbmH_cd 1 η (fun j m => hη j m) i l l'
      have h := (contDiff_const (c := -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))).mul
        (Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport
          hn (i := 1) hc (fun l' => hbmH_cs η i l l'))
      have heq : (fun y => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPotential (fun l' => bmH χ η i l l') y) = Ddef η i l := by
        funext y
        show -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
              * Work.CR.Flat.Cauchy.bmPotential (fun l' => bmH χ η i l l') y
            = -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
              * Work.CR.Flat.Cauchy.bmPot (fun l' => bmH χ η i l l') y
        rw [Work.CR.Flat.Cauchy.bmPotential_eq_bmPot]
      rw [← heq]; exact h
    have hD_anti : ∀ i l z, Ddef η i l z = - Ddef η l i z := by
      intro i l z
      have hswap : ∀ m w, bmH χ η i l m w = - bmH χ η l i m w := by
        intro m w
        show dbarCoord m χ w * η i l w + dbarCoord i χ w * η l m w - dbarCoord l χ w * η i m w
          = -(dbarCoord m χ w * η l i w + dbarCoord l χ w * η i m w
              - dbarCoord i χ w * η l m w)
        rw [hanti i l w]; ring
      show -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPot (fun m => bmH χ η i l m) z
          = - (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPot (fun m => bmH χ η l i m) z)
      have hfam : (fun m => bmH χ η i l m) = fun m => fun w => (-1 : ℝ) • bmH χ η l i m w := by
        funext m w; rw [hswap m w]; simp
      rw [hfam, bmPot_smul_of_cont]
      show -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * (((-1 : ℝ) • Work.CR.Flat.Cauchy.bmPot (bmH χ η l i)) z)
          = - (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPot (bmH χ η l i) z)
      rw [Pi.smul_apply, neg_one_smul]
      ring
    have hD_closed : ∀ i l k y, y ∈ polydisc 0 ρ'' →
        dbarCoord i (Ddef η l k) y - dbarCoord l (Ddef η i k) y
          + dbarCoord k (Ddef η i l) y = 0 := by
      refine closedOn_of_eq_on_open (isOpen_polydisc 0 ρ'') (fun j k y hy => ?_)
        (Work.NN.Core.bmDefectClosed hn hχ_sm hχ_cs hη hanti hcl)
      have hcy : χ y = 1 := hχ_one y (fun i => le_of_lt (by simpa using hy i))
      show -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPot (fun m => bmH χ η j k m) y
          = bmDefect χ η j k y
      have hdef : bmDefect χ η j k y = (χ y - 1) * η j k y
            + -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
              * Work.CR.Flat.Cauchy.bmPot (fun m => bmH χ η j k m) y := by
        show (χ y - 1) * η j k y - ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
              * Work.CR.Flat.Cauchy.bmPot (fun m => bmH χ η j k m) y
            = (χ y - 1) * η j k y + -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
              * Work.CR.Flat.Cauchy.bmPot (fun m => bmH χ η j k m) y
        ring
      rw [hdef, hcy]; ring
    have hsolve := TelTwoDF.S2_solves G (η := Ddef η) hD_cd1 hD_anti
      (fun i l k z hz2 => hD_closed i l k z
        (fun j => lt_of_lt_of_le (lt_trans (by simpa using hz2 j) (hGbg j)) (le_refl _)))
    have hdrow : ∀ i : Fin n,
        DifferentiableAt ℝ (bmRow (fun i' l' w => χ w * η i' l' w) i) z := by
      intro i
      have h := (contDiff_const (c := -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))).mul
        (Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport
          hn (i := 1) (fun l' => hχ_cd1.mul (hη i l')) (fun l' => hχη_cs i l'))
      have heq : bmRow (fun i' l' w => χ w * η i' l' w) i
          = fun y => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
              * Work.CR.Flat.Cauchy.bmPotential (fun l' => fun w => χ w * η i l' w) y := by
        funext y; rw [Work.NN.Core.bmRow_apply, Work.CR.Flat.Cauchy.bmPotential_eq_bmPot]
      rw [heq]; exact (h.differentiable (by norm_num)).differentiableAt
    have hdS2 : ∀ i : Fin n, DifferentiableAt ℝ (TelTwoDF.S2 G (Ddef η) i) z := by
      intro i
      have hcd := hCSreg 1 (Ddef η) hD_cd1
      exact ((hcd.1 i).contDiffAt
        ((isOpen_polydisc 0 G.e).mem_nhds (by rw [hGe]; exact hz))).differentiableAt one_ne_zero
    have hsol : dbarCoord j (TelTwoDF.S2 G (Ddef η) l) z
        - dbarCoord l (TelTwoDF.S2 G (Ddef η) j) z = Ddef η j l z :=
      hsolve j l z (by
        intro k
        show ‖z k‖ < G.e k
        rw [hGe]
        exact by simpa using hz k)
    have hbf : bmDefect χ η j l z = (χ z - 1) * η j l z + Ddef η j l z := by
      show (χ z - 1) * η j l z - ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPot (fun m => bmH χ η j l m) z
        = (χ z - 1) * η j l z + Ddef η j l z
      rw [show Ddef η j l z = -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPot (fun m => bmH χ η j l m) z from rfl]
      ring
    have hcz : χ z = 1 := hχ_one z
      (fun i => le_of_lt (lt_trans (by simpa using hz i) (hρ'ρ'' i)))
    have hbr := hbmdef j l z
    rw [hbf, hcz] at hbr
    rw [hT2_apply η hV]
    show dbarCoord j (opFun η l) z - dbarCoord l (opFun η j) z = η j l z
    rw [show opFun η l = fun w => bmRow (fun i l' w => χ w * η i l' w) l w
          - TelTwoDF.S2 G (Ddef η) l w from rfl,
      show opFun η j = fun w => bmRow (fun i l' w => χ w * η i l' w) j w
          - TelTwoDF.S2 G (Ddef η) j w from rfl,
      dbarCoord_sub_local j (hdrow l) (hdS2 l), dbarCoord_sub_local l (hdrow j) (hdS2 j)]
    linear_combination hbr - hsol
  · -- clause (b)
    intro k η hη hanti hcl
    have hV : η ∈ V := by
      rw [hVmem]; intro i l
      exact ((hη i l).of_le (by simp)).contDiffOn
    have hχη_cd : ∀ i l, ContDiff ℝ (k + 1) (fun w => χ w * η i l w) := fun i l =>
      (hχ_sm.of_le (by simp)).mul (hη i l)
    have hbmH_cd : ∀ j kk l, ContDiff ℝ (k + 1) (bmH χ η j kk l) := by
      intro j kk l
      have hd : ∀ s : Fin n, ContDiff ℝ (k + 1) (dbarCoord s χ) := fun s =>
        (contDiff_dbarCoord_of_smooth_top hχ_sm s).of_le (by simp)
      show ContDiff ℝ (k + 1) (fun w => dbarCoord l χ w * η j kk w
        + dbarCoord j χ w * η kk l w - dbarCoord kk χ w * η j l w)
      exact (((hd l).mul (hη j kk)).add ((hd j).mul (hη kk l))).sub ((hd kk).mul (hη j l))
    have hDη_cd : ∀ i l, ContDiff ℝ (k + 1) (Ddef η i l) := by
      intro i l
      have h := (contDiff_const (c := -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))).mul
        (Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport hn (i := k + 1)
          (fun l' => hbmH_cd i l l') (fun l' => hbmH_cs_all η i l l'))
      have heq : (fun y => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
            * Work.CR.Flat.Cauchy.bmPotential (fun l' => bmH χ η i l l') y) = Ddef η i l := by
        funext y
        show -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
              * Work.CR.Flat.Cauchy.bmPotential (fun l' => bmH χ η i l l') y
            = -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
              * Work.CR.Flat.Cauchy.bmPot (fun l' => bmH χ η i l l') y
        rw [Work.CR.Flat.Cauchy.bmPotential_eq_bmPot]
      rw [← heq]; exact h
    have hbrow_sm_all : ∀ j : Fin n,
        ContDiffOn ℝ (k + 1) (bmRow (fun i l w => χ w * η i l w) j) (polydisc 0 ρ') :=
      fun j => (contDiff_bmRow_of hn hχη_cd (fun i l => hχη_cs_all η i l) j).contDiffOn
    have hs2_sm_all : ∀ j : Fin n,
        ContDiffOn ℝ (k + 1) (TelTwoDF.S2 G (Ddef η) j) (polydisc 0 ρ') := fun j => by
      have h := (hCSreg (k + 1) (Ddef η) hDη_cd).1 j
      rwa [hGe] at h
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [hT2_apply η hV]
      rw [show opFun η j = fun w => bmRow (fun i l w => χ w * η i l w) j w
          - TelTwoDF.S2 G (Ddef η) j w from rfl]
      exact (hbrow_sm_all j).sub (hs2_sm_all j)
    · set S : ℝ≥0∞ := ∑ j, ∑ l, holderNorm k α (η j l) (polydisc 0 ρ) with hSdef
      have hrow : holderNorm (k + 1) α (bmRow (fun i l w => χ w * η i l w) j) (polydisc 0 ρ')
          ≤ ENNReal.ofReal (Crow k) * S := by
        have h := hCrowbd k η hη j
        rwa [← hSdef] at h
      have hinner : ∀ i l : Fin n, holderNorm (k + 1) α (Ddef η i l) (polydisc 0 G.b)
          ≤ ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k) * S := by
        intro i l
        have hmono : holderNorm (k + 1) α (Ddef η i l) (polydisc 0 G.b)
            ≤ holderNorm (k + 1) α (Ddef η i l) (polydisc 0 ρ'') :=
          holderNorm_mono_set (isOpen_polydisc 0 ρ'') (isOpen_polydisc 0 G.b)
            (fun z hz j => lt_of_lt_of_le (hz j) (le_of_lt (hGbg j))) (k + 1) α (Ddef η i l)
        have hcont : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞)
            (fun y => Work.CR.Flat.Cauchy.bmPot (fun l' => bmH χ η i l l') y)
            (polydisc 0 ρ'') := by
          have heq : (fun y => Work.CR.Flat.Cauchy.bmPot (fun l' => bmH χ η i l l') y)
              = fun y => Work.CR.Flat.Cauchy.bmPotential (fun l' => bmH χ η i l l') y := by
            funext y; exact (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot _ y).symm
          rw [heq]
          exact (Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport hn (i := k + 1)
            (fun l' => hbmH_cd i l l') (fun l' => hbmH_cs_all η i l l')).contDiffOn
        have hsm : holderNorm (k + 1) α (Ddef η i l) (polydisc 0 ρ'')
            = ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
              * holderNorm (k + 1) α
                  (fun y => Work.CR.Flat.Cauchy.bmPot (fun l' => bmH χ η i l l') y)
                  (polydisc 0 ρ'') := by
          have hD_eq : Ddef η i l = ((-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)) : ℂ)
              • (fun y => Work.CR.Flat.Cauchy.bmPot (fun l' => bmH χ η i l l') y) := by
            funext y; rfl
          rw [hD_eq, Work.CR.Flat.Holder.holderNorm_smul _ hcont
            (isOpen_polydisc 0 ρ'').uniqueDiffOn, norm_neg]
        have hpot := hCpotbd k η hη i l
        rw [← hSdef] at hpot
        calc holderNorm (k + 1) α (Ddef η i l) (polydisc 0 G.b)
            ≤ holderNorm (k + 1) α (Ddef η i l) (polydisc 0 ρ'') := hmono
          _ = ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
              * holderNorm (k + 1) α
                  (fun y => Work.CR.Flat.Cauchy.bmPot (fun l' => bmH χ η i l l') y)
                  (polydisc 0 ρ'') := hsm
          _ ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
              * (ENNReal.ofReal (Cpot k) * S) :=
              mul_le_mul_of_nonneg_left hpot bot_le
          _ = ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k) * S :=
            ofReal_mul_mul_assoc (a := ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖) (b := Cpot k)
              (norm_nonneg _) (le_of_lt (hCpotpos k)) S
      have hs2bd : holderNorm (k + 1) α (TelTwoDF.S2 G (Ddef η) j) (polydisc 0 ρ')
          ≤ ENNReal.ofReal (CS (k + 1) * ((n : ℝ) * (n : ℝ)
              * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k))) * S := by
        have hsum1 : (∑ _i : Fin n, ∑ _l : Fin n,
              (ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k) * S))
            = ENNReal.ofReal ((n : ℝ) * (n : ℝ)
                * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k)) * S := by
          have h1 : (∑ _i : Fin n, ∑ _l : Fin n,
                (ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k) * S))
              = (n : ℝ≥0∞) * ((n : ℝ≥0∞)
                  * (ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k)
                      * S)) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            rw [nsmul_eq_mul, nsmul_eq_mul]
          rw [h1, ← ENNReal.ofReal_natCast]
          rw [ofReal_mul_mul_assoc (a := (n : ℝ)) (b := (n : ℝ)) (Nat.cast_nonneg n)
            (Nat.cast_nonneg n)
            (ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k) * S)]
          exact ofReal_mul_mul_assoc (a := (n : ℝ) * (n : ℝ))
            (b := ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k)
            (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg n))
            (mul_nonneg (norm_nonneg _) (le_of_lt (hCpotpos k))) S
        calc holderNorm (k + 1) α (TelTwoDF.S2 G (Ddef η) j) (polydisc 0 ρ')
            = holderNorm (k + 1) α (TelTwoDF.S2 G (Ddef η) j) (polydisc 0 G.e) := by rw [hGe]
          _ ≤ ENNReal.ofReal (CS (k + 1))
              * ∑ i, ∑ l, holderNorm (k + 1) α (Ddef η i l) (polydisc 0 G.b) :=
                (hCSreg (k + 1) (Ddef η) hDη_cd).2 j
          _ ≤ ENNReal.ofReal (CS (k + 1))
              * ∑ i : Fin n, ∑ l : Fin n,
                  (ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k) * S) :=
                mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
                  Finset.sum_le_sum fun l _ => hinner i l) bot_le
          _ = ENNReal.ofReal (CS (k + 1))
              * (ENNReal.ofReal ((n : ℝ) * (n : ℝ)
                  * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k)) * S) := by rw [hsum1]
          _ = ENNReal.ofReal (CS (k + 1) * ((n : ℝ) * (n : ℝ)
              * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k))) * S :=
            ofReal_mul_mul_assoc (a := CS (k + 1))
              (b := (n : ℝ) * (n : ℝ) * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k))
              (le_of_lt (hCSpos (k + 1)))
              (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg n))
                (mul_nonneg (norm_nonneg _) (le_of_lt (hCpotpos k)))) S
      have hsub := holderNorm_sub_le (k := k + 1) (α := α) (hbrow_sm_all j) (hs2_sm_all j)
        (isOpen_polydisc 0 ρ').uniqueDiffOn
      calc holderNorm (k + 1) α (T2 η j) (polydisc 0 ρ')
          = holderNorm (k + 1) α (fun w => bmRow (fun i l w => χ w * η i l w) j w
              - TelTwoDF.S2 G (Ddef η) j w) (polydisc 0 ρ') := by
            rw [hT2_apply η hV]
            rw [show opFun η j = fun w => bmRow (fun i l w => χ w * η i l w) j w
                - TelTwoDF.S2 G (Ddef η) j w from rfl]
        _ ≤ holderNorm (k + 1) α (bmRow (fun i l w => χ w * η i l w) j) (polydisc 0 ρ')
            + holderNorm (k + 1) α (TelTwoDF.S2 G (Ddef η) j) (polydisc 0 ρ') := hsub
        _ ≤ ENNReal.ofReal (Crow k) * S
            + ENNReal.ofReal (CS (k + 1) * ((n : ℝ) * (n : ℝ)
                * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k))) * S :=
              add_le_add hrow hs2bd
        _ = ENNReal.ofReal (Crow k + CS (k + 1) * ((n : ℝ) * (n : ℝ)
              * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k))) * S := by
            have hq : (0 : ℝ) ≤ CS (k + 1) * ((n : ℝ) * (n : ℝ)
                * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k)) :=
              mul_nonneg (le_of_lt (hCSpos (k + 1)))
                (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg n))
                  (mul_nonneg (norm_nonneg ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))
                    (le_of_lt (hCpotpos k))))
            rw [← add_mul, ← ENNReal.ofReal_add (q := CS (k + 1) * ((n : ℝ) * (n : ℝ)
                * (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cpot k))) (le_of_lt (hCrowpos k)) hq]
  · -- clause (c)
    intro η hη hanti hcl
    have hV : η ∈ V := by rw [hVmem]; intro i l; exact (hη i l).of_le (by simp)
    have hχη_sm : ∀ i l, ContDiff ℝ (⊤ : ℕ∞) (fun w => χ w * η i l w) := fun i l =>
      contDiff_mul_of_contDiffOn hρ'''ρ (⊤ : ℕ∞) hχ_sm (hη i l) hχ_zero
    have hbmH_sm : ∀ j kk l, ContDiff ℝ (⊤ : ℕ∞) (bmH χ η j kk l) := by
      intro j kk l
      show ContDiff ℝ (⊤ : ℕ∞) (fun w => dbarCoord l χ w * η j kk w
        + dbarCoord j χ w * η kk l w - dbarCoord kk χ w * η j l w)
      exact (((contDiff_mul_of_contDiffOn hρ'''ρ (⊤ : ℕ∞)
            (contDiff_dbarCoord_of_smooth_top hχ_sm l) (hη j kk) (hχdbar_zero l)).add
          (contDiff_mul_of_contDiffOn hρ'''ρ (⊤ : ℕ∞)
            (contDiff_dbarCoord_of_smooth_top hχ_sm j) (hη kk l) (hχdbar_zero j))).sub
        (contDiff_mul_of_contDiffOn hρ'''ρ (⊤ : ℕ∞)
          (contDiff_dbarCoord_of_smooth_top hχ_sm kk) (hη j l) (hχdbar_zero kk)))
    have hDη_sm : ∀ i l, ContDiff ℝ (⊤ : ℕ∞) (Ddef η i l) := by
      intro i l
      have h := (contDiff_const (c := -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹))).mul
        (contDiff_bmPot_top hn (fun l' => hbmH_sm i l l') (fun l' => hbmH_cs_all η i l l'))
      have heq : (Ddef η i l) = fun y => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.Cauchy.bmPot (fun l' => bmH χ η i l l') y := rfl
      rw [heq]; exact h
    intro j
    have hbrow_sm : ContDiffOn ℝ (⊤ : ℕ∞) (bmRow (fun i l w => χ w * η i l w) j)
        (polydisc 0 ρ') :=
      (contDiff_bmRow_top hn hχη_sm (fun i l => hχη_cs_all η i l) j).contDiffOn
    have hs2_sm : ContDiffOn ℝ (⊤ : ℕ∞) (TelTwoDF.S2 G (Ddef η) j) (polydisc 0 ρ') := by
      have h := hCSsm (Ddef η) hDη_sm j
      rwa [hGe] at h
    rw [hT2_apply η hV]
    rw [show opFun η j = fun w => bmRow (fun i l w => χ w * η i l w) j w
        - TelTwoDF.S2 G (Ddef η) j w from rfl]
    exact hbrow_sm.sub hs2_sm

end

end Work.NN.Core
