import Mathlib
import Submission.Work.A14D.slitPieces

namespace Work.A14D

open Complex Metric Filter
open scoped Topology
open Classical

noncomputable section

/-- The function obtained by gluing `gA` (on `halfUp δ`), `gB` (on `halfDn δ`) and `gC`
(elsewhere).  On the two open pieces `halfUp δ`, `halfDn δ` it is *definitionally* equal to
`gA`, resp. `gB`. -/
def glueFun (δ : ℝ) (gA gB gC : ℂ → ℂ) : ℂ → ℂ :=
  fun z => if z ∈ halfUp δ then gA z else if z ∈ halfDn δ then gB z else gC z

lemma glueFun_eqOn_halfUp (δ : ℝ) (gA gB gC : ℂ → ℂ) :
    Set.EqOn (glueFun δ gA gB gC) gA (halfUp δ) := by
  intro z hz
  simp only [glueFun, if_pos hz]

lemma glueFun_eqOn_halfDn (δ : ℝ) (gA gB gC : ℂ → ℂ) :
    Set.EqOn (glueFun δ gA gB gC) gB (halfDn δ) := by
  intro z hz
  have hzup : z ∉ halfUp δ := by
    intro hup
    have hmem : z ∈ halfUp δ ∩ halfDn δ := ⟨hup, hz⟩
    rw [halfUp_inter_halfDn] at hmem
    exact hmem
  simp only [glueFun, if_neg hzup, if_pos hz]

lemma glueFun_eqOn_halfRt (δ : ℝ) {gA gB gC : ℂ → ℂ}
    (hAC : Set.EqOn gA gC (halfUp δ ∩ halfRt δ))
    (hBC : Set.EqOn gB gC (halfDn δ ∩ halfRt δ)) :
    Set.EqOn (glueFun δ gA gB gC) gC (halfRt δ) := by
  intro z hz
  by_cases hup : z ∈ halfUp δ
  · simp only [glueFun, if_pos hup]
    exact hAC ⟨hup, hz⟩
  · by_cases hdn : z ∈ halfDn δ
    · simp only [glueFun, if_neg hup, if_pos hdn]
      exact hBC ⟨hdn, hz⟩
    · simp only [glueFun, if_neg hup, if_neg hdn]

/-- If `F` coincides with `G` on a neighbourhood of `z`, then `LZ F z = LZ G z`: the value, the
first derivative (`EventuallyEq.deriv_eq`) and the second derivative (via `EventuallyEq.deriv`
followed by `EventuallyEq.deriv_eq`) all agree. -/
lemma LZ_congr_eventuallyEq {F G : ℂ → ℂ} {z : ℂ} (h : F =ᶠ[𝓝 z] G) : LZ F z = LZ G z := by
  have h0 : F z = G z := h.eq_of_nhds
  have h1 : deriv F z = deriv G z := h.deriv_eq
  have h2 : deriv (deriv F) z = deriv (deriv G) z := h.deriv.deriv_eq
  simp only [LZ_def, h2, h1, h0]

/-- `F`, agreeing with a differentiable `G` on an open set `U`, is differentiable at each point of
`U`. -/
lemma differentiableAt_of_eqOn_open {F G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hFG : Set.EqOn F G U) (hG : DifferentiableOn ℂ G U) {z : ℂ} (hz : z ∈ U) :
    DifferentiableAt ℂ F z :=
  (hG.differentiableAt (hU.mem_nhds hz)).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (hU.mem_nhds hz) hFG)

/-- Gluing three solutions of `LZ = 0` on the three convex pieces of the slit disc.
(Module `Submission.Work.A14D.slitPieces` provides `halfUp δ`, `halfDn δ`, `halfRt δ`, their
openness/convexity, `slitDisk_subset_union`, `halfUp_inter_halfDn`, `halfUp_subset_slitDisk`,
`halfDn_subset_slitDisk`, `halfRt_subset_slitDisk`, `isOpen_halfUp` etc.)

Set `F := fun z => if z ∈ halfUp δ then gA z else if z ∈ halfDn δ then gB z else gC z`.  Then
`F` agrees with `gA` on `halfUp δ` and with `gB` on `halfDn δ` by definition, and with `gC` on
`halfRt δ` using the two agreement hypotheses; it is holomorphic (and `LZ F = 0`) on
`slitDisk δ` because on `halfUp δ` it equals `gA` (which is open), on `halfDn δ \ halfUp δ` it
equals `gB`, and near a point of `halfRt δ \ (halfUp δ ∪ halfDn δ)` (a *real* point) a small ball
stays inside the open `halfRt δ`, on which `F = gC` by the two agreements.  Use
`Filter.EventuallyEq.deriv_eq` (twice) to transfer `deriv`, `deriv ∘ deriv`. -/
theorem glue_three_LZ {δ : ℝ} {gA gB gC : ℂ → ℂ}
    (hAd : DifferentiableOn ℂ gA (halfUp δ)) (hBd : DifferentiableOn ℂ gB (halfDn δ))
    (hCd : DifferentiableOn ℂ gC (halfRt δ))
    (hLA : ∀ z ∈ halfUp δ, LZ gA z = 0) (hLB : ∀ z ∈ halfDn δ, LZ gB z = 0)
    (hLC : ∀ z ∈ halfRt δ, LZ gC z = 0)
    (hAC : Set.EqOn gA gC (halfUp δ ∩ halfRt δ))
    (hBC : Set.EqOn gB gC (halfDn δ ∩ halfRt δ)) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (slitDisk δ) ∧ (∀ z ∈ slitDisk δ, LZ F z = 0) ∧
      Set.EqOn F gA (halfUp δ) ∧ Set.EqOn F gB (halfDn δ) ∧ Set.EqOn F gC (halfRt δ) := by
  refine ⟨glueFun δ gA gB gC, ?_, ?_, glueFun_eqOn_halfUp δ gA gB gC,
    glueFun_eqOn_halfDn δ gA gB gC, glueFun_eqOn_halfRt δ hAC hBC⟩
  · intro z hz
    rcases slitDisk_subset_union δ hz with (hup | hdn) | hrt
    · exact (differentiableAt_of_eqOn_open (isOpen_halfUp δ) (glueFun_eqOn_halfUp δ gA gB gC)
        hAd hup).differentiableWithinAt
    · exact (differentiableAt_of_eqOn_open (isOpen_halfDn δ) (glueFun_eqOn_halfDn δ gA gB gC)
        hBd hdn).differentiableWithinAt
    · exact (differentiableAt_of_eqOn_open (isOpen_halfRt δ) (glueFun_eqOn_halfRt δ hAC hBC)
        hCd hrt).differentiableWithinAt
  · intro z hz
    rcases slitDisk_subset_union δ hz with (hup | hdn) | hrt
    · rw [LZ_congr_eventuallyEq (Filter.eventuallyEq_of_mem ((isOpen_halfUp δ).mem_nhds hup)
        (glueFun_eqOn_halfUp δ gA gB gC))]
      exact hLA z hup
    · rw [LZ_congr_eventuallyEq (Filter.eventuallyEq_of_mem ((isOpen_halfDn δ).mem_nhds hdn)
        (glueFun_eqOn_halfDn δ gA gB gC))]
      exact hLB z hdn
    · rw [LZ_congr_eventuallyEq (Filter.eventuallyEq_of_mem ((isOpen_halfRt δ).mem_nhds hrt)
        (glueFun_eqOn_halfRt δ hAC hBC))]
      exact hLC z hrt

end

end Work.A14D
