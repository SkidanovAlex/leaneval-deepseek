/-
# `PhiStarE5` — transferring the pointwise decay to the smooth representative

A.e.-equality on the quadrant gives a.e.-equality of the `θ`-slices (Fubini); slice continuity
then upgrades it to equality of the slices, hence of the rays, so that the pointwise decay of
the weak solution transfers to its smooth representative. -/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.PhiStarE5.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.PhiStarE5

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst (SmoothOpen Q0 mem_Q0 smoothOpen_of_forall)

set_option autoImplicit false
noncomputable section

/-! ## 6. Transferring the pointwise decay to the smooth representative

Given a weak solution `Ψ` of `bslOp α Ψ = F` (with the decay along every ray) and a `C^∞`
function `Φ` agreeing with `Ψ` a.e. on the open quadrant (its smooth representative), the decay
of `Ψ` transfers to `Φ`.  The point is that a.e.-equality on the quadrant gives, by Fubini,
a.e.-equality of the `θ`-slices; if the slices of `Ψ` are continuous (for a.e. `z`) and those of
`Φ` always are, the slices agree *everywhere*, hence so do the rays, and continuity in `z` plus
the decay of `Ψ` along the ray gives the decay of `Φ`.  (`a.e.`-equality alone would not
determine the values on a single ray.) -/

/-- **Fubini for a.e. equality**: a.e.-equality of two functions on a product of measures gives
a.e.-equality of the sections, for a.e. first coordinate. -/
theorem ae_slice_eq_of_ae_eq {Φ Ψ : ℝ → ℝ → ℝ}
    (h : (fun p : ℝ × ℝ => Φ p.1 p.2)
        =ᵐ[volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))]
        (fun p : ℝ × ℝ => Ψ p.1 p.2)) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      (fun θ => Φ z θ) =ᵐ[volume.restrict (Set.Ioo 0 (π / 2))] (fun θ => Ψ z θ) := by
  have hmeas : (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))
      = ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))) := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod]
  rw [hmeas] at h
  exact MeasureTheory.Measure.ae_ae_eq_of_ae_eq_uncurry h

/-- Two functions that are continuous on an open set and agree a.e. there agree everywhere. -/
theorem eqOn_of_ae_eq_of_continuousOn {f g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (h : f =ᵐ[volume.restrict s] g) : ∀ x ∈ s, f x = g x := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, hxs, hxne⟩ := hcon
  have hUopen : IsOpen {y : ℝ | y ∈ s ∧ f y ≠ g y} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨hys, hyne⟩ := hy
    have hf' : ContinuousAt f y := (hf.continuousWithinAt hys).continuousAt (hs.mem_nhds hys)
    have hg' : ContinuousAt g y := (hg.continuousWithinAt hys).continuousAt (hs.mem_nhds hys)
    have hcont : ContinuousAt (fun y => f y - g y) y := hf'.sub hg'
    have hne : f y - g y ≠ 0 := sub_ne_zero.mpr hyne
    have hnb : (fun y => f y - g y) ⁻¹' ({0}ᶜ) ∈ 𝓝 y :=
      hcont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hne)
    refine Filter.inter_mem (hs.mem_nhds hys) ?_
    refine Filter.mem_of_superset hnb ?_
    intro y' hy'
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hy' ⊢
    exact sub_ne_zero.mp hy'
  have hUne : ({y : ℝ | y ∈ s ∧ f y ≠ g y}).Nonempty := ⟨x, hxs, hxne⟩
  have hpos : 0 < volume {y : ℝ | y ∈ s ∧ f y ≠ g y} :=
    IsOpen.measure_pos volume hUopen hUne
  have hnull : volume {y : ℝ | y ∈ s ∧ f y ≠ g y} = 0 := by
    have h' : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ s → f y = g y := by
      rw [← MeasureTheory.ae_restrict_iff' hs.measurableSet]; exact h
    have hz := MeasureTheory.ae_iff.mp h'
    have hset : {y : ℝ | y ∈ s ∧ f y ≠ g y}
        = {y : ℝ | ¬(y ∈ s → f y = g y)} := by
      ext y
      simp only [Set.mem_ofPred_eq, not_imp]
    rw [hset]
    exact hz
  exact absurd hnull (ne_of_gt hpos)

/-- **The slices of the smooth representative agree with those of the weak solution
everywhere**, for a.e. `z`. -/
theorem ae_slice_eq_all {Φ Ψ : ℝ → ℝ → ℝ} (hΦ : SmoothOpen Φ)
    (hslice : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => Ψ z θ) (Set.Ioo 0 (π / 2)))
    (hae : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      (fun θ => Φ z θ) =ᵐ[volume.restrict (Set.Ioo 0 (π / 2))] (fun θ => Ψ z θ)) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), ∀ θ ∈ Set.Ioo 0 (π / 2), Φ z θ = Ψ z θ := by
  filter_upwards [hslice, hae, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with
    z hslicez haez hzpos
  have hcΦ : ContinuousOn (fun θ => Φ z θ) (Set.Ioo 0 (π / 2)) := by
    have h0 : ContDiffOn ℝ 0 (Function.uncurry Φ) Q0 := SmoothOpen.forall hΦ 0
    have h1 : ContDiffOn ℝ 0 (fun θ : ℝ => Φ z θ) (Set.Ioo 0 (π / 2)) :=
      h0.comp ((contDiffOn_const (c := z)).prodMk contDiffOn_id)
        (fun θ hθ => mem_Q0.mpr ⟨hzpos, hθ.1, hθ.2⟩)
    exact h1.continuousOn
  exact eqOn_of_ae_eq_of_continuousOn isOpen_Ioo hcΦ hslicez haez

/-- A function that agrees a.e. (on `(0,∞)`) with a function tending to `0` at infinity and is
continuous on `(0,∞)` tends to `0` at infinity. -/
theorem tendsto_of_ae_eq_of_tendsto {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi 0)) (hg : Tendsto g atTop (𝓝 0))
    (h : f =ᵐ[volume.restrict (Set.Ioi 0)] g) :
    Tendsto f atTop (𝓝 0) := by
  by_contra hc
  rw [Metric.tendsto_atTop] at hc hg
  push_neg at hc
  obtain ⟨ε, hε, hfreq⟩ := hc
  obtain ⟨R, hR⟩ := hg (ε / 2) (by linarith)
  -- the null set where `f` and `g` differ
  set S : Set ℝ := {y : ℝ | y ∈ Set.Ioi 0 ∧ f y ≠ g y} with hSdef
  have hSnull : volume S = 0 := by
    have h'' : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Set.Ioi 0 → f y = g y := by
      rw [← MeasureTheory.ae_restrict_iff' measurableSet_Ioi]; exact h
    have hz := MeasureTheory.ae_iff.mp h''
    have hset : S = {y : ℝ | ¬(y ∈ Set.Ioi 0 → f y = g y)} := by
      ext y
      simp only [hSdef, Set.mem_ofPred_eq, not_imp]
    rw [hset]
    exact hz
  -- the set where `f` is large is open on `(0,∞)`
  have hAopen : IsOpen ({t : ℝ | ε / 2 < |f t|} ∩ Set.Ioi 0) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨hyA, hy0⟩ := hy
    have hcont : ContinuousAt f y :=
      (hf.continuousWithinAt hy0).continuousAt (isOpen_Ioi.mem_nhds hy0)
    have hnb : {y' : ℝ | ε / 2 < |f y'|} ∈ 𝓝 y := by
      have h1 : Set.Ioi (ε / 2) ∈ 𝓝 (|f y|) := isOpen_Ioi.mem_nhds hyA
      have h2 : ContinuousAt (fun y' => |f y'|) y := hcont.abs
      exact h2.preimage_mem_nhds h1
    exact Filter.inter_mem hnb (isOpen_Ioi.mem_nhds hy0)
  have hAunb : ∀ N : ℝ, ∃ y, y > N ∧ ε / 2 < |f y| ∧ y ∈ Set.Ioi 0 := by
    intro N
    obtain ⟨y, hyN, hyε⟩ := hfreq (max N 0 + 1)
    have hdist : dist (f y) 0 = |f y| := by rw [Real.dist_eq, sub_zero]
    rw [hdist] at hyε
    exact ⟨y, by linarith [le_max_left N 0], by linarith,
      by simp only [Set.mem_Ioi]; linarith [le_max_right N 0]⟩
  -- an open neighbourhood of some large point, hence not contained in the null set
  obtain ⟨y, hyU, hyeq⟩ : ∃ y ∈ (({t : ℝ | ε / 2 < |f t|} ∩ Set.Ioi 0) ∩ Set.Ioi (max R 0)),
      f y = g y := by
    by_contra hcon
    push_neg at hcon
    have hsub : (({t : ℝ | ε / 2 < |f t|} ∩ Set.Ioi 0) ∩ Set.Ioi (max R 0)) ⊆ S := by
      intro y hy
      exact ⟨hy.1.2, hcon y hy⟩
    obtain ⟨y₀, hy₀1, hy₀2, hy₀3⟩ := hAunb (max R 0)
    have hne : ((({t : ℝ | ε / 2 < |f t|} ∩ Set.Ioi 0) ∩ Set.Ioi (max R 0))).Nonempty :=
      ⟨y₀, ⟨⟨hy₀2, hy₀3⟩, hy₀1⟩⟩
    have hpos : 0 < volume
        (({t : ℝ | ε / 2 < |f t|} ∩ Set.Ioi 0) ∩ Set.Ioi (max R 0)) :=
      IsOpen.measure_pos volume (hAopen.inter isOpen_Ioi) hne
    have hle : volume (({t : ℝ | ε / 2 < |f t|} ∩ Set.Ioi 0) ∩ Set.Ioi (max R 0)) ≤ 0 := by
      rw [← hSnull]; exact measure_mono hsub
    exact absurd hle (not_le.mpr hpos)
  have hgt : y > R := by
    have := hyU.2; simp only [Set.mem_Ioi] at this; linarith [le_max_left R 0]
  have hlarge : ε / 2 < |f y| := hyU.1.1
  have hsmall : |g y| < ε / 2 := by
    have := hR y (le_of_lt hgt)
    rwa [Real.dist_eq, sub_zero] at this
  rw [hyeq] at hlarge
  linarith

/-- **The decay of the smooth representative.** -/
theorem smoothRep_decay {Φ Ψ : ℝ → ℝ → ℝ} (hΦ : SmoothOpen Φ)
    (hae : (fun p : ℝ × ℝ => Φ p.1 p.2)
      =ᵐ[volume.restrict Q0] (fun p : ℝ × ℝ => Ψ p.1 p.2))
    (hslice : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => Ψ z θ) (Set.Ioo 0 (π / 2)))
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Ψ z θ) atTop (𝓝 0)) :
    ∀ θ ∈ Set.Ioo 0 (π / 2), Tendsto (fun z => Φ z θ) atTop (𝓝 0) := by
  have h1 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      (fun θ => Φ z θ) =ᵐ[volume.restrict (Set.Ioo 0 (π / 2))] (fun θ => Ψ z θ) :=
    ae_slice_eq_of_ae_eq hae
  have h2 := ae_slice_eq_all hΦ hslice h1
  intro θ hθ
  have h3 : (fun z => Φ z θ) =ᵐ[volume.restrict (Set.Ioi 0)] (fun z => Ψ z θ) :=
    h2.mono (fun z hz => hz θ hθ)
  have hcΦ : ContinuousOn (fun z => Φ z θ) (Set.Ioi 0) := by
    have h0 : ContDiffOn ℝ 0 (Function.uncurry Φ) Q0 := SmoothOpen.forall hΦ 0
    have h1' : ContDiffOn ℝ 0 (fun z : ℝ => Φ z θ) (Set.Ioi 0) :=
      h0.comp (contDiffOn_id.prodMk (contDiffOn_const (c := θ)))
        (fun z hz => mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)
    exact h1'.continuousOn
  exact tendsto_of_ae_eq_of_tendsto hcΦ (hdec θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) h3

end

end Work.FTS.H2.PhiStarE5
