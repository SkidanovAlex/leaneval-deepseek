/-
# Boundary behaviour of the zero-mode integrals `NOf` and `ROf`

The `L₁₂` zero-mode identity `L₁₂(𝓛_Γ f)(0) = -L₁₂(f)(0)` is proved by integrating the a.e.
identity `GOf α f r - uOf f r = mdOf f r - 2 uOf f r/(1+r) - 2 ROf f r/(1+r)²` over `(ε,ρ)` and
letting `ε → 0⁺`, `ρ → ∞`.  The boundary terms of that computation are exactly the four limits
proved here:

* `ContinuousOn (NOf f) (Ici 0)` and `Tendsto (NOf f) atTop (𝓝 0)` — `NOf f r` is the joint
  integral `∫_{(r,∞) × Iθ} K(θ) ∂_z f(z,θ)`, whose integrand is integrable on `(0,∞) × Iθ`
  (`L12Hyp.hint`); continuity in `r` (the inner set moves) is dominated convergence, and the
  limit at `+∞` is the *antitone* limit of set integrals (the intersection of the sets
  `(r,∞) × Iθ` is empty);
* `Tendsto (ROf f) (𝓝[>] 0) (𝓝 (ROf f 0))` — the tail integral of the integrable density
  `uOf f = L12dens f` is continuous at `0` (again an instance of the same dominated-convergence
  lemma, the only new input being `L12Hyp.hintL2`);
* `Tendsto (fun r => ROf f r/(1+r)) atTop (𝓝 0)` — from the tail limit `ROf f → 0` and
  `(1+r)⁻¹ → 0` (the paper's decay in `ρ`).

The two reusable ingredients are proved first, in slightly more general form:
`continuous_setIntegral_lt` (DCT for the set integrals cut by a threshold `r < φ x`) and
`tendsto_setIntegral_Ioi_atTop` (the antipodal tail limit).
-/

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Apriori.ZeroMode.L12_ZMDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Apriori.ZeroMode

open scoped Real Topology
open MeasureTheory Set Filter

/-- The standard DCT step for the a.e. convergence of `r ↦ A_r.indicator g x`. -/
lemma ae_tendsto_indicator_lt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {φ : α → ℝ} {S : Set α} {h : α → ℝ} {r₀ : ℝ}
    (hnull : μ (S ∩ {x | φ x = r₀}) = 0) :
    ∀ᵐ x ∂μ, Tendsto (fun r : ℝ => ({x' | r < φ x'}).indicator (S.indicator h) x) (𝓝 r₀)
      (𝓝 (({x' | r₀ < φ x'}).indicator (S.indicator h) x)) := by
  classical
  have hae : ∀ᵐ x ∂μ, x ∉ S ∨ φ x ≠ r₀ := by
    rw [ae_iff]
    convert hnull using 2
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, not_or, not_not]
  filter_upwards [hae] with x hx
  rcases hx with hxS | hxphi
  · have hg0 : (S.indicator h) x = 0 := Set.indicator_of_notMem hxS h
    have h0 : ∀ r : ℝ, ({x' | r < φ x'}).indicator (S.indicator h) x = 0 := by
      intro r
      rw [Set.indicator_apply, hg0]
      simp
    simp only [h0]
    exact tendsto_const_nhds
  · rcases lt_or_gt_of_ne hxphi with hlt | hgt
    · have hev : (fun _ : ℝ => ({x' | r₀ < φ x'}).indicator (S.indicator h) x) =ᶠ[𝓝 r₀]
          (fun r : ℝ => ({x' | r < φ x'}).indicator (S.indicator h) x) := by
        filter_upwards [Ioi_mem_nhds hlt] with r hr
        have hm1 : x ∉ {x' : α | r < φ x'} := fun hc => not_lt.mpr (le_of_lt hr) (by simpa using hc)
        have hm2 : x ∉ {x' : α | r₀ < φ x'} := fun hc => not_lt.mpr (le_of_lt hlt) (by simpa using hc)
        rw [Set.indicator_of_notMem hm1 (S.indicator h),
            Set.indicator_of_notMem hm2 (S.indicator h)]
      exact tendsto_const_nhds.congr' hev
    · have hev : (fun _ : ℝ => ({x' | r₀ < φ x'}).indicator (S.indicator h) x) =ᶠ[𝓝 r₀]
          (fun r : ℝ => ({x' | r < φ x'}).indicator (S.indicator h) x) := by
        filter_upwards [Iio_mem_nhds hgt] with r hr
        have hm1 : x ∈ {x' : α | r < φ x'} := by simpa using hr
        have hm2 : x ∈ {x' : α | r₀ < φ x'} := by simpa using hgt
        rw [Set.indicator_of_mem hm1 (S.indicator h),
            Set.indicator_of_mem hm2 (S.indicator h)]
      exact tendsto_const_nhds.congr' hev

theorem tendsto_setIntegral_Ioi_atTop {u : ℝ → ℝ} (hu : IntegrableOn u (Ioi 0) volume) :
    Tendsto (fun r : ℝ => ∫ x in Ioi r, u x) atTop (𝓝 0) := by
  have h := tendsto_setIntegral_of_antitone (μ := (volume : Measure ℝ)) (f := u)
    (s := fun r : ℝ => Ioi r) (fun r => measurableSet_Ioi) (fun a b hab => Ioi_subset_Ioi hab)
    ⟨0, hu⟩
  rwa [show (⋂ r : ℝ, Ioi r) = (∅ : Set ℝ) from by
    ext x; simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false, not_forall]
    exact ⟨x, lt_irrefl x⟩, setIntegral_empty] at h

theorem continuous_setIntegral_lt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : α → ℝ} {S : Set α} (hS : MeasurableSet S) (hint : IntegrableOn h S μ)
    {φ : α → ℝ} (hφ : Measurable φ) (hnull : ∀ r₀ : ℝ, μ (S ∩ {x | φ x = r₀}) = 0) :
    Continuous (fun r : ℝ => ∫ x in S ∩ {x | r < φ x}, h x ∂μ) := by
  classical
  rw [continuous_iff_continuousAt]
  intro r₀
  have hg : Integrable (S.indicator h) μ := (integrable_indicator_iff hS).mpr hint
  have haesm : AEStronglyMeasurable (S.indicator h) μ := hg.aestronglyMeasurable
  have hmeas : ∀ r : ℝ, MeasurableSet {x | r < φ x} := fun r => hφ measurableSet_Ioi
  have hkey : ∀ r : ℝ, (∫ x in S ∩ {x | r < φ x}, h x ∂μ)
      = ∫ x, ({x | r < φ x}).indicator (S.indicator h) x ∂μ := by
    intro r
    have h1 : (S ∩ {x | r < φ x}).indicator h
        = ({x | r < φ x}).indicator (S.indicator h) := by
      rw [indicator_indicator]
      exact congrArg (fun t => t.indicator h) (Set.inter_comm S {x | r < φ x})
    rw [← integral_indicator (hS.inter (hmeas r)), h1]
  simp_rw [hkey]
  exact tendsto_integral_filter_of_dominated_convergence (fun x => ‖S.indicator h x‖)
    (Eventually.of_forall fun r => haesm.indicator (hmeas r))
    (Eventually.of_forall fun _ => ae_of_all _ fun _ => norm_indicator_le_norm_self _ _)
    hg.norm (ae_tendsto_indicator_lt (hnull r₀))

theorem ZM_Nfun_limits {α : ℝ} {f : ℝ → ℝ → ℝ} (H : Work.FTS.Apriori.ZeroMode.L12Hyp α f) :
    ContinuousOn (Work.FTS.Apriori.ZeroMode.NOf f) (Set.Ici 0)
    ∧ Filter.Tendsto (Work.FTS.Apriori.ZeroMode.NOf f) Filter.atTop (𝓝 0)
    ∧ Filter.Tendsto (Work.FTS.Apriori.ZeroMode.ROf f) (𝓝[>] (0 : ℝ))
        (𝓝 (Work.FTS.Apriori.ZeroMode.ROf f 0))
    ∧ Filter.Tendsto (fun r : ℝ => Work.FTS.Apriori.ZeroMode.ROf f r / (1 + r))
        Filter.atTop (𝓝 0) := by
  have hIθ : MeasurableSet (Work.Spaces.Iθ : Set ℝ) := by
    simp only [Work.Spaces.Iθ]; exact measurableSet_Icc
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) continuity of NOf on [0,∞)
    have hnull : ∀ r₀ : ℝ, (volume : Measure (ℝ × ℝ))
        ((Ioi 0 ×ˢ (Work.Spaces.Iθ : Set ℝ)) ∩ {p : ℝ × ℝ | p.1 = r₀}) = 0 := by
      intro r₀
      refine measure_mono_null (t := ({r₀} ×ˢ (univ : Set ℝ))) ?_ ?_
      · intro p hp
        exact ⟨hp.2, mem_univ p.2⟩
      · change (volume.prod volume) ({r₀} ×ˢ (univ : Set ℝ)) = 0
        rw [Measure.prod_prod]
        simp
    have hcont : Continuous (fun r : ℝ =>
        ∫ p in (Ioi 0 ×ˢ (Work.Spaces.Iθ : Set ℝ)) ∩ {p : ℝ × ℝ | r < p.1},
          Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2 ∂(volume : Measure (ℝ × ℝ))) :=
      continuous_setIntegral_lt (μ := (volume : Measure (ℝ × ℝ)))
        (h := fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
        (S := Ioi 0 ×ˢ (Work.Spaces.Iθ : Set ℝ))
        (measurableSet_Ioi.prod hIθ) H.hint measurable_fst hnull
    refine hcont.continuousOn.congr ?_
    intro r hr
    have hset : (Ioi 0 ×ˢ (Work.Spaces.Iθ : Set ℝ)) ∩ {p : ℝ × ℝ | r < p.1}
        = (Ioi r) ×ˢ (Work.Spaces.Iθ : Set ℝ) := by
      ext p
      show (p.1 ∈ Ioi (0:ℝ) ∧ p.2 ∈ (Work.Spaces.Iθ : Set ℝ)) ∧ r < p.1 ↔
        p.1 ∈ Ioi r ∧ p.2 ∈ (Work.Spaces.Iθ : Set ℝ)
      simp only [mem_Ioi]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩; exact ⟨⟨lt_of_le_of_lt hr h3, h2⟩, h3⟩
    simp only [Work.FTS.Apriori.ZeroMode.NOf_eq]
    rw [hset]
  · -- (2) NOf → 0 at +∞
    have hIinter : (⋂ r : ℝ, (Ioi r) ×ˢ (Work.Spaces.Iθ : Set ℝ))
        = (∅ : Set (ℝ × ℝ)) := by
      ext p
      simp only [mem_iInter, mem_prod, mem_Ioi, mem_empty_iff_false, iff_false, not_forall]
      exact ⟨p.1, fun h => lt_irrefl p.1 h.1⟩
    have h := tendsto_setIntegral_of_antitone (μ := (volume : Measure (ℝ × ℝ)))
      (f := fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (s := fun r : ℝ => (Ioi r) ×ˢ (Work.Spaces.Iθ : Set ℝ))
      (fun r => measurableSet_Ioi.prod hIθ)
      (fun a b hab => Set.prod_mono (Ioi_subset_Ioi hab) subset_rfl)
      ⟨0, H.hint⟩
    rw [hIinter, setIntegral_empty] at h
    simpa only [Work.FTS.Apriori.ZeroMode.NOf_eq] using h
  · -- (3) ROf is right-continuous at 0
    have hnull : ∀ r₀ : ℝ, (volume : Measure ℝ) (Ioi 0 ∩ {x : ℝ | x = r₀}) = 0 := by
      intro r₀
      refine measure_mono_null (t := ({r₀} : Set ℝ)) ?_ ?_
      · intro x hx; exact hx.2
      · exact Real.volume_singleton
    have hcont : Continuous (fun r : ℝ =>
        ∫ x in Ioi 0 ∩ {x : ℝ | r < x}, Work.Construction.L12dens f x ∂(volume : Measure ℝ)) :=
      continuous_setIntegral_lt (μ := (volume : Measure ℝ))
        (h := Work.Construction.L12dens f) (S := Ioi 0) measurableSet_Ioi H.hintL2
        measurable_id hnull
    have hF0 : (∫ x in Ioi 0 ∩ {x : ℝ | (0:ℝ) < x},
        Work.Construction.L12dens f x ∂(volume : Measure ℝ)) = ROf f 0 := by
      rw [show Ioi 0 ∩ {x : ℝ | (0:ℝ) < x} = Ioi 0 from by ext x; simp [Set.mem_Ioi]]
      simp only [Work.FTS.Apriori.ZeroMode.ROf_eq, Work.Coercivity.L12f, Work.FM.L12,
        Work.Construction.L12dens]
    have heq : ROf f =ᶠ[𝓝[>] (0:ℝ)] (fun r : ℝ =>
        ∫ x in Ioi 0 ∩ {x : ℝ | r < x}, Work.Construction.L12dens f x ∂(volume : Measure ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [show Ioi 0 ∩ {x : ℝ | r < x} = Ioi r from by
        ext x; simp only [mem_inter_iff, mem_Ioi]; constructor
        · rintro ⟨h1, h2⟩; exact h2
        · intro h2; exact ⟨lt_trans (by simpa using hr) h2, h2⟩]
      simp only [Work.FTS.Apriori.ZeroMode.ROf_eq, Work.Coercivity.L12f, Work.FM.L12,
        Work.Construction.L12dens]
    have h1 : Tendsto (fun r : ℝ =>
        ∫ x in Ioi 0 ∩ {x : ℝ | r < x}, Work.Construction.L12dens f x ∂(volume : Measure ℝ))
        (𝓝[>] (0:ℝ)) (𝓝 (ROf f 0)) := by
      have h2 : Tendsto (fun r : ℝ =>
          ∫ x in Ioi 0 ∩ {x : ℝ | r < x}, Work.Construction.L12dens f x ∂(volume : Measure ℝ))
          (𝓝[>] (0:ℝ))
          (𝓝 (∫ x in Ioi 0 ∩ {x : ℝ | (0:ℝ) < x},
            Work.Construction.L12dens f x ∂(volume : Measure ℝ))) :=
        (hcont.continuousAt (x := 0)).continuousWithinAt (s := Ioi (0:ℝ))
      rwa [hF0] at h2
    exact h1.congr' heq.symm
  · -- (4) ROf r / (1+r) → 0 at +∞
    have htail : Tendsto (ROf f) atTop (𝓝 0) := by
      have h := tendsto_setIntegral_Ioi_atTop
        (u := fun x => Work.Construction.L12dens f x) H.hintL2
      have e : (fun r : ℝ => ∫ x in Ioi r, Work.Construction.L12dens f x) = ROf f := by
        funext r
        simp only [Work.FTS.Apriori.ZeroMode.ROf_eq, Work.Coercivity.L12f, Work.FM.L12,
          Work.Construction.L12dens]
      rwa [e] at h
    have hinv : Tendsto (fun r : ℝ => (1 + r)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
    have hmul := htail.mul hinv
    simpa [div_eq_mul_inv] using hmul

end Work.FTS.Apriori.ZeroMode
