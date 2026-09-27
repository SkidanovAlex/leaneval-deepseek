import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLC6Core.measurable_growthFun

namespace Work.EKLRelCross

open MeasureTheory
open scoped ENNReal

/-!
# `Work.EKLRelCross.restrict_eq_of_pushforward_relation`

If two Radon measures `ρ`, `ρ'` on `SL₃(ℝ)` are both normalised by `Box1 U` and their
push-forwards along the orbit map `g ↦ g • x` (restricted to a measurable set `S ⊆ U`) are
proportional with the *opposite* proportionality constants `ρ' S`, `ρ S`, then `ρ` and `ρ'`
agree on `S`.

The mathematics: the orbit map is injective on the closed subgroup `U` (freeness at `x`), hence a
measurable embedding after restricting to `U`, so push-forward along it is injective on measures
carried by `U`.  This forces `(ρ' S) • (ρ ↾ S) = (ρ S) • (ρ' ↾ S)`, and evaluating at
`Box1 U ⊆ S` (both measures give `1` there, and `ρ' S ≠ 0`) yields `ρ' S = ρ S` and hence
`ρ ↾ S = ρ' ↾ S`.
-/

/-- If `μ sᶜ = 0`, then for every `t` the measure of `t` equals the measure of `t ∩ s`. -/
theorem measure_eq_measure_inter_of_compl_null
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) {s t : Set α}
    (hs : μ sᶜ = 0) : μ t = μ (t ∩ s) := by
  have h0 : μ (t \ s) = 0 := measure_mono_null (Set.sdiff_subset_compl t s) hs
  apply le_antisymm
  · calc μ t ≤ μ ((t ∩ s) ∪ (t \ s)) := measure_mono (by
            intro x hx
            by_cases hxs : x ∈ s
            · exact Or.inl ⟨hx, hxs⟩
            · exact Or.inr ⟨hx, hxs⟩)
      _ ≤ μ (t ∩ s) + μ (t \ s) := measure_union_le _ _
      _ = μ (t ∩ s) := by rw [h0, add_zero]
  · exact measure_mono Set.inter_subset_left

/-- The orbit map `g ↦ g • x` is injective on a closed subgroup `U` acting freely at `x`; hence
its push-forward is injective on measures carried by `U`. -/
theorem map_smul_injective_of_free (U : Subgroup Work.EKLContract.SL3)
    (hUcl : IsClosed (U : Set Work.EKLContract.SL3)) (x : Work.EKLContract.X3)
    (hfree : ∀ u ∈ U, u • x = x → u = 1)
    {μ ν : MeasureTheory.Measure Work.EKLContract.SL3}
    (hμ : μ (U : Set Work.EKLContract.SL3)ᶜ = 0)
    (hν : ν (U : Set Work.EKLContract.SL3)ᶜ = 0)
    (h : μ.map (fun g : Work.EKLContract.SL3 => g • x)
          = ν.map (fun g : Work.EKLContract.SL3 => g • x)) : μ = ν := by
  classical
  haveI : PolishSpace Work.EKLContract.SL3 :=
    Work.EKLContract.Lemmas.polishSpace_specialLinearGroup
  haveI : PolishSpace U := hUcl.polishSpace
  have hφinj : Function.Injective (fun u : U => (u : Work.EKLContract.SL3) • x) := by
    intro a b hab
    have hab' : (a : Work.EKLContract.SL3) • x = (b : Work.EKLContract.SL3) • x := hab
    have hmem : (b : Work.EKLContract.SL3)⁻¹ * (a : Work.EKLContract.SL3) ∈ U :=
      mul_mem (U.inv_mem b.2) a.2
    have hfix : ((b : Work.EKLContract.SL3)⁻¹ * (a : Work.EKLContract.SL3)) • x = x := by
      rw [mul_smul, hab', ← mul_smul, inv_mul_cancel, one_smul]
    have hone : (b : Work.EKLContract.SL3)⁻¹ * (a : Work.EKLContract.SL3) = 1 :=
      hfree _ hmem hfix
    have h2 : (a : Work.EKLContract.SL3) = (b : Work.EKLContract.SL3) := by
      have h3 := congrArg (fun g : Work.EKLContract.SL3 => (b : Work.EKLContract.SL3) * g) hone
      simpa using h3
    exact Subtype.ext h2
  have hφcont : Continuous (fun u : U => (u : Work.EKLContract.SL3) • x) := by fun_prop
  have hφ : MeasurableEmbedding (fun u : U => (u : Work.EKLContract.SL3) • x) :=
    hφcont.measurableEmbedding hφinj
  obtain ⟨ψ, hψmeas, hψeq⟩ :=
    hφ.exists_measurable_extend (g := id) measurable_id (fun _ => ⟨1⟩)
  have hψ : ∀ u : U, ψ ((u : Work.EKLContract.SL3) • x) = u := fun u => congr_fun hψeq u
  have hφ'meas : Measurable (fun g : Work.EKLContract.SL3 => g • x) := by fun_prop
  refine MeasureTheory.Measure.ext (fun A hA => ?_)
  let B : Set Work.EKLContract.X3 := {y | ((ψ y : U) : Work.EKLContract.SL3) ∈ A}
  have hBmeas : MeasurableSet B :=
    hA.preimage (continuous_subtype_val.measurable.comp hψmeas)
  have hpre : (fun g : Work.EKLContract.SL3 => g • x) ⁻¹' B ∩ (U : Set Work.EKLContract.SL3)
      = A ∩ (U : Set Work.EKLContract.SL3) := by
    ext g
    constructor
    · rintro ⟨hg, hgU⟩
      have hg' : ((ψ (g • x) : U) : Work.EKLContract.SL3) ∈ A := hg
      have h1 : ψ (g • x) = (⟨g, hgU⟩ : U) := by
        rw [show g • x = ((⟨g, hgU⟩ : U) : Work.EKLContract.SL3) • x from rfl, hψ ⟨g, hgU⟩]
      rw [h1] at hg'
      exact ⟨hg', hgU⟩
    · rintro ⟨hgA, hgU⟩
      have h1 : ψ (g • x) = (⟨g, hgU⟩ : U) := by
        rw [show g • x = ((⟨g, hgU⟩ : U) : Work.EKLContract.SL3) • x from rfl, hψ ⟨g, hgU⟩]
      refine ⟨?_, hgU⟩
      show ((ψ (g • x) : U) : Work.EKLContract.SL3) ∈ A
      rw [h1]
      exact hgA
  have hmapA : μ A = (μ.map (fun g : Work.EKLContract.SL3 => g • x)) B := by
    rw [MeasureTheory.Measure.map_apply hφ'meas hBmeas]
    rw [measure_eq_measure_inter_of_compl_null μ hμ (t := A),
        measure_eq_measure_inter_of_compl_null μ hμ
          (t := (fun g : Work.EKLContract.SL3 => g • x) ⁻¹' B), hpre]
  have hmapB : ν A = (ν.map (fun g : Work.EKLContract.SL3 => g • x)) B := by
    rw [MeasureTheory.Measure.map_apply hφ'meas hBmeas]
    rw [measure_eq_measure_inter_of_compl_null ν hν (t := A),
        measure_eq_measure_inter_of_compl_null ν hν
          (t := (fun g : Work.EKLContract.SL3 => g • x) ⁻¹' B), hpre]
  calc μ A = (μ.map (fun g : Work.EKLContract.SL3 => g • x)) B := hmapA
    _ = (ν.map (fun g : Work.EKLContract.SL3 => g • x)) B := by rw [h]
    _ = ν A := hmapB.symm

theorem restrict_eq_of_pushforward_relation (U : Subgroup Work.EKLContract.SL3) (x : Work.EKLContract.X3) (S : Set Work.EKLContract.SL3)
    (hUcl : IsClosed (U : Set Work.EKLContract.SL3)) (hBoxc : IsCompact (Work.EKLContract.Box1 U))
    (hSmeas : MeasurableSet S) (hBoxS : Work.EKLContract.Box1 U ⊆ S) (hSU : S ⊆ (U : Set Work.EKLContract.SL3))
    (hfree : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂)
    (ρ ρ' : MeasureTheory.Measure Work.EKLContract.SL3) [MeasureTheory.IsFiniteMeasureOnCompacts ρ] [MeasureTheory.IsFiniteMeasureOnCompacts ρ']
    (hSfin : ρ S ≠ ⊤) (hSfin' : ρ' S ≠ ⊤)
    (hρ1 : ρ (Work.EKLContract.Box1 U) = 1) (hρ'1 : ρ' (Work.EKLContract.Box1 U) = 1)
    (hrel : (ρ' S) • ((ρ.restrict S).map (fun g : Work.EKLContract.SL3 => g • x))
      = (ρ S) • ((ρ'.restrict S).map (fun g : Work.EKLContract.SL3 => g • x))) :
    ρ.restrict S = ρ'.restrict S := by
  have hfree1 : ∀ u ∈ U, u • x = x → u = 1 := by
    intro u hu hux
    exact hfree u hu 1 U.one_mem (by simpa using hux)
  have hdisj : (U : Set Work.EKLContract.SL3)ᶜ ∩ S = ∅ := by
    rw [← Set.subset_empty_iff]
    intro g hg
    exact hg.1 (hSU hg.2)
  have hcar : (ρ.restrict S) (U : Set Work.EKLContract.SL3)ᶜ = 0 := by
    rw [MeasureTheory.Measure.restrict_apply hUcl.measurableSet.compl, hdisj]; simp
  have hcar' : (ρ'.restrict S) (U : Set Work.EKLContract.SL3)ᶜ = 0 := by
    rw [MeasureTheory.Measure.restrict_apply hUcl.measurableSet.compl, hdisj]; simp
  have hcarS : ((ρ' S) • (ρ.restrict S)) (U : Set Work.EKLContract.SL3)ᶜ = 0 := by
    rw [MeasureTheory.Measure.smul_apply, hcar, smul_zero]
  have hcarS' : ((ρ S) • (ρ'.restrict S)) (U : Set Work.EKLContract.SL3)ᶜ = 0 := by
    rw [MeasureTheory.Measure.smul_apply, hcar', smul_zero]
  have hmap : ((ρ' S) • (ρ.restrict S)).map (fun g : Work.EKLContract.SL3 => g • x)
      = ((ρ S) • (ρ'.restrict S)).map (fun g : Work.EKLContract.SL3 => g • x) := by
    rw [MeasureTheory.Measure.map_smul, MeasureTheory.Measure.map_smul] <;> try fun_prop
    exact hrel
  have hkey : (ρ' S) • (ρ.restrict S) = (ρ S) • (ρ'.restrict S) :=
    map_smul_injective_of_free U hUcl x hfree1 hcarS hcarS' hmap
  have hBox1_meas : MeasurableSet (Work.EKLContract.Box1 U) := hBoxc.isClosed.measurableSet
  have hIntS : Work.EKLContract.Box1 U ∩ S = Work.EKLContract.Box1 U := Set.inter_eq_left.mpr hBoxS
  have hval : ρ' S = ρ S := by
    have h1 := congrArg
      (fun μ : MeasureTheory.Measure Work.EKLContract.SL3 => μ (Work.EKLContract.Box1 U)) hkey
    rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.smul_apply,
        MeasureTheory.Measure.restrict_apply hBox1_meas, hIntS, hρ1,
        MeasureTheory.Measure.restrict_apply hBox1_meas, hIntS, hρ'1] at h1
    simpa only [smul_eq_mul, mul_one] using h1
  have hb : ρ' S ≠ 0 := by
    intro h0
    have hle : (1 : ENNReal) ≤ ρ' S := by rw [← hρ'1]; exact measure_mono hBoxS
    rw [h0] at hle
    exact one_ne_zero (le_antisymm hle bot_le)
  have h2 : (ρ' S) • (ρ.restrict S) = (ρ' S) • (ρ'.restrict S) := by
    rw [hkey, hval]
  refine MeasureTheory.Measure.ext (fun A hA => ?_)
  have h3 := congrArg (fun μ : MeasureTheory.Measure Work.EKLContract.SL3 => μ A) h2
  rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.smul_apply, smul_eq_mul,
      smul_eq_mul] at h3
  exact (ENNReal.mul_right_inj hb hSfin').mp h3

end Work.EKLRelCross
