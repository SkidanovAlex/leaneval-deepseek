import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.fiber_inv_finite
import Submission.Work.EKLC6Core.hopf_saturate
import Submission.Work.EKLC6Core.borel_atom_saturated_measurable
import Submission.Work.EKLC6Core.invariant_inter_plaque_ae
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.measurable_growthFun
import Submission.Work.EKLComp.prove_X3
import Submission.Work.EKLC7.LeafwiseComponentFull
import Submission.Work.EKLRelCross.leafwise_unique
import Submission.Work.EKLRelCross.bigShape_flowers_fr
import Submission.Work.EKLC6Core.leafwise_eq_of_flower_clauses

/-!
# `Work.EKLC6Core.fiber_leafwise` — the fibre conditional measures carry the leafwise system
(Pisa 7.22 / 7.23)

For a probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, `T = aDiag t ·` preserving `μ`, a
leafwise system `ν` for the contracted horospherical subgroup `U = Uminus t`, and `ν` `A`-covariant
on a conull set `X''`, the conditional measures of `μ` over the σ-algebra of `T`-invariant sets
carry the *same* leafwise system: for `μ`-a.e. `x`,

`IsLeafwise (condExpKernel μ (invariants T) x) (Uminus t) ν X'`.

## Strategy

* The seven pointwise fields (`radon`, `carried`, `normalised`, `measurable`, `pos`,
  `equivariant`, `meas_dom`) are inherited verbatim from `hL`; the `conull` field is the fact
  that the conditional measures of a conull set are a.e. conull.
* The `condexp` field is the mathematical content.  For a *fixed* plaque algebra `(Z,m)` and a
  bounded Borel `f`, we show for `μ`-a.e. `x` that the plaque average
  `G y = (∫ u in shape m U y, f (u • y) ∂(ν y)) / (ν y (shape m U y)).toReal` is a version of
  `condExp m ((κ x)|_Z) f`.  The two ingredients are
  1. `Φ = condExp m (μ|_Z) f` agrees with `G` `μ|_Z`-a.e. (the `condexp` field of `hL`), hence,
     for `μ`-a.e. `x`, also `(κ x)|_Z`-a.e. (a Borel null superset of the exceptional set has
     `κ x`-measure zero for a.e. `x`);
  2. the *transfer*: for every `A ∈ m`, `Φ` satisfies the defining integral identity of
     `condExp m ((κ x)|_Z) f`.  This goes through the `(β′)`-step of Pisa 7.23
     (`invariant_inter_plaque_ae`): every `T`-invariant measurable set has an `m`-measurable
     version modulo `μ` on `Z`; Dynkin's π-λ theorem upgrades the identity from a countable
     π-system generating `m` to all of `m`.
* The uniformity of the `condexp` clause over *all* plaque algebras and test functions is then
  obtained by rigidity: the countable family of "flowers" (`bigShape_flowers_fr`) together with
  a candidate system satisfying the pointwise fields determines the leafwise system
  (`leafwise_eq_of_flower_clauses`); the fibre also *has* a leafwise system by `P_Leafwise`
  (`Work.EKLC7.P_Leafwise_proved`), so `ν` is a.e. equal to it and inherits all its fields.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal symmDiff

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## Two elementary helpers -/

/-- If `B` is a `μ`-null *measurable* set, then the conditional measures of `μ` over the
σ-algebra of `T`-invariant sets vanish on `B` almost everywhere. -/
private theorem condExpKernel_eq_zero_of_null {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] [StandardBorelSpace X3]
    {T : X3 → X3} (hT : Measurable T)
    {B : Set X3} (hBmeas : MeasurableSet B) (hB0 : μ B = 0) :
    ∀ᵐ x ∂μ, ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x B = 0 := by
  have hm : MeasurableSpace.invariants T ≤ (inferInstance : MeasurableSpace X3) :=
    MeasurableSpace.invariants_le T
  have hind : B.indicator (fun _ => (1 : ℝ)) =ᵐ[μ] (0 : X3 → ℝ) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine le_antisymm ?_ bot_le
    refine le_trans (MeasureTheory.measure_mono ?_) (le_of_eq hB0)
    intro x hx
    by_contra hxc
    exact hx (by simp [Set.indicator_of_notMem hxc])
  have h2 : μ[B.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.invariants T]
      =ᵐ[μ] (0 : X3 → ℝ) := by
    have h := MeasureTheory.condExp_congr_ae (μ := μ) (m := MeasurableSpace.invariants T) hind
    rwa [MeasureTheory.condExp_zero] at h
  have hreal : (fun x => (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x).real B)
      =ᵐ[μ] (0 : X3 → ℝ) :=
    (ProbabilityTheory.condExpKernel_ae_eq_condExp (μ := μ)
      (m := MeasurableSpace.invariants T) hm hBmeas).trans h2
  filter_upwards [hreal] with x hx
  haveI : IsProbabilityMeasure (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) :=
    IsMarkovKernel.isProbabilityMeasure x
  have hfin : ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x B < ⊤ := by
    refine lt_of_le_of_lt (MeasureTheory.measure_mono (Set.subset_univ B)) ?_
    rw [MeasureTheory.measure_univ]
    exact ENNReal.one_lt_top
  rw [MeasureTheory.measureReal_def] at hx
  rcases (ENNReal.toReal_eq_zero_iff _).mp hx with h | h
  · exact h
  · exact absurd h (ne_of_lt hfin)

/-- A normalised set average of a function bounded by `C ≥ 0` is again bounded by `C`. -/
private theorem abs_setIntegral_div_toReal_le {α : Type*} [MeasurableSpace α]
    (ρ : MeasureTheory.Measure α) (S : Set α) (f : α → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ y, |f y| ≤ C) :
    |(∫ y in S, f y ∂ρ) / (ρ S).toReal| ≤ C := by
  by_cases hS : ρ S = ⊤
  · rw [hS, ENNReal.toReal_top, div_zero, abs_zero]
    exact hC
  · have hSlt : ρ S < ∞ := lt_top_iff_ne_top.mpr hS
    by_cases hS0 : ρ S = 0
    · have hzero : (∫ y in S, f y ∂ρ) = 0 := by
        rw [MeasureTheory.Measure.restrict_eq_zero.mpr hS0]
        simp
      rw [hS0, ENNReal.toReal_zero, div_zero, abs_zero]
      exact hC
    · have hpos : 0 < (ρ S).toReal := ENNReal.toReal_pos hS0 hS
      have hbound : |∫ y in S, f y ∂ρ| ≤ C * (ρ S).toReal := by
        have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := ρ) (f := f) (s := S)
          (C := C) hSlt (fun y _ => by simpa [Real.norm_eq_abs] using hf y)
        simpa [Real.norm_eq_abs, MeasureTheory.measureReal_def] using h
      rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      exact hbound

/-! ## The fibre `condexp` clause for one plaque algebra

For a *fixed* plaque algebra `(Z,m)` and a bounded Borel `f`, the plaque average `G` defined by
the leafwise system `ν` is a version of the conditional expectation of `f` with respect to `m`
for the fibre measures `κ x = condExpKernel μ (invariants T) x`, for `μ`-a.e. `x`.

Three ingredients:

* the `μ`-level `condexp` clause of `hL` gives `Φ = μ|_Z[f|m] = G` `μ|_Z`-a.e., hence
  `(κ x)|_Z`-a.e. because the exceptional set is contained in a *Borel* null set and the
  conditional measures of a null Borel set vanish a.e.;
* the *transfer* (Pisa 7.23): for an `m`-measurable `A` and a set `E` measurable for
  `invariants T`, the set `E ∩ Z` has an `m`-measurable version `E'` (`invariant_inter_plaque_ae`,
  the `(β′)`-step), so `∫_E 1_{A∩Z}(f - Φ) dμ = ∫_{(E' ∩ A ∩ Z)} (f - Φ) dμ = 0`; the kernel
  identity `condExp I μ h =ᵐ ∫ h d(κ x)` then gives the defining integral identity of the
  `m`-conditional expectation for the fibre `κ x`;
* Dynkin's π-λ theorem upgrades a countable π-system generating `m` to all of `m`.
-/
private theorem fibre_condExp_clause {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] [StandardBorelSpace X3]
    (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ (Uminus t) ν X')
    {Z : Set X3} (M : {m : MeasurableSpace X3 // IsPlaqueAlgebra (Uminus t) Z m})
    {f : X3 → ℝ} (hfmeas : Measurable f) (hfbdd : ∃ C, ∀ y, |f y| ≤ C) :
    ∀ᵐ x ∂μ,
      MeasureTheory.condExp M.1 ((ProbabilityTheory.condExpKernel μ
          (MeasurableSpace.invariants (fun x : X3 => aDiag t • x)) x).restrict Z) f
        =ᵐ[((ProbabilityTheory.condExpKernel μ
          (MeasurableSpace.invariants (fun x : X3 => aDiag t • x)) x).restrict Z)]
      (fun y => (∫ u in shape M.1 (Uminus t) y, f (u • y) ∂(ν y))
        / ((ν y) (shape M.1 (Uminus t) y)).toReal) := by
  classical
  obtain ⟨C₀, hC₀b⟩ := hfbdd
  set C : ℝ := max C₀ 0 with hCdef
  have hCb : ∀ y, |f y| ≤ C := fun y => le_trans (hC₀b y) (le_max_left _ _)
  have hCnn : 0 ≤ C := le_max_right _ _
  set T : X3 → X3 := fun x => aDiag t • x with hTdef
  have hTmeas : Measurable T := by
    rw [hTdef]
    exact (continuous_const_smul (aDiag t)).measurable
  set Φ : X3 → ℝ := MeasureTheory.condExp M.1 (μ.restrict Z) f with hΦdef
  set G : X3 → ℝ := fun y => (∫ u in shape M.1 (Uminus t) y, f (u • y) ∂(ν y))
      / ((ν y) (shape M.1 (Uminus t) y)).toReal with hGdef
  have hZmeas : MeasurableSet Z := M.2.1 Z M.2.2.2.1
  have hZgen : ∃ b : Set (Set X3), b.Countable ∧ M.1 = MeasurableSpace.generateFrom b :=
    M.2.2.1
  have hΦmeas : Measurable Φ := by
    rw [hΦdef]
    exact (MeasureTheory.stronglyMeasurable_condExp (μ := μ.restrict Z) (m := M.1)
      (f := f)).measurable.mono M.2.1 le_rfl
  have hμclause : ∀ᵐ x ∂(μ.restrict Z), Φ x = G x := by
    rw [hΦdef, hGdef]
    exact hL.condexp Z M.1 M.2 f hfmeas ⟨C₀, hC₀b⟩
  have hNull : μ {x | x ∈ Z ∧ Φ x ≠ G x} = 0 := by
    have h := (MeasureTheory.ae_restrict_iff' hZmeas).mp hμclause
    have h' : μ {x : X3 | ¬ (x ∈ Z → Φ x = G x)} = 0 := MeasureTheory.ae_iff.mp h
    convert h' using 2
    ext y
    simp only [Set.mem_setOf_eq, ne_eq]
    tauto
  obtain ⟨N, hNsub, hNmeas, hN0⟩ := MeasureTheory.exists_measurable_superset_of_null hNull
  have hκN : ∀ᵐ x ∂μ, ProbabilityTheory.condExpKernel μ
      (MeasurableSpace.invariants T) x N = 0 :=
    condExpKernel_eq_zero_of_null hTmeas hNmeas hN0
  have hΦG : ∀ᵐ x ∂μ, Φ =ᵐ[(ProbabilityTheory.condExpKernel μ
      (MeasurableSpace.invariants T) x).restrict Z] G := by
    filter_upwards [hκN] with x hxN
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hZmeas]
    have hN' : (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
        ((Nᶜ)ᶜ) = 0 := by simpa using hxN
    have haeN : ∀ᵐ y ∂(ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x),
        y ∈ Nᶜ :=
      Filter.eventually_iff.mpr (MeasureTheory.mem_ae_iff.mpr hN')
    filter_upwards [haeN] with y hyN
    intro hyZ
    by_contra hne
    exact hyN (hNsub ⟨hyZ, hne⟩)
  have hGbdd : ∀ y, |G y| ≤ C := by
    intro y
    rw [hGdef]
    exact abs_setIntegral_div_toReal_le (ν y) (shape M.1 (Uminus t) y) (fun u => f (u • y))
      hCnn (fun u => hCb (u • y))
  -- a countable π-system generating `M.1`
  obtain ⟨b, hbcount, hbgen⟩ := hZgen
  have hb_m : ∀ s ∈ b, MeasurableSet[M.1] s := fun s hs => by
    rw [hbgen]
    exact MeasurableSpace.measurableSet_generateFrom hs
  set Sπ : Set (Set X3) := b ∪ (fun s : Set X3 => sᶜ) '' b with hSdef
  have hScount : Sπ.Countable := hbcount.union (hbcount.image _)
  haveI : Countable ↥Sπ := hScount
  set π : Set (Set X3) :=
    Set.range (fun t : Finset ↥Sπ => ⋂₀ ((fun p : ↥Sπ => (p : Set X3)) '' (t : Set ↥Sπ)))
    with hπdef
  have hπcount : π.Countable := Set.countable_range _
  have hπsub : ∀ A ∈ π, MeasurableSet[M.1] A := by
    rintro A ⟨t, ht⟩
    rw [← ht]
    dsimp only
    rw [Set.sInter_image]
    refine MeasurableSet.biInter t.countable_toSet (fun p _ => ?_)
    rcases p.2 with hp | hp
    · exact hb_m p.1 hp
    · obtain ⟨s, hs, hsp⟩ := hp
      rw [← hsp]
      exact (hb_m s hs).compl
  have hπgen : MeasurableSpace.generateFrom π = M.1 := by
    refine le_antisymm (MeasurableSpace.generateFrom_le hπsub) ?_
    rw [hbgen]
    refine MeasurableSpace.generateFrom_mono ?_
    intro s hs
    exact ⟨{⟨s, Or.inl hs⟩}, by simp⟩
  have hπpi : IsPiSystem π := by
    rintro A ⟨t, ht⟩ B ⟨t', ht'⟩ -
    rw [← ht, ← ht'] at *
    refine ⟨t ∪ t', ?_⟩
    dsimp only
    rw [Finset.coe_union, Set.image_union, Set.sInter_union]
  -- the defining property of `Φ`, transported to integrals over `μ`
  have hΦzero : ∀ S : Set X3, MeasurableSet[M.1] S → S ⊆ Z →
      ∫ y in S, (f y - Φ y) ∂μ = 0 := by
    intro S hSm hSZ
    have hfint : MeasureTheory.Integrable f (μ.restrict Z) :=
      MeasureTheory.Integrable.of_bound hfmeas.aestronglyMeasurable C (Eventually.of_forall hCb)
    have hcond : ∫ y in S, Φ y ∂(μ.restrict Z) = ∫ y in S, f y ∂(μ.restrict Z) := by
      rw [hΦdef]
      exact MeasureTheory.setIntegral_condExp (μ := μ.restrict Z) (m := M.1)
        (m₀ := (inferInstance : MeasurableSpace X3)) M.2.1 (f := f) hfint hSm
    have hΦint : MeasureTheory.Integrable Φ (μ.restrict Z) := by
      rw [hΦdef]
      exact MeasureTheory.integrable_condExp
    have hlin : ∫ y in S, (f y - Φ y) ∂(μ.restrict Z)
        = ∫ y in S, f y ∂(μ.restrict Z) - ∫ y in S, Φ y ∂(μ.restrict Z) :=
      MeasureTheory.integral_sub hfint.integrableOn hΦint.integrableOn
    have hres : (μ.restrict Z).restrict S = μ.restrict S := Measure.restrict_restrict_of_subset hSZ
    have hsub : ∫ y in S, (f y - Φ y) ∂(μ.restrict Z) = 0 := by
      rw [hlin, hcond, sub_self]
    rw [← hres, hsub]
  -- the transfer
  have htransfer : ∀ A ∈ π, ∀ᵐ x ∂μ,
      ∫ y in A, (f y - Φ y) ∂((ProbabilityTheory.condExpKernel μ
        (MeasurableSpace.invariants T) x).restrict Z) = 0 := by
    intro A hAπ
    have hAm : MeasurableSet[M.1] A := hπsub A hAπ
    have hAB : MeasurableSet A := M.2.1 A hAm
    set hA : X3 → ℝ := (A ∩ Z).indicator (fun y => f y - Φ y) with hAdef
    have hAmeas : Measurable hA := by
      rw [hAdef]
      exact (hfmeas.sub hΦmeas).indicator (hAB.inter hZmeas)
    have hAsupp : ∀ y ∉ Z, hA y = 0 := by
      intro y hy
      rw [hAdef]
      exact Set.indicator_of_notMem (fun hc => hy hc.2) _
    have hAae : ∀ᵐ y ∂μ, |hA y| ≤ C + C := by
      have hΦbdd : ∀ᵐ y ∂(μ.restrict Z), |Φ y| ≤ C := by
        rw [hΦdef]
        exact MeasureTheory.ae_bdd_abs_condExp_of_ae_bdd_abs
          (μ := μ.restrict Z) (m := M.1) (f := f) (Eventually.of_forall hCb)
      have hb := (MeasureTheory.ae_restrict_iff' hZmeas).mp hΦbdd
      filter_upwards [hb] with y hy
      rw [hAdef]
      by_cases hyAZ : y ∈ A ∩ Z
      · rw [Set.indicator_of_mem hyAZ]
        calc |f y - Φ y| ≤ |f y| + |Φ y| := abs_sub _ _
          _ ≤ C + C := by linarith [hCb y, hy hyAZ.2]
      · rw [Set.indicator_of_notMem hyAZ, abs_zero]
        exact add_nonneg hCnn hCnn
    have hAint : MeasureTheory.Integrable hA μ :=
      MeasureTheory.Integrable.of_bound hAmeas.aestronglyMeasurable (C + C) (by
        filter_upwards [hAae] with y hy
        simpa [Real.norm_eq_abs] using hy)
    -- the integral over every invariant set vanishes
    have hstep : ∀ E : Set X3,
        @MeasurableSet X3 (MeasurableSpace.invariants T) E → ∫ y in E, hA y ∂μ = 0 := by
      intro E hE
      obtain ⟨hEmeas, -⟩ := MeasurableSpace.measurableSet_invariants.mp hE
      obtain ⟨E', hE'm, hE'diff⟩ :=
        invariant_inter_plaque_ae (μ := μ) (t := t) hmp Z ⟨M.1, M.2⟩ E hE
      have hE'B : MeasurableSet E' := M.2.1 E' hE'm
      have hsymm : μ ((E ∆ E') ∩ Z) = 0 := by
        refine le_antisymm ?_ bot_le
        refine le_trans (MeasureTheory.measure_mono ?_) (le_of_eq hE'diff)
        rintro y ⟨hyΔ, hyZ⟩
        rcases hyΔ with ⟨hyE, hyE'⟩ | ⟨hyE', hyE⟩
        · exact Or.inr ⟨⟨hyE, hyZ⟩, hyE'⟩
        · exact Or.inl ⟨hyE', fun hc => hyE hc.1⟩
      -- step 1: `hA` is supported on `Z`
      have h1 : ∫ y in E, hA y ∂μ = ∫ y in E ∩ Z, hA y ∂μ := by
        rw [← MeasureTheory.integral_indicator hEmeas (f := hA),
          ← MeasureTheory.integral_indicator (hEmeas.inter hZmeas) (f := hA)]
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun y => ?_)
        by_cases hyZ : y ∈ Z
        · by_cases hyE : y ∈ E
          · rw [Set.indicator_of_mem hyE, Set.indicator_of_mem (show y ∈ E ∩ Z from ⟨hyE, hyZ⟩)]
          · rw [Set.indicator_of_notMem hyE, Set.indicator_of_notMem (fun hc => hyE hc.1)]
        · have hL : (Set.indicator E hA) y = 0 := by
            by_cases hyE : y ∈ E
            · rw [Set.indicator_of_mem hyE, hAsupp y hyZ]
            · rw [Set.indicator_of_notMem hyE]
          have hR : (Set.indicator (E ∩ Z) hA) y = 0 :=
            Set.indicator_of_notMem (fun hc => hyZ hc.2) _
          rw [hL, hR]
      -- step 2: replace `E` by its `m`-measurable version `E'`
      have h2 : ∫ y in E ∩ Z, hA y ∂μ = ∫ y in E' ∩ Z, hA y ∂μ := by
        rw [← MeasureTheory.integral_indicator (hEmeas.inter hZmeas) (f := hA),
          ← MeasureTheory.integral_indicator (hE'B.inter hZmeas) (f := hA)]
        refine MeasureTheory.integral_congr_ae ?_
        rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
        refine le_antisymm ?_ bot_le
        refine le_trans (MeasureTheory.measure_mono ?_) (le_of_eq hsymm)
        intro y hy
        have hyne : (Set.indicator (E ∩ Z) hA) y ≠ (Set.indicator (E' ∩ Z) hA) y := hy
        have hyZ : y ∈ Z := by
          by_contra hnotZ
          exact hyne (by
            have h1 : (Set.indicator (E ∩ Z) hA) y = 0 :=
              Set.indicator_of_notMem (fun hc => hnotZ hc.2) _
            have h2 : (Set.indicator (E' ∩ Z) hA) y = 0 :=
              Set.indicator_of_notMem (fun hc => hnotZ hc.2) _
            rw [h1, h2])
        refine ⟨?_, hyZ⟩
        by_contra hnot
        apply hyne
        have hiff : y ∈ E ↔ y ∈ E' := by
          constructor
          · intro h; by_contra h2; exact hnot (Or.inl ⟨h, h2⟩)
          · intro h; by_contra h2; exact hnot (Or.inr ⟨h, h2⟩)
        by_cases h : y ∈ E
        · rw [Set.indicator_of_mem (show y ∈ E ∩ Z from ⟨h, hyZ⟩),
            Set.indicator_of_mem (show y ∈ E' ∩ Z from ⟨hiff.mp h, hyZ⟩)]
        · rw [Set.indicator_of_notMem (fun hc => h hc.1),
            Set.indicator_of_notMem (fun hc => h (hiff.mpr hc.1))]
      -- step 3: the integral over the `m`-measurable set `E' ∩ A ∩ Z`
      have h3 : ∫ y in E' ∩ Z, hA y ∂μ = ∫ y in E' ∩ (A ∩ Z), (f y - Φ y) ∂μ := by
        rw [← MeasureTheory.integral_indicator (hE'B.inter hZmeas) (f := hA),
          ← MeasureTheory.integral_indicator (hE'B.inter (hAB.inter hZmeas))
            (f := fun y => f y - Φ y)]
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun y => ?_)
        by_cases hyZ : y ∈ Z
        · by_cases hyE' : y ∈ E'
          · by_cases hyAZ : y ∈ A ∩ Z
            · rw [Set.indicator_of_mem (show y ∈ E' ∩ Z from ⟨hyE', hyZ⟩), hAdef,
                Set.indicator_of_mem hyAZ, Set.indicator_of_mem (show y ∈ E' ∩ (A ∩ Z) from ⟨hyE', hyAZ⟩)]
            · rw [Set.indicator_of_mem (show y ∈ E' ∩ Z from ⟨hyE', hyZ⟩), hAdef,
                Set.indicator_of_notMem hyAZ, Set.indicator_of_notMem (fun hc => hyAZ hc.2)]
          · rw [Set.indicator_of_notMem (fun hc => hyE' hc.1),
              Set.indicator_of_notMem (fun hc => hyE' hc.1)]
        · have hL : (Set.indicator (E' ∩ Z) hA) y = 0 :=
            Set.indicator_of_notMem (fun hc => hyZ hc.2) _
          have hR : (Set.indicator (E' ∩ (A ∩ Z)) (fun y => f y - Φ y)) y = 0 :=
            Set.indicator_of_notMem (fun hc => hyZ hc.2.2) _
          rw [hL, hR]
      rw [h1, h2, h3]
      exact hΦzero (E' ∩ (A ∩ Z)) (hE'm.inter (hAm.inter M.2.2.2.1))
        (fun y hy => hy.2.2)
    -- hence the conditional expectation over `invariants T` vanishes
    have hzero : (0 : X3 → ℝ) =ᵐ[μ]
        MeasureTheory.condExp (MeasurableSpace.invariants T) μ hA := by
      refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq (μ := μ)
        (m := MeasurableSpace.invariants T)
        (m₀ := (inferInstance : MeasurableSpace X3)) (MeasurableSpace.invariants_le T)
        (f := hA) (g := (0 : X3 → ℝ))
        hAint (fun s _ _ => MeasureTheory.integrableOn_zero) (fun s hs _ => ?_)
        (MeasureTheory.stronglyMeasurable_const.aestronglyMeasurable)
      have hz : ∫ y in s, (0 : X3 → ℝ) y ∂μ = 0 := by simp
      rw [hz, hstep s hs]
    have hkern := ProbabilityTheory.condExp_ae_eq_integral_condExpKernel (μ := μ)
      (m := MeasurableSpace.invariants T) (f := hA) (MeasurableSpace.invariants_le T) hAint
    have hkern' : ∀ᵐ x ∂μ,
        ∫ y, hA y ∂(ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) = 0 := by
      filter_upwards [hzero, hkern] with x hx1 hx2
      rw [← hx2, ← hx1]
      simp
    filter_upwards [hkern'] with x hx
    have hconv : ∫ y, hA y ∂(ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
        = ∫ y in A, (f y - Φ y) ∂((ProbabilityTheory.condExpKernel μ
            (MeasurableSpace.invariants T) x).restrict Z) := by
      rw [hAdef, MeasureTheory.integral_indicator (hAB.inter hZmeas)]
      rw [Measure.restrict_restrict hAB]
    rw [← hconv]
    exact hx
  -- countably many `A`
  haveI : Countable ↥π := hπcount
  have htransfer' : ∀ᵐ x ∂μ, ∀ A : ↥π,
      ∫ y in (A : Set X3), (f y - Φ y) ∂((ProbabilityTheory.condExpKernel μ
        (MeasurableSpace.invariants T) x).restrict Z) = 0 := by
    rw [eventually_countable_forall]
    intro A
    exact htransfer A A.2
  -- final assembly
  filter_upwards [hΦG, htransfer'] with x hΦGx htrx
  set κx : MeasureTheory.Measure X3 := (ProbabilityTheory.condExpKernel μ
    (MeasurableSpace.invariants T) x).restrict Z with hκxdef
  have hΦ_int : MeasureTheory.Integrable Φ κx := by
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (C + 1))
      hΦmeas.aestronglyMeasurable ?_
    filter_upwards [hΦGx] with y hy
    have hb := hGbdd y
    calc ‖Φ y‖ = ‖G y‖ := by rw [hy]
      _ = |G y| := Real.norm_eq_abs _
      _ ≤ C := hb
      _ ≤ C + 1 := by linarith
  have hf_int : MeasureTheory.Integrable f κx := by
    refine MeasureTheory.Integrable.of_bound hfmeas.aestronglyMeasurable C ?_
    filter_upwards with y
    simpa [Real.norm_eq_abs] using hCb y
  have htotal : ∫ y in (Set.univ : Set X3), (f y - Φ y) ∂κx = 0 := by
    have hmem : (Set.univ : Set X3) ∈ π := ⟨(∅ : Finset ↥Sπ), by simp⟩
    have h0 := htrx ⟨Set.univ, hmem⟩
    rw [MeasureTheory.setIntegral_univ]
    rwa [MeasureTheory.setIntegral_univ] at h0
  have hident : ∀ A : Set X3, MeasurableSet[M.1] A → ∫ y in A, (f y - Φ y) ∂κx = 0 := by
    have hbase : ∀ A ∈ π, ∫ y in A, (f y - Φ y) ∂κx = 0 := by
      intro A hA
      have h0 := htrx ⟨A, hA⟩
      simpa [hκxdef] using h0
    have hcompl : ∀ t : Set X3, MeasurableSet t →
        ∫ y in t, (f y - Φ y) ∂κx = 0 → ∫ y in tᶜ, (f y - Φ y) ∂κx = 0 := by
      intro t ht htc
      have h := MeasureTheory.integral_add_compl (μ := κx) (f := fun y => f y - Φ y) ht
        (hf_int.sub hΦ_int)
      have htotal' : ∫ y, (fun y => f y - Φ y) y ∂κx = 0 := by
        rw [← MeasureTheory.setIntegral_univ]
        exact htotal
      rw [htc, zero_add, htotal'] at h
      exact h
    have hunion : ∀ (g : ℕ → Set X3), Pairwise (fun i j => Disjoint (g i) (g j)) →
        (∀ i, MeasurableSet (g i)) → (∀ i, ∫ y in g i, (f y - Φ y) ∂κx = 0) →
        ∫ y in ⋃ i, g i, (f y - Φ y) ∂κx = 0 := by
      intro g hgd hgm hgi
      rw [show (∫ y in ⋃ i, g i, f y - Φ y ∂κx)
          = ∑' i, ∫ y in g i, f y - Φ y ∂κx from
        MeasureTheory.integral_iUnion (μ := κx) hgm hgd (hf_int.sub hΦ_int).integrableOn]
      simp [hgi]
    intro A hA
    exact MeasurableSpace.induction_on_inter (m := M.1) (s := π) hπgen.symm hπpi
      (by simp)
      (fun t ht => hbase t ht)
      (fun t htm ih => hcompl t (M.2.1 t htm) ih)
      (fun g hgd hgm ih => hunion g hgd (fun i => M.2.1 (g i) (hgm i)) ih)
      A hA
  have hone : Φ =ᵐ[κx] MeasureTheory.condExp M.1 κx f := by
    refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq (μ := κx) (m := M.1)
      (m₀ := (inferInstance : MeasurableSpace X3)) M.2.1 (f := f) (g := Φ) hf_int
      (fun s _ _ => hΦ_int.integrableOn) (fun s hs _ => ?_)
      (MeasureTheory.stronglyMeasurable_condExp (μ := μ.restrict Z) (m := M.1)
        (f := f)).aestronglyMeasurable
    have h := hident s hs
    have hlin : ∫ y in s, (f y - Φ y) ∂κx
        = ∫ y in s, f y ∂κx - ∫ y in s, Φ y ∂κx :=
      MeasureTheory.integral_sub hf_int.integrableOn hΦ_int.integrableOn
    rw [hlin, sub_eq_zero] at h
    exact h.symm
  have hfin : MeasureTheory.condExp M.1 κx f =ᵐ[κx] G := hone.symm.trans hΦGx
  rw [hκxdef] at hfin
  exact hfin

/-- The plaque averages of two families that agree `ρ`-a.e. agree `(ρ|_Z)`-a.e. -/
private theorem plaqueAverage_ae_eq (t : Fin 3 → ℝ) {ρ : MeasureTheory.Measure X3}
    {ν ν' : X3 → Measure SL3} (h : ν =ᵐ[ρ] ν') (Z : Set X3) (m : MeasurableSpace X3)
    (f : X3 → ℝ) :
    (fun y => (∫ u in shape m (Uminus t) y, f (u • y) ∂(ν' y))
        / ((ν' y) (shape m (Uminus t) y)).toReal)
      =ᵐ[ρ.restrict Z]
      (fun y => (∫ u in shape m (Uminus t) y, f (u • y) ∂(ν y))
        / ((ν y) (shape m (Uminus t) y)).toReal) := by
  have hnull : ρ {y | ν y ≠ ν' y} = 0 := by
    rw [Filter.EventuallyEq] at h
    exact MeasureTheory.ae_iff.mp h
  have hnullZ : (ρ.restrict Z) {y | ν y ≠ ν' y} = 0 :=
    le_antisymm (le_trans (Measure.restrict_le_self _) (le_of_eq hnull)) bot_le
  have hae : ∀ᵐ y ∂(ρ.restrict Z), ν y = ν' y := by
    filter_upwards [MeasureTheory.ae_iff.mpr hnullZ] with y hy
    exact hy
  filter_upwards [hae] with y hy
  rw [hy]

/-- The `condexp` clause for `ν` for a measure `ρ` for which `ν` agrees with a leafwise system
`ν'` a.e. -/
private theorem condexp_of_ae_eq (t : Fin 3 → ℝ) {ρ : MeasureTheory.Measure X3}
    {ν ν' : X3 → Measure SL3} {X'' : Set X3}
    (hL' : IsLeafwise ρ (Uminus t) ν' X'') (hae : ν' =ᵐ[ρ] ν)
    (f : X3 → ℝ) (hf : Measurable f) (hfb : ∃ C, ∀ y, |f y| ≤ C)
    (Z : Set X3) (m : MeasurableSpace X3) (hP : IsPlaqueAlgebra (Uminus t) Z m) :
    ∀ᵐ y ∂(ρ.restrict Z),
      MeasureTheory.condExp m (ρ.restrict Z) f y
        = (∫ u in shape m (Uminus t) y, f (u • y) ∂(ν y))
          / ((ν y) (shape m (Uminus t) y)).toReal := by
  have h1 := hL'.condexp Z m hP f hf hfb
  have h2 := (plaqueAverage_ae_eq t (ρ := ρ) hae Z m f).symm
  filter_upwards [h1, h2] with y hy1 hy2
  rw [hy1, hy2]

/-! ## The main theorem

For `μ`-a.e. point, the conditional measure of `μ` over the σ-algebra of `T`-invariant sets
carries the leafwise system `ν`.  The pointwise fields are those of `hL`; the `condexp` field is
obtained by rigidity: the countable family of flowers with big shapes (whose petals contain every
point with free `U`-orbit, `bigShape_flowers_fr`) together with the pointwise fields determines
the leafwise system (`leafwise_eq_of_flower_clauses`), while the fibre has a leafwise system by
the existence clause of `P_Leafwise` (`Work.EKLC7.P_Leafwise_proved`).  The fibres also satisfy
the `condexp` clauses of the flowers by `fibre_condExp_clause`, for `μ`-a.e. `x`.
-/
theorem fiber_leafwise {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] [StandardBorelSpace Work.EKLContract.X3]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariant ν X'') (hX'' : μ (X''ᶜ) = 0) :
    ∀ᵐ x ∂μ, Work.EKLContract.IsLeafwise
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
        (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)) x)
      (Work.EKLC6Core.Uminus t) ν X' := by
  classical
  have h2 : P_X3 := Work.EKLComp.prove_X3
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hcontr : ∀ u ∈ Uminus t,
      Tendsto (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (𝓝 1) :=
    (uminus_isHoro t).2
  have hTmeas : Measurable (fun x : X3 => aDiag t • x) :=
    (continuous_const_smul (aDiag t)).measurable
  haveI : Countable ↥Work.EKLRelCross.piSys := Work.EKLRelCross.piSys_countable
  -- flowers of every radius `n + 2`
  have hfl : ∀ n : ℕ, ∃ (Z G : ℕ → Set X3) (m : ℕ → MeasurableSpace X3),
      (∀ k, IsPlaqueAlgebra (Uminus t) (Z k) (m k)) ∧
      (∀ k, MeasurableSet (G k) ∧ G k ⊆ Z k) ∧
      ({x : X3 | ∀ u ∈ Uminus t, u • x = x → u = 1} ⊆ ⋃ k, G k) ∧
      (∀ k, ∀ x ∈ G k, ∀ u ∈ (V ((n : ℝ) + 2) ∩ (Uminus t : Set SL3)),
        u • x ∈ atom (m k) x) :=
    fun n => Work.EKLRelCross.bigShape_flowers_fr h2 μ (Uminus t) hU t hmp hcontr
      ((n : ℝ) + 2) (by positivity)
  choose Z G m hZplaq hGdata hFrsub hshape using hfl
  -- the fibre `condexp` clauses for the flowers
  have hclause : ∀ᵐ x ∂μ, ∀ p : ℕ × ℕ × ↥Work.EKLRelCross.piSys,
      MeasureTheory.condExp (m p.1 p.2.1)
          ((ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
            (fun x : X3 => aDiag t • x)) x).restrict (Z p.1 p.2.1))
          ((p.2.2 : Set X3).indicator (fun _ => (1 : ℝ)))
        =ᵐ[((ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
            (fun x : X3 => aDiag t • x)) x).restrict (Z p.1 p.2.1))]
      (fun y => (∫ u in shape (m p.1 p.2.1) (Uminus t) y,
            ((p.2.2 : Set X3).indicator (fun _ => (1 : ℝ))) (u • y) ∂(ν y))
        / ((ν y) (shape (m p.1 p.2.1) (Uminus t) y)).toReal) := by
    rw [eventually_countable_forall]
    rintro ⟨n, k, C⟩
    exact fibre_condExp_clause (μ := μ) t hmp hL (Z := Z n k) (M := ⟨m n k, hZplaq n k⟩)
      (f := (C : Set X3).indicator (fun _ => (1 : ℝ)))
      (measurable_const.indicator (Work.EKLRelCross.measurableSet_of_mem_piSys C.2))
      ⟨1, fun y => by
        by_cases hy : y ∈ (C : Set X3) <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]⟩
  -- conullity of `X'` and `T`-invariance for the fibres
  have hXconull : ∀ᵐ x ∂μ, ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
      (fun x : X3 => aDiag t • x)) x X'ᶜ = 0 :=
    condExpKernel_eq_zero_of_null hTmeas hL.meas_dom.compl hL.conull
  have hTinv : ∀ᵐ x ∂μ, MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x)
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
        (fun x : X3 => aDiag t • x)) x)
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
        (fun x : X3 => aDiag t • x)) x) :=
    fiber_inv_finite μ (fun x : X3 => aDiag t • x) hTmeas hmp
  filter_upwards [hclause, hXconull, hTinv] with x hclx hX'x hTinvx
  haveI : IsProbabilityMeasure (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
      (fun x : X3 => aDiag t • x)) x) := IsMarkovKernel.isProbabilityMeasure x
  -- the free-orbit set is null for the fibre
  have hFr : ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
      (fun x : X3 => aDiag t • x)) x
      {x : X3 | ∀ u ∈ Uminus t, u • x = x → u = 1}ᶜ = 0 := by
    have hfree := Work.EKLRelCross.free_orbits_of_contracting h2 hU t hTinvx hcontr
    rw [MeasureTheory.ae_iff] at hfree
    exact hfree
  have hcover : ∀ n : ℕ, ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
      (fun x : X3 => aDiag t • x)) x (⋃ k, G n k)ᶜ = 0 := by
    intro n
    refine MeasureTheory.measure_mono_null (fun y hy => ?_) hFr
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hy ⊢
    exact fun hcon => hy (hFrsub n hcon)
  -- a leafwise system for the fibre
  obtain ⟨ν'', X'', hL''⟩ := ((Work.EKLC7.P_Leafwise_proved h2)
    (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
      (fun x : X3 => aDiag t • x)) x) (Uminus t) hU t hTinvx hcontr).1
  -- rigidity
  have hrig : ∀ᵐ y ∂(ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
      (fun x : X3 => aDiag t • x)) x), ν'' y = ν y :=
    leafwise_eq_of_flower_clauses (ρ := ProbabilityTheory.condExpKernel μ
        (MeasurableSpace.invariants (fun x : X3 => aDiag t • x)) x)
      h2 (Uminus t) hU t hTinvx hcontr hX'x (fun y hy => hL.radon y hy)
      (fun y hy => hL.carried y hy) (fun y hy => hL.normalised y hy)
      Z G m hZplaq (fun n k => (hGdata n k).1) (fun n k => (hGdata n k).2) hcover hshape
      (fun n k C _ => hclx (n, k, ⟨C, by assumption⟩)) hL''
  -- assemble the `IsLeafwise` structure
  refine ⟨hL.meas_dom, hX'x, hL.radon, hL.carried, hL.normalised, hL.measurable, hL.pos,
    hL.equivariant, ?_⟩
  intro Z₀ m₀ hPlaq f hfm hfb
  exact condexp_of_ae_eq t hL'' hrig f hfm hfb Z₀ m₀ hPlaq

end Work.EKLC6Core
