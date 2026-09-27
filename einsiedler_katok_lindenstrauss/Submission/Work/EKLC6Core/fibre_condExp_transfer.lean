import Mathlib
import Submission.Work.EKLC6Core.FibreAlongDefs
import Submission.Work.EKLC6Core.invariant_inter_plaque_ae
import Submission.Work.EKLComp.LeafAux
import Submission.Work.EKLC6Core.abs_setIntegral_div_toReal_le
import Submission.Work.EKLC6Core.kernel_integral_eq_zero_of_invariant_setIntegral
import Submission.Work.EKLC6Core.setIntegral_eq_zero_of_piSystem

/-!
# `Work.EKLC6Core.fibre_condExp_transfer`

Transfer of the `condexp` field of a leafwise system to the fibres of the invariant σ-algebra
(Pisa 7.23): for `μ`-a.e. base point `x`, the conditional expectation of a bounded Borel `f` with
respect to a plaque algebra `(Z, m)`, computed for the fibre measure `(fibre μ t x)|_Z`, is the
`ν`-average over the plaque of an `m`-atom.

The proof has three steps.

* The defining identity of `Φ := condExp m (μ|_Z) f` turns every `m`-measurable set integral against
  `f - Φ` into `0`; the Hopf saturation `invariant_inter_plaque_ae` (Pisa 7.20) replaces the
  `T`-invariant sets `E` occurring in the defining property of a conditional expectation by an
  `m`-measurable set up to a `μ`-null set, so that `1_{A∩Z} · (f - Φ)` has vanishing integral over
  every `T`-invariant set, for every member `A` of a countable π-system generating `m`.
* `kernel_integral_eq_zero_of_invariant_setIntegral` transfers this to the conditional kernel
  `fibre μ t x = condExpKernel μ (invariants T) x`, and `setIntegral_eq_zero_of_piSystem` (Dynkin)
  upgrades it from the π-system to all of `m`; `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`
  then identifies `Φ` with `condExp m ((fibre μ t x)|_Z) f` `(fibre μ t x)|_Z`-a.e.
* Finally the `condexp` field of `hL` gives `Φ =ᵐ[μ|_Z] G`, and `μ|_Z`-null sets are
  `(fibre μ t x)|_Z`-null for `μ`-a.e. `x`, so `G` is the required version of the conditional
  expectation.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal symmDiff

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Null sets for the conditional kernel -/

/-- A `μ`-null measurable set is a null set for the conditional kernel
`condExpKernel μ (invariants T)` for `μ`-a.e. point. -/
private theorem condExpKernel_eq_zero_of_null {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] [StandardBorelSpace X3]
    {T : X3 → X3} (hT : Measurable T)
    {B : Set X3} (hBmeas : MeasurableSet B) (hB0 : μ B = 0) :
    ∀ᵐ x ∂μ, ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x B = 0 := by
  have hm : MeasurableSpace.invariants T ≤ (inferInstance : MeasurableSpace X3) :=
    MeasurableSpace.invariants_le T
  exact Work.EKLComp.kernel_measure_eq_zero μ ⟨MeasurableSpace.invariants T⟩ hm hBmeas hB0

/-- **The fibre `condexp` clause for one plaque algebra** (the body of the transfer, with the
plaque algebra packed into a subtype so that the conclusion can be stated in terms of a single
`M : {m // IsPlaqueAlgebra (Uminus t) Z m}`). -/
private theorem fibre_condExp_aux {μ : MeasureTheory.Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ] [StandardBorelSpace X3]
    (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ (Uminus t) ν X')
    {Z : Set X3} (M : {m : MeasurableSpace X3 // IsPlaqueAlgebra (Uminus t) Z m})
    {f : X3 → ℝ} (hfmeas : Measurable[instMeasurableSpaceX3] f)
    (hfbdd : ∃ C, ∀ y, |f y| ≤ C) :
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
    -- hence the integral of `hA` against the conditional kernel vanishes a.e.
    -- (the conditional expectation over `invariants T` is `0`, and it is computed by the kernel)
    have hkern' := kernel_integral_eq_zero_of_invariant_setIntegral (μ := μ) hAint hstep
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
  -- Dynkin's π-λ upgrade: the identity `∫_A (f - Φ) ∂κx = 0` holds on the π-system `π`, hence on
  -- all of `M.1`.
  have hident : ∀ A : Set X3, MeasurableSet[M.1] A → ∫ y in A, (f y - Φ y) ∂κx = 0 := by
    have hbase : ∀ A ∈ π, ∫ y in A, (f y - Φ y) ∂κx = 0 := by
      intro A hA
      have h0 := htrx ⟨A, hA⟩
      simpa [hκxdef] using h0
    exact setIntegral_eq_zero_of_piSystem (κ := κx) (π := π) (m := M.1) (u := fun y => f y - Φ y)
      M.2.1 hπgen.symm hπsub hπpi ⟨(∅ : Finset ↥Sπ), by simp⟩
      (hf_int.sub hΦ_int) hbase
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



/-! ## The transfer -/

/-- **Transfer of the `condexp` field of a leafwise system to the fibres of the invariant σ-algebra** (Pisa 7.23).  Here `Work.EKLC6Core.diagMap t = (aDiag t ·)`, `Work.EKLC6Core.fibre μ t x = condExpKernel μ (invariants (diagMap t)) x`, `Work.EKLC6Core.BorelMeas f` is Borel measurability of `f` (with the σ-algebra pinned, because a bare `Measurable f` in a context containing a local `m : MeasurableSpace X₃` means measurability for `m`), and `Work.EKLC6Core.nuAvg (Uminus t) ν m f` is the function `y ↦ (∫ u in shape m (Uminus t) y, f (u • y) ∂(ν y)) / ((ν y) (shape m (Uminus t) y)).toReal` occurring on the right-hand side of the `condexp` field of `IsLeafwise`.

Proof sketch.  Write `ρ_x := (κ x)|_Z` with `κ x := fibre μ t x`, `F := condExp m ((μ|_Z)) f`, `G := nuAvg (Uminus t) ν m f`, so that `hL.condexp Z m hPA f hf hfb` gives `F =ᵐ[μ|_Z] G`.
(1) *Key identity.*  For `s ∈ m` (WLOG `s ⊆ Z`), `φ := 1_{s∩Z}·(F - f)` is `μ`-integrable, so `condExp_ae_eq_integral_condExpKernel` gives `(fun x ↦ ∫ φ ∂(κ x)) =ᵐ[μ] 𝔼_μ[φ | invariants (diagMap t)]`; and this conditional expectation vanishes because for every invariant measurable `B` the set `B ∩ s ∩ Z` may be replaced by an `m`-measurable set up to a `μ`-null set (`Work.EKLC6Core.invariant_inter_plaque_ae`, the Hopf saturation of Pisa 7.20), after which the defining property of `F = condExp m (μ|_Z) f` applies.  Hence for `μ`-a.e. `x` (one null set per member of a countable π-system generating `m`): `∫_s F ∂ρ_x = ∫_s f ∂ρ_x`.
(2) Consequently, for such an `x`, the finite signed measures `A ↦ ∫_A F ∂ρ_x` and `A ↦ ∫_A f ∂ρ_x` on `m` agree on a countable π-system generating `m`, hence on `m` (`MeasureTheory.ext_of_generate_finite`, applied to the positive and negative parts).  Then `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq` with candidate `F` (a.e. `m`-strongly measurable by construction; `IntegrableOn F s ρ_x` for `ρ_x s < ∞`, since `|F| ≤ C` holds `μ|_Z`-a.e. by `MeasureTheory.ae_bdd_abs_condExp_of_ae_bdd_abs` and `μ|_Z`-null sets are `ρ_x`-null for `μ`-a.e. `x`) gives `condExp m ρ_x f =ᵐ[ρ_x] F`.
(3) Finally `F =ᵐ[ρ_x] G` for `μ`-a.e. `x` because `F =ᵐ[μ|_Z] G` and `μ|_Z`-null sets are `ρ_x`-null for `μ`-a.e. `x`; chain with (2).
The step "a measurable `μ`-null set `B` satisfies `κ x B = 0` for `μ`-a.e. `x`" is `Work.EKLComp.kernel_measure_eq_zero`, and the same transfer of null sets applies to the *non-measurable* set `{F ≠ G}` (it is contained in a measurable `μ|_Z`-null set).  Note the two `=ᵐ` statements are about the *restricted* measure `(fibre μ t x).restrict Z`, and the left-hand side of the target is Mathlib's canonical version `condExp m ((fibre μ t x).restrict Z) f`. -/
theorem fibre_condExp_transfer {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (Work.EKLC6Core.diagMap t) μ μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    {Z : Set Work.EKLContract.X3} {m : MeasurableSpace Work.EKLContract.X3}
    (hPA : Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z m)
    {f : Work.EKLContract.X3 → ℝ}
    (hf : Work.EKLC6Core.BorelMeas f)
    (hfb : ∃ C, ∀ y, |f y| ≤ C) :
    ∀ᵐ x ∂μ,
      MeasureTheory.condExp m ((Work.EKLC6Core.fibre μ t x).restrict Z) f
        =ᵐ[(Work.EKLC6Core.fibre μ t x).restrict Z]
        Work.EKLC6Core.nuAvg (Work.EKLC6Core.Uminus t) ν m f := by
  have hfmeas : Measurable[instMeasurableSpaceX3] f := hf
  have h := fibre_condExp_aux (μ := μ) t hmp hL (Z := Z) (M := ⟨m, hPA⟩) (f := f) hfmeas hfb
  -- `nuAvg (Uminus t) ν m f` is *by definition* the average displayed in the fibre `condexp`
  -- clause, and `fibre μ t x` is *by definition* `condExpKernel μ (invariants (diagMap t)) x`.
  rw [show nuAvg (Uminus t) ν m f
      = (fun y => (∫ u in shape m (Uminus t) y, f (u • y) ∂(ν y))
          / ((ν y) (shape m (Uminus t) y)).toReal) from rfl]
  filter_upwards [h] with x hx
  exact hx

end Work.EKLC6Core

end
