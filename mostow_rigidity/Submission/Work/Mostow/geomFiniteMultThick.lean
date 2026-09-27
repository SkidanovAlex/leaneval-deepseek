import Mathlib
import Submission.Mostow.HLDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.HaarBase
import Submission.Work.Mostow.VolDefs
import Submission.Work.Mostow.BoostTransitive
import Submission.Work.Mostow.thickPart_cocompact

/-!
# `geomFiniteMultThick`: the multiplicity-`N` thick part of a lattice

`Work.Mostow.geomFiniteMultThick`: for a lattice `Γ ≤ PO(n,1)`, and any `δ > 0`, `N : ℕ`, the set
of points `u` at which at most `N` elements of `Γ` satisfy `hdist u (γ • u) < δ` is contained in
the `Γ`-translates of a compact set (`MultThickProp Γ`).

This is the multiplicity-`N` form of the classical packing argument ("the thick part of a lattice
is cocompact"), and it is the same proof: pick a maximal `Γ`-separated subset `S` of the
multiplicity-`N` set with separation `δ`; the open balls of radius `δ/2` about the points of `S`
are pairwise disjoint, and -- using that `S` is separated and that every point of `S` has
multiplicity at most `N` -- the translates of a finite union of such balls cover any point of the
quotient at most `N` times. The counting bound `countMultiplicityBound` (`vol ≤ N * vol D`) then
forces `S` to be finite, and maximality of `S` shows that the union of the closed `δ`-balls about
`S` is the required compact set.

The two ingredients from the surrounding development are
* `Work.Mostow.volHPosOpen` (`Submission.Work.Mostow.VolDefs`) — the hyperbolic volume is positive
  on nonempty open sets,
* `Work.Mostow.volH_hBall_homogeneous` and `Work.Mostow.hdist_continuous_left`
  (`Submission.Work.Mostow.thickPart_cocompact`) — homogeneity of the volume of hyperbolic balls
  (from transitivity of the `PO(n,1)`-action) and continuity of `x ↦ hdist u x`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

variable {n : ℕ}

set_option maxHeartbeats 1000000

/-! ## The counting bound -/

/-- **Counting bound.** Let a countable group `G` act measurably on a measurable space `α`,
preserving a measure `μ`, let `s` be a fundamental domain and `t` a measurable set such that for
almost every `x ∈ s` the set `{g : G | g • x ∈ t}` is contained in a finite set of cardinality at
most `N`. Then `μ t ≤ N * μ s`.

This is the multiplicity-`N` generalisation of `MeasureTheory.IsFundamentalDomain.measure_le_of_pairwise_disjoint`
(the case `N = 1`). The proof is the standard "fiber counting" computation: `μ t` is the sum over
`g : G` of `(μ.restrict s) (g⁻¹ • t)`, which is the integral over `s` of the multiplicity function
`x ↦ #{g : g • x ∈ t}`, bounded by `N` almost everywhere. -/
theorem countMultiplicityBound {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace α] (μ : Measure α) [Countable G] [MeasurableConstSMul G α]
    [SMulInvariantMeasure G α μ] {s t : Set α} (hs : IsFundamentalDomain G s μ)
    (ht : MeasurableSet t) (N : ℕ)
    (hcount : ∀ᵐ x ∂(μ.restrict s),
      ∃ F : Finset G, F.card ≤ N ∧ ∀ g : G, g • x ∈ t → g ∈ F) :
    μ t ≤ N * μ s := by
  -- `g⁻¹ • t` is the preimage of `t` under `g • ·`, hence measurable.
  have hmeas : ∀ g : G, MeasurableSet (g⁻¹ • t) := fun g => by
    rw [← Set.preimage_smul]
    exact (measurable_const_smul g) ht
  -- (1) Decompose `t` along the translates of the fundamental domain.
  have hstep1 : μ t = ∑' g : G, (μ.restrict s) (g⁻¹ • t) := by
    rw [hs.measure_eq_tsum' t]
    refine tsum_congr fun g => ?_
    rw [Measure.restrict_apply₀' hs.nullMeasurableSet]
    exact (measure_inv_smul_inter μ g t s).symm
  -- (2) Sum of the measures = integral of the multiplicity function.
  have hstep2 : ∑' g : G, (μ.restrict s) (g⁻¹ • t)
      = ∫⁻ x, ∑' g : G, (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x ∂(μ.restrict s) := by
    rw [lintegral_tsum (μ := μ.restrict s)
      (f := fun g x => (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x)
      (fun g => (Measurable.indicator measurable_const (hmeas g)).aemeasurable)]
    refine tsum_congr fun g => ?_
    rw [lintegral_indicator_one (hmeas g)]
  -- (3) The multiplicity function is bounded by `N` almost everywhere.
  have hbound : ∀ᵐ x ∂(μ.restrict s),
      ∑' g : G, (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x ≤ N := by
    filter_upwards [hcount] with x hx
    obtain ⟨F, hFcard, hF⟩ := hx
    have hsupp : ∀ g ∉ F, (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x = 0 := by
      intro g hg
      rw [Set.indicator_of_notMem]
      intro hmem
      rw [Set.mem_inv_smul_set_iff] at hmem
      exact hg (hF g hmem)
    rw [tsum_eq_sum hsupp]
    calc ∑ g ∈ F, (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x
        ≤ ∑ _g ∈ F, (1 : ℝ≥0∞) := Finset.sum_le_sum fun g _ => Set.indicator_le_self _ _ x
      _ = F.card := by simp
      _ ≤ N := by exact_mod_cast hFcard
  calc μ t = ∑' g : G, (μ.restrict s) (g⁻¹ • t) := hstep1
    _ = ∫⁻ x, ∑' g : G, (g⁻¹ • t).indicator (1 : α → ℝ≥0∞) x ∂(μ.restrict s) := hstep2
    _ ≤ ∫⁻ _x, (N : ℝ≥0∞) ∂(μ.restrict s) := lintegral_mono_ae hbound
    _ = N * (μ.restrict s) Set.univ := lintegral_const N
    _ = N * μ s := by rw [Measure.restrict_apply_univ]

/-- The counting bound specialised to a discrete subgroup `Γ ≤ PO(n,1)` acting on `ℍⁿ`. -/
theorem volH_le_card_mul_of_ae_count' (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ))
    {D F : Set (E n)} (hD : IsFundamentalDomain Γ D (volH n)) (hF : MeasurableSet F) (N : ℕ)
    (hcount : ∀ᵐ z ∂((volH n).restrict D),
      ∃ s : Finset Γ, s.card ≤ N ∧ ∀ γ : Γ, (γ : PO n 1) • z ∈ F → γ ∈ s) :
    volH n F ≤ N * volH n D := by
  have hAb : POBasic n := POBasic.ofProp hA
  have hId : HypIsoData n := HypIsoData.ofProp hI
  -- the `Γ`-action on `ℍⁿ`, inherited from the `PO(n,1)`-action
  letI : MulAction (PO n 1) (E n) :=
    { one_smul := fun u => hAb.one_smul u
      mul_smul := fun g h u => hAb.mul_smul g h u }
  letI : MulAction Γ (E n) := inferInstance
  haveI : MeasurableConstSMul Γ (E n) :=
    ⟨fun c => (hId.contDiff_smul (c : PO n 1)).continuous.measurable⟩
  haveI : SMulInvariantMeasure Γ (E n) (volH n) :=
    ⟨fun c s hs => (hId.measurePreserving_smul (c : PO n 1)).measure_preimage hs.nullMeasurableSet⟩
  haveI : Countable Γ := countable_of_isDiscrete (PO n 1) hdisc
  exact countMultiplicityBound (volH n) (s := D) (t := F) hD hF N hcount

/-! ## The main theorem -/

/-- **The multiplicity-`N` thick part of a lattice is cocompact.**  For a lattice `Γ ≤ PO(n,1)`,
any `δ > 0` and any `N : ℕ`, a point at which at most `N` elements of `Γ` are `δ`-short lies in
the `Γ`-translates of a fixed compact set. -/
theorem geomFiniteMultThick (n : ℕ) (hn : 1 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ) : MultThickProp Γ := by
  classical
  intro δ hδ N
  obtain ⟨hdisc, D, hD, hDfin⟩ := hΓ
  have hAb : POBasic n := POBasic.ofProp hA
  have hId : HypIsoData n := HypIsoData.ofProp hI
  haveI : Countable Γ := countable_of_isDiscrete (PO n 1) hdisc
  -- the `Γ`-action on `ℍⁿ`, inherited from the `PO(n,1)`-action
  letI : MulAction (PO n 1) (E n) :=
    { one_smul := fun u => hAb.one_smul u
      mul_smul := fun g h u => hAb.mul_smul g h u }
  letI : MulAction Γ (E n) := inferInstance
  haveI : MeasurableConstSMul Γ (E n) :=
    ⟨fun c => (hId.contDiff_smul (c : PO n 1)).continuous.measurable⟩
  haveI : SMulInvariantMeasure Γ (E n) (volH n) :=
    ⟨fun c s hs => (hId.measurePreserving_smul (c : PO n 1)).measure_preimage hs.nullMeasurableSet⟩
  set r : ℝ := δ / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have h2r : 2 * r = δ := by rw [hrdef]; ring
  -- the set of points of multiplicity at most `N`
  set Mset : Set (E n) := {u | ({γ : Γ | hdist u ((γ : PO n 1) • u) < δ}.Finite ∧
      {γ : Γ | hdist u ((γ : PO n 1) • u) < δ}.ncard ≤ N)} with hMdef
  have mMset : ∀ u : E n, u ∈ Mset ↔ ({γ : Γ | hdist u ((γ : PO n 1) • u) < δ}.Finite ∧
      {γ : Γ | hdist u ((γ : PO n 1) • u) < δ}.ncard ≤ N) := by
    intro u
    rw [hMdef]
    exact Iff.rfl
  -- `Γ`-separated subsets of `Mset`, with separation `δ`
  set Good : Set (Set (E n)) :=
    {S | S ⊆ Mset ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      ∀ γ : Γ, δ ≤ hdist u ((γ : PO n 1) • v)} with hGooddef
  have hGood_empty : (∅ : Set (E n)) ∈ Good := by
    rw [hGooddef]
    refine ⟨Set.empty_subset _, ?_⟩
    intro u hu
    exact absurd hu (Set.notMem_empty u)
  obtain ⟨S, -, hSmax⟩ := zorn_subset_nonempty Good
    (by
      intro c hc hchain _
      rw [hGooddef] at hc ⊢
      refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
      · intro u hu
        obtain ⟨s, hsc, hus⟩ := Set.mem_sUnion.mp hu
        exact (hc hsc).1 hus
      · intro u hu v hv huv γ
        obtain ⟨s, hsc, hus⟩ := Set.mem_sUnion.mp hu
        obtain ⟨t, htc, hvt⟩ := Set.mem_sUnion.mp hv
        rcases eq_or_ne s t with rfl | hne
        · exact (hc hsc).2 u hus v hvt huv γ
        · rcases hchain hsc htc hne with hst | hts
          · exact (hc htc).2 u (hst hus) v hvt huv γ
          · exact (hc hsc).2 u hus v (hts hvt) huv γ)
    ∅ hGood_empty
  have hSmem : S ∈ Good := (maximal_iff.mp hSmax).1
  rw [hGooddef] at hSmem
  have hSsub : S ⊆ Mset := hSmem.1
  have hSsep : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ∀ γ : Γ, δ ≤ hdist u ((γ : PO n 1) • v) := hSmem.2
  -- the counting bound for a finite piece of `S`
  have hpack : ∀ T : Finset (E n), (↑T : Set (E n)) ⊆ S →
      (T.card : ℝ≥0∞) * volH n (hBall 0 r) ≤ (N : ℝ≥0∞) * volH n D := by
    intro T hTS
    set A : Set (E n) := ⋃ u ∈ (T : Set (E n)), hBall u r with hAdef
    have hAmeas : MeasurableSet A := by
      rw [hAdef]
      exact T.finite_toSet.measurableSet_biUnion
        (fun u _ => (isOpen_lt (hdist_continuous_left u) continuous_const).measurableSet)
    -- the translates of `A` have multiplicity at most `N`
    have hcount : ∀ᵐ z ∂((volH n).restrict D),
        ∃ F : Finset Γ, F.card ≤ N ∧ ∀ γ : Γ, (γ : PO n 1) • z ∈ A → γ ∈ F := by
      refine Filter.Eventually.of_forall fun z => ?_
      by_cases hz : ∃ u ∈ (T : Set (E n)), ∃ γ : Γ,
        hdist (((γ⁻¹ : Γ) : PO n 1) • u) z < r
      · obtain ⟨u₀, hu₀T, γ₀, hγ₀⟩ := hz
        obtain ⟨hfin₀, hcard₀⟩ := (mMset u₀).mp (hSsub (hTS hu₀T))
        -- any `γ` with `x ∈ γ • A` has `γ₀ * γ⁻¹` short at `u₀`
        have key : ∀ (η : Γ) (u : E n), hdist (((η⁻¹ : Γ) : PO n 1) • u) z < r →
            hdist u₀ (((γ₀ * η⁻¹ : Γ) : PO n 1) • u) < δ := by
          intro η u hu
          have h1 : hdist u₀ (((γ₀ * η⁻¹ : Γ) : PO n 1) • u)
              = hdist (((γ₀⁻¹ : Γ) : PO n 1) • u₀) (((η⁻¹ : Γ) : PO n 1) • u) := by
            have h := hId.isom_smul ((γ₀ : Γ) : PO n 1)
              (((γ₀⁻¹ : Γ) : PO n 1) • u₀) (((η⁻¹ : Γ) : PO n 1) • u)
            have e1 : ((γ₀ : Γ) : PO n 1) • (((γ₀⁻¹ : Γ) : PO n 1) • u₀) = u₀ := by
              rw [← hAb.mul_smul]
              have hc : ((γ₀ : Γ) : PO n 1) * ((γ₀⁻¹ : Γ) : PO n 1) = 1 := by
                rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
              rw [hc, hAb.one_smul]
            have e2 : ((γ₀ : Γ) : PO n 1) • (((η⁻¹ : Γ) : PO n 1) • u)
                = (((γ₀ * η⁻¹ : Γ) : PO n 1)) • u := by
              rw [← hAb.mul_smul, ← Subgroup.coe_mul]
            rw [e1, e2] at h
            exact h
          rw [h1]
          calc hdist (((γ₀⁻¹ : Γ) : PO n 1) • u₀) (((η⁻¹ : Γ) : PO n 1) • u)
              ≤ hdist (((γ₀⁻¹ : Γ) : PO n 1) • u₀) z
                + hdist z (((η⁻¹ : Γ) : PO n 1) • u) := hId.triangle _ _ _
            _ < r + r := add_lt_add hγ₀ (by rw [hId.symm]; exact hu)
            _ = δ := by rw [hrdef]; ring
        have hFcard : ((hfin₀.toFinset).image (fun s : Γ => s⁻¹ * γ₀)).card ≤ N := by
          calc ((hfin₀.toFinset).image (fun s : Γ => s⁻¹ * γ₀)).card
              ≤ hfin₀.toFinset.card := Finset.card_image_le
            _ = ({γ : Γ | hdist u₀ ((γ : PO n 1) • u₀) < δ}).ncard :=
                  (Set.ncard_eq_toFinset_card _ hfin₀).symm
            _ ≤ N := hcard₀
        refine ⟨(hfin₀.toFinset).image (fun s : Γ => s⁻¹ * γ₀), hFcard, ?_⟩
        intro γ hγA
        -- `γ • z ∈ A` exhibits `γ ∈ C = {γ | ∃ u ∈ T, hdist (γ⁻¹ • u) z < r}`
        have hγC : ∃ u ∈ (T : Set (E n)), hdist (((γ⁻¹ : Γ) : PO n 1) • u) z < r := by
          simp only [hAdef, Set.mem_iUnion, Set.mem_setOf_eq, hBall, exists_prop] at hγA
          obtain ⟨u, hu, hu'⟩ := hγA
          refine ⟨u, hu, ?_⟩
          have h := hId.isom_smul (((γ⁻¹ : Γ) : PO n 1)) u ((γ : PO n 1) • z)
          have e : ((γ⁻¹ : Γ) : PO n 1) • (((γ : Γ) : PO n 1) • z) = z := by
            rw [← hAb.mul_smul]
            have hc : ((γ⁻¹ : Γ) : PO n 1) * ((γ : Γ) : PO n 1) = 1 := by
              rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
            rw [hc, hAb.one_smul]
          rw [e] at h
          rw [h]
          exact hu'
        obtain ⟨u, huT, hu⟩ := hγC
        have hueq : u = u₀ := by
          by_contra hne
          have hsep := hSsep u₀ (hTS hu₀T) u (hTS huT) (Ne.symm hne) (γ₀ * γ⁻¹)
          have hlt := key γ u hu
          linarith
        rw [hueq] at hu
        refine Finset.mem_image.mpr ⟨γ₀ * γ⁻¹, ?_, ?_⟩
        · rw [Set.Finite.mem_toFinset]
          exact key γ u₀ hu
        · show (γ₀ * γ⁻¹)⁻¹ * γ₀ = γ
          group
      · refine ⟨∅, by simp, ?_⟩
        intro γ hγA
        exfalso
        simp only [hAdef, Set.mem_iUnion, Set.mem_setOf_eq, hBall, exists_prop] at hγA
        obtain ⟨u, hu, hu'⟩ := hγA
        refine hz ⟨u, hu, γ, ?_⟩
        have h := hId.isom_smul (((γ⁻¹ : Γ) : PO n 1)) u ((γ : PO n 1) • z)
        have e : ((γ⁻¹ : Γ) : PO n 1) • (((γ : Γ) : PO n 1) • z) = z := by
          rw [← hAb.mul_smul]
          have hc : ((γ⁻¹ : Γ) : PO n 1) * ((γ : Γ) : PO n 1) = 1 := by
            rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
          rw [hc, hAb.one_smul]
        rw [e] at h
        rw [h]
        exact hu'
    have hle := volH_le_card_mul_of_ae_count' n hA hI Γ hdisc hD hAmeas N hcount
    have hvolA : volH n A = (T.card : ℝ≥0∞) * volH n (hBall 0 r) := by
      have hsum : volH n A = ∑ u ∈ T, volH n (hBall u r) := by
        rw [hAdef]
        refine measure_biUnion_finset (fun u hu v hv huv => ?_)
          (fun u _ => (isOpen_lt (hdist_continuous_left u) continuous_const).measurableSet)
        refine hBall_disjoint hId ?_
        rw [h2r]
        have h1 : δ ≤ hdist u (((1 : Γ) : PO n 1) • v) := hSsep u (hTS hu) v (hTS hv) huv 1
        rwa [show (((1 : Γ) : PO n 1)) = (1 : PO n 1) from rfl, hAb.one_smul] at h1
      rw [hsum, Finset.sum_congr rfl (fun u _ => volH_hBall_homogeneous hA hI u r),
        Finset.sum_const, nsmul_eq_mul]
    rw [← hvolA]
    exact hle
  -- `S` is finite by the counting bound
  have hSfin : S.Finite := by
    by_contra hinf
    rw [Set.not_finite] at hinf
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ,
        (N : ℝ≥0∞) * volH n D < (N₀ : ℝ≥0∞) * volH n (hBall 0 r) := by
      by_cases hvtop : volH n (hBall 0 r) = ⊤
      · refine ⟨1, ?_⟩
        rw [hvtop]
        simpa using lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) hDfin)
      · have hvpos : volH n (hBall 0 r) ≠ 0 :=
          (volHPosOpen n (isOpen_lt (hdist_continuous_left 0) continuous_const)
            ⟨0, by
              simp only [hBall, Set.mem_ofPred_eq]
              rw [hdist_self]
              exact hr⟩).ne'
        obtain ⟨N₀, hN₀⟩ := ENNReal.exists_nat_gt
          (r := (N : ℝ≥0∞) * volH n D * (volH n (hBall 0 r))⁻¹)
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hDfin)
            (ENNReal.inv_ne_top.mpr hvpos))
        refine ⟨N₀, ?_⟩
        have hmul := ENNReal.mul_lt_mul_left hvpos hvtop hN₀
        rwa [mul_assoc, ENNReal.inv_mul_cancel hvpos hvtop, mul_one] at hmul
    obtain ⟨T, hTS, hTcard⟩ := hinf.exists_subset_card_eq N₀
    have hle := hpack T hTS
    rw [hTcard] at hle
    exact absurd hle (not_le.mpr hN₀)
  -- the compact set: the closed `δ`-balls about the finite separated set
  refine ⟨⋃ v ∈ (S : Set (E n)), hClosedBall v δ, ?_, ?_⟩
  · exact hSfin.isCompact_biUnion fun v _ => by simpa [hClosedBall] using hId.ball_compact v δ
  · intro u hu
    by_cases huS : u ∈ S
    · refine ⟨1, ?_⟩
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, hClosedBall]
      refine ⟨u, huS, ?_⟩
      show hdist u (((1 : Γ) : PO n 1) • u) ≤ δ
      have h0 : hdist u (((1 : Γ) : PO n 1) • u) = 0 := by
        have hc : (((1 : Γ) : PO n 1)) = (1 : PO n 1) := rfl
        rw [hc, hAb.one_smul]
        exact (hId.eq_zero u u).mpr rfl
      rw [h0]
      exact hδ.le
    · -- maximality of `S` produces a pair which is too close
      have hnotgood : S ∪ {u} ∉ Good := by
        intro hg
        have heq : S = S ∪ {u} := (maximal_iff.mp hSmax).2 hg Set.subset_union_left
        have : u ∈ S ∪ {u} := Set.mem_union_right _ rfl
        rw [← heq] at this
        exact huS this
      have hmemSub : (S ∪ {u} : Set (E n)) ⊆ Mset := by
        intro w hw
        rcases hw with hw | hw
        · exact hSsub hw
        · rw [Set.mem_singleton_iff.mp hw]; exact (mMset u).mpr hu
      have hnotsep : ¬ (∀ w ∈ (S ∪ {u} : Set (E n)), ∀ w' ∈ (S ∪ {u} : Set (E n)),
          w ≠ w' → ∀ γ : Γ, δ ≤ hdist w ((γ : PO n 1) • w')) := fun hsep =>
        hnotgood (by rw [hGooddef]; exact ⟨hmemSub, hsep⟩)
      push_neg at hnotsep
      obtain ⟨a, ha, b, hb, hab, γ, hγlt⟩ := hnotsep
      have ha' : a ∈ S ∨ a = u := by
        simpa only [Set.mem_union, Set.mem_singleton_iff] using ha
      have hb' : b ∈ S ∨ b = u := by
        simpa only [Set.mem_union, Set.mem_singleton_iff] using hb
      rcases ha' with haS | hau
      · rcases hb' with hbS | hbu
        · exact absurd (hSsep a haS b hbS hab γ) (not_le.mpr hγlt)
        · rw [hbu] at hγlt
          refine ⟨γ, ?_⟩
          simp only [Set.mem_iUnion, Set.mem_ofPred_eq, hClosedBall]
          exact ⟨a, haS, le_of_lt hγlt⟩
      · rcases hb' with hbS | hbu
        · rw [hau] at hγlt
          refine ⟨γ⁻¹, ?_⟩
          simp only [Set.mem_iUnion, Set.mem_ofPred_eq, hClosedBall]
          refine ⟨b, hbS, ?_⟩
          have heq : hdist b (((γ⁻¹ : Γ) : PO n 1) • u)
              = hdist u (((γ : Γ) : PO n 1) • b) := by
            have h := hId.isom_smul ((γ : Γ) : PO n 1) b (((γ⁻¹ : Γ) : PO n 1) • u)
            have e : ((γ : Γ) : PO n 1) • (((γ⁻¹ : Γ) : PO n 1) • u) = u := by
              rw [← hAb.mul_smul]
              have hc : ((γ : Γ) : PO n 1) * ((γ⁻¹ : Γ) : PO n 1) = 1 := by
                rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
              rw [hc, hAb.one_smul]
            rw [e] at h
            exact h.symm.trans (hId.symm _ _)
          rw [heq]
          exact le_of_lt hγlt
        · exact absurd (hau.trans hbu.symm) hab

end

end Work.Mostow
