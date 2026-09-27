import Mathlib
import Submission.Work.Mostow.geomFiniteThickThinDefs
import Submission.Work.Mostow.HaarBase
import Submission.Work.Mostow.BoostTransitive
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.VolDefs
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.BaryContinuity

/-!
# The thick part of a lattice is cocompact

For a lattice `Γ ≤ PO(n,1)` and `ε > 0`, the `ε`-thick part
`ThickPart Γ ε = {u | ∀ γ : Γ, γ ≠ 1 → ε ≤ hdist u (γ • u)}` is contained in the
`Γ`-translates of a compact set (`IsCocompactUnder Γ (ThickPart Γ ε)`).

This is the classical "packing" argument.  If `u ∈ ThickPart Γ ε`, then the open hyperbolic
ball of radius `ε/2` about `u` injects into the quotient `Γ \ ℍⁿ`; and if `u, v` lie in a
`Γ`-separated subset of the thick part, then the translates of the two balls are pairwise
disjoint.  A fundamental domain `D` of `Γ` has finite `volH`-measure `V`, and every such ball
has volume `v > 0` (the action of `PO(n,1)` is transitive and preserves `volH`), so a
`Γ`-separated subset of the thick part has at most `V / v` elements.  A maximal such subset is
therefore finite and, by maximality, its `ε`-balls cover the thick part up to the action of `Γ`.

No Margulis-type input is needed: the only analytic ingredient is the invariance of `volH`
under the (transitive) action of `PO(n,1)`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Topology Pointwise

noncomputable section

variable {n : ℕ}

-- The chart `E n` is a `PiLp` space and `PO n 1` a quotient of a matrix group, so unifying
-- `Continuous`- and `MeasurableSpace`-instances is expensive; give the elaborator room.
set_option maxHeartbeats 2000000

/-- The open ball of radius `r` around `u` for the hyperbolic distance. -/
def hBall (u : E n) (r : ℝ) : Set (E n) := {x | hdist u x < r}

/-- The closed ball of radius `r` around `u` for the hyperbolic distance. -/
def hClosedBall (u : E n) (r : ℝ) : Set (E n) := {x | hdist u x ≤ r}

/-! ## Elementary facts -/

/-- `x ↦ hdist u x` is continuous: in the chart it is `arcosh` of the smooth function
`tpart u * tpart x - ⟪u,x⟫`, whose values are `≥ 1`. -/
lemma hdist_continuous_left (u : E n) : Continuous (fun x : E n => hdist u x) := by
  have hcont : Continuous (fun x : E n => tpart u * tpart x - inner ℝ u x) := by
    simp only [tpart]
    fun_prop
  have h := ContinuousOn.comp_continuous (g := Real.arcosh)
    (f := fun x : E n => tpart u * tpart x - inner ℝ u x) (s := Set.Ici 1)
    Real.continuousOn_arcosh hcont (fun x => one_le_cosh_hdist u x)
  simpa [Function.comp_def, hdist] using h

/-- The inverse-translate form of the isometry property, for an element of a subgroup. -/
lemma hdist_smul_inv_left (hAb : POBasic n) (hId : HypIsoData n) {Γ : Subgroup (PO n 1)}
    (γ : Γ) (u v : E n) :
    hdist ((γ : PO n 1) • u) v = hdist u (((γ⁻¹ : Γ) : PO n 1) • v) := by
  have hcoe : (((γ⁻¹ : Γ) : PO n 1)) = ((γ : PO n 1))⁻¹ := rfl
  calc hdist ((γ : PO n 1) • u) v
      = hdist (((γ⁻¹ : Γ) : PO n 1) • ((γ : PO n 1) • u)) (((γ⁻¹ : Γ) : PO n 1) • v) :=
        (hId.isom_smul (((γ⁻¹ : Γ) : PO n 1)) ((γ : PO n 1) • u) v).symm
    _ = hdist u (((γ⁻¹ : Γ) : PO n 1) • v) := by
          rw [hcoe, ← hAb.mul_smul, inv_mul_cancel, hAb.one_smul]

/-- Two hyperbolic balls of radius `r` whose centres are at distance `≥ 2r` are disjoint. -/
lemma hBall_disjoint (hId : HypIsoData n) {u v : E n} {r : ℝ} (h : 2 * r ≤ hdist u v) :
    Disjoint (hBall u r) (hBall v r) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [hBall, Set.mem_ofPred_eq] at hx hx'
  have h1 : hdist u v ≤ hdist u x + hdist x v := hId.triangle u x v
  rw [hId.symm x v] at h1
  linarith

/-- The `volH`-measure of a hyperbolic ball does not depend on its centre: the action of
`PO(n,1)` is transitive and preserves `volH`. -/
theorem volH_hBall_homogeneous (hA : POActionProp n) (hI : HypIsometryProp n)
    (u : E n) (r : ℝ) :
    volH n (hBall u r) = volH n (hBall 0 r) := by
  have hId : HypIsoData n := HypIsoData.ofProp hI
  obtain ⟨g, hg⟩ := (BoostTransitive n hA).1 u
  have hpre : (fun y : E n => g • y) ⁻¹' hBall u r = hBall 0 r := by
    ext x
    simp only [Set.mem_preimage, hBall, Set.mem_ofPred_eq, ← hg, hId.isom_smul g 0 x]
  have hmeas : MeasurableSet (hBall u r) :=
    (isOpen_lt (hdist_continuous_left u) continuous_const).measurableSet
  have hmp : MeasurePreserving (fun y : E n => g • y) (volH n) (volH n) :=
    hId.measurePreserving_smul g
  calc volH n (hBall u r)
      = ((volH n).map (fun y : E n => g • y)) (hBall u r) := by rw [hmp.map_eq]
    _ = volH n ((fun y : E n => g • y) ⁻¹' hBall u r) :=
          Measure.map_apply hmp.measurable hmeas
    _ = volH n (hBall 0 r) := by rw [hpre]



/-- If the `Γ`-translates of a null-measurable set `A` are pairwise a.e. disjoint, then
`volH A ≤ volH D` for a fundamental domain `D` of `Γ`: the "packing bound".

(Delegated as `Work.Mostow.volH_le_fundamentalDomain`; reproduced here because that module
imports the `poCenter`/`poSheet` chain, whose `Work.Mostow.boostP` clashes with the
`Work.Mostow.BoostTransitive.boostP` already in this file's closure through
`Submission.Work.Mostow.geomFiniteThickThinDefs`.) -/
theorem volH_le_of_isFundamentalDomain (hA : POActionProp n) (hI : HypIsometryProp n)
    {Γ : Subgroup (PO n 1)} (hdisc : IsDiscrete (SetLike.coe Γ)) {D A : Set (E n)}
    (hD : IsFundamentalDomain Γ D (volH n)) (hAmeas : NullMeasurableSet A (volH n))
    (hdisj : ∀ γ : Γ, γ ≠ 1 → AEDisjoint (volH n) ((fun x => (γ : PO n 1) • x) '' A) A) :
    volH n A ≤ volH n D := by
  have hAb : POBasic n := POBasic.ofProp hA
  have hId : HypIsoData n := HypIsoData.ofProp hI
  -- the `Γ`-action on the chart, inherited from the `PO n 1`-action
  letI : MulAction (PO n 1) (E n) :=
    { one_smul := fun u => hAb.one_smul u
      mul_smul := fun g h u => hAb.mul_smul g h u }
  letI : MulAction Γ (E n) := inferInstance
  haveI : Countable Γ := (countable_of_isDiscrete (PO n 1) hdisc).to_subtype
  haveI : MeasurableConstSMul Γ (E n) :=
    ⟨fun c => (hId.contDiff_smul (c : PO n 1)).continuous.measurable⟩
  haveI : SMulInvariantMeasure Γ (E n) (volH n) :=
    ⟨fun c s hs => (hId.measurePreserving_smul (c : PO n 1)).measure_preimage hs.nullMeasurableSet⟩
  refine hD.measure_le_of_pairwise_disjoint hAmeas ?_
  rintro γ₁ γ₂ hne
  show volH n ((γ₁ • A ∩ D) ∩ (γ₂ • A ∩ D)) = 0
  have hsub₁ : (γ₁ • A ∩ D) ∩ (γ₂ • A ∩ D) ⊆ γ₁ • A ∩ γ₂ • A :=
    fun x hx => ⟨hx.1.1, hx.2.1⟩
  have hδne : γ₂⁻¹ * γ₁ ≠ (1 : Γ) := by
    intro h
    have h1 : γ₁ = γ₂ := by
      calc γ₁ = γ₂ * (γ₂⁻¹ * γ₁) := by group
        _ = γ₂ := by rw [h, mul_one]
    exact hne h1
  have hg₁ : γ₁ • A = γ₂ • ((γ₂⁻¹ * γ₁) • A) := by
    rw [smul_smul, ← mul_assoc, mul_inv_cancel, one_mul]
  have hsub₂ : γ₁ • A ∩ γ₂ • A ⊆ γ₂ • ((γ₂⁻¹ * γ₁) • A ∩ A) := by
    rw [Set.smul_set_inter, hg₁]
  have hnull : volH n (γ₂ • ((γ₂⁻¹ * γ₁) • A ∩ A)) = 0 := by
    rw [measure_smul (volH n) γ₂]
    exact hdisj (γ₂⁻¹ * γ₁) hδne
  exact measure_mono_null (hsub₁.trans hsub₂) hnull

/-- **The thick part of a lattice is cocompact.** -/
theorem thickPart_cocompact (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ) (ε : ℝ) (hε : 0 < ε) :
    IsCocompactUnder Γ (ThickPart Γ ε) := by
  have hAb : POBasic n := POBasic.ofProp hA
  have hId : HypIsoData n := HypIsoData.ofProp hI
  obtain ⟨hdisc, D, hD, hDfin⟩ := hΓ
  haveI : Countable Γ := (countable_of_isDiscrete (PO n 1) hdisc).to_subtype
  set r : ℝ := ε / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have h2r : 2 * r = ε := by rw [hrdef]; ring
  -- the volume of the test ball is positive
  have hvpos : 0 < volH n (hBall 0 r) :=
    volHPosOpen n (isOpen_lt (hdist_continuous_left 0) continuous_const)
      ⟨0, by
        simp only [hBall, Set.mem_ofPred_eq]
        rw [hdist_self]
        exact hr⟩
  -- the volume of a test ball does not depend on its centre
  have hvol : ∀ u : E n, volH n (hBall u r) = volH n (hBall 0 r) :=
    fun u => volH_hBall_homogeneous hA hI u r
  -- the packing bound for a finite Γ-separated family
  have hbound : ∀ t : Finset (E n), (↑t : Set (E n)) ⊆ ThickPart Γ ε →
      (∀ u ∈ t, ∀ v ∈ t, u ≠ v → ∀ γ : Γ, ε ≤ hdist u ((γ : PO n 1) • v)) →
      (t.card : ℝ≥0∞) * volH n (hBall 0 r) ≤ volH n D := by
    intro t hsub hsep
    set A : Set (E n) := ⋃ u ∈ (t : Set (E n)), hBall u r with hAdef
    have hmemA : ∀ x : E n, x ∈ A ↔ ∃ u ∈ t, hdist u x < r := by
      intro x
      simp only [hAdef, hBall, Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨u, hu, h⟩
        exact ⟨u, by simpa using hu, h⟩
      · rintro ⟨u, hu, h⟩
        exact ⟨u, by simpa using hu, h⟩
    -- the translates of `A` are pairwise disjoint
    have hdisj : ∀ γ : Γ, γ ≠ 1 → AEDisjoint (volH n) ((fun x => (γ : PO n 1) • x) '' A) A := by
      intro γ hγ1
      refine Disjoint.aedisjoint ?_
      rw [Set.disjoint_left]
      intro x hx hxA
      obtain ⟨y, hyA, hyx⟩ := hx
      obtain ⟨u, hu, hux⟩ := (hmemA x).mp hxA
      obtain ⟨v, hv, hvy⟩ := (hmemA y).mp hyA
      have hlt : hdist u ((γ : PO n 1) • v) < ε := by
        have h1 : hdist u ((γ : PO n 1) • v) ≤ hdist u x + hdist x ((γ : PO n 1) • v) :=
          hId.triangle u x ((γ : PO n 1) • v)
        have h2 : hdist x ((γ : PO n 1) • v) = hdist y v := by
          rw [← hyx, hId.isom_smul (γ : PO n 1) y v]
        have h3 : hdist y v < r := by rw [hId.symm y v]; exact hvy
        rw [h2] at h1
        linarith
      rcases eq_or_ne u v with rfl | huv
      · exact absurd (hsub hu γ hγ1) (not_le.mpr hlt)
      · exact absurd (hsep u hu v hv huv γ) (not_le.mpr hlt)
    have hmeas : NullMeasurableSet A (volH n) := by
      rw [hAdef]
      exact (isOpen_biUnion fun u _ =>
        isOpen_lt (hdist_continuous_left u) continuous_const).measurableSet.nullMeasurableSet
    have hpack : volH n A ≤ volH n D := volH_le_of_isFundamentalDomain hA hI hdisc hD hmeas hdisj
    have hvolA : volH n A = (t.card : ℝ≥0∞) * volH n (hBall 0 r) := by
      have hsum : volH n A = ∑ u ∈ t, volH n (hBall u r) := by
        rw [hAdef]
        refine measure_biUnion_finset (fun u hu v hv huv => ?_)
          (fun u _ => (isOpen_lt (hdist_continuous_left u) continuous_const).measurableSet)
        refine hBall_disjoint hId ?_
        rw [h2r]
        have h1 : ε ≤ hdist u (((1 : Γ) : PO n 1) • v) := hsep u hu v hv huv 1
        rwa [show (((1 : Γ) : PO n 1)) = (1 : PO n 1) from rfl,
          hAb.one_smul] at h1
      rw [hsum, Finset.sum_congr rfl (fun u _ => hvol u), Finset.sum_const, nsmul_eq_mul]
    rw [← hvolA]
    exact hpack
  -- a maximal Γ-separated subset of the thick part
  let Good : Set (Set (E n)) :=
    {S : Set (E n) | S ⊆ ThickPart Γ ε ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ∀ γ : Γ, ε ≤ hdist u ((γ : PO n 1) • v)}
  have hGood_empty : (∅ : Set (E n)) ∈ Good := by
    refine ⟨Set.empty_subset _, ?_⟩
    intro u hu
    exact absurd hu (Set.notMem_empty u)
  obtain ⟨S, -, hSmax⟩ := zorn_subset_nonempty Good
    (by
      intro c hc hchain _
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
  have hSsub : S ⊆ ThickPart Γ ε := hSmem.1
  have hSsep : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ∀ γ : Γ, ε ≤ hdist u ((γ : PO n 1) • v) := hSmem.2
  -- maximality gives the covering
  have hcover : ∀ u ∈ ThickPart Γ ε, ∃ v ∈ S, ∃ γ : Γ, hdist u ((γ : PO n 1) • v) < ε := by
    intro u hu
    by_contra hcon
    push_neg at hcon
    have hnew : S ∪ {u} ∈ Good := by
      refine ⟨?_, ?_⟩
      · intro w hw
        rcases hw with hw | hw
        · exact hSsub hw
        · rwa [Set.mem_singleton_iff.mp hw]
      · intro a ha b hb hab γ
        rcases ha with haS | hau <;> rcases hb with hbS | hbu
        · exact hSsep a haS b hbS hab γ
        · rw [Set.mem_singleton_iff.mp hbu]
          have heq : hdist a ((γ : PO n 1) • u) = hdist u (((γ⁻¹ : Γ) : PO n 1) • a) := by
            rw [hId.symm a ((γ : PO n 1) • u), hdist_smul_inv_left hAb hId γ u a]
          rw [heq]
          exact hcon a haS γ⁻¹
        · rw [Set.mem_singleton_iff.mp hau]
          exact hcon b hbS γ
        · rw [Set.mem_singleton_iff.mp hau, Set.mem_singleton_iff.mp hbu] at hab
          exact absurd rfl hab
    have heq : S = S ∪ {u} := (maximal_iff.mp hSmax).2 hnew (by intro x hx; exact Or.inl hx)
    have huS : u ∈ S := by
      have h1 : u ∈ S ∪ {u} := Set.mem_union_right S rfl
      rwa [← heq] at h1
    have hge : ε ≤ hdist u (((1 : Γ) : PO n 1) • u) := hcon u huS 1
    rw [show (((1 : Γ) : PO n 1)) = (1 : PO n 1) from rfl, hAb.one_smul, hdist_self] at hge
    linarith
  -- finiteness of the maximal separated subset
  have hSfin : S.Finite := by
    by_contra hinf
    rw [Set.not_finite] at hinf
    obtain ⟨N, hN⟩ : ∃ N : ℕ, volH n D < (N : ℝ≥0∞) * volH n (hBall 0 r) := by
      by_cases hvtop : volH n (hBall 0 r) = ⊤
      · refine ⟨1, ?_⟩
        rw [hvtop]
        simpa using lt_top_iff_ne_top.mpr hDfin
      · obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt
          (r := volH n D * (volH n (hBall 0 r))⁻¹)
          (ENNReal.mul_ne_top hDfin (ENNReal.inv_ne_top.mpr hvpos.ne'))
        refine ⟨N, ?_⟩
        have hmul := ENNReal.mul_lt_mul_left hvpos.ne' hvtop hN
        rwa [mul_assoc, ENNReal.inv_mul_cancel hvpos.ne' hvtop, mul_one] at hmul
    obtain ⟨t, htS, htcard⟩ := hinf.exists_subset_card_eq N
    have hle := hbound t (fun u hu => hSsub (htS hu))
      (fun u hu v hv huv γ => hSsep u (htS hu) v (htS hv) huv γ)
    rw [htcard] at hle
    exact absurd hle (not_le.mpr hN)
  -- the compact set
  refine ⟨⋃ v ∈ (S : Set (E n)), hClosedBall v ε, ?_, ?_⟩
  · exact hSfin.isCompact_biUnion fun v _ => by simpa [hClosedBall] using hId.ball_compact v ε
  · intro u hu
    obtain ⟨v, hvS, γ, hγ⟩ := hcover u hu
    refine ⟨γ⁻¹, ?_⟩
    have h1 : hdist v (((γ⁻¹ : Γ) : PO n 1) • u) = hdist u ((γ : PO n 1) • v) := by
      rw [hId.symm v (((γ⁻¹ : Γ) : PO n 1) • u), hdist_smul_inv_left hAb hId (γ⁻¹) u v]
      congr 1
      rw [inv_inv]
    simp only [hClosedBall, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨v, hvS, le_of_lt (h1.trans_lt hγ)⟩

end

end Work.Mostow
