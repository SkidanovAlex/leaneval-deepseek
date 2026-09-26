import Mathlib
import Submission.Work.BoxShrink.PinchOff.IB.Main
import Submission.Work.BoxShrink.PinchOff.Stabilizer
import Submission.Work.SurgeryInvariance.Span.union_eq_sup
import Submission.Work.SurgeryInvariance.WindingSpan.carrier_eq_top
import Submission.Work.BoxShrink.PinchOff.windingSpan_sdiff_iUnion_range_eq_of_not_isEssential

/-!
# Exactly one piece of a complement of inessential curves has full winding span

Let `γ : Fin n → ClosedCurve P` be a family of pairwise disjoint *simple* closed curves of a
parametrised torus `P`, all of them *inessential*, and let the complement of their images in the
carrier be split into pieces `X i` which are pairwise disjoint, nonempty, open in the carrier and
cover it.  Then exactly one of the pieces has full winding span.

The argument has two halves.

* *Existence.*  Peeling the curves out of the whole carrier does not change the winding span
  (`Work.BoxShrink.PinchOff.windingSpan_sdiff_iUnion_range_eq_of_not_isEssential`), so the span of
  the complement is that of the carrier, namely `⊤`.  The span of a union of pairwise disjoint open
  pieces is the supremum of the spans of the pieces (`windingSpan_biUnion_eq_sup`, an induction on
  `Work.SurgeryInvariance.Span.union_eq_sup`), and each piece's span is `⊥` or `⊤`
  (`Work.BoxShrink.PinchOff.windingSpan_bot_or_top_aux`).  Hence some piece has span `⊤`.

* *Uniqueness.*  A piece of span `⊤` carries an unbounded connected component of its preimage in
  the parameter plane (`exists_unbounded_component_of_windingSpan_eq_top`, from the contrapositive
  of `Work.BoxShrink.PinchOff.windingSpan_eq_bot_of_components_bounded`).  The preimage of the
  complement of the curves is the disjoint union of the preimages of the pieces, so such a
  component is a component of the complement of the lifted curves; and the complement of a closed
  set with compact components has at most one unbounded component
  (`Work.BoxShrink.PinchOff.unbounded_component_unique`).  Two distinct pieces of span `⊤` would
  therefore have a common component, contradicting disjointness.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff.IB

open Work.BoxShrink.PinchOff

noncomputable section

/-! ## Two generalities on the winding span -/

/-- An arbitrary union of regions open in the carrier is open in the carrier. -/
theorem isOpenInCarrier_iUnion {ι : Type*} {P : Work.CoreTopology.ParamTorus} {u : ι → Set R3}
    (h : ∀ i, Work.SurgeryInvariance.IsOpenInCarrier P (u i)) :
    Work.SurgeryInvariance.IsOpenInCarrier P (⋃ i, u i) := by
  unfold Work.SurgeryInvariance.IsOpenInCarrier at h ⊢
  rw [Set.preimage_iUnion]
  exact isOpen_iUnion h

/-- The empty region is open in the carrier. -/
theorem isOpenInCarrier_empty (P : Work.CoreTopology.ParamTorus) :
    Work.SurgeryInvariance.IsOpenInCarrier P (∅ : Set R3) := by
  rw [Work.SurgeryInvariance.IsOpenInCarrier]
  exact isOpen_empty

/-- The winding span of the empty region vanishes. -/
theorem windingSpan_empty (P : Work.CoreTopology.ParamTorus) :
    Work.SurgeryInvariance.WindingSpan P (∅ : Set R3) = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan, Work.SurgeryInvariance.windingVectors]
  simp

/-- **A finite union of regions open in the carrier is open in the carrier.** -/
theorem isOpenInCarrier_biUnion {ι : Type*} [DecidableEq ι] {P : Work.CoreTopology.ParamTorus}
    {u : ι → Set R3} (h : ∀ i, Work.SurgeryInvariance.IsOpenInCarrier P (u i))
    (s : Finset ι) :
    Work.SurgeryInvariance.IsOpenInCarrier P (⋃ i ∈ (s : Set ι), u i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 : (⋃ i ∈ (((∅ : Finset ι)) : Set ι), u i) = (∅ : Set R3) := by simp
      rw [h0]
      exact isOpenInCarrier_empty P
  | insert a s ha ih =>
      rw [Finset.coe_insert, Set.biUnion_insert]
      exact Work.SurgeryInvariance.isOpenInCarrier_union P (h a) ih

/-- **The winding span is additive over finitely many pairwise disjoint pieces which are open in
the carrier.**  A closed curve of the torus has connected image, so a curve of the union lies in one
of the pieces; the statement follows by induction on the finset from
`Work.SurgeryInvariance.Span.union_eq_sup`. -/
theorem windingSpan_biUnion_eq_sup {ι : Type*} [DecidableEq ι] {P : Work.CoreTopology.ParamTorus}
    {u : ι → Set R3} (hopen : ∀ i, Work.SurgeryInvariance.IsOpenInCarrier P (u i))
    (hdisj : ∀ i j : ι, i ≠ j → Disjoint (u i) (u j)) (s : Finset ι) :
    Work.SurgeryInvariance.WindingSpan P (⋃ i ∈ (s : Set ι), u i)
      = s.sup (fun i => Work.SurgeryInvariance.WindingSpan P (u i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sup_empty]
      have h : (⋃ i ∈ (((∅ : Finset ι)) : Set ι), u i) = (∅ : Set R3) := by simp
      rw [h, windingSpan_empty]
  | insert a s ha ih =>
      have hdisj' : Disjoint (u a) (⋃ i ∈ (s : Set ι), u i) := by
        rw [Set.disjoint_left]
        rintro x hx hxs
        simp only [Set.mem_iUnion, exists_prop] at hxs
        obtain ⟨i, his, hxi⟩ := hxs
        exact Set.disjoint_left.mp (hdisj a i (fun h => ha (h ▸ his))) hx hxi
      calc Work.SurgeryInvariance.WindingSpan P (⋃ i ∈ (((insert a s : Finset ι)) : Set ι), u i)
          = Work.SurgeryInvariance.WindingSpan P (u a ∪ ⋃ i ∈ (s : Set ι), u i) := by
            rw [Finset.coe_insert, Set.biUnion_insert]
        _ = Work.SurgeryInvariance.WindingSpan P (u a) ⊔
              Work.SurgeryInvariance.WindingSpan P (⋃ i ∈ (s : Set ι), u i) :=
              Work.SurgeryInvariance.Span.union_eq_sup (hopen a)
                (isOpenInCarrier_biUnion hopen s) hdisj'
        _ = Work.SurgeryInvariance.WindingSpan P (u a) ⊔
              s.sup (fun i => Work.SurgeryInvariance.WindingSpan P (u i)) := by rw [ih]
        _ = (insert a s).sup (fun i => Work.SurgeryInvariance.WindingSpan P (u i)) := by
              rw [Finset.sup_insert]

/-! ## Regions of full span have unbounded lifted components -/

/-- **A region of full winding span has an unbounded component in the parameter plane.**  If every
connected component of the preimage `X̃` were bounded, the winding span of `X` would vanish
(`Work.BoxShrink.PinchOff.windingSpan_eq_bot_of_components_bounded`, whose proof shows that a
bounded component cannot be invariant under a nonzero lattice translation). -/
theorem exists_unbounded_component_of_windingSpan_eq_top {P : Work.CoreTopology.ParamTorus}
    {X : Set R3} (hXc : X ⊆ P.carrier) (hopen : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (h : Work.SurgeryInvariance.WindingSpan P X = ⊤) :
    ∃ x ∈ Xtilde P X, ∀ R : ℝ, ∃ w ∈ connectedComponentIn (Xtilde P X) x, R ≤ ‖w‖ := by
  have hne : Work.SurgeryInvariance.WindingSpan P X ≠ ⊥ := by rw [h]; exact top_ne_bot
  have hnbdd : ¬ ∀ z : ℂ, Bornology.IsBounded (connectedComponentIn (Xtilde P X) z) :=
    fun hb => hne (windingSpan_eq_bot_of_components_bounded hXc hopen hb)
  push Not at hnbdd
  obtain ⟨z, hz⟩ := hnbdd
  have hunb : ∀ R : ℝ, ∃ w ∈ connectedComponentIn (Xtilde P X) z, R ≤ ‖w‖ := by
    intro R
    by_contra hcon
    push Not at hcon
    exact hz (Bornology.IsBounded.subset Metric.isBounded_closedBall (fun w hw => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt (hcon w hw)))
  obtain ⟨x, hxmem, -⟩ := hunb 0
  refine ⟨x, connectedComponentIn_subset _ _ hxmem, fun R => ?_⟩
  obtain ⟨w, hw, hR⟩ := hunb R
  rw [connectedComponentIn_eq hxmem] at hw
  exact ⟨w, hw, hR⟩

/-! ## The theorem -/

theorem existsUnique_top_of_partition {P : Work.CoreTopology.ParamTorus} {n : ℕ}
    {γ : Fin n → Work.CoreTopology.ClosedCurve P}
    {X : Fin n → Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (γ i))
    (hess : ∀ i, ¬ Work.CoreTopology.IsEssential P (γ i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ))
    (hsub : ∀ i, X i ⊆ P.carrier)
    (hopen : ∀ i, Work.SurgeryInvariance.IsOpenInCarrier P (X i))
    (hdisjX : ∀ i j : Fin n, i ≠ j → Disjoint (X i) (X j))
    (hcover : P.carrier \ (⋃ i, Set.range (γ i).γ) = ⋃ i, X i)
    (hne : ∀ i, (X i).Nonempty) :
    ∃! i : Fin n, Work.SurgeryInvariance.WindingSpan P (X i) = ⊤ := by
  classical
  set C : Set R3 := ⋃ i, Set.range (γ i).γ with hCdef
  -- the carrier is open in itself
  have hcarrier_open : Work.SurgeryInvariance.IsOpenInCarrier P P.carrier := by
    rw [Work.SurgeryInvariance.IsOpenInCarrier]
    have h : (Subtype.val ⁻¹' P.carrier : Set P.carrier) = Set.univ := by ext x; simp
    rw [h]; exact isOpen_univ
  -- the union of the curves is compact, hence closed
  have hC_closed : IsClosed C := by
    rw [hCdef]
    refine (isCompact_iUnion (fun i => ?_)).isClosed
    have h : Set.range (γ i).γ = (γ i).γ '' Set.Icc (0 : ℝ) (2 * Real.pi) := by
      refine Set.Subset.antisymm ?_ (Set.image_subset_range _ _)
      rw [Work.CoreTopology.ClosedCurve.range_eq_image P (γ i)]
      exact Set.image_mono Set.Ico_subset_Icc_self
    rw [h]
    exact isCompact_Icc.image_of_continuousOn (γ i).cont.continuousOn
  -- each piece lies in the complement of the curves
  have hX_sub : ∀ i, X i ⊆ P.carrier \ C := by
    intro i
    rw [hCdef, hcover]
    exact Set.subset_iUnion (fun j => X j) i
  -- the preimage of the complement of the curves is the union of the lifted pieces
  have hXt_u : (Xtilde P C)ᶜ = ⋃ i, Xtilde P (X i) := by
    have h1 : (Xtilde P C)ᶜ = Xtilde P Cᶜ := by
      show (planePsi P ⁻¹' C)ᶜ = planePsi P ⁻¹' Cᶜ
      exact Set.preimage_compl.symm
    have h2 : Xtilde P Cᶜ = Xtilde P (P.carrier \ C) := by
      ext z
      exact ⟨fun hz => ⟨planePsi_mem_carrier P z, hz⟩, fun hz => hz.2⟩
    have h4 : Xtilde P (⋃ i, X i) = ⋃ i, Xtilde P (X i) := by
      show planePsi P ⁻¹' (⋃ i, X i) = ⋃ i, planePsi P ⁻¹' X i
      exact Set.preimage_iUnion
    rw [h1, h2, hcover, h4]
  have hXt_disj : ∀ i j : Fin n, i ≠ j → Disjoint (Xtilde P (X i)) (Xtilde P (X j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hz1 hz2
    exact Set.disjoint_left.mp (hdisjX i j hij) hz1 hz2
  -- each lifted piece is clopen in the preimage of the complement
  have hXt_clopen : ∀ i, IsOpen ((Xtilde P C)ᶜ \ Xtilde P (X i)) := by
    intro i
    have hset : (Xtilde P C)ᶜ \ Xtilde P (X i)
        = Set.iUnion (fun j : {j : Fin n // j ≠ i} => Xtilde P (X j.1)) := by
      rw [hXt_u]
      ext z
      constructor
      · rintro ⟨hz, hzi⟩
        obtain ⟨k, hzk⟩ := Set.mem_iUnion.mp hz
        by_cases hki : k = i
        · exact absurd (hki ▸ hzk) hzi
        · exact Set.mem_iUnion.mpr ⟨⟨k, hki⟩, hzk⟩
      · intro hz
        obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hz
        exact ⟨Set.mem_iUnion.mpr ⟨j.1, hzj⟩,
          fun hzi => Set.disjoint_left.mp (hXt_disj j.1 i j.2) hzj hzi⟩
    rw [hset]
    exact isOpen_iUnion (fun j => isOpen_Xtilde (hsub j.1) (hopen j.1))
  have hCt_closed : IsClosed (Xtilde P C) := hC_closed.preimage (continuous_planePsi P)
  have hcomp : ∀ z ∈ Xtilde P C, IsCompact (connectedComponentIn (Xtilde P C) z) := by
    rw [hCdef]
    exact components_compact hsimple hess hdisj
  -- **Existence**: peeling shows that the complement of the curves spans everything
  have hpeel : Work.SurgeryInvariance.WindingSpan P (P.carrier \ C) = ⊤ := by
    rw [hCdef]
    rw [← Work.BoxShrink.PinchOff.windingSpan_sdiff_iUnion_range_eq_of_not_isEssential
      (P := P) (X := P.carrier) (γ := γ) hcarrier_open hsimple hess hdisj
      (fun i t => (γ i).mem t)]
    exact Work.SurgeryInvariance.WindingSpan.carrier_eq_top P
  have htop : Work.SurgeryInvariance.WindingSpan P (⋃ i, X i) = ⊤ := by
    rw [hCdef, hcover] at hpeel
    exact hpeel
  have hsup : Work.SurgeryInvariance.WindingSpan P (⋃ i, X i)
      = ⨆ i, Work.SurgeryInvariance.WindingSpan P (X i) := by
    have h := windingSpan_biUnion_eq_sup (P := P) (u := X) hopen hdisjX
      (Finset.univ : Finset (Fin n))
    have h1 : (⋃ i ∈ (((Finset.univ : Finset (Fin n))) : Set (Fin n)), X i) = ⋃ i, X i := by
      ext z; simp
    rw [h1, Finset.sup_univ_eq_iSup] at h
    exact h
  -- each piece spans either everything or nothing
  have hdich : ∀ i : Fin n, Work.SurgeryInvariance.WindingSpan P (X i) = ⊥ ∨
      Work.SurgeryInvariance.WindingSpan P (X i) = ⊤ := by
    intro i
    refine Work.BoxShrink.PinchOff.windingSpan_bot_or_top_aux (P := P) (γ := γ)
      (X := X i) (Y := Set.iUnion (fun j : {j : Fin n // j ≠ i} => X j.1)) hsimple hess hdisj
      (hopen i) (isOpenInCarrier_iUnion (fun j => hopen j.1)) ?_ ?_
    · rw [Set.disjoint_left]
      rintro x hx hxy
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxy
      exact Set.disjoint_left.mp (hdisjX i j.1 (fun h => j.2 h.symm)) hx hxj
    · rw [hcover]
      ext x
      constructor
      · intro hx
        obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
        by_cases hji : j = i
        · exact Or.inl (hji ▸ hxj)
        · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hxj⟩)
      · rintro (hx | hx)
        · exact Set.mem_iUnion.mpr ⟨i, hx⟩
        · obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
          exact Set.mem_iUnion.mpr ⟨j.1, hxj⟩
  have hex : ∃ i : Fin n, Work.SurgeryInvariance.WindingSpan P (X i) = ⊤ := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ i : Fin n, Work.SurgeryInvariance.WindingSpan P (X i) = ⊥ :=
      fun i => (hdich i).resolve_right (hcon i)
    have hbot : (⨆ i, Work.SurgeryInvariance.WindingSpan P (X i)) = ⊥ := iSup_eq_bot.mpr hall
    have : (⊤ : Submodule ℚ (ℚ × ℚ)) = ⊥ := by rw [← htop, hsup, hbot]
    exact top_ne_bot this
  -- **Uniqueness**
  have huniq : ∀ i j : Fin n, Work.SurgeryInvariance.WindingSpan P (X i) = ⊤ →
      Work.SurgeryInvariance.WindingSpan P (X j) = ⊤ → i = j := by
    intro i j hi hj
    by_contra hij
    obtain ⟨x, hxXt, hxunb⟩ :=
      exists_unbounded_component_of_windingSpan_eq_top (hsub i) (hopen i) hi
    obtain ⟨y, hyXt, hyunb⟩ :=
      exists_unbounded_component_of_windingSpan_eq_top (hsub j) (hopen j) hj
    have hXi_sub : Xtilde P (X i) ⊆ (Xtilde P C)ᶜ := by
      rw [hXt_u]; exact Set.subset_iUnion (fun k => Xtilde P (X k)) i
    have hXj_sub : Xtilde P (X j) ⊆ (Xtilde P C)ᶜ := by
      rw [hXt_u]; exact Set.subset_iUnion (fun k => Xtilde P (X k)) j
    have hxi : connectedComponentIn (Xtilde P C)ᶜ x = connectedComponentIn (Xtilde P (X i)) x :=
      connectedComponentIn_of_clopen hXi_sub (isOpen_Xtilde (hsub i) (hopen i))
        (hXt_clopen i) hxXt
    have hxj : connectedComponentIn (Xtilde P C)ᶜ y = connectedComponentIn (Xtilde P (X j)) y :=
      connectedComponentIn_of_clopen hXj_sub (isOpen_Xtilde (hsub j) (hopen j))
        (hXt_clopen j) hyXt
    have hxC : x ∉ Xtilde P C := by simpa using hXi_sub hxXt
    have hyC : y ∉ Xtilde P C := by simpa using hXj_sub hyXt
    have hbx : ∀ R : ℝ, ∃ w ∈ connectedComponentIn (Xtilde P C)ᶜ x, R ≤ ‖w‖ := by
      intro R
      obtain ⟨w, hw, hR⟩ := hxunb R
      rw [← hxi] at hw
      exact ⟨w, hw, hR⟩
    have hby : ∀ R : ℝ, ∃ w ∈ connectedComponentIn (Xtilde P C)ᶜ y, R ≤ ‖w‖ := by
      intro R
      obtain ⟨w, hw, hR⟩ := hyunb R
      rw [← hxj] at hw
      exact ⟨w, hw, hR⟩
    have heq := unbounded_component_unique hCt_closed hcomp hxC hyC hbx hby
    have hyin : y ∈ Xtilde P (X i) := by
      have h1 : y ∈ connectedComponentIn (Xtilde P C)ᶜ x := by
        rw [heq]
        exact mem_connectedComponentIn hyC
      have h2 : y ∈ connectedComponentIn (Xtilde P (X i)) x := by
        rw [← hxi]; exact h1
      exact connectedComponentIn_subset _ _ h2
    exact Set.disjoint_left.mp (hXt_disj i j hij) hyin hyXt
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, hi, fun j hj => huniq j i hj hi⟩

end

end Work.BoxShrink.PinchOff.IB
