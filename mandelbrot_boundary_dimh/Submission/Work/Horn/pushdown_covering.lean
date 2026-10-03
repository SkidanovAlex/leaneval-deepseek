import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.basic
import Submission.Work.HornCov.covering_of_components
import Submission.Work.HornCov.covering_components_homeomorph
import Submission.Work.Horn.sheets_eq_of_inter
import Submission.Work.Horn.homeomorph_image_of_injOn
import Submission.Work.Horn.injOn_piExp_of_sheet

namespace Work.Horn

open Set Topology

noncomputable section

/-! ## `π` is continuous and open -/

theorem piExp_isOpenMap : IsOpenMap MandelDim.piExp := by
  have h1 : MandelDim.piExp = Complex.exp ∘
      (Homeomorph.mulLeft₀ (2 * (Real.pi : ℂ) * Complex.I) (by simp)) := by
    funext w
    rw [Function.comp_apply, Homeomorph.coe_mulLeft₀]
    rfl
  rw [h1]
  exact Complex.isOpenMap_exp.comp (Homeomorph.mulLeft₀ _ _).isOpenMap

theorem piExp_continuous : Continuous MandelDim.piExp := by
  unfold MandelDim.piExp; fun_prop

/-! ## A component of the preimage of a ball under a covering is a sheet -/

theorem sheet_homeo_of_component {X : Set ℂ} (hX : IsOpen X) {O : Set ℂ} (hO : IsOpen O)
    [SimplyConnectedSpace ↥O] [LocallyPathConnectedSpace ↥O]
    {E : ℂ → ℂ} {p : ↥X → ℂ} (hpE : ∀ x : ↥X, p x = E (x : ℂ)) (hpc : Continuous p)
    (hp : IsCoveringMapOn p O) (hsurj : ∀ s ∈ O, ∃ x : ↥X, p x = s)
    (x : ↥X) (hx : p x ∈ O) :
    ∃ H : ↥(Subtype.val '' connectedComponentIn (p ⁻¹' O) x) ≃ₜ ↥O,
      IsOpen (Subtype.val '' connectedComponentIn (p ⁻¹' O) x) ∧
      E '' (Subtype.val '' connectedComponentIn (p ⁻¹' O) x) = O ∧
      (∀ u : ↥(Subtype.val '' connectedComponentIn (p ⁻¹' O) x), (H u : ℂ) = E (u : ℂ)) := by
  haveI : LocallyPathConnectedSpace ↥X := hX.locallyPathConnectedSpace
  let A : Set ℂ := Subtype.val '' connectedComponentIn (p ⁻¹' O) x
  let e : ↥(connectedComponentIn (p ⁻¹' O) x) ≃ₜ ↥A :=
    Topology.IsEmbedding.subtypeVal.homeomorphImage (connectedComponentIn (p ⁻¹' O) x)
  obtain ⟨H₀, hH₀⟩ :=
    Work.HornCov.covering_components_homeomorph (p := p) (S := O) hO hp hsurj x hx
  let H : ↥A ≃ₜ ↥O := e.symm.trans H₀
  have hcoe : ∀ z : ↥(connectedComponentIn (p ⁻¹' O) x), ((e z : ↥A) : ℂ) = ((z : ↥X) : ℂ) :=
    fun z => by simp only [e, A, Homeomorph.trans_apply]; rfl
  have hcompat : ∀ u : ↥A, (H u : ℂ) = E (u : ℂ) := by
    intro u
    show (H₀ (e.symm u) : ℂ) = E (u : ℂ)
    rw [hH₀]
    show p ((e.symm u : ↥(connectedComponentIn (p ⁻¹' O) x)) : ↥X) = E (u : ℂ)
    rw [hpE]
    congr 1
    have happ : e (e.symm u) = u := Homeomorph.apply_symm_apply _ u
    calc (((e.symm u : ↥(connectedComponentIn (p ⁻¹' O) x))) : ↥X)
        = ((e (e.symm u) : ↥A) : ℂ) := by rw [← hcoe]
      _ = (u : ℂ) := by rw [happ]
  refine ⟨H, ?_, ?_, hcompat⟩
  · exact hX.isOpenMap_subtype_val _ ((hO.preimage hpc).connectedComponentIn)
  · refine Set.Subset.antisymm ?_ ?_
    · rintro y ⟨u, hu, rfl⟩
      rw [← hcompat ⟨u, hu⟩]
      exact (H ⟨u, hu⟩).2
    · intro y hy
      refine ⟨((H.symm ⟨y, hy⟩ : ↥A) : ℂ), (H.symm ⟨y, hy⟩).2, ?_⟩
      rw [← hcompat (H.symm ⟨y, hy⟩)]
      exact congrArg (fun t : ↥O => (t : ℂ)) (Homeomorph.apply_symm_apply H ⟨y, hy⟩)

/-! ## The sheet candidate predicate -/

/-- A set is a sheet over `O` if it is the image of a component of `E⁻¹(O)` in one of the
two ends. -/
def IsESheet (E : ℂ → ℂ) (Yu Yl O : Set ℂ) (A : Set ℂ) : Prop :=
  (∃ w : ↥Yu, E (w : ℂ) ∈ O ∧
      A = Subtype.val '' connectedComponentIn ((fun x : ↥Yu => E x) ⁻¹' O) w) ∨
  (∃ w : ↥Yl, E (w : ℂ) ∈ O ∧
      A = Subtype.val '' connectedComponentIn ((fun x : ↥Yl => E x) ⁻¹' O) w)

/-! ## The main transfer lemma -/

theorem pushdown_covering_aux {E : ℂ → ℂ} {Yu Yl : Set ℂ} {v : ℂ}
    (hYuO : IsOpen Yu) (hYlO : IsOpen Yl)
    (hYuT : MandelDim.IsTInvariant Yu) (hYlT : MandelDim.IsTInvariant Yl)
    (hYuE : ∀ w ∈ Yu, E (w + 1) = E w + 1) (hYlE : ∀ w ∈ Yl, E (w + 1) = E w + 1)
    (hYuc : Continuous (fun w : ↥Yu => E w)) (hYlc : Continuous (fun w : ↥Yl => E w))
    (hcovu : IsCoveringMapOn (fun w : ↥Yu => E w) {y : ℂ | ∀ k : ℤ, y ≠ v + k})
    (hcovl : IsCoveringMapOn (fun w : ↥Yl => E w) {y : ℂ | ∀ k : ℤ, y ≠ v + k})
    (hsurju : ∀ y : ℂ, (∀ k : ℤ, y ≠ v + k) → ∃ w ∈ Yu, E w = y)
    (hsurjl : ∀ y : ℂ, (∀ k : ℤ, y ≠ v + k) → ∃ w ∈ Yl, E w = y) :
    IsCoveringMapOn
      (fun z : ↥(insert 0 (MandelDim.piExp '' (Yu ∪ Yl))) => MandelDim.pushdown E (z : ℂ))
      {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ MandelDim.piExp v} := by
  intro x hx
  obtain ⟨hx0, hxv⟩ := hx
  -- a canonical lift of `x`
  let c₀ : ℂ := Complex.log x / (2 * Real.pi * Complex.I)
  have hπc₀ : MandelDim.piExp c₀ = x := MandelDim.piExp_log_div x hx0
  -- the unramified base set
  let S : Set ℂ := {y : ℂ | ∀ k : ℤ, y ≠ v + k}
  have hc₀S : c₀ ∈ S := fun k hk =>
    hxv (by rw [← hπc₀, hk]; exact Work.Horn.MandelDim.piExp_add_intCast v k)
  have hSopen : IsOpen S := by
    have hcl : IsClosed (Set.range (fun k : ℤ => v + (k : ℂ))) := by
      have h2 : Set.range (fun k : ℤ => v + (k : ℂ))
          = (fun z : ℂ => z - v) ⁻¹' Set.range (fun k : ℤ => (k : ℂ)) := by
        ext y; simp only [Set.mem_range, Set.mem_preimage]
        constructor
        · rintro ⟨k, rfl⟩; exact ⟨k, by ring⟩
        · rintro ⟨k, hk⟩; exact ⟨k, by rw [hk]; ring⟩
      rw [h2]
      exact Complex.isClosed_range_intCast.preimage (continuous_id.sub continuous_const)
    have h1 : S = (Set.range (fun k : ℤ => v + (k : ℂ)))ᶜ := by
      ext y; simp only [S, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_range, not_exists]
      exact forall_congr' fun k => by rw [eq_comm]
    rw [h1]; exact hcl.isOpen_compl
  obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.mp hSopen c₀ hc₀S
  let ε : ℝ := min r (1/4)
  have hεpos : 0 < ε := lt_min hr (by norm_num)
  have hε2 : 2 * ε < 1 := by have h : ε ≤ 1/4 := min_le_right _ _; linarith
  let O : Set ℂ := Metric.ball c₀ ε
  have hOopen : IsOpen O := Metric.isOpen_ball
  have hOsub : O ⊆ S := (Metric.ball_subset_ball (min_le_left _ _)).trans hrS
  have hOconn : IsPreconnected O := Metric.isPreconnected_ball
  haveI hOcontr : ContractibleSpace ↥O :=
    Convex.contractibleSpace (convex_ball c₀ ε) ⟨c₀, Metric.mem_ball_self hεpos⟩
  haveI hOSC : SimplyConnectedSpace ↥O := SimplyConnectedSpace.ofContractible _
  haveI hOLP : LocallyPathConnectedSpace ↥O := hOopen.locallyPathConnectedSpace
  haveI hYuLP : LocallyPathConnectedSpace ↥Yu := hYuO.locallyPathConnectedSpace
  haveI hYlLP : LocallyPathConnectedSpace ↥Yl := hYlO.locallyPathConnectedSpace
  have hUopen : IsOpen (MandelDim.piExp '' O) := piExp_isOpenMap O hOopen
  have hxU : x ∈ MandelDim.piExp '' O := ⟨c₀, Metric.mem_ball_self hεpos, hπc₀⟩
  -- the target is contained in the punctured plane
  have hUsub : MandelDim.piExp '' O ⊆ {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ MandelDim.piExp v} := by
    rintro ζ ⟨o, ho, rfl⟩
    refine ⟨MandelDim.piExp_ne_zero o, ?_⟩
    intro hc
    obtain ⟨k, hk⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp hc
    exact (hOsub ho) k hk
  -- surjectivity of the two coverings over `O`
  have hsurjO_u : ∀ s ∈ O, ∃ w : ↥Yu, E w = s := fun s hs => by
    obtain ⟨w, hw, hwe⟩ := hsurju s (hOsub hs); exact ⟨⟨w, hw⟩, hwe⟩
  have hsurjO_l : ∀ s ∈ O, ∃ w : ↥Yl, E w = s := fun s hs => by
    obtain ⟨w, hw, hwe⟩ := hsurjl s (hOsub hs); exact ⟨⟨w, hw⟩, hwe⟩
  have hcovuO : IsCoveringMapOn (fun w : ↥Yu => E w) O := hcovu.mono hOsub
  have hcovlO : IsCoveringMapOn (fun w : ↥Yl => E w) O := hcovl.mono hOsub
  -- `π` is injective on `O`
  have hInjO : Set.InjOn MandelDim.piExp O :=
    injOn_piExp_of_sheet (E := id) (X := Set.univ) (W := O) (c := c₀) (ε := ε)
      (fun w => Iff.rfl) (fun w _ => rfl) (Set.subset_univ _) hε2 (fun z hz => hz)
  -- integer equivariance on the union
  have hUT : MandelDim.IsTInvariant (Yu ∪ Yl) := fun w => by
    simp only [Set.mem_union]; rw [hYuT w, hYlT w]
  have hUE : ∀ w ∈ Yu ∪ Yl, w + 1 ∈ Yu ∪ Yl → E (w + 1) = E w + 1 := fun w hw _ =>
    hw.elim (fun h => hYuE w h) (fun h => hYlE w h)
  -- the homeomorphism `O ≅ π '' O`
  have hOUhom : ∃ H : ↥O ≃ₜ ↥(MandelDim.piExp '' O),
      ∀ a : ↥O, (H a : ℂ) = MandelDim.piExp (a : ℂ) :=
    homeomorph_image_of_injOn piExp_continuous piExp_isOpenMap hOopen hInjO
  -- the sheet predicate
  have sheetData : ∀ A : Set ℂ, IsESheet E Yu Yl O A →
      ∃ (H : ↥A ≃ₜ ↥O) (_ : IsOpen A), A ⊆ Yu ∪ Yl ∧ E '' A = O ∧
        (∀ u : ↥A, (H u : ℂ) = E (u : ℂ)) := by
    intro A hA
    rcases hA with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
    · obtain ⟨H, hAopen, hrange, hcomp⟩ :=
        sheet_homeo_of_component hYuO hOopen (E := E) (p := fun x : ↥Yu => E x)
          (fun x => rfl) hYuc hcovuO hsurjO_u w hw
      refine ⟨H, hAopen, ?_, hrange, hcomp⟩
      rintro a ⟨z, -, rfl⟩; exact Or.inl z.2
    · obtain ⟨H, hAopen, hrange, hcomp⟩ :=
        sheet_homeo_of_component hYlO hOopen (E := E) (p := fun x : ↥Yl => E x)
          (fun x => rfl) hYlc hcovlO hsurjO_l w hw
      refine ⟨H, hAopen, ?_, hrange, hcomp⟩
      rintro a ⟨z, -, rfl⟩; exact Or.inr z.2
  -- distinct sheets are equal or disjoint
  have sheetDisj : ∀ A A' : Set ℂ, IsESheet E Yu Yl O A → IsESheet E Yu Yl O A' →
      (A ∩ A').Nonempty → A = A' := by
    intro A A' hA hA' hne
    obtain ⟨HA, hAopen, -, -, hAcomp⟩ := sheetData A hA
    obtain ⟨HA', hA'open, -, -, hA'comp⟩ := sheetData A' hA'
    exact sheets_eq_of_inter hOconn hAopen hA'open HA hAcomp HA' hA'comp hne
  -- `π` is injective on a union of sheets
  have hInjUnion : ∀ A A' : Set ℂ, IsESheet E Yu Yl O A → IsESheet E Yu Yl O A' →
      Set.InjOn MandelDim.piExp (A ∪ A') := by
    intro A A' hA hA'
    obtain ⟨-, -, hAsub, hArange, -⟩ := sheetData A hA
    obtain ⟨-, -, hA'sub, hA'range, -⟩ := sheetData A' hA'
    refine injOn_piExp_of_sheet (E := E) (X := Yu ∪ Yl) (W := A ∪ A') (c := c₀) (ε := ε) hUT ?_ ?_ hε2 ?_
    · intro w hw
      exact hUE w hw ((hUT w).mp hw)
    · rintro a (ha | ha)
      · exact hAsub ha
      · exact hA'sub ha
    · intro a ha
      rcases ha with ha | ha
      · show E a ∈ O; rw [← hArange]; exact ⟨a, ha, rfl⟩
      · show E a ∈ O; rw [← hA'range]; exact ⟨a, ha, rfl⟩
  -- each sheet maps homeomorphically onto its `π`-image
  have hAZhomeo : ∀ A : Set ℂ, IsESheet E Yu Yl O A →
      ∃ H : ↥A ≃ₜ ↥(MandelDim.piExp '' A), ∀ a : ↥A, (H a : ℂ) = MandelDim.piExp (a : ℂ) := by
    intro A hA
    obtain ⟨-, hAopen, -, -, -⟩ := sheetData A hA
    exact homeomorph_image_of_injOn piExp_continuous piExp_isOpenMap hAopen
      ((hInjUnion A A hA hA).mono Set.subset_union_left)
  -- the index type of sheets
  let ι := {A : Set ℂ // IsESheet E Yu Yl O A}
  letI : TopologicalSpace ι := ⊥
  haveI : DiscreteTopology ι := ⟨rfl⟩
  let D : Set ℂ := insert 0 (MandelDim.piExp '' (Yu ∪ Yl))
  let C : ι → Set ↥D := fun i => {z : ↥D | (z : ℂ) ∈ MandelDim.piExp '' (i.1)}
  let g : ↥D → ℂ := fun z => MandelDim.pushdown E (z : ℂ)
  have sheetData' : ∀ i : ι, ∃ (H : ↥(i.1) ≃ₜ ↥O) (_ : IsOpen (i.1)),
      i.1 ⊆ Yu ∪ Yl ∧ E '' (i.1) = O ∧ (∀ u : ↥(i.1), (H u : ℂ) = E (u : ℂ)) :=
    fun i => sheetData i.1 i.2
  choose sheetH hSheetOpen hSheetSub hSheetRange hSheetComp using sheetData'
  have hCopen : ∀ i : ι, IsOpen (C i) := fun i =>
    (piExp_isOpenMap i.1 (hSheetOpen i)).preimage continuous_subtype_val
  have hCdisj : Pairwise (fun i j : ι => Disjoint (C i) (C j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    simp only [C, Set.mem_setOf_eq] at hzi hzj
    obtain ⟨a, ha, haz⟩ := hzi
    obtain ⟨a', ha', ha'z⟩ := hzj
    have hπ : MandelDim.piExp a = MandelDim.piExp a' := by rw [haz, ha'z]
    have hinj := hInjUnion i.1 j.1 i.2 j.2
    have heq : a = a' := hinj (Or.inl ha) (Or.inr ha') hπ
    have hne : (i.1 ∩ j.1).Nonempty := ⟨a, ha, heq ▸ ha'⟩
    exact hij (Subtype.ext (sheetDisj i.1 j.1 i.2 j.2 hne))
  have hCcov : g ⁻¹' (MandelDim.piExp '' O) = ⋃ i : ι, C i := by
    ext z
    constructor
    · intro hz
      have hzD : (z : ℂ) ∈ insert 0 (MandelDim.piExp '' (Yu ∪ Yl)) := z.2
      have hz0 : (z : ℂ) ≠ 0 := by
        intro h
        obtain ⟨o, ho, hoz⟩ := hz
        have h1 : MandelDim.pushdown E (z : ℂ) = 0 := by
          rw [h]; exact Work.Horn.MandelDim.pushdown_zero E
        have h2 : MandelDim.piExp o = 0 := by
          have h3 := hoz
          rw [show g z = MandelDim.pushdown E (z : ℂ) from rfl, h1] at h3
          exact h3
        exact MandelDim.piExp_ne_zero o h2
      obtain ⟨w, hw, hwz⟩ : ∃ w ∈ Yu ∪ Yl, MandelDim.piExp w = (z : ℂ) := by
        rcases hzD with h | h
        · exact absurd h hz0
        · exact h
      obtain ⟨o, ho, hoz⟩ := hz
      have hEw : MandelDim.pushdown E (z : ℂ) = MandelDim.piExp (E w) := by
        rw [← hwz]
        exact Work.Horn.MandelDim.pushdown_piExp hUT hUE hw
      have hπEo : MandelDim.piExp (E w) = MandelDim.piExp o := by
        calc MandelDim.piExp (E w) = MandelDim.pushdown E (z : ℂ) := hEw.symm
          _ = g z := rfl
          _ = MandelDim.piExp o := hoz.symm
      obtain ⟨k, hk⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp hπEo
      have hside : (w - (k : ℂ) ∈ Yu) ∨ (w - (k : ℂ) ∈ Yl) := by
        rcases hw with h | h
        · exact Or.inl (by
            have h' := Work.Horn.MandelDim.IsTInvariant.add_int hYuT h (-k)
            rwa [show w + ((-k : ℤ) : ℂ) = w - (k : ℂ) by push_cast; ring] at h')
        · exact Or.inr (by
            have h' := Work.Horn.MandelDim.IsTInvariant.add_int hYlT h (-k)
            rwa [show w + ((-k : ℤ) : ℂ) = w - (k : ℂ) by push_cast; ring] at h')
      have hEwk : E (w - (k : ℂ)) = o := by
        rcases hw with h | h
        · have h1 : E (w + ((-k : ℤ) : ℂ)) = E w + ((-k : ℤ) : ℂ) :=
            Work.Horn.MandelDim.E_add_int (E := E) hYuT (fun w hw _ => hYuE w hw) h (-k)
          rw [show w + ((-k : ℤ) : ℂ) = w - (k : ℂ) by push_cast; ring] at h1
          rw [h1, hk]; push_cast; ring
        · have h1 : E (w + ((-k : ℤ) : ℂ)) = E w + ((-k : ℤ) : ℂ) :=
            Work.Horn.MandelDim.E_add_int (E := E) hYlT (fun w hw _ => hYlE w hw) h (-k)
          rw [show w + ((-k : ℤ) : ℂ) = w - (k : ℂ) by push_cast; ring] at h1
          rw [h1, hk]; push_cast; ring
      have hπwk : MandelDim.piExp (w - (k : ℂ)) = MandelDim.piExp w := by
        have h := Work.Horn.MandelDim.piExp_add_intCast (w - (k : ℂ)) k
        rw [show w - (k : ℂ) + (k : ℂ) = w by ring] at h
        exact h.symm
      rcases hside with hmem | hmem
      · have hc : (⟨w - (k : ℂ), hmem⟩ : ↥Yu) ∈
            connectedComponentIn ((fun x : ↥Yu => E x) ⁻¹' O) ⟨w - (k : ℂ), hmem⟩ :=
          mem_connectedComponentIn (by show E (w - (k : ℂ)) ∈ O; rw [hEwk]; exact ho)
        refine Set.mem_iUnion.mpr ⟨⟨Subtype.val ''
            connectedComponentIn ((fun x : ↥Yu => E x) ⁻¹' O) ⟨w - (k : ℂ), hmem⟩,
            Or.inl ⟨⟨w - (k : ℂ), hmem⟩, by rw [hEwk]; exact ho, rfl⟩⟩, ?_⟩
        exact ⟨w - (k : ℂ), ⟨⟨w - (k : ℂ), hmem⟩, hc, rfl⟩, by rw [hπwk]; exact hwz⟩
      · have hc : (⟨w - (k : ℂ), hmem⟩ : ↥Yl) ∈
            connectedComponentIn ((fun x : ↥Yl => E x) ⁻¹' O) ⟨w - (k : ℂ), hmem⟩ :=
          mem_connectedComponentIn (by show E (w - (k : ℂ)) ∈ O; rw [hEwk]; exact ho)
        refine Set.mem_iUnion.mpr ⟨⟨Subtype.val ''
            connectedComponentIn ((fun x : ↥Yl => E x) ⁻¹' O) ⟨w - (k : ℂ), hmem⟩,
            Or.inr ⟨⟨w - (k : ℂ), hmem⟩, by rw [hEwk]; exact ho, rfl⟩⟩, ?_⟩
        exact ⟨w - (k : ℂ), ⟨⟨w - (k : ℂ), hmem⟩, hc, rfl⟩, by rw [hπwk]; exact hwz⟩
    · intro hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      simp only [C, Set.mem_setOf_eq] at hi
      obtain ⟨a, ha, haz⟩ := hi
      have hEaO : E a ∈ O := by rw [← hSheetRange i]; exact ⟨a, ha, rfl⟩
      refine ⟨E a, hEaO, ?_⟩
      have hpp := Work.Horn.MandelDim.pushdown_piExp (E := E) hUT hUE (hSheetSub i ha)
      rw [haz] at hpp
      exact hpp.symm
  have hHomeo : ∀ i : ι, ∃ H : ↥(C i) ≃ₜ ↥(MandelDim.piExp '' O),
      ∀ z : ↥(C i), (H z : ℂ) = MandelDim.pushdown E (z : ℂ) := by
    intro i
    obtain ⟨HOU, hHOU⟩ := hOUhom
    obtain ⟨HAZ, hHAZ⟩ := hAZhomeo i.1 i.2
    have himg : Subtype.val '' C i = MandelDim.piExp '' (i.1) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        obtain ⟨a, ha, rfl⟩ := hy
        exact ⟨⟨MandelDim.piExp a, Set.mem_insert_of_mem _
          ⟨a, hSheetSub i ha, rfl⟩⟩, ⟨a, ha, rfl⟩, rfl⟩
    let e1 : ↥(C i) ≃ₜ ↥(MandelDim.piExp '' (i.1)) :=
      (Topology.IsEmbedding.subtypeVal.homeomorphImage (C i)).trans (Homeomorph.setCongr himg)
    let H : ↥(C i) ≃ₜ ↥(MandelDim.piExp '' O) := e1.trans (HAZ.symm.trans ((sheetH i).trans HOU))
    refine ⟨H, ?_⟩
    intro z
    have he1 : ((e1 z : ↥(MandelDim.piExp '' (i.1))) : ℂ) = (z : ℂ) := by
      show ((Topology.IsEmbedding.subtypeVal.homeomorphImage (C i) z :
        ↥(Subtype.val '' C i)) : ℂ) = (z : ℂ)
      rw [Topology.IsEmbedding.homeomorphImage]
      rfl
    have hπw : MandelDim.piExp (((HAZ.symm (e1 z)) : ↥(i.1)) : ℂ) = (z : ℂ) := by
      have hh := hHAZ (HAZ.symm (e1 z))
      rw [Homeomorph.apply_symm_apply] at hh
      rw [← hh]
      exact he1
    have hcomp : (H z : ℂ) = MandelDim.piExp (E (((HAZ.symm (e1 z)) : ↥(i.1)) : ℂ)) := by
      simp only [H, Homeomorph.trans_apply, hHOU, hSheetComp i, hHAZ]
    rw [hcomp, ← hπw]
    exact (Work.Horn.MandelDim.pushdown_piExp hUT hUE (hSheetSub i (HAZ.symm (e1 z)).2)).symm
  choose Hhat hHhat using hHomeo
  exact Work.HornCov.covering_of_components (f := g)
    (S := MandelDim.piExp '' O) hUopen C hCopen hCdisj hCcov Hhat hHhat x hxU

/-! ## A covering over a preconnected base with nonempty range is onto the base -/

theorem surjOn_of_isCoveringMapOn {X : Type*} [TopologicalSpace X] {f : X → ℂ} {S : Set ℂ}
    (hf : IsCoveringMapOn f S) (hS : IsPreconnected S) (hne : ∃ x : X, f x ∈ S) :
    ∀ y ∈ S, ∃ x : X, f x = y := by
  haveI : PreconnectedSpace ↥S := Subtype.preconnectedSpace hS
  have hcl : IsClopen {y : ↥S | ∃ x : X, f x = (y : ℂ)} := by
    refine ⟨?_, ?_⟩
    · -- the complement of the range is open
      have hopen : IsOpen {y : ↥S | ∃ x : X, f x = (y : ℂ)}ᶜ := by
        rw [isOpen_iff_mem_nhds]
        rintro y hy
        haveI : IsEmpty ↥(f ⁻¹' ({(y : ℂ)} : Set ℂ)) :=
          Set.isEmpty_coe_sort.mpr
            (Set.eq_empty_of_subset_empty fun x hx => hy ⟨x, by simpa using hx⟩)
        obtain ⟨-, U, hyU, hUopen, -, H, -⟩ := hf (y : ℂ) y.2
        have hUempty : f ⁻¹' U = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro x hx
          exact isEmptyElim ((H ⟨x, hx⟩).2)
        refine Filter.mem_of_superset
          ((hUopen.preimage continuous_subtype_val).mem_nhds
          (by simpa only [Set.mem_preimage] using hyU)) ?_
        rintro y' hy' ⟨x, hx⟩
        have hxU : x ∈ f ⁻¹' U := by rw [Set.mem_preimage, hx]; exact hy'
        rw [hUempty] at hxU
        exact hxU
      simpa using isClosed_compl_iff.mpr hopen
    · -- the range is open
      rw [isOpen_iff_mem_nhds]
      rintro y ⟨x, hx⟩
      haveI : Nonempty ↥(f ⁻¹' ({(y : ℂ)} : Set ℂ)) := ⟨⟨x, by simpa using hx⟩⟩
      obtain ⟨-, U, hyU, hUopen, -, H, hH⟩ := hf (y : ℂ) y.2
      refine Filter.mem_of_superset
        ((hUopen.preimage continuous_subtype_val).mem_nhds
          (by simpa only [Set.mem_preimage] using hyU)) ?_
      rintro y' hy'
      refine ⟨(H.symm (⟨⟨(y' : ℂ), (by simpa only [Set.mem_preimage] using hy')⟩,
        Classical.ofNonempty⟩)).1, ?_⟩
      have key : (H (H.symm (⟨⟨(y' : ℂ), (by simpa only [Set.mem_preimage] using hy')⟩,
          Classical.ofNonempty⟩))).1.1 = (y' : ℂ) := by
        rw [Homeomorph.apply_symm_apply]
      exact (hH _).symm.trans key
  have huniv := hcl.eq_univ ⟨⟨f hne.choose, hne.choose_spec⟩, hne.choose, rfl⟩
  intro y hy
  have hmem : (⟨y, hy⟩ : ↥S) ∈ {y : ↥S | ∃ x : X, f x = (y : ℂ)} := by
    rw [huniv]; exact Set.mem_univ _
  exact hmem

theorem E_surjOn_ends_local (hTopo : MandelDim.HornTopoStatement)
    {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c)
    (hcov : IsCoveringMapOn (fun x : MandelDim.BuOf d B => d.E x)
              {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k} ∧
            IsCoveringMapOn (fun x : MandelDim.BlOf d B => d.E x)
              {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k}) :
    (∀ y : ℂ, (∀ k : ℤ, y ≠ d.Φ c + k) → ∃ w ∈ MandelDim.BuOf d B, d.E w = y) ∧
    (∀ y : ℂ, (∀ k : ℤ, y ≠ d.Φ c + k) → ∃ w ∈ MandelDim.BlOf d B, d.E w = y) := by
  obtain ⟨hBuO, hBlO, hBuT, hBlT, hUp, hLo, hDE⟩ := hTopo f₀ D₀ B c d hsetup
  have hSconn : IsPreconnected {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k} := by
    have hrange : {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k}
        = (Set.range (fun k : ℤ => d.Φ c + (k : ℂ)))ᶜ := by
      ext y; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_range, not_exists]
      exact forall_congr' fun k => by rw [eq_comm]
    rw [hrange]
    exact (Set.Countable.isPathConnected_compl_of_one_lt_rank (E := ℂ)
      (by rw [Complex.rank_real_complex]; norm_num) (Set.countable_range _)).isConnected.isPreconnected
  constructor
  · intro y hy
    obtain ⟨x, hx⟩ := surjOn_of_isCoveringMapOn hcov.1 hSconn (by
      -- a point of `BuOf` whose `E`-image avoids the lattice
      obtain ⟨R, hR⟩ := Work.Horn.MandelDim.ParabData.E_upper_iff d 1 (by norm_num)
      set t : ℝ := max R (max d.η₀ ((d.Φ c).im + 2)) + 1 with htdef
      have htη : d.η₀ < t := by
        have h1 : d.η₀ ≤ max d.η₀ ((d.Φ c).im + 2) := le_max_left _ _
        have h2 : max d.η₀ ((d.Φ c).im + 2)
            ≤ max R (max d.η₀ ((d.Φ c).im + 2)) := le_max_right _ _
        rw [htdef]; linarith
      have htR : R < t := by
        have h1 : R ≤ max R (max d.η₀ ((d.Φ c).im + 2)) := le_max_left _ _
        rw [htdef]; linarith
      have ht2 : (d.Φ c).im + 2 < t := by
        have h1 : (d.Φ c).im + 2 ≤ max d.η₀ ((d.Φ c).im + 2) := le_max_right _ _
        have h2 : max d.η₀ ((d.Φ c).im + 2)
            ≤ max R (max d.η₀ ((d.Φ c).im + 2)) := le_max_right _ _
        rw [htdef]; linarith
      have htI : ((t : ℂ) * Complex.I).im = t := by simp
      refine ⟨⟨(t : ℂ) * Complex.I, hUp (by show d.η₀ < ((t : ℂ) * Complex.I).im; rw [htI]; exact htη)⟩, ?_⟩
      intro k hk
      have hsmall : ‖d.E ((t : ℂ) * Complex.I) - (t : ℂ) * Complex.I‖ < 1 :=
        hR _ (by rw [htI]; exact htR)
      have him : |(d.E ((t : ℂ) * Complex.I) - (t : ℂ) * Complex.I).im| ≤
          ‖d.E ((t : ℂ) * Complex.I) - (t : ℂ) * Complex.I‖ := Complex.abs_im_le_norm _
      have hlt := abs_lt.mp (lt_of_le_of_lt him hsmall)
      have hdecomp : (d.E ((t : ℂ) * Complex.I)).im =
          t + (d.E ((t : ℂ) * Complex.I) - (t : ℂ) * Complex.I).im := by
        nth_rewrite 1 [show d.E ((t : ℂ) * Complex.I) = (t : ℂ) * Complex.I +
          (d.E ((t : ℂ) * Complex.I) - (t : ℂ) * Complex.I) by ring]
        rw [Complex.add_im, htI]
      have hki : (d.E ((t : ℂ) * Complex.I)).im = (d.Φ c).im := by rw [hk]; simp
      rw [hdecomp] at hki
      linarith [hlt.1]) y hy
    exact ⟨x.1, x.2, hx⟩
  · intro y hy
    obtain ⟨x, hx⟩ := surjOn_of_isCoveringMapOn hcov.2 hSconn (by
      obtain ⟨cl, hcl⟩ := Work.Horn.MandelDim.ParabData.E_lower_iff d
      obtain ⟨R, hR⟩ := hcl 1 (by norm_num)
      set t : ℝ := max R (max d.η₀ (cl.im + 2 - (d.Φ c).im)) + 1 with htdef
      have htη : d.η₀ < t := by
        have h1 : d.η₀ ≤ max d.η₀ (cl.im + 2 - (d.Φ c).im) := le_max_left _ _
        have h2 : max d.η₀ (cl.im + 2 - (d.Φ c).im)
            ≤ max R (max d.η₀ (cl.im + 2 - (d.Φ c).im)) := le_max_right _ _
        rw [htdef]; linarith
      have htR : R < t := by
        have h1 : R ≤ max R (max d.η₀ (cl.im + 2 - (d.Φ c).im)) := le_max_left _ _
        rw [htdef]; linarith
      have ht3 : cl.im + 1 - (d.Φ c).im < t := by
        have h1 : cl.im + 2 - (d.Φ c).im ≤ max d.η₀ (cl.im + 2 - (d.Φ c).im) := le_max_right _ _
        have h2 : max d.η₀ (cl.im + 2 - (d.Φ c).im)
            ≤ max R (max d.η₀ (cl.im + 2 - (d.Φ c).im)) := le_max_right _ _
        rw [htdef]; linarith
      have htI : (-(t : ℂ) * Complex.I).im = -t := by simp
      refine ⟨⟨-(t : ℂ) * Complex.I, hLo (by show (-(t : ℂ) * Complex.I).im < -d.η₀; rw [htI]; linarith)⟩, ?_⟩
      intro k hk
      have hsmall : ‖d.E (-(t : ℂ) * Complex.I) - (-(t : ℂ) * Complex.I) - cl‖ < 1 :=
        hR _ (by rw [htI]; linarith)
      have him : |(d.E (-(t : ℂ) * Complex.I) - (-(t : ℂ) * Complex.I) - cl).im| ≤
          ‖d.E (-(t : ℂ) * Complex.I) - (-(t : ℂ) * Complex.I) - cl‖ :=
        Complex.abs_im_le_norm _
      have hlt := abs_lt.mp (lt_of_le_of_lt him hsmall)
      have hdecomp : (d.E (-(t : ℂ) * Complex.I)).im =
          -t + cl.im + (d.E (-(t : ℂ) * Complex.I) - (-(t : ℂ) * Complex.I) - cl).im := by
        nth_rewrite 1 [show d.E (-(t : ℂ) * Complex.I) = (-(t : ℂ) * Complex.I) +
          (cl + (d.E (-(t : ℂ) * Complex.I) - (-(t : ℂ) * Complex.I) - cl)) by ring]
        rw [Complex.add_im, Complex.add_im, htI]
        ring
      have hki : (d.E (-(t : ℂ) * Complex.I)).im = (d.Φ c).im := by rw [hk]; simp
      rw [hdecomp] at hki
      linarith [hlt.2]) y hy
    exact ⟨x.1, x.2, hx⟩

/-! ## The lemma requested by the HORN owner -/

theorem pushdown_covering (hTopo : MandelDim.HornTopoStatement)
    {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c)
    (hcov : IsCoveringMapOn (fun x : MandelDim.BuOf d B => d.E x)
          {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k} ∧
        IsCoveringMapOn (fun x : MandelDim.BlOf d B => d.E x)
          {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k}) :
    IsCoveringMapOn
      (fun z : ↥(insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B))) =>
        MandelDim.pushdown d.E (z : ℂ))
      {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ MandelDim.piExp (d.Φ c)} := by
  obtain ⟨hsurju, hsurjl⟩ := E_surjOn_ends_local hTopo d hsetup hcov
  obtain ⟨hBuO, hBlO, hBuT, hBlT, hUp, hLo, hDE⟩ := hTopo f₀ D₀ B c d hsetup
  have hYuE : ∀ w ∈ MandelDim.BuOf d B, d.E (w + 1) = d.E w + 1 := fun w hw =>
    Work.Horn.MandelDim.ParabData.E_add_one d (hDE (Or.inl hw))
      (hDE (Or.inl ((hBuT w).mp hw)))
  have hYlE : ∀ w ∈ MandelDim.BlOf d B, d.E (w + 1) = d.E w + 1 := fun w hw =>
    Work.Horn.MandelDim.ParabData.E_add_one d (hDE (Or.inr hw))
      (hDE (Or.inr ((hBlT w).mp hw)))
  have hYuc : Continuous (fun w : ↥(MandelDim.BuOf d B) => d.E w) := by
    have hsub : MandelDim.BuOf d B ⊆ d.Dφ := fun w hw => (hDE (Or.inl hw)).1
    have hdiff : DifferentiableOn ℂ d.E (MandelDim.BuOf d B) :=
      d.Φ_holo.comp (d.φ_holo.mono hsub) (fun w hw => (hDE (Or.inl hw)).2)
    exact hdiff.continuousOn.restrict
  have hYlc : Continuous (fun w : ↥(MandelDim.BlOf d B) => d.E w) := by
    have hsub : MandelDim.BlOf d B ⊆ d.Dφ := fun w hw => (hDE (Or.inr hw)).1
    have hdiff : DifferentiableOn ℂ d.E (MandelDim.BlOf d B) :=
      d.Φ_holo.comp (d.φ_holo.mono hsub) (fun w hw => (hDE (Or.inr hw)).2)
    exact hdiff.continuousOn.restrict
  exact pushdown_covering_aux (E := d.E) (Yu := MandelDim.BuOf d B) (Yl := MandelDim.BlOf d B)
    (v := d.Φ c) hBuO hBlO hBuT hBlT hYuE hYlE hYuc hYlc hcov.1 hcov.2 hsurju hsurjl


end

end Work.Horn
