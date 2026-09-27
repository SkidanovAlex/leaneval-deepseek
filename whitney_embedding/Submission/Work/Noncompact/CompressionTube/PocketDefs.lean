import Mathlib
import Submission.Work.Noncompact.CompressionTube.proper_continuous_floor

/-!
# Pocket hulls and pocket-free compact exhaustions

The "pocket hull" machinery of Whitney's compression argument: a *pocket* of a set `C` is a
relatively compact component of the complement of `C`; the pocket hull of `C` is `C` together with
the closures of all the pockets.  Completing the even levels of a compact exhaustion by their
pockets gives a *pocket-free* exhaustion: every component of the complement of a level has
non-compact closure.  This is the input of the shell-by-shell routing of the spines and of the
line construction.  (This material used to be the header of
`Submission/Work/Noncompact/CompressionTube/exists_disjoint_lines`; it is kept in its own module so
that it is available *below* the target file -- in particular to `Work.Noncompact.Routing.*`, which
the target file imports.)
-/

namespace Work.Noncompact.CompressionTube

open Set Topology Function

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]

/-- A *pocket* of a set `C`: a relatively compact component of the complement of `C`. -/
def IsPocket (C Q : Set M) : Prop :=
  ∃ x ∈ Cᶜ, Q = connectedComponentIn Cᶜ x ∧ IsCompact (closure Q)

/-- The *pocket hull* of `C`: `C` together with the closures of all the pockets of `C`. -/
def pocketHull (C : Set M) : Set M :=
  C ∪ ⋃₀ (closure '' {Q : Set M | IsPocket C Q})

lemma pocket_subset_compl {C Q : Set M} (h : IsPocket C Q) : Q ⊆ Cᶜ := by
  obtain ⟨x, hx, rfl, -⟩ := h
  exact connectedComponentIn_subset _ _

lemma pocket_preconnected {C Q : Set M} (h : IsPocket C Q) : IsPreconnected Q := by
  obtain ⟨x, hx, rfl, -⟩ := h
  exact isPreconnected_connectedComponentIn

lemma pocket_closure_subset_hull {C Q : Set M} (h : IsPocket C Q) :
    closure Q ⊆ pocketHull C := by
  intro y hy
  exact Or.inr (mem_sUnion.mpr ⟨closure Q, mem_image_of_mem closure h, hy⟩)

lemma subset_pocketHull {C : Set M} : C ⊆ pocketHull C := fun x hx => Or.inl hx

lemma component_eq_of_inter {F Q Q' : Set M}
    (hQ : ∃ x, Q = connectedComponentIn F x) (hQ' : ∃ y, Q' = connectedComponentIn F y)
    (h : (Q ∩ Q').Nonempty) : Q = Q' := by
  obtain ⟨z, hzQ, hzQ'⟩ := h
  obtain ⟨x, rfl⟩ := hQ
  obtain ⟨y, rfl⟩ := hQ'
  rw [connectedComponentIn_eq hzQ, connectedComponentIn_eq hzQ']

lemma pocket_closure_diff_subset [LocallyConnectedSpace M] {C Q : Set M} (hCc : IsClosed C)
    (h : IsPocket C Q) : closure Q \ Q ⊆ C := by
  obtain ⟨x, hx, rfl, -⟩ := h
  intro y hy
  by_contra hyC
  have hyF : y ∈ Cᶜ := hyC
  set U : Set M := connectedComponentIn Cᶜ y with hU
  have hUopen : IsOpen U := by
    rw [hU]; exact (isOpen_compl_iff.mpr hCc).connectedComponentIn
  have hUne : (U ∩ connectedComponentIn Cᶜ x).Nonempty :=
    mem_closure_iff.mp hy.1 U hUopen (mem_connectedComponentIn hyF)
  have heq : U = connectedComponentIn Cᶜ x :=
    component_eq_of_inter ⟨y, rfl⟩ ⟨x, rfl⟩ (by simpa [hU] using hUne)
  have : y ∈ connectedComponentIn Cᶜ x := heq ▸ mem_connectedComponentIn hyF
  exact hy.2 this

lemma front_ne_of_isPocket [LocallyConnectedSpace M] {C Q : Set M} (hM : ¬ CompactSpace M)
    (hCc : IsClosed C) (hQ : IsPocket C Q) : (closure Q \ Q).Nonempty := by
  by_contra hempty
  rw [not_nonempty_iff_eq_empty] at hempty
  obtain ⟨x, hx, hQeq, hQc⟩ := hQ
  have hsubQ : closure Q ⊆ Q := Set.diff_eq_empty.mp hempty
  have hclosed : IsClosed Q := closure_subset_iff_isClosed.mp hsubQ
  have hopen : IsOpen Q := hQeq ▸ (isOpen_compl_iff.mpr hCc).connectedComponentIn
  rcases (isPreconnected_iff_subset_of_disjoint.mp isPreconnected_univ) Q Qᶜ hopen
      hclosed.isOpen_compl (by simp) (by simp) with h | h
  · have hQuniv : Q = univ := Set.eq_univ_of_univ_subset h
    rw [hQuniv, closure_univ] at hQc
    exact hM (isCompact_univ_iff.mp hQc)
  · have hxQ : x ∈ Q := by rw [hQeq]; exact mem_connectedComponentIn hx
    exact (h trivial) hxQ

lemma component_subset_compl_hull [LocallyConnectedSpace M] {C : Set M} (hCc : IsClosed C)
    {x : M} (hx : x ∉ pocketHull C) : connectedComponentIn Cᶜ x ⊆ (pocketHull C)ᶜ := by
  intro y hy
  have hyF : y ∈ Cᶜ := connectedComponentIn_subset _ _ hy
  rintro (hyC | hyS)
  · exact hyF hyC
  · obtain ⟨_, ⟨Q, hQ, rfl⟩, hyQ⟩ := mem_sUnion.mp hyS
    obtain ⟨q, hq, hQeq, hQc⟩ := hQ
    set U : Set M := connectedComponentIn Cᶜ y with hU
    have hUopen : IsOpen U := by
      rw [hU]; exact (isOpen_compl_iff.mpr hCc).connectedComponentIn
    have hUne : (U ∩ Q).Nonempty := mem_closure_iff.mp hyQ U hUopen (mem_connectedComponentIn hyF)
    have heq : U = Q := component_eq_of_inter ⟨y, rfl⟩ ⟨q, hQeq⟩ (by simpa [hU] using hUne)
    have hxC' : x ∈ Cᶜ := fun hcon => hx (subset_pocketHull hcon)
    have hxU : x ∈ U := by
      rw [hU]
      have hcy : connectedComponentIn Cᶜ y = connectedComponentIn Cᶜ x :=
        (connectedComponentIn_eq hy).symm
      rw [hcy]
      exact mem_connectedComponentIn hxC'
    have hxQ : x ∈ Q := heq ▸ hxU
    exact hx (pocket_closure_subset_hull ⟨q, hq, hQeq, hQc⟩ (subset_closure hxQ))

lemma isClosed_pocketHull [LocallyConnectedSpace M] {C : Set M} (hCc : IsClosed C) :
    IsClosed (pocketHull C) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hxC : x ∈ Cᶜ := fun hcon => hx (subset_pocketHull hcon)
  exact Filter.mem_of_superset
    ((IsOpen.connectedComponentIn (isOpen_compl_iff.mpr hCc)).mem_nhds
      (mem_connectedComponentIn hxC))
    (component_subset_compl_hull hCc hx)

lemma exists_lt_of_isCompact {g : M → ℝ} (hg : Continuous g) {C : Set M} (hC : IsCompact C) :
    ∃ t : ℝ, ∀ x ∈ C, g x < t := by
  obtain ⟨a, ha⟩ := (hC.image hg).bddAbove
  exact ⟨a + 1, fun x hx => lt_of_le_of_lt (ha ⟨x, hx, rfl⟩) (lt_add_one a)⟩

lemma pocket_subset_or_meets [LocallyConnectedSpace M] {C : Set M} (hM : ¬ CompactSpace M)
    (hCc : IsClosed C) {g : M → ℝ} (hg : Continuous g)
    {t : ℝ} (ht : ∀ x ∈ C, g x < t) {Q : Set M} (hQ : IsPocket C Q) :
    (Q ∩ g ⁻¹' {t}).Nonempty ∨ Q ⊆ g ⁻¹' (Iio t) := by
  by_cases hmeet : (Q ∩ g ⁻¹' {t}).Nonempty
  · exact Or.inl hmeet
  · right
    obtain ⟨x, hx, hQeq, hQc⟩ := hQ
    have hQpre : IsPreconnected Q := hQeq ▸ isPreconnected_connectedComponentIn
    have hfront : (closure Q \ Q).Nonempty := front_ne_of_isPocket hM hCc ⟨x, hx, hQeq, hQc⟩
    obtain ⟨q, hqcl, hqQ⟩ := hfront
    have hqC : q ∈ C := pocket_closure_diff_subset hCc ⟨x, hx, hQeq, hQc⟩ ⟨hqcl, hqQ⟩
    have hqt : g q < t := ht q hqC
    obtain ⟨y, hyt, hyQ⟩ :=
      mem_closure_iff.mp hqcl {z : M | g z < t} (isOpen_lt hg continuous_const) hqt
    intro z hzQ
    by_contra hcon
    have hzt : t < g z := by
      refine lt_of_le_of_ne (not_lt.mp hcon) ?_
      intro hzt
      exact hmeet ⟨z, hzQ, hzt.symm⟩
    have hord : (g '' Q).OrdConnected :=
      isPreconnected_iff_ordConnected.mp (hQpre.image g hg.continuousOn)
    have hmem : t ∈ g '' Q :=
      hord.out ⟨y, hyQ, rfl⟩ ⟨z, hzQ, rfl⟩ ⟨le_of_lt hyt, le_of_lt hzt⟩
    obtain ⟨w, hwQ, hwt⟩ := hmem
    exact hmeet ⟨w, hwQ, hwt⟩

lemma pocket_closure_subset_Iio [LocallyConnectedSpace M] {C Q : Set M} (hCc : IsClosed C)
    {g : M → ℝ} {t : ℝ} (ht : ∀ x ∈ C, g x < t) (hQ : IsPocket C Q)
    (hsub : Q ⊆ g ⁻¹' (Iio t)) : closure Q ⊆ g ⁻¹' (Iio t) := by
  intro z hz
  by_cases hzQ : z ∈ Q
  · exact hsub hzQ
  · exact ht z (pocket_closure_diff_subset hCc hQ ⟨hz, hzQ⟩)

lemma finite_pockets_meeting [LocallyConnectedSpace M] {C : Set M} (hCc : IsClosed C)
    {g : M → ℝ} (hg : Continuous g) (hgp : IsProperMap g) {t : ℝ} (ht : ∀ x ∈ C, g x < t) :
    {Q : Set M | IsPocket C Q ∧ (Q ∩ g ⁻¹' {t}).Nonempty}.Finite := by
  have hK : IsCompact (g ⁻¹' ({t} : Set ℝ)) := hgp.isCompact_preimage isCompact_singleton
  have hUopen : ∀ y : {y : M // y ∈ g ⁻¹' ({t} : Set ℝ)},
      IsOpen (connectedComponentIn Cᶜ y.1) := fun y =>
    (isOpen_compl_iff.mpr hCc).connectedComponentIn
  have hcov : g ⁻¹' ({t} : Set ℝ) ⊆
      ⋃ y : {y : M // y ∈ g ⁻¹' ({t} : Set ℝ)}, connectedComponentIn Cᶜ y.1 := by
    intro z hz
    have hzt : g z = t := by simpa using hz
    have hzC : z ∈ Cᶜ := fun hcon => absurd (ht z hcon) (by rw [hzt]; exact lt_irrefl t)
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_connectedComponentIn hzC⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun y : {y : M // y ∈ g ⁻¹' ({t} : Set ℝ)} => connectedComponentIn Cᶜ y.1) hUopen hcov
  refine (s.image (fun y : {y : M // y ∈ g ⁻¹' ({t} : Set ℝ)} =>
    connectedComponentIn Cᶜ y.1)).finite_toSet.subset ?_
  intro Q hQ
  obtain ⟨hQp, hQm⟩ := hQ
  obtain ⟨z, hzQ, hzg⟩ := hQm
  have hzt : g z = t := by simpa using hzg
  have hzC : z ∈ Cᶜ := fun hcon => absurd (ht z hcon) (by rw [hzt]; exact lt_irrefl t)
  obtain ⟨hQw, hQspec⟩ := hQp
  have hzs : z ∈ ⋃ y ∈ s, connectedComponentIn Cᶜ y.1 := hs hzg
  obtain ⟨y, hys, hzy⟩ := mem_iUnion₂.mp hzs
  have hQeq : Q = connectedComponentIn Cᶜ z :=
    component_eq_of_inter ⟨hQw, hQspec.2.1⟩ ⟨z, rfl⟩ ⟨z, hzQ, mem_connectedComponentIn hzC⟩
  have hyeq : connectedComponentIn Cᶜ y.1 = connectedComponentIn Cᶜ z :=
    connectedComponentIn_eq hzy
  exact Finset.mem_image.mpr ⟨y, hys, by rw [hQeq, hyeq]⟩

theorem isCompact_pocketHull [LocallyConnectedSpace M] (hM : ¬ CompactSpace M) {g : M → ℝ}
    (hg : Continuous g) (hgp : IsProperMap g) (hgnn : ∀ x, 0 ≤ g x) {C : Set M}
    (hC : IsCompact C) : IsCompact (pocketHull C) := by
  have hCc : IsClosed C := hC.isClosed
  obtain ⟨t, ht⟩ := exists_lt_of_isCompact hg hC
  have hfin := finite_pockets_meeting hCc hg hgp ht
  have hbig : IsCompact (C ∪ g ⁻¹' (Set.Icc 0 t) ∪
      ⋃ Q ∈ {Q : Set M | IsPocket C Q ∧ (Q ∩ g ⁻¹' {t}).Nonempty}, closure Q) :=
    (hC.union (hgp.isCompact_preimage isCompact_Icc)).union
      (hfin.isCompact_biUnion (fun Q hQ => by
        obtain ⟨x, hx, hQeq, hQc⟩ := hQ.1; exact hQc))
  refine hbig.of_isClosed_subset (isClosed_pocketHull hCc) ?_
  intro y hy
  rcases hy with hyC | hyS
  · exact Or.inl (Or.inl hyC)
  · obtain ⟨_, ⟨Q, hQ, rfl⟩, hyQ⟩ := mem_sUnion.mp hyS
    rcases pocket_subset_or_meets hM hCc hg ht hQ with hmeet | hsub
    · exact Or.inr (mem_biUnion (show Q ∈ {Q : Set M | IsPocket C Q ∧
        (Q ∩ g ⁻¹' {t}).Nonempty} from ⟨hQ, hmeet⟩) hyQ)
    · exact Or.inl (Or.inr ⟨hgnn y, le_of_lt (pocket_closure_subset_Iio hCc ht hQ hsub hyQ)⟩)

/-- Components in a smaller set sit inside components in a bigger set. -/
lemma connectedComponentIn_mono {F F' : Set M} (h : F ⊆ F') (x : M) :
    connectedComponentIn F x ⊆ connectedComponentIn F' x := by
  by_cases hx : x ∈ F
  · exact IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
      (mem_connectedComponentIn hx) (subset_trans (connectedComponentIn_subset F x) h)
  · rw [connectedComponentIn_eq_empty (by simpa using hx)]
    exact empty_subset _

/-- The pocket hull of the empty set is empty: the ambient space is non-compact. -/
lemma pocketHull_empty (hM : ¬ CompactSpace M) : pocketHull (∅ : Set M) = ∅ := by
  rw [pocketHull, Set.empty_union, Set.sUnion_eq_empty]
  rintro T ⟨Q, hQ, rfl⟩
  obtain ⟨x, hx, hQeq, hQc⟩ := hQ
  have hQuniv : Q = univ := by
    rw [hQeq, Set.compl_empty, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ x]
  rw [hQuniv, closure_univ] at hQc
  exact absurd (isCompact_univ_iff.mp hQc) hM

/-- Pockets of `C` are contained in the pocket hull of any bigger set `D`. -/
lemma pocket_subset_pocketHull_of_subset {C D Q : Set M} (hCD : C ⊆ D)
    (hQ : IsPocket C Q) : Q ⊆ pocketHull D := by
  obtain ⟨x, hx, hQeq, hQc⟩ := hQ
  intro y hy
  by_cases hyD : y ∈ D
  · exact subset_pocketHull hyD
  · have hyF : y ∈ Dᶜ := hyD
    have hy' : y ∈ connectedComponentIn Cᶜ x := hQeq ▸ hy
    have hcy : connectedComponentIn Cᶜ y = connectedComponentIn Cᶜ x :=
      (connectedComponentIn_eq hy').symm
    have hRsub : connectedComponentIn Dᶜ y ⊆ Q := by
      refine subset_trans (connectedComponentIn_mono (compl_subset_compl.mpr hCD) y) ?_
      rw [hcy, ← hQeq]
    exact pocket_closure_subset_hull ⟨y, hyF, rfl,
      IsCompact.of_isClosed_subset hQc isClosed_closure (closure_mono hRsub)⟩
      (subset_closure (mem_connectedComponentIn hyF))

/-- **A pocket-free exhaustion**, built by completing the even levels of any compact
exhaustion with the closures of their relatively compact complement components. -/
theorem pocketFreeExhaustion_self {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M] (hM : ¬ CompactSpace M) :
    ∃ K : ℕ → Set M,
      (∀ i, IsCompact (K i)) ∧ K 0 = ∅ ∧ (∀ i, K i ⊆ interior (K (i + 1))) ∧
      (⋃ i, K i) = Set.univ ∧
      (∀ i (x : M), x ∉ K i → ¬ IsCompact (closure (connectedComponentIn (K i)ᶜ x))) := by
  haveI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  haveI : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  haveI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨g, hg, hgp, hg1⟩ := proper_continuous_floor (n := n) (M := M)
  have hgnn : ∀ x, 0 ≤ g x := fun x => le_trans zero_le_one (hg1 x)
  let E : CompactExhaustion M := (CompactExhaustion.choice M).shiftr
  have hE0 : E 0 = ∅ := rfl
  refine ⟨fun i => pocketHull (E (2 * i)), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact isCompact_pocketHull hM hg hgp hgnn (E.isCompact (2 * i))
  · show pocketHull (E (2 * 0)) = ∅
    rw [Nat.mul_zero, hE0]
    exact pocketHull_empty hM
  · intro i x hx
    rcases hx with hxE | hxS
    · refine interior_maximal ?_ isOpen_interior (E.subset_interior_succ (2 * i) hxE)
      intro y hy
      exact subset_pocketHull (E.subset (by omega) (interior_subset hy))
    · obtain ⟨T, hT, hxT⟩ := mem_sUnion.mp hxS
      have hT' : ∃ Q ∈ {Q : Set M | IsPocket (E (2 * i)) Q}, closure Q = T := by
        simpa using hT
      obtain ⟨Q, hQ, hQT⟩ := hT'
      have hxQ : x ∈ closure Q := by rw [← hQT] at hxT; exact hxT
      obtain ⟨q, hqE, hQeq, hQc⟩ := hQ
      have hQopen : IsOpen Q :=
        hQeq ▸ (isOpen_compl_iff.mpr (E.isCompact (2 * i)).isClosed).connectedComponentIn
      have hle : 2 * i ≤ 2 * (i + 1) := by omega
      have hsub : Q ⊆ pocketHull (E (2 * (i + 1))) :=
        pocket_subset_pocketHull_of_subset (E.subset hle) ⟨q, hqE, hQeq, hQc⟩
      by_cases hxQ' : x ∈ Q
      · exact interior_maximal hsub hQopen hxQ'
      · have hxE : x ∈ E (2 * i) :=
          pocket_closure_diff_subset (E.isCompact (2 * i)).isClosed ⟨q, hqE, hQeq, hQc⟩ ⟨hxQ, hxQ'⟩
        refine interior_maximal ?_ isOpen_interior (E.subset_interior_succ (2 * i) hxE)
        intro y hy
        exact subset_pocketHull (E.subset (by omega) (interior_subset hy))
  · rw [eq_univ_iff_forall]
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp (E.iUnion_eq ▸ mem_univ x)
    exact mem_iUnion.mpr ⟨2 * i, subset_pocketHull (E.subset (by omega) hi)⟩
  · intro i x hx
    have hxC : x ∈ (E (2 * i))ᶜ := fun hcon => hx (subset_pocketHull hcon)
    have hcomp : connectedComponentIn (pocketHull (E (2 * i)))ᶜ x =
        connectedComponentIn (E (2 * i))ᶜ x := by
      refine le_antisymm ?_ ?_
      · exact IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
          (mem_connectedComponentIn (show x ∈ (pocketHull (E (2 * i)))ᶜ from hx))
          (fun z hz => (compl_subset_compl.mpr subset_pocketHull)
            (connectedComponentIn_subset _ _ hz))
      · exact IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
          (mem_connectedComponentIn hxC)
          (component_subset_compl_hull (E.isCompact (2 * i)).isClosed hx)
    rw [hcomp]
    intro hcomp2
    exact hx (pocket_closure_subset_hull ⟨x, hxC, rfl, hcomp2⟩
      (subset_closure (mem_connectedComponentIn hxC)))

end

end Work.Noncompact.CompressionTube
