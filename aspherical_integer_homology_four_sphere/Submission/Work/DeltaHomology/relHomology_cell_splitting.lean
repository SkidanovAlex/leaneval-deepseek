import Mathlib
import Submission.Work.DeltaHomology.CellData
import Submission.Work.DeltaHomology.mem_skelSet_iff
import Submission.Work.DeltaHomology.relHomology_iso_clopen_sum
import Submission.Work.Homology.SingHomologyClopen
import Submission.Work.Homology.relHomology_homeo
import Submission.Work.Homology.cokernel_biproduct_map_iso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

noncomputable section

/-- Chain complexes of `ℤ`-modules have finite biproducts. -/
noncomputable instance : HasFiniteBiproducts (ChainComplex (ModuleCat ℤ) ℕ) :=
  Abelian.hasFiniteBiproducts (C := ChainComplex (ModuleCat ℤ) ℕ)

variable {K : DeltaCx} {X : TopCat}

/-- The complement of the `k`-skeleton inside the `(k+1)`-skeleton. -/
abbrev skelDiff (R : DeltaRealization K X) (k : ℕ) : Set X :=
  {x : X | x ∈ R.toDeltaSimplexMap.skelSet (k + 1) ∧ x ∉ R.toDeltaSimplexMap.skelSet k}

/-- **A point of the open `k`-cell is the image of an interior point of the standard simplex.**

If `x` lies in `intCell k σ` — the part of the closed cell `cell k σ` outside all lower
skeleta — then it cannot lie on a face of `σ` (that would put it in `skelSet (k-1)`), so it is
`cls k σ y` for an interior point `y` of the standard simplex.  Conversely the image of an
interior point lies in no lower skeleton, by uniqueness of the open simplex through a point
(`R.bij`). -/
theorem mem_intCell_iff_interior (R : DeltaRealization K X) (k : ℕ) (σ : Fin (K.card k))
    (x : X) :
    x ∈ R.toDeltaSimplexMap.intCell k σ ↔
      ∃ y : StdSimplex ℝ (Fin (k + 1)),
        (∀ i, 0 < y.weights i) ∧ R.toDeltaSimplexMap.cls k σ y = x := by
  constructor
  · rintro ⟨hx, hlow⟩
    obtain ⟨y, rfl⟩ := hx
    refine ⟨y, ?_, rfl⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨i, hi⟩ := hcon
    have hi0 : y.weights i = 0 := le_antisymm hi (StdSimplex.weights_nonneg i)
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have hi_eq : i = 0 := Fin.ext (by have := i.isLt; omega)
      rw [hi_eq] at hi0
      have htot := StdSimplex.total_of_fintype y
      rw [Fin.sum_univ_one] at htot
      rw [htot] at hi0
      exact one_ne_zero hi0
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hkpos)
      obtain ⟨y', hy'⟩ := exists_stdSimplex_map_succAbove_eq i y hi0
      have hface := DeltaSimplexMap.cls_face R.toDeltaSimplexMap σ i y'
      have hmem : R.toDeltaSimplexMap.cls (k' + 1) σ y ∈ R.toDeltaSimplexMap.skelSet k' := by
        rw [← hy', ← hface]
        exact R.toDeltaSimplexMap.cell_subset_skelSet _ (Set.mem_range_self y')
      exact hlow k' (Nat.lt_succ_self k') hmem
  · rintro ⟨y, hy, rfl⟩
    refine ⟨Set.mem_range_self y, ?_⟩
    intro j hj hmem
    obtain ⟨p, hp, hpk⟩ := (mem_skelSet_iff R j _).mp hmem
    have h1 : DeltaSimplexMap.real R.toDeltaSimplexMap (⟨k, σ, y, hy⟩ : OpenSimplex K) =
        DeltaSimplexMap.real R.toDeltaSimplexMap p := hp.symm
    have huniq := (R.bij (DeltaSimplexMap.real R.toDeltaSimplexMap p)).unique h1 rfl
    have hdim : p.dim = k := (congrArg OpenSimplex.dim huniq).symm
    omega

/-- A point of the closed cell `cell (k+1) τ` which is not in `skelSet k` lies in the open cell. -/
theorem mem_intCell_of_mem_cell_of_not_mem_skelSet (R : DeltaRealization K X) (k : ℕ)
    (τ : Fin (K.card (k + 1))) {x : X} (hx : x ∈ R.toDeltaSimplexMap.cell (k + 1) τ)
    (hk : x ∉ R.toDeltaSimplexMap.skelSet k) :
    x ∈ R.toDeltaSimplexMap.intCell (k + 1) τ :=
  ⟨hx, fun j hj hmem => hk (R.toDeltaSimplexMap.skelSet_mono (Nat.lt_succ_iff.mp hj) hmem)⟩

/-- The open cells are pairwise disjoint. -/
theorem intCell_disjoint (R : DeltaRealization K X) (k : ℕ) {σ τ : Fin (K.card k)}
    (h : σ ≠ τ) :
    Disjoint (R.toDeltaSimplexMap.intCell k σ) (R.toDeltaSimplexMap.intCell k τ) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨y, hy, hyx⟩ := (mem_intCell_iff_interior R k σ x).mp hx
  obtain ⟨y', hy', hy'x⟩ := (mem_intCell_iff_interior R k τ x).mp hx'
  have h1 : DeltaSimplexMap.real R.toDeltaSimplexMap (⟨k, σ, y, hy⟩ : OpenSimplex K) = x := hyx
  have h2 : DeltaSimplexMap.real R.toDeltaSimplexMap (⟨k, τ, y', hy'⟩ : OpenSimplex K) = x := hy'x
  have huniq : (⟨k, σ, y, hy⟩ : OpenSimplex K) = ⟨k, τ, y', hy'⟩ := (R.bij x).unique h1 h2
  refine h (eq_of_heq ?_)
  exact (OpenSimplex.mk.inj huniq).2.1

/-- The open `(k+1)`-cells cover the complement of the `k`-skeleton in the `(k+1)`-skeleton. -/
theorem exists_intCell_of_mem_skelDiff (R : DeltaRealization K X) (k : ℕ) {x : X}
    (hx : x ∈ skelDiff R k) :
    ∃ σ : Fin (K.card (k + 1)), x ∈ R.toDeltaSimplexMap.intCell (k + 1) σ := by
  obtain ⟨hx1, hx2⟩ := hx
  rw [DeltaSimplexMap.skelSet] at hx1
  simp only [Set.mem_iUnion, Set.mem_range] at hx1
  obtain ⟨j, σ, y, hy⟩ := hx1
  obtain ⟨jv, hjv⟩ := j
  have hj : jv = k + 1 := by
    rcases lt_or_eq_of_le hjv with h | h
    · exfalso
      have hmem : x ∈ R.toDeltaSimplexMap.skelSet k := by
        rw [← hy]
        exact R.toDeltaSimplexMap.cls_mem_skelSet (Nat.lt_succ_iff.mp h) σ y
      exact hx2 hmem
    · exact h
  subst hj
  exact ⟨σ, mem_intCell_of_mem_cell_of_not_mem_skelSet R k σ ⟨y, hy⟩ hx2⟩

/-- Inside the complement of the `k`-skeleton the `(k+1)`-skeleton is the disjoint union of the
open `(k+1)`-cells. -/
theorem skelSet_succ_eq_skelSet_union_intCell (R : DeltaRealization K X) (k : ℕ) :
    R.toDeltaSimplexMap.skelSet (k + 1) =
      R.toDeltaSimplexMap.skelSet k ∪
        ⋃ σ : Fin (K.card (k + 1)), R.toDeltaSimplexMap.intCell (k + 1) σ := by
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hk : x ∈ R.toDeltaSimplexMap.skelSet k
    · exact Or.inl hk
    · exact Or.inr (Set.mem_iUnion.mpr (exists_intCell_of_mem_skelDiff R k ⟨hx, hk⟩))
  · intro x hx
    rcases hx with hk | hx
    · exact R.toDeltaSimplexMap.skelSet_mono (Nat.le_succ k) hk
    · obtain ⟨σ, hx⟩ := Set.mem_iUnion.mp hx
      exact R.toDeltaSimplexMap.intCell_subset_skelSet (k + 1) σ hx

/-- The open `k`-cell meets the set of barycentres of `k`-cells exactly in its own barycentre. -/
theorem intCell_inter_barycenterSet (R : DeltaRealization K X) (k : ℕ) (σ : Fin (K.card k)) :
    R.toDeltaSimplexMap.intCell k σ ∩ R.toDeltaSimplexMap.barycenterSet k =
      {R.toDeltaSimplexMap.cellBarycenter k σ} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hx'⟩
    obtain ⟨τ, rfl⟩ := hx'
    have hmem : R.toDeltaSimplexMap.cellBarycenter k τ ∈ R.toDeltaSimplexMap.intCell k τ :=
      DeltaSimplexMap.cellBarycenter_mem_intCell R k τ
    have hστ : σ = τ := by
      by_contra hne
      exact Set.disjoint_left.mp (intCell_disjoint R k hne) hx hmem
    rw [hστ]
    exact rfl
  · rintro x rfl
    exact ⟨DeltaSimplexMap.cellBarycenter_mem_intCell R k σ,
      R.toDeltaSimplexMap.cellBarycenter_mem_barycenterSet k σ⟩

/-- The open `(k+1)`-cells are contained in the complement of the `k`-skeleton. -/
theorem intCell_subset_skelDiff (R : DeltaRealization K X) (k : ℕ)
    (σ : Fin (K.card (k + 1))) :
    R.toDeltaSimplexMap.intCell (k + 1) σ ⊆ skelDiff R k :=
  fun _ hx => ⟨R.toDeltaSimplexMap.intCell_subset_skelSet (k + 1) σ hx,
    hx.2 k (Nat.lt_succ_self k)⟩

/-- The complement, inside `X^{k+1} ∖ X^k`, of the open cell of `σ` is the trace of the union of
the *other* closed `(k+1)`-cells. -/
theorem skelDiff_inter_intCell_eq (R : DeltaRealization K X) (k : ℕ)
    (σ : Fin (K.card (k + 1))) :
    skelDiff R k ∩ R.toDeltaSimplexMap.intCell (k + 1) σ =
      skelDiff R k ∩
        (⋃ τ : {τ : Fin (K.card (k + 1)) // τ ≠ σ}, R.toDeltaSimplexMap.cell (k + 1) τ.1)ᶜ := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxi⟩
    refine ⟨hx, ?_⟩
    intro hmem
    obtain ⟨τ, hτ⟩ := Set.mem_iUnion.mp hmem
    obtain ⟨z, hz⟩ := hτ
    have hτ' : τ.1 ≠ σ := τ.2
    have hτi : x ∈ R.toDeltaSimplexMap.intCell (k + 1) τ.1 :=
      mem_intCell_of_mem_cell_of_not_mem_skelSet R k τ.1 ⟨z, hz⟩ hx.2
    exact Set.disjoint_left.mp (intCell_disjoint R (k + 1) (Ne.symm hτ')) hxi hτi
  · rintro x ⟨hx, hxi⟩
    refine ⟨hx, ?_⟩
    obtain ⟨σ', hσ'⟩ := exists_intCell_of_mem_skelDiff R k hx
    by_cases h : σ' = σ
    · rwa [h] at hσ'
    · exfalso
      apply hxi
      exact Set.mem_iUnion.mpr ⟨⟨σ', h⟩, R.toDeltaSimplexMap.intCell_subset_cell (k + 1) σ' hσ'⟩

/-- The canonical homeomorphism from the open cell of `σ` (as a subspace of `X^{k+1} ∖ X^k`) to
the open cell of `σ` (as a subspace of `X`). -/
def pieceHomeo (R : DeltaRealization K X) (k : ℕ) (σ : Fin (K.card (k + 1))) :
    (↥{y : ↥(skelDiff R k) | (y : X) ∈ R.toDeltaSimplexMap.intCell (k + 1) σ}) ≃ₜ
      (↥(R.toDeltaSimplexMap.intCell (k + 1) σ)) where
  toFun y := ⟨(y : ↥(skelDiff R k)).1, y.2⟩
  invFun x := ⟨⟨x.1, intCell_subset_skelDiff R k σ x.2⟩, x.2⟩
  left_inv y := rfl
  right_inv x := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

@[simp]
theorem pieceHomeo_coe (R : DeltaRealization K X) (k : ℕ) (σ : Fin (K.card (k + 1)))
    (y : ↥{y : ↥(skelDiff R k) | (y : X) ∈ R.toDeltaSimplexMap.intCell (k + 1) σ}) :
    ((pieceHomeo R k σ y : ↥(R.toDeltaSimplexMap.intCell (k + 1) σ)) : X) = (y : X) := rfl

/-- The canonical homeomorphism of the previous lemma identifies the punctured relative subsets. -/
theorem pieceHomeo_mem_iff (R : DeltaRealization K X) (k : ℕ) (σ : Fin (K.card (k + 1)))
    (y : ↥{y : ↥(skelDiff R k) | (y : X) ∈ R.toDeltaSimplexMap.intCell (k + 1) σ}) :
    ((y : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1) ↔
      ((pieceHomeo R k σ y : ↥(R.toDeltaSimplexMap.intCell (k + 1) σ)) : X) ≠
        R.toDeltaSimplexMap.cellBarycenter (k + 1) σ) := by
  constructor
  · intro hp hcontra
    rw [DeltaSimplexMap.punctSkel] at hp
    exact hp.2 (hcontra ▸ R.toDeltaSimplexMap.cellBarycenter_mem_barycenterSet (k + 1) σ)
  · intro hb
    refine ⟨R.toDeltaSimplexMap.intCell_subset_skelSet (k + 1) σ y.2, ?_⟩
    intro hmem
    obtain ⟨τ, hτ⟩ := hmem
    have hmemτ : (y : X) ∈ R.toDeltaSimplexMap.intCell (k + 1) τ := by
      rw [← hτ]
      exact DeltaSimplexMap.cellBarycenter_mem_intCell R (k + 1) τ
    have hτσ : τ = σ := by
      by_contra hne
      exact Set.disjoint_left.mp (intCell_disjoint R (k + 1) hne) hmemτ y.2
    refine hb ?_
    rw [pieceHomeo_coe, ← hτ, hτσ]
    rfl


/-! ## Additivity of relative homology over a finite disjoint open cover -/

section OpenCover

variable {ι : Type*} [Fintype ι] {Z : TopCat}

/-- Every point of a connected (nonempty) standard simplex maps into exactly one piece of a
finite pairwise disjoint open cover: the preimages of the pieces are pairwise disjoint open sets
covering the simplex, and the unique one containing a chosen basepoint is clopen, hence all of
the simplex. -/
theorem exists_mem_piece (V : ι → Set Z) (hopen : ∀ i, IsOpen (V i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) (hcov : ∀ x : Z, ∃ i, x ∈ V i)
    (n : ℕ) (g : C(StdSimplex ℝ (Fin (n + 1)), Z)) : ∃ i, ∀ z, g z ∈ V i := by
  obtain ⟨i₀, hi₀⟩ := hcov (g (Classical.arbitrary (StdSimplex ℝ (Fin (n + 1)))))
  have hclo : IsClopen (g ⁻¹' V i₀) := by
    refine ⟨?_, (hopen i₀).preimage g.continuous⟩
    rw [← isOpen_compl_iff]
    have hset : (g ⁻¹' V i₀)ᶜ = ⋃ j : {j : ι // j ≠ i₀}, g ⁻¹' V j.1 := by
      ext z
      constructor
      · intro hz
        obtain ⟨i, hi⟩ := hcov (g z)
        exact Set.mem_iUnion.mpr ⟨⟨i, fun h => hz (h ▸ hi)⟩, hi⟩
      · intro hw
        rw [Set.mem_iUnion] at hw
        obtain ⟨j, hj⟩ := hw
        intro hz
        exact Set.disjoint_left.mp (hdisj j.1 i₀ j.2) hj hz
    rw [hset]
    exact isOpen_iUnion (fun i => (hopen i.1).preimage g.continuous)
  rcases isClopen_iff.mp hclo with h | h
  · exfalso
    have hmem : (Classical.arbitrary (StdSimplex ℝ (Fin (n + 1)))) ∈ g ⁻¹' V i₀ := hi₀
    rw [h] at hmem
    exact hmem
  · refine ⟨i₀, fun z => ?_⟩
    have : z ∈ g ⁻¹' V i₀ := by rw [h]; trivial
    exact this

/-- The piece of a finite disjoint open cover in which a singular simplex lies. -/
noncomputable def pieceOf (V : ι → Set Z) (hopen : ∀ i, IsOpen (V i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) (hcov : ∀ x : Z, ∃ i, x ∈ V i)
    (n : ℕ) (s : (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk n))) : ι :=
  Classical.choose (exists_mem_piece V hopen hdisj hcov n (TopCat.toSSetObjEquiv Z _ s))

/-- A singular simplex lies in the piece selected by `pieceOf`. -/
theorem pieceOf_mem (V : ι → Set Z) (hopen : ∀ i, IsOpen (V i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) (hcov : ∀ x : Z, ∃ i, x ∈ V i)
    (n : ℕ) (s : (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk n))) :
    ∀ z, TopCat.toSSetObjEquiv Z (Opposite.op (SimplexCategory.mk n)) s z
      ∈ V (pieceOf V hopen hdisj hcov n s) :=
  Classical.choose_spec
    (exists_mem_piece V hopen hdisj hcov n (TopCat.toSSetObjEquiv Z _ s))

/-- The piece in which a simplex lies is unique. -/
theorem eq_pieceOf (V : ι → Set Z) (hopen : ∀ i, IsOpen (V i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) (hcov : ∀ x : Z, ∃ i, x ∈ V i)
    (n : ℕ) (s : (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk n)))
    {i : ι} (hi : ∀ z, TopCat.toSSetObjEquiv Z (Opposite.op (SimplexCategory.mk n)) s z ∈ V i) :
    i = pieceOf V hopen hdisj hcov n s := by
  by_contra hne
  exact Set.disjoint_left.mp
    (hdisj i (pieceOf V hopen hdisj hcov n s) hne)
    (hi (Classical.arbitrary (StdSimplex ℝ (Fin (n + 1)))))
    (pieceOf_mem V hopen hdisj hcov n s (Classical.arbitrary (StdSimplex ℝ (Fin (n + 1)))))

end OpenCover


/-! ## The chain-level splitting over a finite disjoint open cover -/

theorem sChainMap_comp (R : ModuleCat ℤ) {X Y Z' : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z') :
    sChainMap R (f ≫ g) = sChainMap R f ≫ sChainMap R g :=
  singChainMap_comp R f g

theorem sChainMap_id (R : ModuleCat ℤ) (X : TopCat) : sChainMap R (𝟙 X) = 𝟙 (sChain R X) :=
  singChainMap_id R X

/-- A homeomorphism of spaces induces an isomorphism of singular chain complexes (in the
`SSet.chainComplex` presentation). -/
noncomputable def chainIsoS (R : ModuleCat ℤ) {α β : Type} [TopologicalSpace α]
    [TopologicalSpace β] (e : α ≃ₜ β) : sChain R (TopCat.of α) ≅ sChain R (TopCat.of β) where
  hom := sChainMap R (homeomorphTopCatHom e)
  inv := sChainMap R (homeomorphTopCatInv e)
  hom_inv_id := by rw [← sChainMap_comp, homeomorphTopCatHom_comp_inv, sChainMap_id]
  inv_hom_id := by rw [← sChainMap_comp, homeomorphTopCatInv_comp_hom, sChainMap_id]

section Criterion

/-- A map out of a finite biproduct `⨁ i, K i` is an isomorphism as soon as it has a two-sided
matrix inverse: maps `g i : Y ⟶ K i` with `f i ≫ g i = 𝟙`, `f i ≫ g j = 0` for `i ≠ j` and
`∑ i, g i ≫ f i = 𝟙 Y`.  The inverse is then `biproduct.lift g`. -/
theorem biproduct_desc_isIso_of_components {C : Type*} [Category* C] [Preadditive C]
    {ι : Type} [Fintype ι] {K : ι → C} [HasBiproduct K] {Y : C}
    (f : ∀ i, K i ⟶ Y) (g : ∀ i, Y ⟶ K i)
    (h1 : ∀ i, f i ≫ g i = 𝟙 (K i)) (h2 : ∀ i j, i ≠ j → f i ≫ g j = 0)
    (h3 : ∑ i, g i ≫ f i = 𝟙 Y) : IsIso (biproduct.desc f) := by
  classical
  have hlift : biproduct.lift g = ∑ i, g i ≫ biproduct.ι K i := by
    rw [← Category.comp_id (biproduct.lift g), ← biproduct.total (f := K), Preadditive.comp_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Category.assoc, biproduct.lift_π]
  have hinv : biproduct.lift g ≫ biproduct.desc f = 𝟙 Y := by
    rw [hlift, Preadditive.sum_comp]
    rw [show (∑ j, (g j ≫ biproduct.ι K j) ≫ biproduct.desc f) = ∑ j, g j ≫ f j from by
      apply Finset.sum_congr rfl
      intro j _
      rw [Category.assoc, biproduct.ι_desc]]
    exact h3
  have hother : biproduct.desc f ≫ biproduct.lift g = 𝟙 (⨁ K) := by
    rw [hlift, Preadditive.comp_sum]
    apply biproduct.hom_ext'
    intro i
    rw [Preadditive.comp_sum]
    have hterm : ∀ j, biproduct.ι K i ≫ (biproduct.desc f ≫ g j ≫ biproduct.ι K j)
        = if j = i then biproduct.ι K i else 0 := by
      intro j
      rw [← Category.assoc, biproduct.ι_desc]
      by_cases hij : j = i
      · subst hij
        rw [← Category.assoc, h1 j, Category.id_comp, ite_eq_left rfl]
      · rw [← Category.assoc, h2 i j (Ne.symm hij), zero_comp, ite_eq_right hij]
    rw [Finset.sum_congr rfl fun j _ => hterm j, Category.comp_id,
      Finset.sum_ite_eq' Finset.univ i fun _ => biproduct.ι K i]
    simp
  exact IsIso.mk ⟨biproduct.lift g, hother, hinv⟩

end Criterion

section ChainSplit

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Z : TopCat}

/-- The pointwise biproduct of a family of chain complexes agrees, in each degree, with the
biproduct of the components. -/
noncomputable def biprodXeval {J : Type} [Fintype J] (K : J → ChainComplex (ModuleCat ℤ) ℕ)
    (n : ℕ) : (⨁ K).X n ≅ ⨁ (fun j => (K j).X n) :=
  Functor.mapBiproduct (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n) K

/-- A morphism of chain complexes out of a finite biproduct of complexes is an isomorphism as
soon as it is an isomorphism in every degree. -/
theorem isIso_biproduct_desc_of_isIso_components {J : Type} [Fintype J]
    (K : J → ChainComplex (ModuleCat ℤ) ℕ) {Y : ChainComplex (ModuleCat ℤ) ℕ}
    (f : ∀ j, K j ⟶ Y) (h : ∀ n, IsIso (biproduct.desc fun j => (f j).f n)) :
    IsIso (biproduct.desc f) := by
  have hcomp : ∀ n, IsIso ((biproduct.desc f).f n) := by
    intro n
    have hPres : PreservesBiproduct K
        (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n) :=
      preservesBiproduct_of_preservesCoproduct _
    haveI := hPres
    haveI hI : IsIso (biproduct.desc fun j => (f j).f n) := h n
    have hδ : (biprodXeval K n).inv ≫ (biproduct.desc f).f n
        = biproduct.desc (fun j => (f j).f n) :=
      biproduct.mapBiproduct_inv_map_desc
        (F := HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n) (f := K) f
    exact IsIso.of_isIso_fac_left hδ
  haveI (n : ℕ) : IsIso ((biproduct.desc f).f n) := hcomp n
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Lifting a simplex of a subspace along the inclusion and then descending again gives the
original simplex (with an arbitrary choice of membership proof). -/
theorem liftSimplex_incl {X : TopCat} {A : Set X} {n : ℕ}
    (v : (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op (SimplexCategory.mk n)))
    (h : ∀ z, TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))
      ((TopCat.toSSet.map (incl A)).app (Opposite.op (SimplexCategory.mk n)) v) z ∈ A) :
    liftSimplex ((TopCat.toSSet.map (incl A)).app (Opposite.op (SimplexCategory.mk n)) v) h
      = v := by
  apply (TopCat.toSSetObjEquiv (TopCat.of A) (Opposite.op (SimplexCategory.mk n))).injective
  rw [toSSetObjEquiv_liftSimplex]
  rfl

/-- The degree-`n` component of the restriction of the singular chains of `Z` to the piece
`V i`: a simplex is sent to its lift in `V i` if its side is `i`, and to `0` otherwise. -/
noncomputable def restComp (V : ι → Set Z) (hopen : ∀ i, IsOpen (V i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) (hcov : ∀ x : Z, ∃ i, x ∈ V i)
    (i : ι) (n : ℕ) :
    (sChain ZMod Z).X n ⟶ (sChain ZMod (TopCat.of (V i))).X n :=
  Sigma.desc (fun s => if hs : pieceOf V hopen hdisj hcov n s = i
    then SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of (V i)))
      (liftSimplex s (hs ▸ pieceOf_mem V hopen hdisj hcov n s))
    else 0)

theorem iota_restComp (V : ι → Set Z) (hopen : ∀ i, IsOpen (V i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) (hcov : ∀ x : Z, ∃ i, x ∈ V i)
    (i : ι) (n : ℕ) (s : (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk n))) :
    SSet.ιChainComplex (TopCat.toSSet.obj Z) s ≫ restComp V hopen hdisj hcov i n
      = if hs : pieceOf V hopen hdisj hcov n s = i
        then SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of (V i)))
          (liftSimplex s (hs ▸ pieceOf_mem V hopen hdisj hcov n s))
        else 0 :=
  Sigma.ι_comp_desc _ _

/-- The restriction to the piece `V i` is a left inverse of the inclusion of `V i`. -/
theorem restComp_incl (V : ι → Set Z) (hopen : ∀ i, IsOpen (V i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) (hcov : ∀ x : Z, ∃ i, x ∈ V i)
    (i : ι) (n : ℕ) :
    (sChainMap ZMod (incl (V i))).f n ≫ restComp V hopen hdisj hcov i n
      = 𝟙 ((sChain ZMod (TopCat.of (V i))).X n) := by
  apply SSet.chainComplex_hom_ext
  intro v
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  have hpiece : pieceOf V hopen hdisj hcov n
      ((TopCat.toSSet.map (incl (V i))).app (Opposite.op (SimplexCategory.mk n)) v) = i :=
    (eq_pieceOf V hopen hdisj hcov n _
      (fun z => (TopCat.toSSetObjEquiv (TopCat.of (V i)) (Opposite.op (SimplexCategory.mk n))
        v z).2)).symm
  rw [iota_restComp, dif_pos hpiece, liftSimplex_incl, Category.comp_id]

/-- The restriction to a different piece `V j` kills the simplices of `V i`. -/
theorem restComp_incl_ne (V : ι → Set Z) (hopen : ∀ i, IsOpen (V i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) (hcov : ∀ x : Z, ∃ i, x ∈ V i)
    {i j : ι} (hij : i ≠ j) (n : ℕ) :
    (sChainMap ZMod (incl (V i))).f n ≫ restComp V hopen hdisj hcov j n = 0 := by
  apply SSet.chainComplex_hom_ext
  intro v
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, iota_restComp]
  have hpiece : pieceOf V hopen hdisj hcov n
      ((TopCat.toSSet.map (incl (V i))).app (Opposite.op (SimplexCategory.mk n)) v) = i :=
    (eq_pieceOf V hopen hdisj hcov n _
      (fun z => (TopCat.toSSetObjEquiv (TopCat.of (V i)) (Opposite.op (SimplexCategory.mk n))
        v z).2)).symm
  rw [dif_neg (fun h => hij (hpiece.symm.trans h)), comp_zero]

/-- The sum of the restrictions is the identity. -/
theorem sum_restComp (V : ι → Set Z) (hopen : ∀ i, IsOpen (V i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) (hcov : ∀ x : Z, ∃ i, x ∈ V i)
    (n : ℕ) :
    ∑ i, restComp V hopen hdisj hcov i n ≫ (sChainMap ZMod (incl (V i))).f n
      = 𝟙 ((sChain ZMod Z).X n) := by
  apply SSet.chainComplex_hom_ext
  intro s
  rw [Preadditive.comp_sum]
  have hterm : ∀ i, SSet.ιChainComplex (TopCat.toSSet.obj Z) s
        ≫ (restComp V hopen hdisj hcov i n ≫ (sChainMap ZMod (incl (V i))).f n)
      = if pieceOf V hopen hdisj hcov n s = i
        then SSet.ιChainComplex (TopCat.toSSet.obj Z) s else 0 := by
    intro i
    rw [← Category.assoc, iota_restComp]
    by_cases hi : pieceOf V hopen hdisj hcov n s = i
    · rw [dif_pos hi, if_pos hi, SSet.ι_chainComplexMap_f, toSSet_map_incl_liftSimplex]
    · rw [dif_neg hi, if_neg hi, zero_comp]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Category.comp_id,
    Finset.sum_ite_eq Finset.univ (pieceOf V hopen hdisj hcov n s)
      (fun _ => SSet.ιChainComplex (TopCat.toSSet.obj Z) s)]
  simp

/-- The sum of the inclusions of the pieces of the cover. -/
noncomputable def merge (V : ι → Set Z) :
    (⨁ (fun i : ι => sChain ZMod (TopCat.of (V i)))) ⟶ sChain ZMod Z :=
  biproduct.desc (fun i => sChainMap ZMod (incl (V i)))

/-- **The sum of the inclusions of the pieces of a finite disjoint open cover is an
isomorphism.** -/
theorem isIso_merge (V : ι → Set Z) (hopen : ∀ i, IsOpen (V i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) (hcov : ∀ x : Z, ∃ i, x ∈ V i) :
    IsIso (merge V) := by
  apply isIso_biproduct_desc_of_isIso_components
    (fun i => sChain ZMod (TopCat.of (V i)))
    (fun i => sChainMap ZMod (incl (V i)))
  intro n
  exact biproduct_desc_isIso_of_components (fun i => (sChainMap ZMod (incl (V i))).f n)
    (fun i => restComp V hopen hdisj hcov i n)
    (fun i => restComp_incl V hopen hdisj hcov i n)
    (fun i j hij => restComp_incl_ne V hopen hdisj hcov hij n)
    (sum_restComp V hopen hdisj hcov n)

end ChainSplit

/-! ## The trace of a cover on a subspace -/

section Relative

variable {ι : Type} [Fintype ι] {Z : TopCat}

/-- The trace of a set `U` on a subspace `A`. -/
def traceSet (A U : Set Z) : Set ↥A := {a : ↥A | (a : Z) ∈ U}

/-- The trace of `U` on `A`, viewed inside the space `A`, is canonically homeomorphic to
the trace of `A` on `U`, viewed inside the space `U`. -/
def coverHomeo (A U : Set Z) :
    (↥(traceSet A U)) ≃ₜ (↥{x : ↥U | (x : Z) ∈ A}) where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  left_inv x := rfl
  right_inv y := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

/-- The canonical map from the trace of `U` on `A` (viewed inside the space `A`) to `U`, i.e.
the composite `{x ∈ A : x ∈ U} ≅ {x ∈ U : x ∈ A} ↪ U`. -/
def coverProj (A U : Set Z) :
    TopCat.of (traceSet A U) ⟶ TopCat.of U :=
  homeomorphTopCatHom (coverHomeo A U) ≫ incl {x : ↥U | (x : Z) ∈ A}

/-- The inclusion of the trace of `U` on `A` into `A`, followed by the inclusion of `A` into `Z`,
is the same as `coverProj` followed by the inclusion of `U` into `Z`. -/
theorem incl_coverProj (A U : Set Z) :
    incl (traceSet A U) ≫ incl A = coverProj A U ≫ incl U := by
  apply TopCat.hom_ext
  ext x
  rfl

end Relative


section Assembly

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Z : TopCat}

/-- **Additivity of relative homology over a finite disjoint open cover.** -/
theorem relHomology_openCover_split_aux (Z : TopCat)
    (V : ι → Set Z) (hopen : ∀ i, IsOpen (V i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (V i) (V j)) (hcov : ∀ x : Z, ∃ i, x ∈ V i)
    (A : Set Z) (m : ℕ) :
    Nonempty (relHomology ZMod m Z A ≅
      ⨁ (fun i => relHomology ZMod m (TopCat.of (V i)) {x : ↥(V i) | (x : Z) ∈ A})) := by
  classical
  -- ## the two chain-level splittings
  let DX : (⨁ fun i => sChain ZMod (TopCat.of (V i))) ⟶ sChain ZMod Z :=
    biproduct.desc (fun i => sChainMap ZMod (incl (V i)))
  haveI hDX : IsIso DX := isIso_merge V hopen hdisj hcov
  have hopenA : ∀ i, IsOpen (traceSet A (V i)) :=
    fun i => (hopen i).preimage continuous_subtype_val
  have hdisjA : ∀ i j, i ≠ j → Disjoint (traceSet A (V i)) (traceSet A (V j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro a hai haj
    exact Set.disjoint_left.mp (hdisj i j hij) hai haj
  have hcovA : ∀ a : ↥A, ∃ i, a ∈ traceSet A (V i) := by
    intro a
    obtain ⟨i, hi⟩ := hcov (a : Z)
    exact ⟨i, hi⟩
  let DA : (⨁ fun i => sChain ZMod (TopCat.of (traceSet A (V i))))
      ⟶ sChain ZMod (TopCat.of A) :=
    biproduct.desc (fun i => sChainMap ZMod (incl (X := TopCat.of A) (traceSet A (V i))))
  haveI hDA : IsIso DA := isIso_merge (Z := TopCat.of A) (fun i => traceSet A (V i)) hopenA hdisjA hcovA
  -- ## the map between the two splittings
  let sw : ∀ i, sChain ZMod (TopCat.of (traceSet A (V i)))
      ⟶ sChain ZMod (TopCat.of (V i)) := fun i => sChainMap ZMod (coverProj A (V i))
  have hfac : ∀ i, sChainMap ZMod (incl (X := TopCat.of A) (traceSet A (V i)))
        ≫ sChainMap ZMod (incl A)
      = sw i ≫ sChainMap ZMod (incl (V i)) := by
    intro i
    dsimp only [sw]
    rw [← sChainMap_comp, ← sChainMap_comp, incl_coverProj]
  -- ## the compatibility square
  have hsquare : sChainMap ZMod (incl A) ≫ inv DX = inv DA ≫ biproduct.map sw := by
    have key : DA ≫ sChainMap ZMod (incl A) ≫ inv DX = biproduct.map sw := by
      apply biproduct.hom_ext'
      intro i
      have h1 : biproduct.ι (fun i => sChain ZMod (TopCat.of (traceSet A (V i)))) i ≫ DA
          = sChainMap ZMod (incl (X := TopCat.of A) (traceSet A (V i))) := by
        dsimp only [DA]; exact biproduct.ι_desc _ _
      have h2 : biproduct.ι (fun i => sChain ZMod (TopCat.of (V i))) i ≫ DX
          = sChainMap ZMod (incl (V i)) := by
        dsimp only [DX]; exact biproduct.ι_desc _ _
      have h2' : sChainMap ZMod (incl (V i)) ≫ inv DX
          = biproduct.ι (fun b => sChain ZMod (TopCat.of (V b))) i := by
        rw [← h2, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      rw [biproduct.ι_map, ← Category.assoc, h1, ← Category.assoc, hfac i, Category.assoc, h2']
    rw [← key, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  -- ## the chain-level isomorphism on relative chains
  have hcok : relChain ZMod Z A ≅ cokernel (biproduct.map sw) :=
    cokernel.mapIso (sChainMap ZMod (incl A)) (biproduct.map sw) (asIso DA).symm
      (asIso DX).symm hsquare
  -- ## identifying the pieces
  have hsw : ∀ i, sw i = (chainIsoS ZMod (coverHomeo A (V i))).hom
      ≫ sChainMap ZMod (incl (X := TopCat.of (V i)) {x : ↥(V i) | (x : Z) ∈ A}) := by
    intro i
    dsimp only [sw, chainIsoS, coverProj]
    rw [← sChainMap_comp]
  have hpieces : ∀ i, cokernel (sw i)
      ≅ relChain ZMod (TopCat.of (V i)) {x : ↥(V i) | (x : Z) ∈ A} := by
    intro i
    refine cokernel.mapIso (sw i) (sChainMap ZMod (incl (X := TopCat.of (V i))
      {x : ↥(V i) | (x : Z) ∈ A})) (chainIsoS ZMod (coverHomeo A (V i))) (Iso.refl _) ?_
    rw [Iso.refl_hom, Category.comp_id]
    exact hsw i
  have hchain : relChain ZMod Z A ≅
      ⨁ (fun i => relChain ZMod (TopCat.of (V i)) {x : ↥(V i) | (x : Z) ∈ A}) :=
    hcok ≪≫ (cokernel_biproduct_map_iso
        (fun i => sChain ZMod (TopCat.of (traceSet A (V i))))
        (fun i => sChain ZMod (TopCat.of (V i))) sw).some
      ≪≫ biproduct.mapIso (fun i => hpieces i)
  -- ## passing to homology
  refine ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) m).mapIso
    hchain ≪≫ ?_⟩
  exact Functor.mapBiproduct
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) m)
    (fun i => relChain ZMod (TopCat.of (V i)) {x : ↥(V i) | (x : Z) ∈ A})

end Assembly

/-- **The relative homology over the open `(k+1)`-cells splits as a direct sum.**  Inside
`Y := X^{k+1} ∖ X^k` the open cells `χ.intCell (k+1) σ` are pairwise disjoint and each is
clopen in `Y` (it is the complement in `Y` of the finite union of the other closed cells,
which is closed), so relative homology is additive over them. -/
theorem relHomology_cell_splitting {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (k m : ℕ) :
    Nonempty (relHomology ZMod m
        (TopCat.of {x : X | x ∈ R.toDeltaSimplexMap.skelSet (k + 1) ∧
          x ∉ R.toDeltaSimplexMap.skelSet k})
        {x : ↥{x : X | x ∈ R.toDeltaSimplexMap.skelSet (k + 1) ∧
          x ∉ R.toDeltaSimplexMap.skelSet k} |
          (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)} ≅
      (∐ fun σ : Fin (K.card (k + 1)) => relHomology ZMod m
        (TopCat.of (R.toDeltaSimplexMap.intCell (k + 1) σ))
        {x : ↥(R.toDeltaSimplexMap.intCell (k + 1) σ) |
          (x : X) ≠ R.toDeltaSimplexMap.cellBarycenter (k + 1) σ})) := by
  classical
  change Nonempty (relHomology ZMod m (TopCat.of (skelDiff R k))
      {x : ↥(skelDiff R k) | (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)} ≅
    (∐ fun σ : Fin (K.card (k + 1)) => relHomology ZMod m
      (TopCat.of (R.toDeltaSimplexMap.intCell (k + 1) σ))
      {x : ↥(R.toDeltaSimplexMap.intCell (k + 1) σ) |
        (x : X) ≠ R.toDeltaSimplexMap.cellBarycenter (k + 1) σ}))
  have hcl : ∀ σ : Fin (K.card (k + 1)),
      IsClosed (⋃ τ : {τ : Fin (K.card (k + 1)) // τ ≠ σ},
        R.toDeltaSimplexMap.cell (k + 1) τ.1) := by
    intro σ
    letI : T2Space X := R.t2
    exact isClosed_iUnion_of_finite
      (fun τ => (isCompact_range (R.toDeltaSimplexMap.cls (k + 1) τ.1).continuous).isClosed)
  have hopen : ∀ σ : Fin (K.card (k + 1)),
      IsOpen {y : ↥(skelDiff R k) | (y : X) ∈ R.toDeltaSimplexMap.intCell (k + 1) σ} := by
    intro σ
    have hset : {y : ↥(skelDiff R k) | (y : X) ∈ R.toDeltaSimplexMap.intCell (k + 1) σ} =
        (fun y : ↥(skelDiff R k) => (y : X)) ⁻¹'
          (⋃ τ : {τ : Fin (K.card (k + 1)) // τ ≠ σ},
            R.toDeltaSimplexMap.cell (k + 1) τ.1)ᶜ := by
      ext y
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have hmem : (y : X) ∈ skelDiff R k ∩
            (⋃ τ : {τ : Fin (K.card (k + 1)) // τ ≠ σ},
              R.toDeltaSimplexMap.cell (k + 1) τ.1)ᶜ := by
          rw [← skelDiff_inter_intCell_eq R k σ]
          exact ⟨y.2, h⟩
        exact hmem.2
      · have hmem : (y : X) ∈ skelDiff R k ∩ R.toDeltaSimplexMap.intCell (k + 1) σ := by
          rw [skelDiff_inter_intCell_eq R k σ]
          exact ⟨y.2, h⟩
        exact hmem.2
    rw [hset]
    exact (hcl σ).isOpen_compl.preimage continuous_subtype_val
  have hdisj : ∀ σ τ : Fin (K.card (k + 1)), σ ≠ τ →
      Disjoint {y : ↥(skelDiff R k) | (y : X) ∈ R.toDeltaSimplexMap.intCell (k + 1) σ}
        {y : ↥(skelDiff R k) | (y : X) ∈ R.toDeltaSimplexMap.intCell (k + 1) τ} := by
    intro σ τ hne
    rw [Set.disjoint_left]
    intro y hy hy'
    exact Set.disjoint_left.mp (intCell_disjoint R (k + 1) hne) hy hy'
  have hcov : ∀ y : ↥(skelDiff R k),
      ∃ σ : Fin (K.card (k + 1)), (y : X) ∈ R.toDeltaSimplexMap.intCell (k + 1) σ :=
    fun y => exists_intCell_of_mem_skelDiff R k y.2
  have hpiece : ∀ σ : Fin (K.card (k + 1)),
      Nonempty (relHomology ZMod m
          (TopCat.of {y : ↥(skelDiff R k) | (y : X) ∈ R.toDeltaSimplexMap.intCell (k + 1) σ})
          {x : ↥{y : ↥(skelDiff R k) | (y : X) ∈ R.toDeltaSimplexMap.intCell (k + 1) σ} |
            (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)} ≅
        relHomology ZMod m (TopCat.of (R.toDeltaSimplexMap.intCell (k + 1) σ))
          {x : ↥(R.toDeltaSimplexMap.intCell (k + 1) σ) |
            (x : X) ≠ R.toDeltaSimplexMap.cellBarycenter (k + 1) σ}) := by
    intro σ
    refine relHomology_homeo (pieceHomeo R k σ) _ _ ?_ m
    intro y
    simpa only [Set.mem_setOf_eq] using pieceHomeo_mem_iff R k σ y
  have e1 : Nonempty (relHomology ZMod m (TopCat.of (skelDiff R k))
        {x : ↥(skelDiff R k) | (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)} ≅
      ⨁ (fun σ : Fin (K.card (k + 1)) => relHomology ZMod m
        (TopCat.of {y : ↥(skelDiff R k) | (y : X) ∈ R.toDeltaSimplexMap.intCell (k + 1) σ})
        {x : ↥{y : ↥(skelDiff R k) | (y : X) ∈ R.toDeltaSimplexMap.intCell (k + 1) σ} |
          (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)})) :=
    relHomology_openCover_split_aux (TopCat.of (skelDiff R k))
      (fun σ : Fin (K.card (k + 1)) =>
        {y : ↥(skelDiff R k) | (y : X) ∈ R.toDeltaSimplexMap.intCell (k + 1) σ})
      hopen hdisj hcov
      {y : ↥(skelDiff R k) | (y : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)} m
  refine ⟨e1.some ≪≫ biproduct.mapIso (fun σ => (hpiece σ).some)
    ≪≫ biproduct.isoCoproduct _⟩

end

end Work.DeltaHomology
