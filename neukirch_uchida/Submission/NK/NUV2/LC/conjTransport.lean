import Mathlib
import Submission.NK.NUV2.LC.LeafInputs

/-!
# Conjugation transport for the profinite cohomology `H²(·, Z/p)`

The colimit defining `NK.BrauerHasse.H2Profinite p V` is taken over the finite Galois levels
`L` of `K'/K`; an element `σ ∈ Gal(K'/K)` permutes these levels (`L ↦ σ • L`, the *conjugate
level* `conjLevel σ L`) and matches the level groups of `V` with those of `σVσ⁻¹`
(`conjSub V σ`), so that the cohomologies are isomorphic.  In particular non-triviality is
transported, which is the leaf `NK.NUV2.LC.ConjTransport` of the Neukirch containment.

This is pure profinite-cohomology bookkeeping — no arithmetic enters.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open NK.BrauerHasse

namespace NK.NUV2.LC

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## §1. The conjugate subgroup and the conjugate level -/

/-- The conjugate `σVσ⁻¹` of a subgroup `V ≤ Gal(K'/K)`. -/
abbrev conjSub (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K)) : Subgroup Gal(K'/K) :=
  V.map (MulAut.conj σ)

/-- The conjugation homomorphism, computed on elements (coercion form). -/
@[simp]
lemma conj_apply_apply (σ x : Gal(K'/K)) :
    (↑(MulAut.conj σ) : Gal(K'/K) →* Gal(K'/K)) x = σ * x * σ⁻¹ := by
  show (MulAut.conj σ) x = σ * x * σ⁻¹
  rw [MulAut.conj_apply]

/-- The conjugation homomorphism, computed on elements (`toMonoidHom` form). -/
@[simp]
lemma toMonoidHom_conj_apply (σ x : Gal(K'/K)) :
    (MulAut.conj σ).toMonoidHom x = σ * x * σ⁻¹ := by
  show (MulAut.conj σ) x = σ * x * σ⁻¹
  rw [MulAut.conj_apply]

/-- Membership in the conjugate subgroup: `x ∈ σVσ⁻¹ ↔ σ⁻¹xσ ∈ V`. -/
lemma mem_conjSub {V : Subgroup Gal(K'/K)} {σ x : Gal(K'/K)} :
    x ∈ conjSub V σ ↔ σ⁻¹ * x * σ ∈ V := by
  constructor
  · intro hx
    obtain ⟨v, hv, hvx⟩ := Subgroup.mem_map.mp hx
    have hvv : σ⁻¹ * (↑(MulAut.conj σ) : Gal(K'/K) →* Gal(K'/K)) v * σ = v := by
      rw [conj_apply_apply]
      group
    rw [← hvx, hvv]
    exact hv
  · intro hx
    refine Subgroup.mem_map.mpr ⟨σ⁻¹ * x * σ, hx, ?_⟩
    rw [conj_apply_apply]
    group

/-- Conjugating twice by `σ` and `σ⁻¹` returns the original subgroup. -/
lemma conjSub_conjSub (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K)) :
    conjSub (conjSub V σ) σ⁻¹ = V := by
  ext x
  rw [mem_conjSub, mem_conjSub]
  have h : σ⁻¹ * ((σ⁻¹)⁻¹ * x * σ⁻¹) * σ = x := by group
  rw [h]

/-- The conjugate `σ • L` of a finite Galois intermediate field `L ≤ K'`, i.e. the image of `L`
under the automorphism `σ`. -/
noncomputable def conjLevel (σ : Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    FiniteGaloisIntermediateField K K' where
  toIntermediateField := L.toIntermediateField.map σ.toAlgHom
  finiteDimensional := IntermediateField.finiteDimensional_map σ.toAlgHom
  isGalois := IsGalois.of_algEquiv (IntermediateField.equivMap L.toIntermediateField σ.toAlgHom)

@[simp]
lemma conjLevel_toIntermediateField (σ : Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    (conjLevel σ L).toIntermediateField = L.toIntermediateField.map σ.toAlgHom := rfl

lemma mem_conjLevel {σ : Gal(K'/K)} {L : FiniteGaloisIntermediateField K K'} {x : K'} :
    x ∈ (conjLevel σ L).toIntermediateField ↔ ∃ y ∈ L.toIntermediateField, σ y = x := by
  rw [conjLevel_toIntermediateField]
  exact IntermediateField.mem_map (S := L.toIntermediateField) (f := σ.toAlgHom)

/-- `conjLevel σ` is monotone. -/
lemma conjLevel_le_conjLevel (σ : Gal(K'/K)) {L L' : FiniteGaloisIntermediateField K K'}
    (h : L ≤ L') : conjLevel σ L ≤ conjLevel σ L' := by
  rw [FiniteGaloisIntermediateField.le_iff] at h ⊢
  exact IntermediateField.map_mono σ.toAlgHom h

/-- **The fixing subgroup of a conjugate level** is the conjugate of the fixing subgroup. -/
lemma fixingSubgroup_conjLevel (σ : Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    (conjLevel σ L).fixingSubgroup = L.fixingSubgroup.map (MulAut.conj σ).toMonoidHom := by
  ext τ
  rw [IntermediateField.mem_fixingSubgroup_iff, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨σ⁻¹ * τ * σ, ?_, ?_⟩
    · rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have h1 : τ (σ y) = σ y :=
        h (σ y) (by rw [conjLevel, IntermediateField.mem_map]; exact ⟨y, hy, rfl⟩)
      show (σ⁻¹ * τ * σ) y = y
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h1]
      simp
    · show (MulAut.conj σ) (σ⁻¹ * τ * σ) = τ
      rw [MulAut.conj_apply]
      group
  · rintro ⟨ρ, hρ, rfl⟩ x ⟨y, hy, rfl⟩
    have hρy : ρ y = y := (IntermediateField.mem_fixingSubgroup_iff L ρ).mp hρ y hy
    show (MulEquiv.toMonoidHom (MulAut.conj σ)) ρ (σ y) = σ y
    show (MulAut.conj σ ρ) (σ y) = σ y
    show (σ * ρ * σ⁻¹) (σ y) = σ y
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, show σ⁻¹ (σ y) = y from by simp, hρy]

/-- Conjugating a level by `σ` and then by `σ⁻¹` returns it. -/
lemma conjLevel_conjLevel (σ : Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    conjLevel σ⁻¹ (conjLevel σ L) = L := by
  apply FiniteGaloisIntermediateField.val_injective
  show (conjLevel σ⁻¹ (conjLevel σ L)).toIntermediateField = L.toIntermediateField
  have hcomp : (σ⁻¹).toAlgHom.comp σ.toAlgHom = AlgHom.id K K' := by
    ext x; simp
  rw [conjLevel_toIntermediateField, conjLevel_toIntermediateField, IntermediateField.map_map,
    hcomp, IntermediateField.map_id]

/-- A level is contained in the level one obtains by conjugating with `σ` and back with `σ⁻¹`. -/
lemma le_conjLevel_conjLevel (σ : Gal(K'/K)) (L : FiniteGaloisIntermediateField K K') :
    L ≤ conjLevel σ⁻¹ (conjLevel σ L) := by
  intro x hx
  rw [mem_conjLevel]
  exact ⟨σ x, (mem_conjLevel).mpr ⟨x, hx, rfl⟩, by simp⟩

/-! ## §2. The conjugation isomorphisms of the level groups -/

/-- The conjugation isomorphism `V ≃* σVσ⁻¹` of subgroups of `Gal(K'/K)`. -/
noncomputable def conjH (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K)) :
    ↥V ≃* ↥(conjSub V σ) :=
  MulEquiv.subgroupMap (MulAut.conj σ) V

@[simp]
lemma coe_conjH (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K)) (x : ↥V) :
    (↑(conjH V σ x) : Gal(K'/K)) = σ * ↑x * σ⁻¹ := by
  rw [conjH, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]

/-- The inverse conjugation on subgroups is the conjugation by `σ⁻¹`. -/
lemma coe_symm_conjH (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K)) (x : ↥(conjSub V σ)) :
    (↑((conjH V σ).symm x) : Gal(K'/K)) = σ⁻¹ * ↑x * σ := by
  have h := congrArg (Subtype.val) (MulEquiv.apply_symm_apply (conjH V σ) x)
  simp only [coe_conjH] at h
  rw [← h]
  group

@[simp]
lemma conjH_symm_apply_apply (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K)) (x : ↥V) :
    (conjH V σ).symm (conjH V σ x) = x :=
  MulEquiv.symm_apply_apply _ _

/-- The conjugation isomorphism of subgroups maps `A ∩ V` onto `σAσ⁻¹ ∩ σVσ⁻¹`. -/
lemma map_subgroupOf_conjH (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K))
    (A : Subgroup Gal(K'/K)) :
    (A.subgroupOf V).map (conjH V σ) = (A.map (MulAut.conj σ).toMonoidHom).subgroupOf (conjSub V σ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hyA, hxy⟩ := Subgroup.mem_map.mp hx
    have hyA' : (↑y : Gal(K'/K)) ∈ A := Subgroup.mem_subgroupOf.mp hyA
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨↑y, hyA', ?_⟩)
    rw [← congrArg Subtype.val hxy]
    show (↑(MulAut.conj σ) : Gal(K'/K) →* Gal(K'/K)) ↑y = (↑(conjH V σ y) : Gal(K'/K))
    rw [coe_conjH, conj_apply_apply]
  · intro hx
    obtain ⟨m, hmA, hmx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
    have hmm : σ⁻¹ * (↑x : Gal(K'/K)) * σ = m := by
      rw [← hmx, toMonoidHom_conj_apply]
      group
    have hmV : m ∈ V := by
      have h := (mem_conjSub (V := V) (σ := σ)).mp x.2
      rwa [hmm] at h
    refine Subgroup.mem_map.mpr ⟨⟨m, hmV⟩, Subgroup.mem_subgroupOf.mpr hmA, ?_⟩
    apply Subtype.ext
    show (↑(conjH V σ ⟨m, hmV⟩) : Gal(K'/K)) = (↑x : Gal(K'/K))
    rw [coe_conjH]
    show σ * m * σ⁻¹ = (↑x : Gal(K'/K))
    rw [← hmx, toMonoidHom_conj_apply]

/-- The level-group isomorphism induced by conjugation:
`V/(V ∩ Gal(L)) ≃* σVσ⁻¹/(σVσ⁻¹ ∩ Gal(σL))`. -/
noncomputable def levelConjEquiv (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    LevelGroup V L ≃* LevelGroup (conjSub V σ) (conjLevel σ L) :=
  QuotientGroup.congr (L.fixingSubgroup.subgroupOf V)
    ((conjLevel σ L).fixingSubgroup.subgroupOf (conjSub V σ)) (conjH V σ)
    (by rw [fixingSubgroup_conjLevel]; exact map_subgroupOf_conjH V σ L.fixingSubgroup)

/-- The inverse level-group isomorphism:
`σVσ⁻¹/(σVσ⁻¹ ∩ Gal(M)) ≃* V/(V ∩ Gal(σ⁻¹M))`. -/
noncomputable def levelConjInvEquiv (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K))
    (M : FiniteGaloisIntermediateField K K') :
    LevelGroup (conjSub V σ) M ≃* LevelGroup V (conjLevel σ⁻¹ M) :=
  QuotientGroup.congr (M.fixingSubgroup.subgroupOf (conjSub V σ))
    ((conjLevel σ⁻¹ M).fixingSubgroup.subgroupOf V) (conjH V σ).symm
    (by
      rw [Subgroup.map_symm_eq_iff_map_eq]
      rw [fixingSubgroup_conjLevel, map_subgroupOf_conjH, Subgroup.map_map]
      have h : (MulAut.conj σ).toMonoidHom.comp (MulAut.conj σ⁻¹).toMonoidHom =
          MonoidHom.id Gal(K'/K) := by
        ext x
        rw [MonoidHom.comp_apply, MonoidHom.id_apply, toMonoidHom_conj_apply,
          toMonoidHom_conj_apply]
        group
      rw [h, Subgroup.map_id])

/-! ## §3. Naturality of the level isomorphisms -/

/-- **Naturality of `levelConjEquiv`** with respect to the inflation maps. -/
lemma levelConjEquiv_natural (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K))
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L')
    (x : LevelGroup (conjSub V σ) (conjLevel σ L')) :
    (levelQuotHom (U := V) h) ((levelConjEquiv V σ L').symm x) =
      (levelConjEquiv V σ L).symm
        ((levelQuotHom (U := conjSub V σ) (conjLevel_le_conjLevel σ h)) x) := by
  induction x using QuotientGroup.induction_on with
  | H y =>
    simp only [levelQuotHom, levelConjEquiv, QuotientGroup.congr_symm,
      QuotientGroup.congr_mk, QuotientGroup.map_mk, MonoidHom.id_apply]

/-- **Naturality of `levelConjInvEquiv`** with respect to the inflation maps. -/
lemma levelConjInvEquiv_natural (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K))
    {M M' : FiniteGaloisIntermediateField K K'} (k : M ≤ M')
    (x : LevelGroup V (conjLevel σ⁻¹ M')) :
    (levelQuotHom (U := conjSub V σ) k) ((levelConjInvEquiv V σ M').symm x) =
      (levelConjInvEquiv V σ M).symm
        ((levelQuotHom (U := V) (conjLevel_le_conjLevel σ⁻¹ k)) x) := by
  induction x using QuotientGroup.induction_on with
  | H y =>
    simp only [levelQuotHom, levelConjInvEquiv, QuotientGroup.congr_symm,
      QuotientGroup.congr_mk, QuotientGroup.map_mk, MonoidHom.id_apply]

/-- The round-trip `e_L.symm ∘ e''_{σL}.symm` is the inflation map from `L` to `σ⁻¹(σL)`. -/
lemma levelConjEquiv_comp_levelConjInvEquiv (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K')
    (x : LevelGroup V (conjLevel σ⁻¹ (conjLevel σ L))) :
    (levelConjEquiv V σ L).symm ((levelConjInvEquiv V σ (conjLevel σ L)).symm x) =
      (levelQuotHom (U := V) (le_conjLevel_conjLevel σ L)) x := by
  induction x using QuotientGroup.induction_on with
  | H y =>
    simp only [levelQuotHom, levelConjEquiv, levelConjInvEquiv, QuotientGroup.congr_symm,
      QuotientGroup.congr_mk, QuotientGroup.map_mk, MonoidHom.id_apply,
      MulEquiv.symm_symm, conjH_symm_apply_apply]

/-! ## §4. The transport maps on `H²(·, Z/p)` -/

/-- The forward transport family: a class at the level `L` is sent to the level `σ • L` of the
conjugate subgroup along the conjugation isomorphism. -/
noncomputable def conjFamily (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K)) (p : ℕ) :
    (L : FiniteGaloisIntermediateField K K') → LevelH2 p V L → H2Profinite p (conjSub V σ) :=
  fun L a => H2Profinite.ofLevel (conjLevel σ L) ((H2.map (levelConjEquiv V σ L).symm.toMonoidHom) a)

/-- The backward transport family. -/
noncomputable def conjInvFamily (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K)) (p : ℕ) :
    (M : FiniteGaloisIntermediateField K K') → LevelH2 p (conjSub V σ) M → H2Profinite p V :=
  fun M b => H2Profinite.ofLevel (conjLevel σ⁻¹ M)
    ((H2.map (levelConjInvEquiv V σ M).symm.toMonoidHom) b)

@[simp]
lemma conjFamily_apply (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K)) (p : ℕ)
    (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p V L) :
    conjFamily V σ p L a =
      H2Profinite.ofLevel (conjLevel σ L) ((H2.map (levelConjEquiv V σ L).symm.toMonoidHom) a) :=
  rfl

@[simp]
lemma conjInvFamily_apply (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K)) (p : ℕ)
    (M : FiniteGaloisIntermediateField K K') (b : LevelH2 p (conjSub V σ) M) :
    conjInvFamily V σ p M b =
      H2Profinite.ofLevel (conjLevel σ⁻¹ M)
        ((H2.map (levelConjInvEquiv V σ M).symm.toMonoidHom) b) := rfl

/-- The levelwise form of the naturality of `levelConjEquiv` in `H²(·, Z/p)`. -/
lemma levelConjEquiv_natural_H2 (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K)) (p : ℕ)
    {L L' : FiniteGaloisIntermediateField K K'} (h : L ≤ L') (a : LevelH2 p V L) :
    (H2.map (levelConjEquiv V σ L').symm.toMonoidHom) ((levelMap p (U := V) h) a) =
      (levelMap p (U := conjSub V σ) (conjLevel_le_conjLevel σ h))
        ((H2.map (levelConjEquiv V σ L).symm.toMonoidHom) a) := by
  rw [levelMap, levelMap, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
    ← H2.map_comp, ← H2.map_comp]
  have hnat : MonoidHom.comp (levelQuotHom (U := V) h)
        (levelConjEquiv V σ L').symm.toMonoidHom =
      MonoidHom.comp (levelConjEquiv V σ L).symm.toMonoidHom
        (levelQuotHom (U := conjSub V σ) (conjLevel_le_conjLevel σ h)) := by
    ext x
    exact levelConjEquiv_natural V σ h x
  rw [hnat]

/-- The levelwise form of the naturality of `levelConjInvEquiv` in `H²(·, Z/p)`. -/
lemma levelConjInvEquiv_natural_H2 (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K)) (p : ℕ)
    {M M' : FiniteGaloisIntermediateField K K'} (k : M ≤ M')
    (b : LevelH2 p (conjSub V σ) M) :
    (H2.map (levelConjInvEquiv V σ M').symm.toMonoidHom) ((levelMap p (U := conjSub V σ) k) b) =
      (levelMap p (U := V) (conjLevel_le_conjLevel σ⁻¹ k))
        ((H2.map (levelConjInvEquiv V σ M).symm.toMonoidHom) b) := by
  rw [levelMap, levelMap, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
    ← H2.map_comp, ← H2.map_comp]
  have hnat : MonoidHom.comp (levelQuotHom (U := conjSub V σ) k)
        (levelConjInvEquiv V σ M').symm.toMonoidHom =
      MonoidHom.comp (levelConjInvEquiv V σ M).symm.toMonoidHom
        (levelQuotHom (U := V) (conjLevel_le_conjLevel σ⁻¹ k)) := by
    ext x
    exact levelConjInvEquiv_natural V σ k x
  rw [hnat]

/-- The levelwise form of the round-trip identity in `H²(·, Z/p)`. -/
lemma levelConjEquiv_comp_levelConjInvEquiv_H2 (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K))
    (p : ℕ) (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p V L) :
    (H2.map (levelConjInvEquiv V σ (conjLevel σ L)).symm.toMonoidHom)
        ((H2.map (levelConjEquiv V σ L).symm.toMonoidHom) a) =
      (levelMap p (U := V) (le_conjLevel_conjLevel σ L)) a := by
  rw [levelMap, ← CategoryTheory.comp_apply, ← H2.map_comp]
  have hcomp : MonoidHom.comp (levelConjEquiv V σ L).symm.toMonoidHom
        (levelConjInvEquiv V σ (conjLevel σ L)).symm.toMonoidHom =
      levelQuotHom (U := V) (le_conjLevel_conjLevel σ L) := by
    ext x
    exact levelConjEquiv_comp_levelConjInvEquiv V σ L x
  rw [hcomp]

/-! ## §5. Compatibility of the two transports with the levels -/

lemma conjFamily_compat (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K)) (p : ℕ) :
    ∀ (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L') (a : LevelH2 p V L),
      conjFamily V σ p L' ((levelMap p (U := V) h) a) = conjFamily V σ p L a := by
  intro L L' h a
  rw [conjFamily_apply, conjFamily_apply]
  rw [← H2Profinite.ofLevel_levelMap (p := p) (U := conjSub V σ)
    (h := conjLevel_le_conjLevel σ h) (a := (H2.map (levelConjEquiv V σ L).symm.toMonoidHom) a)]
  congr 1
  exact levelConjEquiv_natural_H2 V σ p h a

lemma conjInvFamily_compat (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K)) (p : ℕ) :
    ∀ (M M' : FiniteGaloisIntermediateField K K') (k : M ≤ M')
      (b : LevelH2 p (conjSub V σ) M),
      conjInvFamily V σ p M' ((levelMap p (U := conjSub V σ) k) b) =
        conjInvFamily V σ p M b := by
  intro M M' k b
  rw [conjInvFamily_apply, conjInvFamily_apply]
  rw [← H2Profinite.ofLevel_levelMap (p := p) (U := V)
    (h := conjLevel_le_conjLevel σ⁻¹ k)
    (a := (H2.map (levelConjInvEquiv V σ M).symm.toMonoidHom) b)]
  congr 1
  exact levelConjInvEquiv_natural_H2 V σ p k b

/-- **The round trip is the identity.** -/
lemma conjInvFamily_conjFamily (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K)) (p : ℕ) :
    ∀ (L : FiniteGaloisIntermediateField K K') (a : LevelH2 p V L),
      (H2Profinite.lift (conjInvFamily V σ p) (conjInvFamily_compat V σ p))
        ((H2Profinite.lift (conjFamily V σ p) (conjFamily_compat V σ p))
          (H2Profinite.ofLevel L a)) = H2Profinite.ofLevel L a := by
  intro L a
  rw [H2Profinite.lift_ofLevel, conjFamily_apply, H2Profinite.lift_ofLevel, conjInvFamily_apply]
  rw [← H2Profinite.ofLevel_levelMap (p := p) (U := V) (h := le_conjLevel_conjLevel σ L)
    (a := a)]
  congr 1
  exact levelConjEquiv_comp_levelConjInvEquiv_H2 V σ p L a

/-! ## §6. The transport of non-triviality -/

/-- **The transport of non-triviality of `H²(·, Z/p)` under conjugation of the subgroup.** -/
theorem nontrivial_H2Profinite_conjSub {p : ℕ} {V : Subgroup Gal(K'/K)} {σ : Gal(K'/K)}
    (h : Nontrivial (H2Profinite p V)) : Nontrivial (H2Profinite p (conjSub V σ)) := by
  classical
  have hleft : (H2Profinite.lift (conjInvFamily V σ p) (conjInvFamily_compat V σ p)) ∘
      (H2Profinite.lift (conjFamily V σ p) (conjFamily_compat V σ p)) = id := by
    have h1 : (H2Profinite.lift (conjInvFamily V σ p) (conjInvFamily_compat V σ p)) ∘
        (H2Profinite.lift (conjFamily V σ p) (conjFamily_compat V σ p)) =
        H2Profinite.lift (fun L a => H2Profinite.ofLevel (p := p) (U := V) L a)
          (fun L L' h a => H2Profinite.ofLevel_levelMap h a) :=
      H2Profinite.lift_unique _ _ _ (fun L a => conjInvFamily_conjFamily V σ p L a)
    have h2 : H2Profinite.lift (fun L a => H2Profinite.ofLevel (p := p) (U := V) L a)
        (fun L L' h a => H2Profinite.ofLevel_levelMap h a) = id := by
      funext x
      obtain ⟨L, a, rfl⟩ := H2Profinite.ofLevel_surjective x
      rw [H2Profinite.lift_ofLevel]
      rfl
    rw [h1, h2]
  have hinj : Function.Injective
      (H2Profinite.lift (conjFamily V σ p) (conjFamily_compat V σ p)) := by
    intro x y hxy
    have hx := congrFun hleft x
    have hy := congrFun hleft y
    simp only [Function.comp_apply, id_eq] at hx hy
    rw [← hx, ← hy, hxy]
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (H2Profinite p V)
  exact ⟨_, _, fun hc => hxy (hinj hc)⟩

/-! ## §7. The requested lemma -/

theorem conjTransport : NK.NUV2.LC.ConjTransport := by
  intro K K' _ _ _ _ _ V σ h
  exact nontrivial_H2Profinite_conjSub h

end NK.NUV2.LC
