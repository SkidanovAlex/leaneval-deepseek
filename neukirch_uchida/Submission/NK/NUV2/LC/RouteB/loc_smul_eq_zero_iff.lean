import Mathlib
import Submission.NK.NUV2.LC.RouteB.locConjAux

/-!
# The localisation at a place is invariant under conjugation by an element of the group

For a closed subgroup `W ≤ Gal(K'/K)`, an element `v ∈ W` and a place `A` of `K'` over a finite
prime of `K`, the two localisations

`H2Profinite.loc p W x A` and `H2Profinite.loc p W x (v • A)`

vanish simultaneously.  This is the "comparison" input of `NK.NUV2.LC.RouteB.notInOrbit_of_loc_eq_zero`
(two places with different local behaviour of a class are not conjugate).

The mathematics is that conjugation by `v` acts on each finite level group
`LevelGroup W L = W/(W ∩ Gal(K'/L))` as an *inner* automorphism (the subgroup `Gal(K'/L)` is normal
in `Gal(K'/K)`), and inner automorphisms act trivially on `H²(·, Z/p)` with trivial coefficients
(`NK.NUV2.LC.RouteB.H2_map_conj_eq_id`).

The proof is level-wise.  Writing `x = ofLevel L a`, the level criterion
`NK.HassePrinciple.loc_ofLevel_eq_zero_iff` reduces the claim to: for every finite level `M ≥ L`,
the class `c = levelMap h a` of `H²(W/(W ∩ Gal(K'/M)), Z/p)` dies in `H²((W ∩ D_A)/(...), Z/p)`
if and only if it dies in `H²((W ∩ D_{vA})/(...), Z/p)`.  Those two local groups are conjugate
(`stabSubgroup A` is carried to `stabSubgroup (v • A)` by conjugation with `v`), and the resulting
commuting square

```
LevelGroup (W ⊓ D_A) M --levelInclHom--> LevelGroup W M
   | levelConjHom                                 | conj by v (inner)
   v                                              v
LevelGroup (W ⊓ D_{vA}) M --levelInclHom--> LevelGroup W M
```

together with `H2_map_conj_eq_id` gives the identification of the two restriction maps.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open CategoryTheory
open scoped Pointwise

namespace NK.NUV2.LC.RouteB

open NK.BrauerHasse

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## §0. Conjugation in a quotient group -/

/-- **Conjugation in a quotient group**: the class of `a` acts on the class of `b` by the class of
`a * b * a⁻¹`. -/
lemma mulAut_conj_mk {G : Type} [Group G] (N : Subgroup G) [N.Normal] (a b : G) :
    (MulAut.conj ((a : G ⧸ N))) ((b : G ⧸ N)) = ((a * b * a⁻¹ : G) : G ⧸ N) := by
  rw [MulAut.conj_apply]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]

/-! ## §1. The conjugation of subgroups -/

/-- Conjugation by `v` as a homomorphism `V →* V.map (MulAut.conj v)`. -/
noncomputable def conjSubHom (V : Subgroup Gal(K'/K)) (v : Gal(K'/K)) :
    ↥V →* ↥(V.map (MulAut.conj v).toMonoidHom) :=
  (MulEquiv.subgroupMap (MulAut.conj v) V).toMonoidHom

lemma conjSubHom_apply (V : Subgroup Gal(K'/K)) (v : Gal(K'/K)) (y : ↥V) :
    (↑(conjSubHom V v y) : Gal(K'/K)) = v * ↑y * v⁻¹ := by
  show (↑((MulEquiv.subgroupMap (MulAut.conj v) V) y) : Gal(K'/K)) = v * ↑y * v⁻¹
  rw [MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]

/-- The inverse of `conjSubHom`, as a homomorphism `V.map (MulAut.conj v) →* V`. -/
noncomputable def conjSubInvHom (V : Subgroup Gal(K'/K)) (v : Gal(K'/K)) :
    ↥(V.map (MulAut.conj v).toMonoidHom) →* ↥V :=
  (MulEquiv.subgroupMap (MulAut.conj v) V).symm.toMonoidHom

lemma conjSubInvHom_conjSubHom (V : Subgroup Gal(K'/K)) (v : Gal(K'/K)) (y : ↥V) :
    conjSubInvHom V v (conjSubHom V v y) = y :=
  MulEquiv.symm_apply_apply _ _

lemma conjSubHom_conjSubInvHom (V : Subgroup Gal(K'/K)) (v : Gal(K'/K))
    (z : ↥(V.map (MulAut.conj v).toMonoidHom)) :
    conjSubHom V v (conjSubInvHom V v z) = z :=
  MulEquiv.apply_symm_apply _ _

lemma conjSubInvHom_apply (V : Subgroup Gal(K'/K)) (v : Gal(K'/K))
    (z : ↥(V.map (MulAut.conj v).toMonoidHom)) :
    (↑(conjSubInvHom V v z) : Gal(K'/K)) = v⁻¹ * ↑z * v := by
  have h1 : (↑(conjSubHom V v (conjSubInvHom V v z)) : Gal(K'/K)) = ↑z := by
    rw [conjSubHom_conjSubInvHom]
  rw [conjSubHom_apply] at h1
  rw [← h1]
  group

/-- If `v ∈ W` then `W` is stable under conjugation by `v`. -/
lemma conj_map_self {W : Subgroup Gal(K'/K)} {v : Gal(K'/K)} (hv : v ∈ W) :
    W.map (MulAut.conj v).toMonoidHom = W :=
  (Subgroup.mem_normalizer_iff_map_conj_eq).mp (Subgroup.le_normalizer hv)

/-- The fixing subgroup of a finite Galois level is normal in `Gal(K'/K)`, hence stable under
conjugation. -/
lemma fixingSubgroup_map_conj_self (M : FiniteGaloisIntermediateField K K') (v : Gal(K'/K)) :
    M.fixingSubgroup.map (MulAut.conj v).toMonoidHom = M.fixingSubgroup :=
  Subgroup.Normal.map_conj_eq M.fixingSubgroup v

/-! ## §2. The conjugation isomorphism of the level groups -/

/-- The conjugation homomorphism `LevelGroup V M →* LevelGroup (V.map (MulAut.conj v)) M` on the
finite level groups. -/
noncomputable def levelConjHom (V : Subgroup Gal(K'/K)) (v : Gal(K'/K))
    (M : FiniteGaloisIntermediateField K K') :
    LevelGroup V M →* LevelGroup (V.map (MulAut.conj v).toMonoidHom) M :=
  QuotientGroup.map (M.fixingSubgroup.subgroupOf V)
    (M.fixingSubgroup.subgroupOf (V.map (MulAut.conj v).toMonoidHom))
    (conjSubHom V v)
    (fun x hx => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      rw [conjSubHom_apply]
      simpa using Subgroup.Normal.conj_mem' (inferInstance : M.fixingSubgroup.Normal) ↑x
        (Subgroup.mem_subgroupOf.mp hx) v⁻¹)

/-- The inverse conjugation homomorphism of the level groups. -/
noncomputable def levelConjInvHom (V : Subgroup Gal(K'/K)) (v : Gal(K'/K))
    (M : FiniteGaloisIntermediateField K K') :
    LevelGroup (V.map (MulAut.conj v).toMonoidHom) M →* LevelGroup V M :=
  QuotientGroup.map (M.fixingSubgroup.subgroupOf (V.map (MulAut.conj v).toMonoidHom))
    (M.fixingSubgroup.subgroupOf V)
    (conjSubInvHom V v)
    (fun z hz => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      rw [conjSubInvHom_apply]
      exact Subgroup.Normal.conj_mem' (inferInstance : M.fixingSubgroup.Normal) ↑z
        (Subgroup.mem_subgroupOf.mp hz) v)

lemma levelConjHom_mk (V : Subgroup Gal(K'/K)) (v : Gal(K'/K))
    (M : FiniteGaloisIntermediateField K K') (y : ↥V) :
    levelConjHom V v M (y : LevelGroup V M) =
      (conjSubHom V v y : LevelGroup (V.map (MulAut.conj v).toMonoidHom) M) :=
  rfl

lemma levelConjInvHom_mk (V : Subgroup Gal(K'/K)) (v : Gal(K'/K))
    (M : FiniteGaloisIntermediateField K K') (z : ↥(V.map (MulAut.conj v).toMonoidHom)) :
    levelConjInvHom V v M (z : LevelGroup (V.map (MulAut.conj v).toMonoidHom) M) =
      (conjSubInvHom V v z : LevelGroup V M) :=
  rfl

/-- The value of the inclusion of a subgroup into the ambient level group, on cosets. -/
lemma levelInclHom_mk {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') (y : ↥V) :
    levelInclHom h L (y : LevelGroup V L) = (Subgroup.inclusion h y : LevelGroup U L) :=
  rfl

lemma levelConjInvHom_comp (V : Subgroup Gal(K'/K)) (v : Gal(K'/K))
    (M : FiniteGaloisIntermediateField K K') :
    (levelConjInvHom V v M).comp (levelConjHom V v M) = MonoidHom.id (LevelGroup V M) := by
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H y =>
    show levelConjInvHom V v M (levelConjHom V v M (y : LevelGroup V M)) = (y : LevelGroup V M)
    rw [levelConjHom_mk, levelConjInvHom_mk, conjSubInvHom_conjSubHom]

lemma levelConjHom_comp (V : Subgroup Gal(K'/K)) (v : Gal(K'/K))
    (M : FiniteGaloisIntermediateField K K') :
    (levelConjHom V v M).comp (levelConjInvHom V v M) =
      MonoidHom.id (LevelGroup (V.map (MulAut.conj v).toMonoidHom) M) := by
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H y =>
    show levelConjHom V v M (levelConjInvHom V v M
      (y : LevelGroup (V.map (MulAut.conj v).toMonoidHom) M))
      = (y : LevelGroup (V.map (MulAut.conj v).toMonoidHom) M)
    rw [levelConjInvHom_mk, levelConjHom_mk, conjSubHom_conjSubInvHom]

/-! ## §3. The commuting square -/

/-- **The commuting square.**  Conjugating the inclusion of the local level group `V/(V ∩ Gal(K'/M))`
into `W/(W ∩ Gal(K'/M))` is the inclusion of the conjugate level group
`σVσ⁻¹/(σVσ⁻¹ ∩ Gal(K'/M))`; on the target the conjugation is the *inner* automorphism of
`LevelGroup W M` given by the class of `v`. -/
lemma levelConjHom_square {W V : Subgroup Gal(K'/K)} {v : Gal(K'/K)} (hv : v ∈ W)
    (hVW : V ≤ W) (hVW' : V.map (MulAut.conj v).toMonoidHom ≤ W)
    (M : FiniteGaloisIntermediateField K K') :
    (MulAut.conj ((⟨v, hv⟩ : ↥W) : LevelGroup W M)).toMonoidHom.comp (levelInclHom hVW M)
      = (levelInclHom hVW' M).comp (levelConjHom V v M) := by
  apply MonoidHom.ext
  intro x
  induction x using QuotientGroup.induction_on with
  | H y =>
    show (MulAut.conj ((⟨v, hv⟩ : ↥W) : LevelGroup W M))
        (levelInclHom hVW M (y : LevelGroup V M))
      = levelInclHom hVW' M (levelConjHom V v M (y : LevelGroup V M))
    rw [levelConjHom_mk, levelInclHom_mk, levelInclHom_mk]
    rw [mulAut_conj_mk]
    have h : (⟨v, hv⟩ * Subgroup.inclusion hVW y * ⟨v, hv⟩⁻¹ : ↥W) =
        (Subgroup.inclusion hVW' (conjSubHom V v y) : ↥W) := by
      apply Subtype.ext
      show v * (↑y : Gal(K'/K)) * v⁻¹ = ↑(conjSubHom V v y)
      rw [conjSubHom_apply]
    rw [h]

/-! ## §4. The level-wise comparison of the two restrictions -/

/-- **The level-wise comparison.**  For a class `c` of `H²(W/(W ∩ Gal(K'/M)), Z/p)`, the
restriction to the local group `V ⊓ D_A` vanishes if and only if the restriction to the conjugate
local group `(V ⊓ D_A).map (conj v)` vanishes.

Both restrictions are obtained from one another by the conjugation isomorphism of the local level
groups, whose effect on the target `LevelGroup W M` is an inner automorphism, hence trivial on
`H²(·, Z/p)`. -/
theorem H2_map_levelInclHom_conj (p : ℕ) {W V V' : Subgroup Gal(K'/K)} {v : Gal(K'/K)}
    (hv : v ∈ W) (he : V' = V.map (MulAut.conj v).toMonoidHom)
    (hVW : V ≤ W) (hV'W : V' ≤ W)
    (M : FiniteGaloisIntermediateField K K') (c : H2 p (LevelGroup W M)) :
    (H2.map (levelInclHom hV'W M)).hom c = 0 ↔ (H2.map (levelInclHom hVW M)).hom c = 0 := by
  subst he
  have hsq := levelConjHom_square hv hVW hV'W M
  -- The restriction to the conjugate local group factors through the restriction to `V`.
  have h1 : levelInclHom hV'W M =
      ((MulAut.conj ((⟨v, hv⟩ : ↥W) : LevelGroup W M)).toMonoidHom.comp
        (levelInclHom hVW M)).comp (levelConjInvHom V v M) := by
    rw [hsq, MonoidHom.comp_assoc, levelConjHom_comp, MonoidHom.comp_id]
  have h2 : H2.map (p := p) (levelInclHom hV'W M) =
      H2.map (p := p) (levelInclHom hVW M) ≫ H2.map (p := p) (levelConjInvHom V v M) := by
    rw [h1, H2.map_comp, H2.map_comp, H2_map_conj_eq_id, Category.id_comp]
  have h3 : (H2.map (p := p) (levelInclHom hV'W M)).hom c =
      (H2.map (p := p) (levelConjInvHom V v M)).hom
        ((H2.map (p := p) (levelInclHom hVW M)).hom c) := by
    rw [h2]
    rfl
  -- The conjugation map on `H²` is injective.
  have hker : ∀ y : H2 p (LevelGroup V M),
      (H2.map (p := p) (levelConjInvHom V v M)).hom y = 0 → y = 0 := by
    intro y hy
    have hcomp : H2.map (p := p) (levelConjInvHom V v M) ≫
        H2.map (p := p) (levelConjHom V v M) = 𝟙 (H2 p (LevelGroup V M)) := by
      rw [← H2.map_comp, levelConjInvHom_comp, H2.map_id]
    have hy2 := congrArg
      (fun (f : H2 p (LevelGroup V M) ⟶ H2 p (LevelGroup V M)) => f.hom y) hcomp
    rw [ModuleCat.comp_apply, hy, map_zero] at hy2
    simpa [ModuleCat.id_apply] using hy2.symm
  constructor
  · intro hc
    rw [h3] at hc
    exact hker _ hc
  · intro hc
    rw [h3, hc, map_zero]

/-! ## §5. The requested statement -/

/-- **The vanishing of the localisation is invariant under conjugation of the place.**  For
`v ∈ W`, the localisations of a class `x ∈ H²(W, Z/p)` at the places `A` and `v • A` vanish
simultaneously. -/
theorem loc_smul_eq_zero_iff (p : ℕ) {K K' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] {W : Subgroup Gal(K'/K)} {v : Gal(K'/K)} (hv : v ∈ W)
    (x : NK.BrauerHasse.H2Profinite p W) (A : NK.BrauerHasse.OverFinitePrime K K') :
    (NK.BrauerHasse.H2Profinite.loc p W x (v • A) = 0) ↔
      (NK.BrauerHasse.H2Profinite.loc p W x A = 0) := by
  obtain ⟨L, a, rfl⟩ := H2Profinite.ofLevel_surjective x
  rw [NK.HassePrinciple.loc_ofLevel_eq_zero_iff p (v • A) L a,
    NK.HassePrinciple.loc_ofLevel_eq_zero_iff p A L a]
  refine exists_congr (fun M => exists_congr (fun h => ?_))
  rw [← NK.BrauerHasse.levelMap_locLevel_apply p W (v • A).1 h a,
    ← NK.BrauerHasse.levelMap_locLevel_apply p W A.1 h a]
  rw [NK.LocalDecomposition.locLevel_eq_map_levelInclHom,
    NK.LocalDecomposition.locLevel_eq_map_levelInclHom]
  -- identify the subgroup of the conjugated place
  have hV' : W ⊓ stabSubgroup ((v • A).1) =
      (W ⊓ stabSubgroup A.1).map (MulAut.conj v).toMonoidHom := by
    rw [show stabSubgroup ((v • A).1) =
        (stabSubgroup A.1).map (MulAut.conj v).toMonoidHom from
      NK.LocalDecomposition.stabSubgroup_smul A.1 v]
    conv_lhs => rw [← conj_map_self hv]
    rw [← Subgroup.map_inf_eq _ _ _ (MulAut.conj v).injective]
  exact H2_map_levelInclHom_conj (K := K) (K' := K') p (W := W)
    (V := W ⊓ stabSubgroup A.1) (V' := W ⊓ stabSubgroup ((v • A).1)) (v := v)
    hv hV' inf_le_left inf_le_left M ((levelMap p (U := W) h) a)

end NK.NUV2.LC.RouteB
