import Mathlib
import Submission.Work.CurveBasics.BaseChangeScheme
import Submission.Work.CurveBasics.BaseChange.krullDimLE_tensor

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The local rings of a base changed curve have Krull dimension at most one

Let `C` be a curve over a field `k` and `F/k` a field extension.  We show that every local
ring of the base change `C_F = C ×_k Spec F` has Krull dimension at most one.

The strategy is to reduce to commutative algebra in a single affine chart.

* Around a point `z` of `C_F` choose an affine open `V = Spec A` of `C` containing the image
  of `z`.  Then `A = Γ(C, V)` is a finitely generated `k`-algebra of Krull dimension `≤ 1`
  (`krullDimLE_sections`), and the preimage of `V` in `C_F` is `Spec (A ⊗[k] F)`
  (`preimageIso`).
* `Work.CurveBasics.BaseChange.krullDimLE_tensor` shows that `A ⊗[k] F` still has Krull
  dimension `≤ 1`.
* The stalk `O_{C_F, z}` is a localisation of `Γ(C_F, fst ⁻¹ᵁ V) ≅ A ⊗[k] F`, and
  localisation does not increase the Krull dimension.
-/

namespace Work.CurveBasics.BaseChange

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct
open Work.CurveBasics

universe u

/-- The canonical `k`-algebra structure on the ring of sections of an open subset of a scheme
over `Spec k`. -/
noncomputable instance instAlgebraSections {k : Type u} [Field k] (C : Curve k)
    (V : C.left.Opens) : Algebra k Γ(C.left, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ C.hom.appLE ⊤ V (by simp)).hom.toAlgebra

/-- The coordinate ring of an affine open subset of a curve is a finitely generated
`k`-algebra.  This uses that `C` is locally of finite type over `k`. -/
lemma finiteType_sections {k : Type u} [Field k] (C : Curve k) (V : C.left.Opens)
    (hV : IsAffineOpen V) : Algebra.FiniteType k Γ(C.left, V) := by
  have hf : (C.hom.appLE ⊤ V (by simp)).hom.FiniteType :=
    Scheme.Hom.finiteType_appLE C.hom (isAffineOpen_top (Spec (CommRingCat.of k))) hV _
  rw [← RingHom.finiteType_algebraMap]
  have h1 : algebraMap k Γ(C.left, V) = (C.hom.appLE ⊤ V (by simp)).hom.comp
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom) := rfl
  rw [h1]
  exact RingHom.FiniteType.comp hf (RingHom.FiniteType.of_surjective _ (by
    intro y
    exact ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom y, Iso.inv_hom_id_apply _ _⟩))

/-- The coordinate ring of an affine open subset of a curve has Krull dimension at most one.
This is the local version of the corresponding statement for `C` at a single point: the
local rings of `C` are the localisations of `Γ(C,V)` at its primes. -/
theorem krullDimLE_sections {k : Type u} [Field k] (C : Curve k) (V : C.left.Opens)
    (hV : IsAffineOpen V) : Ring.KrullDimLE 1 Γ(C.left, V) := by
  refine Ring.krullDimLE_of_isLocalization_maximal (fun P _ => Localization.AtPrime P) ?_
  intro P hP
  rw [Ring.krullDimLE_iff,
    IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)]
  set y : ↥(Spec Γ(C.left, V)) := ⟨P, hP.isPrime⟩ with hy
  have hpx : hV.primeIdealOf (hV.isoSpec.inv y) = y := by
    show hV.isoSpec.hom (hV.isoSpec.inv y) = y
    have h := congrArg (fun f : (Spec Γ(C.left, V)) ⟶ (Spec Γ(C.left, V)) => f y)
      hV.isoSpec.inv_hom_id
    rw [Scheme.Hom.comp_apply] at h
    simpa using h
  have hpx' : (hV.primeIdealOf (hV.isoSpec.inv y)).asIdeal = P := by rw [hpx, hy]
  letI : Algebra Γ(C.left, V) (C.left.presheaf.stalk (hV.isoSpec.inv y).1) :=
    TopCat.Presheaf.algebra_section_stalk C.left.presheaf (U := V) (hV.isoSpec.inv y)
  haveI := hV.isLocalization_stalk (hV.isoSpec.inv y)
  have h2 := IsLocalization.AtPrime.ringKrullDim_eq_height
    (hV.primeIdealOf (hV.isoSpec.inv y)).asIdeal (C.left.presheaf.stalk (hV.isoSpec.inv y).1)
  rw [← hpx', ← h2]
  exact Ring.krullDimLE_iff.mp (C.krullDim_stalk_le_one (hV.isoSpec.inv y).1)

/-- The structure morphism of the affine chart `Spec Γ(C,V) ⟶ Spec k` is `Spec` of the
canonical `k`-algebra structure on `Γ(C,V)`. -/
lemma fromSpec_comp_hom {k : Type u} [Field k] (C : Curve k) (V : C.left.Opens)
    (hV : IsAffineOpen V) :
    hV.fromSpec ≫ C.hom = Spec.map (CommRingCat.ofHom (algebraMap k Γ(C.left, V))) := by
  have i : V ≤ C.hom ⁻¹ᵁ ⊤ := by simp
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec C.hom (isAffineOpen_top (Spec (CommRingCat.of k)))
    hV i]
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- The underlying morphism of the open immersion `V ⟶ C` followed by the structure morphism
of `C` is `Spec` of the canonical `k`-algebra structure on `Γ(C,V)`. -/
lemma iota_comp_hom {k : Type u} [Field k] (C : Curve k) (V : C.left.Opens)
    (hV : IsAffineOpen V) :
    V.ι ≫ C.hom =
      hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(C.left, V))) := by
  rw [← IsAffineOpen.isoSpec_hom_fromSpec hV, Category.assoc, fromSpec_comp_hom C V hV]

/-- For an affine open `V ⊆ C` the preimage of `V` in the base change `C_F` is the fibred
product `V ×_{Spec k} Spec F`; this is the pasting of the defining pullback square of `C_F`
with the preimage square of `V`. -/
lemma paste_square {k : Type u} [Field k] (C : Curve k) (F : Type u) [Field F] [Algebra k F]
    (V : C.left.Opens) :
    IsPullback ((C.baseChangeFst F) ∣_ V)
      ((C.baseChangeFst F ⁻¹ᵁ V).ι ≫ pullback.snd C.hom (Curve.specMap k F))
      (V.ι ≫ C.hom) (Curve.specMap k F) := by
  have hA : IsPullback ((C.baseChangeFst F) ∣_ V) ((C.baseChangeFst F ⁻¹ᵁ V).ι) V.ι
      (C.baseChangeFst F) := isPullback_morphismRestrict (C.baseChangeFst F) V
  have hB : IsPullback (C.baseChangeFst F) (pullback.snd C.hom (Curve.specMap k F))
      C.hom (Curve.specMap k F) := IsPullback.of_hasPullback C.hom (Curve.specMap k F)
  exact hA.paste_vert hB

/-- The preimage of an affine open `V ⊆ C` in the base change `C_F` is a pullback along
`Spec` of the canonical `k`-algebra structure on `Γ(C,V)` (instead of along `V.ι ≫ C.hom`). -/
lemma isPullback_spec {k : Type u} [Field k] (C : Curve k) (F : Type u) [Field F] [Algebra k F]
    (V : C.left.Opens) (hV : IsAffineOpen V) :
    IsPullback (((C.baseChangeFst F) ∣_ V) ≫ hV.isoSpec.hom)
      ((C.baseChangeFst F ⁻¹ᵁ V).ι ≫ pullback.snd C.hom (Curve.specMap k F))
      (Spec.map (CommRingCat.ofHom (algebraMap k Γ(C.left, V)))) (Curve.specMap k F) := by
  refine (paste_square C F V).of_iso (Iso.refl _) hV.isoSpec (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_ <;> simp [iota_comp_hom C V hV]

/-- The preimage of an affine open of `C` in `C_F` is affine, with coordinate ring
`Γ(C,V) ⊗[k] F`. -/
noncomputable def preimageIso {k : Type u} [Field k] (C : Curve k) (F : Type u) [Field F]
    [Algebra k F] (V : C.left.Opens) (hV : IsAffineOpen V) :
    (↑(C.baseChangeFst F ⁻¹ᵁ V) : Scheme) ≅ Spec (CommRingCat.of (Γ(C.left, V) ⊗[k] F)) :=
  (isPullback_spec C F V hV).isoPullback ≪≫ pullbackSpecIso k Γ(C.left, V) F

/-- The sections of the preimage of an affine open `V ⊆ C` over `C_F` are
`Γ(C,V) ⊗[k] F`. -/
noncomputable def sectionsIso {k : Type u} [Field k] (C : Curve k) (F : Type u) [Field F]
    [Algebra k F] (V : C.left.Opens) (hV : IsAffineOpen V) :
    Γ(C.baseChangeLeft F, C.baseChangeFst F ⁻¹ᵁ V) ≃+* (Γ(C.left, V) ⊗[k] F) :=
  (((C.baseChangeFst F ⁻¹ᵁ V).topIso).commRingCatIsoToRingEquiv).symm.trans <|
    ((Scheme.Γ.mapIso (preimageIso C F V hV).op).commRingCatIsoToRingEquiv).symm.trans <|
      (Scheme.ΓSpecIso (CommRingCat.of (Γ(C.left, V) ⊗[k] F))).commRingCatIsoToRingEquiv

open Work.CurveBasics in
theorem krullDim_le_one {k : Type u} [Field k] (C : Curve k) (F : Type u) [Field F]
    [Algebra k F] (z : C.baseChangeLeft F) :
    Ring.KrullDimLE 1 ((C.baseChangeLeft F).presheaf.stalk z) := by
  -- an affine chart of `C` around the image of `z`
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, -⟩ :=
    C.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (C.baseChangeFst F z))
      isOpen_univ
  -- the preimage of the chart is affine with coordinate ring `Γ(C,V) ⊗[k] F`
  have hAff : IsAffineOpen (C.baseChangeFst F ⁻¹ᵁ V) :=
    IsAffine.of_isIso (preimageIso C F V hV).hom
  -- `Γ(C,V)` is a finitely generated `k`-algebra of Krull dimension `≤ 1`
  haveI : Algebra.FiniteType k Γ(C.left, V) := finiteType_sections C V hV
  have hAF : Ring.KrullDimLE 1 (Γ(C.left, V) ⊗[k] F) :=
    krullDimLE_tensor (k := k) (F := F) (krullDimLE_sections C V hV)
  -- hence so are the sections over the preimage
  have hsec : Ring.KrullDimLE 1 Γ(C.baseChangeLeft F, C.baseChangeFst F ⁻¹ᵁ V) := by
    rw [Ring.krullDimLE_iff] at hAF ⊢
    exact (le_of_eq (ringKrullDim_eq_of_ringEquiv (sectionsIso C F V hV))).trans hAF
  -- the stalk at `z` is a localisation of these sections, so has dimension `≤ 1` too
  letI : Algebra Γ(C.baseChangeLeft F, C.baseChangeFst F ⁻¹ᵁ V)
      ((C.baseChangeLeft F).presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk (C.baseChangeLeft F).presheaf
      (U := C.baseChangeFst F ⁻¹ᵁ V) ⟨z, hzV⟩
  have hloc := hAff.isLocalization_stalk ⟨z, hzV⟩
  rw [Ring.krullDimLE_iff] at hsec ⊢
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hAff.primeIdealOf ⟨z, hzV⟩).asIdeal
      ((C.baseChangeLeft F).presheaf.stalk z)]
  exact (Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top').trans hsec

end Work.CurveBasics.BaseChange
