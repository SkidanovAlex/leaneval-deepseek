import Mathlib
import Submission.Work.Cohomology.cokernelComponent
import Submission.Work.Cohomology.capRelMid
import Submission.Work.Cohomology.Crux.Transgression
import Submission.Work.Cohomology.relMV_shortExact
import Submission.Work.Cohomology.MVcapSquares
import Submission.Work.Cohomology.relKernMono
import Submission.Work.Cohomology.relCapHHom

/-!
# The downward reindexing of a chain complex of `ℤ`-modules, and the cap-product shifts

The relative and absolute Mayer–Vietoris short exact sequences
(`Work.Cohomology.cruxShort`, `Work.Cohomology.mvSmall_shortExact`) live in the category of chain
complexes of `ℤ`-modules indexed by `ℕ`.  The cap product with a relative `4`-cocycle `α` is a map
of *degree* `-4`, i.e. a collection of maps

`cap X A U V α m : (relMVTopC X A U V).X (4 + m) ⟶ (smallChains U V).X m`,

so to speak about its compatibility with the Mayer–Vietoris connecting maps (the *transgression
identity*, Hatcher's Lemma 3.36) one has to reindex the source complexes.  This file provides the
reindexing (`dsh`, "downward shift by `4`") and its basic functoriality.

The reindexed complex `dsh C` has `(dsh C).X n = C.X (4 + n)` and `(dsh C).d i j = C.d (4+i) (4+j)`,
so that `HomologicalComplex.homology (dsh C) k` agrees with `HomologicalComplex.homology C (k + 4)`
for `k ≥ 1` (the only obstruction is the truncation of `ComplexShape.down ℕ` at degree `0`, where
`prev 0 = 0`); the identification is recorded in
`Work.Cohomology.Endgame.dshHomologyIso` (in the companion file).

## Main definitions

* `dsh` — the downward shift by `4` of a chain complex of `ℤ`-modules;
* `dshMap` — the induced morphism, with the functoriality lemmas `dshMap_comp`, `dshMap_id`,
  `dshMap_zero`;
* `dshShort` — the induced short complex.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## The downward shift by `4` -/

/-- **The embedding of the index type `ℕ` of chain complexes into itself given by `n ↦ 4 + n`.**
It realises the downward reindexing `n ↦ n + 4` as a restriction of complexes, so that Mathlib's
`HomologicalComplex.restrictionHomologyIso` identifies the homologies (see `dshHomologyIso`). -/
def shiftEmb : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) where
  f n := 4 + n
  injective_f := by
    intro a b h
    simp only at h
    omega
  rel := by
    intro i j hij
    simp only [ComplexShape.down_Rel] at hij ⊢
    omega

/-- The shift embedding satisfies the `IsRelIff` condition. -/
instance shiftEmb_isRelIff : shiftEmb.IsRelIff where
  rel' := by
    intro i j hij
    simp only [ComplexShape.down_Rel] at hij ⊢
    simp only [shiftEmb] at hij
    omega

/-- **The downward reindexing `n ↦ n + 4` of a chain complex of `ℤ`-modules**, realised as the
restriction of complexes along the shift embedding `shiftEmb`. -/
noncomputable def dsh (C : ChainComplex (ModuleCat ℤ) ℕ) : ChainComplex (ModuleCat ℤ) ℕ :=
  C.restriction shiftEmb

/-- The objects of the reindexed complex. -/
theorem dsh_X (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) : (dsh C).X n = C.X (4 + n) :=
  HomologicalComplex.restriction_X C shiftEmb n

/-- The differentials of the reindexed complex. -/
theorem dsh_d (C : ChainComplex (ModuleCat ℤ) ℕ) (i j : ℕ) :
    (dsh C).d i j = C.d (4 + i) (4 + j) :=
  HomologicalComplex.restriction_d C shiftEmb i j

/-- **The homology of the reindexed complex is the shifted homology** (as an explicit
isomorphism, so that later statements may refer to it). -/
noncomputable def dshHomologyIso (C : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    (dsh C).homology (k + 1) ≅ C.homology (k + 5) := by
  have h : (C.restriction shiftEmb).homology (k + 1) ≅ C.homology (4 + (k + 1)) :=
    C.restrictionHomologyIso shiftEmb (k + 2) (k + 1) k
      (show (ComplexShape.down ℕ).prev (k + 1) = k + 2 from
        (ComplexShape.down ℕ).prev_eq' (by simp only [ComplexShape.down_Rel] <;> omega))
      (show (ComplexShape.down ℕ).next (k + 1) = k from
        (ComplexShape.down ℕ).next_eq' (by simp only [ComplexShape.down_Rel] <;> omega))
      (i' := 4 + (k + 2)) (j' := 4 + (k + 1)) (k' := 4 + k)
      (by simp only [shiftEmb]) (by simp only [shiftEmb]) (by simp only [shiftEmb])
      (show (ComplexShape.down ℕ).prev (4 + (k + 1)) = 4 + (k + 2) from
        (ComplexShape.down ℕ).prev_eq' (by simp only [ComplexShape.down_Rel] <;> omega))
      (show (ComplexShape.down ℕ).next (4 + (k + 1)) = 4 + k from
        (ComplexShape.down ℕ).next_eq' (by simp only [ComplexShape.down_Rel] <;> omega))
  rw [show 4 + (k + 1) = k + 5 from by omega] at h
  exact (by simpa only [dsh] using h)

/-- The morphism of reindexed complexes induced by `f : C ⟶ D`. -/
def dshMap {C D : ChainComplex (ModuleCat ℤ) ℕ} (f : C ⟶ D) : dsh C ⟶ dsh D where
  f n := f.f (4 + n)
  comm' i j hij := f.comm (4 + i) (4 + j)

/-- Functoriality of `dshMap`. -/
theorem dshMap_comp {C D E : ChainComplex (ModuleCat ℤ) ℕ} (f : C ⟶ D) (g : D ⟶ E) :
    dshMap (f ≫ g) = dshMap f ≫ dshMap g :=
  HomologicalComplex.hom_ext _ _ (fun _ => rfl)

/-- `dshMap` preserves identities. -/
theorem dshMap_id (C : ChainComplex (ModuleCat ℤ) ℕ) : dshMap (𝟙 C) = 𝟙 (dsh C) :=
  HomologicalComplex.hom_ext _ _ (fun _ => rfl)

/-- `dshMap` preserves zero morphisms. -/
theorem dshMap_zero {C D : ChainComplex (ModuleCat ℤ) ℕ} :
    dshMap (0 : C ⟶ D) = 0 :=
  HomologicalComplex.hom_ext _ _ (fun n => (HomologicalComplex.zero_f C D (4+n)).trans
    (HomologicalComplex.zero_f (dsh C) (dsh D) n).symm)

/-- The short complex obtained by reindexing the three terms of a short complex. -/
def dshShort (S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)) :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (dshMap S.f) (dshMap S.g) (by rw [← dshMap_comp, S.zero, dshMap_zero])

/-- The first term of `dshShort`. -/
@[simp] theorem dshShort_X₁ (S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)) :
    (dshShort S).X₁ = dsh S.X₁ := rfl

/-- The second term of `dshShort`. -/
@[simp] theorem dshShort_X₂ (S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)) :
    (dshShort S).X₂ = dsh S.X₂ := rfl

/-- The third term of `dshShort`. -/
@[simp] theorem dshShort_X₃ (S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)) :
    (dshShort S).X₃ = dsh S.X₃ := rfl

/-- The first map of `dshShort`. -/
@[simp] theorem dshShort_f (S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)) :
    (dshShort S).f = dshMap S.f := rfl

/-- The second map of `dshShort`. -/
@[simp] theorem dshShort_g (S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)) :
    (dshShort S).g = dshMap S.g := rfl

/-! ## The explicit cap maps on the three terms of the relative Mayer–Vietoris sequence -/

/-- **The degreewise form of `biprod.map` for chain complexes.** -/
theorem biprod_map_f_comp_biprodXIso_hom {K L K' L' : ChainComplex (ModuleCat ℤ) ℕ}
    (f : K ⟶ K') (g : L ⟶ L') (n : ℕ) :
    (biprod.map f g).f n ≫ (HomologicalComplex.biprodXIso K' L' n).hom =
      (HomologicalComplex.biprodXIso K L n).hom ≫ biprod.map (f.f n) (g.f n) := by
  apply biprod.hom_ext
  · rw [Category.assoc, HomologicalComplex.biprodXIso_hom_fst, ← HomologicalComplex.comp_f,
      biprod.map_fst, HomologicalComplex.comp_f]
    conv_rhs => rw [Category.assoc, biprod.map_fst, ← Category.assoc,
      HomologicalComplex.biprodXIso_hom_fst]
  · rw [Category.assoc, HomologicalComplex.biprodXIso_hom_snd, ← HomologicalComplex.comp_f,
      biprod.map_snd, HomologicalComplex.comp_f]
    conv_rhs => rw [Category.assoc, biprod.map_snd, ← Category.assoc,
      HomologicalComplex.biprodXIso_hom_snd]

/-- `biprod.map` is compatible with composition. -/
theorem biprod_map_comp_map {K L K' L' K'' L'' : ModuleCat ℤ} (f : K ⟶ K') (g : L ⟶ L')
    (f' : K' ⟶ K'') (g' : L' ⟶ L'') :
    biprod.map f g ≫ biprod.map f' g' = biprod.map (f ≫ f') (g ≫ g') := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.map_fst, ← Category.assoc, biprod.map_fst, Category.assoc,
      biprod.map_fst]
  · rw [Category.assoc, biprod.map_snd, ← Category.assoc, biprod.map_snd, Category.assoc,
      biprod.map_snd]

/-- `biprod.map 0 0 = 0`. -/
theorem biprod_map_zero_zero {K L K' L' : ModuleCat ℤ} :
    biprod.map (0 : K ⟶ K') (0 : L ⟶ L') = 0 := by
  apply biprod.hom_ext <;> simp

/-- Postcomposition with a morphism out of a biproduct. -/
theorem biprod_lift_comp {A C D E : ModuleCat ℤ} (x : A ⟶ C) (f : C ⟶ D) (g : C ⟶ E) :
    x ≫ biprod.lift f g = biprod.lift (x ≫ f) (x ≫ g) := by
  apply biprod.hom_ext <;> simp

/-- `biprod.map` against `biprod.desc`. -/
theorem biprod_map_desc {A B C D E : ModuleCat ℤ} (f : A ⟶ C) (g : B ⟶ D)
    (h : C ⟶ E) (k : D ⟶ E) :
    biprod.map f g ≫ biprod.desc h k = biprod.desc (f ≫ h) (g ≫ k) := by
  apply biprod.hom_ext'
  · simp only [biprod.inl_map_assoc, biprod.inl_desc]
  · simp only [biprod.inr_map_assoc, biprod.inr_desc]

/-- **The degreewise component of a cokernel projection is an epimorphism**: it differs from
`cokernel.π (f.f n)` by the isomorphism `cokernelComponentIso`. -/
theorem epi_cokernel_π_f {K L : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L) (n : ℕ) :
    Epi ((cokernel.π f).f n) := by
  have h : (cokernel.π f).f n = cokernel.π (f.f n) ≫ (cokernelComponentIso f n).inv := by
    rw [← cancel_mono (cokernelComponentIso f n).hom, cokernelComponentIso_canon, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [h]
  infer_instance

variable {X : TopCat}

/-- **The cap product with a relative `4`-cocycle, descended to the relative complex
`C^{U,V}(X,A)`** (the top term of the relative Mayer–Vietoris sequence). -/
noncomputable def capTopCanon (A U V : Set X) (α : relKern ℤ X A 4) (m : ℕ) :
    (relMVTopC X A U V).X (4 + m) ⟶ (smallChains U V).X m :=
  (cokernelComponentIso (smallInToSmall U V A) (4 + m)).hom ≫
    cokernel.desc ((smallInToSmall U V A).f (4 + m)) (capSub (smallSubcomplex U V) 4 m α.1)
      (smallInToSmall_capSub_eq_zero X U V A 4 m α.1 α.2)

/-- **The computation rule of `capTopCanon`**: composed with the cokernel projection it is the cap
product with the underlying cochain. -/
theorem capTopCanon_spec (A U V : Set X) (α : relKern ℤ X A 4) (m : ℕ) :
    (cokernel.π (smallInToSmall U V A)).f (4 + m) ≫ capTopCanon A U V α m =
      capSub (smallSubcomplex U V) 4 m α.1 := by
  rw [capTopCanon, ← Category.assoc, cokernelComponentIso_canon, cokernel.π_desc]

/-- **The cap product with a relative `4`-cocycle, descended to the first term
`C^{U,V}(U ∩ V, U ∩ V ∩ A)` of the relative Mayer–Vietoris sequence.** -/
noncomputable def capUvCanon (A U V : Set X) (α : relKern ℤ X A 4) (m : ℕ) :
    (relMVUV X A U V).X (4 + m) ⟶ (smallInChains U V (U ∩ V)).X m :=
  (cokernelComponentIso (subInclChain U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V))
      (4 + m)).hom ≫
    cokernel.desc ((subInclChain U V (Set.inter_subset_left :
        U ∩ V ∩ A ⊆ U ∩ V)).f (4 + m))
      (capSub (smallInSubcomplex U V (U ∩ V)) 4 m α.1)
      (subInclChain_capSub_eq_zero X U V (U ∩ V) (U ∩ V ∩ A) Set.inter_subset_left 4 m α.1
        (relKern_mono (Set.inter_subset_right : U ∩ V ∩ A ⊆ A) α.2))

/-- **The computation rule of `capUvCanon`.** -/
theorem capUvCanon_spec (A U V : Set X) (α : relKern ℤ X A 4) (m : ℕ) :
    (cokernel.π (subInclChain U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V))).f (4 + m) ≫
        capUvCanon A U V α m = capSub (smallInSubcomplex U V (U ∩ V)) 4 m α.1 := by
  rw [capUvCanon, ← Category.assoc, cokernelComponentIso_canon, cokernel.π_desc]

/-- **The cap product with a relative `4`-cocycle, descended to the middle term of the relative
Mayer–Vietoris sequence**, with values in the *raw biproduct* of the two summands. -/
noncomputable def capMidCanon0 (A U V : Set X) (α : relKern ℤ X A 4) (m : ℕ) :
    (cruxMid X A U V).X (4 + m) ⟶
      ((smallInChains U V U).X m ⊞ (smallInChains U V V).X m) :=
  (cokernelComponentIso (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A)) (4 + m)).hom ≫
    cokernel.desc ((biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A)).f (4 + m))
      ((HomologicalComplex.biprodXIso (smallInChains U V U) (smallInChains U V V)
          (4 + m)).hom ≫
        biprod.map (capSub (smallInSubcomplex U V U) 4 m α.1)
          (capSub (smallInSubcomplex U V V) 4 m α.1)) (by
      rw [← Category.assoc, biprod_map_f_comp_biprodXIso_hom]
      simp only [relMVτ₂U, relMVτ₂V]
      rw [Category.assoc, biprod_map_comp_map,
        subInclChain_capSub_eq_zero X U V U (U ∩ A) Set.inter_subset_left 4 m α.1
          (relKern_mono (Set.inter_subset_right : U ∩ A ⊆ A) α.2),
        subInclChain_capSub_eq_zero X U V V (V ∩ A) Set.inter_subset_left 4 m α.1
          (relKern_mono (Set.inter_subset_right : V ∩ A ⊆ A) α.2),
        biprod_map_zero_zero, comp_zero])

/-- **The computation rule of `capMidCanon0`.** -/
theorem capMidCanon0_spec (A U V : Set X) (α : relKern ℤ X A 4) (m : ℕ) :
    (cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))).f (4 + m) ≫
        capMidCanon0 A U V α m =
      (HomologicalComplex.biprodXIso (smallInChains U V U) (smallInChains U V V)
          (4 + m)).hom ≫
        biprod.map (capSub (smallInSubcomplex U V U) 4 m α.1)
          (capSub (smallInSubcomplex U V V) 4 m α.1) := by
  rw [capMidCanon0, ← Category.assoc, cokernelComponentIso_canon, cokernel.π_desc]

/-- **The cap product with a relative `4`-cocycle, descended to the middle term of the relative
Mayer–Vietoris sequence.** -/
noncomputable def capMidCanon (A U V : Set X) (α : relKern ℤ X A 4) (m : ℕ) :
    (cruxMid X A U V).X (4 + m) ⟶ (smallInChains U V U ⊞ smallInChains U V V).X m :=
  capMidCanon0 A U V α m ≫
    (HomologicalComplex.biprodXIso (smallInChains U V U) (smallInChains U V V) m).inv

/-- **The computation rule of `capMidCanon`.** -/
theorem capMidCanon_spec (A U V : Set X) (α : relKern ℤ X A 4) (m : ℕ) :
    (cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))).f (4 + m) ≫
        capMidCanon A U V α m =
      (HomologicalComplex.biprodXIso (smallInChains U V U) (smallInChains U V V)
          (4 + m)).hom ≫
        biprod.map (capSub (smallInSubcomplex U V U) 4 m α.1)
          (capSub (smallInSubcomplex U V V) 4 m α.1) ≫
        (HomologicalComplex.biprodXIso (smallInChains U V U) (smallInChains U V V) m).inv := by
  rw [capMidCanon, ← Category.assoc, capMidCanon0_spec, Category.assoc]

/-- `biprod.lift` against `biprod.map`. -/
theorem biprod_lift_map {A C D E F : ModuleCat ℤ} (a : A ⟶ C) (b : A ⟶ D)
    (f : C ⟶ E) (g : D ⟶ F) :
    biprod.lift a b ≫ biprod.map f g = biprod.lift (a ≫ f) (b ≫ g) := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.map_fst, ← Category.assoc, biprod.lift_fst, biprod.lift_fst]
  · rw [Category.assoc, biprod.map_snd, ← Category.assoc, biprod.lift_snd, biprod.lift_snd]

/-! ## The cap product against the Mayer–Vietoris maps -/

/-- **The cap product is compatible with the first map of the relative Mayer–Vietoris
sequence** (Hatcher's Lemma 3.36 at the chain level). -/
theorem capUvCanon_mvLeft (A U V : Set X) (α : relKern ℤ X A 4) (m : ℕ) :
    capUvCanon A U V α m ≫ (mvLeftSmall U V).f m
      = (cruxF X A U V).f (4 + m) ≫ capMidCanon A U V α m := by
  set hU : U ∩ V ⊆ U := Set.inter_subset_left with hUdef
  set hV : U ∩ V ⊆ V := Set.inter_subset_right with hVdef
  set K := smallInChains U V U with hK
  set L := smallInChains U V V with hL
  -- the defining property of `cruxF`
  have hnat : (cokernel.π (subInclChain U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V))).f
        (4 + m) ≫ (cruxF X A U V).f (4 + m)
      = (mvLeftSmall U V).f (4 + m) ≫
        (cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))).f (4 + m) := by
    have h := congrArg (fun φ : smallInChains U V (U ∩ V) ⟶ cruxMid X A U V => φ.f (4 + m))
      (cokernel_π_cokernelMap (relMVτ₁ U V A)
        (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A)) (mvLeftSmallA U V A)
        (mvLeftSmall U V) (relMVv U V A).comm₁₂)
    simpa only [cruxF, relMVv, relMVτ₁, HomologicalComplex.comp_f] using h
  have hlift : (mvLeftSmall U V).f (4 + m) ≫ (HomologicalComplex.biprodXIso K L (4 + m)).hom
      = biprod.lift ((subInclChain U V hU).f (4 + m)) ((subInclChain U V hV).f (4 + m)) := by
    simpa only [mvLeftSmall] using
      biprod_lift_f_comp_biprodXIso_hom (subInclChain U V hU) (subInclChain U V hV) (4 + m)
  have hdesc : (mvLeftSmall U V).f m ≫ (HomologicalComplex.biprodXIso K L m).hom
      = biprod.lift ((subInclChain U V hU).f m) ((subInclChain U V hV).f m) := by
    simpa only [mvLeftSmall] using
      biprod_lift_f_comp_biprodXIso_hom (subInclChain U V hU) (subInclChain U V hV) m
  have hcompU : capSub (smallInSubcomplex U V (U ∩ V)) 4 m α.1 ≫
      (subInclChain U V hU).f m
      = (subInclChain U V hU).f (4 + m) ≫ capSub (smallInSubcomplex U V U) 4 m α.1 :=
    capSub_comp_incl_sub (smallInSubcomplex U V (U ∩ V)) (smallInSubcomplex U V U)
      (smallInSubcomplex_mono hU) 4 m α.1
  have hcompV : capSub (smallInSubcomplex U V (U ∩ V)) 4 m α.1 ≫
      (subInclChain U V hV).f m
      = (subInclChain U V hV).f (4 + m) ≫ capSub (smallInSubcomplex U V V) 4 m α.1 :=
    capSub_comp_incl_sub (smallInSubcomplex U V (U ∩ V)) (smallInSubcomplex U V V)
      (smallInSubcomplex_mono hV) 4 m α.1
  have hL : (cokernel.π (subInclChain U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V))).f
        (4 + m) ≫ (capUvCanon A U V α m ≫ (mvLeftSmall U V).f m)
      = biprod.lift ((subInclChain U V hU).f (4 + m) ≫
            capSub (smallInSubcomplex U V U) 4 m α.1)
          ((subInclChain U V hV).f (4 + m) ≫
            capSub (smallInSubcomplex U V V) 4 m α.1)
          ≫ (HomologicalComplex.biprodXIso K L m).inv := by
    rw [← Category.assoc, capUvCanon_spec]
    rw [show (mvLeftSmall U V).f m = biprod.lift ((subInclChain U V hU).f m)
        ((subInclChain U V hV).f m) ≫ (HomologicalComplex.biprodXIso K L m).inv from by
      rw [← cancel_mono (HomologicalComplex.biprodXIso K L m).hom]
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact hdesc]
    rw [← Category.assoc, biprod_lift_comp]
    rw [hcompU, hcompV]
  have hR : (cokernel.π (subInclChain U V (Set.inter_subset_left : U ∩ V ∩ A ⊆ U ∩ V))).f
        (4 + m) ≫ ((cruxF X A U V).f (4 + m) ≫ capMidCanon A U V α m)
      = biprod.lift ((subInclChain U V hU).f (4 + m) ≫
            capSub (smallInSubcomplex U V U) 4 m α.1)
          ((subInclChain U V hV).f (4 + m) ≫
            capSub (smallInSubcomplex U V V) 4 m α.1)
          ≫ (HomologicalComplex.biprodXIso K L m).inv := by
    rw [← Category.assoc, hnat, Category.assoc, capMidCanon_spec]
    rw [← Category.assoc, hlift, ← Category.assoc, biprod_lift_map]
  haveI hπ : Epi ((cokernel.π (subInclChain U V (Set.inter_subset_left :
      U ∩ V ∩ A ⊆ U ∩ V))).f (4 + m)) :=
    epi_cokernel_π_f _ (4 + m)
  refine (cancel_epi ((cokernel.π (subInclChain U V (Set.inter_subset_left :
      U ∩ V ∩ A ⊆ U ∩ V))).f (4 + m))).mp ?_
  rw [hL, hR]

/-! ## Naturality of the degreewise biproduct isomorphism for the differentials -/

/-- **The degreewise biproduct isomorphism is natural for the differentials.** -/
theorem biprodXIso_hom_d {K L : ChainComplex (ModuleCat ℤ) ℕ} (i j : ℕ) :
    (HomologicalComplex.biprodXIso K L i).hom ≫ biprod.map (K.d i j) (L.d i j) =
      (K ⊞ L).d i j ≫ (HomologicalComplex.biprodXIso K L j).hom := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.map_fst, ← Category.assoc, HomologicalComplex.biprodXIso_hom_fst,
      (biprod.fst : K ⊞ L ⟶ K).comm i j, Category.assoc,
      HomologicalComplex.biprodXIso_hom_fst]
  · rw [Category.assoc, biprod.map_snd, ← Category.assoc, HomologicalComplex.biprodXIso_hom_snd,
      (biprod.snd : K ⊞ L ⟶ L).comm i j, Category.assoc,
      HomologicalComplex.biprodXIso_hom_snd]

/-- **The inverse degreewise biproduct isomorphism is natural for the differentials.** -/
theorem biprodXIso_inv_d {K L : ChainComplex (ModuleCat ℤ) ℕ} (i j : ℕ) :
    (HomologicalComplex.biprodXIso K L i).inv ≫ (K ⊞ L).d i j =
      biprod.map (K.d i j) (L.d i j) ≫ (HomologicalComplex.biprodXIso K L j).inv := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, HomologicalComplex.inl_biprodXIso_inv,
      (biprod.inl : K ⟶ K ⊞ L).comm i j, ← Category.assoc, biprod.inl_map, Category.assoc,
      ← HomologicalComplex.inl_biprodXIso_inv]
  · rw [← Category.assoc, HomologicalComplex.inr_biprodXIso_inv,
      (biprod.inr : L ⟶ K ⊞ L).comm i j, ← Category.assoc, biprod.inr_map, Category.assoc,
      ← HomologicalComplex.inr_biprodXIso_inv]

/-! ## The chain-map property of the cap maps -/

/-- The underlying cochain of a relative cocycle is an absolute cocycle. -/
theorem cochainDiff_eq_zero_of_relDiffLM_eq_zero (A U V : Set X) (α : relKern ℤ X A 4)
    (hα : relDiffLM ℤ X A 4 α = 0) :
    cochainDiff ℤ (TopCat.toSSet.obj X) α.1 = 0 := by
  have h := congrArg (fun x => x.1) hα
  rw [relDiffLM_coe_cochainDiff] at h
  simpa using h

/-- **The cap map on the top term is a chain map** (with the degree shift `dsh`). -/
theorem capTopCanon_comm (A U V : Set X) (α : relKern ℤ X A 4)
    (hα : relDiffLM ℤ X A 4 α = 0) (m : ℕ) :
    (relMVTopC X A U V).d (4 + m + 1) (4 + m) ≫ capTopCanon A U V α m
      = capTopCanon A U V α (m + 1) ≫ (smallChains U V).d (m + 1) m := by
  have hc := cochainDiff_eq_zero_of_relDiffLM_eq_zero (X := X) A U V α hα
  haveI hπ : Epi ((cokernel.π (smallInToSmall U V A)).f (4 + m + 1)) :=
    epi_cokernel_π_f _ (4 + m + 1)
  refine (cancel_epi ((cokernel.π (smallInToSmall U V A)).f (4 + m + 1))).mp ?_
  rw [← Category.assoc,
    (cokernel.π (smallInToSmall U V A)).comm (4 + m + 1) (4 + m),
    Category.assoc, capTopCanon_spec]
  conv_rhs => rw [← Category.assoc,
    show (cokernel.π (smallInToSmall U V A)).f (4 + m + 1)
      = (cokernel.π (smallInToSmall U V A)).f (4 + (m + 1)) from rfl,
    capTopCanon_spec]
  exact (capSub_comm_d_of_even (smallSubcomplex U V) 4 m (by norm_num) α.1 hc).symm

/-- **The cap map on the first term is a chain map** (with the degree shift `dsh`). -/
theorem capUvCanon_comm (A U V : Set X) (α : relKern ℤ X A 4)
    (hα : relDiffLM ℤ X A 4 α = 0) (m : ℕ) :
    (relMVUV X A U V).d (4 + m + 1) (4 + m) ≫ capUvCanon A U V α m
      = capUvCanon A U V α (m + 1) ≫ (smallInChains U V (U ∩ V)).d (m + 1) m := by
  have hc := cochainDiff_eq_zero_of_relDiffLM_eq_zero (X := X) A U V α hα
  haveI hπ : Epi ((cokernel.π (subInclChain U V (Set.inter_subset_left :
      U ∩ V ∩ A ⊆ U ∩ V))).f (4 + m + 1)) :=
    epi_cokernel_π_f _ (4 + m + 1)
  refine (cancel_epi ((cokernel.π (subInclChain U V (Set.inter_subset_left :
      U ∩ V ∩ A ⊆ U ∩ V))).f (4 + m + 1))).mp ?_
  rw [← Category.assoc,
    (cokernel.π (subInclChain U V (Set.inter_subset_left :
      U ∩ V ∩ A ⊆ U ∩ V))).comm (4 + m + 1) (4 + m),
    Category.assoc, capUvCanon_spec]
  conv_rhs => rw [← Category.assoc,
    show (cokernel.π (subInclChain U V (Set.inter_subset_left :
        U ∩ V ∩ A ⊆ U ∩ V))).f (4 + m + 1)
      = (cokernel.π (subInclChain U V (Set.inter_subset_left :
        U ∩ V ∩ A ⊆ U ∩ V))).f (4 + (m + 1)) from rfl,
    capUvCanon_spec]
  exact (capSub_comm_d_of_even (smallInSubcomplex U V (U ∩ V)) 4 m (by norm_num) α.1 hc).symm


/-- **The cap map on the middle term is a chain map with values in the raw biproduct** (with the
degree shift `dsh`). -/
theorem capMidCanon0_comm (A U V : Set X) (α : relKern ℤ X A 4)
    (hα : relDiffLM ℤ X A 4 α = 0) (m : ℕ) :
    (cruxMid X A U V).d (4 + m + 1) (4 + m) ≫ capMidCanon0 A U V α m
      = capMidCanon0 A U V α (m + 1) ≫
        biprod.map ((smallInChains U V U).d (m + 1) m) ((smallInChains U V V).d (m + 1) m) := by
  have hc := cochainDiff_eq_zero_of_relDiffLM_eq_zero (X := X) A U V α hα
  have hU₀ := capSub_comm_d_of_even (smallInSubcomplex U V U) 4 m (by norm_num) α.1 hc
  have hV₀ := capSub_comm_d_of_even (smallInSubcomplex U V V) 4 m (by norm_num) α.1 hc
  have hU : (smallInChains U V U).d (4 + m + 1) (4 + m) ≫
      capSub (smallInSubcomplex U V U) 4 m α.1
      = capSub (smallInSubcomplex U V U) 4 (m + 1) α.1 ≫
        (smallInChains U V U).d (m + 1) m := hU₀.symm
  have hV : (smallInChains U V V).d (4 + m + 1) (4 + m) ≫
      capSub (smallInSubcomplex U V V) 4 m α.1
      = capSub (smallInSubcomplex U V V) 4 (m + 1) α.1 ≫
        (smallInChains U V V).d (m + 1) m := hV₀.symm
  have hspec : (cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))).f (4 + m + 1) ≫
      capMidCanon0 A U V α (m + 1) =
      (HomologicalComplex.biprodXIso (smallInChains U V U) (smallInChains U V V)
        (4 + m + 1)).hom ≫
        biprod.map (capSub (smallInSubcomplex U V U) 4 (m + 1) α.1)
          (capSub (smallInSubcomplex U V V) 4 (m + 1) α.1) :=
    capMidCanon0_spec A U V α (m + 1)
  have hconj : (smallInChains U V U ⊞ smallInChains U V V).d (4 + m + 1) (4 + m) ≫
      (HomologicalComplex.biprodXIso (smallInChains U V U) (smallInChains U V V)
        (4 + m)).hom
      = (HomologicalComplex.biprodXIso (smallInChains U V U) (smallInChains U V V)
          (4 + m + 1)).hom ≫
        biprod.map ((smallInChains U V U).d (4 + m + 1) (4 + m))
          ((smallInChains U V V).d (4 + m + 1) (4 + m)) :=
    (biprodXIso_hom_d (K := smallInChains U V U) (L := smallInChains U V V)
      (4 + m + 1) (4 + m)).symm
  haveI hπ : Epi ((cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))).f
    (4 + m + 1)) := epi_cokernel_π_f _ (4 + m + 1)
  refine (cancel_epi ((cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))).f
    (4 + m + 1))).mp ?_
  have hL : (cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))).f (4 + m + 1) ≫
      ((cruxMid X A U V).d (4 + m + 1) (4 + m) ≫ capMidCanon0 A U V α m)
      = (HomologicalComplex.biprodXIso (smallInChains U V U) (smallInChains U V V)
            (4 + m + 1)).hom ≫
          biprod.map (capSub (smallInSubcomplex U V U) 4 (m + 1) α.1 ≫
              (smallInChains U V U).d (m + 1) m)
            (capSub (smallInSubcomplex U V V) 4 (m + 1) α.1 ≫
              (smallInChains U V V).d (m + 1) m) := by
    rw [← Category.assoc,
      (cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))).comm (4 + m + 1) (4 + m),
      Category.assoc, capMidCanon0_spec]
    rw [← Category.assoc, hconj, Category.assoc, biprod_map_comp_map]
    rw [hU, hV]
  have hR : (cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))).f (4 + m + 1) ≫
      (capMidCanon0 A U V α (m + 1) ≫
        biprod.map ((smallInChains U V U).d (m + 1) m) ((smallInChains U V V).d (m + 1) m))
      = (HomologicalComplex.biprodXIso (smallInChains U V U) (smallInChains U V V)
            (4 + m + 1)).hom ≫
          biprod.map (capSub (smallInSubcomplex U V U) 4 (m + 1) α.1 ≫
              (smallInChains U V U).d (m + 1) m)
            (capSub (smallInSubcomplex U V V) 4 (m + 1) α.1 ≫
              (smallInChains U V V).d (m + 1) m) := by
    rw [← Category.assoc, hspec, Category.assoc, biprod_map_comp_map]
  rw [hL, hR]


/-- **The cap map on the middle term is a chain map** (with the degree shift `dsh`). -/
theorem capMidCanon_comm (A U V : Set X) (α : relKern ℤ X A 4)
    (hα : relDiffLM ℤ X A 4 α = 0) (m : ℕ) :
    (cruxMid X A U V).d (4 + m + 1) (4 + m) ≫ capMidCanon A U V α m
      = capMidCanon A U V α (m + 1) ≫
        (smallInChains U V U ⊞ smallInChains U V V).d (m + 1) m := by
  have h0 := capMidCanon0_comm A U V α hα m
  have key : (HomologicalComplex.biprodXIso (smallInChains U V U) (smallInChains U V V)
        (m + 1)).inv ≫ (smallInChains U V U ⊞ smallInChains U V V).d (m + 1) m
      = biprod.map ((smallInChains U V U).d (m + 1) m) ((smallInChains U V V).d (m + 1) m) ≫
        (HomologicalComplex.biprodXIso (smallInChains U V U) (smallInChains U V V) m).inv :=
    biprodXIso_inv_d (K := smallInChains U V U) (L := smallInChains U V V) (m + 1) m
  rw [show capMidCanon A U V α m = capMidCanon0 A U V α m ≫
      (HomologicalComplex.biprodXIso (smallInChains U V U) (smallInChains U V V) m).inv
      from rfl]
  rw [← Category.assoc, h0, Category.assoc]
  conv_rhs => rw [show capMidCanon A U V α (m + 1) = capMidCanon0 A U V α (m + 1) ≫
      (HomologicalComplex.biprodXIso (smallInChains U V U) (smallInChains U V V) (m + 1)).inv
      from rfl]
  conv_rhs => rw [Category.assoc, key]

/-- **The cap product is compatible with the second map of the relative Mayer–Vietoris
sequence.** -/
theorem capMidCanon_mvRight (A U V : Set X) (α : relKern ℤ X A 4) (m : ℕ) :
    capMidCanon A U V α m ≫ (mvRightSmall U V).f m
      = (cruxG X A U V).f (4 + m) ≫ capTopCanon A U V α m := by
  set K := smallInChains U V U with hK
  set L := smallInChains U V V with hL
  have hnatG : (cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))).f (4 + m) ≫
        (cruxG X A U V).f (4 + m)
      = (mvRightSmall U V).f (4 + m) ≫ (cokernel.π (smallInToSmall U V A)).f (4 + m) := by
    have h := congrArg (fun φ : (smallInChains U V U ⊞ smallInChains U V V) ⟶
        relMVTopC X A U V => φ.f (4 + m))
      (cokernel_π_cokernelMap (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))
        (smallInToSmall U V A) (mvRightSmallA U V A) (mvRightSmall U V)
        (relMVv U V A).comm₂₃)
    simpa only [cruxG, relMVv, relMVτ₃, HomologicalComplex.comp_f] using h
  have hdescR : (HomologicalComplex.biprodXIso K L m).inv ≫ (mvRightSmall U V).f m
      = biprod.desc ((smallInToSmall U V U).f m) ((-(smallInToSmall U V V)).f m) := by
    simpa only [mvRightSmall] using
      biprodXIso_inv_comp_desc_f (smallInToSmall U V U) (-(smallInToSmall U V V)) m
  have hdescR₄ : (HomologicalComplex.biprodXIso K L (4 + m)).inv ≫ (mvRightSmall U V).f (4 + m)
      = biprod.desc ((smallInToSmall U V U).f (4 + m)) ((-(smallInToSmall U V V)).f (4 + m)) := by
    simpa only [mvRightSmall] using
      biprodXIso_inv_comp_desc_f (smallInToSmall U V U) (-(smallInToSmall U V V)) (4 + m)
  have hdescR4 : (mvRightSmall U V).f (4 + m) =
      (HomologicalComplex.biprodXIso K L (4 + m)).hom ≫
        biprod.desc ((smallInToSmall U V U).f (4 + m))
          ((-(smallInToSmall U V V)).f (4 + m)) := by
    calc (mvRightSmall U V).f (4 + m)
        = ((HomologicalComplex.biprodXIso K L (4 + m)).hom ≫
              (HomologicalComplex.biprodXIso K L (4 + m)).inv) ≫
              (mvRightSmall U V).f (4 + m) := by
            rw [Iso.hom_inv_id, Category.id_comp]
      _ = (HomologicalComplex.biprodXIso K L (4 + m)).hom ≫
            ((HomologicalComplex.biprodXIso K L (4 + m)).inv ≫
              (mvRightSmall U V).f (4 + m)) := by
            rw [Category.assoc]
      _ = (HomologicalComplex.biprodXIso K L (4 + m)).hom ≫
            biprod.desc ((smallInToSmall U V U).f (4 + m))
              ((-(smallInToSmall U V V)).f (4 + m)) := by rw [hdescR₄]
  have hcompU' : capSub (smallInSubcomplex U V U) 4 m α.1 ≫ (smallInToSmall U V U).f m
      = (smallInToSmall U V U).f (4 + m) ≫ capSub (smallSubcomplex U V) 4 m α.1 :=
    capSub_comp_incl_sub (smallInSubcomplex U V U) (smallSubcomplex U V)
      (smallInSubcomplex_le U V U) 4 m α.1
  have hcompV' : capSub (smallInSubcomplex U V V) 4 m α.1 ≫ (smallInToSmall U V V).f m
      = (smallInToSmall U V V).f (4 + m) ≫ capSub (smallSubcomplex U V) 4 m α.1 :=
    capSub_comp_incl_sub (smallInSubcomplex U V V) (smallSubcomplex U V)
      (smallInSubcomplex_le U V V) 4 m α.1
  have hcompV'' : capSub (smallInSubcomplex U V V) 4 m α.1 ≫
      ((-(smallInToSmall U V V)).f m)
      = -((smallInToSmall U V V).f (4 + m) ≫ capSub (smallSubcomplex U V) 4 m α.1) := by
    rw [show (-(smallInToSmall U V V)).f m = -((smallInToSmall U V V).f m) from rfl]
    rw [Preadditive.comp_neg, hcompV']
  have hnegV : ((-(smallInToSmall U V V)).f (4 + m)) ≫ capSub (smallSubcomplex U V) 4 m α.1
      = -((smallInToSmall U V V).f (4 + m) ≫ capSub (smallSubcomplex U V) 4 m α.1) := by
    rw [show (-(smallInToSmall U V V)).f (4 + m) = -((smallInToSmall U V V).f (4 + m))
      from rfl]
    rw [Preadditive.neg_comp]
  have hspec : (cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))).f (4 + m) ≫
      capMidCanon A U V α m =
      (HomologicalComplex.biprodXIso K L (4 + m)).hom ≫
        biprod.map (capSub (smallInSubcomplex U V U) 4 m α.1)
          (capSub (smallInSubcomplex U V V) 4 m α.1) ≫
        (HomologicalComplex.biprodXIso K L m).inv :=
    capMidCanon_spec A U V α m
  haveI hπ : Epi ((cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))).f (4 + m)) :=
    epi_cokernel_π_f _ (4 + m)
  refine (cancel_epi ((cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))).f
    (4 + m))).mp ?_
  have hL : (cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))).f (4 + m) ≫
      (capMidCanon A U V α m ≫ (mvRightSmall U V).f m)
      = (HomologicalComplex.biprodXIso K L (4 + m)).hom ≫
          biprod.desc ((smallInToSmall U V U).f (4 + m) ≫ capSub (smallSubcomplex U V) 4 m α.1)
            (-((smallInToSmall U V V).f (4 + m) ≫ capSub (smallSubcomplex U V) 4 m α.1)) := by
    rw [← Category.assoc, hspec]
    rw [Category.assoc, Category.assoc, hdescR, biprod_map_desc]
    rw [hcompU', hcompV'']
  have hR : (cokernel.π (biprod.map (relMVτ₂U U V A) (relMVτ₂V U V A))).f (4 + m) ≫
      ((cruxG X A U V).f (4 + m) ≫ capTopCanon A U V α m)
      = (HomologicalComplex.biprodXIso K L (4 + m)).hom ≫
          biprod.desc ((smallInToSmall U V U).f (4 + m) ≫ capSub (smallSubcomplex U V) 4 m α.1)
            (-((smallInToSmall U V V).f (4 + m) ≫ capSub (smallSubcomplex U V) 4 m α.1)) := by
    rw [← Category.assoc, hnatG, Category.assoc, capTopCanon_spec]
    rw [hdescR4]
    rw [Category.assoc, biprod_desc_comp]
    rw [hnegV]
  rw [hL, hR]


/-! ## Packaging the cap product as a morphism of the two Mayer–Vietoris short exact sequences -/

/-- The small-chains Mayer–Vietoris short complex of the cover `U ∪ V`. -/
noncomputable def mvSmallSES (U V : Set X) : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (mvLeftSmall U V) (mvRightSmall U V) (mvCompSmall U V)

/-- **The cap product as a chain map `dsh C^{U,V}(U∩V,U∩V∩A) ⟶ C^{U,V}(U∩V)`.** -/
noncomputable def capUvChain (A U V : Set X) (α : relKern ℤ X A 4)
    (hα : relDiffLM ℤ X A 4 α = 0) :
    dsh (relMVUV X A U V) ⟶ smallInChains U V (U ∩ V) where
  f m := capUvCanon A U V α m
  comm' i j hij := by
    rw [show i = j + 1 from hij.symm]
    exact (capUvCanon_comm A U V α hα j).symm

/-- **The cap product as a chain map `dsh (cruxMid) ⟶ C^{U,V}(U) ⊞ C^{U,V}(V)`.** -/
noncomputable def capMidChain (A U V : Set X) (α : relKern ℤ X A 4)
    (hα : relDiffLM ℤ X A 4 α = 0) :
    dsh (cruxMid X A U V) ⟶ (smallInChains U V U ⊞ smallInChains U V V) where
  f m := capMidCanon A U V α m
  comm' i j hij := by
    rw [show i = j + 1 from hij.symm]
    exact (capMidCanon_comm A U V α hα j).symm

/-- **The cap product as a chain map `dsh C^{U,V}(X,A) ⟶ C^{U,V}(X)`.** -/
noncomputable def capTopChain (A U V : Set X) (α : relKern ℤ X A 4)
    (hα : relDiffLM ℤ X A 4 α = 0) :
    dsh (relMVTopC X A U V) ⟶ smallChains U V where
  f m := capTopCanon A U V α m
  comm' i j hij := by
    rw [show i = j + 1 from hij.symm]
    exact (capTopCanon_comm A U V α hα j).symm

/-- **The reindexed relative Mayer–Vietoris short complex is short exact.** -/
theorem dshShort_cruxShort_shortExact (A U V : Set X) :
    (dshShort (cruxShort X A U V)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => ?_)
  have h := (HomologicalComplex.shortExact_iff_degreewise_shortExact
    (cruxShort X A U V)).mp (cruxShort_shortExact X A U V) (4 + n)
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)) h

/-- **The cap product with a relative `4`-cocycle is a morphism of short exact sequences**
from the reindexed relative Mayer–Vietoris sequence to the small-chains one. -/
noncomputable def capSES (A U V : Set X) (α : relKern ℤ X A 4)
    (hα : relDiffLM ℤ X A 4 α = 0) :
    dshShort (cruxShort X A U V) ⟶ mvSmallSES U V :=
  ShortComplex.homMk (capUvChain A U V α hα) (capMidChain A U V α hα) (capTopChain A U V α hα)
    (by
      apply HomologicalComplex.hom_ext
      intro m
      simpa only [HomologicalComplex.hom_ext_iff, HomologicalComplex.comp_f, capUvChain,
        capMidChain, dshMap, dshShort, cruxShort, mvSmallSES] using
        capUvCanon_mvLeft A U V α m)
    (by
      apply HomologicalComplex.hom_ext
      intro m
      simpa only [HomologicalComplex.hom_ext_iff, HomologicalComplex.comp_f, capMidChain,
        capTopChain, dshMap, dshShort, cruxShort, mvSmallSES] using
        capMidCanon_mvRight A U V α m)

/-- **The transgression identity** (Hatcher's Lemma 3.36): the cap product with a relative
`4`-cocycle commutes with the Mayer–Vietoris connecting maps.  This is the naturality of the
connecting map of a short exact sequence under the morphism `capSES`. -/
theorem transgression_capUvCanon (A U V : Set X) (α : relKern ℤ X A 4)
    (hα : relDiffLM ℤ X A 4 α = 0) (m : ℕ) :
    (dshShort_cruxShort_shortExact A U V).δ (m + 1) m
        (by simp only [ComplexShape.down_Rel]) ≫
        HomologicalComplex.homologyMap (capUvChain A U V α hα) m
      = HomologicalComplex.homologyMap (capTopChain A U V α hα) (m + 1) ≫
        (mvSmall_shortExact U V).δ (m + 1) m (by simp only [ComplexShape.down_Rel]) :=
  HomologicalComplex.HomologySequence.δ_naturality (capSES A U V α hα)
    (dshShort_cruxShort_shortExact A U V) (mvSmall_shortExact U V) (m + 1) m
    (by simp only [ComplexShape.down_Rel])



/-- **The homology of the reindexed complex, in the index form needed for the transgression
identity**: `(dsh C).homology m ≅ C.homology (4 + m)` for `1 ≤ m`. -/
noncomputable def dshHomologyIso_mulFour (C : ChainComplex (ModuleCat ℤ) ℕ) (m : ℕ)
    (hm : 1 ≤ m) : (dsh C).homology m ≅ C.homology (4 + m) := by
  have h : (C.restriction shiftEmb).homology m ≅ C.homology (4 + m) :=
    C.restrictionHomologyIso shiftEmb (m + 1) m (m - 1)
      (show (ComplexShape.down ℕ).prev m = m + 1 from
        (ComplexShape.down ℕ).prev_eq' (by simp only [ComplexShape.down_Rel] <;> omega))
      (show (ComplexShape.down ℕ).next m = m - 1 from
        (ComplexShape.down ℕ).next_eq' (by simp only [ComplexShape.down_Rel] <;> omega))
      (i' := 4 + (m + 1)) (j' := 4 + m) (k' := 4 + (m - 1))
      (by simp only [shiftEmb]) (by simp only [shiftEmb]) (by simp only [shiftEmb])
      (show (ComplexShape.down ℕ).prev (4 + m) = 4 + (m + 1) from
        (ComplexShape.down ℕ).prev_eq' (by simp only [ComplexShape.down_Rel] <;> omega))
      (show (ComplexShape.down ℕ).next (4 + m) = 4 + (m - 1) from
        (ComplexShape.down ℕ).next_eq' (by simp only [ComplexShape.down_Rel] <;> omega))
  exact (by simpa only [dsh] using h)

end

end Work.Cohomology
