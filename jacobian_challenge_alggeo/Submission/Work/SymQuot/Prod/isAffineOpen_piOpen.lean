/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The product open `Vⁿ ⊆ Xⁿ` is affine for `V ⊆ X` affine

For a `K`-scheme `X`, an open subscheme `V ⊆ X` and `n : ℕ`, the product open
`piOpen X V n ⊆ Xⁿ` (`Work.SymQuot.piOpen`) is the open subscheme of tuples all of whose
coordinates lie in `V`.  The main result here is that it is **affine** when `V` is affine:
it is the image of the open immersion `Vⁿ ⟶ Xⁿ`, and `Vⁿ` is a fibre product of affine
`K`-schemes, hence affine.

The proof is by induction on `n`.  The inductive step uses the identification
`(prod X n ⨯ X).left ≅ pullback (prod X n).hom X.hom` (associativity of the fibre product over
`Spec K`), the fact that a `pullback.map` of open immersions is an open immersion, and
`Scheme.Pullback.range_map` to identify its range with the "binary product open"
`fst ⁻¹ᵁ U ⊓ snd ⁻¹ᵁ W`, which is affine because it is the image of the open immersion
`U ×_S W ⟶ A ×_S B` and `U ×_S W` is a fibre product of affine schemes over the affine base `S`.
-/
import Mathlib
import Submission.Work.SymQuot.ProdOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


-- The fibred products appearing below are `Work.SymQuot.prod` (a `def`, not an `abbrev`), and the
-- statements mix it freely with `Limits.Pi`; ignoring transparency in definitional equality keeps
-- the `rw`/`simp` matching below robust.
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.Prod

variable {K : Type u} [Field K]

/-- **The binary product open.**  For affine opens `U ⊆ A` and `W ⊆ B` of schemes over an affine
base `S`, the open subscheme `fst ⁻¹ᵁ U ⊓ snd ⁻¹ᵁ W` of the fibre product `A ×_S B` is affine.

Indeed it is the range of the open immersion `pullback.map` from `U ×_S W` (a fibre product of
affine schemes over the affine base `S`, hence affine) and the computation of that range is
`Scheme.Pullback.range_map`. -/
private theorem isAffineOpen_inf_preimage {S A B : Scheme} [IsAffine S] (f : A ⟶ S) (g : B ⟶ S)
    {U : A.Opens} (hU : IsAffineOpen U) {W : B.Opens} (hW : IsAffineOpen W) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ W) := by
  haveI : IsAffine U := hU
  haveI : IsAffine W := hW
  let h : pullback (U.ι ≫ f) (W.ι ≫ g) ⟶ pullback f g :=
    pullback.map (U.ι ≫ f) (W.ι ≫ g) f g U.ι W.ι (𝟙 S) (by simp) (by simp)
  haveI : IsOpenImmersion h :=
    Scheme.pullback_map_isOpenImmersion (U.ι ≫ f) (W.ι ≫ g) f g U.ι W.ι (𝟙 S) (by simp) (by simp)
  have hrange : h.opensRange = pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ W := by
    ext x
    rw [Scheme.Hom.coe_opensRange]
    change x ∈ Set.range ⇑h ↔
      x ∈ (pullback.fst f g ⁻¹ᵁ U : Set _) ⊓ (pullback.snd f g ⁻¹ᵁ W : Set _)
    rw [Scheme.Pullback.range_map (U.ι ≫ f) (W.ι ≫ g) f g U.ι W.ι (𝟙 S) (by simp) (by simp)]
    simp [Set.mem_inter_iff, Set.mem_preimage, Scheme.Opens.range_ι]
  rw [← hrange]
  exact isAffineOpen_opensRange h

/-- `pullback (prod X n).hom X.hom`, regarded as an object of `Sch K` via its projection to
`Spec K`.  This is the "`Xⁿ ×_K X`" of the inductive step. -/
private noncomputable abbrev Zover (X : Work.GCBasics.Sch K) (n : ℕ) : Work.GCBasics.Sch K :=
  Over.mk (pullback.fst (Work.SymQuot.prod X n).hom X.hom ≫ (Work.SymQuot.prod X n).hom)

/-- The projection `Xⁿ⁺¹ ⟶ Xⁿ` forgetting the `0`-th coordinate. -/
private noncomputable def drop (X : Work.GCBasics.Sch K) (n : ℕ) :
    Work.SymQuot.prod X (n+1) ⟶ Work.SymQuot.prod X n :=
  Pi.lift (fun i : Fin n => Work.SymQuot.proj X (n+1) i.succ)

private theorem drop_proj (X : Work.GCBasics.Sch K) (n : ℕ) (i : Fin n) :
    drop X n ≫ Work.SymQuot.proj X n i = Work.SymQuot.proj X (n+1) i.succ :=
  Limits.Pi.lift_comp_π _ i

/-- The `0`-th projection `Xⁿ⁺¹ ⟶ X`, as a morphism out of the fibre product `Xⁿ ×_K X`. -/
private noncomputable def z0 (X : Work.GCBasics.Sch K) (n : ℕ) : Zover X n ⟶ X :=
  Over.homMk (pullback.snd (Work.SymQuot.prod X n).hom X.hom) (by rw [← pullback.condition]; rfl)

/-- The composite `Xⁿ ×_K X ⟶ Xⁿ ⟶ X` of the `i`-th projection, as a morphism out of `Xⁿ ×_K X`. -/
private noncomputable def zs (X : Work.GCBasics.Sch K) (n : ℕ) (i : Fin n) : Zover X n ⟶ X :=
  Over.homMk (pullback.fst (Work.SymQuot.prod X n).hom X.hom
    ≫ (Work.SymQuot.proj X n i).left) (by rw [Category.assoc, Over.w]; rfl)

private theorem z0_left (X : Work.GCBasics.Sch K) (n : ℕ) :
    (z0 X n).left = pullback.snd (Work.SymQuot.prod X n).hom X.hom :=
  Over.homMk_left _ _

private theorem zs_left (X : Work.GCBasics.Sch K) (n : ℕ) (i : Fin n) :
    (zs X n i).left = pullback.fst (Work.SymQuot.prod X n).hom X.hom
    ≫ (Work.SymQuot.proj X n i).left := Over.homMk_left _ _

/-- **`Xⁿ ×_K X ≅ Xⁿ⁺¹`**, the forward direction: the coordinates are the `i`-th coordinate of
`Xⁿ` (for `i.succ`) and the `X`-coordinate (for `0`). -/
private noncomputable def ΨO (X : Work.GCBasics.Sch K) (n : ℕ) :
    Zover X n ⟶ Work.SymQuot.prod X (n+1) :=
  Pi.lift (fun m : Fin (n+1) => Fin.cases (z0 X n) (fun i => zs X n i) m)

private theorem ΨO_proj_zero (X : Work.GCBasics.Sch K) (n : ℕ) :
    ΨO X n ≫ Work.SymQuot.proj X (n+1) 0 = z0 X n := by
  change Limits.Pi.lift (fun m : Fin (n+1) => Fin.cases (z0 X n) (fun i => zs X n i) m)
    ≫ Limits.Pi.π (fun _ : Fin (n+1) => X) 0 = z0 X n
  rw [Limits.Pi.lift_comp_π, Fin.cases_zero]

private theorem ΨO_proj_succ (X : Work.GCBasics.Sch K) (n : ℕ) (i : Fin n) :
    ΨO X n ≫ Work.SymQuot.proj X (n+1) i.succ = zs X n i := by
  change Limits.Pi.lift (fun m : Fin (n+1) => Fin.cases (z0 X n) (fun i => zs X n i) m)
    ≫ Limits.Pi.π (fun _ : Fin (n+1) => X) i.succ = zs X n i
  rw [Limits.Pi.lift_comp_π, Fin.cases_succ]

/-- **`Xⁿ ×_K X ≅ Xⁿ⁺¹`**, the inverse direction: the pair `(drop, 0-th projection)`. -/
private noncomputable def ΦO (X : Work.GCBasics.Sch K) (n : ℕ) :
    Work.SymQuot.prod X (n+1) ⟶ Zover X n :=
  Over.homMk (pullback.lift (drop X n).left (Work.SymQuot.proj X (n+1) 0).left
    (by rw [Over.w (drop X n), Over.w (Work.SymQuot.proj X (n+1) 0)]))
    (by
      rw [show Over.hom (Zover X n) = pullback.fst (Work.SymQuot.prod X n).hom X.hom
        ≫ (Work.SymQuot.prod X n).hom from rfl]
      rw [pullback.lift_fst_assoc, Over.w (drop X n)])

private theorem ΦO_left (X : Work.GCBasics.Sch K) (n : ℕ) : (ΦO X n).left = pullback.lift
    (drop X n).left (Work.SymQuot.proj X (n+1) 0).left
    (by rw [Over.w (drop X n), Over.w (Work.SymQuot.proj X (n+1) 0)]) := Over.homMk_left _ _

private theorem ΦO_z0 (X : Work.GCBasics.Sch K) (n : ℕ) :
    ΦO X n ≫ z0 X n = Work.SymQuot.proj X (n+1) 0 := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, ΦO_left, z0_left]
  rw [pullback.lift_snd]

private theorem ΦO_zs (X : Work.GCBasics.Sch K) (n : ℕ) (i : Fin n) :
    ΦO X n ≫ zs X n i = Work.SymQuot.proj X (n+1) i.succ := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, ΦO_left, zs_left]
  rw [← Category.assoc, pullback.lift_fst]
  rw [← Over.comp_left, drop_proj]

private theorem ΨO_drop (X : Work.GCBasics.Sch K) (n : ℕ) :
    ΨO X n ≫ drop X n = Over.homMk (pullback.fst (Work.SymQuot.prod X n).hom X.hom)
    (by rw [show Over.hom (Zover X n) = pullback.fst (Work.SymQuot.prod X n).hom X.hom
          ≫ (Work.SymQuot.prod X n).hom from rfl]) := by
  apply Limits.Pi.hom_ext
  intro i
  rw [Category.assoc, drop_proj, ΨO_proj_succ]
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.homMk_left, zs_left]

private theorem ΦO_ΨO (X : Work.GCBasics.Sch K) (n : ℕ) :
    ΦO X n ≫ ΨO X n = 𝟙 (Work.SymQuot.prod X (n+1)) := by
  apply Limits.Pi.hom_ext
  intro m
  rw [Category.assoc]
  refine Fin.cases ?_ ?_ m
  · rw [show ΨO X n ≫ Limits.Pi.π (fun _ : Fin (n+1) => X) 0 = z0 X n from ΨO_proj_zero X n,
      ΦO_z0, Category.id_comp]
  · intro i
    rw [show ΨO X n ≫ Limits.Pi.π (fun _ : Fin (n+1) => X) i.succ = zs X n i
        from ΨO_proj_succ X n i, ΦO_zs, Category.id_comp]

private theorem ΨO_ΦO (X : Work.GCBasics.Sch K) (n : ℕ) : ΨO X n ≫ ΦO X n = 𝟙 (Zover X n) := by
  apply Over.OverMorphism.ext
  rw [Over.id_left]
  apply pullback.hom_ext
  · simp only [Over.comp_left]
    rw [Category.assoc, ΦO_left, pullback.lift_fst, Category.id_comp]
    rw [← Over.comp_left, ΨO_drop]
    exact Over.homMk_left _ _
  · simp only [Over.comp_left]
    rw [Category.assoc, ΦO_left, pullback.lift_snd, Category.id_comp]
    rw [← Over.comp_left, ΨO_proj_zero, z0_left]

/-- **`Xⁿ ×_K X ≅ Xⁿ⁺¹`** (associativity of the `n`-fold fibre product over `Spec K`). -/
private noncomputable def succIso (X : Work.GCBasics.Sch K) (n : ℕ) :
    Zover X n ≅ Work.SymQuot.prod X (n+1) where
  hom := ΨO X n
  inv := ΦO X n
  hom_inv_id := ΨO_ΦO X n
  inv_hom_id := ΦO_ΨO X n

private theorem ΨO_apply_zero (X : Work.GCBasics.Sch K) (n : ℕ)
    (z : ↥(pullback (Work.SymQuot.prod X n).hom X.hom)) :
    (Work.SymQuot.proj X (n+1) 0).left ((ΨO X n).left z)
      = (pullback.snd (Work.SymQuot.prod X n).hom X.hom) z := by
  change ((ΨO X n) ≫ Work.SymQuot.proj X (n+1) 0).left z
    = (pullback.snd (Work.SymQuot.prod X n).hom X.hom) z
  rw [ΨO_proj_zero, z0_left]
  rfl

private theorem ΨO_apply_succ (X : Work.GCBasics.Sch K) (n : ℕ) (i : Fin n)
    (z : ↥(pullback (Work.SymQuot.prod X n).hom X.hom)) :
    (Work.SymQuot.proj X (n+1) i.succ).left ((ΨO X n).left z)
      = (Work.SymQuot.proj X n i).left
          ((pullback.fst (Work.SymQuot.prod X n).hom X.hom) z) := by
  change ((ΨO X n) ≫ Work.SymQuot.proj X (n+1) i.succ).left z
    = (Work.SymQuot.proj X n i).left
          ((pullback.fst (Work.SymQuot.prod X n).hom X.hom) z)
  rw [ΨO_proj_succ, zs_left]
  rfl

/-- **The product open of `Xⁿ⁺¹` is the product open of `Xⁿ ×_K X`.**  Pulling `piOpen X V (n+1)`
back along `ΨO : Xⁿ ×_K X ⟶ Xⁿ⁺¹` gives the binary product open with factors `piOpen X V n` and
`V`. -/
private theorem ΨO_preimage (X : Work.GCBasics.Sch K) (n : ℕ) (V : X.left.Opens) :
    (ΨO X n).left ⁻¹ᵁ (Work.SymQuot.piOpen X V (n+1))
      = pullback.fst (Work.SymQuot.prod X n).hom X.hom ⁻¹ᵁ (Work.SymQuot.piOpen X V n)
        ⊓ pullback.snd (Work.SymQuot.prod X n).hom X.hom ⁻¹ᵁ V := by
  ext z
  change (ΨO X n).left z ∈ Work.SymQuot.piOpen X V (n+1) ↔
    (pullback.fst (Work.SymQuot.prod X n).hom X.hom) z ∈ Work.SymQuot.piOpen X V n ∧
      (pullback.snd (Work.SymQuot.prod X n).hom X.hom) z ∈ V
  rw [Work.SymQuot.mem_piOpen, Work.SymQuot.mem_piOpen, Fin.forall_fin_succ]
  exact ⟨fun ⟨h0, hs⟩ =>
      ⟨fun i => by rw [← ΨO_apply_succ X n i z]; exact hs i,
        by rw [← ΨO_apply_zero X n z]; exact h0⟩,
    fun ⟨hs, h0⟩ =>
      ⟨by rw [ΨO_apply_zero]; exact h0, fun i => by rw [ΨO_apply_succ]; exact hs i⟩⟩

/-- `IsAffineOpen` is invariant under pulling back along an isomorphism. -/
private theorem isAffineOpen_preimage_iff {X Y : Scheme} (f : X ⟶ Y) [IsIso f] {U : Y.Opens} :
    IsAffineOpen (f ⁻¹ᵁ U) ↔ IsAffineOpen U :=
  ⟨fun h => by haveI : IsAffine ↑(f ⁻¹ᵁ U) := h; exact IsAffine.of_isIso (inv (f ∣_ U)),
   fun h => IsAffineOpen.preimage_of_isIso h f⟩

/-- The inductive step: `piOpen X V (n+1)` is affine whenever `piOpen X V n` is. -/
private theorem isAffineOpen_piOpen_succ (X : Work.GCBasics.Sch K) (n : ℕ) (V : X.left.Opens)
    (hV : IsAffineOpen V) (h : IsAffineOpen (Work.SymQuot.piOpen X V n)) :
    IsAffineOpen (Work.SymQuot.piOpen X V (n+1)) := by
  haveI : IsIso (ΨO X n).left := by
    rw [show (ΨO X n).left = (succIso X n).hom.left from rfl, ← Over.forget_map]
    exact Functor.map_isIso _ _
  exact (isAffineOpen_preimage_iff (ΨO X n).left).mp
    (by rw [ΨO_preimage]; exact isAffineOpen_inf_preimage (Work.SymQuot.prod X n).hom X.hom h hV)

/-- `prod X 0` is the terminal object of `Sch K`, whose underlying scheme is `Spec K`. -/
private noncomputable def prodZeroIso (X : Work.GCBasics.Sch K) :
    Work.SymQuot.prod X 0 ≅ (Over.mk (𝟙 (Spec (CommRingCat.of K))) :
      Work.GCBasics.Sch K) :=
  (CategoryTheory.Limits.isLimitEquivIsTerminalOfIsEmpty (C := Work.GCBasics.Sch K)
    (J := Discrete (Fin 0))
    (Limits.limit.cone (Discrete.functor (fun _ : Fin 0 => X))))
    (Limits.limit.isLimit _) |>.uniqueUpToIso Over.mkIdTerminal

private theorem isAffineOpen_piOpen_aux (X : Work.GCBasics.Sch K) (n : ℕ) (V : X.left.Opens)
    (hV : IsAffineOpen V) : IsAffineOpen (Work.SymQuot.piOpen X V n) := by
  induction n with
  | zero =>
    haveI : IsAffine (Work.SymQuot.prod X 0).left := by
      haveI hT : IsAffine ((Over.mk (𝟙 (Spec (CommRingCat.of K))) :
          Work.GCBasics.Sch K).left) := by
        change IsAffine (Spec (CommRingCat.of K)); infer_instance
      haveI : IsIso (prodZeroIso X).hom.left := by rw [← Over.forget_map]; infer_instance
      exact IsAffine.of_isIso (prodZeroIso X).hom.left
    rw [show Work.SymQuot.piOpen X V 0 = ⊤ from by
      ext x; simp [Work.SymQuot.mem_piOpen]]
    exact isAffineOpen_top _
  | succ n ih => exact isAffineOpen_piOpen_succ X n V hV ih

theorem isAffineOpen_piOpen {K : Type*} [Field K] (X : Work.GCBasics.Sch K) (n : ℕ) (V : X.left.Opens) (hV : AlgebraicGeometry.IsAffineOpen V) : AlgebraicGeometry.IsAffineOpen (Work.SymQuot.piOpen X V n) :=
  isAffineOpen_piOpen_aux X n V hV

end Work.SymQuot.Prod
