/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The sum map `Cⁿ(F) → Symⁿ C(F)` is surjective for `F` algebraically closed

For an algebraically closed field `F`, every `F`-point of the `n`-th symmetric power
`Symⁿ C = Cⁿ/S_n` of a curve `C` is a sum of `n` `F`-points of `C`:
the `n`-fold sum map `Sym.powMap C n : (Fin n → C(F)) → Symⁿ C(F)` is surjective.

This is the "splitting" statement used to build the point/divisor dictionary: an effective
divisor of degree `n` over an algebraically closed field splits into `n` points.

The proof is geometric.  Let `q = Sym.quot C n : Cⁿ ⟶ Symⁿ C` be the quotient map, which is
integral and surjective.  For a point `p : Spec F ⟶ Symⁿ C` form the fibre product
`Z = Spec F ×_{Symⁿ C} Cⁿ`; the projection `Z ⟶ Spec F` is again integral and surjective, hence
affine and nonempty, and — since `F` is algebraically closed — an integral surjection onto
`Spec F` from a nonempty scheme has a section (`exists_section_of_isIntegralHom`).
Composing this section with the other projection `Z ⟶ Cⁿ` produces the desired point of `Cⁿ`
lying over `p`.
-/
import Mathlib
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.Chart.quotientMap_isIntegralHom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.SymQuot.Sym

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

/-- **A nonzero ring integral over an algebraically closed field has a retraction to it.**
Let `F` be an algebraically closed field and `φ : F →+* A` an integral ring homomorphism with
`A ≠ 0`.  Then there is a ring homomorphism `ψ : A →+* F` with `ψ ∘ φ = id_F`: take a maximal
ideal `m ⊆ A`; the quotient `A/m` is a field integral over `F`, hence equal to `F` because `F`
is algebraically closed. -/
theorem exists_ringHom_of_isAlgClosed {F : Type u} [Field F] [IsAlgClosed F]
    {A : Type u} [CommRing A] [Nontrivial A] (φ : F →+* A) (hφ : φ.IsIntegral) :
    ∃ ψ : A →+* F, ψ.comp φ = RingHom.id F := by
  letI : Algebra F A := φ.toAlgebra
  haveI hAint : Algebra.IsIntegral F A := by
    rw [Algebra.isIntegral_iff]
    intro x
    exact hφ x
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : m.IsMaximal := hm
  haveI : Algebra.IsIntegral F (A ⧸ m) :=
    Algebra.IsIntegral.of_surjective (Ideal.Quotient.mkₐ F m) (Ideal.Quotient.mkₐ_surjective F m)
  have hint : (algebraMap F (A ⧸ m)).IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  have hbij : Function.Bijective (algebraMap F (A ⧸ m)) :=
    IsAlgClosed.ringHom_bijective_of_isIntegral (algebraMap F (A ⧸ m)) hint
  let e : F ≃ₐ[F] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId F (A ⧸ m)) hbij
  refine ⟨(e.symm : (A ⧸ m) →+* F).comp (Ideal.Quotient.mk m), ?_⟩
  ext x
  simp only [RingHom.comp_apply, RingHom.id_apply]
  have h1 : (Ideal.Quotient.mk m) (φ x) = algebraMap F (A ⧸ m) x := by
    rw [← Ideal.Quotient.mk_algebraMap F m x]
    rfl
  rw [h1]
  exact e.symm_apply_apply x

/-- **The ring-theoretic core of the proof.**  Let `φ : F →+* A` be a ring homomorphism from an
algebraically closed field `F` to a nonzero ring `A`, and let `w : B →+* F` be a ring
homomorphism such that `w ∘ φ = id_F`.  Then `w` gives a section of the corresponding map of
affine schemes. -/
theorem exists_section_of_isIntegralHom {F : Type u} [Field F] [IsAlgClosed F]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of F)) [IsIntegralHom f] (hZ : Nonempty Z) :
    ∃ s : Spec (CommRingCat.of F) ⟶ Z, s ≫ f = 𝟙 (Spec (CommRingCat.of F)) := by
  haveI hZaff : IsAffine Z := isAffine_of_isAffineHom f
  have hspec : Nonempty (Spec (Z.presheaf.obj (Opposite.op ⊤))) :=
    ⟨Z.isoSpec.hom hZ.some⟩
  haveI hAntriv : Nontrivial (Z.presheaf.obj (Opposite.op ⊤)) := by
    obtain ⟨p⟩ := hspec
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    haveI : Subsingleton (Ideal (Z.presheaf.obj (Opposite.op ⊤))) := inferInstance
    exact p.isPrime.ne_top (Subsingleton.elim _ _)
  have hfa : (f.appTop).hom.IsIntegral := IsIntegralHom.isIntegral_app f ⊤ (isAffineOpen_top _)
  set φ : F →+* (Z.presheaf.obj (Opposite.op ⊤)) :=
    (f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom with hφdef
  have hφ : φ.IsIntegral :=
    (RingHom.RespectsIso.cancel_left_isIso RingHom.isIntegral_respectsIso
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv f.appTop).mpr hfa
  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_isAlgClosed φ hφ
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ (Scheme.isoSpec Z).inv, ?_⟩
  rw [Category.assoc, ← Scheme.isoSpec_inv_naturality f]
  rw [← Category.assoc, ← Spec.map_comp]
  have h1 : ψ.comp (f.appTop).hom = (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom := by
    ext x
    have hx : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom x) = x := by
      have h := congrArg (fun (t : Γ(Spec (CommRingCat.of F), ⊤) ⟶
        Γ(Spec (CommRingCat.of F), ⊤)) => CommRingCat.Hom.hom t x)
        (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id
      simpa using h
    have := DFunLike.congr_fun hψ ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom x)
    simp only [RingHom.comp_apply, RingHom.id_apply, hφdef] at this
    rw [hx] at this
    exact this
  rw [show f.appTop ≫ CommRingCat.ofHom ψ = CommRingCat.ofHom (ψ.comp (f.appTop).hom) from by
    apply CommRingCat.hom_ext; rfl, h1]
  have h2 : CommRingCat.ofHom (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
      = (Scheme.ΓSpecIso (CommRingCat.of F)).hom := rfl
  rw [h2]
  simpa [SpecMap_ΓSpecIso_hom] using Scheme.toSpecΓ_isoSpec_inv (X := Spec (CommRingCat.of F))

/-- **The sum map is surjective on points over an algebraically closed field.** -/
theorem exists_powMap_eq {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ) {F : Type u} [Field F] [Algebra K F] [IsAlgClosed F] (p : Work.GCBasics.FPt (Work.SymQuot.Sym C n) F) : ∃ x : Fin n → Work.GCBasics.FPt C.toOver F, Work.SymQuot.Sym.powMap C n x = p := by
  classical
  have hsurj : Function.Surjective (Work.SymQuot.Sym.quot C n).left :=
    Work.SymQuot.Sym.quot_surjective C n
  haveI hsurjI : Surjective (Work.SymQuot.Sym.quot C n).left := ⟨hsurj⟩
  have hint : IsIntegralHom (Work.SymQuot.Sym.quot C n).left := by
    rw [Work.SymQuot.Sym.quot_left]
    exact Work.SymQuot.Chart.quotientMap_isIntegralHom (Work.SymQuot.symData C n)
  -- the fibre of `Sym.quot` over `p`
  let Z := Limits.pullback (Work.SymQuot.Sym.quot C n).left p.left
  haveI hZne : Nonempty Z := by
    haveI : Surjective (Limits.pullback.snd (Work.SymQuot.Sym.quot C n).left p.left) :=
      inferInstance
    obtain ⟨z, -⟩ := (Limits.pullback.snd (Work.SymQuot.Sym.quot C n).left p.left).surjective
      (IsLocalRing.closedPoint F)
    exact ⟨z⟩
  haveI hintZ : IsIntegralHom
      (Limits.pullback.snd (Work.SymQuot.Sym.quot C n).left p.left) := inferInstance
  obtain ⟨s, hs⟩ := exists_section_of_isIntegralHom
    (Limits.pullback.snd (Work.SymQuot.Sym.quot C n).left p.left) hZne
  -- the two projections of the fibre product agree on the structure morphisms
  have hcond : Limits.pullback.fst (Work.SymQuot.Sym.quot C n).left p.left
        ≫ (Work.SymQuot.prod C.toOver n).hom
      = Limits.pullback.snd (Work.SymQuot.Sym.quot C n).left p.left
        ≫ (Work.GCBasics.specOf K F).hom := by
    rw [← Over.w (Work.SymQuot.Sym.quot C n), ← Over.w p]
    simp only [← Category.assoc, Limits.pullback.condition]
  -- the induced point `Spec F ⟶ Cⁿ`
  let xl : (Work.GCBasics.specOf K F).left ⟶ (Work.SymQuot.prod C.toOver n).left :=
    s ≫ Limits.pullback.fst (Work.SymQuot.Sym.quot C n).left p.left
  have hxl : xl ≫ (Work.SymQuot.prod C.toOver n).hom = (Work.GCBasics.specOf K F).hom := by
    show (s ≫ Limits.pullback.fst (Work.SymQuot.Sym.quot C n).left p.left)
        ≫ (Work.SymQuot.prod C.toOver n).hom = _
    rw [Category.assoc, hcond, ← Category.assoc, hs, Category.id_comp]
  let x' : Work.GCBasics.FPt (Work.SymQuot.prod C.toOver n) F := Over.homMk xl hxl
  -- `x'` lies over `p`
  have hx' : x' ≫ Work.SymQuot.Sym.quot C n = p := by
    apply Over.OverMorphism.ext
    show xl ≫ (Work.SymQuot.Sym.quot C n).left = p.left
    show (s ≫ Limits.pullback.fst (Work.SymQuot.Sym.quot C n).left p.left)
        ≫ (Work.SymQuot.Sym.quot C n).left = p.left
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hs, Category.id_comp]
  refine ⟨fun m => x' ≫ Work.SymQuot.proj C.toOver n m, ?_⟩
  have hlift : Limits.Pi.lift (fun m => x' ≫ Work.SymQuot.proj C.toOver n m) = x' := by
    apply Limits.Pi.hom_ext
    intro m
    rw [Limits.Pi.lift_comp_π]
    try rfl
  rw [Work.SymQuot.Sym.powMap, hlift]
  exact hx'

end Work.SymQuot.Sym
