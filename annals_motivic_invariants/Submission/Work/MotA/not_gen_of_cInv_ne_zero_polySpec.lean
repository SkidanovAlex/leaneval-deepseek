import Mathlib
import Submission.Work.MotA.Defs
import Submission.Work.CrauderKatz.cInv_conj_eq
import Submission.Work.Motivic.not_gen_of_cInv_ne_zero

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotA

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

/-! ### Transporting along the affine-space identification

The two lemmas below package the isomorphism `Work.MotA.polySpecIsoAffine 𝕜 n` as a morphism over
`Spec 𝕜`, in the form needed to conjugate a birational self-map of `Work.MotA.polySpec 𝕜 n` into
the Cremona group `Cr 𝕜 n`. -/

/-- An isomorphism of `S`-schemes, viewed as a partial isomorphism, is a partial isomorphism
over `S`.  (`PartialIso.ofIso` is a plain definition, so its `IsOver` property has to be extracted
by hand; the composite is `X.topIso ≪≫ e ≪≫ Y.topIso.symm`, whose underlying morphism is `e.hom`
up to the trivial open subscheme identifications.) -/
lemma partialIso_ofIso_isOver {X Y S : Scheme.{0}} [X.Over S] [Y.Over S] (e : X ≅ Y)
    (he : e.hom.IsOver S) : (PartialIso.ofIso e).IsOver (X ↘ S) (Y ↘ S) := by
  rw [PartialIso.IsOver]
  show (X.topIso ≪≫ e ≪≫ Y.topIso.symm).hom ≫ (⊤ : Y.Opens).ι ≫ (Y ↘ S) =
      (⊤ : X.Opens).ι ≫ (X ↘ S)
  rw [← Scheme.topIso_hom Y, ← Scheme.topIso_hom X]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  have h : e.hom ≫ Y ↘ S = X ↘ S := (Hom.isOver_iff S).mp he
  simpa [Category.assoc] using congrArg (fun t => X.topIso.hom ≫ t) h

/-- Mathlib's `AffineSpace.SpecIso (Fin n) 𝕜 : 𝔸(Fin n; Spec 𝕜) ≅ Spec 𝕜[x₁,…,xₙ]` is a morphism
over `Spec 𝕜` for the structure map of `Work.MotA.polySpec` (the two sides agree by
`AffineSpace.SpecIso_inv_over` and `MvPolynomial.C = algebraMap 𝕜 𝕜[x₁,…,xₙ]`). -/
lemma specIso_isOver (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    (AffineSpace.SpecIso (Fin n) (CommRingCat.of 𝕜)).hom.IsOver
      (Spec (CommRingCat.of 𝕜)) := by
  rw [Hom.isOver_iff]
  rw [show Work.MotA.polySpec 𝕜 n ↘ Spec (CommRingCat.of 𝕜) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : 𝕜 →+* MvPolynomial (Fin n) 𝕜)) from rfl]
  rw [← AffineSpace.SpecIso_inv_over (n := Fin n) (R := CommRingCat.of 𝕜)]
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rfl

/-- Audit node **A1, transport to the Cremona group.**

`Work.MotA.polySpec 𝕜 n = AlgebraicGeometry.Spec (CommRingCat.of (MvPolynomial (Fin n) 𝕜))` is
affine `n`-space in the `PrimeSpectrum` model, identified with `MotivicInvariants`' `𝔸ⁿ` by
`Work.MotA.polySpecIsoAffine 𝕜 n : polySpec 𝕜 n ≅ 𝔸(Fin n; Spec (.of 𝕜))` (Mathlib's
`AffineSpace.SpecIso`), an isomorphism over `Spec 𝕜`.

**Claim.** A non-vanishing invariant coefficient of some birational self-map `f` of
`Work.MotA.polySpec 𝕜 n` over `Spec 𝕜` obstructs generation of `Cr 𝕜 n` by pseudo-regularizable
elements.

Route.  Let `ψ : 𝔸(Fin n; Spec 𝕜) ⤏ Work.MotA.polySpec 𝕜 n` be the birational map attached to the
isomorphism `Work.MotA.polySpecIsoAffine 𝕜 n` (use `PartialIso.ofIso` and `.symm` as convenient;
either orientation works).  It is over `Spec 𝕜` by `AffineSpace.SpecIso_inv_over`
(resp. `AffineSpace.SpecIso_hom` together with `AffineSpace.over`).  Then
`g := ψ.trans (f.trans ψ.symm)` is a birational self-map of `𝔸(Fin n; Spec 𝕜)` over `Spec 𝕜`,
hence an element of `MotivicInvariants.Cr 𝕜 n`, and `Work.CrauderKatz.cInv_conj_eq` gives
`cInv 𝕜 z g = cInv 𝕜 z f ≠ 0`.  Conclude with `Work.Motivic.not_gen_of_cInv_ne_zero` applied to
`g`, `z` and that inequality.  The `Variety 𝕜 (Work.MotA.polySpec 𝕜 n)` instance needed by
`cInv_conj_eq` is `Work.MotA.instVarietyPolySpec`, the one for `𝔸(Fin n; Spec 𝕜)` comes from
`ChallengeDeps`, and the `IsOver` instances for the composite come from
`Work.Motivic.pseudoReg_isOver_trans` / `Work.Motivic.pseudoReg_isOver_toBirationalMap` (instance
search does not unfold `BirationalMap.trans`). -/
theorem not_gen_of_cInv_ne_zero_polySpec (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (h : ∃ (Z : AlgebraicGeometry.Scheme.{0})
        (_ : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))) (z : Z)
        (f : (Work.MotA.polySpec 𝕜 n).BirationalMap (Work.MotA.polySpec 𝕜 n)),
        f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) ∧ cInv 𝕜 z f ≠ 0) :
    ¬ MotivicInvariants.GenByPseudoRegularizable 𝕜 n := by
  obtain ⟨Z, hZ, z, f, hf, hc⟩ := h
  letI := hZ
  haveI hfI : f.IsOver (Spec (CommRingCat.of 𝕜)) := hf
  -- the identification `𝔸ⁿ ≅ polySpec 𝕜 n`, as an isomorphism over `Spec 𝕜`
  haveI hspecIso : (AffineSpace.SpecIso (Fin n) (CommRingCat.of 𝕜)).hom.IsOver
      (Spec (CommRingCat.of 𝕜)) := specIso_isOver 𝕜 n
  let ψ : (𝔸(Fin n; Spec (CommRingCat.of 𝕜))).BirationalMap (Work.MotA.polySpec 𝕜 n) :=
    (PartialIso.ofIso (AffineSpace.SpecIso (Fin n) (CommRingCat.of 𝕜))).toBirationalMap
  haveI hψover : ψ.IsOver (Spec (CommRingCat.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_toBirationalMap
      (PartialIso.ofIso (AffineSpace.SpecIso (Fin n) (CommRingCat.of 𝕜)))
      (partialIso_ofIso_isOver _ hspecIso)
  haveI hψsymm : (ψ.symm).IsOver (Spec (CommRingCat.of 𝕜)) :=
    inferInstanceAs (ψ.inv.IsOver (Spec (CommRingCat.of 𝕜)))
  haveI hfψ : (f.trans ψ.symm).IsOver (Spec (CommRingCat.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans f ψ.symm
  -- the conjugate of `f` by `ψ`, a birational self-map of affine space over `Spec 𝕜`
  let g : (𝔸(Fin n; Spec (CommRingCat.of 𝕜))).BirationalMap
      (𝔸(Fin n; Spec (CommRingCat.of 𝕜))) := ψ.trans (f.trans ψ.symm)
  haveI hgover : g.IsOver (Spec (CommRingCat.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans ψ (f.trans ψ.symm)
  refine Work.Motivic.not_gen_of_cInv_ne_zero 𝕜 n ⟨Z, hZ, z, ⟨g, hgover⟩, ?_⟩
  -- conjugation does not change the invariant coefficient
  have hconj : cInv 𝕜 z g = cInv 𝕜 z f :=
    Work.CrauderKatz.cInv_conj_eq (𝕜 := 𝕜) z ψ f
  rw [hconj]
  exact hc

end Work.MotA
