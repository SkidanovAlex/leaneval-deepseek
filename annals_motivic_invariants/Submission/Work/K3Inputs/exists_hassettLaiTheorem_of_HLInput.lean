import Mathlib
import Submission.Work.K3Inputs.Defs
import Submission.Work.K3Inputs.LinkCore
import Submission.Work.K3Inputs.HLItems
import Submission.Work.K3Inputs.StablyBiratK3
import Submission.Work.K3Inputs.exists_variety_prodOver_affineSpace

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral
attribute [instance] Work.K3.K3Data.varietyS Work.K3.K3Data.varietyS' Work.K3.K3Data.varietyP
attribute [instance] Work.K3.TerasomaInput.varietyS Work.K3.TerasomaInput.overSigma
  Work.K3.TerasomaInput.isOverSigma
attribute [instance] Work.K3Inputs.LinkCore.varietyS Work.K3Inputs.LinkCore.varietyS'
  Work.K3Inputs.LinkCore.varietyP Work.K3Inputs.LinkCore.isOverψ Work.K3Inputs.LinkCore.isOverε
  Work.K3Inputs.LinkCore.isOverδ
attribute [instance] Work.K3Inputs.HLInput.overSigma' Work.K3Inputs.HLInput.isOverSigma'
  Work.K3Inputs.HLInput.isClosedImmersionSigma' Work.K3Inputs.HLInput.isReducedSigma'
  Work.K3Inputs.HLInput.smoothSigma' Work.K3Inputs.HLInput.geomIntS
  Work.K3Inputs.HLInput.geomIntS' Work.K3Inputs.HLInput.geomIntP

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open MotivicInvariants Order
open Work.K3Inputs

noncomputable section

/-!
## The product with affine space is insensitive to the `Over`-structure

`Work.K3.prodOver 𝕜 X Y = X ×_{Spec 𝕜} Y` depends on the `Over (Spec 𝕜)`-structure of `X` as
*data*.  For `Y = 𝔸(Fin n; Spec 𝕜)` this dependence disappears: `𝔸(n;S)` is by definition the
fibre product `S ×_𝟙 Spec ℤ[n]` over the *terminal* object of `Scheme`, so
`X ×_{Spec 𝕜} 𝔸(n; Spec 𝕜) ≅ X ×_𝟙 Spec ℤ[n]` — the same scheme for every `Over`-structure on
`X`.  This is what allows the ℙ¹-bundle bridge of the K3 link, whose geometric clauses are stated
with the canonical `Work.K3.baseChangeOver`, to be transferred to the `Variety.over`-structure
with which `Work.K3.StablyBirational` (and `Work.K3Inputs.IsP1BundleOver`, `CylinderRigid`)
actually build their fibre products.  See `NOTES.md` §5.3.
-/

/-- **The product `X ×_{Spec 𝕜} 𝔸ⁿ` only depends on the terminal structure of `X`.**

`𝔸(n; S) = S ×_𝟙 Spec ℤ[n]` with the first projection as structure morphism
(`AlgebraicGeometry.AffineSpace`), so the square

```
pullback f (pullback.fst t_S t_A) --fst--> S ×_𝟙 A --snd--> A
            |                                |              |
            snd                        pullback.fst t_S t_A t_A
            ∨                                ∨              ∨
            X ---------f--------------------> S ---t_S---> 𝟙
```

is the pasting of two pullback squares, hence a pullback square: the left-hand object is
`X ×_𝟙 A` for the terminal structure of `X`, independently of `f`. -/
theorem prodOver_iso_terminal (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) (n : ℕ)
    (o : X.Over (Spec (.of 𝕜))) :
    Nonempty (@Work.K3.prodOver 𝕜 _ X (AffineN 𝕜 n) o
        (inferInstance : (AffineN 𝕜 n).Over (Spec (.of 𝕜))) ≅
      pullback (terminal.from (Spec (CommRingCat.of (MvPolynomial (Fin n) (ULift ℤ)))))
        (terminal.from X)) := by
  let A : Scheme.{0} := Spec (CommRingCat.of (MvPolynomial (Fin n) (ULift ℤ)))
  let zS : pullback (terminal.from (Spec (.of 𝕜))) (terminal.from A) ⟶ Spec (.of 𝕜) :=
    pullback.fst _ _
  let zA : pullback (terminal.from (Spec (.of 𝕜))) (terminal.from A) ⟶ A := pullback.snd _ _
  have h1 : CategoryTheory.IsPullback (pullback.fst o.hom zS) (pullback.snd o.hom zS) o.hom zS :=
    CategoryTheory.IsPullback.of_hasPullback o.hom zS
  have h2 : CategoryTheory.IsPullback
      (pullback.fst (terminal.from (Spec (.of 𝕜))) (terminal.from A))
      (pullback.snd (terminal.from (Spec (.of 𝕜))) (terminal.from A))
      (terminal.from (Spec (.of 𝕜))) (terminal.from A) :=
    CategoryTheory.IsPullback.of_hasPullback (terminal.from (Spec (.of 𝕜))) (terminal.from A)
  have hh : CategoryTheory.IsPullback (pullback.snd o.hom zS ≫ zA) (pullback.fst o.hom zS)
      (terminal.from A) (terminal.from X) := by
    have h3 := CategoryTheory.IsPullback.paste_horiz h1.flip h2.flip
    rwa [show o.hom ≫ terminal.from (Spec (CommRingCat.of 𝕜)) = terminal.from X from
      CategoryTheory.Limits.terminal.hom_ext _ _] at h3
  change Nonempty (pullback o.hom zS ≅ pullback (terminal.from A) (terminal.from X))
  exact ⟨hh.isoPullback⟩

/-- **`X ×_{Spec 𝕜} 𝔸ⁿ` is unchanged (up to canonical isomorphism) by the `Over`-structure of
`X`.** -/
theorem prodOver_iso_of_over (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) (n : ℕ)
    (o o' : X.Over (Spec (.of 𝕜))) :
    Nonempty (@Work.K3.prodOver 𝕜 _ X (AffineN 𝕜 n) o
        (inferInstance : (AffineN 𝕜 n).Over (Spec (.of 𝕜))) ≅
      @Work.K3.prodOver 𝕜 _ X (AffineN 𝕜 n) o'
        (inferInstance : (AffineN 𝕜 n).Over (Spec (.of 𝕜)))) := by
  obtain ⟨e₁⟩ := prodOver_iso_terminal 𝕜 X n o
  obtain ⟨e₂⟩ := prodOver_iso_terminal 𝕜 X n o'
  exact ⟨e₁.trans e₂.symm⟩

/-- **Stable birationality is insensitive to the `Over`-structure** (with the affine exponents
fixed): transporting the two cylinders along `prodOver_iso_of_over` preserves the relation. -/
theorem StablyBirat_iso_over {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}}
    (oX oX' : X.Over (Spec (.of 𝕜))) (oY oY' : Y.Over (Spec (.of 𝕜)))
    (h : @StablyBirat 𝕜 _ X Y oX oY) : @StablyBirat 𝕜 _ X Y oX' oY' := by
  obtain ⟨n, m, hb⟩ := h
  obtain ⟨e₁⟩ := prodOver_iso_of_over 𝕜 X n oX oX'
  obtain ⟨e₂⟩ := prodOver_iso_of_over 𝕜 Y m oY oY'
  exact ⟨n, m, (Birational.trans ⟨PartialIso.ofIso e₁.symm⟩ hb).trans
    ⟨PartialIso.ofIso e₂⟩⟩

/-! ## The uniform ℙ¹-bundle bridge -/

/-- **The `bridge_bc` clause of `Work.K3.HassettLaiTheorem`, proved from (F1)/(F2).**

For every subfield `𝕜 ⊆ ℂ` and every `Variety`-structure on the two base-changed centres, a
`ResEquiv` between the (base-changed) exceptional divisors `q`, `p` forces the two `𝕜`-centres to
be stably birational over `𝕜`.

The proof follows `Work.K3Inputs.bridge_of_clauses` with the clauses (F1)/(F2) of `HLInput`
(which are stated with the canonical `Work.K3.baseChangeOver`), and then transfers the resulting
`StablyBirat` to the `Variety.over`-structure with which `Work.K3.StablyBirational` builds its
products (`StablyBirat_iso_over`); the `Variety`-instances are the binders of the statement, as
required. -/
theorem bridge_bc_of_HLInput (T : Work.K3.TerasomaInput) (h : HLInput T) :
    ∀ (𝕜 : Subfield ℂ) [Variety ↥𝕜 (Work.K3.baseChange ℚ ↥𝕜 h.core.S)]
      [Variety ↥𝕜 (Work.K3.baseChange ℚ ↥𝕜 h.core.S')]
      (p q : Work.K3.baseChange ℚ ↥𝕜 h.core.P),
      Work.K3.baseChangeProj ℚ ↥𝕜 h.core.P p = h.core.x → coheight p = 1 →
      Work.K3.baseChangeProj ℚ ↥𝕜 h.core.P q = h.core.y → coheight q = 1 →
      ResEquiv ↥𝕜 q p →
      Work.K3.StablyBirational ↥𝕜 (Work.K3.baseChange ℚ ↥𝕜 h.core.S)
        (Work.K3.baseChange ℚ ↥𝕜 h.core.S') := by
  intro 𝕜 vS vS' p q hpx hpc hqy hqc hres
  have hbridge : @StablyBirat ↥𝕜 _ (Work.K3.baseChange ℚ ↥𝕜 h.core.S)
      (Work.K3.baseChange ℚ ↥𝕜 h.core.S')
      (Work.K3.baseChangeOver ℚ ↥𝕜 h.core.S)
      (Work.K3.baseChangeOver ℚ ↥𝕜 h.core.S') :=
    @bridge_of_clauses ↥𝕜 _ (Work.K3.baseChange ℚ ↥𝕜 h.core.P)
      (Work.K3.baseChange ℚ ↥𝕜 h.core.S) (Work.K3.baseChange ℚ ↥𝕜 h.core.S') _ _
      (Work.K3.baseChangeOver ℚ ↥𝕜 h.core.P) (Work.K3.baseChangeOver ℚ ↥𝕜 h.core.S)
      (Work.K3.baseChangeOver ℚ ↥𝕜 h.core.S') q p (h.y_cylinder_bc 𝕜 q hqy hqc)
      (h.x_cylinder_bc 𝕜 p hpx hpc) (h.cylinderRigid_bc 𝕜) hres
  have hbridge' : @StablyBirat ↥𝕜 _ (Work.K3.baseChange ℚ ↥𝕜 h.core.S)
      (Work.K3.baseChange ℚ ↥𝕜 h.core.S')
      (@Variety.over ↥𝕜 _ (Work.K3.baseChange ℚ ↥𝕜 h.core.S) vS)
      (@Variety.over ↥𝕜 _ (Work.K3.baseChange ℚ ↥𝕜 h.core.S') vS') :=
    StablyBirat_iso_over (𝕜 := ↥𝕜) (X := Work.K3.baseChange ℚ ↥𝕜 h.core.S)
      (Y := Work.K3.baseChange ℚ ↥𝕜 h.core.S')
      (Work.K3.baseChangeOver ℚ ↥𝕜 h.core.S)
      (@Variety.over ↥𝕜 _ (Work.K3.baseChange ℚ ↥𝕜 h.core.S) vS)
      (Work.K3.baseChangeOver ℚ ↥𝕜 h.core.S')
      (@Variety.over ↥𝕜 _ (Work.K3.baseChange ℚ ↥𝕜 h.core.S') vS') hbridge
  exact StablyBirat_to_stablyBirational (Work.K3.baseChange ℚ ↥𝕜 h.core.S)
    (Work.K3.baseChange ℚ ↥𝕜 h.core.S') hbridge'

/-! ## The assembly -/

/-- **The K3 chapter's geometric input, with both bridges proved.**

`Work.K3Inputs.HLInput T` carries every field of `Work.K3.HassettLaiTheorem T` except the two
bridge clauses, which are replaced by their geometric content:

* `h.core : Work.K3Inputs.LinkCore ℚ` (the link data with the bridge `bridge` of
  `Work.K3.K3Data` replaced by the (F1)/(F2) clauses; see `Work.K3Inputs.LinkCore.bridge`), and
* the three base-change-uniform clauses `y_cylinder_bc`, `x_cylinder_bc`, `cylinderRigid_bc`
  (replacing `bridge_bc`).

The claim assembles `Work.K3.HassettLaiTheorem T` from it: the link data is
`Work.K3Inputs.LinkCore.toK3Data h.core` (whose `bridge` is *proved*), the uniform bridge clause
`bridge_bc` is derived from the three clauses exactly as in
`Work.K3Inputs.bridge_of_clauses` followed by
`Work.K3Inputs.StablyBirat_to_stablyBirational`, and all other fields are those of `HLInput`.  Every
field of the K3 chapter's structure is thus accounted for, and the residual assumptions are exactly
the four numbered items of `thm-HL` (as named `Prop`s in `Work.K3Inputs.HLItems`) plus (F1)/(F2).

A warning about instances (see `NOTES.md` §5.3): the `Over`-structure of a base change enters as
*data* into the types of `Work.K3Inputs.IsP1BundleOver`, `SameCylinderField`, `CylinderRigid` and
`Work.K3.StablyBirational`, and two instances (`Work.K3.baseChangeOver` and
`MotivicInvariants.Variety.over`) are available for it, with equal priority and with the second
selectable via a delayed `Variety` metavariable.  The clause fields of `HLInput` fix
`Work.K3.baseChangeOver` explicitly; the assembly therefore needs the same discipline one level up
(explicit `Over`-arguments for `Cyl`/`StablyBirat` and for the witness of
`Work.K3.StablyBirational`, i.e. `Variety.over` of the `Variety` binders of the goal).  Helper API
defined inside this file is welcome. -/
theorem exists_hassettLaiTheorem_of_HLInput (T : Work.K3.TerasomaInput)
    (h : Work.K3Inputs.HLInput T) : Nonempty (Work.K3.HassettLaiTheorem T) := by
  refine ⟨{ data := h.core.toK3Data
            centre := h.centre
            Sigma' := h.Sigma'
            overSigma' := h.overSigma'
            sigma' := h.sigma'
            isOverSigma' := h.isOverSigma'
            isClosedImmersionSigma' := h.isClosedImmersionSigma'
            isReducedSigma' := h.isReducedSigma'
            smoothSigma' := h.smoothSigma'
            hasLengthThree' := h.hasLengthThree'
            hl' := h.hl'
            notIsoGeom := h.notIsoGeom
            geomIntS := h.geomIntS
            geomIntS' := h.geomIntS'
            geomIntP := h.geomIntP
            isK3_bc := h.isK3_bc
            kTrivial_bc := h.kTrivial_bc
            picardOne_bc := h.picardOne_bc
            isK3'_bc := h.isK3'_bc
            kTrivial'_bc := h.kTrivial'_bc
            picardOne'_bc := h.picardOne'_bc
            hasLengthThree_bc := h.hasLengthThree_bc
            hl_bc := h.hl_bc
            x_codim1 := h.x_codim1
            y_codim1 := h.y_codim1
            x_notIso := h.x_notIso
            y_notIso := h.y_notIso
            bridge_bc := bridge_bc_of_HLInput T h
            transports_bc := h.transports_bc }⟩

end

end Work.K3Inputs
