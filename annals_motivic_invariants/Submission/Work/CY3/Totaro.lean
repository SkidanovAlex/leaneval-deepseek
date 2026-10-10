import Submission.Work.CY3.Link

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3.Totaro` — the non-birationality input (`thm:BurtCY`, `cor-CYnSB`)

This file records the **named input** which makes the CY3 link motivically non-trivial — Totaro's
theorem, communicated to the authors and proved in the appendix of Lin–Shinder,
*Motivic invariants of birational maps* (Annals **199** (1), 2024):

> **Theorem (`thm:BurtCY`, appendix).**  Let `X₁`, `X₂` be smooth projective varieties over a field
> with a birational map `φ : X₁ ⇢ X₂`.  Assume that `K_{X₁}` and `K_{X₂}` are nef.  Then `φ` is a
> pseudo-isomorphism.  If in addition `NS(X₁)_ℚ` or `NS(X₂)_ℚ` is one-dimensional, then `φ` is an
> isomorphism.
>
> **Corollary (`cor-CYnSB`).**  Let `Z`, `Z'` be `K`-trivial varieties of Picard number one over
> an algebraically closed field.  If `Z ≄ Z'`, then `Z × W` is not birational to `Z' × W` for any
> separably rationally connected variety `W`; in particular `Z` is not stably birational to `Z'`.

It is *used* in the paper in `lem-nSBG2`: after the reduction to an algebraically closed field and
the computation of the two cubic self-intersections (`c₁(M|_Z)³ = 14 ≠ 42 = c₁(M'|_{Z'})³`, from
Ito–Miura–Okawa–Ueda), the two centres `Z`, `Z'` of the link are non-isomorphic `K`-trivial
threefolds of Picard rank one, hence not stably birational.

Mathlib has no nefness, no negativity lemma, no `Proj` of a graded ring over a graded algebra of
global sections, and no Néron–Severi groups, so Totaro's theorem is a named hypothesis here.  What
is *proved* below is that it applies to the CY3 link: Totaro's input, applied to the two centres,
turns the failure of `ResEquiv` for the two exceptional divisors into the non-stable birationality
of the centres (through the `ℙ¹`-bundle bridge `CY3Data.bridge`), which is exactly the
non-triviality input of the L-link.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **Named input: Totaro's theorem** (`thm:BurtCY`, `cor-CYnSB`).

Two non-isomorphic `K`-trivial varieties of Picard number one over a field are not stably
birational.  (The paper's `cor-CYnSB` is stated for `K`-trivial varieties of Picard number one over
an algebraically closed field; `lem-nSBG2` reduces to that case, and the form recorded here is the
form in which the link consumes it — the same convention as in the K3 area, see
`Work.K3.TotaroInput`.) -/
structure TotaroInput (𝕜 : Type) [Field 𝕜] : Prop where
  /-- `K`-trivial, Picard number one, non-isomorphic `⟹` not stably birational. -/
  not_stablyBirat_of_not_iso : ∀ (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y],
    IsKTrivial 𝕜 X → IsKTrivial 𝕜 Y → PicardRankOne 𝕜 X → PicardRankOne 𝕜 Y →
    ¬ IsoOver 𝕜 X Y → ¬ StablyBirational 𝕜 X Y

/-- **The per-pair form of Totaro's input (`lem-nSBG2`, second half) — the faithful replacement of
the universal form above.**

Every consumer of `TotaroInput` in this workspace uses it at one *fixed* pair, namely the two
centres of a link: `Work.CY3Stab.Prod.exists_cInv_ne_zero_of_CY3Data` invokes it exactly once, at
the pair `(D.Z', D.Z)`, and `Work.Wire123.exists_cInv_ne_zero_of_CY3Data_sep` is the same proof with
this field as its hypothesis.

The universal form cannot be instantiated as it stands: its geometric hypotheses
`IsKTrivial`, `PicardRankOne` are classes with no fields, hence satisfied by *every* `𝕜`-variety, so
the field asserts that no two non-isomorphic varieties are stably birational — refuted by the pair
`𝔸⁰`, `𝔸¹` (`Work.Wire123.not_totaroInput`, and `Work.Wire123.not_totaroInput_after`).  At a pair
(the two centres of a link) the statement is exactly the paper's `cor-CYnSB` and is consistent.
`TotaroInput.toInputAt` below shows that nothing is lost. -/
structure TotaroInputAt (𝕜 : Type) [Field 𝕜] (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y] :
    Prop where
  /-- non-isomorphic `K`-trivial varieties of Picard rank one are not stably birational -/
  not_stablyBirat : ¬ IsoOver 𝕜 X Y → ¬ StablyBirational 𝕜 X Y

/-- The universal input gives the pair form at every pair satisfying its (named) hypotheses — the
direction in which the two interfaces are compared. -/
theorem TotaroInput.toInputAt (𝕜 : Type) [Field 𝕜] (T : TotaroInput 𝕜) {X Y : Scheme.{0}}
    [Variety 𝕜 X] [Variety 𝕜 Y] (hX : IsKTrivial 𝕜 X) (hY : IsKTrivial 𝕜 Y) (pX : PicardRankOne 𝕜 X)
    (pY : PicardRankOne 𝕜 Y) : TotaroInputAt 𝕜 X Y :=
  ⟨fun hne => T.not_stablyBirat_of_not_iso X Y hX hY pX pY hne⟩

variable {𝕜 : Type} [Field 𝕜]

/-- **Totaro's input enters the link.**  If the two centres of the CY3 datum are not isomorphic
over `𝕜`, then the two exceptional divisors do not have isomorphic function fields: by the
`ℙ¹`-bundle bridge `D.bridge`, an isomorphism of the function fields `κ(y) ≅ κ(x)` would make `Z`
and `Z'` stably birational, contradicting Totaro's input. -/
theorem CY3Data.not_resEquiv_yx_of_totaro (D : CY3Data 𝕜) (T : TotaroInputAt 𝕜 D.Z D.Z')
    (h : ¬ IsoOver 𝕜 D.Z D.Z') : ¬ ResEquiv 𝕜 D.y D.x := fun hres =>
  T.not_stablyBirat h (D.bridge hres)

/-- **The CY3 L-link**, produced from the geometric data, Totaro's input and the failure of the
centres to be isomorphic over `𝕜` (paper `lem-nSBG2`). -/
noncomputable def CY3Data.toCY3Link (D : CY3Data 𝕜) (T : TotaroInputAt 𝕜 D.Z D.Z')
    (h : ¬ IsoOver 𝕜 D.Z D.Z') : CY3Link 𝕜 :=
  { toCY3Data := D, not_resEquiv_yx := D.not_resEquiv_yx_of_totaro T h }

/-- **The two centres are not stably birational**: this is the paper's `lem-nSBG2`, second half —
Totaro's `cor-CYnSB` applied to the two non-isomorphic `K`-trivial threefolds of Picard rank
one.  It is the pure geometric form of the non-triviality of the link (the form in which the
paper's `thm:bir-generation` (c) uses it, together with Corollary `cor-CYnSB`, to deduce
`[Z × ℙ¹ × W] ≠ [Z' × ℙ¹ × W]`). -/
theorem CY3Data.not_stablyBirational (D : CY3Data 𝕜) (T : TotaroInputAt 𝕜 D.Z D.Z')
    (h : ¬ IsoOver 𝕜 D.Z D.Z') : ¬ StablyBirational 𝕜 D.Z D.Z' :=
  T.not_stablyBirat h

/-- The non-vanishing of the invariant coefficient of the link, directly from the geometric datum
and the named input.  This is the shape consumed by `Work.Motivic.not_gen_of_cInv_ne_zero` for
`n = 5`. -/
theorem CY3Data.exists_cInv_ne_zero (D : CY3Data 𝕜) (T : TotaroInputAt 𝕜 D.Z D.Z')
    (h : ¬ IsoOver 𝕜 D.Z D.Z') :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 5),
      cInv 𝕜 z₀ (φ : (Affine 𝕜 5).BirationalMap (Affine 𝕜 5)) ≠ 0 :=
  (D.toCY3Link T h).exists_cInv_ne_zero

end

end Work.CY3
