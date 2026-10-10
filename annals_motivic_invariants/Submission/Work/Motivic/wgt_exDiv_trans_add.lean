import Mathlib
import Submission.Work.Motivic.Defs
import Submission.Work.Motivic.cInv_add_defs
import Submission.Work.Motivic.cInv_add_pt
import Submission.Work.Motivic.cInv_add_trans
import Submission.Work.Motivic.exDiv_finite_of_variety

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

set_option linter.style.haveILetI false

/-!
# First counting identity for the additivity of the Lin–Shinder invariant

With `R = exDiv (φ.trans ψ)`, `P = exDiv φ`, `Q = exDiv ψ` and `P' = exDiv φ.symm`,
we prove `wgt R + wgt (Q ∩ P') = wgt (R ∩ P) + wgt Q`.

The proof has two ingredients, isolated as `private` lemmas below.

* `phiPt φ` restricts to a bijection `R ∖ P ≃ Q ∖ P'` (this is `transSdiffEquiv`), and it
  preserves residue fields (`ResEquiv_phiPt`), so both sides of the difference of the two
  telescoping identities agree.
* `wgt_inter_add_wgt_sdiff` telescopes `wgt R` along `P` and `wgt Q` along `P'`; the finiteness
  hypotheses come from `exDiv_finite_of_variety`.
-/

section

variable {𝕜 : Type} [Field 𝕜] {X Y Z : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y] [Variety 𝕜 Z]

/-- For `x ∈ exDiv (φ.trans ψ) ∖ exDiv φ` the map `φ` is an isomorphism at `x`: this point is
codimension one and not exceptional for `φ`. -/
private lemma isIsoAt_of_mem_diff_trans {φ : X.BirationalMap Y} {ψ : Y.BirationalMap Z}
    {x : X} (hx : x ∈ exDiv (φ.trans ψ) \ exDiv φ) : IsIsoAt φ x := by
  by_contra h
  exact hx.2 ⟨hx.1.1, h⟩

/-- For `y ∈ exDiv ψ ∖ exDiv φ.symm` the map `φ.symm` is an isomorphism at `y`: this point is
codimension one and not exceptional for `φ.symm`. -/
private lemma isIsoAt_of_mem_diff_symm {φ : X.BirationalMap Y} {ψ : Y.BirationalMap Z}
    {y : Y} (hy : y ∈ (exDiv ψ : Set Y) \ (exDiv φ.symm : Set Y)) : IsIsoAt φ.symm y := by
  by_contra h
  exact hy.2 ⟨hy.1.1, h⟩

/-- The forward map of the bijection `R ∖ P → Q ∖ P'`, `x ↦ φ(x)`, lands in `Q ∖ P'`. -/
private lemma phiPt_mem_diff_trans {φ : X.BirationalMap Y} {ψ : Y.BirationalMap Z}
    [φ.IsOver (Spec (.of 𝕜))] {x : X} (hx : x ∈ exDiv (φ.trans ψ) \ exDiv φ) :
    phiPt φ ⟨x, isIsoAt_of_mem_diff_trans (𝕜 := 𝕜) hx⟩ ∈
      (exDiv ψ : Set Y) \ (exDiv φ.symm : Set Y) := by
  have hIso : IsIsoAt φ x := isIsoAt_of_mem_diff_trans (𝕜 := 𝕜) hx
  refine ⟨⟨(coheight_phiPt φ ⟨x, hIso⟩).trans hx.1.1, ?_⟩, ?_⟩
  · intro hψ
    exact hx.1.2 ((isIsoAt_trans_iff (𝕜 := 𝕜) φ ψ x hIso).mpr hψ)
  · intro hmem
    exact hmem.2 (phiPt_symm (𝕜 := 𝕜) φ ⟨x, hIso⟩).choose

/-- The inverse map of the bijection `R ∖ P → Q ∖ P'`, `y ↦ φ⁻¹(y)`, lands in `R ∖ P`. -/
private lemma phiPt_mem_diff_symm {φ : X.BirationalMap Y} {ψ : Y.BirationalMap Z}
    [φ.IsOver (Spec (.of 𝕜))] {y : Y}
    (hy : y ∈ (exDiv ψ : Set Y) \ (exDiv φ.symm : Set Y)) :
    phiPt (φ.symm) ⟨y, isIsoAt_of_mem_diff_symm (𝕜 := 𝕜) hy⟩ ∈ exDiv (φ.trans ψ) \ exDiv φ := by
  haveI hsymm : (φ.symm).IsOver (Spec (.of 𝕜)) :=
    inferInstanceAs (φ.inv.IsOver (Spec (.of 𝕜)))
  have hIsoSymm : IsIsoAt φ.symm y := isIsoAt_of_mem_diff_symm (𝕜 := 𝕜) hy
  have hIsoφ : IsIsoAt φ (phiPt (φ.symm) ⟨y, hIsoSymm⟩) :=
    (phiPt_symm (𝕜 := 𝕜) (φ.symm) ⟨y, hIsoSymm⟩).choose
  have hval : phiPt φ ⟨phiPt (φ.symm) ⟨y, hIsoSymm⟩, hIsoφ⟩ = y :=
    (phiPt_symm (𝕜 := 𝕜) (φ.symm) ⟨y, hIsoSymm⟩).choose_spec
  refine ⟨⟨(coheight_phiPt (φ.symm) ⟨y, hIsoSymm⟩).trans hy.1.1, ?_⟩, ?_⟩
  · intro htr
    have hψ : IsIsoAt ψ (phiPt φ ⟨phiPt (φ.symm) ⟨y, hIsoSymm⟩, hIsoφ⟩) :=
      (isIsoAt_trans_iff (𝕜 := 𝕜) φ ψ _ hIsoφ).mp htr
    rw [hval] at hψ
    exact hy.1.2 hψ
  · intro hmem
    exact hmem.2 hIsoφ

/-- The forward map `R ∖ P → Q ∖ P'`. -/
private noncomputable def fwdMap {φ : X.BirationalMap Y} {ψ : Y.BirationalMap Z}
    [φ.IsOver (Spec (.of 𝕜))] :
    ↥(exDiv (φ.trans ψ) \ exDiv φ) → ↥((exDiv ψ : Set Y) \ (exDiv φ.symm : Set Y)) :=
  fun a => ⟨phiPt φ ⟨a.1, isIsoAt_of_mem_diff_trans (𝕜 := 𝕜) a.2⟩,
    phiPt_mem_diff_trans (𝕜 := 𝕜) a.2⟩

/-- The inverse map `Q ∖ P' → R ∖ P`. -/
private noncomputable def bwdMap {φ : X.BirationalMap Y} {ψ : Y.BirationalMap Z}
    [φ.IsOver (Spec (.of 𝕜))] :
    ↥((exDiv ψ : Set Y) \ (exDiv φ.symm : Set Y)) → ↥(exDiv (φ.trans ψ) \ exDiv φ) :=
  fun b => ⟨phiPt (φ.symm) ⟨b.1, isIsoAt_of_mem_diff_symm (𝕜 := 𝕜) b.2⟩,
    phiPt_mem_diff_symm (𝕜 := 𝕜) b.2⟩

/-- `phiPt φ` restricts to a bijection `R ∖ P ≃ Q ∖ P'`. -/
private noncomputable def transSdiffEquiv {φ : X.BirationalMap Y} {ψ : Y.BirationalMap Z}
    [φ.IsOver (Spec (.of 𝕜))] :
    ↥(exDiv (φ.trans ψ) \ exDiv φ) ≃ ↥((exDiv ψ : Set Y) \ (exDiv φ.symm : Set Y)) where
  toFun := fwdMap (𝕜 := 𝕜)
  invFun := bwdMap (𝕜 := 𝕜)
  left_inv a := by
    apply Subtype.ext
    show phiPt (φ.symm) ⟨phiPt φ ⟨a.1, isIsoAt_of_mem_diff_trans (𝕜 := 𝕜) a.2⟩,
      isIsoAt_of_mem_diff_symm (𝕜 := 𝕜) (phiPt_mem_diff_trans (𝕜 := 𝕜) a.2)⟩ = a.1
    obtain ⟨h, hspec⟩ := phiPt_symm (𝕜 := 𝕜) φ
      ⟨a.1, isIsoAt_of_mem_diff_trans (𝕜 := 𝕜) a.2⟩
    rw [show (⟨phiPt φ ⟨a.1, isIsoAt_of_mem_diff_trans (𝕜 := 𝕜) a.2⟩,
        isIsoAt_of_mem_diff_symm (𝕜 := 𝕜) (phiPt_mem_diff_trans (𝕜 := 𝕜) a.2)⟩ :
        {z // IsIsoAt φ.symm z}) =
      ⟨phiPt φ ⟨a.1, isIsoAt_of_mem_diff_trans (𝕜 := 𝕜) a.2⟩, h⟩ from Subtype.ext rfl]
    exact hspec
  right_inv b := by
    apply Subtype.ext
    show phiPt φ ⟨phiPt (φ.symm) ⟨b.1, isIsoAt_of_mem_diff_symm (𝕜 := 𝕜) b.2⟩,
      isIsoAt_of_mem_diff_trans (𝕜 := 𝕜) (phiPt_mem_diff_symm (𝕜 := 𝕜) b.2)⟩ = b.1
    haveI hsymm : (φ.symm).IsOver (Spec (.of 𝕜)) :=
      inferInstanceAs (φ.inv.IsOver (Spec (.of 𝕜)))
    obtain ⟨h, hspec⟩ := phiPt_symm (𝕜 := 𝕜) (φ.symm)
      ⟨b.1, isIsoAt_of_mem_diff_symm (𝕜 := 𝕜) b.2⟩
    rw [show (⟨phiPt (φ.symm) ⟨b.1, isIsoAt_of_mem_diff_symm (𝕜 := 𝕜) b.2⟩,
        isIsoAt_of_mem_diff_trans (𝕜 := 𝕜) (phiPt_mem_diff_symm (𝕜 := 𝕜) b.2)⟩ :
        {z // IsIsoAt φ z}) =
      ⟨phiPt (φ.symm) ⟨b.1, isIsoAt_of_mem_diff_symm (𝕜 := 𝕜) b.2⟩, h⟩ from Subtype.ext rfl]
    exact hspec

end

/-- **First counting identity** for the additivity of the Lin–Shinder invariant.

Writing `R = exDiv (φ.trans ψ)`, `P = exDiv φ`, `Q = exDiv ψ` and `P' = exDiv φ.symm` (so `P, R ⊆ X`
and `Q, P' ⊆ Y`), this says

`wgt R + wgt (Q ∩ P') = wgt (R ∩ P) + wgt Q`.

Proof route (all the ingredients are already proved in this workspace and are listed in
`depends_on`; `Work.Motivic.wgt`, `Work.Motivic.wgt_inter_add_wgt_sdiff`,
`Work.Motivic.wgt_eq_of_bijection` are in `Submission/Work/Motivic/cInv_add_defs.lean`,
`Work.Motivic.phiPt_symm`, `Work.Motivic.coheight_phiPt`, `Work.Motivic.ResEquiv_phiPt` in
`Submission/Work/Motivic/cInv_add_pt.lean`, `Work.Motivic.isIsoAt_trans_iff`,
`Work.Motivic.not_isIsoAt_symm` in `Submission/Work/Motivic/cInv_add_trans.lean`,
`Work.Motivic.exDiv_finite_of_variety` in `Submission/Work/Motivic/exDiv_finite_of_variety.lean`):

1. **Bijection** `R \ P → Q \ P'`, `x ↦ phiPt φ ⟨x, _⟩` (well defined since `x ∈ R \ P` gives
   `IsIsoAt φ x`; it is injective and its inverse is `y ↦ phiPt φ.symm ⟨y, _⟩`).
   * for `x ∈ R \ P`: `coheight x = 1`, `¬ IsIsoAt (φ.trans ψ) x`, `IsIsoAt φ x`.  Then
     `coheight (phiPt φ x) = 1` (`coheight_phiPt`); `¬ IsIsoAt ψ (phiPt φ x)` (otherwise
     `IsIsoAt (φ.trans ψ) x`, the `←` direction of `isIsoAt_trans_iff`); and
     `IsIsoAt φ.symm (phiPt φ x)` (from `phiPt_symm`); so `phiPt φ x ∈ Q \ P'`.
   * conversely, given `y ∈ Q \ P'`, put `x := phiPt φ.symm ⟨y, _⟩`: then `IsIsoAt φ x`
     (`phiPt_symm` for `φ.symm`), `coheight x = 1`, and `¬ IsIsoAt (φ.trans ψ) x`: if it held, the
     `→` direction of `isIsoAt_trans_iff` (applied to `φ`, `ψ`, `x`) would give
     `IsIsoAt ψ (phiPt φ x)`, and `phiPt φ x = y` because `phiPt φ` and `phiPt φ.symm` are mutually
     inverse (`phiPt_symm`), contradicting `¬ IsIsoAt ψ y`.
   * `ResEquiv 𝕜 x (phiPt φ x)` is `ResEquiv_phiPt`, so `wgt_eq_of_bijection` (applied to the
     bijection restricted to `{x ∈ R \ P | ResEquiv 𝕜 x w}`) gives
     `wgt 𝕜 w (R \ P) = wgt 𝕜 w (Q \ P')`.  No finiteness is needed for this step.
2. **Telescoping** using `wgt_inter_add_wgt_sdiff` and finiteness of the sets
   (`exDiv_finite_of_variety`; note `(R ∪ …) ∩ {x | ResEquiv 𝕜 x w}` is a subset of a finite set,
   so `Set.Finite.subset` gives the required `Finite` hypotheses):
   `wgt 𝕜 w R = wgt 𝕜 w (R ∩ P) + wgt 𝕜 w (R \ P)` and
   `wgt 𝕜 w Q = wgt 𝕜 w (Q ∩ P') + wgt 𝕜 w (Q \ P')`.
3. Combine 1 and 2 with `omega` (both sides are `ℕ`). -/
theorem wgt_exDiv_trans_add {𝕜 : Type} [Field 𝕜] {X Y Z W : Scheme.{0}} [Variety 𝕜 X]
    [Variety 𝕜 Y] [Variety 𝕜 Z] [W.Over (Spec (.of 𝕜))] (w : W) (φ : X.BirationalMap Y)
    (ψ : Y.BirationalMap Z) [φ.IsOver (Spec (.of 𝕜))] [ψ.IsOver (Spec (.of 𝕜))] :
    wgt 𝕜 w (exDiv (φ.trans ψ)) + wgt 𝕜 w (exDiv ψ ∩ exDiv φ.symm) =
      wgt 𝕜 w (exDiv (φ.trans ψ) ∩ exDiv φ) + wgt 𝕜 w (exDiv ψ) := by
  -- Step 1: `phiPt φ` is a residue-field-preserving bijection `R ∖ P ≃ Q ∖ P'`.
  have hbij : wgt 𝕜 w (exDiv (φ.trans ψ) \ exDiv φ) =
      wgt 𝕜 w ((exDiv ψ : Set Y) \ (exDiv φ.symm : Set Y)) :=
    wgt_eq_of_bijection (𝕜 := 𝕜) w (transSdiffEquiv (𝕜 := 𝕜) (φ := φ) (ψ := ψ))
      (fun a => ResEquiv_phiPt (𝕜 := 𝕜) φ
        ⟨a.1, isIsoAt_of_mem_diff_trans (𝕜 := 𝕜) a.2⟩)
  -- Step 2: telescope `wgt R` along `P` and `wgt Q` along `P'`.
  have hR := wgt_inter_add_wgt_sdiff (𝕜 := 𝕜) w
    (A := exDiv (φ.trans ψ)) (B := exDiv φ) (exDiv_finite_of_variety 𝕜 (φ.trans ψ))
  have hQ := wgt_inter_add_wgt_sdiff (𝕜 := 𝕜) w
    (A := (exDiv ψ : Set Y)) (B := (exDiv φ.symm : Set Y)) (exDiv_finite_of_variety 𝕜 ψ)
  -- Step 3: add the two telescoping identities and use the bijection.
  omega

end Work.Motivic
