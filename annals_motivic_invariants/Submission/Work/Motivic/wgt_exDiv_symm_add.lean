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

set_option linter.style.haveILetI false

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

/-!
# The second counting identity for the additivity of the Lin–Shinder invariant

`wgt 𝕜 w (exDiv φ) + wgt 𝕜 w (exDiv ψ.symm ∩ exDiv (φ.trans ψ).symm)
  = wgt 𝕜 w (exDiv (φ.trans ψ) ∩ exDiv φ) + wgt 𝕜 w (exDiv ψ.symm)`

The proof has two halves.

* A bijection `exDiv φ \ exDiv (φ.trans ψ) → exDiv ψ.symm \ exDiv (φ.trans ψ).symm`, given on a
  point `x` by `phiPt (φ.trans ψ) x`, matching residue fields (`ResEquiv_phiPt`), hence preserving
  weights (`wgt_eq_of_bijection`).  Well-definedness of `phiPt` (independence of the chosen
  witness of `IsIsoAt`) is `phiPt_proof_irrel`, and the two maps are mutually inverse by
  `phiPt_symm` (`phiPt_symm_apply`).
* Telescoping `wgt P = wgt (P ∩ R) + wgt (P \ R)` and `wgt Q' = wgt (Q' ∩ S) + wgt (Q' \ S)`
  using `wgt_inter_add_wgt_sdiff` and finiteness of the exceptional sets
  (`exDiv_finite_of_variety`), plus `wgt (P ∩ R) = wgt (R ∩ P)`.
-/

section Aux

/-- `phiPt φ x` does not depend on the chosen proof that `φ` is an isomorphism at `x`. -/
private lemma phiPt_proof_irrel {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}} [Variety 𝕜 X]
    [Variety 𝕜 Y] (φ : X.BirationalMap Y) [φ.IsOver (Spec (.of 𝕜))] (x : X)
    (h₁ h₂ : IsIsoAt φ x) : phiPt φ ⟨x, h₁⟩ = phiPt φ ⟨x, h₂⟩ := by
  have h : ∀ (k : IsIsoAt φ x),
      phiPt φ ⟨x, k⟩ = h₁.choose.target.ι (h₁.choose.iso.hom ⟨x, h₁.choose_spec.1⟩) :=
    fun k => phiPt_eq_of_rep (𝕜 := 𝕜) (φ := φ) (x := x) (h := k) (i := h₁.choose)
      h₁.choose_spec.2 h₁.choose_spec.1
  exact (h h₁).trans (h h₂).symm

/-- `phiPt φ.symm` is a left inverse of `phiPt φ`, for *any* witness that `φ.symm` is an
isomorphism at the image point. -/
private lemma phiPt_symm_apply {𝕜 : Type} [Field 𝕜] {X Y : Scheme.{0}} [Variety 𝕜 X]
    [Variety 𝕜 Y] (φ : X.BirationalMap Y) [φ.IsOver (Spec (.of 𝕜))]
    (p : {x : X // IsIsoAt φ x}) (h : IsIsoAt φ.symm (phiPt φ p)) :
    phiPt φ.symm ⟨phiPt φ p, h⟩ = p.1 := by
  haveI hsymm : (φ.symm).IsOver (Spec (.of 𝕜)) :=
    inferInstanceAs (φ.inv.IsOver (Spec (.of 𝕜)))
  rw [phiPt_proof_irrel (𝕜 := 𝕜) (X := Y) (Y := X) (φ := φ.symm) (x := phiPt φ p) h
      (phiPt_symm (𝕜 := 𝕜) (X := X) (Y := Y) φ p).choose]
  exact (phiPt_symm (𝕜 := 𝕜) (X := X) (Y := Y) φ p).choose_spec

/-- A codimension-one point at which `φ` is not listed as exceptional *is* a point at which `φ`
is an isomorphism. -/
private lemma IsIsoAt_of_notMem_exDiv {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (φ : X.BirationalMap Y) {x : X} (h1 : coheight x = 1) (hx : x ∉ exDiv φ) :
    IsIsoAt φ x := by
  by_contra h
  exact hx ⟨h1, h⟩

/-- The weight of `exDiv φ \ exDiv (φ.trans ψ)` equals the weight of
`exDiv ψ.symm \ exDiv (φ.trans ψ).symm`: the point map of `φ.trans ψ` is a bijection between these
two sets, and it matches residue fields. -/
private lemma wgt_exDiv_sdiff_bijection {𝕜 : Type} [Field 𝕜] {X Y Z W : Scheme.{0}}
    [Variety 𝕜 X] [Variety 𝕜 Y] [Variety 𝕜 Z] [W.Over (Spec (.of 𝕜))] (w : W)
    (φ : X.BirationalMap Y) (ψ : Y.BirationalMap Z) [φ.IsOver (Spec (.of 𝕜))]
    [ψ.IsOver (Spec (.of 𝕜))] :
    wgt 𝕜 w (exDiv φ \ exDiv (φ.trans ψ)) =
      wgt 𝕜 w (exDiv ψ.symm \ exDiv (φ.trans ψ).symm) := by
  haveI htrans : (φ.trans ψ).IsOver (Spec (.of 𝕜)) := by
    change (φ.hom.comp ψ.hom).IsOver (Spec (.of 𝕜)); infer_instance
  haveI htranss : ((φ.trans ψ).symm).IsOver (Spec (.of 𝕜)) :=
    inferInstanceAs ((φ.trans ψ).inv.IsOver (Spec (.of 𝕜)))
  -- the forward map `x ↦ phiPt (φ.trans ψ) x`
  have hF : ∀ a : ↥(exDiv φ \ exDiv (φ.trans ψ)), IsIsoAt (φ.trans ψ) a.1 := fun a =>
    IsIsoAt_of_notMem_exDiv (φ.trans ψ) a.2.1.1 a.2.2
  have hFmem : ∀ a : ↥(exDiv φ \ exDiv (φ.trans ψ)),
      phiPt (φ.trans ψ) ⟨a.1, hF a⟩ ∈ exDiv ψ.symm \ exDiv (φ.trans ψ).symm := by
    intro a
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [coheight_phiPt]; exact a.2.1.1
    · exact not_isIsoAt_symm (𝕜 := 𝕜) (X := X) (Y := Y) (Z := Z) φ ψ a.1 a.2.1.2 (hF a)
    · intro h
      exact h.2 (phiPt_symm (𝕜 := 𝕜) (X := X) (Y := Z) (φ.trans ψ) ⟨a.1, hF a⟩).choose
  -- the backward map `z ↦ phiPt (φ.trans ψ).symm z`
  have hG : ∀ b : ↥(exDiv ψ.symm \ exDiv (φ.trans ψ).symm), IsIsoAt (φ.trans ψ).symm b.1 := fun b =>
    IsIsoAt_of_notMem_exDiv (φ.trans ψ).symm b.2.1.1 b.2.2
  have hGmem : ∀ b : ↥(exDiv ψ.symm \ exDiv (φ.trans ψ).symm),
      phiPt (φ.trans ψ).symm ⟨b.1, hG b⟩ ∈ exDiv φ \ exDiv (φ.trans ψ) := by
    intro b
    haveI hψs : (ψ.symm).IsOver (Spec (.of 𝕜)) :=
      inferInstanceAs (ψ.inv.IsOver (Spec (.of 𝕜)))
    haveI hφs : (φ.symm).IsOver (Spec (.of 𝕜)) :=
      inferInstanceAs (φ.inv.IsOver (Spec (.of 𝕜)))
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [coheight_phiPt]; exact b.2.1.1
    · exact not_isIsoAt_symm (𝕜 := 𝕜) (X := Z) (Y := Y) (Z := X) ψ.symm φ.symm b.1 b.2.1.2 (hG b)
    · intro h
      exact h.2 (phiPt_symm (𝕜 := 𝕜) (X := Z) (Y := X) ((φ.trans ψ).symm) ⟨b.1, hG b⟩).choose
  refine wgt_eq_of_bijection (𝕜 := 𝕜) w (A := exDiv φ \ exDiv (φ.trans ψ))
    (B := exDiv ψ.symm \ exDiv ((φ.trans ψ).symm)) ?_ ?_
  · refine ⟨fun a => ⟨phiPt (φ.trans ψ) ⟨a.1, hF a⟩, hFmem a⟩,
            fun b => ⟨phiPt (φ.trans ψ).symm ⟨b.1, hG b⟩, hGmem b⟩, ?_, ?_⟩
    · intro a
      apply Subtype.ext
      exact phiPt_symm_apply (𝕜 := 𝕜) (X := X) (Y := Z) (φ.trans ψ) ⟨a.1, hF a⟩ _
    · intro b
      apply Subtype.ext
      exact phiPt_symm_apply (𝕜 := 𝕜) (X := Z) (Y := X) ((φ.trans ψ).symm) ⟨b.1, hG b⟩ _
  · intro a
    exact ResEquiv_phiPt (𝕜 := 𝕜) (X := X) (Y := Z) (φ.trans ψ) ⟨a.1, hF a⟩

end Aux

/-- **Second counting identity** for the additivity of the Lin–Shinder invariant.

Writing `R = exDiv (φ.trans ψ)`, `P = exDiv φ`, `Q' = exDiv ψ.symm` and `S = exDiv (φ.trans ψ).symm`
(so `P, R ⊆ X` and `Q', S ⊆ Z`; note `(φ.trans ψ).symm = ψ.symm.trans φ.symm`), this says

`wgt P + wgt (Q' ∩ S) = wgt (R ∩ P) + wgt Q'`.

Proof route: the point map of `φ.trans ψ` is a weight-preserving bijection
`P \ R → Q' \ S` (`wgt_exDiv_sdiff_bijection`), and `wgt` telescopes over the partitions
`P = (P ∩ R) ⊔ (P \ R)`, `Q' = (Q' ∩ S) ⊔ (Q' \ S)` (`wgt_inter_add_wgt_sdiff`,
finiteness by `exDiv_finite_of_variety`).  Combining, and replacing `P ∩ R` by `R ∩ P`, gives the
identity. -/
theorem wgt_exDiv_symm_add {𝕜 : Type} [Field 𝕜] {X Y Z W : Scheme.{0}} [Variety 𝕜 X]
    [Variety 𝕜 Y] [Variety 𝕜 Z] [W.Over (Spec (.of 𝕜))] (w : W) (φ : X.BirationalMap Y)
    (ψ : Y.BirationalMap Z) [φ.IsOver (Spec (.of 𝕜))] [ψ.IsOver (Spec (.of 𝕜))] :
    wgt 𝕜 w (exDiv φ) + wgt 𝕜 w (exDiv ψ.symm ∩ exDiv (φ.trans ψ).symm) =
      wgt 𝕜 w (exDiv (φ.trans ψ) ∩ exDiv φ) + wgt 𝕜 w (exDiv ψ.symm) := by
  have h1 := wgt_inter_add_wgt_sdiff (𝕜 := 𝕜) (w := w) (A := exDiv φ) (B := exDiv (φ.trans ψ))
    (exDiv_finite_of_variety 𝕜 φ)
  have h2 := wgt_inter_add_wgt_sdiff (𝕜 := 𝕜) (w := w) (A := exDiv ψ.symm)
    (B := exDiv (φ.trans ψ).symm) (exDiv_finite_of_variety 𝕜 ψ.symm)
  have h3 := wgt_exDiv_sdiff_bijection (𝕜 := 𝕜) w φ ψ
  have h4 := wgt_congr (𝕜 := 𝕜) w (Set.inter_comm (exDiv φ) (exDiv (φ.trans ψ)))
  omega

end Work.Motivic
