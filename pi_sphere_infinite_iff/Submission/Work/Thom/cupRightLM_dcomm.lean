/-
# The cup product with a relative cocycle commutes with the differentials

`Work.Thom.cupRightLM t B' i` (`Submission/Work/Thom/cupDeltaInfra.lean`) is the linear map

`C^i(Y,B') → C^{i+n}(Y,B)`,  `c ↦ c ⌣ t`,

given by the Alexander–Whitney product with a *cocycle* `t ∈ C^n(Y,B)`.  Here we prove that it is
a morphism of cochain complexes of degree `n`, i.e. that it commutes with the differentials once
the target is shifted by `n` (`Tsq.shK`):

`cupRightLM t B' i ≫ d^{i+n}_{sh} = d^i_{C^*(Y,B')} ≫ cupRightLM t B' (i+1)`.

By the Leibniz rule `δ(a ⌣ b) = (δa) ⌣ b + (-1)^a · a ⌣ (δb)` (`Work.Cohomology.cupLeibniz`) and
the hypothesis `δt = 0` this reduces to `δ(c ⌣ t) = (δc) ⌣ t`: the two sides of the identity are
evaluated on an element and compared in the underlying cochain module, where both equal
`(δc) ⌣ t`.  The only bookkeeping is the degree equality `(i+1)+n = i+(n+1)`, handled by the
transports `eqRec_symm_eqRec` and `relComplex_d_val` below.

To make the definitional equalities involved in the shift of a complex (`Tsq.shK K n = K.restriction
(shEmb n)`) usable at the transparency of proof automation, the relevant semireducible definitions
are marked `[local implicit_reducible]` in this file.
-/

import Mathlib
import Submission.Work.Thom.cupDeltaInfra

open CategoryTheory CategoryTheory.Limits

namespace Work.Thom

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

attribute [local implicit_reducible] Work.Cohomology.relComplex
attribute [local implicit_reducible] Work.Cohomology.singularCochainComplex
attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor
attribute [local implicit_reducible] ComplexShape.Embedding.mk'
attribute [local implicit_reducible] HomologicalComplex.restriction
attribute [local implicit_reducible] TopCat.toSSet

/-! ## Elementary transport lemmas -/

/-- Transporting an element back and forth along an equality of natural numbers is the identity. -/
lemma cupRightLM_eqRec_symm_eqRec (F : ℕ → Type*) {a b : ℕ} (h : a = b) (y : F a) :
    (h.symm ▸ (h ▸ y) : F a) = y := by
  cases h; rfl

/-- The transport of a relative cochain along an equality of degrees, on the underlying
Alexander–Whitney cochains. -/
lemma cupRightLM_XIsoOfEq_coe {Y : TopCat} {B : Set Y} {k j : ℕ} (h : k = j)
    (y : (Work.Cohomology.relComplex ℤ Y B).X k) :
    (((Work.Cohomology.relComplex ℤ Y B).XIsoOfEq h).hom y).1 =
      (h ▸ (y.1 : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj Y) k) :
        Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj Y) j) := by
  subst h; simp

/-- The differential of the relative complex at a pair of equal (but not syntactically identical)
indices, in terms of the differential at the canonical indices and the transport. -/
lemma cupRightLM_relComplex_d_val {Y : TopCat} {B : Set Y} {k j : ℕ} (h : k + 1 = j)
    (u : (Work.Cohomology.relComplex ℤ Y B).X k) :
    ((Work.Cohomology.relComplex ℤ Y B).d k j).hom u
      = ((Work.Cohomology.relComplex ℤ Y B).XIsoOfEq h).hom
        (Work.Cohomology.relDiffLM ℤ Y B k u) := by
  have hd := HomologicalComplex.d_comp_XIsoOfEq_hom (Work.Cohomology.relComplex ℤ Y B) h k
  rw [← hd, ModuleCat.hom_comp, LinearMap.comp_apply, Work.Cohomology.relComplex_d]
  rfl

/-- **The Leibniz rule with one factor a cocycle**: for a cochain `ψ` of degree `p` and a cocycle
`t'` of degree `n`, `δ(ψ ⌣ t') = (δψ) ⌣ t'`, with the product transported along
`(p+1)+n = p+n+1`. -/
lemma cupRightLM_cup_cochainDiff_of_cocycle (X : SSet) (p n : ℕ)
    (ψ : Work.Cohomology.Cochain ℤ X p) (t' : Work.Cohomology.Cochain ℤ X n)
    (hdt : Work.Cohomology.cochainDiff ℤ X t' = 0) (h : (p+1)+n = p+n+1) :
    Work.Cohomology.cochainDiff ℤ X (Work.Cohomology.cup ℤ X ψ t')
      = h ▸ (Work.Cohomology.cup ℤ X (Work.Cohomology.cochainDiff ℤ X ψ) t') := by
  have hleib := Work.Cohomology.cupLeibniz ℤ X ψ t'
  rw [hdt] at hleib
  rw [Work.Cohomology.cup_zero_right', smul_zero, add_zero] at hleib
  have hh : Nat.add_right_comm p 1 n = h := Subsingleton.elim _ _
  rwa [hh] at hleib

/-! ## The two sides of the identity, evaluated on an element -/

/-- The left hand side, applied to `c`, is `(δc) ⌣ t`. -/
lemma cupRightLM_dcomm_lhs_val {Y : TopCat} {B : Set Y} {n : ℕ}
    (τ : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj Y) n)
    (hτ : τ ∈ Work.Cohomology.relKern ℤ Y B n)
    (ht : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj Y) τ = 0)
    (B' : Set Y) (i : ℕ)
    (c : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj Y) i)
    (hc : c ∈ Work.Cohomology.relKern ℤ Y B' i) :
    ((((Tsq.shK (Work.Cohomology.relComplex ℤ Y B) n).d i (i+1)).hom
        ((ModuleCat.ofHom (Work.Thom.cupRightLM
            (⟨τ, hτ⟩ : ↥((Work.Cohomology.relComplex ℤ Y B).X n)) B' i)).hom
          (⟨c, hc⟩ : ↥((Work.Cohomology.relComplex ℤ Y B').X i))))).1
      = Work.Cohomology.cup ℤ (TopCat.toSSet.obj Y)
          (Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj Y) c) τ := by
  have h₁ : (i+1) + n = i + n + 1 := Nat.add_right_comm i 1 n
  simp only [Tsq.shK_d, Tsq.shK_X]
  rw [cupRightLM_relComplex_d_val (h := h₁.symm)]
  rw [cupRightLM_XIsoOfEq_coe (h := h₁.symm)]
  simp only [ModuleCat.hom_ofHom, Work.Cohomology.relDiffLM_coe,
    Work.Cohomology.singularCochain_d_apply, Work.Thom.cupRightLM_apply]
  rw [cupRightLM_cup_cochainDiff_of_cocycle (TopCat.toSSet.obj Y) i n c τ ht h₁]
  rw [cupRightLM_eqRec_symm_eqRec (fun x => Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj Y) x) h₁]

/-- The right hand side, applied to `c`, is `(δc) ⌣ t` as well. -/
lemma cupRightLM_dcomm_rhs_val {Y : TopCat} {B : Set Y} {n : ℕ}
    (τ : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj Y) n)
    (hτ : τ ∈ Work.Cohomology.relKern ℤ Y B n)
    (B' : Set Y) (i : ℕ)
    (c : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj Y) i)
    (hc : c ∈ Work.Cohomology.relKern ℤ Y B' i) :
    (ModuleCat.Hom.hom (ModuleCat.ofHom (Work.Thom.cupRightLM
        (⟨τ, hτ⟩ : ↥((Work.Cohomology.relComplex ℤ Y B).X n)) B' (i+1)))
        (ModuleCat.Hom.hom ((Work.Cohomology.relComplex ℤ Y B').d i (i+1))
          (⟨c, hc⟩ : ↥((Work.Cohomology.relComplex ℤ Y B').X i)))).1
      = Work.Cohomology.cup ℤ (TopCat.toSSet.obj Y)
          (Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj Y) c) τ := by
  simp only [ModuleCat.hom_ofHom, Work.Cohomology.relComplex_d_apply,
    Work.Cohomology.relDiffLM_coe,
    Work.Cohomology.singularCochain_d_apply, Work.Thom.cupRightLM_apply]

/-! ## The main identity -/

theorem cupRightLM_dcomm {Y : TopCat} {B : Set Y} {n : ℕ}
    (t : ↥((Work.Cohomology.relComplex ℤ Y B).X n))
    (ht : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj Y) t.1 = 0)
    (B' : Set Y) (i : ℕ) :
    CategoryTheory.CategoryStruct.comp (ModuleCat.ofHom (Work.Thom.cupRightLM t B' i))
        ((Work.Thom.Tsq.shK (Work.Cohomology.relComplex ℤ Y B) n).d i (i + 1))
      = CategoryTheory.CategoryStruct.comp ((Work.Cohomology.relComplex ℤ Y B').d i (i + 1))
        (ModuleCat.ofHom (Work.Thom.cupRightLM t B' (i + 1))) := by
  obtain ⟨τ, hτ⟩ := t
  have htτ : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj Y) τ = 0 := ht
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  apply LinearMap.ext
  intro x
  obtain ⟨c, hc⟩ := x
  simp only [LinearMap.comp_apply]
  rw [Subtype.ext_iff]
  exact (cupRightLM_dcomm_lhs_val τ hτ htτ B' i c hc).trans
    (cupRightLM_dcomm_rhs_val τ hτ B' i c hc).symm

end

end Work.Thom
