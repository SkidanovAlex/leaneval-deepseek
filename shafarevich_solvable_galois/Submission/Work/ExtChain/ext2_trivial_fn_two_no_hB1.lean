import Mathlib
import Submission.Work.ExtChain.ext2_trivial_fn_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ExtChain

open CategoryTheory

set_option linter.style.haveILetI false

noncomputable section

/-- **Injectivity of the edge map `α_A : Ext²_H(𝔽_p,A) → Ext²_H(ℤ,A) = H²(H,A)`** of the coefficient
sequence `0 → ℤ --p--> ℤ → 𝔽_p → 0`, using only `H¹(H,A) = 0`.

The contravariant long exact sequence of `coeffSES` reads

  `Ext¹(ℤ,A) --·p--> Ext¹(ℤ,A) --δ--> Ext²(𝔽_p,A) --α_A--> Ext²(ℤ,A)`,

and exactness at `Ext²(𝔽_p,A)` identifies `ker α_A` with the image of the connecting map `δ`, whose
source `Ext¹(ℤ,A) = H¹(H,A)` is trivial by hypothesis.  Hence `α_A` is injective. -/
private lemma coeffSES_edge_injective {p : ℕ} [Fact p.Prime] {H : Type} [Group H]
    (A : Rep.{0} SSGRoute.PTExt.Coeff H)
    (hA1 : Subsingleton (CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.unitRep H) A 1)) :
    Function.Injective (fun z : CategoryTheory.Abelian.Ext.{0}
        (Work.SSGRoute.Phi1.coeffSES H p).X₃ A 2 =>
      (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.Phi1.coeffSES H p).g).comp z (zero_add 2)) := by
  have hS := Work.SSGRoute.Phi1.coeffSES_shortExact H p
  haveI : Subsingleton (CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.Phi1.coeffSES H p).X₁ A 1) := hA1
  -- the kernel of the edge map is trivial: exactness exhibits any element of it as the image of
  -- the connecting map, whose source `Ext¹(ℤ,A)` is a subsingleton.
  have hker : ∀ z : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.Phi1.coeffSES H p).X₃ A 2,
      (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.Phi1.coeffSES H p).g).comp z
          (zero_add 2) = 0 → z = 0 := by
    intro z hz
    obtain ⟨x₁, hx₁⟩ := CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃ hS A z hz
      (show 1 + 1 = 2 by norm_num)
    have hx₁0 : x₁ = 0 := Subsingleton.elim _ _
    rw [hx₁0] at hx₁
    rw [CategoryTheory.Abelian.Ext.comp_zero] at hx₁
    exact hx₁.symm
  intro z w hzw
  dsimp only at hzw
  have hsub : (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.Phi1.coeffSES H p).g).comp (z - w)
      (zero_add 2) = 0 := by
    rw [sub_eq_add_neg, CategoryTheory.Abelian.Ext.comp_add,
      CategoryTheory.Abelian.Ext.comp_neg, hzw, add_neg_cancel]
  have h0 : z - w = 0 := hker (z - w) hsub
  exact sub_eq_zero.mp h0

/-- **Naturality of the edge map** `α` of the coefficient sequence `0 → ℤ --p--> ℤ → 𝔽_p → 0` in
the coefficient: for a coefficient morphism `φ : A ⟶ B`, the square

  `Ext²(𝔽_p,A) --α_A--> Ext²(ℤ,A)`
  `     φ↓                    φ↓`
  `Ext²(𝔽_p,B) --α_B--> Ext²(ℤ,B)`

commutes, since both composites are associativity of the Yoneda product with `φ`. -/
private lemma coeffSES_edge_natural {p : ℕ} {H : Type} [Group H]
    (A B : Rep.{0} SSGRoute.PTExt.Coeff H) (φ : A ⟶ B)
    (z : CategoryTheory.Abelian.Ext.{0} (Work.SSGRoute.Phi1.coeffSES H p).X₃ A 2) :
    ((CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.Phi1.coeffSES H p).g).comp z (zero_add 2)).comp
        (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2) =
      (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.Phi1.coeffSES H p).g).comp
        (z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2)) (zero_add 2) :=
  CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero
    (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.Phi1.coeffSES H p).g) z
    (CategoryTheory.Abelian.Ext.mk₀ φ) (zero_add 2)

/-- **Degree-two Hasse principle for the trivial `𝔽_p`-coefficient, in a group of order two, without
the redundant hypothesis `H¹(H,B) = 0`.**

This is the companion of `Work.ExtChain.ext2_trivial_fn_two`
(`Submission/Work/ExtChain/ext2_trivial_fn_two.lean`), whose proof in fact never uses its
hypothesis `hB1 : Subsingleton (Ext¹(unitRep H, B))`: the square

  `Ext²(𝔽_p,A) --α_A--> Ext²(ℤ,A) = H²(H,A)`
  `   φ↓                            φ↓`
  `Ext²(𝔽_p,B) --α_B--> Ext²(ℤ,B) = H²(H,B)`

together with injectivity of `α_A` (from `H¹(H,A) = 0`) and injectivity of the right vertical map
suffices.  This statement records that fact, dropping `hB1` so that it applies to coefficient pairs
`A = Kˣ`, `B = 𝕀_K` for which `H¹(H, 𝕀_K) = 0` is not available in the workspace. -/
theorem ext2_trivial_fn_two_no_hB1 {p : ℕ} [Fact p.Prime] {H : Type} [Group H]
    (hH : Nat.card H = 2) (A B : Rep.{0} SSGRoute.PTExt.Coeff H) (φ : A ⟶ B)
    (hA1 : Subsingleton (CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.unitRep H) A 1))
    (hφ : Function.Injective (fun z : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.unitRep H) A 2 =>
      z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2))) :
    Function.Injective (fun z : CategoryTheory.Abelian.Ext.{0}
      (Rep.trivial SSGRoute.PTExt.Coeff H (ZMod p)) A 2 =>
      z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2)) := by
  have hinj := coeffSES_edge_injective (p := p) (H := H) A hA1
  -- the same statement with the codomain spelled as `Ext²(ℤ,A)` of the coefficient sequence
  have hφ' : Function.Injective (fun z : CategoryTheory.Abelian.Ext.{0}
        (Work.SSGRoute.Phi1.coeffSES H p).X₂ A 2 =>
      z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2)) := hφ
  have main : Function.Injective (fun z : CategoryTheory.Abelian.Ext.{0}
        (Work.SSGRoute.Phi1.coeffSES H p).X₃ A 2 =>
      z.comp (CategoryTheory.Abelian.Ext.mk₀ φ) (add_zero 2)) := by
    intro x y hxy
    dsimp only at hxy
    -- it suffices to show `α_A x = α_A y`, and `hφ` turns this into an equality after `φ`
    apply hinj
    apply hφ'
    dsimp only
    rw [coeffSES_edge_natural (p := p) (H := H) A B φ x,
      coeffSES_edge_natural (p := p) (H := H) A B φ y, hxy]
  exact main

end

end Work.ExtChain
