import Mathlib
import Submission.Work.Kunneth.EZAWDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Extensionality for morphisms out of the tensor product of two singular chain complexes

`Work.Kunneth.tChain X Y` is the tensor product `C_*(X) ⊗_ℤ C_*(Y)` of the two singular chain
complexes; its degree-`n` part is the direct sum `⨁_{p+q=n} C_p(X) ⊗_ℤ C_q(Y)` (`Work.Kunneth.tpC`,
whose summands are included by `Work.Kunneth.tpLof`).  This file proves that a morphism out of
`(tChain X Y).X n` is determined by its values on the elementary tensors `genCh X σ ⊗ genCh Y τ`
of generators of the two chain complexes — the shape in which maps out of the Künneth complex are
computed.

The ingredients are

* `chainComplex_linear_ext` — a `ℤ`-linear map out of the degree-`k` chains of a simplicial set is
  determined by its values on the generators `genCh S σ` (Mathlib's `SSet.chainComplex_hom_ext`
  transported to `ℤ`-linear maps);
* `curry_comm_apply` — the curried form of a bilinear map in its second variable, obtained from
  `TensorProduct.curry` and the symmetry of the tensor product;
* `tmul_gen_ext` — a `ℤ`-linear map out of the summand `C_p(X) ⊗_ℤ C_q(Y)` is determined by its
  values on the elementary tensors of generators, obtained by applying the first point once in each
  variable;
* `tChain_hom_ext` — the direct-sum step, assembling the summand-wise statements.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- **Extensionality on the generators of the singular chains.**  A `ℤ`-linear map out of the
degree-`k` chains of a simplicial set is determined by its values on the generators `genCh S σ`. -/
lemma chainComplex_linear_ext {S : SSet} {k : ℕ} {N : Type} [AddCommGroup N] [Module ℤ N]
    {L L' : ↥((sChain S).X k) →ₗ[ℤ] N}
    (h : ∀ σ : S _⦋k⦌, L (genCh S σ) = L' (genCh S σ)) : L = L' := by
  have hmor : ModuleCat.ofHom L = ModuleCat.ofHom L' := by
    apply SSet.chainComplex_hom_ext (C := ModuleCat ℤ) (R := zz) (n := k)
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, genCh] using h σ
  exact congrArg ModuleCat.Hom.hom hmor

/-- The curried form of a bilinear map `B` in its second variable: for fixed `y`,
`x ↦ B (x ⊗ y)` is the linear map obtained by currying `B` composed with the symmetry of the
tensor product, evaluated at `y`. -/
lemma curry_comm_apply {X Y : SSet} {p q : ℕ} {M : ModuleCat.{0,0} ℤ}
    (B : tpSummand (sChain X) (sChain Y) p q →ₗ[ℤ] ↥M) (y : ↥((sChain Y).X q))
    (x : ↥((sChain X).X p)) :
    (TensorProduct.curry (B.comp
        (TensorProduct.comm ℤ ↥((sChain Y).X q) ↥((sChain X).X p)).toLinearMap)) y x
      = B (x ⊗ₜ[ℤ] y) := by
  rw [TensorProduct.curry_apply, LinearMap.comp_apply]
  exact congrArg B (TensorProduct.comm_tmul ℤ ↥((sChain Y).X q) ↥((sChain X).X p) y x)

/-- **Bilinear extensionality on generators.**  Two `ℤ`-linear maps out of the summand
`C_p(X) ⊗_ℤ C_q(Y)` of the tensor product of the two singular chain complexes that agree on every
elementary tensor `genCh X σ ⊗ genCh Y τ` of generators are equal.

The proof applies `chainComplex_linear_ext` once in each variable: first in the variable `x` for
each generator `genCh Y τ` of the second factor, then in the variable `y` for every `x`. -/
lemma tmul_gen_ext {X Y : SSet} {p q : ℕ} {M : ModuleCat.{0,0} ℤ}
    {B B' : tpSummand (sChain X) (sChain Y) p q →ₗ[ℤ] ↥M}
    (h : ∀ (σ : X _⦋p⦌) (τ : Y _⦋q⦌),
        B (genCh X σ ⊗ₜ[ℤ] genCh Y τ) = B' (genCh X σ ⊗ₜ[ℤ] genCh Y τ)) : B = B' := by
  -- Step 1: for every generator `τ` of `Y`, the maps `x ↦ B (x ⊗ τ)` and `x ↦ B' (x ⊗ τ)` agree.
  have h1 : ∀ τ : Y _⦋q⦌,
      (TensorProduct.curry (B.comp
          (TensorProduct.comm ℤ ↥((sChain Y).X q) ↥((sChain X).X p)).toLinearMap)) (genCh Y τ)
        = (TensorProduct.curry (B'.comp
          (TensorProduct.comm ℤ ↥((sChain Y).X q) ↥((sChain X).X p)).toLinearMap)) (genCh Y τ) := by
    intro τ
    apply chainComplex_linear_ext (S := X) (k := p)
    intro σ
    rw [curry_comm_apply, curry_comm_apply]
    exact h σ τ
  -- Step 2: for every `x`, the maps `y ↦ B (x ⊗ y)` and `y ↦ B' (x ⊗ y)` agree.
  have h2 : ∀ x : ↥((sChain X).X p),
      (TensorProduct.curry B) x = (TensorProduct.curry B') x := by
    intro x
    apply chainComplex_linear_ext (S := Y) (k := q)
    intro τ
    have hx := congrArg (fun (f : ↥((sChain X).X p) →ₗ[ℤ] ↥M) => f x) (h1 τ)
    rw [curry_comm_apply, curry_comm_apply] at hx
    rw [TensorProduct.curry_apply, TensorProduct.curry_apply]
    exact hx
  -- Step 3: the two bilinear maps agree on every elementary tensor.
  refine TensorProduct.ext' (fun x y => ?_)
  have hy := congrArg (fun (g : ↥((sChain Y).X q) →ₗ[ℤ] ↥M) => g y) (h2 x)
  rw [TensorProduct.curry_apply, TensorProduct.curry_apply] at hy
  exact hy

theorem tChain_hom_ext {X Y : SSet} {n : ℕ} {M : ModuleCat ℤ}
    (f g : (Work.Kunneth.tChain X Y).X n ⟶ M)
    (h : ∀ (p q : ℕ) (hpq : p + q = n)
      (σ : X.obj (Opposite.op (SimplexCategory.mk p)))
      (τ : Y.obj (Opposite.op (SimplexCategory.mk q))),
      ModuleCat.Hom.hom f (Work.Kunneth.tpLof (Work.Kunneth.sChain X) (Work.Kunneth.sChain Y) n
          ⟨(p, q), hpq⟩ (TensorProduct.tmul ℤ (Work.Kunneth.genCh X σ) (Work.Kunneth.genCh Y τ)))
        = ModuleCat.Hom.hom g (Work.Kunneth.tpLof (Work.Kunneth.sChain X) (Work.Kunneth.sChain Y) n
          ⟨(p, q), hpq⟩ (TensorProduct.tmul ℤ (Work.Kunneth.genCh X σ) (Work.Kunneth.genCh Y τ)))) :
    f = g := by
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro pq
  obtain ⟨⟨p, q⟩, hpq⟩ := pq
  refine tmul_gen_ext (fun σ τ => ?_)
  exact h p q hpq σ τ

end

end Work.Kunneth
