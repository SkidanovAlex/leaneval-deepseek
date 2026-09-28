import Mathlib
import Submission.Work.Kunneth.Tensor
import Submission.Work.KunnethEZ.Defs
import Submission.Work.Cohomology.AlexanderWhitney

/-!
# The singular chains of a simplicial set and the Alexander–Whitney map

This file sets up the objects of the `Work.Kunneth` chapter, for a simplicial set `X`
(the singular simplicial set `TopCat.toSSet.obj X` of a topological space `X` in the
applications):

* `sChain X` — the singular chain complex of `X` with `ℤ` coefficients (this is
  `Work.Cohomology.chainC ℤ X`, definitionally);
* `zz` — `ℤ` regarded as a `ℤ`-module;
* `genChain X σ` — the generator of `C_n(X)` attached to a simplex `σ`, as a map `ℤ ⟶ C_n(X)`;
* `genTensor X Y σ τ` — the generator `σ ⊗ τ` of `C_p(X) ⊗_ℤ C_q(Y)`, as a map
  `ℤ ⟶ C_p(X) ⊗ C_q(Y)`;
* `backInclLE`, `backFaceLE` — the back `q`-face of an `n`-simplex for any `q ≤ n`
  (the existing `Work.Cohomology.backFace` is the case `n = p + q`);
* `awGen`, `awHom` — the **Alexander–Whitney map** `C_n(X × Y) ⟶ ⨁_{p+q=n} C_p(X) ⊗ C_q(Y)`,
  `(σ,τ) ↦ Σ_{p+q=n} σ_front_p ⊗ τ_back_q`.

The chain-map property of `awHom` and the corresponding shuffle map `ezHom` in the reverse
direction are proved in the companion files (`awHom_d`, `ezHom`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- `ℤ` regarded as a `ℤ`-module. -/
abbrev zz : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- The singular chain complex of a simplicial set, with `ℤ` coefficients. -/
abbrev sChain (X : SSet) : ChainComplex (ModuleCat ℤ) ℕ := X.chainComplex zz

/-- The singular chain complex of a topological space, with `ℤ` coefficients. -/
abbrev TChain (X : TopCat) : ChainComplex (ModuleCat ℤ) ℕ := sChain (TopCat.toSSet.obj X)

/-- **The tensor product of the singular chain complexes of `X` and `Y`.** -/
abbrev tChain (X Y : SSet) : ChainComplex (ModuleCat ℤ) ℕ := tpC (sChain X) (sChain Y)

/-- The product (the monoidal tensor) of two simplicial sets; it is the degreewise product. -/
abbrev sProd (X Y : SSet) : SSet := X ⊗ Y

/-- The generator of `C_n(X)` attached to an `n`-simplex `σ`, as a map `ℤ ⟶ C_n(X)`. -/
abbrev genChain (X : SSet) {n : ℕ} (σ : X _⦋n⦌) : zz ⟶ (sChain X).X n :=
  X.ιChainComplex (R := zz) σ

/-- The generator `σ ⊗ τ` of `C_p(X) ⊗_ℤ C_q(Y)`, as a map `ℤ ⟶ C_p(X) ⊗ C_q(Y)`. -/
def genTensor (X Y : SSet) {p q : ℕ} (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    zz ⟶ (sChain X).X p ⊗ (sChain Y).X q :=
  (λ_ zz).inv ≫
    MonoidalCategory.tensorHom (X.ιChainComplex (R := zz) σ) (Y.ιChainComplex (R := zz) τ)

/-- The inclusion of the last `q+1` vertices in `⦋n⦌`, for `q ≤ n`. -/
def backInclLE (q n : ℕ) (h : q ≤ n) : ⦋q⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk
    ⟨fun j => ⟨n - q + j.1, by
        have := j.2; simp only [SimplexCategory.len_mk] at this ⊢; omega⟩,
      fun i j hij => by
        exact Nat.add_le_add_left (show i.1 ≤ j.1 from hij) _⟩

/-- The **back `q`-face** of an `n`-simplex: the face spanned by its last `q+1` vertices. -/
def backFaceLE (X : SSet) (q n : ℕ) (h : q ≤ n) : X _⦋n⦌ → X _⦋q⦌ :=
  X.map (backInclLE q n h).op

/-- The **Alexander–Whitney chain** of an `n`-simplex `(σ,τ)` of `X ⊗ Y`, as a map
`ℤ ⟶ ⨁_{p+q=n} C_p(X) ⊗_ℤ C_q(Y)`: the sum `Σ_{p+q=n} σ_front_p ⊗ τ_back_q`. -/
def awGen (X Y : SSet) (n : ℕ) (z : (X ⊗ Y) _⦋n⦌) : zz ⟶ (tChain X Y).X n :=
  ∑ p : Fin (n + 1),
    genTensor X Y (Work.Cohomology.frontFace X p.val n (by omega) z.1)
        (backFaceLE Y (n - p.val) n (by omega) z.2) ≫
      ModuleCat.ofHom (tpLof (sChain X) (sChain Y) n ⟨(p.val, n - p.val), by omega⟩)

/-- **The Alexander–Whitney map** `C_n(X ⊗ Y) ⟶ ⨁_{p+q=n} C_p(X) ⊗_ℤ C_q(Y)`. -/
def awHom (X Y : SSet) (n : ℕ) : (sChain (X ⊗ Y)).X n ⟶ (tChain X Y).X n :=
  ((X ⊗ Y).isColimitChainComplexXCofan zz n).desc
    (Cofan.mk ((tChain X Y).X n) (awGen X Y n))

/-- The value of `awHom` on the generator of a simplex. -/
theorem awHom_gen (X Y : SSet) (n : ℕ) (z : (X ⊗ Y) _⦋n⦌) :
    ((X ⊗ Y).ιChainComplex (R := zz) z) ≫ awHom X Y n = awGen X Y n z :=
  Cofan.IsColimit.fac _ _ _

end

end Work.Kunneth
