import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFT.GaloisIdelesAction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The identity of `Gal(L/K)` acts trivially on the idèles

The action of `Gal(L/K) = (L ≃ₐ[K] L)` on the idèle group `𝕀 L` was defined in
`Submission.NK.GlobalCFT.GaloisIdelesAction` by the component formula

`(σ · x)_w = σ_*(x_{σ⁻¹ w})`,

with `σ_* : L_w ≃+* L_{σ w}` the canonical isomorphism of local fields
(`NK.GlobalCFT.Place.localRingEquiv`).  This file proves the first law of that action,

`1 · x = x` for every idèle `x`,

which is needed in order to turn the bare `SMul` instance into a usable action (and hence to
descend it to the idèle class group `C_L`).

The whole content is local: for the identity automorphism the canonical isomorphism
`L_w ≃+* L_{1 · w}` of local fields is the identity, up to the transport along the equality
`1 · w = w` of places.  Since `Place.localField L` is a family of *types* indexed by the places,
`L_w` and `L_{1 · w}` are propositionally but not definitionally equal, and the local identity has
to be expressed using the transport `h ▸ ·` along `h : 1 · w = w`.  We prove it by the density
argument already used for the composition law
`NK.GlobalCFT.Galois.globalCFT_localRingEquiv_comp`: two continuous maps out of `L_w` which
agree on the dense image of `L` are equal.

## Main results

* `NK.GlobalCFT.Galois.globalCFT_one_smul_idele`: `1 • x = x` for `x : 𝕀 L`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Galois

open NK.GlobalCFT

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-! ### Transport along an equality of places -/

/-- Casting along `h : a = b` and back again does nothing.  Both sides live in the fibre at `a`. -/
private lemma eqRec_symm_eqRec {α : Type*} {F : α → Type*} {a b : α} (h : a = b) (z : F a) :
    h.symm ▸ (h ▸ z) = z := by
  cases h; rfl

/-- Transporting the component of an idèle at a place along an equality of places commutes with
the underlying elements: this is the usual functoriality of the application of a dependent
function. -/
private lemma localField_val_eqRec_apply (x : Idele L) {a b : Place L} (h : a = b) :
    h ▸ (x a : (Place.localField L a)ˣ).val = (x b : (Place.localField L b)ˣ).val := by
  cases h; rfl

/-! ### The local isomorphism attached to an automorphism fixing `L`

If `σ : L ≃ₐ[K] L` is the identity on `L`, then the induced isomorphism of local fields
`L_w ≃+* L_{σ w}` is the identity, up to transporting along `σ • w = w`. -/

/-- If `σ` fixes `L` pointwise and `h : σ • w = w`, then `Place.localRingEquiv σ w` is the
identity, transported along `h`. -/
private lemma localRingEquiv_of_apply_eq_self (σ : L ≃ₐ[K] L) (hσ : ∀ y : L, σ y = y)
    (w : Place L) (h : σ • w = w) (y : Place.localField L w) :
    Place.localRingEquiv σ w y = h.symm ▸ y := by
  have hdense : DenseRange (algebraMap L (Place.localField L w)) :=
    denseRange_algebraMap_localField w
  have hcont₁ : Continuous (fun y : Place.localField L w => Place.localRingEquiv σ w y) :=
    continuous_localRingEquiv σ w
  have hcont₂ : Continuous (fun y : Place.localField L w => h.symm ▸ y) :=
    continuous_localField_cast h.symm continuous_id
  -- Both sides are continuous and agree on the dense image of `L` in `L_w`.
  have hfun : (fun y : Place.localField L w => Place.localRingEquiv σ w y) =
      fun y : Place.localField L w => h.symm ▸ y := by
    refine DenseRange.equalizer hdense hcont₁ hcont₂ ?_
    funext x
    simp only [Function.comp_apply]
    rw [Place.localRingEquiv_algebraMap, localField_cast_algebraMap h.symm x, hσ x]
  exact congrFun hfun y

/-- The inverse of the local isomorphism attached to an automorphism fixing `L` acts as the
transport along `h : σ • w = w`. -/
private lemma symm_localRingEquiv_of_apply_eq_self (σ : L ≃ₐ[K] L) (hσ : ∀ y : L, σ y = y)
    (w : Place L) (h : σ • w = w) (z : Place.localField L (σ • w)) :
    (Place.localRingEquiv σ w).symm z = h ▸ z := by
  have h1 : (Place.localRingEquiv σ w) ((Place.localRingEquiv σ w).symm z) = z :=
    RingEquiv.apply_symm_apply _ _
  rw [localRingEquiv_of_apply_eq_self σ hσ w h] at h1
  have h2 : h ▸ (h.symm ▸ ((Place.localRingEquiv σ w).symm z)) = h ▸ z := by rw [h1]
  rwa [eqRec_symm_eqRec] at h2

/-! ### The identity acts trivially on the idèles -/

/-- The identity of `Gal(L/K)` acts trivially on the idèle group `𝕀 L`.

On the component at a place `w` the component formula reads
`(1 · x)_w = (Place.localRingEquiv 1⁻¹ w).symm (x (1⁻¹ · w))`; since `1⁻¹ = 1` and the local
isomorphism attached to `1` is the identity (up to transport along `1 · w = w`), this is
`x w`. -/
theorem globalCFT_one_smul_idele {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (x : NK.GlobalCFT.Idele L) :
    (1 : L ≃ₐ[K] L) • x = x := by
  ext w
  rw [Idele.smul_apply]
  show (Place.localRingEquiv ((1 : L ≃ₐ[K] L))⁻¹ w).symm
      ↑(x (((1 : L ≃ₐ[K] L))⁻¹ • w)) = ↑(x w)
  have h : ((1 : L ≃ₐ[K] L))⁻¹ • w = w := by simp
  have hσ : ∀ y : L, ((1 : L ≃ₐ[K] L))⁻¹ y = y := by intro y; simp
  rw [symm_localRingEquiv_of_apply_eq_self ((1 : L ≃ₐ[K] L))⁻¹ hσ w h
    (↑(x (((1 : L ≃ₐ[K] L))⁻¹ • w)))]
  exact localField_val_eqRec_apply x h

end NK.GlobalCFT.Galois
