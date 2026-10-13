/-
# DSFFP: faithful flatness mod `p` ⟹ mod `p^m` (the FFP node of `DSMap.Mix2`)

Subproject DSFFP (curric-46 lead).  Deliverable: `DSMap.Mix2.ff_mod_pow_proved`.

The plan is the classical **local flatness criterion** (Stacks 10.99.8, tag `051C`):
for a ring `S`, an ideal `I` with `I ^ n = ⊥`, and an `S`-module `T` with

* `h1 : I ⊗[S] T → T` injective (`Tor₁ᴬ(S/I, T) = 0`), and
* `h2 : T/IT` flat over `S/I`,

the module `T` is flat over `S`.

This file fixes the vocabulary used by the node set: `TPure` ("`f ⊗ id_T` is injective") and
`IdxInj` (the hypothesis `h1`), plus their elementary API.
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

open TensorProduct

namespace Work.DSFFP

universe u

/-- `f` is `T`-pure if `f ⊗ 𝟙_T` is injective (i.e. the map `N ⊗ T → P ⊗ T` is injective). -/
def TPure {S : Type u} [CommRing S] (T : Type u) [AddCommGroup T] [Module S T]
    {N P : Type u} [AddCommGroup N] [AddCommGroup P] [Module S N] [Module S P]
    (f : N →ₗ[S] P) : Prop := Function.Injective (f.rTensor T)

/-- The `h1` hypothesis of the local flatness criterion: `I ⊗[S] T → T` is injective. -/
def IdxInj {S : Type u} [CommRing S] (I : Ideal S) (T : Type u) [AddCommGroup T]
    [Module S T] : Prop :=
  Function.Injective (TensorProduct.lift ((LinearMap.lsmul S T).comp I.subtype))

section Basic

variable {S : Type u} [CommRing S] {T N P Q : Type u} [AddCommGroup T] [Module S T]
  [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q] [Module S N] [Module S P] [Module S Q]

lemma TPure.comp {f : N →ₗ[S] P} {g : P →ₗ[S] Q} (hf : TPure T f) (hg : TPure T g) :
    TPure T (g ∘ₗ f) := by
  rw [TPure] at *
  rw [LinearMap.rTensor_comp]
  exact hg.comp hf

lemma TPure.of_retract {f : N →ₗ[S] P} {r : P →ₗ[S] N} (h : r ∘ₗ f = LinearMap.id) :
    TPure T f := by
  rw [TPure]
  have h2 : (r.rTensor T) ∘ₗ (f.rTensor T) = LinearMap.id := by
    rw [← LinearMap.rTensor_comp, h, LinearMap.rTensor_id]
  exact Function.LeftInverse.injective (g := fun x => (LinearMap.rTensor T r) x)
    (fun x => congr_fun (congr_arg DFunLike.coe h2) x)

lemma TPure.id : TPure T (LinearMap.id : N →ₗ[S] N) := by
  rw [TPure, LinearMap.rTensor_id]
  exact Function.injective_id

lemma TPure.iff_ker (f : N →ₗ[S] P) :
    TPure T f ↔ LinearMap.ker (f.rTensor T) = ⊥ := by
  rw [TPure, LinearMap.ker_eq_bot]

end Basic

end Work.DSFFP
