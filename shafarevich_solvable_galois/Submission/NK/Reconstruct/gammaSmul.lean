import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.NK.Reconstruct.GammaModule
import Submission.NK.Reconstruct.continuous_toZModPow
import Submission.NK.Reconstruct.gammaHaus
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `ℤ_ℓ`-action on `Γ_K` is continuous, and the continuous dual is `ℤ_ℓ`-linear

This file proves the two facts about the topological `ℤ_ℓ`-module `Γ_K`
(`NK.Reconstruct.instModuleAdditiveGamma`) which every *rank* computation about `Γ_K` needs:

* `NK.Reconstruct.continuous_smul_gamma` — for fixed `x`, the scalar map `a ↦ a • x` is
  **continuous** from `ℤ_ℓ` (with its `ℓ`-adic topology) to `Γ_K`.  Since `Γ_K` is a closed
  subgroup of the product of its finite levels (each discrete) and on a finite level the scalar
  action is the power map with exponent the *reduction* of `a` modulo `ℓ ^ N`
  (`NK.Reconstruct.smul_ellPart_eq_pow`), this is the continuity of
  `a ↦ (toZModPow N a).val` composed with a map out of a discrete space.

* `NK.Reconstruct.dual_apply_smul` — **every continuous additive homomorphism `Γ_K → ℤ_ℓ` is
  `ℤ_ℓ`-linear**: `g (a • x) = a * g x`.  Because `ℕ` is dense in `ℤ_ℓ`
  (`PadicInt.denseRange_natCast`), both sides are continuous in `a` and they agree on integers
  (`AddMonoidHom.map_nsmul`), so they agree everywhere.

The second statement is the reason `NK.Reconstruct.Dual` is a usable model of Shimizu's
`Hom_cts(Γ_K, ℤ_ℓ)`: it is a `ℤ_ℓ`-module, it embeds `ℤ_ℓ`-linearly into the linear dual of `Γ_K`,
and for the *rank* computations of Shimizu's §4 (Lemma 4f.1 and Proposition 4f.5) it may be treated
as the linear dual.

## Contents

* `smul_apply_coe` — the component of a scalar multiple;
* `continuous_smul_gamma` — continuity of the scalar action;
* `dual_apply_smul` — the dual is `ℤ_ℓ`-linear;
* `instModuleDual`, `dualToLinear` — the `ℤ_ℓ`-module structure on the dual and its embedding into
  the linear dual;
* `invisibleSubmodule`, `HausQuot`, `hausMk` — `Γ_K` modulo the subgroup invisible to every
  continuous character, as a `ℤ_ℓ`-module.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. X §10.3, Ch. XII;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace NK.Reconstruct

open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsGalois K K'] {ℓ : ℕ} [Fact ℓ.Prime]

/-! ## The components of a scalar multiple -/

/-- **The components of a scalar multiple of `x ∈ Γ_K`**: on the finite level `L` the scalar action
of `a : ℤ_ℓ` is the power map with exponent the representative of the reduction of `a` modulo
`ℓ ^ N`, `N = ellExp (LevelAbelianization L.L) ℓ`. -/
theorem smul_apply_coe (x : Additive (Gamma K K' ℓ)) (a : PadicInt ℓ) (L : FrobLevel K K') :
    (Additive.toMul (a • x)).1 L
      = (Additive.toMul x).1 L ^ (PadicInt.toZModPow (p := ℓ)
          (ellExp (LevelAbelianization L.L) ℓ) a).val := by
  show Additive.toMul (a • Additive.ofMul ((Additive.toMul x).1 L)) = _
  rw [smul_ellPart_eq_pow]
  simp

/-! ## Continuity of the scalar action -/

/-- **The scalar action of `ℤ_ℓ` on `Γ_K` is continuous in the scalar**, for fixed `x`.  This is
the statement that `Γ_K` is a *topological* `ℤ_ℓ`-module, and it is what makes the continuous dual
of `Γ_K` linear (`NK.Reconstruct.dual_apply_smul`). -/
theorem continuous_smul_gamma (x : Additive (Gamma K K' ℓ)) :
    Continuous fun a : PadicInt ℓ => a • x := by
  refine Continuous.subtype_mk (continuous_pi fun L => ?_) _
  have hpow : Continuous fun c : ZMod (ℓ ^ ellExp (LevelAbelianization L.L) ℓ) =>
      (Additive.toMul x).1 L ^ c.val := continuous_of_discreteTopology
  have hcomp : Continuous fun a : PadicInt ℓ =>
      (Additive.toMul x).1 L ^ (PadicInt.toZModPow (p := ℓ)
        (ellExp (LevelAbelianization L.L) ℓ) a).val :=
    hpow.comp (continuous_toZModPow ℓ _)
  exact hcomp.congr (fun a => (smul_apply_coe x a L).symm)

/-! ## Linearity of the continuous dual -/

/-- **Every continuous additive homomorphism `Γ_K → ℤ_ℓ` is `ℤ_ℓ`-linear.**

Both `a ↦ g (a • x)` (continuity of the scalar action `NK.Reconstruct.continuous_smul_gamma`
composed with `g`) and `a ↦ a * g x` are continuous functions of `a ∈ ℤ_ℓ`, and they agree on the
natural numbers — `g (n • x) = n • g x` for `g` additive and `(n : ℤ_ℓ) • x = n • x` — which are
dense in `ℤ_ℓ` (`PadicInt.denseRange_natCast`).  Hence they agree everywhere. -/
theorem dual_apply_smul (g : Additive (Gamma K K' ℓ) →+ PadicInt ℓ) (hg : Continuous ⇑g)
    (a : PadicInt ℓ) (x : Additive (Gamma K K' ℓ)) :
    g (a • x) = a * g x := by
  have hgcont : Continuous fun a : PadicInt ℓ => g (a • x) := hg.comp (continuous_smul_gamma x)
  have hmulcont : Continuous fun a : PadicInt ℓ => a * g x := continuous_mul_const _
  have hagree : (fun a : PadicInt ℓ => g (a • x)) ∘ (Nat.cast : ℕ → PadicInt ℓ)
      = (fun a : PadicInt ℓ => a * g x) ∘ (Nat.cast : ℕ → PadicInt ℓ) := by
    funext n
    show g ((n : PadicInt ℓ) • x) = (n : PadicInt ℓ) * g x
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]
  exact congrFun (DenseRange.equalizer PadicInt.denseRange_natCast hgcont hmulcont hagree) a

/-! ## The dual as a `ℤ_ℓ`-module -/

/-- The scalar action on the continuous dual, defined pointwise. -/
noncomputable instance instSMulDual : SMul (PadicInt ℓ) (Dual (Gamma K K' ℓ) ℓ) where
  smul a g :=
    ⟨{ toFun := fun x => a * (g : Additive (Gamma K K' ℓ) →+ PadicInt ℓ) x
       map_zero' := by simp
       map_add' := fun x y => by rw [map_add, mul_add] },
     continuous_const.mul g.2⟩

theorem smul_dual_apply (a : PadicInt ℓ) (g : Dual (Gamma K K' ℓ) ℓ)
    (x : Additive (Gamma K K' ℓ)) :
    ((a • g : Dual (Gamma K K' ℓ) ℓ) : Additive (Gamma K K' ℓ) →+ PadicInt ℓ) x
      = a * (g : Additive (Gamma K K' ℓ) →+ PadicInt ℓ) x := rfl

/-- **The continuous dual `Hom_cts(Γ_K, ℤ_ℓ)` is a `ℤ_ℓ`-module.**  The structure is transported
from the pointwise structure on `Additive (Γ_K) →+ ℤ_ℓ` along the injective coercion. -/
noncomputable instance instModuleDual : Module (PadicInt ℓ) (Dual (Gamma K K' ℓ) ℓ) :=
  Function.Injective.module (PadicInt ℓ) (dualCarrier (Gamma K K' ℓ) ℓ).subtype
    (fun f g h => Subtype.ext h)
    (fun a g => AddMonoidHom.ext fun x => by
      show a * (g : Additive (Gamma K K' ℓ) →+ PadicInt ℓ) x
        = (a • (g : Additive (Gamma K K' ℓ) →+ PadicInt ℓ)) x
      rfl)

/-- **The continuous dual is the linear dual** (for the purposes of the `ℤ_ℓ`-module structure):
the coercion of `Dual (Γ) ℓ` into `Module.Dual (ℤ_ℓ) (Additive Γ)` is a `ℤ_ℓ`-linear injection; by
`NK.Reconstruct.dual_apply_smul` every element of the continuous dual is a `ℤ_ℓ`-linear map. -/
noncomputable def dualToLinear (g : Dual (Gamma K K' ℓ) ℓ) :
    Module.Dual (PadicInt ℓ) (Additive (Gamma K K' ℓ)) where
  toFun := (g : Additive (Gamma K K' ℓ) →+ PadicInt ℓ)
  map_add' := (g : Additive (Gamma K K' ℓ) →+ PadicInt ℓ).map_add
  map_smul' a x := dual_apply_smul (g : Additive (Gamma K K' ℓ) →+ PadicInt ℓ) g.2 a x

@[simp] theorem dualToLinear_apply (g : Dual (Gamma K K' ℓ) ℓ)
    (x : Additive (Gamma K K' ℓ)) :
    dualToLinear g x = (g : Additive (Gamma K K' ℓ) →+ PadicInt ℓ) x := rfl

theorem dualToLinear_injective : Function.Injective (dualToLinear (K := K) (K' := K') (ℓ := ℓ)) :=
  fun f g h => Subtype.ext (AddMonoidHom.ext fun x => congrArg (fun u => u x) h)

/-! ## The invisible subgroup and the Hausdorff quotient -/

/-- **The invisible subgroup of `Γ_K`**, as a `ℤ_ℓ`-submodule: the intersection of the kernels of
all continuous homomorphisms `Γ_K → ℤ_ℓ`.  This is the subgroup of `Γ_K` which is not seen by the
continuous duality, i.e. the kernel of `Γ_K ↠ Γ_K^{tf}`
(`NK.Reconstruct.gammaHausMk_eq_one_iff`). -/
noncomputable def invisibleSubmodule : Submodule (PadicInt ℓ) (Additive (Gamma K K' ℓ)) :=
  ⨅ (g : Dual (Gamma K K' ℓ) ℓ), LinearMap.ker (dualToLinear g)

theorem mem_invisibleSubmodule_iff (x : Additive (Gamma K K' ℓ)) :
    x ∈ invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ)
      ↔ ∀ g : Dual (Gamma K K' ℓ) ℓ,
        (g : Additive (Gamma K K' ℓ) →+ PadicInt ℓ) x = 0 := by
  simp only [invisibleSubmodule, Submodule.mem_iInf, LinearMap.mem_ker, dualToLinear_apply]

/-- The invisible subgroup coincides with the kernel of the quotient map `Γ_K ↠ Γ_K^{tf}`. -/
theorem mem_invisibleSubmodule_iff_gammaHausMk (x : Additive (Gamma K K' ℓ)) :
    x ∈ invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ)
      ↔ gammaHausMk (K := K) (K' := K') ℓ (Additive.toMul x) = 1 :=
  (mem_invisibleSubmodule_iff x).trans
    (gammaHausMk_eq_one_iff (K := K) (K' := K') (Additive.toMul x)).symm

/-- **The Hausdorff torsion-free quotient `Γ_K^{tf}`**, as the quotient of `Γ_K` by its invisible
subgroup.  It is isomorphic, as a group, to `NK.Reconstruct.GammaHaus` (the image of
`NK.Reconstruct.gammaEvalMul`); the quotient form is the one carrying the `ℤ_ℓ`-module structure
used in the rank computations. -/
noncomputable abbrev HausQuot (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] : Type _ :=
  Additive (Gamma K K' ℓ) ⧸ invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ)

/-- The quotient map `Γ_K ↠ Γ_K^{tf}`. -/
noncomputable def hausMk : Additive (Gamma K K' ℓ) →ₗ[PadicInt ℓ] HausQuot K K' ℓ :=
  (invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ)).mkQ

@[simp] theorem hausMk_apply (x : Additive (Gamma K K' ℓ)) :
    hausMk (K := K) (K' := K') (ℓ := ℓ) x
      = (invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ)).mkQ x := rfl

theorem hausMk_surjective : Function.Surjective (hausMk (K := K) (K' := K') (ℓ := ℓ)) :=
  (invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ)).mkQ_surjective

theorem hausMk_eq_zero_iff (x : Additive (Gamma K K' ℓ)) :
    hausMk (K := K) (K' := K') (ℓ := ℓ) x = 0 ↔
      x ∈ invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ) :=
  Submodule.Quotient.mk_eq_zero _

end NK.Reconstruct
