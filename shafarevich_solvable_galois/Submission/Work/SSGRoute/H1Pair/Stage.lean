/-
# Finite stages of a `Gal`-module, and the elementary finiteness facts of the assembly

The assembly of `Work.SSGRoute.coker_obstruction` has to apply the arithmetic input (Poitou–Tate
at `H¹`, which is stated only for **finite** coefficient modules) to an *arbitrary*
`Gal(K/k)`-module `E₂`: the local data `(f ∘ α, f ∘ β)` takes values in `f(E)`, which is finite
because `E` is, so it really lives in a finite submodule.  The reduction is the *finite stage*:

* `Stage p G E E₂ f` packages a finite `G`-stable submodule `W ⊆ E₂` (as an abstract finite
  `G`-module with an equivariant injection `i` into `E₂`), together with an equivariant
  factorization `f = i ∘ f₀` through it;
* `finite_stage_factor` (delegated, in `H1Pair/finite_stage.lean`) produces such a stage through
  which the coefficient morphism `F` factors, on which the given homology class still dies.  The
  marked-up design, including the one subtlety (the stage must be chosen *after* a bounding
  `2`-chain for the class, because `H₁` is only right exact), is in
  `Submission/Work/SSGRoute/H1Pair/FINITE_STAGE_DESIGN.md`.

This file only holds the vocabulary and the two finiteness facts (`E ⊗ T` is finite-dimensional
over `𝔽_p`, and a line is finite-dimensional) that the assembly uses.
-/
import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct

namespace Work.SSGRoute.H1Pair

/-- A **finite stage** of a `G`-module `E₂` above the finite `G`-module `E` and an equivariant
`f : E → E₂`: a finite `G`-module `W`, an equivariant injection `i : W → E₂` and an equivariant
`f₀ : E → W` with `i ∘ f₀ = f`. -/
structure Stage (p : ℕ) (G : Type) [Group G] (E E₂ : Type) [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction G E] [SMulCommClass G (ZMod p) E]
    [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction G E₂] [SMulCommClass G (ZMod p) E₂]
    (f : E →ₗ[ZMod p] E₂) where
  /-- the finite coefficient module of the stage -/
  W : Type
  [instAdd : AddCommGroup W]
  [instModule : Module (ZMod p) W]
  [instSmul : DistribMulAction G W]
  [instComm : SMulCommClass G (ZMod p) W]
  [instFinite : Finite W]
  /-- the inclusion of the stage into `E₂` -/
  i : W →ₗ[ZMod p] E₂
  inj : Function.Injective i
  equiv : ∀ (g : G) (m : W), i (g • m) = g • i m
  /-- the factorization of `f` through the stage -/
  f₀ : E →ₗ[ZMod p] W
  f₀_equiv : ∀ (g : G) (e : E), f₀ (g • e) = g • f₀ e
  comp : ∀ e : E, i (f₀ e) = f e

attribute [instance] Stage.instAdd Stage.instModule Stage.instSmul Stage.instComm Stage.instFinite


/-- **A line is finite-dimensional** — the only finiteness input the assembly needs from
`IsCyclotomicDual` (whose second component is `Module.finrank (ZMod p) T = 1`). -/
theorem moduleFinite_of_finrank_eq_one (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T]
    [Module (ZMod p) T] (h : Module.finrank (ZMod p) T = 1) : Module.Finite (ZMod p) T :=
  Module.finite_of_finrank_pos (by omega)

/-- **`E ⊗ T` is finite-dimensional** over `𝔽_p` when `E` is finite and `T` is a line: the
coefficient module of the assembly's Tate twist. -/
theorem moduleFinite_tensor_of_finite (p : ℕ) [Fact p.Prime] (E T : Type) [AddCommGroup E]
    [Module (ZMod p) E] [Finite E] [AddCommGroup T] [Module (ZMod p) T]
    (h : Module.finrank (ZMod p) T = 1) :
    Module.Finite (ZMod p) (TensorProduct (ZMod p) E T) := by
  haveI : Module.Finite (ZMod p) E := Module.Finite.of_finite
  haveI : Module.Finite (ZMod p) T := moduleFinite_of_finrank_eq_one p T h
  infer_instance

/-- The `𝔽_p`-hypothesis of the assembly, read off `IsCyclotomicDual`. -/
theorem moduleFinite_tensor_of_isCyclotomicDual (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [Normal k K] (ζ : Ω)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E] :
    Module.Finite (ZMod p) (TensorProduct (ZMod p) E T) :=
  moduleFinite_tensor_of_finite p E T hT.1


/-- **A finitely generated module over `𝔽_p` is a finite type.**  (Over the finite ring `𝔽_p`, the
span of a finite set is finite: it is the image of a Finsupp module on that set.) -/
theorem finite_of_moduleFinite (p : ℕ) [NeZero p] (X : Type) [AddCommGroup X]
    [Module (ZMod p) X] [Module.Finite (ZMod p) X] : Finite X := by
  classical
  haveI : Fintype (ZMod p) := ZMod.fintype p
  obtain ⟨s, hs⟩ := (show (⊤ : Submodule (ZMod p) X).FG from ‹Module.Finite (ZMod p) X›.fg_top)
  refine Finite.of_surjective
    (fun c : ↥(s : Set X) →₀ ZMod p => c.sum fun x a => a • (x : X)) ?_
  intro x
  have hx : x ∈ Submodule.span (ZMod p) (s : Set X) := by
    simpa [hs] using (Submodule.mem_top : x ∈ (⊤ : Submodule (ZMod p) X))
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp (R := ZMod p)
    (v := fun x : ↥(s : Set X) => (x : X))).1 (by simpa using hx)
  exact ⟨c, hc⟩

/-- **The coefficient module of the assembly is a finite type**: `E ⊗ T` with `E` finite and `T` a
line over `𝔽_p`. -/
theorem finite_tensor_of_isCyclotomicDual (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [Normal k K] (ζ : Ω)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E] :
    Finite (TensorProduct (ZMod p) E T) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Module.Finite (ZMod p) (TensorProduct (ZMod p) E T) :=
    moduleFinite_tensor_of_isCyclotomicDual p k Ω K ζ T hT E
  exact finite_of_moduleFinite p (TensorProduct (ZMod p) E T)

end Work.SSGRoute.H1Pair

