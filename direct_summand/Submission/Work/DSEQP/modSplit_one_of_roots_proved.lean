/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `KRULL-P`: descent of almost splittings with compatible roots

This file proves `Work.DSEQP.modSplit_one_of_roots_proved`, whose statement is the frozen node
`DSMap.Gaps.modSplit_one_of_roots` of the EQP design
(`sources/dsmap/direct_summand_gaps_1013.md`, node 9).

## Mathematics

Let `P` be a bounded-above complex of finite free `A`-modules with a coaugmentation
`ε : A → P⁰`, let `S` be a faithfully flat `A`-algebra, and suppose that after base change to `S`
the coaugmentation splits modulo the image of `d⁻¹` with values `r e`, where
`(r e) ^ (p ^ e) = algebraMap A S d` for some `d ≠ 0`.  Then `P` splits over `A` with value `1`.

## Formal structure

* `modelQuot P = P⁰ ⧸ im(d⁻¹)` is the obstruction module and `modelValueIdeal P ε` is the
  *value ideal*: the set of values `φ (ε 1)` of `A`-linear functionals on `modelQuot P`.
* `mem_modelValueIdeal_map_of_modSplitA` (**value-set description**): over a flat base `D`, every
  value of a splitting lies in the extension of the value ideal.  The obstruction module is
  finitely presented, so `Hom_A(Q,D) = Hom_A(Q,A) ⊗_A D` (`dualTensorHom_surjective`).
* `modSplitA_of_one_mem_modelValueIdeal`: a functional on `Q` with value `1` is an honest
  splitting with value `1` (tensor–hom adjunction, as in `Work.DSAM3`).
* Krull descent (`Work.DSEQP.one_mem_of_forall_pthRoot_mem`) then upgrades "all `pᵉ`-th roots of
  `d` are values" to `1 ∈ modelValueIdeal P ε`.

Everything is phrased for the `A`-linear form `Work.DSAM3.ModSplitA` of the frozen
`DSMap.Mix.ModSplit`; the two are exchanged by `Work.DSAM3.modSplit_iff_ModSplitA`.
-/
import Mathlib
import Submission.Work.DSMap.Gaps
import Submission.Work.DSAM3.Api
import Submission.Work.DSEQP.dualTensorHom_surjective
import Submission.Work.DSEQP.krull_descent
import Submission.Work.DSEQP.Descent

open CategoryTheory AlgebraicGeometry IsLocalRing Limits
open scoped TensorProduct

namespace Work.DSEQP

universe a

set_option maxHeartbeats 1000000

section Model

variable {A : Type a} [CommRing A]

/-- `Q = P⁰ ⧸ im(d⁻¹)`: the module classifying the obstruction to splitting `ε`. -/
noncomputable abbrev modelQuot (P : CochainComplex (ModuleCat.{a} A) ℤ) : Type a :=
  (P.X 0) ⧸ (LinearMap.range (P.d (-1) 0).hom)

/-- The class of the unit `ε 1` in the obstruction module `Q`. -/
noncomputable def modelUnit (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) : modelQuot P :=
  Submodule.mkQ _ (ε.hom 1)

/-- The **value ideal** of the model `(P, ε)`: the values `φ (ε 1)` of `A`-linear functionals
`φ : Q → A` on the obstruction module. -/
noncomputable def modelValueIdeal (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) : Ideal A :=
  LinearMap.range (LinearMap.applyₗ (modelUnit P ε))

lemma mem_modelValueIdeal_iff (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) (x : A) :
    x ∈ modelValueIdeal P ε ↔ ∃ φ : modelQuot P →ₗ[A] A, φ (modelUnit P ε) = x := by
  simp only [modelValueIdeal, LinearMap.mem_range, LinearMap.applyₗ_apply_apply]

/-- An `A`-linear map out of `P⁰` killing the differential factors through the obstruction
module `Q`. -/
lemma exists_factor_of_kill (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0)
    {D : Type*} [AddCommGroup D] [Module A D] (t : P.X 0 →ₗ[A] D)
    (ht : ∀ y, t ((P.d (-1) 0).hom y) = 0) :
    ∃ tq : modelQuot P →ₗ[A] D, tq (modelUnit P ε) = t (ε.hom 1) :=
  ⟨(LinearMap.range (P.d (-1) 0).hom).liftQ t (fun x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ht y),
    by simp only [modelUnit, Submodule.mkQ_apply, Submodule.liftQ_apply]⟩

end Model

section ValueSet

variable {A : Type a} [CommRing A] [IsNoetherianRing A]

/-- **Value-set description.**  For a flat `A`-algebra `D`, every value of a splitting of the
model `(P, ε)` over `D` lies in the extension of the value ideal. -/
theorem mem_modelValueIdeal_map_of_modSplitA (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (hP : DSMap.Mix.IsBddFinFree P) (ε : ModuleCat.of A A ⟶ P.X 0)
    {D : Type a} [CommRing D] (ψ : A →+* D)
    (hflat : letI : Algebra A D := ψ.toAlgebra; Module.Flat A D) (c : D)
    (h : DSAM3.ModSplitA P ε ψ ⊥ c) :
    c ∈ Ideal.map ψ (modelValueIdeal P ε) := by
  letI : Algebra A D := ψ.toAlgebra
  haveI : Module.Flat A D := hflat
  obtain ⟨t, ht1, ht2⟩ := h
  have htδ : ∀ y : P.X (-1), t ((P.d (-1) 0).hom y) = 0 := fun y => by
    have h' := LinearMap.congr_fun ht1 y
    simpa using h'
  -- pass from the quotient `D ⧸ ⊥` back to `D`
  let t' : P.X 0 →ₗ[A] D := (AlgEquiv.quotientBot A D).toLinearMap.comp t
  have ht'δ : ∀ y : P.X (-1), t' ((P.d (-1) 0).hom y) = 0 := fun y => by
    simp only [t', LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, htδ y, map_zero]
  have ht'u : t' (ε.hom 1) = c := by
    simp only [t', LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, ht2,
      AlgEquiv.quotientBot_mk]
  -- factor through the obstruction module
  obtain ⟨tq, htq⟩ := exists_factor_of_kill (A := A) (D := D) P ε t' ht'δ
  -- the obstruction module is finitely presented, so flat base change of its dual is exact
  haveI hP0 : Module.Finite A (P.X 0) := (hP.1 0).2
  haveI hQ : Module.Finite A (modelQuot P) :=
    Module.Finite.of_surjective (Submodule.mkQ (LinearMap.range (P.d (-1) 0).hom))
      (Submodule.mkQ_surjective _)
  haveI hQp : Module.FinitePresentation A (modelQuot P) :=
    Module.finitePresentation_of_finite (R := A) (M := modelQuot P)
  obtain ⟨w, hw⟩ := dualTensorHom_surjective A (modelQuot P) D tq
  have key : ∀ w' : Module.Dual A (modelQuot P) ⊗[A] D,
      dualTensorHom A (modelQuot P) D w' (modelUnit P ε) ∈
        Ideal.map ψ (modelValueIdeal P ε) := by
    intro w'
    induction w' using TensorProduct.inductionOn with
    | tmul f d =>
      rw [dualTensorHom_apply]
      have hf : f (modelUnit P ε) ∈ modelValueIdeal P ε :=
        (mem_modelValueIdeal_iff P ε _).2 ⟨f, rfl⟩
      rw [show (f (modelUnit P ε)) • d = ψ (f (modelUnit P ε)) * d from rfl]
      exact Ideal.mul_mem_right d _ (Ideal.mem_map_of_mem ψ hf)
    | add x y hx hy => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
  have hc : c = dualTensorHom A (modelQuot P) D w (modelUnit P ε) := by
    rw [show dualTensorHom A (modelQuot P) D w = tq from hw, htq, ht'u]
  rw [hc]
  exact key w

end ValueSet

section Splitting

variable {A : Type a} [CommRing A]

/-- **From a value to a splitting.**  If `1` lies in the value ideal, the model splits with
value `1`. -/
theorem modSplitA_of_one_mem_modelValueIdeal (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (ε : ModuleCat.of A A ⟶ P.X 0) (h1 : (1 : A) ∈ modelValueIdeal P ε) :
    DSAM3.ModSplitA P ε (RingHom.id A) ⊥ 1 := by
  letI : Algebra A A := (RingHom.id A).toAlgebra
  obtain ⟨φ, hφ⟩ := (mem_modelValueIdeal_iff P ε 1).1 h1
  let t0 : P.X 0 →ₗ[A] A := φ.comp (Submodule.mkQ (LinearMap.range (P.d (-1) 0).hom))
  have htδ0 : t0.comp (P.d (-1) 0).hom = 0 := by
    ext y
    show φ ((LinearMap.range (P.d (-1) 0).hom).mkQ ((P.d (-1) 0).hom y)) = 0
    have hmem : (P.d (-1) 0).hom y ∈ LinearMap.range (P.d (-1) 0).hom := ⟨y, rfl⟩
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hmem, map_zero]
  have htu0 : t0 (ε.hom 1) = 1 := by
    show φ ((LinearMap.range (P.d (-1) 0).hom).mkQ (ε.hom 1)) = 1
    rw [show (LinearMap.range (P.d (-1) 0).hom).mkQ (ε.hom 1) = modelUnit P ε from rfl, hφ]
  refine ⟨((Ideal.Quotient.mkₐ (R₁ := A) (⊥ : Ideal A)).toLinearMap).comp t0, ?_, ?_⟩
  · rw [LinearMap.comp_assoc, htδ0, LinearMap.comp_zero]
  · simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, htu0]

end Splitting

section Main

/-- **KRULL-P** (the frozen node `DSMap.Gaps.modSplit_one_of_roots`): over a faithfully flat
`S`, almost splittings with values `r e` where `(r e)^(p^e) = algebraMap A S d`, `d ≠ 0`, force
an honest splitting over `A`. -/
theorem modSplit_one_of_roots_proved (A S : Type a) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing S] [Algebra A S] [Module.FaithfullyFlat A S] (p : ℕ)
    [Fact p.Prime] (P : CochainComplex (ModuleCat.{a} A) ℤ) (hP : DSMap.Mix.IsBddFinFree P)
    (ε : ModuleCat.of A A ⟶ P.X 0) (d : A) (hd : d ≠ 0) (r : ℕ → S)
    (hr : ∀ e, r e ^ (p ^ e) = algebraMap A S d)
    (h : ∀ e, DSMap.Mix.ModSplit P ε (algebraMap A S) ⊥ (r e)) :
    DSMap.Mix.ModSplit P ε (RingHom.id A) ⊥ 1 := by
  -- flatness for the algebra structure `(algebraMap A S).toAlgebra` used inside `ModSplit`
  have hff : Module.FaithfullyFlat A S := inferInstance
  have hmodEq : (@Algebra.toModule A S _ _ (algebraMap A S).toAlgebra) =
      (@Algebra.toModule A S _ _ (inferInstance : Algebra A S)) :=
    congrArg (fun al : Algebra A S => @Algebra.toModule A S _ _ al) toAlgebra_algebraMap
  have hflat : (letI : Algebra A S := (algebraMap A S).toAlgebra; Module.Flat A S) :=
    hmodEq ▸ hff.toFlat
  -- the value-set description: every `r e` is a value of the value ideal
  have hmem : ∀ e : ℕ, r e ∈ (modelValueIdeal P ε).map (algebraMap A S) := fun e =>
    mem_modelValueIdeal_map_of_modSplitA P hP ε (algebraMap A S) hflat (r e)
      ((DSAM3.modSplit_iff_ModSplitA P ε (algebraMap A S) ⊥ (r e)).mp (h e))
  -- the `e = 0` case gives `d ∈ modelValueIdeal P ε`
  have hdmem : d ∈ modelValueIdeal P ε := by
    have h0 := hmem 0
    rw [show r 0 = algebraMap A S d from by simpa using hr 0] at h0
    have h1 : d ∈ Ideal.comap (algebraMap A S) ((modelValueIdeal P ε).map (algebraMap A S)) := h0
    rwa [Ideal.comap_map_eq_self_of_faithfullyFlat] at h1
  -- Krull descent: all `pᵉ`-th roots of a nonzero element of the ideal are values ⟹ `1 ∈`
  have h1 : (1 : A) ∈ modelValueIdeal P ε :=
    one_mem_of_forall_pthRoot_mem A S p hdmem hd (fun e => ⟨r e, hmem e, hr e⟩)
  exact (DSAM3.modSplit_iff_ModSplitA P ε (RingHom.id A) ⊥ 1).mpr
    (modSplitA_of_one_mem_modelValueIdeal P ε h1)

end Main

end Work.DSEQP
