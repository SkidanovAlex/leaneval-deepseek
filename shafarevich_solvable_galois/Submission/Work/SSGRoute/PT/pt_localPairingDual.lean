import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.PT

/-- A functional on `X` (a finite `𝔽_p`-module) which is nonzero at `x` and vanishes on a submodule
`U` not containing `x`.  This is the elementary "duality separates points, modulo the subspace"
step used in the double-annihilator argument. -/
private lemma exists_dual_ne_zero_notMem {p : ℕ} [Fact p.Prime] {X : Type*}
    [AddCommGroup X] [Module (ZMod p) X] (U : Submodule (ZMod p) X) {x : X} (hx : x ∉ U) :
    ∃ f : X →ₗ[ZMod p] ZMod p, f x ≠ 0 ∧ ∀ u ∈ U, f u = 0 := by
  obtain ⟨f, hfx, hfU⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (p := U) hx
    (Module.Projective.of_free (R := ZMod p) (P := X ⧸ U))
  exact ⟨f, hfx, fun u hu => by
    have : f u ∈ (⊥ : Submodule (ZMod p) (ZMod p)) := by
      rw [← hfU]; exact Submodule.mem_map_of_mem hu
    simpa using this⟩

/-- **Per-coordinate finite duality** for a non-degenerate pairing of finite `𝔽_p`-modules
`β : X →ₗ Y →ₗ ZMod p` with `U' = U^⊥` (`hU`): (i) `β` realises *every* linear functional on `X`;
(ii) the double annihilator `(U^⊥)^⊥ = U`; (iii) every linear functional on the quotient `X ⧸ U`
is realised by an element of `U'`.  These are the local facts behind the restricted-product
pairing. -/
theorem pt_localPairingDual
    (p : ℕ) [Fact p.Prime]
    {X Y : Type*} [AddCommGroup X] [Module (ZMod p) X] [Finite X]
    [AddCommGroup Y] [Module (ZMod p) Y] [Finite Y]
    (β : X →ₗ[ZMod p] Y →ₗ[ZMod p] ZMod p)
    (hβL : ∀ x : X, (∀ y : Y, β x y = 0) → x = 0)
    (hβR : ∀ y : Y, (∀ x : X, β x y = 0) → y = 0)
    (U : Submodule (ZMod p) X) (U' : Submodule (ZMod p) Y)
    (hU : ∀ y : Y, y ∈ U' ↔ ∀ x ∈ U, β x y = 0) :
    (∀ φ : X →ₗ[ZMod p] ZMod p, ∃ y : Y, ∀ x : X, φ x = β x y) ∧
    (∀ x : X, (∀ y ∈ U', β x y = 0) → x ∈ U) ∧
    (∀ φ : X ⧸ U →ₗ[ZMod p] ZMod p,
      ∃ y : Y, y ∈ U' ∧ ∀ x : X, φ (Submodule.Quotient.mk x) = β x y) := by
  classical
  -- finiteness provides finite-dimensionality over the field `𝔽_p`
  haveI : Module.Finite (ZMod p) X := Module.Finite.of_finite
  haveI : Module.Finite (ZMod p) Y := Module.Finite.of_finite
  -- `β : X →ₗ (Y →ₗ 𝔽_p)` is injective (left non-degeneracy)
  have hinjL : Function.Injective β := by
    intro x y hxy
    have hz : β (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h0 : ∀ z : Y, β (x - y) z = 0 := fun z => by rw [hz]; rfl
    have h1 : x - y = 0 := hβL (x - y) h0
    rwa [sub_eq_zero] at h1
  -- `β.flip : Y →ₗ (X →ₗ 𝔽_p)` is injective (right non-degeneracy)
  have hinjR : Function.Injective (LinearMap.flip β) := by
    intro x y hxy
    have hz : LinearMap.flip β (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h0 : ∀ z : X, β z (x - y) = 0 := by
      intro z
      have h1 := congrArg (fun (f : X →ₗ[ZMod p] ZMod p) => f z) hz
      simpa using h1
    have h1 : x - y = 0 := hβR (x - y) h0
    rwa [sub_eq_zero] at h1
  -- the two finranks agree
  have hPQ : Module.finrank (ZMod p) X = Module.finrank (ZMod p) Y := by
    have h1 : Module.finrank (ZMod p) X ≤ Module.finrank (ZMod p) Y := by
      have h := LinearMap.finrank_le_finrank_of_injective (R := ZMod p)
        (M := X) (M' := Module.Dual (ZMod p) Y) hinjL
      rwa [Subspace.dual_finrank_eq] at h
    have h2 : Module.finrank (ZMod p) Y ≤ Module.finrank (ZMod p) X := by
      have h := LinearMap.finrank_le_finrank_of_injective (R := ZMod p)
        (M := Y) (M' := Module.Dual (ZMod p) X) hinjR
      rwa [Subspace.dual_finrank_eq] at h
    omega
  -- `β.flip` is therefore bijective
  have hsurjR : Function.Surjective (LinearMap.flip β) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := ZMod p) (V := Y) (V₂ := Module.Dual (ZMod p) X)
      (by rw [Subspace.dual_finrank_eq, hPQ])).mp hinjR
  -- (i) every functional on `X` is realised by an element of `Y`
  have hmain : ∀ φ : X →ₗ[ZMod p] ZMod p, ∃ y : Y, ∀ x : X, φ x = β x y := by
    intro φ
    obtain ⟨y, hy⟩ := hsurjR φ
    refine ⟨y, fun x => ?_⟩
    have h := congrArg (fun (f : X →ₗ[ZMod p] ZMod p) => f x) hy
    simpa using h.symm
  -- (iii) every functional on the quotient is realised by an element of `U'`
  have hiii : ∀ φ : X ⧸ U →ₗ[ZMod p] ZMod p,
      ∃ y : Y, y ∈ U' ∧ ∀ x : X, φ (Submodule.Quotient.mk x) = β x y := by
    intro φ
    obtain ⟨y, hy⟩ := hmain (φ.comp (Submodule.mkQ U))
    refine ⟨y, ?_, fun x => ?_⟩
    · rw [hU]
      intro x hx
      have h0 : (Submodule.mkQ U) x = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hx
      have h1 : φ ((Submodule.mkQ U) x) = β x y := by simpa using hy x
      rw [h0, map_zero] at h1
      exact h1.symm
    · have h1 : φ ((Submodule.mkQ U) x) = β x y := by simpa using hy x
      simpa [Submodule.mkQ_apply] using h1
  refine ⟨hmain, ?_, hiii⟩
  -- (ii) the double annihilator `(U^⊥)^⊥ = U`
  intro x hx
  by_contra hxU
  obtain ⟨f, hfx, hfU⟩ := exists_dual_ne_zero_notMem (p := p) U hxU
  obtain ⟨y, hy⟩ := hmain f
  have hyU : y ∈ U' := by
    rw [hU]
    intro u hu
    rw [← hy u, hfU u hu]
  exact hfx (by rw [← hx y hyU]; exact hy x)

end Work.SSGRoute.PT
