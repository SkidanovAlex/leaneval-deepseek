import Mathlib
import Submission.Work.HallHigman.GLCore.Defs
import Submission.Work.HallHigman.GLCore.glCore_algClosed

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.HallHigman.GLCore

universe u v w

/-! ## Extension of scalars

The base-change step of the GL-core: from an arbitrary field `K` of characteristic `p` to its
algebraic closure.  We realise `End_K V ⊗_K K̄` concretely as `M_n(K̄)` via a `K`-basis of `V`
(`n = dim_K V`), using `LinearMap.toMatrixAlgEquiv`, `Matrix.map (algebraMap K K̄)` and
`Matrix.toLinAlgEquiv'`. -/

/-- Scalar extension of square matrices along a ring hom `f : K →+* L`. -/
noncomputable def glCoreMatMap {K L : Type*} [Semiring K] [Semiring L] (f : K →+* L) (n : ℕ) :
    Matrix (Fin n) (Fin n) K →+* Matrix (Fin n) (Fin n) L where
  toFun M := M.map f
  map_one' := Matrix.map_one f (map_zero f) (map_one f)
  map_mul' M N := Matrix.map_mul (f := f)
  map_zero' := Matrix.map_zero f (map_zero f)
  map_add' M N := Matrix.map_add f (map_add f) M N

/-- Scalar extension of matrices is injective for an injective `f`. -/
lemma glCoreMatMap_injective {K L : Type*} [Field K] [Field L] [Algebra K L]
    (hKL : Function.Injective (algebraMap K L)) (n : ℕ) :
    Function.Injective (glCoreMatMap (algebraMap K L) n) := by
  intro a b hab
  exact Matrix.map_injective hKL hab

/-- Extension of scalars `End_K V → End_L (L^n)`, where `n = dim_K V`, obtained by choosing a
`K`-basis of `V`, writing endomorphisms as matrices over `K`, extending coefficients to `L`,
and reading the result as an `L`-linear endomorphism of `L^n`. -/
noncomputable def glCoreScalarMap (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
    (V : Type w) [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    Module.End K V →+* Module.End L (Fin (Module.finrank K V) → L) :=
  ((Matrix.toLinAlgEquiv' (R := L) (n := Fin (Module.finrank K V))).toRingEquiv.toRingHom).comp
    ((glCoreMatMap (algebraMap K L) (Module.finrank K V)).comp
      ((LinearMap.toMatrixAlgEquiv (Module.finBasis K V)).toRingEquiv.toRingHom))

/-- `glCoreScalarMap` is injective: a field extension is faithfully flat. -/
theorem glCoreScalarMap_injective (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]
    (hKL : Function.Injective (algebraMap K L)) (V : Type w) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Function.Injective (glCoreScalarMap K L V) := by
  have h0 : Function.Injective
      ((LinearMap.toMatrixAlgEquiv (Module.finBasis K V)).toRingEquiv.toRingHom) :=
    (LinearMap.toMatrixAlgEquiv (Module.finBasis K V)).injective
  have h1 : Function.Injective (glCoreMatMap (algebraMap K L) (Module.finrank K V)) :=
    glCoreMatMap_injective hKL _
  have h2 : Function.Injective
      ((Matrix.toLinAlgEquiv' (R := L) (n := Fin (Module.finrank K V))).toRingEquiv.toRingHom) :=
    (Matrix.toLinAlgEquiv' (R := L) (n := Fin (Module.finrank K V))).injective
  intro a b hab
  simp only [glCoreScalarMap, RingHom.comp_apply] at hab
  exact h0 (h1 (h2 hab))

/-- **L17 of the GL-core design** (Step 0, base change, of the proof of Hall--Higman B, see
`NOTES_LEAD_ft_hallhigman.md` §2.2): the GL-core statement over an arbitrary field `K` of
characteristic `p`.

Proof: choose a basis of `V`, embed `End_K V ↪ M_n(K)` by `LinearMap.toMatrix`, then apply
`Matrix.map (algebraMap K K̄)` to land in `M_n(K̄) = End_K̄(K̄ⁿ)`; this composite is an injective
`K`-algebra homomorphism carrying `CoreHyp p 𝒬 X` to `CoreHyp p (𝒬.map ·) (Units.map · X)`, so the
algebraically closed case `glCore_algClosed` (L16, in `GLCore/glCore_algClosed.lean`, already
proved) transfers the conclusion back.  (Equivalently one may tensor `V` with `AlgebraicClosure K`.)
-/
lemma glCore {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {p : ℕ}
    [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) [FiniteDimensional K V]
    {Q : Subgroup (Module.End K V)ˣ} {X : (Module.End K V)ˣ}
    (h : Work.HallHigman.CoreHyp p Q X) :
    ((X : Module.End K V) - 1) ^ (p - 1) ≠ 0 := by
  classical
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)) p
  haveI : IsAlgClosed (AlgebraicClosure K) := AlgebraicClosure.isAlgClosed K
  let F : Module.End K V →+* Module.End (AlgebraicClosure K)
      (Fin (Module.finrank K V) → AlgebraicClosure K) := glCoreScalarMap K (AlgebraicClosure K) V
  have hF : Function.Injective F :=
    glCoreScalarMap_injective K (AlgebraicClosure K)
      (FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)) V
  let u : (Module.End K V)ˣ →* (Module.End (AlgebraicClosure K)
      (Fin (Module.finrank K V) → AlgebraicClosure K))ˣ := Units.map F.toMonoidHom
  have hu : Function.Injective u := Units.map_injective hF
  set Q' : Subgroup (Module.End (AlgebraicClosure K)
      (Fin (Module.finrank K V) → AlgebraicClosure K))ˣ := Q.map u with hQ'
  set X' : (Module.End (AlgebraicClosure K)
      (Fin (Module.finrank K V) → AlgebraicClosure K))ˣ := u X with hX'
  have hcard : Nat.card Q' = Nat.card Q := by
    rw [hQ']; exact Subgroup.card_map_of_injective hu
  -- the core hypotheses transport along the injective `K`-algebra map `F`
  have hcore : CoreHyp p Q' X' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · haveI : Finite Q := h.finite
      rw [hQ']
      exact Finite.of_surjective (Subgroup.equivMapOfInjective Q u hu)
        (MulEquiv.surjective _)
    · rw [hcard]; exact h.odd
    · rw [hcard]; exact h.cop
    · rw [hX', ← map_pow u X p, h.pow, map_one]
    · intro a ha
      rw [hX', hQ'] at *
      obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
      rw [← map_mul, ← map_inv, ← map_mul]
      exact Subgroup.mem_map_of_mem u (h.norm a₀ ha₀)
    · obtain ⟨a₀, ha₀, hne⟩ := h.noncomm
      refine ⟨u a₀, ?_, ?_⟩
      · rw [hQ']; exact Subgroup.mem_map_of_mem u ha₀
      · intro hcontra
        rw [hX'] at hcontra
        refine hne (hu ?_)
        rw [map_mul, map_mul]
        exact hcontra
  -- the algebraically closed case
  have hkey := glCore_algClosed (K := AlgebraicClosure K)
    (V := Fin (Module.finrank K V) → AlgebraicClosure K) (p := p) (Q := Q') (X := X') hp2 hcore
  -- transfer the conclusion back along the injective map
  intro hzero
  apply hkey
  have hcoe : (X' : Module.End (AlgebraicClosure K)
      (Fin (Module.finrank K V) → AlgebraicClosure K)) = F (X : Module.End K V) := by
    rw [hX']; exact Units.coe_map F.toMonoidHom X
  rw [hcoe]
  have hmap : (F (X : Module.End K V) - 1) ^ (p - 1)
      = F (((X : Module.End K V) - 1) ^ (p - 1)) := by
    rw [map_pow, map_sub, map_one]
  rw [hmap, hzero, map_zero]

end Work.HallHigman.GLCore
