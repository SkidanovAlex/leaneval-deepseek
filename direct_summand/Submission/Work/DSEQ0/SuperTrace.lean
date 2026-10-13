import Mathlib
import ChallengeDeps
import Submission.Work.DSMap.Map
import Submission.Work.DSEQ0.Basic
import Submission.Work.DSEQ0.Model

/-!
# DSEQ0 (area EQ0): the supertrace of a finite free graded module

The trace argument of area `EQ0` (Bhatt's remark "trace on the perfect complex `RΓ`", see
`sources/dsmap/direct_summap_proof_map.md` §5 and `direct_summand_honest_route.md` §2.3)
produces, on a bounded complex of finite free `A`-modules, a functional
`φ : P⁰ ⟶ A` by the formula `φ(x) = Σᵢ (-1)ⁱ tr(μ(x,−)|_{Pⁱ})`, where `μ` is a strictly unital
product.  The two properties used are

* `φ(d y) = 0`, because `μ(d y, −)` is a graded commutator and supertraces of graded
  commutators vanish (this makes `φ` a chain map `P ⟶ A[0]`, which for `P` concentrated in
  degrees `≥ 0` is automatic anyway); and
* `φ(c 1) = χ`, the Euler characteristic, because `μ` is strictly unital.

This file sets up the notion of supertrace and the Euler characteristic of such a family of
finite free modules.  The two combinatorial lemmas about it are delegated.
-/

open CategoryTheory AlgebraicGeometry Limits

namespace Work.DSEQ0

universe u v w

variable (A : Type u) [CommRing A]

/-- The Euler characteristic `Σᵢ (-1)ⁱ rk (M i)` of a family of finite free `A`-modules indexed
by `Fin (N+1)`.  For a bounded complex this is the Euler characteristic of the complex. -/
noncomputable def eulerChar {N : ℕ} (M : Fin (N + 1) → Type u) [∀ i, AddCommGroup (M i)]
    [∀ i, Module A (M i)] [∀ i, Module.Finite A (M i)] [∀ i, Module.Free A (M i)] : A :=
  ∑ i : Fin (N + 1), (-1 : A) ^ (i : ℕ) * (Module.finrank A (M i) : A)

/-- The supertrace of a family of endomorphisms of a finite free graded `A`-module:
`Σᵢ (-1)ⁱ tr (αᵢ)`. -/
noncomputable def superTrace {N : ℕ} (M : Fin (N + 1) → Type u) [∀ i, AddCommGroup (M i)]
    [∀ i, Module A (M i)] [∀ i, Module.Finite A (M i)] [∀ i, Module.Free A (M i)]
    (α : ∀ i, M i →ₗ[A] M i) : A :=
  ∑ i : Fin (N + 1), (-1 : A) ^ (i : ℕ) * LinearMap.trace A (M i) (α i)

@[simp]
theorem superTrace_one {N : ℕ} (M : Fin (N + 1) → Type u) [∀ i, AddCommGroup (M i)]
    [∀ i, Module A (M i)] [∀ i, Module.Finite A (M i)] [∀ i, Module.Free A (M i)] :
    superTrace A M (fun _ => 1) = eulerChar A M := by
  simp [superTrace, eulerChar]

theorem superTrace_add {N : ℕ} (M : Fin (N + 1) → Type u) [∀ i, AddCommGroup (M i)]
    [∀ i, Module A (M i)] [∀ i, Module.Finite A (M i)] [∀ i, Module.Free A (M i)]
    (α β : ∀ i, M i →ₗ[A] M i) :
    superTrace A M (fun i => α i + β i) = superTrace A M α + superTrace A M β := by
  simp only [superTrace, ← Finset.sum_add_distrib, ← mul_add, map_add]

theorem superTrace_smul {N : ℕ} (M : Fin (N + 1) → Type u) [∀ i, AddCommGroup (M i)]
    [∀ i, Module A (M i)] [∀ i, Module.Finite A (M i)] [∀ i, Module.Free A (M i)]
    (a : A) (α : ∀ i, M i →ₗ[A] M i) :
    superTrace A M (fun i => a • α i) = a * superTrace A M α := by
  simp only [superTrace, map_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `superTrace` as an `A`-linear functional on the module of families of endomorphisms. -/
noncomputable def superTraceLin {N : ℕ} (M : Fin (N + 1) → Type u) [∀ i, AddCommGroup (M i)]
    [∀ i, Module A (M i)] [∀ i, Module.Finite A (M i)] [∀ i, Module.Free A (M i)] :
    (∀ i, M i →ₗ[A] M i) →ₗ[A] A where
  toFun := superTrace A M
  map_add' := superTrace_add A M
  map_smul' := superTrace_smul A M

end Work.DSEQ0
