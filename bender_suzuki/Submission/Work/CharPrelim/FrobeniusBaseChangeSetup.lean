import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Base change of a `Representation` along a field extension

This setup module provides `Work.CharPrelim.repBaseChange F k ρ`, the extension of scalars of a
representation `ρ : Representation F L V` along an algebra map `F → k` of fields, acting on the
`k`-vector space `k ⊗[F] V` by `l ↦ (ρ l).baseChange k`.

It exists so that the main lemma
`Submission.Work.CharPrelim.finrank_invariants_eq_of_isFrobenius` can reduce the statement over
`ZMod p` to the corresponding statement over an algebraically closed field (the algebraic closure
of `ZMod p`) by tensoring the representation with that field.

The field arguments `F` and `k` are made *explicit* so that callers can write
`repBaseChange F k ρ` without relying on named-argument resolution.
-/

open scoped MonoidAlgebra TensorProduct

noncomputable section

namespace Work.CharPrelim

/-- **Base change of a representation.**  For a field extension `F → k` and a representation
`ρ : Representation F L V`, this is the representation of `L` on `k ⊗[F] V` acting only on the
second tensor factor, `l ↦ (ρ l).baseChange k`.

Note `(repBaseChange F k ρ l) (a ⊗ₜ v) = a ⊗ₜ (ρ l v)`, see `repBaseChange_tmul_apply`. -/
def repBaseChange (F : Type*) (k : Type*) [Field F] [Field k] [Algebra F k]
    {L : Type*} [Group L] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F L V) : Representation k L (k ⊗[F] V) where
  toFun l := (ρ l).baseChange k
  map_one' := by
    rw [map_one]
    exact LinearMap.baseChange_one F V
  map_mul' l m := by
    rw [map_mul, LinearMap.baseChange_mul]

@[simp]
theorem repBaseChange_tmul_apply (F : Type*) (k : Type*) [Field F] [Field k] [Algebra F k]
    {L : Type*} [Group L] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F L V) (l : L) (a : k) (v : V) :
    repBaseChange F k ρ l (a ⊗ₜ[F] v) = a ⊗ₜ[F] (ρ l v) := rfl

/-- The `k`-linear map underlying `repBaseChange F k ρ l` is `LinearMap.baseChange`. -/
@[simp]
theorem repBaseChange_apply (F : Type*) (k : Type*) [Field F] [Field k] [Algebra F k]
    {L : Type*} [Group L] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F L V) (l : L) :
    repBaseChange F k ρ l = (ρ l).baseChange k := rfl

end Work.CharPrelim
