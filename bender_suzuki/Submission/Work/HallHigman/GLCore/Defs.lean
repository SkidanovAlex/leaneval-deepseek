/-
Area A10 of the Feit--Thompson (odd order theorem) drive, Hall--Higman Theorem B:
shared definitions for the "GL-core" proof of the order-`p` form of Theorem B.

The mathematical design is `Submission/Work/NOTES_LEAD_ft_hallhigman.md` (project lead,
2026-09-28): the odd-order form of Hall--Higman's Theorem B that Feit--Thompson §7 consumes is

  **(B1)**  `G` finite `p`-solvable of odd order, `V` a faithful `K[G]`-module with `char K = p`
  and `O_p(G) = 1`, `x ≠ 1`  ⟹  `(V.ρ x - 1) ^ (p - 1) ≠ 0`.

Its proof reduces (via `centralizer (O_{p'} G) ≤ O_{p'} G`, see `FT71`/`GLCore.L15`) to a purely
linear-algebraic statement about a finite odd-order `p'`-group `Q ≤ GL(V)` normalised by an
element `X` of order `p` which does not commute with `Q` ("the GL-core", `CoreHyp` below), proved
by a double induction with an abelian case and a non-abelian case (Fourier decomposition of
`End V` under `Q`, a commutant dimension bound, and an arithmetic contradiction).

This file contains the four shared definitions of that design.  The contracts L0–L19 listed in
`NOTES_LEAD_ft_hallhigman.md` §3 refer to them.
-/
import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

universe u v w

namespace Work.HallHigman

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

/-- The commutant of a single endomorphism: `{Y | T * Y = Y * T}`. -/
def commutant (T : Module.End K V) : Submodule K (Module.End K V) :=
  LinearMap.ker (LinearMap.mulLeft K T - LinearMap.mulRight K T)

theorem mem_commutant_iff {T Y : Module.End K V} :
    Y ∈ commutant T ↔ T * Y = Y * T := by
  rw [commutant, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

/-- The commutant of a representation: the `E`-endomorphisms of `V`. -/
def commutantOf {E : Type w} [Monoid E] (σ : E →* Module.End K V) :
    Submodule K (Module.End K V) :=
  ⨅ e, commutant (σ e)

theorem mem_commutantOf_iff {E : Type w} [Monoid E] {σ : E →* Module.End K V}
    {Y : Module.End K V} :
    Y ∈ commutantOf σ ↔ ∀ e : E, σ e * Y = Y * σ e := by
  rw [commutantOf, Submodule.mem_iInf]
  exact forall_congr' fun e => mem_commutant_iff

theorem one_mem_commutantOf {E : Type w} [Monoid E] (σ : E →* Module.End K V) :
    (1 : Module.End K V) ∈ commutantOf σ :=
  (mem_commutantOf_iff).mpr fun e => by rw [mul_one, one_mul]

/-- `V` is irreducible for a set of operators: it is nontrivial and has no nontrivial subspace
invariant under all of them. -/
def IsIrreducibleFor (S : Set (Module.End K V)) : Prop :=
  Nontrivial V ∧ ∀ U : Submodule K V, (∀ s ∈ S, U ≤ U.comap s) → U = ⊥ ∨ U = ⊤

/-- The hypotheses of the GL-core: `𝒬 ≤ GL(V)` is finite of odd order prime to `p` (whence a
`p'`-group), `X` has order `p` (whence a `p`-element of the normaliser), it normalises `𝒬`, and it
does not commute with `𝒬`. -/
structure CoreHyp (p : ℕ) (Q : Subgroup (Module.End K V)ˣ) (X : (Module.End K V)ˣ) : Prop where
  /-- `𝒬` is finite. -/
  finite : Finite Q
  /-- `|𝒬|` is odd. -/
  odd : Odd (Nat.card Q)
  /-- `p ∤ |𝒬|`. -/
  cop : ¬ p ∣ Nat.card Q
  /-- `X` has order `p`. -/
  pow : X ^ p = 1
  /-- `X` normalises `𝒬`. -/
  norm : ∀ a ∈ Q, X * a * X⁻¹ ∈ Q
  /-- `X` does not commute with `𝒬`. -/
  noncomm : ∃ a ∈ Q, a * X ≠ X * a

end Work.HallHigman
