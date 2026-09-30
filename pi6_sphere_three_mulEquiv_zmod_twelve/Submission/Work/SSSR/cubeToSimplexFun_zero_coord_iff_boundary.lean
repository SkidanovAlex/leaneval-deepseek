import Mathlib
import Submission.Work.SSSR.HornDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open scoped Topology unitInterval
/-!
# A coordinate of `θ_n` vanishes iff the cube point lies on the boundary

`Work.SSSR.cubeToSimplexFun n : I^n → Δ^n` is defined by iterating the cone description of the
simplex (see `Work.SSSR.HornDefs`).  This file proves

`(∃ l, θ_n x l = 0) ↔ x ∈ Cube.boundary (Fin n)`,

i.e. the preimage of the union of the coordinate hyperplanes of `Δ^n` is exactly the boundary
`∂I^n` of the cube.  This is the "boundary" half of `Work.SSSR.cubeToSimplex_basic`.

The proof is the induction that the recursion of `θ` dictates.  Writing `x : I^{n+1}` as
`(Fin.init x, x (Fin.last n))` with `t := x (Fin.last n)`, the unfolded formula is

* `θ_{n+1}(x)_{last} = 1 - t`,
* `θ_{n+1}(x)_{succAbove j} = t * θ_n (Fin.init x)_j`,

so a coordinate of `θ_{n+1}(x)` vanishes iff `t = 1`, or `t = 0`, or some coordinate of
`θ_n (Fin.init x)` vanishes; and correspondingly `x` is in the boundary of `I^{n+1}` iff
`t = 1`, or `t = 0`, or `Fin.init x` is in the boundary of `I^n`.

We prove the two "unfolding" statements as the private lemmas `exists_zero_coord_succ` and
`mem_boundary_succ` and then combine them by induction.
-/

/-- Membership in the boundary of `I^{n+1}`, split off the last coordinate: a point of `I^{n+1}`
lies in the boundary iff its last coordinate is `0` or `1`, or its `Fin.init` lies in the
boundary of `I^n`. -/
private lemma mem_boundary_succ (n : ℕ) (x : Fin (n + 1) → unitInterval) :
    x ∈ Cube.boundary (Fin (n + 1)) ↔
      (x (Fin.last n) = 0 ∨ x (Fin.last n) = 1 ∨ Fin.init x ∈ Cube.boundary (Fin n)) := by
  constructor
  · rintro ⟨i, hi⟩
    rcases Fin.eq_self_or_eq_succAbove (Fin.last n) i with h | ⟨m, h⟩
    · subst h; tauto
    · right; right
      refine ⟨m, ?_⟩
      rw [h, Fin.succAbove_last_apply] at hi
      exact hi
  · rintro (h | h | h)
    · exact ⟨Fin.last n, Or.inl h⟩
    · exact ⟨Fin.last n, Or.inr h⟩
    · obtain ⟨m, hm⟩ := h
      exact ⟨m.castSucc, hm⟩

/-- A coordinate of `θ_{n+1}(x)` vanishes, split off the last coordinate. -/
private lemma exists_zero_coord_succ (n : ℕ) (x : Fin (n + 1) → unitInterval) :
    (∃ l : Fin (n + 2), (cubeToSimplexFun (n + 1) x : Fin (n + 2) → ℝ) l = 0) ↔
      ((x (Fin.last n) : ℝ) = 1 ∨ (x (Fin.last n) : ℝ) = 0 ∨
        ∃ j : Fin (n + 1), (cubeToSimplexFun n (Fin.init x) : Fin (n + 1) → ℝ) j = 0) := by
  have hsplit : (∃ l : Fin (n + 2), (cubeToSimplexFun (n + 1) x : Fin (n + 2) → ℝ) l = 0) ↔
      ((cubeToSimplexFun (n + 1) x : Fin (n + 2) → ℝ) (Fin.last (n + 1)) = 0 ∨
        ∃ j : Fin (n + 1),
          (cubeToSimplexFun (n + 1) x : Fin (n + 2) → ℝ) ((Fin.last (n + 1)).succAbove j)
            = 0) := by
    constructor
    · rintro ⟨l, hl⟩
      rcases Fin.eq_self_or_eq_succAbove (Fin.last (n + 1)) l with h | ⟨j, h⟩
      · exact Or.inl (by rwa [h] at hl)
      · exact Or.inr ⟨j, by rwa [h] at hl⟩
    · rintro (h | ⟨j, hj⟩)
      · exact ⟨_, h⟩
      · exact ⟨_, hj⟩
  rw [hsplit, cubeToSimplexFun_last]
  have h2 : ∀ j : Fin (n + 1),
      (cubeToSimplexFun (n + 1) x : Fin (n + 2) → ℝ) ((Fin.last (n + 1)).succAbove j) =
        (x (Fin.last n) : ℝ) * (cubeToSimplexFun n (Fin.init x) : Fin (n + 1) → ℝ) j :=
    fun j => cubeToSimplexFun_succAbove n x j
  simp only [h2]
  constructor
  · rintro (h | h)
    · left; linarith
    · rcases h with ⟨j, hj⟩
      rcases mul_eq_zero.mp hj with h0 | h0
      · right; left; exact h0
      · right; right; exact ⟨j, h0⟩
  · rintro (h | h | ⟨j, hj⟩)
    · left; rw [h]; norm_num
    · right; refine ⟨0, ?_⟩; rw [h, zero_mul]
    · right; refine ⟨j, ?_⟩; rw [hj, mul_zero]

/-- The master induction: a coordinate of `θ_n x` vanishes iff `x` lies on the boundary of the
cube. -/
private theorem zero_coord_iff_boundary_aux : ∀ n : ℕ, ∀ x : Fin n → unitInterval,
    (∃ l : Fin (n + 1), (cubeToSimplexFun n x : Fin (n + 1) → ℝ) l = 0) ↔
      x ∈ Cube.boundary (Fin n) := by
  intro n
  induction n with
  | zero =>
    intro x
    constructor
    · rintro ⟨l, hl⟩
      simp [cubeToSimplexFun] at hl
    · rintro ⟨i, _⟩
      exact Fin.elim0 i
  | succ n ih =>
    intro x
    rw [exists_zero_coord_succ n x, ih (Fin.init x), mem_boundary_succ n x]
    constructor
    · rintro (h | h | h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inr (Or.inl (by rw [h]; norm_num))
      · exact Or.inl (by rw [h]; norm_num)
      · exact Or.inr (Or.inr h)

/-- **A coordinate of `θ_n x` vanishes if and only if `x` is on the boundary of the cube.** -/
theorem cubeToSimplexFun_zero_coord_iff_boundary (n : ℕ) (x : Fin n → unitInterval) :
    (∃ l : Fin (n + 1), (Work.SSSR.cubeToSimplexFun n x : Fin (n + 1) → ℝ) l = 0) ↔
      x ∈ Cube.boundary (Fin n) :=
  zero_coord_iff_boundary_aux n x

end Work.SSSR
