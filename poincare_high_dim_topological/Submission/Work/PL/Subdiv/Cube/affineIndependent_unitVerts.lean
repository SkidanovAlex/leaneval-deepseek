import Mathlib
import Submission.Work.PL.Subdiv.Cube.Defs

/-!
# The Freudenthal vertices of the unit cube are affinely independent

`unitVerts π` is the vertex set `{w_0, …, w_n}` of the Freudenthal (Kuhn) simplex of the unit
cube attached to the ordering `π`.  These are `n + 1` points of `E n = ℝⁿ`, and they are
affinely independent: they are the vertices of a genuine `n`-simplex.

The proof reduces, via `affineIndependent_iff_linearIndependent_vsub` with base point
`w_n = 0`, to the linear independence of `w_0, …, w_{n-1} = w_0 - w_n, …, w_{n-1} - w_n`.
For those, the coordinate `π a` of `w_k` is `1` exactly when `k ≤ a`; testing against the
coordinate functionals therefore gives the triangular system `∑_{k ≤ a} c_k = 0`, whose
unique solution is `c = 0`.
-/

open PL
open scoped BigOperators

namespace Work.PL.Subdiv.Cube

noncomputable section

variable {n : ℕ}

/-- The Freudenthal vectors `w_0, …, w_{n-1}` of the unit cube (the vertices of the unit
Freudenthal simplex other than the origin) are linearly independent. -/
theorem wvec_linearIndependent (π : Equiv.Perm (Fin n)) :
    LinearIndependent ℝ (fun b : Fin n => wvec π (b : ℕ)) := by
  rw [linearIndependent_iff']
  intro s g hg j hj
  -- Reading off the `π a`-th coordinate of the linear combination gives the triangular system
  -- `∑_{b ∈ s, b ≤ a} g b = 0`.
  have hkey : ∀ a : Fin n, ∑ b ∈ s, g b * (if b.val ≤ a.val then (1 : ℝ) else 0) = 0 := by
    intro a
    have h1 := congrArg (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) (π a)) hg
    simp only [map_sum, map_smul, PiLp.proj_apply, map_zero, wvec_at] at h1
    simpa using h1
  have hkey' : ∀ a : Fin n, ∑ b ∈ s.filter (fun b => b.val ≤ a.val), g b = 0 := by
    intro a
    rw [Finset.sum_filter]
    have h := hkey a
    simpa only [mul_ite, mul_one, mul_zero] using h
  -- Strong induction on the value of `j`: the prefix sums determine the coefficients.
  have main : ∀ k : ℕ, ∀ j : Fin n, j.val < k → j ∈ s → g j = 0 := by
    intro k
    induction k with
    | zero => intro j h _; exact absurd h (Nat.not_lt_zero _)
    | succ k ih =>
      intro j hjk hj
      have hsplit : ∑ b ∈ s.filter (fun b => b.val ≤ j.val), g b
          = (∑ b ∈ s.filter (fun b => b.val < j.val), g b)
            + (∑ b ∈ s.filter (fun b => b.val = j.val), g b) := by
        rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases h1 : b.val < j.val
        · have h2 : b.val ≠ j.val := by omega
          simp [h1, Nat.le_of_lt h1, h2]
        · by_cases h2 : b.val = j.val
          · simp [h2]
          · have h3 : ¬ b.val ≤ j.val := by omega
            simp [h1, h2, h3]
      have hB : ∑ b ∈ s.filter (fun b => b.val < j.val), g b = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        rw [Finset.mem_filter] at hb
        exact ih b (by omega) hb.1
      have hC : ∑ b ∈ s.filter (fun b => b.val = j.val), g b = g j := by
        have hfil : s.filter (fun b => b.val = j.val) = {j} := by
          ext b; simp only [Finset.mem_filter, Finset.mem_singleton]
          exact ⟨fun h => Fin.ext h.2, fun h => ⟨h ▸ hj, by rw [h]⟩⟩
        rw [hfil, Finset.sum_singleton]
      have h0 := hkey' j
      rw [hsplit, hB, hC] at h0
      simpa using h0
  exact main (j.val + 1) j (Nat.lt_succ_self _) hj

/-- The Freudenthal vectors `w_0, …, w_n` of the unit cube, indexed by `Fin (n+1)`, are
affinely independent. -/
theorem wvec_affineIndependent (π : Equiv.Perm (Fin n)) :
    AffineIndependent ℝ (fun k : Fin (n + 1) => wvec π (k : ℕ)) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (Fin.last n)]
  refine (linearIndependent_equiv (finSuccAboveEquiv (Fin.last n))).mp ?_
  convert wvec_linearIndependent π using 1
  ext b
  simp [Function.comp_apply, finSuccAboveEquiv_apply, Fin.succAbove_last, wvec_last]

theorem affineIndependent_unitVerts (n : ℕ) (π : Equiv.Perm (Fin n)) :
    AffineIndependent ℝ ((↑) : ↥(unitVerts π) → PL.E n) := by
  have haff := wvec_affineIndependent π
  have hrange : Set.range (fun k : Fin (n + 1) => wvec π (k : ℕ)) = (unitVerts π : Set (PL.E n)) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact mem_unitVerts (Nat.le_of_lt_succ k.isLt)
    · intro hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨⟨k, Finset.mem_range.mp hk⟩, rfl⟩
  have h := haff.range
  rw [hrange] at h
  exact h

end

end Work.PL.Subdiv.Cube
