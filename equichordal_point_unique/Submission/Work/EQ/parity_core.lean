import Mathlib

/-!
# Parity core for the equichordal point problem

This file isolates the elementary parity/arithmetic heart of the equichordal
non-existence argument.  A "walk" on the line whose steps replace `x` by `ε - x`
with `ε = ±1` consists of the two reflections `x ↦ 1 - x` and `x ↦ -1 - x`; their
product is the translation `x ↦ x ± 2`.  Consequently a walk that starts at `-B`
and ends at `B` after `N` steps forces `2B` to be an integer when `N` is even
(impossible for `0 < B < 1/2`), and forces a sum of an odd number of `±1`'s to
vanish when `N` is odd.  This is the contradiction proved as `parity_core`.
-/

namespace Work.EQ

/-- **Parity core.**  A sequence `x : ℕ → ℂ` whose successive terms satisfy
`x (k+1) = ε - x k` with `ε = ±1` (for every `k < N`) cannot run from `x 0 = -B`
to `x N = B` when `0 < B < 1/2`.

The proof tracks the invariant `x k = (-1)^k * (-B) + k + 2m` with `m : ℤ`: the
affine part of the composition of `k` involutions `x ↦ ±1 - x`, whose slope is
`(-1)^k` and whose constant has the same parity as `k`. -/
theorem parity_core (B : ℝ) (hB0 : 0 < B) (hB1 : B < 1 / 2) (x : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N)
    (hrec : ∀ k, k < N → ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ x (k + 1) = ε - x k)
    (hx0 : x 0 = -(B : ℂ)) (hxN : x N = (B : ℂ)) : False := by
  -- `hN` is not needed below, but it belongs to the statement; reference it so that
  -- the proof term does not report it as unused.
  have _hN : 1 ≤ N := hN
  -- Invariant: for every `k ≤ N` there is `m : ℤ` with
  --   `x k = (-1)^k * (-B) + k + 2m`, the right-hand side being viewed in `ℂ`.
  have key : ∀ k, k ≤ N →
      ∃ m : ℤ, x k = (((-1:ℝ)^k * (-B) + (k:ℝ) + 2*(m:ℝ) : ℝ) : ℂ) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨0, by rw [hx0]; push_cast; ring⟩
    | succ k ih =>
      intro hk1
      -- `k < N`, so the recurrence hypothesis applies at `k`.
      have hkN : k < N := by omega
      obtain ⟨ε, hε, hrec'⟩ := hrec k hkN
      obtain ⟨m, hm⟩ := ih (by omega)
      -- `x (k+1) = ε - x k` and `ε = ±1`; the integer constant transforms as
      -- `m ↦ -(k+m)` (for `ε = 1`) resp. `m ↦ -1-(k+m)` (for `ε = -1`).
      rcases hε with hε | hε
      · refine ⟨-(k:ℤ) - m, ?_⟩
        rw [hrec', hε, hm]; push_cast; ring
      · refine ⟨-(k:ℤ) - 1 - m, ?_⟩
        rw [hrec', hε, hm]; push_cast; ring
  obtain ⟨m, hkey⟩ := key N le_rfl
  rw [hxN] at hkey
  -- The complex equation is the image of a real one.
  have hreal : B = (-1:ℝ)^N * (-B) + (N:ℝ) + 2*(m:ℝ) := Complex.ofReal_inj.mp hkey
  rcases Nat.even_or_odd N with hev | hod
  · -- `N` even: `2B = N + 2m` exhibits `B` as an integer.
    obtain ⟨j, hj⟩ := hev
    rw [hj] at hreal
    have hp : (-1:ℝ)^(j+j) = 1 := Even.neg_one_pow ⟨j, rfl⟩
    rw [hp] at hreal
    have hz : B = (((j:ℤ) + m : ℤ) : ℝ) := by
      push_cast at hreal ⊢
      linarith
    have hzpos : (0:ℝ) < (((j:ℤ) + m : ℤ) : ℝ) := by rw [← hz]; exact hB0
    have hzlt : (((j:ℤ) + m : ℤ) : ℝ) < 1 := by rw [← hz]; linarith
    have hzi0 : (0:ℤ) < (j:ℤ) + m := by exact_mod_cast hzpos
    have hzi1 : (j:ℤ) + m < 1 := by exact_mod_cast hzlt
    omega
  · -- `N` odd: `0 = N + 2m` with `N` odd and `2m` even is impossible.
    obtain ⟨j, hj⟩ := hod
    rw [hj] at hreal
    have hp : (-1:ℝ)^(2*j+1) = -1 := Odd.neg_one_pow ⟨j, rfl⟩
    rw [hp] at hreal
    have h0 : (((2:ℤ)*(j:ℤ) + 1 + 2*m : ℤ) : ℝ) = 0 := by
      push_cast at hreal ⊢
      linarith
    have h0' : (2:ℤ)*(j:ℤ) + 1 + 2*m = 0 := by exact_mod_cast h0
    omega

end Work.EQ
