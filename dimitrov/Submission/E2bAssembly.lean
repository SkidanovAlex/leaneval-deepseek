import Mathlib
import Submission.E2bGeneral
import Submission.E2bInst
import Submission.E2bCells
import Submission.SeamCells
import Submission.DirCycle
import Submission.DirSet

/-!
# E2b assembly: the boundary parametrisation of the star's cell spine

`Submission.E2bT.circle_eq_cap_sum` (`Submission/E2bGeneral.lean`,
general-`s`, PROVED) is stated in a *boundary parametrisation*: a function
`b : ℕ → ℝ` whose pieces `(b k, b (k+1))` (`k < 2s`) are alternately the
window (even `k = 2j`, radial `[u j, B]`) and gap (odd `k = 2j+1`, radial
`[A, B]`) cells of the E2b deformation, with `hb : b (2s) = b 0 + 2π` the
cyclic closure.  This module *instantiates that parametrisation for the
actual hedgehog spine*:

    dirX  S h0 j  := (dirList S).get ⟨j, ·⟩      (j < length)
                    else (dirList S).get ⟨0, h0⟩ + 2π   (the cyclic
                    extension: dirX at `length` closes the spine)
    boundary S h0 δ k := dirX S h0 (k/2) − δ      (even k)
                    else dirX S h0 (k/2) + δ      (odd k)

so that window `j` is over angles `(x_j − δ, x_j + δ)` and the last gap
wraps through `b (2s) = b 0 + 2π` (`b_wrap`, the `hb` hypothesis of
`circle_eq_cap_sum`).  The lemmas `b_even`/`b_odd`/`b_two_s`/`b_zero`
convert the boundary values back to the direction list; `b_lt_two_s`
encodes the alternation for `k < 2s`.

The full instantiation of `circle_eq_cap_sum` (deriving `hwin` from
`Submission.E2bCells.nonseam_window_zero_*` and
`Submission.SeamCells.seam_window_zero_*`, `hgap` from
`Submission.SpineGaps.gap_cell_between_dirList` plus the wrap-gap seam
split, and the integrability families from
`Submission.E2bCells.intervalIntegrable_pull_arc/_radial`) is assembled in
a later module on top of this parametrisation.
-/

noncomputable section
open scoped Real
namespace Submission.E2bAssembly

open Submission.DirCycle
open Submission.DirSet

/-- The direction of the spine at index `j`, extended cyclically by a full
turn after the last entry (`dirX` at `length` is `x_0 + 2π`). -/
def dirX (S : Finset ℂ) (h0 : 0 < (dirList S).length) (j : ℕ) : ℝ :=
  if h : j < (dirList S).length then (dirList S).get ⟨j, h⟩
  else (dirList S).get ⟨0, h0⟩ + 2 * Real.pi

/-- The E2b boundary parametrisation: `b (2j) = x_j − δ` (window left),
`b (2j+1) = x_j + δ` (window right), `b (2s) = x_0 + 2π − δ` (the wrap). -/
def boundary (S : Finset ℂ) (h0 : 0 < (dirList S).length) (δ : ℝ) (k : ℕ) : ℝ :=
  if k % 2 = 0 then dirX S h0 (k / 2) - δ
  else dirX S h0 (k / 2) + δ

/-- `dirX` agrees with the list entry below the length. -/
lemma dirX_of_lt (S : Finset ℂ) (h0 : 0 < (dirList S).length) {j : ℕ}
    (hj : j < (dirList S).length) : dirX S h0 j = (dirList S).get ⟨j, hj⟩ := by
  simp [dirX, hj]

/-- `dirX` at the length closes the spine (`x_0 + 2π`). -/
lemma dirX_length (S : Finset ℂ) (h0 : 0 < (dirList S).length) :
    dirX S h0 (dirList S).length = (dirList S).get ⟨0, h0⟩ + 2 * Real.pi := by
  simp [dirX]

/-- Boundary at an even index below `2s`: `b (2j) = x_j − δ`. -/
lemma b_even (S : Finset ℂ) (h0 : 0 < (dirList S).length) (δ : ℝ) {j : ℕ}
    (hj : j < (dirList S).length) :
    boundary S h0 δ (2 * j) = (dirList S).get ⟨j, hj⟩ - δ := by
  unfold boundary
  have hpar : (2 * j) % 2 = 0 := by omega
  have hdiv : (2 * j) / 2 = j := by omega
  simp [hpar, hdiv]
  exact dirX_of_lt S h0 hj

/-- Boundary at an odd index below `2s`: `b (2j+1) = x_j + δ`. -/
lemma b_odd (S : Finset ℂ) (h0 : 0 < (dirList S).length) (δ : ℝ) {j : ℕ}
    (hj : j < (dirList S).length) :
    boundary S h0 δ (2 * j + 1) = (dirList S).get ⟨j, hj⟩ + δ := by
  unfold boundary
  have hpar0 : (2 * j + 1) % 2 ≠ 0 := by omega
  have hdiv : (2 * j + 1) / 2 = j := by omega
  simp [hpar0, hdiv]
  exact dirX_of_lt S h0 hj

/-- Boundary at zero: `b 0 = x_0 − δ`. -/
lemma b_zero (S : Finset ℂ) (h0 : 0 < (dirList S).length) (δ : ℝ) :
    boundary S h0 δ 0 = (dirList S).get ⟨0, h0⟩ - δ := by
  simpa using (b_even S h0 δ (j := 0) h0)

/-- Boundary at `2s` (the wrap): `b (2s) = x_0 + 2π − δ`. -/
lemma b_two_s (S : Finset ℂ) (h0 : 0 < (dirList S).length) (δ : ℝ) :
    boundary S h0 δ (2 * (dirList S).length) =
      (dirList S).get ⟨0, h0⟩ + 2 * Real.pi - δ := by
  unfold boundary
  have hpar : (2 * (dirList S).length) % 2 = 0 := by omega
  have hdiv : (2 * (dirList S).length) / 2 = (dirList S).length := by omega
  simp [hpar, hdiv]
  exact dirX_length S h0

/-- **The cyclic closure (`hb` of `circle_eq_cap_sum`).**  `b (2s) = b 0 +
2π`: the boundary list closes on itself after a full turn. -/
theorem b_wrap (S : Finset ℂ) (h0 : 0 < (dirList S).length) (δ : ℝ) :
    boundary S h0 δ (2 * (dirList S).length) =
      boundary S h0 δ 0 + 2 * Real.pi := by
  rw [b_two_s, b_zero]
  ring

/-- Boundary at `2(j+1)` below `2s`: `b (2(j+1)) = x_{j+1} − δ`. -/
lemma b_two_j_two (S : Finset ℂ) (h0 : 0 < (dirList S).length) (δ : ℝ) {j : ℕ}
    (hj : j + 1 < (dirList S).length) :
    boundary S h0 δ (2 * j + 2) = (dirList S).get ⟨j + 1, hj⟩ - δ := by
  have hpar : 2 * j + 2 = 2 * (j + 1) := by omega
  rw [hpar]
  exact b_even S h0 δ hj


open scoped Complex Real Interval BigOperators
open Complex
open MeasureTheory
open Submission.Fold
open Submission.E2bT

def bX (x : ℕ → ℝ) (δ : ℝ) (k : ℕ) : ℝ :=
  if k % 2 = 0 then x (k / 2) - δ else x (k / 2) + δ

lemma bX_even (x : ℕ → ℝ) (δ : ℝ) (j : ℕ) : bX x δ (2 * j) = x j - δ := by
  unfold bX
  have hpar : (2 * j) % 2 = 0 := by omega
  have hdiv : (2 * j) / 2 = j := by omega
  simp [hpar, hdiv]

lemma bX_odd (x : ℕ → ℝ) (δ : ℝ) (j : ℕ) : bX x δ (2 * j + 1) = x j + δ := by
  unfold bX
  have hpar : (2 * j + 1) % 2 ≠ 0 := by omega
  have hdiv : (2 * j + 1) / 2 = j := by omega
  simp [hpar, hdiv]

lemma bX_even' (x : ℕ → ℝ) (δ : ℝ) (j : ℕ) : bX x δ (2 * j + 2) = x (j + 1) - δ := by
  have h : 2 * j + 2 = 2 * (j + 1) := by omega
  rw [h]
  exact bX_even x δ (j + 1)

lemma bX_wrap (x : ℕ → ℝ) (δ : ℝ) (s : ℕ) (hcl : x s = x 0 + 2 * Real.pi) :
    bX x δ (2 * s) = bX x δ 0 + 2 * Real.pi := by
  rw [bX_even, bX_even (j := 0)]
  rw [hcl]
  ring

/-- The deformation identity in direction form (x, u : ℕ → ℝ, `x s = x 0 +
2π` the cyclic closure). -/
theorem circle_eq_cap_sum_x (h : ℂ → ℂ) (s : ℕ) (hs : 1 ≤ s) (A B δ : ℝ)
    (x u : ℕ → ℝ) (hcl : x s = x 0 + 2 * Real.pi)
    (hBwin : ∀ j : ℕ, j < s → IntervalIntegrable
      (fun y : ℝ => Submission.E2bCore.pull h (B + y * Complex.I)) volume (x j - δ) (x j + δ))
    (hBgap : ∀ j : ℕ, j < s → IntervalIntegrable
      (fun y : ℝ => Submission.E2bCore.pull h (B + y * Complex.I)) volume (x j + δ) (x (j + 1) - δ))
    (hRwinL : ∀ j : ℕ, j < s → IntervalIntegrable
      (fun t : ℝ => Submission.E2bCore.pull h (t + (x j - δ : ℝ) * Complex.I)) volume A (u j))
    (hRwinLB : ∀ j : ℕ, j < s → IntervalIntegrable
      (fun t : ℝ => Submission.E2bCore.pull h (t + (x j - δ : ℝ) * Complex.I)) volume (u j) B)
    (hRwinR : ∀ j : ℕ, j < s → IntervalIntegrable
      (fun t : ℝ => Submission.E2bCore.pull h (t + (x j + δ : ℝ) * Complex.I)) volume A (u j))
    (hRwinRB : ∀ j : ℕ, j < s → IntervalIntegrable
      (fun t : ℝ => Submission.E2bCore.pull h (t + (x j + δ : ℝ) * Complex.I)) volume (u j) B)
    (hwin : ∀ j : ℕ, j < s →
      cellExpr (Submission.E2bCore.pull h) (u j) B (x j - δ) (x j + δ) = 0)
    (hgap : ∀ j : ℕ, j < s →
      cellExpr (Submission.E2bCore.pull h) A B (x j + δ) (x (j + 1) - δ) = 0) :
    (∮ z in C((0 : ℂ), Real.exp B), h z) =
      (∑ j ∈ Finset.range s,
        Complex.I • arcInt (Submission.E2bCore.pull h) (u j) (x j - δ) (x j + δ))
        + (∑ j ∈ Finset.range s,
        Complex.I • arcInt (Submission.E2bCore.pull h) A (x j + δ) (x (j + 1) - δ))
        + (∑ j ∈ Finset.range s, radInt (Submission.E2bCore.pull h) A (u j) (x j - δ))
        - (∑ j ∈ Finset.range s, radInt (Submission.E2bCore.pull h) A (u j) (x j + δ)) := by
  classical
  -- the b-indexed integrability over all 2s pieces
  have hBint : ∀ k : ℕ, k < 2 * s → IntervalIntegrable
      (fun y : ℝ => Submission.E2bCore.pull h (B + y * Complex.I)) volume (bX x δ k) (bX x δ (k + 1)) := by
    intro k hk
    have hpar : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hpar with hpar | hpar
    · -- k even: piece over (x(k/2) − δ, x(k/2) + δ)
      have hkj : k / 2 < s := by omega
      have hkdef : bX x δ k = x (k / 2) - δ := by
        unfold bX
        simp [hpar]
      have hksucc : bX x δ (k + 1) = x (k / 2) + δ := by
        have hodd : (k + 1) % 2 ≠ 0 := by omega
        have hdiv : (k + 1) / 2 = k / 2 := by omega
        unfold bX
        simp [hodd, hdiv]
      rw [hkdef, hksucc]
      exact hBwin (k / 2) hkj
    · -- k odd: piece over (x(k/2) + δ, x(k/2 + 1) − δ)
      have hkodd : (k + 1) % 2 = 0 := by omega
      have hkj : k / 2 < s := by omega
      have hksucc_j : (k + 1) / 2 = k / 2 + 1 := by omega
      have hkdef : bX x δ k = x (k / 2) + δ := by
        unfold bX
        simp [hpar]
      have hksucc : bX x δ (k + 1) = x (k / 2 + 1) - δ := by
        unfold bX
        simp [hkodd, hksucc_j]
      rw [hkdef, hksucc]
      exact hBgap (k / 2) hkj
  -- radials (even angles = x_j − δ and odd = x_j + δ are both windows edges of u_j at b(2j), b(2j+1))
  have hRint : ∀ j : ℕ, j < s → IntervalIntegrable
      (fun t : ℝ => Submission.E2bCore.pull h (t + (bX x δ (2 * j) : ℂ) * Complex.I)) volume A (u j) := by
    intro j hj
    rw [bX_even]
    exact hRwinL j hj
  have hRintB : ∀ j : ℕ, j < s → IntervalIntegrable
      (fun t : ℝ => Submission.E2bCore.pull h (t + (bX x δ (2 * j) : ℂ) * Complex.I)) volume (u j) B := by
    intro j hj
    rw [bX_even]
    exact hRwinLB j hj
  have hRint' : ∀ j : ℕ, j < s → IntervalIntegrable
      (fun t : ℝ => Submission.E2bCore.pull h (t + (bX x δ (2 * j + 1) : ℂ) * Complex.I)) volume A (u j) := by
    intro j hj
    rw [bX_odd]
    exact hRwinR j hj
  have hRintB' : ∀ j : ℕ, j < s → IntervalIntegrable
      (fun t : ℝ => Submission.E2bCore.pull h (t + (bX x δ (2 * j + 1) : ℂ) * Complex.I)) volume (u j) B := by
    intro j hj
    rw [bX_odd]
    exact hRwinRB j hj
  -- cell zeros in b-form
  have hwinb : ∀ j : ℕ, j < s →
      cellExpr (Submission.E2bCore.pull h) (u j) B (bX x δ (2 * j)) (bX x δ (2 * j + 1)) = 0 := by
    intro j hj
    rw [bX_even, bX_odd]
    exact hwin j hj
  have hgapb : ∀ j : ℕ, j < s →
      cellExpr (Submission.E2bCore.pull h) A B (bX x δ (2 * j + 1)) (bX x δ (2 * j + 2)) = 0 := by
    intro j hj
    rw [bX_odd, bX_even']
    exact hgap j hj
  have hm := circle_eq_cap_sum h s hs A B (bX x δ) u (bX_wrap x δ s hcl) hBint
    hRint hRintB hRint' hRintB' hwinb hgapb
  -- rewrite the RHS from b-form to x-form
  simpa [bX_even, bX_odd, bX_even', Finset.sum_congr] using hm

/-! ## The assembled deformation over the star

Proved in `Submission/DStar.lean` as `Submission.DStar.deformation_star`
(identical statement): it instantiates `circle_eq_cap_sum_x` above with
`x j := dirX S hlen0 j` and the per-window/per-gap cell zeros of
`Submission.E2bInst`/`Submission.SeamCells`. -/

end Submission.E2bAssembly

end
