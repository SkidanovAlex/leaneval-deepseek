import Mathlib
import Submission.E2bTelescope
import Submission.Fold
import Submission.E2bCore

/-!
# E2b telescope, general s: window+gap cell zeros ⟹ deformation identity

This is the general-`s` generalization of
`Submission.E2bT.circle_eq_cap_sum_s1` (the s = 1 template, PROVED in
`Submission/E2bTelescope.lean`).  It is the E2b algebraic core: summing the
per-cell Cauchy identities of the `2s` cells that partition the annulus
between the big circle `C(0, e^B)` and the ε-contour `Γ` hugging the
hedgehog collapses (pure interval-integral algebra) to

    ∮_{C(0,e^B)} h
      = Σ_{j<s} I • arcInt(pull h) (u j) (b (2j))   (b (2j+1))     [tip caps]
      + Σ_{j<s} I • arcInt(pull h) A     (b (2j+1)) (b (2j+2))     [gap arcs]
      + Σ_{j<s} radInt(pull h) A (u j) (b (2j))
      - Σ_{j<s} radInt(pull h) A (u j) (b (2j+1))                  [radial sides]

in the *boundary parametrisation*: for `s ≥ 1` spikes, the boundary list
`b : ℕ → ℝ` runs over the `2s` consecutive angular pieces
`(b 0, b 1), (b 1, b 2), …, (b (2s−1), b (2s))` of a fundamental angular
window of length `2π`; the even pieces `(b(2j), b(2j+1))` are the *window*
(above-the-tip) cells over radial `[u j, B]` around spike `j`, and the odd
pieces `(b(2j+1), b(2j+2))` are the *gap* cells over radial `[A, B]`.
The hypothesis `hb : b (2s) = b 0 + 2π` expresses that the last gap ends at
the first boundary shifted by a full turn (the wrap).  (In the application
`b (2j) = x_j − δ`, `b (2j+1) = x_j + δ` for the spike directions `x_j` of
`Submission.DirCycle.dirList`, `δ` the window half-width of
`Submission.E2bParam.exists_delta`, and `u j = log(ℓ_j + margin)` above the
spike tips.)

Per-cell zeros are hypotheses (`hwin`, `hgap`: each cell is star-free and the
rectangle Cauchy identity of `Submission.PolyaShell` /
`Submission.Fold.gap_cell_zero` / `Submission.TipCell` supplies them); the
interval-additivity gluing facts (`hBint` — the `2s` consecutive B-arcs tile
the full circle, `hRint/hRintB/hRint' /hRintB'` — the radial sides at each
window edge split at `u j`) are also hypotheses (automatic for continuous
`pull h`).  The algebra (see the s = 1 proof for the exact pattern):

1. Sum the cell zeros over `j < s`; expand every `cellExpr` (two radial
   sides + two arcs).  The sum splits as
   `radial + (B-arcs) − (tip caps) − (gap arcs) = 0` where
   `B-arcs = Σ_j [I arc(B, b(2j), b(2j+1)) + I arc(B, b(2j+1), b(2j+2))]`.
2. The `2s` B-arc pieces are consecutive, so by
   `Submission.Fold.smul_arc_sum_range_b` (with `t k := b k`, `n := 2s`)
   `B-arcs = I • arcInt (pull h) B (b 0) (b (2s))`, which by `hb` and
   `Submission.E2bCore.circle_eq_arc_window` is exactly `∮_{C(0,e^B)} h`.
3. The radial sum telescopes (shared boundaries between adjacent cells
   cancel on their overlap; the leftover is the segment `[A, u j]` at each
   window edge; the outer edge at `b (2s)` wraps to `b 0` by `hb` +
   `radInt_add_two_pi`) to
   `− Σ_j [radInt(pull h) A (u j) (b (2j)) − radInt(pull h) A (u j) (b (2j+1))]`.
4. Rearrange with `ring`/`linear_combination` over `ℂ` (the s = 1 proof
   does exactly this; here it is done per-`j` with `Finset.sum` bookkeeping
   and parity reindexing `2(j+1) = 2j + 2`, `b (2s) = b 0 + 2π`).
-/

noncomputable section
open scoped Complex Real Interval BigOperators
open Complex
open MeasureTheory
open Submission.Fold

namespace Submission.E2bT

/-- Parity split of a sum over `2n` indices into even and odd parts:
`Σ_{j<n} f(2j) + Σ_{j<n} f(2j+1) = Σ_{k<2n} f k`. -/
lemma sum_range_even_odd (f : ℕ → ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range n, f (2 * j)) + (∑ j ∈ Finset.range n, f (2 * j + 1)) =
      ∑ k ∈ Finset.range (2 * n), f k := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (∑ x ∈ Finset.range (n + 1), f (2 * x)) + (∑ x ∈ Finset.range (n + 1), f (2 * x + 1))
            = ((∑ x ∈ Finset.range n, f (2 * x)) + f (2 * n)) +
              ((∑ x ∈ Finset.range n, f (2 * x + 1)) + f (2 * n + 1)) := by
              rw [Finset.sum_range_succ, Finset.sum_range_succ]
        _ = (∑ x ∈ Finset.range n, f (2 * x)) + (∑ x ∈ Finset.range n, f (2 * x + 1))
              + f (2 * n) + f (2 * n + 1) := by abel
        _ = (∑ k ∈ Finset.range (2 * n), f k) + f (2 * n) + f (2 * n + 1) := by
              rw [ih]
        _ = ∑ k ∈ Finset.range (2 * (n + 1)), f k := by
              rw [show 2 * (n + 1) = 2 * n + 2 by omega]
              have h1 : 2 * n + 2 = (2 * n + 1) + 1 := by omega
              rw [h1]
              rw [Finset.sum_range_succ]
              rw [Finset.sum_range_succ]

/-- A cyclic shift of the even-indexed terms of a periodic sequence:
if `b (2s) = b 0 + 2π` and `g` is `2π`-periodic, then
`Σ_{j<s} g(b(2j)) = Σ_{j<s} g(b(2j+2))`. -/
lemma sum_range_even_shift_wrap (g : ℝ → ℂ) (s : ℕ) (b : ℕ → ℝ)
    (hb : b (2 * s) = b 0 + 2 * Real.pi)
    (hper : ∀ c : ℝ, g (c + 2 * Real.pi) = g c) :
    (∑ j ∈ Finset.range s, g (b (2 * j))) = (∑ j ∈ Finset.range s, g (b (2 * j + 2))) := by
  let f : ℕ → ℂ := fun j => g (b (2 * j))
  have hper0 : g (b (2 * s)) = g (b 0) := by
    rw [hb]
    exact hper (b 0)
  have htel : (∑ j ∈ Finset.range s, (f j - f (j + 1))) = 0 := by
    rw [Finset.sum_range_sub']
    simp [f]
    rw [hper0]
    ring
  have hsub : (∑ j ∈ Finset.range s, g (b (2 * j))) =
      (∑ j ∈ Finset.range s, g (b (2 * (j + 1)))) := by
    have htel' : (∑ j ∈ Finset.range s, (g (b (2 * j)) - g (b (2 * (j + 1))))) = 0 := by
      simpa [f] using htel
    rw [Finset.sum_sub_distrib] at htel'
    exact sub_eq_zero.mp htel'
  rw [hsub]
  apply Finset.sum_congr rfl
  intro j hj
  have hnat : 2 * (j + 1) = 2 * j + 2 := by omega
  rw [hnat]

/-- **General-s deformation identity (algebra).**  If every window cell
(`[u j, B] × (b(2j), b(2j+1))`) and every gap cell
(`[A, B] × (b(2j+1), b(2j+2))`) of the cyclic boundary configuration has
zero boundary integral (`hwin`, `hgap`) and the arc/radial gluing
integrability facts hold, then the big-circle integral of `h` equals the sum
over the tip caps, the base gap arcs and the radial sides of the ε-contour
hugging the `s` spikes. -/
theorem circle_eq_cap_sum (h : ℂ → ℂ) (s : ℕ) (hs : 1 ≤ s) (A B : ℝ) (b u : ℕ → ℝ)
    (hb : b (2 * s) = b 0 + 2 * Real.pi)
    (hBint : ∀ k : ℕ, k < 2 * s → IntervalIntegrable
      (fun y : ℝ => Submission.E2bCore.pull h (B + y * Complex.I)) volume (b k) (b (k + 1)))
    (hRint : ∀ j : ℕ, j < s → IntervalIntegrable
      (fun t : ℝ => Submission.E2bCore.pull h (t + (b (2 * j) : ℂ) * Complex.I)) volume A (u j))
    (hRintB : ∀ j : ℕ, j < s → IntervalIntegrable
      (fun t : ℝ => Submission.E2bCore.pull h (t + (b (2 * j) : ℂ) * Complex.I)) volume (u j) B)
    (hRint' : ∀ j : ℕ, j < s → IntervalIntegrable
      (fun t : ℝ => Submission.E2bCore.pull h (t + (b (2 * j + 1) : ℂ) * Complex.I)) volume A (u j))
    (hRintB' : ∀ j : ℕ, j < s → IntervalIntegrable
      (fun t : ℝ => Submission.E2bCore.pull h (t + (b (2 * j + 1) : ℂ) * Complex.I)) volume (u j) B)
    (hwin : ∀ j : ℕ, j < s →
      cellExpr (Submission.E2bCore.pull h) (u j) B (b (2 * j)) (b (2 * j + 1)) = 0)
    (hgap : ∀ j : ℕ, j < s →
      cellExpr (Submission.E2bCore.pull h) A B (b (2 * j + 1)) (b (2 * j + 2)) = 0) :
    (∮ z in C((0 : ℂ), Real.exp B), h z) =
      (∑ j ∈ Finset.range s,
        Complex.I • arcInt (Submission.E2bCore.pull h) (u j) (b (2 * j)) (b (2 * j + 1)))
        + (∑ j ∈ Finset.range s,
        Complex.I • arcInt (Submission.E2bCore.pull h) A (b (2 * j + 1)) (b (2 * j + 2)))
        + (∑ j ∈ Finset.range s,
        radInt (Submission.E2bCore.pull h) A (u j) (b (2 * j)))
        - (∑ j ∈ Finset.range s,
        radInt (Submission.E2bCore.pull h) A (u j) (b (2 * j + 1))) := by
  classical
  let F : ℂ → ℂ := Submission.E2bCore.pull h
  let X : ℂ := ∑ j ∈ Finset.range s, radInt F (u j) B (b (2 * j))
  let Y : ℂ := ∑ j ∈ Finset.range s, radInt F (u j) B (b (2 * j + 1))
  let C0 : ℂ := ∑ j ∈ Finset.range s, radInt F A B (b (2 * j + 1))
  let D : ℂ := ∑ j ∈ Finset.range s, radInt F A B (b (2 * j + 2))
  let AE : ℂ := ∑ j ∈ Finset.range s, radInt F A B (b (2 * j))
  let aBwin : ℂ := ∑ j ∈ Finset.range s, Complex.I • arcInt F B (b (2 * j)) (b (2 * j + 1))
  let aBgap : ℂ := ∑ j ∈ Finset.range s, Complex.I • arcInt F B (b (2 * j + 1)) (b (2 * j + 2))
  let tCap : ℂ := ∑ j ∈ Finset.range s, Complex.I • arcInt F (u j) (b (2 * j)) (b (2 * j + 1))
  let bGap : ℂ := ∑ j ∈ Finset.range s, Complex.I • arcInt F A (b (2 * j + 1)) (b (2 * j + 2))
  let E : ℂ := ∑ j ∈ Finset.range s, radInt F A (u j) (b (2 * j))
  let O : ℂ := ∑ j ∈ Finset.range s, radInt F A (u j) (b (2 * j + 1))
  let Big : ℂ := Complex.I • arcInt F B (b 0) (b (2 * s))
  -- integrability facts in F
  have hBintF : ∀ k : ℕ, k < 2 * s → IntervalIntegrable
      (fun y : ℝ => F (B + y * Complex.I)) volume (b k) (b (k + 1)) := by
    intro k hk
    simpa [F] using hBint k hk
  -- radial glues at each even angle b(2j)
  have glueE : ∀ j : ℕ, j < s →
      radInt F A (u j) (b (2 * j)) + radInt F (u j) B (b (2 * j)) = radInt F A B (b (2 * j)) := by
    intro j hj
    unfold radInt
    simpa [F] using (intervalIntegral.integral_add_adjacent_intervals (hRint j hj) (hRintB j hj))
  have substE : ∀ j : ℕ, j < s →
      radInt F (u j) B (b (2 * j)) = radInt F A B (b (2 * j)) - radInt F A (u j) (b (2 * j)) := by
    intro j hj
    rw [← glueE j hj]
    abel
  -- radial glues at each odd angle b(2j+1)
  have glueO : ∀ j : ℕ, j < s →
      radInt F A (u j) (b (2 * j + 1)) + radInt F (u j) B (b (2 * j + 1)) =
        radInt F A B (b (2 * j + 1)) := by
    intro j hj
    unfold radInt
    simpa [F] using (intervalIntegral.integral_add_adjacent_intervals (hRint' j hj) (hRintB' j hj))
  have substO : ∀ j : ℕ, j < s →
      radInt F (u j) B (b (2 * j + 1)) = radInt F A B (b (2 * j + 1)) - radInt F A (u j) (b (2 * j + 1)) := by
    intro j hj
    rw [← glueO j hj]
    abel
  -- X = AE - E and Y = C0 - O
  have hX : X = AE - E := by
    dsimp [X, AE, E]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact substE j (Finset.mem_range.mp hj)
  have hY : Y = C0 - O := by
    dsimp [Y, C0, O]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact substO j (Finset.mem_range.mp hj)
  -- cyclic identity AE = D (wrap)
  have hcycl : AE = D := by
    dsimp [AE, D]
    exact sum_range_even_shift_wrap (g := fun c : ℝ => radInt F A B c) s b hb (by
      intro c
      simpa [F, radInt, Submission.E2bCore.radInt] using
        (Submission.E2bCore.radInt_add_two_pi h A B c))
  -- radial telescoping: (X-Y)+(C0-D) = -E + O
  have hRad : (X - Y) + (C0 - D) = -E + O := by
    rw [hX, hY]
    rw [← hcycl]
    abel
  -- the 2s B-arcs combine into the full-window B-arc
  have hBarcs : aBwin + aBgap = Big := by
    dsimp [aBwin, aBgap, Big]
    calc
      (∑ j ∈ Finset.range s, Complex.I • arcInt F B (b (2 * j)) (b (2 * j + 1))) +
          (∑ j ∈ Finset.range s, Complex.I • arcInt F B (b (2 * j + 1)) (b (2 * j + 2)))
          = ∑ k ∈ Finset.range (2 * s),
            Complex.I • arcInt F B (b k) (b (k + 1)) := by
            let g : ℕ → ℂ := fun k => Complex.I • arcInt F B (b k) (b (k + 1))
            have hpar := sum_range_even_odd g s
            have h1 : (∑ j ∈ Finset.range s, Complex.I • arcInt F B (b (2 * j)) (b (2 * j + 1)))
                = ∑ j ∈ Finset.range s, g (2 * j) := by
              apply Finset.sum_congr rfl
              intro j hj
              rfl
            have h2 : (∑ j ∈ Finset.range s, Complex.I • arcInt F B (b (2 * j + 1)) (b (2 * j + 2)))
                = ∑ j ∈ Finset.range s, g (2 * j + 1) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hnat : (2 * j + 1) + 1 = 2 * j + 2 := by omega
              rw [← hnat]
            rw [h1, h2]
            simpa [g] using hpar
      _ = Big := by
            dsimp [Big]
            simpa [arcInt] using (smul_arc_sum_range_b F B b (2 * s) hBintF)
  -- expand the two sum-of-cells identities
  have hsum0 : (∑ j ∈ Finset.range s, cellExpr F (u j) B (b (2 * j)) (b (2 * j + 1))) +
      (∑ j ∈ Finset.range s, cellExpr F A B (b (2 * j + 1)) (b (2 * j + 2))) = 0 := by
    have hw : (∑ j ∈ Finset.range s, cellExpr F (u j) B (b (2 * j)) (b (2 * j + 1))) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simpa [F] using hwin j (Finset.mem_range.mp hj)
    have hg : (∑ j ∈ Finset.range s, cellExpr F A B (b (2 * j + 1)) (b (2 * j + 2))) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simpa [F] using hgap j (Finset.mem_range.mp hj)
    simp [hw, hg]
  have hW : (∑ j ∈ Finset.range s, cellExpr F (u j) B (b (2 * j)) (b (2 * j + 1))) =
      X - Y + aBwin - tCap := by
    unfold cellExpr
    simp [X, Y, aBwin, tCap, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hG : (∑ j ∈ Finset.range s, cellExpr F A B (b (2 * j + 1)) (b (2 * j + 2))) =
      C0 - D + aBgap - bGap := by
    unfold cellExpr
    simp [C0, D, aBgap, bGap, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hsumExp : (X - Y + aBwin - tCap) + (C0 - D + aBgap - bGap) = 0 := by
    rw [← hW, ← hG]
    exact hsum0
  -- assemble
  have hA : aBwin + aBgap = tCap + bGap - (X - Y) - (C0 - D) := by
    linear_combination hsumExp
  have hB : tCap + bGap - (X - Y) - (C0 - D) = tCap + bGap + E - O := by
    calc
      tCap + bGap - (X - Y) - (C0 - D) = tCap + bGap - ((X - Y) + (C0 - D)) := by ring
      _ = tCap + bGap - (-E + O) := by rw [hRad]
      _ = tCap + bGap + E - O := by ring
  have hMain : Big = tCap + bGap + E - O := by
    calc
      Big = aBwin + aBgap := by rw [hBarcs]
      _ = tCap + bGap + E - O := by
            calc
              aBwin + aBgap = tCap + bGap - (X - Y) - (C0 - D) := hA
              _ = tCap + bGap + E - O := hB
  -- circle integral equals Big
  have hcircle : (∮ z in C((0 : ℂ), Real.exp B), h z) = Big := by
    dsimp [Big, F]
    rw [hb]
    simpa [arcInt, Submission.E2bCore.arcInt] using
      (Submission.E2bCore.circle_eq_arc_window h B (b 0))
  calc
    (∮ z in C((0 : ℂ), Real.exp B), h z) = Big := hcircle
    _ = tCap + bGap + E - O := hMain
    _ = (∑ j ∈ Finset.range s,
        Complex.I • arcInt (Submission.E2bCore.pull h) (u j) (b (2 * j)) (b (2 * j + 1)))
        + (∑ j ∈ Finset.range s,
        Complex.I • arcInt (Submission.E2bCore.pull h) A (b (2 * j + 1)) (b (2 * j + 2)))
        + (∑ j ∈ Finset.range s,
        radInt (Submission.E2bCore.pull h) A (u j) (b (2 * j)))
        - (∑ j ∈ Finset.range s,
        radInt (Submission.E2bCore.pull h) A (u j) (b (2 * j + 1))) := by
      dsimp [tCap, bGap, E, O, F]

end Submission.E2bT

end
