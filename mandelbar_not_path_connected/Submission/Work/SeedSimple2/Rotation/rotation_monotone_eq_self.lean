import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A monotone orbit driven by an integer "carry" cannot stay increasing

We prove that a strictly increasing sequence `x : ℕ → ℝ` which is bounded above
and satisfies an exact recurrence of the form

  `x (n+1) - x n = a * x n + b - m n`,   `m n : ℤ`,  `a > 0`

is impossible.  The point is that the integer part `m n` is forced (by
convergence) to be eventually constant, which pins the limit down and makes the
increments eventually *negative*.

This is the combinatorial heart of the statement that the doubling-type map
`x ↦ 1024 x (mod 1)` (with a fixed additive twist) admits no strictly
increasing, bounded orbit, which is what rules out the extremely monotic
rotation in the Mandelbar argument.
-/

namespace Work.SeedSimple2.Rotation

set_option linter.unusedVariables false

open Filter
open scoped Topology

/-- A convergent sequence of reals all of whose values are integers is
eventually constant. -/
theorem tendsto_int_eventually_const {m : ℕ → ℤ} {r : ℝ}
    (h : Tendsto (fun n => (m n : ℝ)) atTop (𝓝 r)) :
    ∃ N, ∀ n ≥ N, m n = m N := by
  rcases (Metric.tendsto_atTop.mp h) (1 / 2) (by norm_num) with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  have h2 := hN N le_rfl
  rw [Real.dist_eq] at h1 h2
  have h3 : |(((m n - m N : ℤ)) : ℝ)| < 1 := by
    rw [Int.cast_sub]
    have key : |(m n : ℝ) - (m N : ℝ)| ≤ |(m n : ℝ) - r| + |r - (m N : ℝ)| := by
      have he : (m n : ℝ) - (m N : ℝ) = ((m n : ℝ) - r) + (r - (m N : ℝ)) := by ring
      rw [he]; exact abs_add_le _ _
    have hr : |r - (m N : ℝ)| = |(m N : ℝ) - r| := abs_sub_comm _ _
    linarith
  have h4 : |m n - m N| < (1 : ℤ) := by
    have hh : (((|m n - m N| : ℤ)) : ℝ) < 1 := by rw [Int.cast_abs]; exact h3
    exact_mod_cast hh
  exact sub_eq_zero.mp (Int.abs_lt_one_iff.mp h4)

/-- No strictly increasing, bounded above real sequence can satisfy
`x (n+1) - x n = a * x n + b - m n` with `m n` integer and `a > 0`. -/
theorem no_strict_increasing_int_orbit {x : ℕ → ℝ} {m : ℕ → ℤ} {a b : ℝ} (ha : 0 < a)
    (hineq : ∀ n, x (n + 1) - x n = a * x n + b - (m n : ℝ))
    (hinc : ∀ n, x n < x (n + 1))
    (hbdd : ∃ B, ∀ n, x n ≤ B) : False := by
  have hstrict : StrictMono x := strictMono_nat_of_lt_succ hinc
  obtain ⟨B, hB⟩ := hbdd
  have hbdd' : BddAbove (Set.range x) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hB n⟩
  set L : ℝ := ⨆ n, x n with hL
  have hxlim : Tendsto x atTop (𝓝 L) := by
    rw [hL]; exact tendsto_atTop_ciSup hstrict.monotone hbdd'
  have hxle : ∀ n, x n ≤ L := fun n => by rw [hL]; exact le_ciSup hbdd' n
  have hxlt : ∀ n, x n < L := fun n => lt_of_lt_of_le (hinc n) (hxle (n + 1))
  have hshift : Tendsto (fun n => x (n + 1)) atTop (𝓝 L) :=
    hxlim.comp (tendsto_add_atTop_nat 1)
  have heps : Tendsto (fun n => x (n + 1) - x n) atTop (𝓝 0) := by
    have h := hshift.sub hxlim
    simpa using h
  have hm : Tendsto (fun n => (m n : ℝ)) atTop (𝓝 (a * L + b)) := by
    have hfun : (fun n => (m n : ℝ)) = fun n => a * x n + b - (x (n + 1) - x n) := by
      funext n; have h' := hineq n; linarith
    rw [hfun]
    have hb : Tendsto (fun _ : ℕ => b) atTop (𝓝 b) := tendsto_const_nhds
    have h := ((hxlim.const_mul a).add hb).sub heps
    simpa using h
  obtain ⟨N, hN⟩ := tendsto_int_eventually_const hm
  have hconst : Tendsto (fun n => (m n : ℝ)) atTop (𝓝 (m N : ℝ)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    exact ⟨N, fun n hn => by rw [hN n hn, dist_self]; exact hε⟩
  have h3 : (m N : ℝ) = a * L + b := (tendsto_nhds_unique hm hconst).symm
  have h4 : x (N + 1) - x N = a * (x N - L) := by
    have h' := hineq N
    rw [h3] at h'
    linarith
  have h5 : a * (x N - L) < 0 := mul_neg_of_pos_of_neg ha (by linarith [hxlt N])
  have h6 : 0 < x (N + 1) - x N := by linarith [hinc N]
  linarith

/-- The requested lemma: a strictly increasing `1024`-orbit of fractional parts,
all lying in an interval of length `≤ 1`, cannot exist. -/
theorem rotation_monotone_eq_self {c0 d0 α θ : ℝ} (hcd : d0 ≤ c0 + 1)
    (harc : ∀ n : ℕ, Int.fract ((1024 : ℝ) ^ n * θ - α) ∈ Set.Ioo c0 d0)
    (hmono : ∀ n : ℕ, Int.fract ((1024 : ℝ) ^ n * θ - α)
      < Int.fract ((1024 : ℝ) ^ (n + 1) * θ - α)) : False := by
  refine no_strict_increasing_int_orbit (x := fun n => Int.fract ((1024 : ℝ) ^ n * θ - α))
    (m := fun n => ⌊(1024 : ℝ) ^ (n + 1) * θ - α⌋
      - (1024 : ℤ) * ⌊(1024 : ℝ) ^ n * θ - α⌋)
    (a := 1023) (b := 1023 * α) (by norm_num) ?_ ?_ ?_
  · intro n
    have h4 : (1024 : ℝ) ^ (n + 1) * θ - α
        = 1024 * ((1024 : ℝ) ^ n * θ - α) + 1023 * α := by
      rw [pow_succ]; ring
    have h1 : Int.fract ((1024 : ℝ) ^ (n + 1) * θ - α)
        = ((1024 : ℝ) ^ (n + 1) * θ - α) - (⌊(1024 : ℝ) ^ (n + 1) * θ - α⌋ : ℝ) := rfl
    have h2 : Int.fract ((1024 : ℝ) ^ n * θ - α)
        = ((1024 : ℝ) ^ n * θ - α) - (⌊(1024 : ℝ) ^ n * θ - α⌋ : ℝ) := rfl
    rw [h1, h2]
    push_cast
    linarith [h4]
  · exact hmono
  · exact ⟨d0, fun n => (harc n).2.le⟩

end Work.SeedSimple2.Rotation
