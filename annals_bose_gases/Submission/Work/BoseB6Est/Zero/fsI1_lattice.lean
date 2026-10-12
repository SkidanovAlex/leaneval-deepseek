import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseB6Est.fsI1_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est, zero-point layer — `fsI1_lattice`

The `I₁` (Bogoliubov zero-point) Lebesgue estimate `fsI1_le` bounds `fsI1` by the
*continuum* model value `−lhyValue (8π)` plus FS's error `10⁶·ε(μ,ρ_z)`.  The
zero-point layer of the small-box programme uses the *mode-lattice* sum
`δ³·Σ_k bracket(t_k)` instead, which by the Riemann comparison
`Work.BoseB6.latticeMeshErr` differs from the continuum value by at most
`latticeMeshErr (8π) n`.

This file performs the (cheap) comparison: since `ε(μ,ρ_z) ≥ 1` and the lattice
error is bounded by an absolute constant, the two error terms absorb one another
against the huge prefactor `10¹⁰·(2π)³` on the zero-point side.

Contents:
* `latticeMeshErr_eight_pi_le` — the crude absolute bound
  `latticeMeshErr (8π) n ≤ 10⁹` for `n ≥ 1` (every term of `latticeMeshErr` is
  `O(1)`: `meshD n = 2π/(n+1) ≤ π` and
  `meshD n · log (gridD n) ≤ 4π` since `log (n+1) ≤ n+1`);
* `fsI1_lattice` — the requested statement.
-/

namespace Work.BoseB6Est.Zero

/-- **The lattice Riemann error at the model value is absolutely bounded.**
`latticeMeshErr c n` is the explicit Riemann error of the mode-lattice
approximation of the Bogoliubov integral.  At `c = 8π` and `n ≥ 1` it is at most
the absolute constant `10⁹`: with `δ = 2π/(n+1) ≤ π`, `√3 ≤ 2`, `π ≤ 3.15`,
`δ·log (gridD n) = δ·2log(n+1) ≤ 4π` and `(n:ℝ)+1 ≥ 2`, the four terms of
`latticeMeshErr` are bounded by `2.8·10⁶`, `7.0·10⁶`, `6.9·10⁶` and `3.3·10⁴`
respectively. -/
lemma latticeMeshErr_eight_pi_le {n : ℕ} (hn : 1 ≤ n) :
    Work.BoseB6.latticeMeshErr (8 * Real.pi) n ≤ 10 ^ 9 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hden2 : (2 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπ : Real.pi ≤ 3.15 := le_of_lt Real.pi_lt_d2
  have hs3 : Real.sqrt 3 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hδ0 : (0 : ℝ) ≤ Work.BoseB6.meshD n := by
    simp only [Work.BoseB6.meshD]; positivity
  have hδ : Work.BoseB6.meshD n ≤ Real.pi := by
    simp only [Work.BoseB6.meshD]
    rw [div_le_iff₀ hden]
    nlinarith [hπ0, hn1]
  have hgrid : ((Work.BoseB6.gridD n : ℕ) : ℝ) = ((n : ℝ) + 1) ^ 2 := by
    simp only [Work.BoseB6.gridD]; push_cast; ring
  -- `log (gridD n) = 2 log (n+1) ≤ 2 (n+1)`
  have hlog : Real.log ((Work.BoseB6.gridD n : ℕ) : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    rw [hgrid, Real.log_pow]
    have h3 := Real.log_le_sub_one_of_pos hden
    push_cast
    linarith
  -- `δ · log (gridD n) ≤ 4π`
  have hδlog : Work.BoseB6.meshD n * Real.log ((Work.BoseB6.gridD n : ℕ) : ℝ)
      ≤ 4 * Real.pi := by
    have h1 := mul_le_mul_of_nonneg_left hlog hδ0
    have h2 : Work.BoseB6.meshD n * (2 * ((n : ℝ) + 1)) = 4 * Real.pi := by
      simp only [Work.BoseB6.meshD]; field_simp; ring
    linarith [h1, h2.ge]
  -- the four terms of `latticeMeshErr (8π) n`, each ≤ 10⁸
  have hT1 : 512 * Real.pi * Real.sqrt 3 * (8 * Real.pi) * (Work.BoseB6.meshD n) ^ 3
      ≤ (10 : ℝ) ^ 8 := by
    have hmain : 512 * Real.pi * Real.sqrt 3 * (8 * Real.pi) * (Work.BoseB6.meshD n) ^ 3
        ≤ 512 * 3.15 * 2 * (8 * 3.15) * (3.15 : ℝ) ^ 3 := by
      gcongr
      try linarith
    norm_num at hmain
    linarith [hmain]
  have hT2 : 520 * Real.pi * Real.sqrt 3 * (8 * Real.pi) ^ 2 * (Work.BoseB6.meshD n)
      ≤ (10 : ℝ) ^ 8 := by
    have hmain : 520 * Real.pi * Real.sqrt 3 * (8 * Real.pi) ^ 2 * (Work.BoseB6.meshD n)
        ≤ 520 * 3.15 * 2 * (8 * 3.15) ^ 2 * 3.15 := by
      gcongr
      try linarith
    norm_num at hmain
    linarith [hmain]
  have hT3 : 128 * Real.pi * Real.sqrt 3 * (8 * Real.pi) ^ 2 * (Work.BoseB6.meshD n)
      * Real.log ((Work.BoseB6.gridD n : ℕ) : ℝ) ≤ (10 : ℝ) ^ 8 := by
    rw [show 128 * Real.pi * Real.sqrt 3 * (8 * Real.pi) ^ 2 * (Work.BoseB6.meshD n)
        * Real.log ((Work.BoseB6.gridD n : ℕ) : ℝ)
        = 128 * Real.pi * Real.sqrt 3 * (8 * Real.pi) ^ 2
          * ((Work.BoseB6.meshD n) * Real.log ((Work.BoseB6.gridD n : ℕ) : ℝ)) by ring]
    have hc : 128 * Real.pi * Real.sqrt 3 * (8 * Real.pi) ^ 2
        ≤ 128 * 3.15 * 2 * (8 * 3.15) ^ 2 := by
      gcongr
      try linarith
    have hδl : (Work.BoseB6.meshD n) * Real.log ((Work.BoseB6.gridD n : ℕ) : ℝ)
        ≤ 4 * 3.15 := le_trans hδlog (by linarith [hπ])
    have hmain := mul_le_mul hc hδl (by positivity) (by positivity)
    norm_num at hmain
    linarith [hmain]
  have hT4 : 4 * (8 * Real.pi) ^ 3 / ((n : ℝ) + 1) ≤ (10 : ℝ) ^ 8 := by
    have h1 : 4 * (8 * Real.pi) ^ 3 / ((n : ℝ) + 1) ≤ 4 * (8 * Real.pi) ^ 3 / 2 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden2
    have h2 : 4 * (8 * Real.pi) ^ 3 / 2 ≤ 4 * (8 * 3.15) ^ 3 / 2 := by
      gcongr
    have h3 : (4 * (8 * 3.15) ^ 3 / 2 : ℝ) ≤ 10 ^ 8 := by norm_num
    linarith [h1, h2, h3]
  rw [Work.BoseB6.latticeMeshErr]
  linarith [hT1, hT2, hT3, hT4]

/-- **The `I₁` estimate on the mode lattice.**  Combining the Lebesgue estimate
`fsI1_le` (giving the continuum model value up to FS's error `10⁶·ε`) with the
one-sided Riemann bound `lattice_sum_lower` (which costs the lattice error
`latticeMeshErr (8π) n ≤ 10⁹` by `latticeMeshErr_eight_pi_le`) and the size
`ε ≥ 1` of FS's error, the mode-lattice zero-point sum plus the physical
prefactor `10¹⁰·(2π)³·ε` dominates `fsI1`, with the two error terms absorbed
into the prefactor. -/
theorem fsI1_lattice {n : ℕ} {K : Work.BoseB6Est.FsKernel}
    {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : Work.BoseB6Est.FsI1Regime K a R ρz μ εT c1 c2 Kl s d) (hn : 1 ≤ n)
    (hlat : Work.BoseB6.latticeMeshErr (8 * Real.pi) n
      ≤ 2 * 10 ^ 11 * Work.BoseB6.lhyEps a R εT Kl s d μ) :
    Work.BoseB6Est.fsI1 K εT c1 c2
      ≤ (Work.BoseB6.meshD n) ^ 3 * Work.BoseB6.latticeSum (8 * Real.pi) n
        + 10 ^ 10 * (2 * Real.pi) ^ 3 * Work.BoseB6.lhyEps a R εT Kl s d μ := by
  have hfs := Work.BoseB6Est.fsI1_le h
  have hlat' := Work.BoseB6.lattice_sum_lower (c := 8 * Real.pi) (by positivity) hn
  set E := Work.BoseB6.lhyEps a R εT Kl s d μ with hEdef
  have hE0 : 0 ≤ E := Work.BoseB6Est.FsI1Regime.lhyEps_nonneg h
  have hbig : (10 : ℝ) ^ 6 + 2 * 10 ^ 11 ≤ 10 ^ 10 * (2 * Real.pi) ^ 3 := by
    have hπ : (3.14 : ℝ) ≤ Real.pi := Real.pi_gt_d2.le
    have h3 : (2 * Real.pi) ^ 3 ≥ (6.28 : ℝ) ^ 3 := by
      have h2 : (6.28 : ℝ) ≤ 2 * Real.pi := by linarith
      exact pow_le_pow_left₀ (by norm_num) h2 3
    have h4 : (10 : ℝ) ^ 10 * (6.28 : ℝ) ^ 3 ≥ 10 ^ 6 + 2 * 10 ^ 11 := by norm_num
    linarith [mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 10 ^ 10)]
  have h1 : 10 ^ 6 * E + Work.BoseB6.latticeMeshErr (8 * Real.pi) n
      ≤ 10 ^ 10 * (2 * Real.pi) ^ 3 * E := by
    have h2 : 10 ^ 6 * E + 2 * 10 ^ 11 * E ≤ 10 ^ 10 * (2 * Real.pi) ^ 3 * E := by
      have : (10 : ℝ) ^ 6 * E + 2 * 10 ^ 11 * E = (10 ^ 6 + 2 * 10 ^ 11) * E := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hbig hE0
    linarith [hlat, h2]
  linarith [hfs, hlat', h1]

end Work.BoseB6Est.Zero
