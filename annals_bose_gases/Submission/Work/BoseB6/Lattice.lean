import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB6.lattice_sum_abs_le
import Submission.Work.BoseB6.lhyValue_eight_pi
import Submission.Work.BoseB6.rpow_five_halves_eq
import Submission.Work.BoseB6.zeroPoint_fs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6 — the mode-lattice Riemann sum and the sharp constant `128/(15√π)`

This is node B6's analytic conclusion: the *mode-lattice sum* of the Bogoliubov
bracket converges to the model integral `−lhyValue 8π = −64π⁴·(128/(15√π))`, with
the explicit error `latticeMeshErr` (`= Work.BoseBox.latticeErr`), and the
resulting FS normalisation

  `−½·(ρ_z a)·Σ_k bracket(t_k) ≥ 4π·(128/(15√π))·ρ_z²a√(ρ_z a³)·ℓ³ − error`,

i.e. FS `eq:BogIntegral`'s leading term, with the zero-point sum evaluated on the
mode lattice instead of the continuum integral.

Contents (all deduced from the delivered pieces):
* `lattice_sum_lower`, `lattice_sum_upper` — the one-sided Riemann bounds;
* `lattice_model_sharp` — the dimensionless sharp-constant form;
* `tendsto_latticeMeshErr`, `tendsto_lattice_sum` — the error vanishes and the
  lattice sum *converges* to `−lhyValue c`;
* `zeroPoint_fs_sharp` — the FS-normalised, fully instantiated zero-point bound.

The mesh convention: `meshD n = 2π/(n+1)` is FS's dimensionless mode-lattice
mesh `2π/(ℓ√(ρ_z a))`; the hypothesis `(n:ℝ)+1 = ℓ√(ρ_z a)` of
`zeroPoint_fs_sharp` says exactly that the physical box side `ℓ` and the
dimensionless refinement index `n` match, so that `δ³·Σ_k` is the Riemann
approximation of `∫_{ℝ³}` in the dimensionless variables.
-/

noncomputable section

open MeasureTheory Filter
open scoped Real BigOperators Topology

namespace Work.BoseB6

/-! ## 1. The quantitative lattice bound -/

/-- **The lattice Riemann sum with explicit error** (two-sided): the mode-lattice
sum of the Bogoliubov bracket differs from `−lhyValue c` by at most
`latticeMeshErr c n`. -/
theorem lattice_sum_value {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    |(meshD n) ^ 3 * latticeSum c n + lhyValue c| ≤ latticeMeshErr c n :=
  lattice_sum_abs_le hc hn

/-- One-sided (lower) Riemann bound. -/
theorem lattice_sum_lower {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    -lhyValue c - latticeMeshErr c n ≤ (meshD n) ^ 3 * latticeSum c n := by
  have h := abs_le.mp (lattice_sum_value hc hn)
  linarith [h.1]

/-- One-sided (upper) Riemann bound. -/
theorem lattice_sum_upper {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    (meshD n) ^ 3 * latticeSum c n ≤ -lhyValue c + latticeMeshErr c n := by
  have h := abs_le.mp (lattice_sum_value hc hn)
  linarith [h.2]

/-- **The zero-point term at the model value** (dimensionless): the Bogoliubov
zero-point `−½δ³Σ_k bracket` is bounded below by `½(lhyValue c − error)`. -/
theorem lattice_zeroPoint_model {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    (1 / 2) * (lhyValue c - latticeMeshErr c n) ≤ -(1 / 2) * ((meshD n) ^ 3 * latticeSum c n) := by
  have h := lattice_sum_upper hc hn
  linarith

/-- **The sharp constant at `c = 8π`**: `−½δ³Σ_k bracket ≥ ½(64π⁴·128/(15√π) − error)`. -/
theorem lattice_model_sharp {n : ℕ} (hn : 1 ≤ n) :
    (1 / 2) * (64 * Real.pi ^ 4 * lhySharp - latticeMeshErr (8 * Real.pi) n) ≤
      -(1 / 2) * ((meshD n) ^ 3 * latticeSum (8 * Real.pi) n) := by
  have h := lattice_zeroPoint_model (by positivity : (0 : ℝ) < 8 * Real.pi) hn
  rw [lhyValue_eight_pi] at h
  exact h

/-! ## 2. Convergence of the lattice sum -/

/-- `meshD n = 2π/(n+1)` is the corpus's `Work.BoseBox.mesh`. -/
lemma meshD_eq (n : ℕ) : meshD n = Work.BoseBox.mesh n := rfl

/-- `gridD n = (n+1)²` is the corpus's `Work.BoseBox.gridN`. -/
lemma gridD_eq (n : ℕ) : gridD n = Work.BoseBox.gridN n := rfl

/-- The explicit error vanishes as the lattice is refined. -/
theorem tendsto_latticeMeshErr {c : ℝ} : Tendsto (latticeMeshErr c) atTop (nhds 0) := by
  have h := Work.BoseBox.tendsto_latticeErr (c := c)
  have hfun : latticeMeshErr c = Work.BoseBox.latticeErr c := by
    funext n
    simp only [latticeMeshErr, Work.BoseBox.latticeErr, meshD, gridD, Work.BoseBox.mesh,
      Work.BoseBox.gridN]
  rw [hfun]
  exact h

/-- **The lattice Riemann sum converges to the model integral**: for `c > 0`,
`δ³Σ_k bracket(t_k) → −lhyValue c = −c^{5/2}·64π/(15√2)` as the lattice is refined
(with the explicit error `latticeMeshErr c n`). -/
theorem tendsto_lattice_sum {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (meshD n) ^ 3 * latticeSum c n) atTop (nhds (-lhyValue c)) := by
  have habs : Tendsto (fun n : ℕ => |(meshD n) ^ 3 * latticeSum c n + lhyValue c|) atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ (tendsto_latticeMeshErr (c := c))
    · exact Eventually.of_forall fun n => abs_nonneg _
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact lattice_sum_value hc hn
  have hf : Tendsto (fun n : ℕ => (meshD n) ^ 3 * latticeSum c n + lhyValue c) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using habs
  have h2 := hf.sub_const (lhyValue c)
  simpa using h2

/-! ## 3. The FS-normalised zero-point bound -/

/-- **FS `eq:BogIntegral`'s zero-point term, fully instantiated.**  With
`ρ_z, a, ℓ > 0` and the refinement index `n` matched to the physical box by
`(n:ℝ)+1 = ℓ√(ρ_z a)` (so that `meshD n = 2π/(ℓ√(ρ_z a))` is the dimensionless
mode-lattice mesh), the zero-point sum of the Bogoliubov Hamiltonian dominates
the LHY correction `4π·(128/(15√π))·ρ_z²a√(ρ_z a³)·ℓ³` up to the explicit lattice
error:

  `−½(ρ_z a)Σ_k bracket ≥ 4π·lhySharp·(ρ_z a)^{5/2}ℓ³ − ½(2π)⁻³ℓ³(ρ_z a)^{5/2}·error`. -/
theorem zeroPoint_fs_sharp {ρz a ℓ : ℝ} (hρz : 0 < ρz) (ha : 0 < a) (hℓ : 0 < ℓ) {n : ℕ}
    (hn : 1 ≤ n) (hrel : (n : ℝ) + 1 = ℓ * Real.sqrt (ρz * a)) :
    -(1 / 2) * (ρz * a) * latticeSum (8 * Real.pi) n
      ≥ 4 * Real.pi * lhySharp * (ρz * a) ^ (5 / 2 : ℝ) * ℓ ^ 3
        - (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * (ρz * a) ^ (5 / 2 : ℝ) * ℓ ^ 3 *
            latticeMeshErr (8 * Real.pi) n := by
  have hconst : (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * lhyValue (8 * Real.pi) =
      4 * Real.pi * lhySharp := by
    rw [lhyValue_eight_pi]
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  exact zeroPoint_fs hρz ha hℓ hn hrel hconst
    (lattice_sum_abs_le (by positivity : (0 : ℝ) < 8 * Real.pi) hn)


/-! ## 4. FS's literal form and the sign of the error -/

/-- The lattice error is nonnegative. -/
theorem latticeMeshErr_nonneg {c : ℝ} (hc : 0 ≤ c) (n : ℕ) : 0 ≤ latticeMeshErr c n := by
  have hmesh : 0 ≤ meshD n := by
    unfold meshD
    positivity
  have hg : (1 : ℝ) ≤ gridD n := by
    have h : (1 : ℕ) ≤ gridD n := by
      unfold gridD
      nlinarith [Nat.succ_pos n]
    exact_mod_cast h
  have hlog : 0 ≤ Real.log (gridD n) := Real.log_nonneg hg
  unfold latticeMeshErr
  have h1 : 0 ≤ 512 * Real.pi * Real.sqrt 3 * c * (meshD n) ^ 3 := by positivity
  have h2 : 0 ≤ 520 * Real.pi * Real.sqrt 3 * c ^ 2 * (meshD n) := by positivity
  have h3 : 0 ≤ 128 * Real.pi * Real.sqrt 3 * c ^ 2 * (meshD n) * Real.log (gridD n) := by
    have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hc2) hmesh) hlog
  have h4 : 0 ≤ 4 * c ^ 3 / ((n : ℝ) + 1) := by positivity
  linarith

/-- **FS's literal coefficient `ρ_z²a√(ρ_z a³)`**: `zeroPoint_fs_sharp` with
`(ρ_z a)^{5/2}` written as `ρ_z²a√(ρ_z a³)` (FS `eq:BogIntegral`'s coefficient). -/
theorem zeroPoint_fs_sharp_sqrt {ρz a ℓ : ℝ} (hρz : 0 < ρz) (ha : 0 < a) (hℓ : 0 < ℓ)
    {n : ℕ} (hn : 1 ≤ n) (hrel : (n : ℝ) + 1 = ℓ * Real.sqrt (ρz * a)) :
    -(1 / 2) * (ρz * a) * latticeSum (8 * Real.pi) n
      ≥ 4 * Real.pi * lhySharp * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3)) * ℓ ^ 3
        - (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * (ρz ^ 2 * a * Real.sqrt (ρz * a ^ 3)) * ℓ ^ 3 *
            latticeMeshErr (8 * Real.pi) n := by
  have h := zeroPoint_fs_sharp hρz ha hℓ hn hrel
  rw [rpow_five_halves_eq hρz ha] at h
  exact h

end Work.BoseB6
