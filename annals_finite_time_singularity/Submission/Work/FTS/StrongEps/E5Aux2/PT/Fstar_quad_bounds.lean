import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.RXR5L.L12fAux.L12f_C1Jet_hsupp_unsat
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.Spaces.c_bounds
import Submission.Work.FM.Core
import Submission.Work.FTS.StrongEps.E5Aux2.FstarSlotBounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- `open scoped Real` is needed for the notation `π` (= `Real.pi`) of the statement below:
-- the workspace sets `autoImplicit = false`, so without this scope `π` is not a name at all.
open scoped Real

namespace Work.FTS.StrongEps.E5Aux2.PT

/-!
# The quadrant bounds for the reference profile `F_*`

`F_*(z,θ) = α (Γ(θ)/c(α)) · 2z/(1+z)²` (`Work.Construction.Fstar α`) is the fixed profile of
Elgindi's self-similar solution.  This module records the three elementary facts about it on
the open quadrant `Q0 = (0,∞) × (0,π/2)`:

* `F_*` is `C²` there (it is `C^∞`, `SmoothQuad_Fstar`);
* `|F_*(z,θ)| ≤ α/c(α)`;
* `|∂_zF_*(z,θ)| ≤ 2α/c(α)`.

## Mathematics

All three are consequences of the separation of variables
`F_* = (2α/c) · Γ ⊗ h`, `h(z) = z/(1+z)²` (`FstarPkg.Fstar_eq_factored`), of the sharp
radial bound `h(z) ≤ 1/4` (the maximum of `z/(1+z)²`, attained at `z = 1`) for `z > 0`, and
of the *global* angular bound `|Γ(θ)| ≤ 1` for every real `θ`.

The last one is what the second and third conjuncts need, and it does **not** need
`θ ∈ Iθ`: the base of the real power is `u(θ) = sinθ cos²θ`, which lies in `[-1,1]` for every
`θ` (both factors are bounded by `1` in absolute value), and for the real power
`|x ^ y| ≤ |x| ^ y ≤ 1` whenever `0 ≤ y` and `|x| ≤ 1`
(`Real.abs_rpow_le_abs_rpow`, `Real.rpow_le_rpow`, `Real.rpow_le_one`; recall that for a
*negative* base Lean's `Real.rpow` is `|x|^y cos (πy)`, again of absolute value `≤ |x|^y`).

The radial derivative is handled through `D_zF_* = (α/c)(Γ · H)`,
`H(z) = 2z(1-z)/(1+z)³ = 2z h'(z)` (`FstarPkg.Dz_Fstar_eq_Hz`), together with the sharp
radial bound `|H(z)| ≤ 2h(z)` of `FstarSlotBounds` (`Hz_abs_le_hKer`); dividing by
`z > 0` turns `|z ∂_zF_*| ≤ (2α/c) z` into `|∂_zF_*| ≤ 2α/c`.

The normalisation constant only enters through its positivity `0 < c(α)`
(`L12fAux.c_pos`, valid for every `α > 0`): the constants `α/c` and `2α/c` are the sharp ones
of the paper and do *not* use the numerical range `1/10 ≤ c ≤ 10` of the `α ≤ 1` regime.
-/

/-- `|Γ(θ)| ≤ 1` for every real angle and every `α ≥ 0`: the base `sinθ cos²θ` of the real
power lies in `[-1,1]`, and `|x^y| ≤ |x|^y ≤ 1` for `0 ≤ y`, `|x| ≤ 1`. -/
lemma abs_Gam_le_one_quad {α θ : ℝ} (hα : 0 ≤ α) : |Work.Spaces.Gam α θ| ≤ 1 := by
  have hbase : |Real.sin θ * Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_mul]
    have hcos : |Real.cos θ ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ, sq_nonneg (Real.cos θ)]
    calc |Real.sin θ| * |Real.cos θ ^ 2| ≤ 1 * 1 :=
          mul_le_mul (Real.abs_sin_le_one θ) hcos (abs_nonneg _) (by norm_num)
      _ = 1 := by ring
  rw [Work.Spaces.Gam]
  calc |(Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)| ≤ |Real.sin θ * Real.cos θ ^ 2| ^ (α / 3) :=
        Real.abs_rpow_le_abs_rpow _ _
    _ ≤ 1 ^ (α / 3) := Real.rpow_le_rpow (abs_nonneg _) hbase (by linarith)
    _ = 1 := Real.one_rpow _

/-- The radial factor `h(z) = z/(1+z)²` is at most `1/4` on `z > 0` (its maximum, at `z = 1`):
equivalently `(1+z)² ≥ 4z`. -/
lemma hKer_le_quarter_quad {z : ℝ} (hz : 0 < z) : Work.Spaces.hKer z ≤ 1 / 4 := by
  rw [Work.Spaces.hKer_apply, div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  nlinarith [sq_nonneg (1 - z), hz]

theorem Fstar_quad_bounds {α : ℝ} (hα : 0 < α) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Fstar α)) Work.FTS.EllipticEst.Q0 ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Fstar α z θ| ≤ α / Work.Spaces.c α) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.pz (Work.Construction.Fstar α) z θ| ≤ 2 * α / Work.Spaces.c α) := by
  have hcpos : 0 < Work.Spaces.c α := Work.FTS_RegExport.RXR5L.L12fAux.c_pos hα
  have hc0 : 0 ≤ Work.Spaces.c α := hcpos.le
  refine ⟨?_, ?_, ?_⟩
  · -- `F_*` is `C^∞` on the strip `(-1,∞) × (0,π/2)`, hence `C²` on the smaller quadrant `Q0`
    refine ((Work.FTS.LocData.SmoothQuad_Fstar α).mono ?_).of_le
      (by simp [Work.Stability.smoothOrder])
    intro p hp
    simp only [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
    exact ⟨by linarith [hp.1], hp.2⟩
  · -- `|F_*| = (2α/c) |Γ| h ≤ (2α/c)·(1/4) = α/(2c) ≤ α/c`
    intro z θ hz hθ0 hθ1
    have hGam : |Work.Spaces.Gam α θ| ≤ 1 := abs_Gam_le_one_quad hα.le
    have hker : Work.Spaces.hKer z ≤ 1 / 4 := hKer_le_quarter_quad hz
    have hker0 : 0 ≤ Work.Spaces.hKer z := Work.FTS.StrongEps.E5Aux2.hKer_nonneg_of_pos hz
    have hcoef0 : 0 ≤ 2 * α / Work.Spaces.c α := div_nonneg (by linarith) hc0
    have hF : Work.Construction.Fstar α z θ
        = 2 * α / Work.Spaces.c α * Work.Spaces.Gam α θ * Work.Spaces.hKer z := by
      rw [Work.FTS.Nonlinear.FstarPkg.Fstar_eq_factored α]
    rw [hF, abs_mul, abs_mul, abs_of_pos (div_pos (by linarith) hcpos), abs_of_nonneg hker0]
    calc 2 * α / Work.Spaces.c α * |Work.Spaces.Gam α θ| * Work.Spaces.hKer z
        = (2 * α / Work.Spaces.c α) * (|Work.Spaces.Gam α θ| * Work.Spaces.hKer z) := by ring
      _ ≤ (2 * α / Work.Spaces.c α) * (1 * (1 / 4)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hGam hker hker0 (by norm_num)) hcoef0
      _ = (α / Work.Spaces.c α) * (1 / 2) := by ring
      _ ≤ (α / Work.Spaces.c α) * 1 :=
          mul_le_mul_of_nonneg_left (by norm_num) (div_nonneg hα.le hc0)
      _ = α / Work.Spaces.c α := by ring
  · -- `D_zF_* = (α/c)(Γ·H)` with `|H(z)| ≤ 2h(z)`, so `|z∂_zF_*| ≤ (2α/c)z`
    intro z θ hz hθ0 hθ1
    have hGam : |Work.Spaces.Gam α θ| ≤ 1 := abs_Gam_le_one_quad hα.le
    have hHz : |Work.FTS.Nonlinear.FstarPkg.Hz z| ≤ 2 * Work.Spaces.hKer z :=
      Work.FTS.StrongEps.E5Aux2.Hz_abs_le_hKer hz
    have hker0 : 0 ≤ Work.Spaces.hKer z := Work.FTS.StrongEps.E5Aux2.hKer_nonneg_of_pos hz
    have hcoef0 : 0 ≤ α / Work.Spaces.c α := div_nonneg hα.le hc0
    have hDz : |Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
        ≤ (2 * α / Work.Spaces.c α) * z := by
      have hEq : Work.Spaces.Dz (Work.Construction.Fstar α) z θ
          = α / Work.Spaces.c α * (Work.Spaces.Gam α θ * Work.FTS.Nonlinear.FstarPkg.Hz z) :=
        Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz hα (by linarith)
      rw [hEq, abs_mul, abs_of_pos (div_pos hα hcpos), abs_mul]
      calc α / Work.Spaces.c α * (|Work.Spaces.Gam α θ| * |Work.FTS.Nonlinear.FstarPkg.Hz z|)
          ≤ α / Work.Spaces.c α * (1 * (2 * Work.Spaces.hKer z)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hGam hHz (abs_nonneg _) (by norm_num)) hcoef0
        _ = 2 * α / Work.Spaces.c α * Work.Spaces.hKer z := by ring
        _ = 2 * α / Work.Spaces.c α * (z / (1 + z) ^ 2) := by rw [Work.Spaces.hKer_apply]
        _ ≤ 2 * α / Work.Spaces.c α * z := by
            refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (by linarith) hc0)
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
            nlinarith [sq_nonneg z, hz]
    have hzpz : z * |Work.Spaces.pz (Work.Construction.Fstar α) z θ|
        = |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| := by
      rw [show Work.Spaces.Dz (Work.Construction.Fstar α) z θ
            = z * Work.Spaces.pz (Work.Construction.Fstar α) z θ from rfl, abs_mul,
        abs_of_pos hz]
    have hmain : z * |Work.Spaces.pz (Work.Construction.Fstar α) z θ|
        ≤ z * (2 * α / Work.Spaces.c α) := by
      rw [hzpz]
      linarith [hDz]
    exact le_of_mul_le_mul_left hmain hz

end Work.FTS.StrongEps.E5Aux2.PT
