import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.Standing
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKaux.FtauSlot` — uniform slot bounds for the profiles `F(τ) = F_* + slice (gn n) τ`

The mixed/radial slots `D_z^k (F_* + slice (gn n) τ)` of order `k ≤ 2` are bounded by a
constant which does not depend on `n`, `τ`, `z` or `θ`: the reference part by the radial jet
bound `FstarJet7` (`|D_z^j F_*| ≤ 10 M`), the perturbation part by the weighted bound
`Cw · z^{3/2}/(1+z)² ≤ Cw` of `Standing.app_slot_le`, and the sum by the additivity
`ftau_DzIter_one_add` / `ftau_DzIter_two_add` of `D_z^k` on the open quadrant.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- `SW z ≤ 1` for `z > 0`. -/
theorem SW_le_one {z : ℝ} (hz : 0 < z) : SW z ≤ 1 := by
  have hpos : (0 : ℝ) < (1 + z) ^ 2 := by positivity
  rw [SW, div_le_iff₀ hpos]
  by_cases h : 1 ≤ z
  · have h1 : z ^ ((3 : ℝ) / 2) ≤ z ^ 2 := by
      rw [← Real.rpow_natCast z 2]
      exact Real.rpow_le_rpow_of_exponent_le h (by norm_num)
    have h2 : z ^ 2 ≤ (1 + z) ^ 2 := by nlinarith
    linarith
  · have hz1 : z < 1 := not_le.mp h
    have h1 : z ^ ((3 : ℝ) / 2) ≤ 1 := by
      have h0 : z ^ ((3 : ℝ) / 2) ≤ (1 : ℝ) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow hz.le hz1.le (by norm_num)
      simpa using h0
    have h2 : (1 : ℝ) ≤ (1 + z) ^ 2 := by nlinarith
    linarith

/-- The additivity of `D_z^k` on `F_* + u` on the open quadrant, for `k ≤ 2`. -/
theorem DzIter_Fstar_add {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {u : ℝ → ℝ → ℝ}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    {k : ℕ} (hk : k ≤ 2) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter k
          (fun z θ => Work.Construction.Fstar β z θ + u z θ) z θ
        = Work.Spaces.DzIter k (Work.Construction.Fstar β) z θ
          + Work.Spaces.DzIter k u z θ := by
  have hF2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Fstar β))
      Work.FTS.EllipticEst.Q0 := Work.FTS_RegExport.RXT.ftau_contDiffOn_Fstar_Q0 hβ hβ1
  have hF1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Fstar β))
      Work.FTS.EllipticEst.Q0 := hF2.of_le (by norm_num)
  have h4' : ContDiffOn ℝ 2 (Function.uncurry u) Work.FTS.EllipticEst.Q0 :=
    h4.of_le (by norm_num)
  have h4'' : ContDiffOn ℝ 1 (Function.uncurry u) Work.FTS.EllipticEst.Q0 :=
    h4.of_le (by norm_num)
  interval_cases k
  · intro z θ hz h1 h2; rfl
  · exact Work.FTS_RegExport.RXT.ftau_DzIter_one_add hF1 h4''
  · exact Work.FTS_RegExport.RXT.ftau_DzIter_two_add hF2 h4'

/-- **Uniform slot bounds for `F(τ) = F_* + slice (gn n) τ`,** `k ≤ 2`. -/
theorem Ftau_slot_le {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam}
    (hcl : ∀ (n : ℕ) (τ : ℝ),
      Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) (slice (gn n) τ))
    (hXn : ∀ (n : ℕ) (τ : ℝ),
      Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
        ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2)
    (τ : ℝ) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ,
      0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ| ≤ CB := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨Cw, hCw0, hCw⟩ := app_slot_le (α := Work.FTS.Regularity.pExp α)
    (C₀ := C₀) hβ hβ1 hcl hXn
  obtain ⟨M, hM0, hM⟩ := Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
  refine ⟨10 * M + Cw, by linarith, ?_⟩
  intro n k hk z θ hz h1 h2
  have hadd := DzIter_Fstar_add (β := Work.FTS.Regularity.pExp α) hβ hβ1
    (h4 := (hcl n τ).reg.forall 4) (k := k) hk z θ hz h1 h2
  change |Work.Spaces.DzIter k (fun z θ => Work.Construction.Fstar
      (Work.FTS.Regularity.pExp α) z θ + slice (gn n) τ z θ) z θ| ≤ 10 * M + Cw
  rw [hadd]
  have hA : |Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α))
      z θ| ≤ 10 * M :=
    Work.FTS_RegExport.RXT.ftau_DzIter_Fstar_le (α := α) hα hα13 hM k (by omega) z θ hz h1 h2
  have hB : |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw := by
    have h := hCw n τ k 0 (by omega) z θ hz h1 h2
    simpa only [Work.Spaces.mixed_zero_right] using
      le_trans h (mul_le_of_le_one_right hCw0 (SW_le_one hz))
  calc |Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
        + Work.Spaces.DzIter k (slice (gn n) τ) z θ|
      ≤ |Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ|
        + |Work.Spaces.DzIter k (slice (gn n) τ) z θ| := abs_add_le _ _
    _ ≤ 10 * M + Cw := add_le_add hA hB

end Work.FTS_RegExport.RXT.Sys.L12FKaux
