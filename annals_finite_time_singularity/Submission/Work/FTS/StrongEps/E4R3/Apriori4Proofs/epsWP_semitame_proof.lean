import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.EpsWPSemitameAux.BlkNstar
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.Jeps_IP6_transfer_aux
import Submission.Work.FTS.StrongEps.H5.Nb5Core
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS_StreamBdry.Inputs.slice_assy
import Submission.Work.FTS_StreamBdry.Inputs.slice_slots
import Submission.Work.FTS_StreamBdry.SB5.sb5_decay

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-!
# `epsWP_semitame_proof` — the semi-tame size of the projected right-hand side

The target is the level-`6` semi-tame estimate of the pre-mollified right-hand side
`epsWP α ρ ε Φs E g τ` of the projected scheme.  Everything happens on the projected slice
`w = slice (JfamP ρ ε g) τ`: by `epsWP_eq_epsWBlk`, `epsWP … = epsWBlk α Φs w (E w) μ lam` with
`μ = muBlk α Φs w (E w)` and `lam = lamfun μ`, both bounded by `MuLamOK`.

Each of the five blocks of `epsWBlk` supplies `BData` (see `blocks/`), and the assembly
`semitame_blk_of_blocks` turns the five `BData`'s into the three conjuncts.
-/

/-- `√(1+x) ≤ 1 + √x` for `x ≥ 0`. -/
theorem sqrt_one_add_le {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (1 + x) ≤ 1 + Real.sqrt x := by
  have hnn : 0 ≤ 1 + Real.sqrt x := by linarith [Real.sqrt_nonneg x]
  rw [← Real.sqrt_sq hnn]
  refine Real.sqrt_le_sqrt ?_
  have hsq : (1 + Real.sqrt x) ^ 2 = 1 + 2 * Real.sqrt x + x := by
    rw [add_sq, one_pow, Real.sq_sqrt hx]; ring
  rw [hsq]
  linarith [Real.sqrt_nonneg x]

/-- `√(a+b) ≤ √a + √b` for `a, b ≥ 0`. -/
theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hnn : 0 ≤ Real.sqrt a + Real.sqrt b := by
    linarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  rw [← Real.sqrt_sq hnn]
  refine Real.sqrt_le_sqrt ?_
  have hsq : (Real.sqrt a + Real.sqrt b) ^ 2 = a + 2 * (Real.sqrt a * Real.sqrt b) + b := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]; ring
  rw [hsq]
  have h2 : 0 ≤ 2 * (Real.sqrt a * Real.sqrt b) := by positivity
  linarith


/-- The `BData` of the `N₀`-block, in the `∃ α₀` shape needed by the assembly: the all-scale
producer `blocks.N0_BData` is used verbatim, and the off-quadrant-vanishing hypothesis of the
assembly is specialised to its `z > 0` half (the part the norms see). -/
theorem blkN0_BData_blocks (C₀ : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ α ∈ Set.Ioc (0 : ℝ) a, ∃ K : ℝ, 0 < K ∧ ∀ {w : Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      (∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (Real.pi / 2)) → w z θ = 0) →
      BData α w K (blkN0 α w) := by
  obtain ⟨K, hK, h⟩ := blocks.N0_BData C₀
  exact ⟨1, one_pos, fun α hα => ⟨K, hK, fun {w} hc hx hzero =>
    h α hα w hc hx (fun z θ hz hth => hzero z θ (fun hh => hth hh.2))⟩⟩



end Work.FTS.StrongEps.E4R3.Apriori4Proofs
