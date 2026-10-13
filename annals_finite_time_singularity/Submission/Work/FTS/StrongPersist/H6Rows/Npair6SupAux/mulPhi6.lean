import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.NonlinRows.NRow10aux.hkmem_of_majorant
import Submission.Work.FTS.NonlinRows.NRow10aux.phiSelfFacts
import Submission.Work.FTS.OpenPkg.radialMul_field
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialBounded6_majorant
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.phiDzdIter6_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The level-six `z/(1+z)` radial multiplier does not change the weighted `ℋ⁶`-norm:
the product is again smooth on the open quadrant, again in `HkMem α 6`, and its `HkNorm`
is bounded by a universal (α-independent) constant times the `HkNorm` of the input.

The proof assembles two independent pieces:

* `radialBounded6_majorant` — the pointwise majorant
  `HkIntegrand α 6 (r·g) ≤ K Br² HkIntegrand α 6 g` for a radial factor `r` whose
  `D_z`-iterates of order `≤ 6` are bounded by `Br`;
* `phiDzdIter6_bound` — the numerical bound `|D_z^b (z/(1+z))| ≤ 10000` for `b ≤ 6`, `z ≥ 0`;

applied with `r = z/(1+z)`, `Br = 10000` through `hkmem_of_majorant` (which transports
`HkMem` and `HkSq` along a pointwise majorant) and the square-root arithmetic on `HkNorm`. -/
theorem mulPhi6 : ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {g : ℝ → ℝ → ℝ}, 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * g z θ) ∧
      Work.Spaces.HkMem α 6 (fun z θ => z / (1 + z) * g z θ) ∧
      Work.Spaces.HkNorm α 6 (fun z θ => z / (1 + z) * g z θ)
        ≤ C * Work.Spaces.HkNorm α 6 g := by
  obtain ⟨K, hKpos, hK⟩ := radialBounded6_majorant
  refine ⟨Real.sqrt (K * 10000 ^ 2) + 1, by positivity, ?_⟩
  intro α g hα hα1 hgSO hgm
  -- smoothness of the radial factor `z/(1+z)` on the open quadrant
  have hphiSO : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)) := by
    simpa [Work.FTS.NonlinRows.NRow10aux.phiF]
      using Work.FTS.NonlinRows.NRow10aux.phiSelf_smoothOpen
  -- smoothness of the product
  have hSO : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z / (1 + z) * g z θ) :=
    Work.FTS.OpenPkg.smoothOpen_sepMul hphiSO hgSO
  -- the pointwise majorant on the whole half-strip
  have hmaj' : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.HkIntegrand α 6 (fun z θ => z / (1 + z) * g z θ) z θ
        ≤ (K * 10000 ^ 2) * Work.Spaces.HkIntegrand α 6 g z θ := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [← hz0]
      have h1 : Work.Spaces.HkIntegrand α 6 (fun z θ => z / (1 + z) * g z θ) 0 θ = 0 := by
        simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
        simp
      have h2 : Work.Spaces.HkIntegrand α 6 g 0 θ = 0 := by
        simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
        simp
      rw [h1, h2, mul_zero]
    · exact hK α (fun z => z / (1 + z)) g 10000 hphiSO hgSO (by norm_num)
        (fun b hb z hz => phiDzdIter6_bound b hb z hz) z θ hzpos hθ.1 hθ.2
  obtain ⟨hmem, hsq⟩ :=
    Work.FTS.NonlinRows.NRow10aux.hkmem_of_majorant α 6
      (mul_nonneg hKpos.le (by norm_num : (0 : ℝ) ≤ 10000 ^ 2)) hSO hgm hmaj'
  refine ⟨hSO, hmem, ?_⟩
  have hXn : 0 ≤ Work.Spaces.HkNorm α 6 g := Real.sqrt_nonneg _
  have hsqrt : Work.Spaces.HkNorm α 6 (fun z θ => z / (1 + z) * g z θ)
      ≤ Real.sqrt (K * 10000 ^ 2) * Work.Spaces.HkNorm α 6 g := by
    rw [Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α 6 (fun z θ => z / (1 + z) * g z θ))
        ≤ Real.sqrt ((K * 10000 ^ 2) * Work.Spaces.HkSq α 6 g) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (K * 10000 ^ 2) * Real.sqrt (Work.Spaces.HkSq α 6 g) :=
          Real.sqrt_mul (by positivity) _
      _ = Real.sqrt (K * 10000 ^ 2) * Work.Spaces.HkNorm α 6 g := rfl
  calc Work.Spaces.HkNorm α 6 (fun z θ => z / (1 + z) * g z θ)
      ≤ Real.sqrt (K * 10000 ^ 2) * Work.Spaces.HkNorm α 6 g := hsqrt
    _ ≤ (Real.sqrt (K * 10000 ^ 2) + 1) * Work.Spaces.HkNorm α 6 g := by
        refine mul_le_mul_of_nonneg_right ?_ hXn
        linarith

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
