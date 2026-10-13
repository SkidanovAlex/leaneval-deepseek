import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.NonlinRows.NRow10aux.PhiDefs
import Submission.Work.FTS.NonlinRows.NRow10aux.phiSelfFacts
import Submission.Work.FTS.NonlinRows.NRow10aux.radialBounded_majorant
import Submission.Work.FTS.NonlinRows.NRow10aux.hkmem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.NRow10aux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# Multiplication by the bounded radial factor `φ(z) = z/(1+z)` costs nothing in `ℋ⁴`

The statement `Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk` is assembled from the three
pieces of the `NRow10aux` chain:

* `radialBounded_majorant` — the pointwise majorant
  `HkIntegrand α 4 (r·g) ≤ K · HkIntegrand α 4 g` for a radial factor `r` with
  `|D_z^b r| ≤ 1`, `b ≤ 4`;
* `phiSelfFacts` — those bounds for `φ` (plus `SmoothOpen φ`);
* `hkmem_of_majorant` — transport of `HkMem`/`HkSq` along a pointwise majorant.

The constant is `C = √K + 1`, which works because `HkMem α 4 g` makes `HkSq α 4 g ≥ 0`
honest and `HkNorm = √(HkSq)`.
-/

/-- At `z = 0` the weight `w` vanishes (`w 0 = (1+0)²/0² = 1/0 = 0`, Lean's totalised
division), so *every* term of the weighted `ℋ^k`-integrand vanishes there. -/
theorem HkIntegrand_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
  simp

theorem mul_phi_Hk :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {g : ℝ → ℝ → ℝ}, 0 < α → α ≤ 1 →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => z / (1 + z) * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * g z θ) ≤ C * Work.FTS.Nonlin.Xn α g := by
  obtain ⟨K, hKpos, hK⟩ := radialBounded_majorant
  have hphiSO : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => phiF z) := phiSelf_smoothOpen
  have hphiBnd : ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter b phiF z| ≤ 1 := fun b hb z hz => phiSelf_DzdIter_bound_phiF b hb z hz
  refine ⟨Real.sqrt K + 1, by positivity, ?_⟩
  intro α g hα hα1 hg
  obtain ⟨hgSO, hgm⟩ := hg
  -- the product is again smooth on the open quadrant
  have hSO : Work.FTS.EllipticEst.SmoothOpen (fun z θ => phiF z * g z θ) := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => p.1 / (1 + p.1)) Work.FTS.EllipticEst.Q0 := hphiSO
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => g p.1 p.2) Work.FTS.EllipticEst.Q0 := hgSO
    exact h1.mul h2
  -- the pointwise majorant, including the degenerate slice `z = 0`
  have hmaj : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.HkIntegrand α 4 (fun z θ => phiF z * g z θ) z θ
        ≤ K * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [← hz0]
      have h0 : Work.Spaces.HkIntegrand α 4 (fun z θ => phiF z * g z θ) 0 θ = 0 :=
        HkIntegrand_zero α 4 _ θ
      have h1 : Work.Spaces.HkIntegrand α 4 g 0 θ = 0 := HkIntegrand_zero α 4 g θ
      rw [h0, h1, mul_zero]
    · exact hK α phiF g hphiSO hgSO hphiBnd z θ hzpos hθ.1 hθ.2
  -- transport of `HkMem` and of the norm along the majorant
  obtain ⟨hHkMem, hHkSq⟩ := hkmem_of_majorant α 4 hKpos.le hSO hgm hmaj
  refine ⟨hHkMem, ?_⟩
  have hXn : 0 ≤ Work.FTS.Nonlin.Xn α g := Real.sqrt_nonneg _
  calc Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * g z θ)
      = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => z / (1 + z) * g z θ)) := rfl
    _ ≤ Real.sqrt (K * Work.Spaces.HkSq α 4 g) := Real.sqrt_le_sqrt hHkSq
    _ = Real.sqrt K * Real.sqrt (Work.Spaces.HkSq α 4 g) := Real.sqrt_mul hKpos.le _
    _ = Real.sqrt K * Work.FTS.Nonlin.Xn α g := rfl
    _ ≤ (Real.sqrt K + 1) * Work.FTS.Nonlin.Xn α g := by
        apply mul_le_mul_of_nonneg_right _ hXn
        linarith [Real.sqrt_nonneg K]

end

end Work.FTS.NonlinRows.NRow10aux
