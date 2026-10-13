import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_EllLimOK.FatouH
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.BoxDataH.Crux
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxRegOfBoxUniform2
import Submission.Work.FTS_EllLimOK.BoxDataH.ClusterLimitH

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.BoxDataH

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/--
**`BoxDataH` from the honest hypothesis `HasPkgH`.**

Along every `LimSeq4` and on every closed box `cbox a b = [a,b] × [0,π/2]` (`0 < a ≤ b`) the
sequence `E (fn n)` converges pointwise to a limit `Ψ` which is `C²` on the box and vanishes on the
two angular boundary lines.

The proof has three steps.  `ClusterLimitH.clusterLimitH` supplies the limit `Ψ` (with the law, the
two `ℋ⁰`-memberships and the `C²`-regularity on every box, obtained from the `C^{2,β}`
Arzelà–Ascoli crux `contDiffOn_two_of_boxUniform2` fed by `PkgBoxH`), together with the
sub-subsequence convergence on the open quadrant; `Filter.tendsto_of_subseq_tendsto` upgrades the
latter to the convergence of the *whole* sequence on the open quadrant, and the two Dirichlet
clauses of the law give the convergence on the two boundary lines.
-/
theorem boxDataH_of_hasPkgH {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS_EllLimOK.BoxDataH α Ce := by
  intro E hE fn f hL a b ha hab
  obtain ⟨Ψ, hbox, hsol, -, -, hcluster⟩ := clusterLimitH (E := E) hα hα1 hE hL
  -- the box-uniform data of the sequence, on every box
  have hboxdata : ∀ a' b' : ℝ, 0 < a' → a' < b' →
      BoxUniform2 a' b' (fun n z θ => E (fn n) z θ) := by
    intro a' b' ha' hab'
    obtain ⟨K, β, hK, hβ, hb⟩ := hE.box a' b' ha' hab'.le
    obtain ⟨B, hB⟩ := hL.bound
    refine ⟨K * max B 0 + 1, β, hβ, ?_, ?_, ?_⟩
    · intro n
      exact (hb (fn n) (hL.classC n)).1
    · intro n k hk p hp
      have h2 : Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ max B 0 :=
        le_trans (hB n) (le_max_left _ _)
      have hle : K * Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ K * max B 0 :=
        mul_le_mul_of_nonneg_left h2 hK.le
      calc ‖iteratedFDerivWithin ℝ k (Function.uncurry (E (fn n)))
              (Work.FTS_EllLimOK.cbox a' b') p‖
          ≤ K * Work.FTS.StrongGlobal.Xn6 α (fn n) :=
            (hb (fn n) (hL.classC n)).2.1 hab' k hk p hp
        _ ≤ K * max B 0 := hle
        _ ≤ K * max B 0 + 1 := by linarith
    · intro n p hp q hq
      have h2 : Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ max B 0 :=
        le_trans (hB n) (le_max_left _ _)
      have hr : (0 : ℝ) ≤ ‖p - q‖ ^ β := Real.rpow_nonneg (norm_nonneg _) _
      have hle : K * Work.FTS.StrongGlobal.Xn6 α (fn n) ≤ K * max B 0 :=
        mul_le_mul_of_nonneg_left h2 hK.le
      calc ‖iteratedFDerivWithin ℝ 2 (Function.uncurry (E (fn n)))
              (Work.FTS_EllLimOK.cbox a' b') p
            - iteratedFDerivWithin ℝ 2 (Function.uncurry (E (fn n)))
              (Work.FTS_EllLimOK.cbox a' b') q‖
          ≤ K * Work.FTS.StrongGlobal.Xn6 α (fn n) * ‖p - q‖ ^ β :=
            (hb (fn n) (hL.classC n)).2.2 hab' p hp q hq
        _ ≤ (K * max B 0) * ‖p - q‖ ^ β := mul_le_mul_of_nonneg_right hle hr
        _ ≤ (K * max B 0 + 1) * ‖p - q‖ ^ β := mul_le_mul_of_nonneg_right (by linarith) hr
  -- the convergence of the whole sequence on the open quadrant
  have hconvQ : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => E (fn n) z θ) Filter.atTop (nhds (Ψ z θ)) := by
    intro z θ hzθ
    refine Filter.tendsto_of_subseq_tendsto (fun ns hns => ?_)
    obtain ⟨τ, hτ⟩ := hcluster ns hns
    exact ⟨τ, hτ z θ hzθ⟩
  -- the pointwise convergence on every box
  have hconvAll : ∀ a' b' : ℝ, 0 < a' → a' < b' → ∀ z ∈ Set.Icc a' b',
      ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      Filter.Tendsto (fun n => E (fn n) z θ) Filter.atTop (nhds (Ψ z θ)) := by
    intro a' b' ha' _ z hz θ hθ
    have hzpos : 0 < z := lt_of_lt_of_le ha' hz.1
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      have hm : (fun n : ℕ => E (fn n) z 0) = fun _ => (0 : ℝ) := by
        funext n
        exact ((hE.toHasPkg (fn n) (hL.classC n)).2.sol).2.1 z hzpos.le
      have hl : Ψ z 0 = 0 := hsol.2.1 z hzpos.le
      rw [hl, hm]
      exact tendsto_const_nhds
    · rcases eq_or_lt_of_le hθ.2 with h1 | h1
      · subst h1
        have hm : (fun n : ℕ => E (fn n) z (Real.pi / 2)) = fun _ => (0 : ℝ) := by
          funext n
          exact ((hE.toHasPkg (fn n) (hL.classC n)).2.sol).2.2.1 z hzpos.le
        have hl : Ψ z (Real.pi / 2) = 0 := hsol.2.2.1 z hzpos.le
        rw [hl, hm]
        exact tendsto_const_nhds
      · exact hconvQ z θ ⟨hzpos, h0, h1⟩
  have hBoxReg : Work.FTS_EllLimOK.BoxReg Ψ :=
    boxReg_of_boxUniform2 (H := fun n z θ => E (fn n) z θ) hboxdata hconvAll
  exact ⟨Ψ, hBoxReg a b ha hab.le, hconvAll a b ha hab, fun z hz =>
    ⟨hsol.2.1 z (le_trans ha.le hz.1), hsol.2.2.1 z (le_trans ha.le hz.1)⟩⟩

end Work.FTS_EllLimOK.BoxDataH
