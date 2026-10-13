import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4Prep
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4Slots
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4Leaf
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4Rec

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TransferDeriv/IP4_transfer_deriv.lean` — the level-four derivative-priced transfer estimate

The hypothesis `hslot` is the *slot* transfer of `TransferDeriv/Defs.lean`; the conclusion lifts it
to the level-four pairing `IP4 = HkIPStep c₁'' c₂'' (HkIPStep c₁' c₂' (HkIPStep c₁ c₂ (H1IP α)))`.

The assembly: `IP4 α (J_ε f) h − IP4 α f (J_ε h)` is the transfer defect `Def 3 0 0` of the
recursion (`IP4Rec`), which the recursion bounds by `KCB 3` times the level-zero bound
(`IP4Leaf.leaf_bound`, through the slot transfer at the cuts of the shifted slots, `IP4Slots`), and
the level-zero bound is `O(ε |f|_{ℋ⁴} |h|_{ℋ⁵})`.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The level-four derivative-priced transfer estimate.** -/
theorem IP4_transfer_deriv {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hslot : ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      ∀ {w : ℝ → ℝ → ℝ} {a b : ℕ}, Work.FTS.TransportS.IsLeafW α a w → a + b ≤ 4 →
      ∀ u v : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen u →
        Work.FTS.EllipticEst.SmoothOpen v →
      SlotIntegrableDeriv ρ ε w a b u v →
      |Work.Coercivity.wip w (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u))
          (Work.Spaces.mixed b a v)
        - Work.Coercivity.wip w (Work.Spaces.mixed b a u)
            (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε v))|
        ≤ K * ε * Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a u)
              (Work.Spaces.mixed b a u))
          * (Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a v)
                (Work.Spaces.mixed b a v))
            + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed (b + 1) a v)
                (Work.Spaces.mixed (b + 1) a v))
            + Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b (a + 1) v)
                (Work.Spaces.mixed b (a + 1) v)))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      ∀ f h : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 5 h →
      |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
          (Work.FTS.StrongEps.Jeps ρ ε f) h
        - Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f
            (Work.FTS.StrongEps.Jeps ρ ε h)|
        ≤ C * ε * (Work.Spaces.HkNorm α 4 f) * (Work.Spaces.HkNorm α 4 h
            + Work.Spaces.HkNorm α 5 h) := by
  refine ⟨KCB c₁ c₂ c₁' c₂' c₁'' c₂'' 3 * (3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21)) * K,
    mul_nonneg (mul_nonneg (KCB_nonneg _ _ _ _ _ _ 3) (by norm_num)) hK, ?_⟩
  intro α hα ε hε f h hf hh
  obtain ⟨hfs, hmf⟩ := hf
  obtain ⟨hhs, hmh⟩ := hh
  have hST : SlotTransfer ρ K := hslot
  have hmain := Def_bound hρ hK hST hα hε hfs hhs hmf hmh c₁ c₂ c₁' c₂' c₁'' c₂'' 3 0 0
    (by norm_num)
  have hL : Def α (stepC c₁ c₂ c₁' c₂' c₁'' c₂'') ρ ε f h 3 0 0
      = Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
          (Work.FTS.StrongEps.Jeps ρ ε f) h
        - Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f
            (Work.FTS.StrongEps.Jeps ρ ε h) := by
    simp only [Def, QP_three_eq_IP4, Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right,
      Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
  rw [hL] at hmain
  refine hmain.trans ?_
  have hN4h : (0 : ℝ) ≤ Work.Spaces.HkNorm α 4 h := Work.Spaces.HkNorm_nonneg α 4 h
  have hKCB : (0 : ℝ) ≤ KCB c₁ c₂ c₁' c₂' c₁'' c₂'' 3 := KCB_nonneg _ _ _ _ _ _ 3
  have hle : Work.Spaces.HkNorm α 5 h
      ≤ Work.Spaces.HkNorm α 4 h + Work.Spaces.HkNorm α 5 h :=
    le_add_of_nonneg_left hN4h
  calc KCB c₁ c₂ c₁' c₂' c₁'' c₂'' 3
        * (3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K * ε
            * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 5 h)
      ≤ KCB c₁ c₂ c₁' c₂' c₁'' c₂'' 3
          * (3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * K * ε
              * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 h + Work.Spaces.HkNorm α 5 h)) := by
        refine mul_le_mul_of_nonneg_left ?_ hKCB
        exact mul_le_mul_of_nonneg_left hle
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) hε.1.le)
            (Work.Spaces.HkNorm_nonneg α 4 f))
    _ = (KCB c₁ c₂ c₁' c₂' c₁'' c₂'' 3 * (3 * (10 + 10 ^ 10 + 10 ^ 17 + 10 ^ 21)) * K)
          * ε * (Work.Spaces.HkNorm α 4 f)
          * (Work.Spaces.HkNorm α 4 h + Work.Spaces.HkNorm α 5 h) := by ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
