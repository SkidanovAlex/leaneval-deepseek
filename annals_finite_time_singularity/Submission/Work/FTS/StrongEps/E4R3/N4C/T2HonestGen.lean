import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.N6Trans.IP4T2Honest
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.ClauseHon
import Submission.Work.FTS.IPGen.ip4SlotDomGen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C

theorem T2HonestGen (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) (h₁ : 0 < c₁) (h₂ : 0 < c₂)
    (h₁' : 0 < c₁') (h₂' : 0 < c₂') (h₁'' : 0 < c₁'') (h₂'' : 0 < c₂'') :
    ∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Work.FTS.Galerkin.Fn,
        Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
        Work.FTS.VocabO.CoefThMem 1 f →
        Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
        Work.Spaces.HkMem α 5 g → Work.Spaces.DecayAll 4 g →
        |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
            (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
          ≤ Ct * α ^ (-(1 / 2 : ℝ))
              * (Work.Spaces.HkNorm α 4 f + Work.FTS.VocabO.CoefTh 1 f)
              * (Work.Spaces.HkNorm α 4 g) ^ 2 := by
  -- The honest per-slot bound `T2SlotHon C` (the three `T2` slot types of the level-four
  -- pairing, in the open-quadrant class), from the honest radial integration by parts and the
  -- honest delicate bound.
  obtain ⟨C, hC, hS⟩ := Work.FTS.StrongPersist.N6Trans.Hon.T2SlotHon_of_slotAbs
    Work.FTS.StrongPersist.N6Trans.Hon.TopSlotHon
    Work.FTS.StrongPersist.N6Trans.Hon.DelicateHon
  -- The slot domination of the concrete coercive `IP4` with the six free (nonnegative)
  -- step coefficients: `|IP4 α u v| ≤ K · leafSum α u v`.
  have hD := Work.FTS.IPGen.ip4SlotDomGen (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂')
    (c₁'' := c₁'') (c₂'' := c₂'') h₁.le h₂.le h₁'.le h₂'.le h₁''.le h₂''.le
  refine ⟨max 1 (max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂''))))) ^ 3 * 3 ^ 3
      * 10 ^ 22 * 75 * C, 1, ?_, one_pos, ?_⟩
  · have h1 : (1 : ℝ) ≤ max 1 (max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂''))))) :=
      le_max_left _ _
    have hK : 0 < max 1 (max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂''))))) ^ 3 * 3 ^ 3
        * (10 : ℝ) ^ 22 :=
      mul_pos (mul_pos (pow_pos (lt_of_lt_of_le one_pos h1) 3) (by norm_num)) (by norm_num)
    exact mul_pos (mul_pos hK (by norm_num)) hC
  · intro α hα f g hf1 hf2 hf3 hg1 hg2 hg3 hg4
    exact Work.FTS.StrongPersist.N6Trans.Hon.T2ClauseHon_of_slot (le_of_lt hC) le_rfl hS hD
      α hα f g hf1 hf2 hf3 hg1 hg2 hg3 hg4

end Work.FTS.StrongEps.E4R3.N4C
