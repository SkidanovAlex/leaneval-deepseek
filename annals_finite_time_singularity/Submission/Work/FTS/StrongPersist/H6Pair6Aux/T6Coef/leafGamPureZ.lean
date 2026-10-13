import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyA
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.TransportS.HardDefs
import Submission.Work.FTS.OpenPkg.Basic

import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1five

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

theorem leafGamPureZ : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : ℝ → ℝ → ℝ) (K0 K4 K6 M : ℝ) (a b a₁ b₁ : ℕ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a₁ = 0 → 1 ≤ a → a₁ ≤ a → b₁ ≤ b → 3 ≤ a₁ + b₁ → a + b ≤ 6 →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed b₁ a₁ A p.1 p.2
          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
            * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(3 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := leafGamPureZ_le4
  obtain ⟨C₂, _hC₂pos, hC₂⟩ := leafGamPureZ_b1five
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁pos, ?_⟩
  intro α hα A f K0 K4 K6 M a b a₁ b₁ hCoef hDat ha₁ ha hle hb₁b h3 hab
  have hK0nn : 0 ≤ K0 := by
    have h := hCoef.val 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
    exact le_trans (abs_nonneg _) h
  have hK4nn : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hCoef.n4
  have hK6nn : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hCoef.n6
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hDat.bdd
  have hNnn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hSnn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hρr : 0 ≤ α ^ (-(3 : ℝ)) := Real.rpow_nonneg hα.1.le _
  have hbr : 0 ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
      + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) :=
    add_nonneg (mul_nonneg (by linarith) (by linarith))
      (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
  have hρbr : 0 ≤ α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
      + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := mul_nonneg hρr hbr
  by_cases hb4 : b₁ ≤ 4
  · obtain ⟨hI, hb⟩ := hC₁ α hα A f K0 K4 K6 M a b a₁ b₁ hCoef hDat ha₁ ha hle hb₁b h3 hab hb4
    refine ⟨hI, ?_⟩
    calc |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
            * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C₁ * α ^ (-(3 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := hb
      _ = C₁ * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) := by ring
      _ ≤ max C₁ C₂ * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hρbr
      _ = max C₁ C₂ * α ^ (-(3 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by ring
  · -- the crux case `b₁ = 5` (the case (E2) of `T6Coef/NOTES_mulTermLarge.md`), which forces
    -- `(a,b,a₁,b₁) = (1,5,0,5)` and is supplied by `leafGamPureZ_b1five`.
    have hb₁5 : b₁ = 5 := by omega
    have hb5 : b = 5 := by omega
    have ha1 : a = 1 := by omega
    subst ha₁
    subst hb₁5
    subst hb5
    subst ha1
    simp only [Nat.sub_zero, Nat.sub_self]
    obtain ⟨hI, hbnd⟩ := hC₂ α hα A f K0 K4 K6 M hCoef hDat
    refine ⟨hI, ?_⟩
    calc |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
            * Work.Spaces.mixed 5 0 A p.1 p.2
            * Work.Spaces.mixed 0 1 f p.1 p.2
            * Work.Spaces.mixed 5 1 f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C₂ * α ^ (-(3 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := hbnd
      _ = C₂ * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) := by ring
      _ ≤ max C₁ C₂ * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hρbr
      _ = max C₁ C₂ * α ^ (-(3 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by ring

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
