import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCaseLt
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCaseGe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCaseHard

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

/-- **The mismatch case of the level-six coefficient row.**  For the coefficient slot
`X = D_z^{b₁}D_θ^{a₁}A` of order `a₁ ≥ 1`, `a₁ + b₁ ≤ 2`, the datum slots
`Y = D_z^{b-b₁}D_θ^{a-a₁} f`, `Z = D_z^bD_θ^a f` of total order `a + b ≤ 6`, and the leaf
weight `leafGam α = w²sin(2θ)^{-γ}`,

`|∫∫ leafGam α · X · Y · Z| ≤ C α^{-3} (1 + K0 + K4) (1 + |f|²_{ℋ⁶})`.

The three index cases `a₁ < a`, `a = a₁ ∧ ¬(a₁ = 1 ∧ b₁ = 0)` and `a = a₁ = 1 ∧ b₁ = 0` are
proved in the sibling modules `mismatchCaseLt`, `mismatchCaseGe`, `mismatchCaseHard`. -/
theorem mismatchCoefCase : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (A f : ℝ → ℝ → ℝ) (K0 K4 : ℝ) (a b a₁ b₁ : ℕ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 4 A →
      Work.Spaces.HkMem α 6 A →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0) →
      Work.FTS.Nonlin.Xn α A ≤ K4 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 7 f →
      Work.Spaces.VanishTheta f →
      1 ≤ a₁ → a₁ + b₁ ≤ 2 → a₁ ≤ a → b₁ ≤ b → a + b ≤ 6 →
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
        ≤ C * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
  obtain ⟨C1, hC1pos, hLt⟩ := mismatchCaseLt
  obtain ⟨C2, hC2pos, hGe⟩ := mismatchCaseGe
  obtain ⟨C3, hC3pos, hHard⟩ := mismatchCaseHard
  refine ⟨max C1 (max C2 C3), lt_of_lt_of_le hC1pos (le_max_left _ _), ?_⟩
  intro α hα A f K0 K4 a b a₁ b₁ hAsm hA4 hA6 hAbdd hA4bnd hfsm hf7 hfv
    ha₁ hab₁ ha₁a hb₁b hab
  have hK0 : 0 ≤ K0 :=
    le_trans (abs_nonneg (A 1 (Real.pi / 4)))
      (hAbdd 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos]))
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hA4bnd
  have hX : 0 ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f) :=
    mul_nonneg (by linarith) (by linarith [Work.Spaces.HkSq_nonneg α 6 f])
  have hα3 : 0 ≤ α ^ (-(3 : ℝ)) := Real.rpow_nonneg hα.1.le _
  have hshape : ∀ c : ℝ, c ≤ max C1 (max C2 C3) →
      c * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))
        ≤ max C1 (max C2 C3) * α ^ (-(3 : ℝ))
          * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
    intro c hc
    have h1 : c * α ^ (-(3 : ℝ)) ≤ max C1 (max C2 C3) * α ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_right hc hα3
    have h2 : c * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))
        ≤ max C1 (max C2 C3) * α ^ (-(3 : ℝ))
          * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
      calc c * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))
          = (c * α ^ (-(3 : ℝ))) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by ring
        _ ≤ (max C1 (max C2 C3) * α ^ (-(3 : ℝ)))
              * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) :=
            mul_le_mul_of_nonneg_right h1 hX
        _ = max C1 (max C2 C3) * α ^ (-(3 : ℝ))
              * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by ring
    exact h2
  by_cases hlt : a₁ < a
  · obtain ⟨hint, hbd⟩ := hLt α hα A f K0 K4 a b a₁ b₁ hAsm hA4 hA6 hAbdd hA4bnd hfsm hf7 hfv
      ha₁ hab₁ ha₁a hb₁b hab hlt
    exact ⟨hint, hbd.trans (hshape C1 (le_max_left C1 (max C2 C3)))⟩
  · have hae : a = a₁ := by omega
    by_cases hb : a₁ = 1 ∧ b₁ = 0
    · obtain ⟨hint, hbd⟩ := hHard α hα A f K0 K4 a b a₁ b₁ hAsm hA4 hA6 hAbdd hA4bnd hfsm
        hf7 hfv ha₁ hab₁ ha₁a hb₁b hab hae hb.1 hb.2
      exact ⟨hint, hbd.trans (hshape C3
        (le_trans (le_max_right C2 C3) (le_max_right C1 (max C2 C3))))⟩
    · obtain ⟨hint, hbd⟩ := hGe α hα A f K0 K4 a b a₁ b₁ hAsm hA4 hA6 hAbdd hA4bnd hfsm
        hf7 hfv ha₁ hab₁ ha₁a hb₁b hab hae hb
      exact ⟨hint, hbd.trans (hshape C2
        (le_trans (le_max_left C2 C3) (le_max_right C1 (max C2 C3))))⟩

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
