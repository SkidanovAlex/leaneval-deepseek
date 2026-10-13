/-
# `RowDth.perTermDthMine` — the per-term bound of the `D_θ` row, assembled

The five slot cases

* `caseLe2Mine` (`i + j ≤ 2`), `caseTo4Mine` (`3 ≤ i + j ≤ 4`) — both in this directory;
* `caseGe5` (`5 ≤ i + j`, not the exceptional weight), `caseExc` (the exceptional slot
  `D_z⁵A · D_θ²f · D_z⁵D_θf` with the `γ`-leaf weight) — the siblings' lemmas;

with the constant `C₁ + C₂ + C₃ + C₄ + 1` and the exceptional case reduced to
`caseExc` by the forced slot identity `(a,b,i,j) = (1,5,0,5)`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Wgt
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Wgt2
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Integ
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.perTermLow
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.perTermMid
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.caseGe5Mine
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.caseExcMine

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth

open Work.FTS.Galerkin (Fn)
open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z)

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- Increasing the numerical factor of a bracket with nonnegative multipliers. -/
theorem mul_const_le_mul_constM {C C' s Br : ℝ} (h : C ≤ C') (hs : 0 ≤ s) (hB : 0 ≤ Br) :
    C * s * Br ≤ C' * s * Br :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hs) hB

/-- `leafEta` and `leafGam α` are distinct functions (`η ≠ γ`). -/
theorem leafEta_ne_leafGamM {α : ℝ} (hα : 0 < α) :
    Work.FTS.TransportS.leafEta ≠ Work.FTS.TransportS.leafGam α := by
  intro h
  have hw : Work.Spaces.w 1 = 4 := by norm_num [Work.Spaces.w]
  have h2 : Real.sin (2 * (Real.pi / 12)) ^ (-Work.Spaces.eta)
      = Real.sin (2 * (Real.pi / 12)) ^ (-(Work.Spaces.gam α)) := by
    have h3 := congrFun (congrFun h 1) (Real.pi / 12)
    simp only [Work.FTS.TransportS.leafEta, Work.FTS.TransportS.leafGam, hw] at h3
    exact mul_left_cancel₀ (by norm_num : (16 : ℝ) ≠ 0) (by simpa using h3)
  have hs : Real.sin (2 * (Real.pi / 12)) = 1 / 2 := by
    rw [show 2 * (Real.pi / 12) = Real.pi / 6 by ring, Real.sin_pi_div_six]
  rw [hs] at h2
  have hlt : (1 / 2 : ℝ) ^ (-Work.Spaces.eta) < (1 / 2 : ℝ) ^ (-(Work.Spaces.gam α)) := by
    rw [Real.rpow_lt_rpow_left_iff_of_base_lt_one (by norm_num) (by norm_num)]
    rw [Work.Spaces.eta, Work.Spaces.gam]
    linarith
  exact absurd h2 (ne_of_lt hlt)

/-- `leafOne` and `leafGam α` are distinct functions. -/
theorem leafOne_ne_leafGamM {α : ℝ} (hα : 0 < α) :
    Work.FTS.TransportS.leafOne ≠ Work.FTS.TransportS.leafGam α := by
  intro h
  have hw : Work.Spaces.w 1 = 4 := by norm_num [Work.Spaces.w]
  have h3 := congrFun (congrFun h 1) (Real.pi / 12)
  simp only [Work.FTS.TransportS.leafOne, Work.FTS.TransportS.leafGam, hw] at h3
  have hs : Real.sin (2 * (Real.pi / 12)) = 1 / 2 := by
    rw [show 2 * (Real.pi / 12) = Real.pi / 6 by ring, Real.sin_pi_div_six]
  rw [hs] at h3
  have hgt : (1 : ℝ) < (1 / 2 : ℝ) ^ (-(Work.Spaces.gam α)) := by
    refine Real.one_lt_rpow_of_pos_of_lt_one_of_neg (by norm_num) (by norm_num) ?_
    rw [Work.Spaces.gam]
    linarith
  nlinarith [h3, hgt]

/-- The `γ`-leaf of `IsLeafW` forces `a ≥ 1`. -/
theorem one_le_of_isLeafW_leafGamM {α : ℝ} (hα : 0 < α) {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (h : Work.FTS.TransportS.IsLeafW α a ρ) (hρ : ρ = Work.FTS.TransportS.leafGam α) :
    1 ≤ a := by
  rcases h with h1 | h1 | h1
  · exact absurd (h1.symm.trans hρ) (leafEta_ne_leafGamM hα)
  · exact absurd (h1.symm.trans hρ) (leafOne_ne_leafGamM hα)
  · exact h1.1

theorem perTermDthMine : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 M : ℝ) (a b i j : ℕ)
      (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M → a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ → i ≤ a → j ≤ b → ¬(i = 0 ∧ j = 0) →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
          * Work.Spaces.mixed j i A z θ * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
          * Work.Spaces.mixed b a f z θ|
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
  obtain ⟨C1, hC1pos, hC1⟩ := caseLe2Mine
  obtain ⟨C2, hC2pos, hC2⟩ := caseTo4Mine
  obtain ⟨C3, hC3pos, hC3⟩ := caseGe5Mine
  obtain ⟨C4, hC4pos, hC4⟩ := caseExcMine
  have h1 : (0 : ℝ) < C1 + C2 + C3 + C4 + 1 := by linarith
  refine ⟨C1 + C2 + C3 + C4 + 1, h1, ?_⟩
  intro α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hia hjb hne
  have hα : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hvalA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0 := hcoef.val
  have hn4 : Work.FTS.Nonlin.Xn α A ≤ K4 := hcoef.n4
  have hn6 : Work.Spaces.HkNorm α 6 A ≤ K6 := hcoef.n6
  have hbdd : Work.FTS.Nonlin.Xn α f ≤ M := hdat.bdd
  have hK0nn : 0 ≤ K0 := le_trans (abs_nonneg (A 1 (Real.pi / 4)))
    (hvalA 1 (Real.pi / 4) (by norm_num) (by positivity) (by linarith [Real.pi_pos]))
  have hK4nn : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hn4
  have hK6nn : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hn6
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hbdd
  have hSqnn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hX6nn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hαnn : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hBnn : 0 ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
      + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) :=
    add_nonneg (mul_nonneg (by linarith) (by linarith))
      (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
  by_cases h4 : i + j ≤ 4
  · by_cases h2 : i + j ≤ 2
    · obtain ⟨hA, hB, hC⟩ := hC1 α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf
        hia hjb hne h2
      exact ⟨hA, hB, le_trans hC (mul_const_le_mul_constM (by linarith) hαnn hBnn)⟩
    · have h3 : 3 ≤ i + j := by omega
      obtain ⟨hA, hB, hC⟩ := hC2 α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf
        hia hjb hne h3 h4
      exact ⟨hA, hB, le_trans hC (mul_const_le_mul_constM (by linarith) hαnn hBnn)⟩
  · have h5 : 5 ≤ i + j := by omega
    by_cases hi0 : i = 0
    · by_cases hg : ρ = Work.FTS.TransportS.leafGam α
      · have ha1 : 1 ≤ a := one_le_of_isLeafW_leafGamM hα hleaf hg
        have hj5 : j = 5 := by omega
        have hb5 : b = 5 := by omega
        have ha1' : a = 1 := by omega
        obtain ⟨hA, hB, hC⟩ := hC4 α hαmem A f K0 K4 K6 M hcoef hdat
        refine ⟨?_, ?_, ?_⟩
        · simpa only [hi0, hj5, hb5, ha1', hg, Nat.sub_self, Nat.sub_zero] using hA
        · simpa only [hi0, hj5, hb5, ha1', hg, Nat.sub_self, Nat.sub_zero] using hB
        · exact le_trans
            (by simpa only [hi0, hj5, hb5, ha1', hg, Nat.sub_self, Nat.sub_zero] using hC)
            (mul_const_le_mul_constM (by linarith) hαnn hBnn)
      · obtain ⟨hA, hB, hC⟩ := hC3 α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf
          hia hjb hne h5 (fun h => hg h.2)
        exact ⟨hA, hB, le_trans hC (mul_const_le_mul_constM (by linarith) hαnn hBnn)⟩
    · obtain ⟨hA, hB, hC⟩ := hC3 α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf
        hia hjb hne h5 (fun h => hi0 h.1)
      exact ⟨hA, hB, le_trans hC (mul_const_le_mul_constM (by linarith) hαnn hBnn)⟩

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth
