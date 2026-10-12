import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.KinPSuperadd.Slices
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.KinPSuperadd

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The excited-particle count `cnPlus ℓ Φ = Σ_i ∫_{abox N ℓ} (QᵢΦ)²` is
nonnegative (it is a sum of box-`L²` norms of the projected states). -/
lemma cnPlus_nonneg_aux {N : ℕ} (ℓ : ℝ) (Φ : X N → ℝ) : 0 ≤ cnPlus ℓ Φ := by
  unfold Submission.BoseGases.cnPlus
  exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))

/-- The diagonal (one-particle-sum) mode form `pDiagForm s F` is nonnegative for
`s > 0` and a nonnegative symbol `F`: it is the sum over the slots of
`(2π)⁻³∫_p F‖p‖·(s³)⁻¹∫_x ‖pSlotAmp‖²`, each summand nonnegative. -/
lemma pDiagForm_nonneg {s : ℝ} (hs : 0 < s) (F : ℝ → ℝ) (hF : ∀ r, 0 ≤ F r)
    {N : ℕ} (Ψ : X N → ℝ) : 0 ≤ pDiagForm s F Ψ := by
  unfold Submission.BoseGases.pDiagForm
  refine Finset.sum_nonneg (fun i _ => ?_)
  refine mul_nonneg (inv_nonneg.mpr ?_) ?_
  · positivity
  · refine integral_nonneg (fun p => mul_nonneg (hF ‖p‖) ?_)
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hs.le 3))
      (integral_nonneg (fun x => sq_nonneg _))

/-- The faithful slot word `diagSlotWord s c₀ cgap = cgap·cnPlus + pDiagForm`
is nonnegative for `s > 0`, `cgap ≥ 0`. -/
lemma diagSlotWord_nonneg (s c₀ cgap : ℝ) (hcgap : 0 ≤ cgap) (hs : 0 < s)
    (N : ℕ) (Ψ : X N → ℝ) : 0 ≤ diagSlotWord s c₀ cgap N Ψ := by
  have hdef : diagSlotWord s c₀ cgap N Ψ
      = cgap * cnPlus s Ψ + pDiagForm s (fsKinCoeff c₀) Ψ := rfl
  rw [hdef]
  exact add_nonneg (mul_nonneg hcgap (cnPlus_nonneg_aux s Ψ))
    (pDiagForm_nonneg hs (fsKinCoeff c₀) (fsKinCoeff_nonneg c₀) Ψ)

theorem rayleigh_diagSlotWord {N : ℕ} {s R μ c₀ cgap : ℝ}
    {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : BoseGases.IsRadial v)
    (hv_memL1 : MeasureTheory.MemLp v 1)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * Submission.BoseGases.chiR0) (hμ : 0 < μ)
    (hcgap : 0 ≤ cgap)
    (hint : ∀ (M : ℕ) (Ψ : Submission.BoseGases.X M → ℝ), ContDiff ℝ ∞ Ψ →
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ∑ i : Fin M, (s ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox M s,
            ‖Submission.BoseGases.pSlotAmp s p Ψ i x‖ ^ 2))
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) :
    @Work.KinPSuperadd.slotEB s μ (Submission.BoseGases.wPairC s v)
        (Submission.BoseGases.wPairC s (Submission.BoseGases.g0 v h))
        (Work.KinPSuperadd.diagSlotWord s c₀ cgap) N *
      (∫ x in Submission.BoseGases.abox N s, (Ψ x) ^ 2)
      ≤ @Work.KinPSuperadd.blockE s μ (Submission.BoseGases.wPairC s v)
        (Submission.BoseGases.wPairC s (Submission.BoseGases.g0 v h))
        (Work.KinPSuperadd.diagSlotWord s c₀ cgap) N Ψ := by
  have hΨs : ContDiff ℝ ∞ Ψ := hΨ
  by_cases hz : (∫ x in abox N s, (Ψ x) ^ 2) = 0
  · -- degenerate case: the state vanishes in box `L²`; both sides are `0`.
    rw [hz, mul_zero, blockE_eq]
    have hl := qLHSword_chosen_lower (N := N) hR hv_nonneg hvrad hv_memL1 hv_supp h
      hs hRs hμ.le (Φ := Ψ) hΨs
    rw [hz] at hl
    have hk := diagSlotWord_nonneg s c₀ cgap hcgap hs N Ψ
    linarith
  · have hpos : 0 < ∫ x in abox N s, (Ψ x) ^ 2 :=
      lt_of_le_of_ne (integral_nonneg (fun x => sq_nonneg (Ψ x))) (Ne.symm hz)
    have hne : Ψ ≠ 0 := fun h0 => hz (by simp [h0])
    -- the quotient range is bounded below (the word is nonnegative and the
    -- potential word is bounded below by `−sboxC·‖·‖²`)
    have hbdd : BddBelow (Set.range (fun Φ : CSBox N s =>
        blockE s μ (wPairC s v) (wPairC s (g0 v h)) (diagSlotWord s c₀ cgap) N (Φ : X N → ℝ) /
          (∫ x in abox N s, ((Φ : X N → ℝ) x) ^ 2))) := by
      refine ⟨-sboxC N μ v, ?_⟩
      rintro y ⟨Φ, rfl⟩
      dsimp only
      rw [blockE_eq, le_div_iff₀ Φ.sq_pos]
      have hl := qLHSword_chosen_lower (N := N) hR hv_nonneg hvrad hv_memL1 hv_supp h
        hs hRs hμ.le (Φ := (Φ : X N → ℝ)) Φ.contDiff
      have hk := diagSlotWord_nonneg s c₀ cgap hcgap hs N (Φ : X N → ℝ)
      linarith
    have hle : slotEB s μ (wPairC s v) (wPairC s (g0 v h)) (diagSlotWord s c₀ cgap) N
        ≤ blockE s μ (wPairC s v) (wPairC s (g0 v h)) (diagSlotWord s c₀ cgap) N Ψ /
          (∫ x in abox N s, (Ψ x) ^ 2) := by
      unfold slotEB
      exact ciInf_le hbdd ⟨Ψ, hΨs, hne, hpos⟩
    exact (le_div_iff₀ hpos).mp hle

end Work.KinPSuperadd
