import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.DefsC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory Filter
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseBoxFock.PCFU

/-- The periodised weight, paired against a smooth compactly supported `Ψ`, equals `ℓ³` times the
`L¹` weight paired against the periodisation `latPerC ℓ Ψ` of `Ψ`.  (Folding/Parseval on the
lattice cell: on `supp Ψ` the periodisation of `W` is the finite sum over
`Work.BoseBoxFock.LatFourier.latFinSet ℓ (R + ρ)` (`ρ` a support radius of `Ψ`), so the left side is
`ℓ³ Σ_{m ∈ S} ∫ Ψ(z) W(z + ℓ • latVec m) dz`; substitute `z ↦ z + ℓ • latVec m`
(`MeasureTheory.integral_add_left_eq_self`) and use that for `W z ≠ 0` the terms of
`Σ_{m ∈ S} Ψ(z - ℓ • latVec m)` are all the nonvanishing terms of `Σ'_m Ψ(z + ℓ • latVec m)`
(reindex by `m ↦ -m`, `Equiv.tsum_eq`).) -/
theorem slotPeriodisationReduction {ℓ R : ℝ} (hℓ : 0 < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W)
    (hWs : ∀ x, R ≤ ‖x‖ → W x = 0)
    {Ψ : EuclideanSpace ℝ (Fin 3) → ℂ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΨs : HasCompactSupport Ψ) :
    ∫ z, Ψ z * Work.BoseBoxFock.latPer3 ℓ W z
      = ((ℓ ^ 3 : ℝ) : ℂ) *
        ∫ z, ((W z : ℝ) : ℂ) * Work.BoseBoxFock.L1Tails.latPerC ℓ Ψ z := by
  classical
  -- ## 0. Two elementary data: a support radius `ρ` and a sup bound `CΨ` for `Ψ`.
  have hsupp : ∃ ρ : ℝ, ∀ z : E3, ρ < ‖z‖ → Ψ z = 0 := by
    obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℝ, ∀ x : E3, x ∈ tsupport Ψ → ‖x‖ ≤ ρ₀ :=
      (hΨs.isCompact.isBounded).exists_norm_le
    exact ⟨max ρ₀ 1, fun z hz => image_eq_zero_of_notMem_tsupport (fun hmem => by
      have h1 := hρ₀ z hmem
      have h2 : ρ₀ < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
      linarith)⟩
  obtain ⟨ρ, hρ⟩ := hsupp
  have hΨbdd : ∃ C : ℝ, ∀ z : E3, ‖Ψ z‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E3) ρ).exists_bound_of_continuousOn
      hΨ.continuous.continuousOn
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : ‖z‖ ≤ ρ
    · refine le_trans (hC z ?_) (le_max_left _ _)
      rwa [Metric.mem_closedBall, dist_zero_right]
    · rw [hρ z (lt_of_not_ge hz), norm_zero]
      exact le_max_right _ _
  obtain ⟨CΨ, hCΨ⟩ := hΨbdd
  -- ## 1. The finite set of lattice points that can contribute.
  -- `ρ` is a support radius of `Ψ`, `R` one of `W`; a term with `m ∉ S` has the shifted
  -- argument outside the support of `W` (left side) resp. of `Ψ` (right side).
  let S : Finset (Fin 3 → ℤ) := Work.BoseBoxFock.LatFourier.latBall ((R + ρ) / ℓ)
  have hSmem : ∀ m : Fin 3 → ℤ, m ∈ S ↔ ‖Work.BoseBoxFock.latVec m‖ ≤ (R + ρ) / ℓ :=
    fun m => Work.BoseBoxFock.LatFourier.mem_latBall
  have hSfar : ∀ m : Fin 3 → ℤ, m ∉ S → R + ρ < ℓ * ‖Work.BoseBoxFock.latVec m‖ := by
    intro m hm
    have h2 : (R + ρ) / ℓ < ‖Work.BoseBoxFock.latVec m‖ :=
      lt_of_not_ge (fun hc => hm ((hSmem m).mpr hc))
    have h3 : R + ρ < ‖Work.BoseBoxFock.latVec m‖ * ℓ := (div_lt_iff₀ hℓ).mp h2
    linarith
  -- ## 2. The left integrand is the finite sum `ℓ³ Σ_{m ∈ S} Ψ z W (z + ℓ•m)`, pointwise.
  have hptL : ∀ z : E3, Ψ z * Work.BoseBoxFock.latPer3 ℓ W z
      = ((ℓ ^ 3 : ℝ) : ℂ) * ∑ m ∈ S, Ψ z * ((W (z + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) := by
    intro z
    have hunfold : Work.BoseBoxFock.latPer3 ℓ W z
        = ((ℓ ^ 3 : ℝ) : ℂ) * ∑' m : Fin 3 → ℤ,
            ((W (z + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) := rfl
    rw [hunfold]
    by_cases hz : ‖z‖ ≤ ρ
    · -- on the ball of radius `ρ` the periodisation of `W` is the finite sum over `S`
      have hsum : (∑' m : Fin 3 → ℤ, ((W (z + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ))
          = ∑ m ∈ S, ((W (z + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) := by
        refine tsum_eq_sum (s := S) (fun m hm => ?_)
        have hgt : R < ‖z + ℓ • Work.BoseBoxFock.latVec m‖ := by
          have h2 : R + ρ < ℓ * ‖Work.BoseBoxFock.latVec m‖ := hSfar m hm
          have h3 : ℓ * ‖Work.BoseBoxFock.latVec m‖
              ≤ ‖z + ℓ • Work.BoseBoxFock.latVec m‖ + ‖z‖ := by
            calc ℓ * ‖Work.BoseBoxFock.latVec m‖
                = ‖ℓ • Work.BoseBoxFock.latVec m‖ :=
                  (Work.BoseBoxFock.LatFourier.latVec_norm_smul ℓ hℓ.le m).symm
              _ = ‖(z + ℓ • Work.BoseBoxFock.latVec m) - z‖ := by congr 1; abel
              _ ≤ ‖z + ℓ • Work.BoseBoxFock.latVec m‖ + ‖z‖ := norm_sub_le _ _
          linarith
        simp [hWs _ hgt.le]
      rw [hsum]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    · -- outside the support of `Ψ` both sides vanish
      have hzρ : ρ < ‖z‖ := lt_of_not_ge hz
      simp [hρ z hzρ]
  -- ## 3. Integrability of the left summands (`Ψ` is bounded, the translate of `W` is `L¹`).
  have hΨmeas : AEStronglyMeasurable Ψ volume := hΨ.continuous.aestronglyMeasurable
  have hΨbdda : ∀ᵐ z : E3 ∂volume, ‖Ψ z‖ ≤ CΨ := Eventually.of_forall hCΨ
  have hIntL : ∀ m : Fin 3 → ℤ, Integrable (fun z : E3 =>
      Ψ z * ((W (z + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ)) := by
    intro m
    have hg : Integrable (fun z : E3 =>
        ((W (z + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ)) volume :=
      (hW.comp_add_right (ℓ • Work.BoseBoxFock.latVec m)).ofReal
    exact hg.bdd_mul hΨmeas hΨbdda
  -- ## 4. The left integral as `ℓ³ Σ_{m ∈ S} ∫ Ψ z W (z + ℓ•m)`.
  have hL : (∫ z, Ψ z * Work.BoseBoxFock.latPer3 ℓ W z)
      = ((ℓ ^ 3 : ℝ) : ℂ) * ∑ m ∈ S,
          ∫ z, Ψ z * ((W (z + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) := by
    rw [show (∫ z, Ψ z * Work.BoseBoxFock.latPer3 ℓ W z)
        = ∫ z, ((ℓ ^ 3 : ℝ) : ℂ) * ∑ m ∈ S,
            Ψ z * ((W (z + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ)
        from integral_congr_ae (Eventually.of_forall hptL)]
    have h1 : (∫ z, ((ℓ ^ 3 : ℝ) : ℂ) * ∑ m ∈ S,
          Ψ z * ((W (z + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ))
        = ((ℓ ^ 3 : ℝ) : ℂ) * ∫ z, ∑ m ∈ S,
            Ψ z * ((W (z + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) :=
      integral_const_mul _ _
    rw [h1]
    congr 1
    exact integral_finsetSum (s := S) (f := fun m z =>
      Ψ z * ((W (z + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ)) (fun m _ => hIntL m)
  -- ## 5. The right integrand is the finite sum `Σ_{m ∈ S} W z Ψ (z - ℓ•m)`.
  have hIntR : ∀ m : Fin 3 → ℤ, Integrable (fun z : E3 =>
      ((W z : ℝ) : ℂ) * Ψ (z - ℓ • Work.BoseBoxFock.latVec m)) := by
    intro m
    have hf : AEStronglyMeasurable (fun z : E3 => Ψ (z - ℓ • Work.BoseBoxFock.latVec m)) volume :=
      (hΨ.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
    have hbd : ∀ᵐ z : E3 ∂volume, ‖Ψ (z - ℓ • Work.BoseBoxFock.latVec m)‖ ≤ CΨ :=
      Eventually.of_forall (fun z => hCΨ _)
    simpa [mul_comm] using (hW.ofReal).bdd_mul hf hbd
  have hptR : ∀ z : E3, ((W z : ℝ) : ℂ) * Work.BoseBoxFock.L1Tails.latPerC ℓ Ψ z
      = ∑ m ∈ S, ((W z : ℝ) : ℂ) * Ψ (z - ℓ • Work.BoseBoxFock.latVec m) := by
    intro z
    by_cases hWz : W z = 0
    · simp [hWz]
    · have hzR : ‖z‖ < R := lt_of_not_ge (fun h => hWz (hWs z h))
      -- reindex `m ↦ -m` and expand the (then finite) periodisation of `Ψ`
      have hexp : Work.BoseBoxFock.L1Tails.latPerC ℓ Ψ z
          = ∑ m ∈ S, Ψ (z - ℓ • Work.BoseBoxFock.latVec m) := by
        have hunfold : Work.BoseBoxFock.L1Tails.latPerC ℓ Ψ z
            = ∑' m : Fin 3 → ℤ, Ψ (z + ℓ • Work.BoseBoxFock.latVec m) := rfl
        rw [hunfold]
        have h1 : (∑' m : Fin 3 → ℤ, Ψ (z + ℓ • Work.BoseBoxFock.latVec m))
            = ∑' m : Fin 3 → ℤ, Ψ (z - ℓ • Work.BoseBoxFock.latVec m) := by
          calc (∑' m : Fin 3 → ℤ, Ψ (z + ℓ • Work.BoseBoxFock.latVec m))
              = ∑' m : Fin 3 → ℤ, Ψ (z + ℓ • Work.BoseBoxFock.latVec (-m)) :=
                (Equiv.tsum_eq (Equiv.neg (Fin 3 → ℤ))
                  (fun m : Fin 3 → ℤ => Ψ (z + ℓ • Work.BoseBoxFock.latVec m))).symm
            _ = ∑' m : Fin 3 → ℤ, Ψ (z - ℓ • Work.BoseBoxFock.latVec m) :=
                tsum_congr (fun m => by
                  congr 1
                  have hv : Work.BoseBoxFock.latVec (-m) = -Work.BoseBoxFock.latVec m := by
                    ext i; simp [Work.BoseBoxFock.latVec]
                  rw [hv, smul_neg]; abel)
        rw [h1]
        refine tsum_eq_sum (s := S) (fun m hm => ?_)
        have hgt : ρ < ‖z - ℓ • Work.BoseBoxFock.latVec m‖ := by
          have h2 : R + ρ < ℓ * ‖Work.BoseBoxFock.latVec m‖ := hSfar m hm
          have h3 : ℓ * ‖Work.BoseBoxFock.latVec m‖
              ≤ ‖z - ℓ • Work.BoseBoxFock.latVec m‖ + ‖z‖ := by
            calc ℓ * ‖Work.BoseBoxFock.latVec m‖ = ‖-(ℓ • Work.BoseBoxFock.latVec m)‖ := by
                  rw [norm_neg, Work.BoseBoxFock.LatFourier.latVec_norm_smul ℓ hℓ.le m]
              _ = ‖(z - ℓ • Work.BoseBoxFock.latVec m) - z‖ := by congr 1; abel
              _ ≤ ‖z - ℓ • Work.BoseBoxFock.latVec m‖ + ‖z‖ := norm_sub_le _ _
          linarith
        rw [hρ _ hgt]
      rw [hexp, Finset.mul_sum]
  -- ## 6. The right integral as `Σ_{m ∈ S} ∫ W z Ψ (z - ℓ•m)`.
  have hR : (∫ z, ((W z : ℝ) : ℂ) * Work.BoseBoxFock.L1Tails.latPerC ℓ Ψ z)
      = ∑ m ∈ S, ∫ z, ((W z : ℝ) : ℂ) * Ψ (z - ℓ • Work.BoseBoxFock.latVec m) := by
    rw [show (∫ z, ((W z : ℝ) : ℂ) * Work.BoseBoxFock.L1Tails.latPerC ℓ Ψ z)
        = ∫ z, ∑ m ∈ S, ((W z : ℝ) : ℂ) * Ψ (z - ℓ • Work.BoseBoxFock.latVec m)
        from integral_congr_ae (Eventually.of_forall hptR)]
    exact integral_finsetSum (s := S) (f := fun m z =>
      ((W z : ℝ) : ℂ) * Ψ (z - ℓ • Work.BoseBoxFock.latVec m)) (fun m _ => hIntR m)
  -- ## 7. Term by term: `∫ Ψ z W (z + ℓ•m) = ∫ W z Ψ (z - ℓ•m)` by the shift substitution.
  have hTerm : ∀ m ∈ S, (∫ z, Ψ z * ((W (z + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ))
      = ∫ z, ((W z : ℝ) : ℂ) * Ψ (z - ℓ • Work.BoseBoxFock.latVec m) := by
    intro m _
    have h := integral_add_left_eq_self (μ := volume)
      (fun u : E3 => ((W u : ℝ) : ℂ) * Ψ (u - ℓ • Work.BoseBoxFock.latVec m))
      (ℓ • Work.BoseBoxFock.latVec m)
    have hfun : (fun x : E3 => (fun u : E3 => ((W u : ℝ) : ℂ)
          * Ψ (u - ℓ • Work.BoseBoxFock.latVec m))
          ((ℓ • Work.BoseBoxFock.latVec m) + x))
        = fun x : E3 => Ψ x * ((W (x + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ) := by
      funext x
      show ((W ((ℓ • Work.BoseBoxFock.latVec m) + x) : ℝ) : ℂ)
          * Ψ (((ℓ • Work.BoseBoxFock.latVec m) + x) - ℓ • Work.BoseBoxFock.latVec m)
        = Ψ x * ((W (x + ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ)
      rw [show (ℓ • Work.BoseBoxFock.latVec m) + x = x + ℓ • Work.BoseBoxFock.latVec m from by abel,
          show (x + ℓ • Work.BoseBoxFock.latVec m) - ℓ • Work.BoseBoxFock.latVec m = x from by abel]
      ring
    rw [hfun] at h
    exact h
  rw [hL, hR]
  congr 1
  exact Finset.sum_congr rfl (fun m hm => hTerm m hm)

end Work.BoseBoxFock.PCFU
