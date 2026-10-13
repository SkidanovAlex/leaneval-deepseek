import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.AeI1Fts.Upsi_P_ae_Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeI1Fts

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 1600000

/-- The level-`0` `ℋ^k`-integrand of `U u = z ∂_z u` is the weighted square
`w z ^ 2 · (U u z θ) ^ 2 · sin(2θ)^{-η}` on `Iθ`. -/
theorem AeI1Fts_HkIntegrand_zero_U (α z θ : ℝ) (u : ℝ → ℝ → ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 (U u) z θ
      = (Work.Spaces.w z) ^ 2 * (U u z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  simp only [Work.Spaces.HkIntegrand]
  norm_num [Finset.sum_range_one]
  rcases eq_or_lt_of_le (Work.FTS.EllipticEst.AngSecond.sin_two_nonneg hθ) with hs | hs
  · rw [← hs]
    have h1 : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 :=
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
    have h2 : (0 : ℝ) ^ (-(Work.Spaces.eta)) = 0 :=
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
    rw [h1, h2, div_zero]
    ring
  · rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hs), mul_pow, mul_pow]
    have hsq : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [sq, ← Real.rpow_add hs]
      congr 1
      rw [Work.Spaces.eta]; ring
    rw [hsq]
    ring

theorem Upsi_P_ae_value_bound (α : ℝ) (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ) (Cχ Cψ Cψ' : ℝ)
    (hS : Work.FTS.EllipticEst.SmoothOpen u) (hψcd : ContDiff ℝ 2 ψ)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u))
    (hV : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ)
    (hχnn : ∀ z ∈ Work.Spaces.Iz, 0 ≤ χ z)
    (hχ : ∀ z ∈ Work.Spaces.Iz, χ z * (1 + z) ^ 4 ≤ Cχ * z ^ 4)
    (hψ : ∀ θ, (ψ θ) ^ 2 ≤ Cψ) (hψ' : ∀ θ, (deriv ψ θ) ^ 2 ≤ Cψ')
    (hCχnn : 0 ≤ Cχ) (hCψnn : 0 ≤ Cψ) (hCψ'nn : 0 ≤ Cψ') :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Spaces.w z) ^ 2 * χ z
          * ∫ θ in Work.Spaces.Iθ,
              (deriv (fun θ' => Work.FTS.EllipticEst.AeI1Fts.U u z θ' * ψ θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ 2 * Cψ * Cχ * (z ^ 2 * ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + 2 * Cψ' * Cχ * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.AeI1Fts.U u) z θ) := by
  have hIθmeas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hIzmeas : MeasurableSet Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]; exact measurableSet_Ici
  have hpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    rw [MeasureTheory.ae_restrict_iff' hIzmeas]
    rw [MeasureTheory.ae_iff]
    have h : {z : ℝ | ¬(z ∈ Work.Spaces.Iz → 0 < z)} = {0} := by
      ext z
      simp only [Set.mem_ofPred_eq, not_imp, Work.Spaces.Iz, Set.mem_Ici,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨hz0, hzlt⟩; exact le_antisymm (not_lt.mp hzlt) hz0
      · rintro rfl; exact ⟨le_refl 0, by norm_num⟩
    rw [h]
    exact MeasureTheory.measure_singleton 0
  have key : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ →
      (Work.Spaces.w z) ^ 2 * χ z
          * ∫ θ in Work.Spaces.Iθ,
              (deriv (fun θ' => U u z θ' * ψ θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ 2 * Cψ * Cχ * (z ^ 2 * ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + 2 * Cψ' * Cχ * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 0 (U u) z θ) := by
    intro z hzpos hVz
    have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hzpos
    have hσnn : ∀ θ ∈ Work.Spaces.Iθ,
        0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      fun θ hθ => Real.rpow_nonneg (Work.FTS.EllipticEst.AngSecond.sin_two_nonneg hθ) _
    -- integrability of the `V`-slot (definitionally the hypothesis `hVz`)
    have hVz' : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (V u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ := by
      simpa only [V] using hVz
    -- integrability of the `U`-slot, from `HkMem α 0 (U u)`
    have hUmem : Work.Spaces.HkMem α 0 (U u) := hU
    have hUint : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ := by
      have h1 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (1 / (Work.Spaces.w z) ^ 2)
            * Work.Spaces.HkIntegrand α 0 (U u) z θ) Work.Spaces.Iθ :=
        (hUmem.1 z hzIz).const_mul _
      refine h1.congr_fun_ae ?_
      refine MeasureTheory.ae_restrict_of_forall_mem hIθmeas fun θ hθ => ?_
      change (1 / (Work.Spaces.w z) ^ 2) * Work.Spaces.HkIntegrand α 0 (U u) z θ
          = (U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      rw [AeI1Fts_HkIntegrand_zero_U α z θ u hθ]
      have hwne : (Work.Spaces.w z) ^ 2 ≠ 0 := by
        have : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
        positivity
      rw [one_div, mul_assoc, inv_mul_cancel_left₀ hwne]
    -- integrability of the majorant
    have hMint : MeasureTheory.IntegrableOn
        (fun θ : ℝ => 2 * Cψ * ((V u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + 2 * Cψ' * ((U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        Work.Spaces.Iθ := by
      have h1 := hVz'.const_mul (2 * Cψ)
      have h2 := hUint.const_mul (2 * Cψ')
      exact h1.add h2
    -- nonnegativity of the two target integrals
    have hBpnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      MeasureTheory.setIntegral_nonneg hIθmeas fun θ hθ =>
        mul_nonneg (sq_nonneg _) (hσnn θ hθ)
    have hGnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (U u) z θ :=
      MeasureTheory.setIntegral_nonneg hIθmeas fun θ _ =>
        Work.Spaces.HkIntegrand_nonneg α 0 (U u) z θ
    by_cases hA : (∫ θ in Work.Spaces.Iθ,
        (deriv (fun θ' => U u z θ' * ψ θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) = 0
    · -- Junk / vanishing case: the left-hand side is `0` and the right-hand side is `≥ 0`.
      rw [hA, mul_zero]
      have h1 : 0 ≤ 2 * Cψ * Cχ * (z ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCψnn) hCχnn)
          (mul_nonneg (sq_nonneg z) hBpnn)
      have h2 : 0 ≤ 2 * Cψ' * Cχ
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (U u) z θ) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCψ'nn) hCχnn) hGnn
      linarith
    · -- Honest case: the θ-slice is integrable, and the product rule applies.
      have hg1int : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (deriv (fun θ' => U u z θ' * ψ θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
        by_contra h
        exact hA (MeasureTheory.integral_undef h)
      -- the product rule, almost everywhere in `θ` (the two endpoints are the only exceptions)
      have hEq : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          (deriv (fun θ' => U u z θ' * ψ θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          = (V u z θ * ψ θ + U u z θ * deriv ψ θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        rw [MeasureTheory.ae_restrict_iff' hIθmeas]
        rw [MeasureTheory.ae_iff]
        refine MeasureTheory.measure_mono_null (t := ({0} ∪ {Real.pi / 2} : Set ℝ)) ?_ ?_
        · intro θ hθ
          rw [Set.mem_ofPred_eq, not_imp, Work.Spaces.Iθ, Set.mem_Icc] at hθ
          rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_singleton_iff]
          by_cases h0 : θ = 0
          · exact Or.inl h0
          · right
            by_contra hpi
            exact hθ.2 (by
              rw [deriv_U_mul_eq hS hψcd hzpos
                ⟨lt_of_le_of_ne hθ.1.1 (Ne.symm h0), lt_of_le_of_ne hθ.1.2 hpi⟩])
        · exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
            (MeasureTheory.measure_singleton (Real.pi / 2))
      have hIntEq : (∫ θ in Work.Spaces.Iθ,
            (deriv (fun θ' => U u z θ' * ψ θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          = ∫ θ in Work.Spaces.Iθ,
              (V u z θ * ψ θ + U u z θ * deriv ψ θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        MeasureTheory.setIntegral_congr_ae hIθmeas
          ((MeasureTheory.ae_restrict_iff' hIθmeas).mp hEq)
      have href : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (V u z θ * ψ θ + U u z θ * deriv ψ θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
        hg1int.congr_fun_ae hEq
      -- pointwise bound of the reference integrand by the majorant
      have hpt : ∀ θ ∈ Work.Spaces.Iθ,
          (V u z θ * ψ θ + U u z θ * deriv ψ θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            ≤ 2 * Cψ * ((V u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + 2 * Cψ' * ((U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
        intro θ hθ
        have hσ : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := hσnn θ hθ
        have h1 : (V u z θ * ψ θ + U u z θ * deriv ψ θ) ^ 2
            ≤ 2 * (V u z θ * ψ θ) ^ 2 + 2 * (U u z θ * deriv ψ θ) ^ 2 := by
          nlinarith [sq_nonneg (V u z θ * ψ θ - U u z θ * deriv ψ θ)]
        have h2 : (V u z θ * ψ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            ≤ Cψ * ((V u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
          have hAux : (V u z θ * ψ θ) ^ 2 ≤ (V u z θ) ^ 2 * Cψ := by
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_left (hψ θ) (sq_nonneg _)
          calc (V u z θ * ψ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              ≤ ((V u z θ) ^ 2 * Cψ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
                mul_le_mul_of_nonneg_right hAux hσ
            _ = Cψ * ((V u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
        have h3 : (U u z θ * deriv ψ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            ≤ Cψ' * ((U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
          have hAux : (U u z θ * deriv ψ θ) ^ 2 ≤ (U u z θ) ^ 2 * Cψ' := by
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_left (hψ' θ) (sq_nonneg _)
          calc (U u z θ * deriv ψ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              ≤ ((U u z θ) ^ 2 * Cψ') * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
                mul_le_mul_of_nonneg_right hAux hσ
            _ = Cψ' * ((U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
        calc (V u z θ * ψ θ + U u z θ * deriv ψ θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            ≤ (2 * (V u z θ * ψ θ) ^ 2 + 2 * (U u z θ * deriv ψ θ) ^ 2)
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
              mul_le_mul_of_nonneg_right h1 hσ
          _ = 2 * ((V u z θ * ψ θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
                + 2 * ((U u z θ * deriv ψ θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
          _ ≤ 2 * (Cψ * ((V u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
                + 2 * (Cψ' * ((U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) :=
              add_le_add (mul_le_mul_of_nonneg_left h2 (by norm_num))
                (mul_le_mul_of_nonneg_left h3 (by norm_num))
          _ = 2 * Cψ * ((V u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
                + 2 * Cψ' * ((U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
              ring
      have hmono : (∫ θ in Work.Spaces.Iθ,
              (V u z θ * ψ θ + U u z θ * deriv ψ θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          ≤ ∫ θ in Work.Spaces.Iθ,
              (2 * Cψ * ((V u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
                + 2 * Cψ' * ((U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) :=
        MeasureTheory.integral_mono_ae href hMint
          (MeasureTheory.ae_restrict_of_forall_mem hIθmeas hpt)
      have hmajeq : (∫ θ in Work.Spaces.Iθ,
              (2 * Cψ * ((V u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
                + 2 * Cψ' * ((U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))))
          = 2 * Cψ * (∫ θ in Work.Spaces.Iθ,
                (V u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + 2 * Cψ' * (∫ θ in Work.Spaces.Iθ,
                (U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
        rw [MeasureTheory.integral_add (hVz'.const_mul (2 * Cψ)) (hUint.const_mul (2 * Cψ')),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      have hA_le : (∫ θ in Work.Spaces.Iθ,
              (deriv (fun θ' => U u z θ' * ψ θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          ≤ 2 * Cψ * (∫ θ in Work.Spaces.Iθ,
                (V u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + 2 * Cψ' * (∫ θ in Work.Spaces.Iθ,
                (U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
        rw [hIntEq, ← hmajeq]
        exact hmono
      -- the two slot identities
      have hVfact : (∫ θ in Work.Spaces.Iθ,
            (V u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          = z ^ 2 * ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_congr_fun hIθmeas fun θ _ => ?_
        show (V u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            = z ^ 2 * ((Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        simp only [V]
        ring
      have hUfact : (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (U u z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (U u) z θ := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_congr_fun hIθmeas fun θ hθ => ?_
        rw [AeI1Fts_HkIntegrand_zero_U α z θ u hθ]
        ring
      have hBvnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
          (V u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        MeasureTheory.setIntegral_nonneg hIθmeas fun θ hθ =>
          mul_nonneg (sq_nonneg _) (hσnn θ hθ)
      have hBunn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
          (U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        MeasureTheory.setIntegral_nonneg hIθmeas fun θ hθ =>
          mul_nonneg (sq_nonneg _) (hσnn θ hθ)
      have hχz : χ z ≤ Cχ := by
        have h1 : χ z * (1 + z) ^ 4 ≤ Cχ * z ^ 4 := hχ z hzIz
        have hzle : z ^ 4 ≤ (1 + z) ^ 4 := pow_le_pow_left₀ (le_of_lt hzpos) (by linarith) 4
        have h2 : Cχ * z ^ 4 ≤ Cχ * (1 + z) ^ 4 := mul_le_mul_of_nonneg_left hzle hCχnn
        have h3 : χ z * (1 + z) ^ 4 ≤ Cχ * (1 + z) ^ 4 := le_trans h1 h2
        exact (mul_le_mul_iff_left₀ (by positivity : (0 : ℝ) < (1 + z) ^ 4)).mp h3
      have hwχz : (Work.Spaces.w z) ^ 2 * χ z ≤ Cχ := by
        have h1 : χ z * (1 + z) ^ 4 ≤ Cχ * z ^ 4 := hχ z hzIz
        have hwz : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
          rw [Work.Spaces.w, div_pow]
          ring
        rw [hwz, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 4)]
        linarith
      calc (Work.Spaces.w z) ^ 2 * χ z
            * (∫ θ in Work.Spaces.Iθ,
                (deriv (fun θ' => U u z θ' * ψ θ') θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          ≤ (Work.Spaces.w z) ^ 2 * χ z
              * (2 * Cψ * (∫ θ in Work.Spaces.Iθ,
                    (V u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
                + 2 * Cψ' * (∫ θ in Work.Spaces.Iθ,
                    (U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) :=
            mul_le_mul_of_nonneg_left hA_le (mul_nonneg (sq_nonneg _) (hχnn z hzIz))
        _ = 2 * Cψ * ((Work.Spaces.w z) ^ 2 * χ z
                * (∫ θ in Work.Spaces.Iθ,
                    (V u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
              + 2 * Cψ' * ((Work.Spaces.w z) ^ 2 * χ z
                * (∫ θ in Work.Spaces.Iθ,
                    (U u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by ring
        _ ≤ 2 * Cψ * (Cχ * (z ^ 2 * (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))))
              + 2 * Cψ' * (Cχ * (∫ θ in Work.Spaces.Iθ,
                  Work.Spaces.HkIntegrand α 0 (U u) z θ)) := by
            refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by linarith))
              (mul_le_mul_of_nonneg_left ?_ (by linarith))
            · rw [hVfact]
              exact mul_le_mul_of_nonneg_right hwχz (mul_nonneg (sq_nonneg z) hBpnn)
            · rw [show (Work.Spaces.w z) ^ 2 * χ z
                    * (∫ θ in Work.Spaces.Iθ, (U u z θ) ^ 2
                        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
                  = χ z * ((Work.Spaces.w z) ^ 2
                    * (∫ θ in Work.Spaces.Iθ, (U u z θ) ^ 2
                        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) by ring,
                hUfact]
              exact mul_le_mul_of_nonneg_right hχz hGnn
        _ = 2 * Cψ * Cχ * (z ^ 2 * (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
              + 2 * Cψ' * Cχ * (∫ θ in Work.Spaces.Iθ,
                  Work.Spaces.HkIntegrand α 0 (U u) z θ) := by ring
  filter_upwards [hV, hpos] with z hVz hzpos
  exact key z hzpos hVz

end Work.FTS.EllipticEst.AeI1Fts
