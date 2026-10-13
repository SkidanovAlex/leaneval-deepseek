import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarDefs
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarHyp
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.FarSlots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB.FEL

open Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false

/-- A monotone comparison of a sub-interval integral against an `Iθ`-integrable dominating
function.  Note that no measurability of `f` is needed: on the smaller interval we only use
`integral_mono_of_nonneg`, while on `Iθ` the dominating function is integrable by hypothesis
and enters `setIntegral_mono_set`. -/
private lemma integral_Icc_le_Iθ {f gD : ℝ → ℝ} {a b : ℝ}
    (hG : MeasureTheory.IntegrableOn gD Work.Spaces.Iθ)
    (hnn : ∀ θ ∈ Set.Icc a b, 0 ≤ f θ)
    (hle : ∀ θ ∈ Set.Icc a b, f θ ≤ gD θ)
    (hs : Set.Icc a b ⊆ Work.Spaces.Iθ)
    (hGn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ gD θ) :
    ∫ θ in Set.Icc a b, f θ ≤ ∫ θ in Work.Spaces.Iθ, gD θ := by
  have h1 : ∫ θ in Set.Icc a b, f θ ≤ ∫ θ in Set.Icc a b, gD θ :=
    MeasureTheory.integral_mono_of_nonneg (μ := MeasureTheory.volume.restrict (Set.Icc a b))
      (by filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
            measurableSet_Icc] with θ hθ
          exact hnn θ hθ)
      (hG.mono_set hs)
      (by filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
            measurableSet_Icc] with θ hθ
          exact hle θ hθ)
  have h2 : ∫ θ in Set.Icc a b, gD θ ≤ ∫ θ in Work.Spaces.Iθ, gD θ :=
    MeasureTheory.setIntegral_mono_set hG
      (by filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
            measurableSet_Icc] with θ hθ
          exact hGn θ hθ)
      (Filter.Eventually.of_forall fun θ hθ => hs hθ)
  exact le_trans h1 h2

/-- **The `u`-slots on a sub-interval of the far window.**  Under `FarHyp k γ u g` (`k ≥ 2`)
and for every `j ≤ k+1` and every `[a,b] ⊆ [3π/8, π/2]`, the `j`-th `u`-slot against the top
weight `qW k γ = sin(2θ)^(2k-γ)` is bounded by `FarR k γ u g`.

Route: `Work.FTS.EllipticEst.remov.TopCoreB.u_slot_le_FarR` (already **proved**) gives the
same bound with `farSet` in place of `Set.Icc a b`.  It remains to transfer the bound to the
sub-interval: by `MeasureTheory.setIntegral_mono_set` (`∫_{Icc a b} f ≤ ∫_{farSet} f`) applied
to the nonnegative integrand `fun θ => (iteratedDeriv j u θ)^2 * qW k γ θ`, which needs
`IntegrableOn` of that integrand on `farSet` — obtained by dominating it with the (integrable)
slot integrand of `FarHyp`:
`qW k γ θ = sin(2θ)^(2k-γ) ≤ sin(2θ)^(2j-4-γ)` for `3 ≤ j ≤ k+1` (`FarSlots.qW_le_slotWeight`),
`≤ sin(2θ)^(-η)` for `j = 2` (`FarSlots.qW_le_sEta`), `≤ 1` for `j ≤ 1` (`FarSlots.qW_le_one`),
using `H3`/`H4`/`H6` of `FarHyp` for the domination function, plus a.e. strong measurability of
`(u^{(j)})²·qW` on `farSet` (`u^{(j)}` is continuous on the *open* interval `(0, π/2) ⊆ ℝ`
containing `[3π/8, b]`). -/
theorem uSlot_Icc_le_FarR (k : ℕ) (hk : 2 ≤ k) :
    ∀ (γ : ℝ) (u g : ℝ → ℝ),
      Work.FTS.EllipticEst.remov.TopCoreB.FarHyp k γ u g →
      ∀ j : ℕ, j ≤ k + 1 →
        ∀ a b : ℝ, 3 * Real.pi / 8 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
          (∫ θ in Set.Icc a b, (iteratedDeriv j u θ) ^ 2
              * Work.FTS.EllipticEst.remov.TopCoreB.qW k γ θ)
            ≤ Work.FTS.EllipticEst.remov.TopCoreB.FarR k γ u g := by
  intro γ u g h j hj a b ha hab hb
  have hγ2 : γ ≤ 5 / 4 := h.hγ2
  -- the sub-interval sits inside `Iθ`
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iθ := by
    intro θ hθ
    exact ⟨by linarith [hθ.1, ha, Real.pi_pos], by linarith [hθ.2, hb, Real.pi_pos]⟩
  -- nonnegativity of every summand of `FarR`
  have hR2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
  have hR3 : 0 ≤ ∑ j' ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
      (iteratedDeriv j' u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (j' : ℝ) - 4 - γ) :=
    Finset.sum_nonneg (fun j' _ => MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (slotWeight_nonneg hθ)))
  have hR4 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
      * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
  have hR5 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hR6 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  rcases lt_or_ge j 3 with hjlt | hjge
  · interval_cases j
    · -- `j = 0`: dominate by `u²`
      have hmain : ∫ θ in Set.Icc a b, (iteratedDeriv 0 u θ) ^ 2 * qW k γ θ
          ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
        integral_Icc_le_Iθ h.hH6
          (fun θ hθ => mul_nonneg (sq_nonneg _) (qW_nonneg (hsub hθ)))
          (fun θ hθ => by
            rw [iteratedDeriv_zero]
            exact mul_le_of_le_one_right (sq_nonneg _) (qW_le_one hk hγ2 (hsub hθ)))
          hsub (fun θ _ => sq_nonneg _)
      have hfin : ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 ≤ FarR k γ u g := by
        simp only [FarR]
        linarith [hR2, hR3, hR4, hR5]
      exact le_trans hmain hfin
    · -- `j = 1`: dominate by `(u')²`
      have hmain : ∫ θ in Set.Icc a b, (deriv u θ) ^ 2 * qW k γ θ
          ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
        integral_Icc_le_Iθ h.hH5
          (fun θ hθ => mul_nonneg (sq_nonneg _) (qW_nonneg (hsub hθ)))
          (fun θ hθ =>
            mul_le_of_le_one_right (sq_nonneg _) (qW_le_one hk hγ2 (hsub hθ)))
          hsub (fun θ _ => sq_nonneg _)
      have hmain' : ∫ θ in Set.Icc a b, (iteratedDeriv 1 u θ) ^ 2 * qW k γ θ
          ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 := by
        simpa only [iteratedDeriv_one] using hmain
      have hfin : ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 ≤ FarR k γ u g := by
        simp only [FarR]
        linarith [hR2, hR3, hR4, hR6]
      exact le_trans hmain' hfin
    · -- `j = 2`: dominate by `(u'')²·σ^{-η}`
      have heq : iteratedDeriv 2 u = fun θ => deriv (deriv u) θ := by
        funext θ
        rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
      have hmain : ∫ θ in Set.Icc a b, (deriv (deriv u) θ) ^ 2 * qW k γ θ
          ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) :=
        integral_Icc_le_Iθ h.hH4
          (fun θ hθ => mul_nonneg (sq_nonneg _) (qW_nonneg (hsub hθ)))
          (fun θ hθ =>
            mul_le_mul_of_nonneg_left (qW_le_sEta hk hγ2 (hsub hθ)) (sq_nonneg _))
          hsub (fun θ hθ => mul_nonneg (sq_nonneg _)
            (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))
      have hmain' : ∫ θ in Set.Icc a b, (iteratedDeriv 2 u θ) ^ 2 * qW k γ θ
          ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) := by
        simpa only [heq] using hmain
      have hfin : ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) ≤ FarR k γ u g := by
        simp only [FarR]
        linarith [hR2, hR3, hR5, hR6]
      exact le_trans hmain' hfin
  · -- `j ≥ 3`: dominate by the `j`-th slot of `FarR`
    have hmem : j ∈ Finset.Icc 3 (k + 1) := Finset.mem_Icc.mpr ⟨hjge, hj⟩
    have hmain : ∫ θ in Set.Icc a b, (iteratedDeriv j u θ) ^ 2 * qW k γ θ
        ≤ ∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ) :=
      integral_Icc_le_Iθ (h.hH3 j hmem)
        (fun θ hθ => mul_nonneg (sq_nonneg _) (qW_nonneg (hsub hθ)))
        (fun θ hθ => mul_le_mul_of_nonneg_left
          (qW_le_slotWeight hk hγ2 hjge (by omega) (hsub hθ)) (sq_nonneg _))
        hsub (fun θ hθ => mul_nonneg (sq_nonneg _) (slotWeight_nonneg hθ))
    have hfin : ∫ θ in Work.Spaces.Iθ, (iteratedDeriv j u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - γ) ≤ FarR k γ u g := by
      simp only [FarR]
      have hsingle := Finset.single_le_sum (f := fun j' => ∫ θ in Work.Spaces.Iθ,
          (iteratedDeriv j' u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (j' : ℝ) - 4 - γ))
        (fun j' _ => MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg (sq_nonneg _) (slotWeight_nonneg hθ))) hmem
      linarith [hsingle, hR2, hR4, hR5, hR6]
    exact le_trans hmain hfin

end Work.FTS.EllipticEst.remov.TopCoreB.FEL
