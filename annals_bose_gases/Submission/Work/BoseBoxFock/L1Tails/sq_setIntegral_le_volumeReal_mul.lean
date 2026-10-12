import Mathlib.MeasureTheory.Function.L2Space
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Cauchy–Schwarz (Jensen) for a set integral of a nonnegative function

The elementary estimate `(∫_s g)² ≤ μ.real s · ∫_s g²` for a real function `g ≥ 0` a.e. on `s`,
obtained from Hölder's inequality with `p = q = 2` applied to the pair `(1, g)` on the restricted
measure `μ.restrict s`.  The auxiliary form is stated for an arbitrary measure `ν` with
`ν univ ≠ ⊤` (needed so that the constant function `1` lies in `L²(ν)`).
-/

open MeasureTheory

namespace Work.BoseBoxFock.L1Tails

/-- Cauchy–Schwarz / Jensen on a single measure `ν` of finite total mass. -/
theorem sq_integral_le_measureReal_univ_mul_integral_sq {α : Type*} [MeasurableSpace α]
    {ν : MeasureTheory.Measure α} {g : α → ℝ}
    (hν : ν Set.univ ≠ ⊤) (hg : MeasureTheory.Integrable g ν)
    (hg2 : MeasureTheory.Integrable (fun x => g x ^ 2) ν) (hg0 : 0 ≤ᵐ[ν] g) :
    (∫ x, g x ∂ν) ^ 2 ≤ ν.real Set.univ * ∫ x, g x ^ 2 ∂ν := by
  have hfin : IsFiniteMeasure ν := ⟨lt_top_iff_ne_top.mpr hν⟩
  have hmem1 : MemLp (fun _ : α => (1:ℝ)) (ENNReal.ofReal (2:ℝ)) ν := memLp_const 1
  have hmemg : MemLp g (ENNReal.ofReal (2:ℝ)) ν := by
    rw [show ENNReal.ofReal (2:ℝ) = 2 by simp]
    exact (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hg2
  have hhold := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := ν) (p := 2) (q := 2)
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
      (f := fun _ : α => (1:ℝ)) (g := g)
      (Filter.Eventually.of_forall fun _ => zero_le_one) hg0 hmem1 hmemg
  -- simplify the constant factors: `1 * g = g`, `1 ^ 2 = 1`, `∫ 1 = ν.real univ`
  simp only [one_mul, Real.rpow_ofNat, one_pow, integral_const, smul_eq_mul, mul_one] at hhold
  have hx : 0 ≤ ∫ x, g x ∂ν := integral_nonneg_of_ae hg0
  have hB : 0 ≤ ∫ x, g x ^ 2 ∂ν :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
  have ha : 0 ≤ ν.real Set.univ := by rw [measureReal_def]; exact ENNReal.toReal_nonneg
  have hsq := pow_le_pow_left₀ hx hhold 2
  simp only [mul_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt ha, Real.sq_sqrt hB] at hsq
  exact hsq

theorem sq_setIntegral_le_volumeReal_mul {β : Type*} [MeasurableSpace β]
    {μ : MeasureTheory.Measure β} {s : Set β} {g : β → ℝ}
    (hs : μ s ≠ ⊤) (hg : MeasureTheory.IntegrableOn g s μ)
    (hg2 : MeasureTheory.IntegrableOn (fun x => g x ^ 2) s μ)
    (hg0 : 0 ≤ᵐ[μ.restrict s] g) :
    (∫ x in s, g x ∂μ) ^ 2 ≤ μ.real s * ∫ x in s, g x ^ 2 ∂μ := by
  have hν : (μ.restrict s) Set.univ ≠ ⊤ := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]; exact hs
  have hνreal : (μ.restrict s).real Set.univ = μ.real s := by
    rw [measureReal_def, measureReal_def, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have hmain := sq_integral_le_measureReal_univ_mul_integral_sq hν hg hg2 hg0
  rw [← hνreal]
  exact hmain

end Work.BoseBoxFock.L1Tails
