import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PB3Aux2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-- **Bessel for the box** (block III, first half): the `Lab N`-frame sum of the fibre integrals of
the slot mean `aPC ℓ i Θ`, integrated over the box `abox n ℓ`, is dominated by the `χ_ℓ²`-weighted
excited-slot energy of `aPC ℓ i Θ` in the *other* slot `j` (`i ≠ j`).

Here `ℓ = ellH v μ`.  The pointwise input is `bessel_fibre` (the finite `pinQ` frame at the
fibre `u ↦ Ψ (x[j ↦ u])`, `Ψ = aPC ℓ i Θ`), which applies at *every* configuration `x`; the
support hypothesis `hΘs` is used only through `aPC_eq_zero_of_notMem_abox`, to see that the
fibre of `Ψ` in the slot-`j` direction vanishes outside the box (the slot-`j` mean of a state
supported in `abox` vanishes whenever the `j`-th coordinate lies outside the box, because
`i ≠ j`).  The remaining content is the interchange of the finite sum with the box integral. -/
theorem pb3_bessel_box {n N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} (i j : Fin n)
    (hij : i ≠ j) {Θ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    (∑ k : Work.BoseBoxFock.Lab N,
        ∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
          Complex.normSq (∫ u : EuclideanSpace ℝ (Fin 3),
            (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u)
              * Work.BoseBoxFock.aPC (Work.BoseBoxFock.ellH v μ) i Θ
                  (Function.update x j u)))
      ≤ ∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
          ∫ u : EuclideanSpace ℝ (Fin 3),
            (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) u) ^ 2
              * ‖Work.BoseBoxFock.aQC (Work.BoseBoxFock.ellH v μ) j
                  (Work.BoseBoxFock.aPC (Work.BoseBoxFock.ellH v μ) i Θ)
                  (Function.update x j u)‖ ^ 2 := by
  classical
  set ℓ : ℝ := ellH v μ with hℓdef
  have hℓ : 0 < ℓ := ellH_pos v μ
  obtain ⟨Cb, hCb⟩ := hΘb
  have hCb0 : 0 ≤ Cb := le_trans (norm_nonneg (Θ (Classical.arbitrary (Fin n → E3)))) (hCb _)
  set Ψ : Xn n → ℂ := aPC ℓ i Θ with hΨdef
  have hΨm : Measurable Ψ := aPC_measurable' i hΘm
  have hΨb : ∀ x, ‖Ψ x‖ ≤ Cb := fun x => aPC_bound_pointwise hℓ i hCb hCb0 x
  -- the pointwise Bessel bound, valid at every configuration `x`
  have hpt : ∀ x : Xn n, ∑ k : Lab N,
      Complex.normSq (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Ψ (Function.update x j u))
      ≤ ∫ u : E3, Submission.BoseGases.chiScale ℓ u ^ 2
          * ‖aQC ℓ j Ψ (Function.update x j u)‖ ^ 2 := by
    intro x
    have h := bessel_fibre (v := v) (μ := μ) (N := N) j x hΨm ⟨Cb, hΨb⟩ (fun u hu => by
      rw [← hℓdef] at hu
      rw [hΨdef]
      exact aPC_eq_zero_of_notMem_abox hℓ hij hΘs (by simpa using hu))
    simpa [Complex.normSq_eq_norm_sq] using h
  -- measurability of the per-`k` fibre integral
  have hI (k : Lab N) : Measurable (fun x : Xn n =>
      ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Ψ (Function.update x j u)) :=
    slotIntegral_measurable hΨm (pinQ_measurable v μ N k) (pb3_pinQ_support k)
  -- integrability of each summand over the box
  have hIk (k : Lab N) : IntegrableOn (fun x : Xn n =>
      Complex.normSq (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Ψ (Function.update x j u)))
      (Submission.BoseGases.abox n ℓ) volume := by
    obtain ⟨Ck, hCk0, hCk⟩ := pinQ_bdd v μ N k
    refine MeasureTheory.IntegrableOn.of_bound
      (Submission.BoseGases.abox_lt_top n ℓ (le_of_lt hℓ)) ?_ ((Ck*Cb*ℓ^3)^2) ?_
    · exact ((Complex.continuous_normSq.measurable.comp (hI k)).aestronglyMeasurable).restrict
    · filter_upwards with x
      have hbd := slotIntegral_bound (j := j) (k := pinQ v μ N k) (F := Ψ) hℓ
        (pb3_pinQ_support k) hCk hΨb hCk0 hCb0 (x := x)
      rw [Complex.normSq_eq_norm_sq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) hbd 2
  -- `χ_ℓ²` is integrable
  have hchi2 : Integrable (fun u : E3 => Submission.BoseGases.chiScale ℓ u ^ 2) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous).pow 2
    · have hf : HasCompactSupport (Submission.BoseGases.chiScale ℓ) :=
        Submission.BoseGases.chiScale_hasCompactSupport (ne_of_gt hℓ)
      refine hf.mono ?_
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro h0
      exact hu (by rw [h0]; ring)
  have haQCm : Measurable (aQC ℓ j Ψ) := hΨm.sub (aPC_measurable' j hΨm)
  have hRu (x : Xn n) : Measurable (fun u : E3 =>
      Submission.BoseGases.chiScale ℓ u ^ 2 * ‖aQC ℓ j Ψ (Function.update x j u)‖ ^ 2) :=
    (((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous.measurable).pow_const 2).mul
      (((haQCm.comp (by fun_prop)).norm).pow_const 2)
  -- the right-hand side is measurable, hence bounded, hence integrable over the box
  have hRmeas : Measurable (fun x : Xn n => ∫ u : E3,
      Submission.BoseGases.chiScale ℓ u ^ 2 * ‖aQC ℓ j Ψ (Function.update x j u)‖ ^ 2) := by
    have hG : StronglyMeasurable (fun p : Xn n × E3 =>
        Submission.BoseGases.chiScale ℓ p.2 ^ 2 * ‖aQC ℓ j Ψ (Function.update p.1 j p.2)‖ ^ 2) :=
      ((((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous.measurable.comp
          measurable_snd).pow_const 2).mul
        (((haQCm.comp (by fun_prop)).norm).pow_const 2)).stronglyMeasurable
    exact hG.integral_prod_right'.measurable
  have hRint : IntegrableOn (fun x : Xn n => ∫ u : E3,
      Submission.BoseGases.chiScale ℓ u ^ 2 * ‖aQC ℓ j Ψ (Function.update x j u)‖ ^ 2)
      (Submission.BoseGases.abox n ℓ) volume := by
    refine MeasureTheory.IntegrableOn.of_bound
      (Submission.BoseGases.abox_lt_top n ℓ (le_of_lt hℓ))
      (hRmeas.aestronglyMeasurable.restrict)
      ((2*Cb)^2 * ∫ u : E3, Submission.BoseGases.chiScale ℓ u ^ 2) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg (fun u => mul_nonneg (sq_nonneg _) (sq_nonneg _)))]
    have haQCbd : ∀ u : E3, ‖aQC ℓ j Ψ (Function.update x j u)‖ ≤ 2 * Cb := by
      intro u
      rw [aQC_apply]
      calc ‖Ψ (Function.update x j u) - aPC ℓ j Ψ (Function.update x j u)‖
          ≤ ‖Ψ (Function.update x j u)‖ + ‖aPC ℓ j Ψ (Function.update x j u)‖ := norm_sub_le _ _
        _ ≤ Cb + Cb := add_le_add (hΨb _) (aPC_bound_pointwise hℓ j hΨb hCb0 _)
        _ = 2 * Cb := by ring
    have hle : ∀ u : E3, Submission.BoseGases.chiScale ℓ u ^ 2
        * ‖aQC ℓ j Ψ (Function.update x j u)‖ ^ 2
        ≤ Submission.BoseGases.chiScale ℓ u ^ 2 * (2*Cb)^2 := by
      intro u
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (haQCbd u) 2) (sq_nonneg _)
    have hInt2 : Integrable (fun u : E3 => Submission.BoseGases.chiScale ℓ u ^ 2 * (2*Cb)^2) :=
      hchi2.mul_const _
    have hInt1 : Integrable (fun u : E3 => Submission.BoseGases.chiScale ℓ u ^ 2
        * ‖aQC ℓ j Ψ (Function.update x j u)‖ ^ 2) :=
      Integrable.mono' hInt2 ((hRu x).aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun u => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
          exact hle u))
    calc ∫ u : E3, Submission.BoseGases.chiScale ℓ u ^ 2
            * ‖aQC ℓ j Ψ (Function.update x j u)‖ ^ 2
        ≤ ∫ u : E3, Submission.BoseGases.chiScale ℓ u ^ 2 * (2*Cb)^2 :=
          integral_mono_ae hInt1 hInt2 (Filter.Eventually.of_forall hle)
      _ = (2*Cb)^2 * ∫ u : E3, Submission.BoseGases.chiScale ℓ u ^ 2 := by
          rw [integral_mul_const, mul_comm]
  have hSint : IntegrableOn (fun x : Xn n => ∑ k : Lab N,
      Complex.normSq (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Ψ (Function.update x j u)))
      (Submission.BoseGases.abox n ℓ) volume :=
    integrable_finsetSum Finset.univ (fun k _ => hIk k)
  -- interchange the finite sum with the box integral, then integrate the pointwise bound
  rw [show (∑ k : Lab N, ∫ x in Submission.BoseGases.abox n ℓ, Complex.normSq (∫ u : E3,
        (starRingEnd ℂ) (pinQ v μ N k u) * Ψ (Function.update x j u)))
      = ∫ x in Submission.BoseGases.abox n ℓ, ∑ k : Lab N, Complex.normSq (∫ u : E3,
        (starRingEnd ℂ) (pinQ v μ N k u) * Ψ (Function.update x j u)) from by
    rw [MeasureTheory.integral_finsetSum]
    exact fun k _ => hIk k]
  exact integral_mono_ae hSint hRint (Filter.Eventually.of_forall hpt)

end Work.BoseBoxFock
