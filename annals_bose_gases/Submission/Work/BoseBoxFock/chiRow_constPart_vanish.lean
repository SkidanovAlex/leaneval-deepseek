import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Q0Value
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiRow_constPart_vanish`

The constant part of the FS χ-row vanishes: for a continuous `Φ` on the
`n`-particle centred box,

    ∑_{i,j} [i≠j] ∫_{abox n ℓ} (PᵢΦ)(Qᵢ PⱼΦ) = 0 ,

where `Pᵢ` is the mean over the centred cube (`Submission.BoseGases.aP`) and
`Qᵢ = 1 − Pᵢ`.

The vanishing is *termwise* and in fact holds for every `i, j` (the condition
`i ≠ j` is never used): since `Pᵢ` is an idempotent self-adjoint projection on
`L²(abox n ℓ)` (`aP_sym_box`, `aP_idem`),

    ∫ (PᵢΦ)·(Pᵢ PⱼΦ) = ∫ (PᵢPᵢΦ)·(PⱼΦ) = ∫ (PᵢΦ)·(PⱼΦ)

so that the integrand `(PᵢΦ)·(Qᵢ PⱼΦ) = (PᵢΦ)(PⱼΦ) − (PᵢΦ)(PᵢPⱼΦ)` integrates
to `0`.
-/

namespace Work.BoseBoxFock

open MeasureTheory
open scoped Topology Real BigOperators

/-- **The key identity.** For continuous `Φ`, `Ψ` on the `n`-particle centred
box and any slot `i`,

    ∫_{abox n ℓ} (PᵢΦ)·(QᵢΨ) = 0 .

This is the self-adjoint idempotency of `Pᵢ`: `QᵢΨ = Ψ − PᵢΨ` and
`⟨PᵢΦ, PᵢΨ⟩ = ⟨PᵢPᵢΦ, Ψ⟩ = ⟨PᵢΦ, Ψ⟩`. -/
lemma aP_mul_aQ_integral_eq_zero {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {Φ Ψ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) (hΨc : Continuous Ψ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
      (Submission.BoseGases.aP ℓ i Φ x) * (Submission.BoseGases.aQ ℓ i Ψ x)) = 0 := by
  have hPΦc : Continuous (Submission.BoseGases.aP ℓ i Φ) :=
    Submission.BoseGases.aP_continuous hℓ i hΦc
  have hPΨc : Continuous (Submission.BoseGases.aP ℓ i Ψ) :=
    Submission.BoseGases.aP_continuous hℓ i hΨc
  have hinteg1 : IntegrableOn (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ i Φ x * Ψ x) (Submission.BoseGases.abox n ℓ) volume :=
    Submission.BoseGases.integrableOn_abox_of_continuous hℓ (hPΦc.mul hΨc)
  have hinteg2 : IntegrableOn (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ i Ψ x)
      (Submission.BoseGases.abox n ℓ) volume :=
    Submission.BoseGases.integrableOn_abox_of_continuous hℓ (hPΦc.mul hPΨc)
  -- `⟨PᵢΦ, PᵢΨ⟩ = ⟨PᵢΦ, Ψ⟩` by self-adjointness and idempotency
  have hkey : (∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ i Ψ x)
      = (∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ i Φ x * Ψ x) := by
    have h1 := Submission.BoseGases.aP_sym_box (N := n) (ℓ := ℓ) hℓ i
      (Φ := Submission.BoseGases.aP ℓ i Φ) (Ψ := Ψ) hPΦc hΨc
    have h2 : (∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ i Φ) x * Ψ x)
        = (∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ i Φ x * Ψ x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Submission.BoseGases.aP_idem hℓ i hΦc x]
    exact h1.symm.trans h2
  calc
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.aP ℓ i Φ x) * (Submission.BoseGases.aQ ℓ i Ψ x))
        = ∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.aP ℓ i Φ x * Ψ x
              - Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ i Ψ x) := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [Submission.BoseGases.aQ]
          ring
    _ = (∫ x in Submission.BoseGases.abox n ℓ, Submission.BoseGases.aP ℓ i Φ x * Ψ x)
          - (∫ x in Submission.BoseGases.abox n ℓ,
              Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ i Ψ x) :=
          integral_sub hinteg1 hinteg2
    _ = 0 := by rw [hkey]; ring

theorem chiRow_constPart_vanish {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else
      (∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.aP ℓ i Φ x) *
          (Submission.BoseGases.aQ ℓ i
            (fun y : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ j Φ y) x))) = 0 := by
  refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
  by_cases hij : i = j
  · rw [if_pos hij]
  · rw [if_neg hij]
    exact aP_mul_aQ_integral_eq_zero hℓ i hΦc
      (Submission.BoseGases.aP_continuous hℓ j hΦc)

end Work.BoseBoxFock
