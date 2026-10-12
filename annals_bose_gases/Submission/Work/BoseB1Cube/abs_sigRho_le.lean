import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.slot_rhoBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.abs_sigRho_le` — the mean-zero one-body deviation bound at the box

For a measurable set `A ⊆ acube ℓ` with `0 < V = |A|`, a continuous `n`-body state `Φ`, and a
measurable `ρ` with `|ρ| ≤ Ξ`, `ρ = 0` off `A` and **mean zero on `A`** (`∫_A ρ = 0`),

    |∫_{abox n ℓ} Φ²·Σᵢρ(xᵢ)|  ≤  Ξ·(2√(S·Q) + Q),   S = boxFlatCount, Q = boxQCount.

This is the sharp form of the density-deviation row of the per-box ledger: it is the
`Work.BoseB1Cube.denseAliveTauSigma` split `χ² = χ̄·1_A + ρ` (with `ρ := χ² − (κ/V)·1_A`,
`∫_A ρ = 0`) discharged in the same shape as `Work.BoseB1Cube.abs_boxQCross_le`.

## Mathematics

Write `Pᵢ = boxPInd V A i` (FS's `P_{B,i} = |B|⁻¹⟨1_B,·⟩1_B`), `Qᵢ = boxQInd V A i`.  By
`hsupp`, `ρ(xᵢ) ≠ 0` only for `xᵢ ∈ A`, and on `xᵢ ∈ A` one has `PᵢΦ + QᵢΦ = Φ`, so *pointwise*

    ρ(xᵢ)·Φ² = ρ(xᵢ)·(PᵢΦ + QᵢΦ)² = ρ(xᵢ)·(PᵢΦ)² + 2ρ(xᵢ)(PᵢΦ)(QᵢΦ) + ρ(xᵢ)·(QᵢΦ)².

The **condensate term vanishes**: `(PᵢΦ)(x)² = 1_A(xᵢ)·c(x_{−i})²` with `c` independent of slot `i`,
so

    ∫_{abox n ℓ} ρ(xᵢ)·(PᵢΦ)² = (∫_A ρ)·(∫ c²) = 0

(`Work.BoseB1Cube.slot_rhoBound` reduces this to the one-slot kernel identity
`Work.BoseFixB1S.Q0C.one_kernel`).  The remaining two rows are bounded by

    |∫ρ(xᵢ)(QᵢΦ)²| ≤ Ξ∫(QᵢΦ)² = Ξ·qᵢ ,
    |2∫ρ(xᵢ)(PᵢΦ)(QᵢΦ)| ≤ 2Ξ∫|PᵢΦ·QᵢΦ| ≤ 2Ξ√(pᵢ·qᵢ)

(Cauchy–Schwarz, `Work.BoseFixB1S.int_abs_mul_le_sqrt_mul_sqrt`), with `pᵢ = ∫(PᵢΦ)²`,
`qᵢ = ∫(QᵢΦ)²`.  Summing over the slots and using Cauchy–Schwarz on the index set
(`Real.sum_sqrt_mul_sqrt_le`) turns `2Σᵢ√(pᵢqᵢ) + Σᵢqᵢ` into `2√(S·Q) + Q`.  The single-slot
estimate is the delegated lemma `Work.BoseB1Cube.slot_rhoBound`; this file supplies the
Fubini/sum bookkeeping, the index Cauchy–Schwarz and the definitional identification of the two
counts.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseB1Cube

set_option linter.unusedVariables false

/-- Pure real assembly: if each slot term satisfies `|Tᵢ| ≤ Ξ(2√(pᵢqᵢ) + qᵢ)` with `pᵢ, qᵢ ≥ 0`,
then `|ΣᵢTᵢ| ≤ Ξ(2√((Σp)(Σq)) + Σq)`. -/
private theorem sum_slot_bound_rho {ι : Type*} [Fintype ι] {Ξ : ℝ} (hΞ0 : 0 ≤ Ξ)
    {T p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hT : ∀ i, |T i| ≤ Ξ * (2 * Real.sqrt (p i * q i) + q i)) :
    |∑ i, T i| ≤ Ξ * (2 * Real.sqrt ((∑ i, p i) * (∑ i, q i)) + ∑ i, q i) := by
  have hsum : |∑ i, T i| ≤ ∑ i, Ξ * (2 * Real.sqrt (p i * q i) + q i) :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun i _ => hT i))
  have hfac : (∑ i, Ξ * (2 * Real.sqrt (p i * q i) + q i))
      = Ξ * (2 * (∑ i, Real.sqrt (p i * q i)) + ∑ i, q i) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcs : (∑ i, Real.sqrt (p i * q i)) ≤ Real.sqrt ((∑ i, p i) * (∑ i, q i)) := by
    have h1 : ∀ i, Real.sqrt (p i * q i) = Real.sqrt (p i) * Real.sqrt (q i) :=
      fun i => Real.sqrt_mul (hp i) (q i)
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    calc (∑ i, Real.sqrt (p i) * Real.sqrt (q i))
        ≤ Real.sqrt (∑ i, p i) * Real.sqrt (∑ i, q i) :=
          Real.sum_sqrt_mul_sqrt_le Finset.univ (fun i => hp i) (fun i => hq i)
      _ = Real.sqrt ((∑ i, p i) * (∑ i, q i)) := by
          rw [Real.sqrt_mul (Finset.sum_nonneg (fun i _ => hp i)) (∑ i, q i)]
  calc |∑ i, T i| ≤ ∑ i, Ξ * (2 * Real.sqrt (p i * q i) + q i) := hsum
    _ = Ξ * (2 * (∑ i, Real.sqrt (p i * q i)) + ∑ i, q i) := hfac
    _ ≤ Ξ * (2 * Real.sqrt ((∑ i, p i) * (∑ i, q i)) + ∑ i, q i) := by
        refine mul_le_mul_of_nonneg_left ?_ hΞ0
        linarith [hcs]

theorem abs_sigRho_le {n : ℕ} {ℓ V Ξ : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hℓ : 0 < ℓ) (hV : 0 < V) (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (hVeq : V = (MeasureTheory.volume A).toReal)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    {ρ : EuclideanSpace ℝ (Fin 3) → ℝ} (hρm : Measurable ρ) (hΞ0 : 0 ≤ Ξ)
    (hρb : ∀ z, |ρ z| ≤ Ξ) (hsupp : ∀ z, z ∉ A → ρ z = 0) (hρA : ∫ z in A, ρ z = 0) :
    |∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * (∑ i : Fin n, ρ (x i))|
      ≤ Ξ * (2 * Real.sqrt (Work.BoseFixB1S.boxFlatCount V ℓ A Φ
              * Work.BoseFixB1S.boxQCount V ℓ A Φ)
            + Work.BoseFixB1S.boxQCount V ℓ A Φ) := by
  -- the per-slot estimates
  have hslot : ∀ i : Fin n, |∫ x in Submission.BoseGases.abox n ℓ, ρ (x i) * (Φ x) ^ 2|
      ≤ Ξ * (2 * Real.sqrt ((∫ x in Submission.BoseGases.abox n ℓ,
                (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)
              * (∫ x in Submission.BoseGases.abox n ℓ,
                (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2))
            + (∫ x in Submission.BoseGases.abox n ℓ,
                (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)) :=
    fun i => slot_rhoBound hℓ hV hA hAc hVeq hΦc hρm hΞ0 hρb hsupp hρA i
  -- boundedness of the state on the compact box
  obtain ⟨C, hC0, hΦb, hPb, hQb⟩ := Work.BoseFixB1S.boxBounds hℓ hV hA hVeq hAc hΦc
  have hΦ2b : ∀ x ∈ Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 ≤ C ^ 2 := by
    intro x hx
    rw [← sq_abs (Φ x)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hΦb x hx) 2
  -- integrability of the individual slot terms
  have hInt : ∀ i : Fin n, Integrable (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * ρ (x i))
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
    intro i
    refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
      ((hΦc.pow 2).measurable.mul (hρm.comp (measurable_pi_apply i))).aestronglyMeasurable
      (C ^ 2 * Ξ) ?_
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul (hΦ2b x hx) (hρb (x i)) (abs_nonneg _) (sq_nonneg _)
  -- the sum inside the integral
  have hstep1 : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * (∑ i : Fin n, ρ (x i)))
      = ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * ρ (x i) := by
    simp only [Finset.mul_sum]
    exact integral_finsetSum Finset.univ (fun i _ => hInt i)
  have hstep2 : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * ρ (x i))
      = ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ, ρ (x i) * (Φ x) ^ 2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    ring
  -- nonnegativity of the two per-slot counts
  have hp : ∀ i : Fin n, 0 ≤ ∫ x in Submission.BoseGases.abox n ℓ,
      (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 :=
    fun i => integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x => sq_nonneg _))
  have hq : ∀ i : Fin n, 0 ≤ ∫ x in Submission.BoseGases.abox n ℓ,
      (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 :=
    fun i => integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x => sq_nonneg _))
  have hmain := sum_slot_bound_rho hΞ0 hp hq hslot
  calc |∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * (∑ i : Fin n, ρ (x i))|
      = |∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ, ρ (x i) * (Φ x) ^ 2| := by
        rw [hstep1, hstep2]
    _ ≤ Ξ * (2 * Real.sqrt ((∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)
          * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2))
        + (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)) := hmain
    _ = Ξ * (2 * Real.sqrt (Work.BoseFixB1S.boxFlatCount V ℓ A Φ
            * Work.BoseFixB1S.boxQCount V ℓ A Φ)
          + Work.BoseFixB1S.boxQCount V ℓ A Φ) := by
        rw [Work.BoseFixB1S.boxFlatCount, Work.BoseFixB1S.boxQCount]

end Work.BoseB1Cube
