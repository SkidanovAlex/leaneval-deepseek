import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.commutatorPairingB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.boxQMassLeFibreB1`

The fibre-weighted excited mass at the FS-faithful box projections is `n₊`-linear: for a
nonnegative fibre `fib`, bounded by `Cf` on the cube `acube ℓ` — where the box indicator
`1_A` of `A ⊆ acube ℓ` localises the slot variable —

  `Σ i, ∫_{abox N ℓ} (Q_{A,i}Φ)² · fib(xᵢ)  ≤  Cf · n₊(A)`,
  `n₊(A) = boxQCount V ℓ A Φ = Σ i, ∫_{abox N ℓ} (Q_{A,i}Φ)²`.

The mathematics is one pointwise inequality per slot.  FS's mean-free projection is
`Q_{A,i}Φ = 1_A(xᵢ)·Φ − P_{A,i}Φ` (both terms carry the box indicator), hence `Q_{A,i}Φ`
vanishes identically on the configurations with `xᵢ ∉ A`.  On `xᵢ ∈ A` one has
`xᵢ ∈ acube ℓ` (as `A ⊆ acube ℓ`), so `0 ≤ fib (xᵢ) ≤ |fib (xᵢ)| ≤ Cf`, and multiplying the
nonnegative number `(Q_{A,i}Φ)²` by it costs at most `Cf`.  Summing over the slots and
factoring `Cf` out of the finite sum gives the claim.

Integrability of the dominating side on the analysis box is `integrableOn_sq_of_bound`
(`Φ` is continuous, hence bounded on the compact box, and `Q_{A,i}Φ` inherits a bound);
the a.e. monotonicity of the integral is then `integral_mono_of_nonneg`, which only needs the
*dominating* integrand to be integrable — the left-hand integrand is nonnegative because
`fib ≥ 0`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

set_option maxHeartbeats 800000

theorem boxQMassLeFibreB1 {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfm : Measurable fib)
    (hfib0 : ∀ z, 0 ≤ fib z) {Cf : ℝ} (hCf0 : 0 ≤ Cf)
    (hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Cf)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 * fib (x i))
      ≤ Cf * Work.BoseFixB1S.boxQCount V ℓ A Φ := by
  classical
  -- `Φ` is measurable and bounded on the analysis box (continuity + compactness).
  obtain ⟨CΦ, _hCΦ0, hCΦ⟩ := exists_abox_bound hℓ hΦc
  have hΦ : GoodState ℓ Φ := ⟨hΦc.measurable, CΦ, hCΦ⟩
  -- **The single-slot inequality.**
  have hsingle : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 * fib (x i))
        ≤ Cf * ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 := by
    intro i
    -- the projection is measurable and bounded on the box, hence square integrable there
    obtain ⟨hmQ, CQ, hbQ⟩ := goodState_boxQInd hℓ hV hA hVeq hAc i hΦ
    have hintQ : Integrable (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
        (volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      integrableOn_sq_of_bound hℓ hmQ hbQ
    -- **the support of the projection is inside `{x | xᵢ ∈ A}`**
    have hzero : ∀ {x : Submission.BoseGases.X N}, x i ∉ A →
        Work.UBBInputs8.boxQInd V A i Φ x = 0 := by
      intro x hx
      simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
      rw [Set.indicator_of_notMem hx]
      ring
    -- the pointwise inequality `(Q_{A,i}Φ)²·fib(xᵢ) ≤ Cf·(Q_{A,i}Φ)²`
    have hpt : ∀ x : Submission.BoseGases.X N,
        (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 * fib (x i)
          ≤ Cf * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 := by
      intro x
      by_cases hmem : x i ∈ A
      · have h1 : fib (x i) ≤ Cf :=
          le_trans (le_abs_self _) (hfibb (x i) (hAc hmem))
        calc (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 * fib (x i)
            ≤ (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 * Cf :=
              mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
          _ = Cf * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 := by ring
      · rw [hzero hmem]; simp
    -- the left-hand integrand is nonnegative (`fib ≥ 0`), so a.e. monotonicity applies
    have hnn : ∀ x : Submission.BoseGases.X N,
        0 ≤ (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 * fib (x i) :=
      fun x => mul_nonneg (sq_nonneg _) (hfib0 _)
    have hmono := integral_mono_of_nonneg (μ := volume.restrict (Submission.BoseGases.abox N ℓ))
      (ae_of_all _ hnn) (hintQ.const_mul Cf) (ae_of_all _ hpt)
    rwa [MeasureTheory.integral_const_mul] at hmono
  -- **sum over the slots and factor `Cf` out of the finite sum**
  simp only [Work.BoseFixB1S.boxQCount]
  calc (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 * fib (x i))
      ≤ ∑ i : Fin N, Cf * ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 :=
        Finset.sum_le_sum (fun i _ => hsingle i)
    _ = Cf * ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 := by rw [Finset.mul_sum]

end Work.BoseFixB1S
