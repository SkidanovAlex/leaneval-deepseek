import Mathlib
import Submission.Work.FIArea4.A4c.Defs
import Submission.Work.FIArea4.A4c.MoebiusCore
import Submission.Work.FIArea4.S15expSum_moebius_split
import Submission.Work.FIArea4.A6R2.Crux
import Submission.Work.FIArea4.A6R2.pD6ngStratumBound
import Submission.Work.FIArea4.A6R.strUvarSum6

namespace Work.FIArea4.A4c

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- **The variance half of the Möbius-split crux** (`Work.FIArea4.A4c.ExpBound6T`, defined in
`Submission/Work/FIArea4/A4c/Defs.lean`).

Proof route:
1. From `mobiusData6 Pa φ β hβ` take the pair-independent data `(W, μ)` and from `moebiusSplit6`
   get `expSum6 β = expSum6ng β + Σ_{w ∈ W.erase 1} μ w · expSum6ng (β_w)` with
   `β_w = Work.S15alt.restrArray β w` (use `restrArray β 1 = β`, `μ 1 = 1`, `‖μ w‖ ≤ 1`).
2. Each `β_w` is `IsPrimBoxCoeff Pa φ` (`Work.FIArea4.isPrimBoxCoeff_restrArray`), so the proved
   `Work.FIArea4.A6R2.ExpBound6ng` applies to it — take it as
   `A6R2.ExpBound6ng_of_inputs A6R2.pD6ngStratumBound (Work.A6R.strUvarSum6)` (both proved and
   axiom-clean) or directly from `Submission.Work.FIArea4.A6R2.Crux`.  (Do NOT import
   `A6R.removal6`, which carries a `sorryAx`.)
3. `Σ_{w ∈ W} A6Ener3 (β_w) = Σ_{z ∈ boxN} τ(Re z)³ ‖β z‖² · #(W.filter (· ∣ z))` by
   `A6Ener3_restrArray` and `sum_swap_divisor_gen` (both in `A4c.MoebiusCore`) with `c ≡ 1`.
4. On this sum apply the hypothesis `DivBound Pa β T` to `W.filter (· ∣ z)` when `β z ≠ 0` (the
   term vanishes when `β z = 0`), giving `≤ T · A6Ener3 Pa β`.  Only the cardinality
   `#(W.filter (· ∣ z)) ≤ T` is used — there is NO decay in `w` anywhere.
Constants: `(log N+1)^4` from `ExpBound6ng`, and the sum over `W` is bounded by `(‖μ 1‖ + Σ_{w ≠ 1} ‖μ w‖)·max
= Σ_w ‖μ w‖ ≤ (#W)` — instead use `‖expSum6‖ ≤ Σ_{w ∈ W} ‖expSum6ng (β_w)‖` via the triangle
inequality and `‖μ w‖ ≤ 1`. -/
theorem expBound6T : Work.FIArea4.A4c.ExpBound6T := by
  -- the unfiltered crux, proved from its two analytic inputs
  obtain ⟨C₁, x₀, hC₁, hng⟩ :=
    Work.FIArea4.A6R2.ExpBound6ng_of_inputs Work.FIArea4.A6R2.pD6ngStratumBound
      Work.FIArea4.A6R.strUvarSum6
  refine ⟨C₁, x₀, hC₁, ?_⟩
  intro Pa hx X j φ β ℓ u t T hβ hX hX9 hDiv
  -- the pair-independent Möbius data
  obtain ⟨W, μ, hμnorm, h1W, hμ1, _hWne, hind⟩ := Work.FIArea4.A4c.mobiusData6 Pa φ β hβ
  have hsplit := Work.FIArea4.A4c.moebiusSplit6 Pa X j β ℓ u t hind h1W hμ1
  have hexp : Work.FIArea4.A6R2.expSum6 Pa X j β ℓ u t
      = Work.FIArea4.A6R2.expSum6ng Pa X j β ℓ u t
        + ∑ w ∈ W.erase 1,
            μ w * Work.FIArea4.A6R2.expSum6ng Pa X j (Work.S15alt.restrArray β w) ℓ u t := by
    rw [← hsplit]; ring
  have hrestr1 : Work.S15alt.restrArray β 1 = β := by
    funext z; simp [Work.S15alt.restrArray]
  -- step 1: the triangle inequality, killing the Möbius weights with `‖μ w‖ ≤ 1`
  have htri : ‖Work.FIArea4.A6R2.expSum6 Pa X j β ℓ u t‖ ≤
      ‖Work.FIArea4.A6R2.expSum6ng Pa X j β ℓ u t‖
        + ∑ w ∈ W.erase 1,
            ‖Work.FIArea4.A6R2.expSum6ng Pa X j (Work.S15alt.restrArray β w) ℓ u t‖ := by
    rw [hexp]
    refine le_trans (norm_add_le _ _) (add_le_add le_rfl ?_)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun w _ => ?_))
    calc ‖μ w * Work.FIArea4.A6R2.expSum6ng Pa X j (Work.S15alt.restrArray β w) ℓ u t‖
        ≤ ‖μ w‖ * ‖Work.FIArea4.A6R2.expSum6ng Pa X j (Work.S15alt.restrArray β w) ℓ u t‖ :=
          norm_mul_le _ _
      _ ≤ 1 * ‖Work.FIArea4.A6R2.expSum6ng Pa X j (Work.S15alt.restrArray β w) ℓ u t‖ :=
          mul_le_mul_of_nonneg_right (hμnorm w) (norm_nonneg _)
      _ = ‖Work.FIArea4.A6R2.expSum6ng Pa X j (Work.S15alt.restrArray β w) ℓ u t‖ := one_mul _
  -- step 2: the unfiltered crux applies to every restricted array
  have hbound : ∀ w : GaussianInt,
      ‖Work.FIArea4.A6R2.expSum6ng Pa X j (Work.S15alt.restrArray β w) ℓ u t‖
        ≤ C₁ * (Real.log Pa.N + 1) ^ 4 * Work.FIArea4.S15Br6 Pa X
            * Work.FIArea4.A6Ener3 Pa (Work.S15alt.restrArray β w) :=
    fun w => hng Pa hx X j φ (Work.S15alt.restrArray β w) ℓ u t
      (Work.FIArea4.isPrimBoxCoeff_restrArray Pa hβ w) hX hX9
  -- step 3/4: the divisor swap, then `DivBound`
  have hsumle : (∑ w ∈ W, Work.FIArea4.A6Ener3 Pa (Work.S15alt.restrArray β w))
      ≤ T * Work.FIArea4.A6Ener3 Pa β := by
    have hswap : (∑ w ∈ W, Work.FIArea4.A6Ener3 Pa (Work.S15alt.restrArray β w))
        = ∑ z ∈ Work.FITop.boxN Pa,
            ((((z.re.natAbs.divisors.card : ℕ) : ℝ) ^ 3) * Complex.normSq (β z)
              * ((W.filter (fun w => w ∣ z)).card : ℝ)) := by
      calc ∑ w ∈ W, Work.FIArea4.A6Ener3 Pa (Work.S15alt.restrArray β w)
          = ∑ w ∈ W, ∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => w ∣ z),
              ((((z.re.natAbs.divisors.card : ℕ) : ℝ) ^ 3) * Complex.normSq (β z)) :=
              Finset.sum_congr rfl (fun w _ => Work.FIArea4.A4c.A6Ener3_restrArray Pa β w)
        _ = ∑ w ∈ W, (1 : ℝ) * (∑ z ∈ (Work.FITop.boxN Pa).filter (fun z => w ∣ z),
              ((((z.re.natAbs.divisors.card : ℕ) : ℝ) ^ 3) * Complex.normSq (β z))) := by
              simp
        _ = ∑ z ∈ Work.FITop.boxN Pa,
              ((((z.re.natAbs.divisors.card : ℕ) : ℝ) ^ 3) * Complex.normSq (β z))
              * (∑ w ∈ W.filter (fun w => w ∣ z), (1 : ℝ)) :=
              Work.FIArea4.A4c.sum_swap_divisor_gen Pa W (fun _ => (1 : ℝ))
                (fun z => ((((z.re.natAbs.divisors.card : ℕ) : ℝ) ^ 3) * Complex.normSq (β z)))
        _ = ∑ z ∈ Work.FITop.boxN Pa,
              ((((z.re.natAbs.divisors.card : ℕ) : ℝ) ^ 3) * Complex.normSq (β z)
              * ((W.filter (fun w => w ∣ z)).card : ℝ)) := by
              refine Finset.sum_congr rfl (fun z _ => ?_)
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    calc (∑ w ∈ W, Work.FIArea4.A6Ener3 Pa (Work.S15alt.restrArray β w))
        = ∑ z ∈ Work.FITop.boxN Pa,
            ((((z.re.natAbs.divisors.card : ℕ) : ℝ) ^ 3) * Complex.normSq (β z)
              * ((W.filter (fun w => w ∣ z)).card : ℝ)) := hswap
      _ ≤ ∑ z ∈ Work.FITop.boxN Pa,
            ((((z.re.natAbs.divisors.card : ℕ) : ℝ) ^ 3) * Complex.normSq (β z) * T) := by
            refine Finset.sum_le_sum (fun z _ => ?_)
            by_cases hz : β z = 0
            · simp [hz]
            · have hcard : ((W.filter (fun w => w ∣ z)).card : ℝ) ≤ T :=
                hDiv z hz (W.filter (fun w => w ∣ z))
                  (fun w hw => (Finset.mem_filter.mp hw).2)
              exact mul_le_mul_of_nonneg_left hcard
                (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 3) (Complex.normSq_nonneg _))
      _ = (∑ z ∈ Work.FITop.boxN Pa,
            ((((z.re.natAbs.divisors.card : ℕ) : ℝ) ^ 3) * Complex.normSq (β z))) * T := by
            rw [Finset.sum_mul]
      _ = T * Work.FIArea4.A6Ener3 Pa β := by
            unfold Work.FIArea4.A6Ener3
            rw [mul_comm]
  -- `1 ∈ W` puts the unrestricted energy back into the `W`-sum
  have hsumW : Work.FIArea4.A6Ener3 Pa β
        + ∑ w ∈ W.erase 1, Work.FIArea4.A6Ener3 Pa (Work.S15alt.restrArray β w)
      = ∑ w ∈ W, Work.FIArea4.A6Ener3 Pa (Work.S15alt.restrArray β w) := by
    have h := Finset.sum_erase_add W
      (fun w => Work.FIArea4.A6Ener3 Pa (Work.S15alt.restrArray β w)) h1W
    rw [hrestr1] at h
    rw [add_comm]
    exact h
  have hnonneg : (0 : ℝ) ≤ C₁ * (Real.log Pa.N + 1) ^ 4 * Work.FIArea4.S15Br6 Pa X :=
    mul_nonneg (mul_nonneg hC₁.le (pow_nonneg (by linarith [Real.log_nonneg Pa.hN1]) 4))
      (Work.FIArea4.A4c.S15Br6_nonneg Pa X)
  -- step 5: assemble
  calc ‖Work.FIArea4.A6R2.expSum6 Pa X j β ℓ u t‖
      ≤ ‖Work.FIArea4.A6R2.expSum6ng Pa X j β ℓ u t‖
        + ∑ w ∈ W.erase 1,
            ‖Work.FIArea4.A6R2.expSum6ng Pa X j (Work.S15alt.restrArray β w) ℓ u t‖ := htri
    _ ≤ C₁ * (Real.log Pa.N + 1) ^ 4 * Work.FIArea4.S15Br6 Pa X * Work.FIArea4.A6Ener3 Pa β
        + ∑ w ∈ W.erase 1, C₁ * (Real.log Pa.N + 1) ^ 4 * Work.FIArea4.S15Br6 Pa X
            * Work.FIArea4.A6Ener3 Pa (Work.S15alt.restrArray β w) := by
          refine add_le_add ?_ (Finset.sum_le_sum (fun w _ => hbound w))
          simpa [hrestr1] using hbound 1
    _ = C₁ * (Real.log Pa.N + 1) ^ 4 * Work.FIArea4.S15Br6 Pa X
          * (Work.FIArea4.A6Ener3 Pa β
            + ∑ w ∈ W.erase 1, Work.FIArea4.A6Ener3 Pa (Work.S15alt.restrArray β w)) := by
          rw [mul_add, Finset.mul_sum]
    _ = C₁ * (Real.log Pa.N + 1) ^ 4 * Work.FIArea4.S15Br6 Pa X
          * (∑ w ∈ W, Work.FIArea4.A6Ener3 Pa (Work.S15alt.restrArray β w)) := by
          rw [← hsumW]
    _ ≤ C₁ * (Real.log Pa.N + 1) ^ 4 * Work.FIArea4.S15Br6 Pa X
          * (T * Work.FIArea4.A6Ener3 Pa β) :=
          mul_le_mul_of_nonneg_left hsumle hnonneg

end Work.FIArea4.A4c
