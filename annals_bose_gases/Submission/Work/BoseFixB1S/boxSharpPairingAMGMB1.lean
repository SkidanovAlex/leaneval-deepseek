import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPmassFibreB1
import Submission.Work.BoseFixB1S.n0FunOp_fibreStructureB1
import Submission.Work.BoseFixB1S.weightedYoungB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxSharpPairingAMGMB1` — the `λ = 4` fibre-weighted AM–GM of the crux

The completion of squares of FS `lm:appinteractionestimate` at the *sharp* parameter `λ = 4`:

```
−(4/volA)·Σᵢ∫ fib(xᵢ)·(Θ₊ qᵢ)² − ((∫_A fib)/(4·volA²))·Σᵢ∫ (Θ₋ pᵢ)²
      ≤ (2/volA)·Σᵢ∫ (Θ₊ qᵢ)·fib(xᵢ)·(Θ₋ pᵢ)
```

with `Θ₊ = √(n₀+1) + √c`, `Θ₋ = √(n₀+1) − √c`, `qᵢ = Q_{B,i}Φ`, `pᵢ = P_{B,i}Φ`.

## Where each piece comes from

* The **weighted Young inequality** `Work.BoseFixB1S.weighted_amgm_integral`
  (`-(λ∫Wu² + λ⁻¹∫Wv²) ≤ 2∫Wuv` for `W ≥ 0`), applied slot-wise at `λ = 4`.
* The **fibre collapse of the `P`-side** `Work.BoseFixB1S.boxPmassFibreB1`
  (`Σᵢ∫fib(xᵢ)(Θ₋pᵢ)² = ((∫fib)/volA)·Σᵢ∫(Θ₋pᵢ)²`), which converts the `λ⁻¹ = 1/4` loss into the
  coefficient `(∫fib)/(4volA²)` of the statement.
* The **integrability** side conditions.  Here the only issue is that the target bounds `fib` *only
  on `A`* (`hfb`): `Work.BoseFixB1S.n0ZeroProp_n0FunOp` shows that `Θ±(Q_{B,i}Φ)` **vanishes off
  `xᵢ ∈ A`**, so on the box the weight `fib(xᵢ)` is only ever read on `A` and the products are
  bounded (hence integrable).  This is the content of the helper
  `Work.BoseFixB1S.integrableOn_fibCoord_mul` below.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

set_option linter.unusedVariables false

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Integrability of `fib(xᵢ)·S` on the analysis box.**  If `fib ≥ 0`, `fib` is bounded on `A`
by `Cf`, `S` is measurable and bounded by `CS ≥ 0` on the box, and `S` *vanishes where `xᵢ ∉ A`*,
then `fib(xᵢ)·S` is integrable on `abox N ℓ`.  The point of the last hypothesis is that on the box
the factor `fib(xᵢ)` is only evaluated on `A`, where the bound `hfb` is available. -/
theorem integrableOn_fibCoord_mul {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {A : Set E3} {fib : E3 → ℝ} (hfm : Measurable fib) (hfib0 : ∀ z, 0 ≤ fib z)
    {Cf : ℝ} (hfb : ∀ z ∈ A, fib z ≤ Cf)
    {S : X N → ℝ} (hSm : Measurable S) {CS : ℝ} (hCS : 0 ≤ CS)
    (hSb : ∀ x ∈ abox N ℓ, |S x| ≤ CS) (i : Fin N) (hSz : ∀ x, x i ∉ A → S x = 0) :
    IntegrableOn (fun x : X N => fib (x i) * S x) (abox N ℓ) volume := by
  refine IntegrableOn.of_bound (abox_lt_top N ℓ hℓ.le)
    ((hfm.comp (measurable_pi_apply i)).aestronglyMeasurable.mul hSm.aestronglyMeasurable)
    (max Cf 0 * CS) ?_
  rw [ae_restrict_iff' (abox_measurable N ℓ)]
  refine ae_of_all _ (fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hfib0 (x i))]
  by_cases hxi : x i ∈ A
  · exact mul_le_mul (le_trans (hfb _ hxi) (le_max_left _ _)) (hSb x hx) (abs_nonneg _)
      (le_max_right _ _)
  · rw [hSz x hxi, abs_zero, mul_zero]
    exact mul_nonneg (le_max_right _ _) hCS

/-- The per-slot `λ = 4` weighted Young inequality, in the exact integrand shape of the target. -/
private lemma slotAMGM {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {fib : E3 → ℝ}
    (hfib0 : ∀ z, 0 ≤ fib z) {u v : X N → ℝ} (i : Fin N)
    (hWu2 : IntegrableOn (fun x : X N => fib (x i) * (u x) ^ 2) (abox N ℓ) volume)
    (hWv2 : IntegrableOn (fun x : X N => fib (x i) * (v x) ^ 2) (abox N ℓ) volume)
    (hWuv : IntegrableOn (fun x : X N => fib (x i) * (u x * v x)) (abox N ℓ) volume) :
    -(4 * (∫ x in abox N ℓ, fib (x i) * (u x) ^ 2)
        + 4⁻¹ * (∫ x in abox N ℓ, fib (x i) * (v x) ^ 2))
      ≤ 2 * (∫ x in abox N ℓ, u x * fib (x i) * v x) := by
  have h := weighted_amgm_integral (N := N) (ℓ := ℓ) hℓ
    (W := fun x : X N => fib (x i)) (u := u) (v := v) (lam := 4)
    (fun x => hfib0 (x i)) (by norm_num) hWu2 hWv2 hWuv
  have hcross : (∫ x in abox N ℓ, fib (x i) * (u x * v x))
      = ∫ x in abox N ℓ, u x * fib (x i) * v x := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hcross] at h
  exact h

theorem boxSharpPairingAMGMB1 {N : ℕ} {ℓ volA c : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (hc : 0 ≤ c)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfm : Measurable fib)
    (hfib0 : ∀ z, 0 ≤ fib z) {Cf : ℝ} (hfb : ∀ z ∈ A, fib z ≤ Cf)
    (hfibint : MeasureTheory.IntegrableOn (fun z => fib z ^ 2) A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    - (4 / volA) * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          fib (x i) * (Work.BoseFixB1S.n0FunOp volA A
            (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
            (Work.UBBInputs8.boxQInd volA A i Φ)) x ^ 2)
      - ((∫ z in A, fib z) / (4 * volA ^ 2)) * (∑ i : Fin N,
          ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.n0FunOp volA A
            (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
            (Work.UBBInputs8.boxPInd volA A i Φ)) x ^ 2)
      ≤ (2 / volA) * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.n0FunOp volA A
              (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
              (Work.UBBInputs8.boxQInd volA A i Φ)) x * fib (x i)
            * (Work.BoseFixB1S.n0FunOp volA A
              (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
              (Work.UBBInputs8.boxPInd volA A i Φ)) x) := by
  classical
  -- ## 0. the fibre bound in the absolute-value form used by the corpus
  have hfbb : ∀ z ∈ A, |fib z| ≤ max Cf 0 := by
    intro z hz
    rw [abs_of_nonneg (hfib0 z)]
    exact le_trans (hfb z hz) (le_max_left _ _)
  -- ## 1. the coefficient bound on the spectrum `{0,…,N}`
  have hcard_le : ∀ S : Finset (Fin N), (S.card : ℝ) ≤ (N : ℝ) := by
    intro S
    have h := Finset.card_le_univ S
    rw [Fintype.card_fin] at h
    exact_mod_cast h
  have hgP : ∀ S : Finset (Fin N),
      |(fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c) (S.card : ℝ)|
        ≤ Real.sqrt ((N : ℝ) + 1) + Real.sqrt c := by
    intro S
    have h1 : Real.sqrt ((S.card : ℝ) + 1) ≤ Real.sqrt ((N : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by have := hcard_le S; linarith)
    rw [abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    linarith [Real.sqrt_nonneg c]
  have hgM : ∀ S : Finset (Fin N),
      |(fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c) (S.card : ℝ)|
        ≤ Real.sqrt ((N : ℝ) + 1) + Real.sqrt c := by
    intro S
    have h1 : Real.sqrt ((S.card : ℝ) + 1) ≤ Real.sqrt ((N : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by have := hcard_le S; linarith)
    calc |Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt c|
        ≤ |Real.sqrt ((S.card : ℝ) + 1)| + |Real.sqrt c| := abs_sub _ _
      _ = Real.sqrt ((S.card : ℝ) + 1) + Real.sqrt c := by
          rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt ((N : ℝ) + 1) + Real.sqrt c := by linarith
  have hΦg : GoodState ℓ Φ := continuous_goodState hℓ hΦc
  -- ## 2. the per-slot `λ = 4` AM–GM
  have hper : ∀ i : Fin N,
      -(4 * (∫ x in abox N ℓ, fib (x i) *
            (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
              (UBBInputs8.boxQInd volA A i Φ)) x ^ 2)
          + 4⁻¹ * (∫ x in abox N ℓ, fib (x i) *
            (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
              (UBBInputs8.boxPInd volA A i Φ)) x ^ 2))
        ≤ 2 * (∫ x in abox N ℓ,
            (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
              (UBBInputs8.boxQInd volA A i Φ)) x * fib (x i)
            * (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
              (UBBInputs8.boxPInd volA A i Φ)) x) := by
    intro i
    set u : X N → ℝ := n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
      (UBBInputs8.boxQInd volA A i Φ) with hu
    set v : X N → ℝ := n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
      (UBBInputs8.boxPInd volA A i Φ) with hv
    have hQg : GoodState ℓ (UBBInputs8.boxQInd volA A i Φ) :=
      goodState_boxQInd hℓ hvol hA hvolA hAc i hΦg
    have hPg : GoodState ℓ (UBBInputs8.boxPInd volA A i Φ) :=
      goodState_boxPInd hℓ hvol hA hvolA hAc i hΦg
    have hug : GoodState ℓ u := by
      rw [hu]
      exact goodState_n0FunOp hℓ hvol hA hvolA hAc
        (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c) hgP hQg
    have hvg : GoodState ℓ v := by
      rw [hv]
      exact goodState_n0FunOp hℓ hvol hA hvolA hAc
        (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c) hgM hPg
    obtain ⟨hum, Cu, huB⟩ := hug
    obtain ⟨hvm, Cv, hvB⟩ := hvg
    -- the two states vanish off `xᵢ ∈ A`
    have hzu : ∀ x : X N, x i ∉ A → u x = 0 := by
      intro x hx
      rw [hu]
      exact n0ZeroProp_n0FunOp (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
        (n0ZeroProp_base (volA := volA) (A := A) (i := i) Φ) x hx
    have hzv : ∀ x : X N, x i ∉ A → v x = 0 := by
      intro x hx
      rw [hv]
      have h0 : n0ZeroProp A i (UBBInputs8.boxPInd volA A i Φ) := by
        intro y hy
        simp only [UBBInputs8.boxPInd]
        rw [Set.indicator_of_notMem hy, mul_zero]
      exact n0ZeroProp_n0FunOp (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c) h0 x hx
    have huC : ∀ x ∈ abox N ℓ, |u x| ≤ max Cu 0 :=
      fun x hx => le_trans (huB x hx) (le_max_left _ _)
    have hvC : ∀ x ∈ abox N ℓ, |v x| ≤ max Cv 0 :=
      fun x hx => le_trans (hvB x hx) (le_max_left _ _)
    -- the three integrability statements
    have hIu2 : IntegrableOn (fun x : X N => fib (x i) * (u x) ^ 2) (abox N ℓ) volume :=
      integrableOn_fibCoord_mul hℓ hfm hfib0 hfb (S := fun x : X N => (u x) ^ 2)
        (hum.pow_const 2) (CS := (max Cu 0) ^ 2) (sq_nonneg _)
        (fun x hx => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (huC x hx) 2)
        i (fun x hx => by rw [hzu x hx]; ring)
    have hIv2 : IntegrableOn (fun x : X N => fib (x i) * (v x) ^ 2) (abox N ℓ) volume :=
      integrableOn_fibCoord_mul hℓ hfm hfib0 hfb (S := fun x : X N => (v x) ^ 2)
        (hvm.pow_const 2) (CS := (max Cv 0) ^ 2) (sq_nonneg _)
        (fun x hx => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hvC x hx) 2)
        i (fun x hx => by rw [hzv x hx]; ring)
    have huv : IntegrableOn (fun x : X N => fib (x i) * (u x * v x)) (abox N ℓ) volume :=
      integrableOn_fibCoord_mul hℓ hfm hfib0 hfb (S := fun x : X N => u x * v x)
        (hum.mul hvm) (CS := max Cu 0 * max Cv 0)
        (mul_nonneg (le_max_right _ _) (le_max_right _ _))
        (fun x hx => by
          rw [abs_mul]
          exact mul_le_mul (huC x hx) (hvC x hx) (abs_nonneg _) (le_max_right _ _))
        i (fun x hx => by rw [hzu x hx, zero_mul])
    exact slotAMGM hℓ hfib0 i hIu2 hIv2 huv
  -- ## 3. sum the per-slot bounds
  have hsum : -(4 * (∑ i : Fin N, ∫ x in abox N ℓ, fib (x i) *
            (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
              (UBBInputs8.boxQInd volA A i Φ)) x ^ 2)
          + 4⁻¹ * (∑ i : Fin N, ∫ x in abox N ℓ, fib (x i) *
            (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
              (UBBInputs8.boxPInd volA A i Φ)) x ^ 2))
      ≤ 2 * (∑ i : Fin N, ∫ x in abox N ℓ,
            (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
              (UBBInputs8.boxQInd volA A i Φ)) x * fib (x i)
            * (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
              (UBBInputs8.boxPInd volA A i Φ)) x) := by
    have h := Finset.sum_le_sum (s := Finset.univ)
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hper i)
    rwa [Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum] at h
  -- ## 4. the fibre collapse of the `P`-side
  have hB : (∑ i : Fin N, ∫ x in abox N ℓ, fib (x i) *
        (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
          (UBBInputs8.boxPInd volA A i Φ)) x ^ 2)
      = ((∫ z in A, fib z) / volA)
        * (∑ i : Fin N, ∫ x in abox N ℓ,
            (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
              (UBBInputs8.boxPInd volA A i Φ)) x ^ 2) :=
    boxPmassFibreB1 (N := N) (ℓ := ℓ) (volA := volA) (c := c)
      hℓ hvol hA hvolA hAc hc hfm hfbb hΦc
  rw [hB] at hsum
  -- ## 5. divide by `volA` and rewrite the two coefficients
  have hscaled : (1 / volA) * (-(4 * (∑ i : Fin N, ∫ x in abox N ℓ, fib (x i) *
          (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
            (UBBInputs8.boxQInd volA A i Φ)) x ^ 2)
        + 4⁻¹ * (((∫ z in A, fib z) / volA) * (∑ i : Fin N, ∫ x in abox N ℓ,
            (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
              (UBBInputs8.boxPInd volA A i Φ)) x ^ 2))))
      ≤ (1 / volA) * (2 * (∑ i : Fin N, ∫ x in abox N ℓ,
          (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
              (UBBInputs8.boxQInd volA A i Φ)) x * fib (x i)
            * (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
              (UBBInputs8.boxPInd volA A i Φ)) x)) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have hLcoef : -(4 / volA) * (∑ i : Fin N, ∫ x in abox N ℓ, fib (x i) *
          (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
            (UBBInputs8.boxQInd volA A i Φ)) x ^ 2)
      - ((∫ z in A, fib z) / (4 * volA ^ 2)) * (∑ i : Fin N, ∫ x in abox N ℓ,
          (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
            (UBBInputs8.boxPInd volA A i Φ)) x ^ 2)
      = (1 / volA) * (-(4 * (∑ i : Fin N, ∫ x in abox N ℓ, fib (x i) *
            (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
              (UBBInputs8.boxQInd volA A i Φ)) x ^ 2)
          + 4⁻¹ * (((∫ z in A, fib z) / volA) * (∑ i : Fin N, ∫ x in abox N ℓ,
              (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
                (UBBInputs8.boxPInd volA A i Φ)) x ^ 2)))) := by
    field_simp
    ring
  have hRcoef : (1 / volA) * (2 * (∑ i : Fin N, ∫ x in abox N ℓ,
          (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
              (UBBInputs8.boxQInd volA A i Φ)) x * fib (x i)
            * (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
              (UBBInputs8.boxPInd volA A i Φ)) x))
      = (2 / volA) * (∑ i : Fin N, ∫ x in abox N ℓ,
          (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
              (UBBInputs8.boxQInd volA A i Φ)) x * fib (x i)
            * (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
              (UBBInputs8.boxPInd volA A i Φ)) x) := by
    ring
  rw [hLcoef, ← hRcoef]
  exact hscaled

end Work.BoseFixB1S
