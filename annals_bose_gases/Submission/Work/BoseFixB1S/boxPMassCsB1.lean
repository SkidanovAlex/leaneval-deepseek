import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.PQIdentAux
import Submission.Work.BoseFixB1S.flatSlotFib_integrable
import Submission.Work.BoseFixB1S.intAbsCS
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxPMassCsB1` — the `P`-mass Cauchy–Schwarz of the per-box cross term

The per-box cross term of the mean-field analysis pairs the two FS box projections in one slot
against a *fibre weight* `fib(xᵢ)`:

  `Σᵢ ∫_{abox N ℓ} (Q_{B,i}Φ)(x)·fib(xᵢ)·(P_{B,i}Φ)(x)`,

and the estimate needed is the Cauchy–Schwarz bound

  `(Σᵢ ∫ Q_{B,i}Φ·fib(xᵢ)·P_{B,i}Φ)² ≤ (Σᵢ ∫ (Q_{B,i}Φ)²·fib(xᵢ)) · κ·S`,

where `S = Σᵢ ∫ (P_{B,i}Φ)²` is the localised flat count (`boxFlatCount`) and
`κ = (∫_A fib)/V` is the fibre average of `fib` on the box `A`.

The mechanism has three independent ingredients.

* **The `P`-side fibre collapse** (`boxPIndFibSumB1`) — for each slot, `P_{B,i}Φ` is
  `P_{B,i}`-fixed, so the *peel* `flatSlotFib_integrable` applies: the weighted `P`-mass is the
  fibre average `κ` times the unweighted one,

    `∫ (P_{B,i}Φ)²·fib(xᵢ) = κ·∫ (P_{B,i}Φ)²` .

  For this only `IntegrableOn fib A` is needed (no boundedness of `fib`): the fibre of a
  `P`-fixed slot is carried by the box indicator, so only the values of `fib` on `A` matter.

* **The weighted Cauchy–Schwarz** (`boxQIPICsfibB1`) — per slot, `L²`-Cauchy–Schwarz at the
  weight `fib(xᵢ)`:

    `|∫ (Q_{B,i}Φ)·fib(xᵢ)·(P_{B,i}Φ)| ≤ √(∫ (Q_{B,i}Φ)²·fib(xᵢ))·√(∫ (P_{B,i}Φ)²·fib(xᵢ))` .

  Both weighted squares are integrable because `Q_{B,i}Φ` and `P_{B,i}Φ` carry the box indicator
  `1_A(xᵢ)` (so their `fib(xᵢ)`-weighted squares only see `fib` on `A`) and `Φ` is bounded on the
  compact box, so `integrableOn_coord_fib` applies to the pair
  `(bounded slot factor) × (indicator fibre)`.

* **The assembly** (this file) — the abstract finite-sum Cauchy–Schwarz
  `sum_sqrt_cs_sq_le`: from per-slot bounds `|Fᵢ| ≤ √(Qᵢ)·√(Pᵢ)` with `Qᵢ, Pᵢ ≥ 0` and a *sum*
  identity `ΣᵢPᵢ = κ·S`, conclude `(ΣᵢFᵢ)² ≤ (ΣᵢQᵢ)·(κ·S)`.  Instantiating
  `Fᵢ = ∫Q_{B,i}Φ·fib(xᵢ)·P_{B,i}Φ`, `Qᵢ = ∫(Q_{B,i}Φ)²·fib(xᵢ)`, `Pᵢ = ∫(P_{B,i}Φ)²·fib(xᵢ)`,
  `S = boxFlatCount`, `κ = (∫_A fib)/V` gives the target.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The abstract finite-sum Cauchy–Schwarz used by the assembly -/

/-- **Finite-sum Cauchy–Schwarz with a summed right factor.**  If `|Fᵢ| ≤ √Qᵢ·√Pᵢ` for every
`i`, all `Qᵢ, Pᵢ ≥ 0`, and `ΣᵢPᵢ = κ·S`, then

  `(ΣᵢFᵢ)² ≤ (ΣᵢQᵢ)·(κ·S)` .

Route: `|ΣᵢFᵢ| ≤ Σᵢ|Fᵢ| ≤ Σᵢ√Qᵢ√Pᵢ ≤ √(ΣᵢQᵢ)·√(ΣᵢPᵢ)` (the last step is
`Real.sum_sqrt_mul_sqrt_le`), and then `sq_le_sq'` with `Real.sq_sqrt`. -/
theorem sum_sqrt_cs_sq_le {n : ℕ} {F Q P : Fin n → ℝ} {κ S : ℝ}
    (hQ0 : ∀ i, 0 ≤ Q i) (hP0 : ∀ i, 0 ≤ P i)
    (hper : ∀ i, |F i| ≤ Real.sqrt (Q i) * Real.sqrt (P i))
    (hPsum : ∑ i, P i = κ * S) :
    (∑ i, F i) ^ 2 ≤ (∑ i, Q i) * (κ * S) := by
  have habs : |∑ i, F i| ≤ Real.sqrt (∑ i, Q i) * Real.sqrt (∑ i, P i) := by
    refine le_trans ?_ (Real.sum_sqrt_mul_sqrt_le Finset.univ hQ0 hP0)
    refine le_trans ?_ (Finset.sum_le_sum (fun i _ => hper i))
    simpa using Finset.abs_sum_le_sum_abs F (Finset.univ : Finset (Fin n))
  have h1 := abs_le.mp habs
  have h2 := sq_le_sq' h1.1 h1.2
  have hs2 : (Real.sqrt (∑ i, Q i) * Real.sqrt (∑ i, P i)) ^ 2
      = (∑ i, Q i) * (∑ i, P i) := by
    rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => hQ0 i)),
      Real.sq_sqrt (Finset.sum_nonneg (fun i _ => hP0 i))]
  rw [hs2, hPsum] at h2
  exact h2

/-! ## 2. The `P`-side fibre collapse -/

/-- **The `P`-side fibre collapse (summed over the slots).**  For a fibre `fib` integrable on the
box `A` (of volume `V > 0`), the `fib(xᵢ)`-weighted `P`-mass equals the fibre average
`κ = (∫_A fib)/V` times the localised flat count:

  `Σᵢ ∫_{abox N ℓ} (P_{B,i}Φ)²·fib(xᵢ) = κ·boxFlatCount V ℓ A Φ` .

Per slot this is `flatSlotFib_integrable` at `Ψ = Θ = P_{B,i}Φ` (which is `P_{B,i}`-fixed,
measurable and bounded on the box by the bound of `Φ`). -/
theorem boxPIndFibSumB1 {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfibint : MeasureTheory.IntegrableOn fib A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * fib (x i))
      = ((∫ z in A, fib z) / V) * Work.BoseFixB1S.boxFlatCount V ℓ A Φ := by
  classical
  have hVreal : V = (MeasureTheory.volume : MeasureTheory.Measure E3).real A := by
    rw [MeasureTheory.Measure.real_def]
    exact hVeq
  -- `Φ` is bounded on the compact box
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox N ℓ) (f := Φ) hΦc.continuousOn
  have hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ C := fun x hx => by
    simpa [Real.norm_eq_abs] using hC x hx
  rcases N with _ | n
  · -- no slots: both sides vanish
    simp [Work.BoseFixB1S.boxFlatCount]
  · -- the per-slot fibre identity, summed over the slots
    have hper : ∀ i : Fin (n + 1),
        (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * fib (x i))
          = ((∫ z in A, fib z) / V)
              * ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                  (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 := by
      intro i
      have hΨm : Measurable (Work.UBBInputs8.boxPInd V A i Φ) :=
        measurable_boxPInd V A hA i hΦc.measurable
      have hfix : Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A i Φ)
          = Work.UBBInputs8.boxPInd V A i Φ := by
        funext x
        exact boxPInd_idempotent hℓ hV hA hVeq hAc i Φ x
      have hPb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ,
          |Work.UBBInputs8.boxPInd V A i Φ x| ≤ C :=
        abs_boxPInd_le hℓ hV hA hVeq hAc i hΦb
      have h := flatSlotFib_integrable (n := n) (ℓ := ℓ) (volA := V) hℓ hV hA hVreal hAc i
        hΨm hΨm hfix hfix hPb hPb (fib := fib) hfibint
      -- `h : ∫ P·P·fib(xᵢ) = (1/V·∫_A fib)·∫ P·P`
      have e1 : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            Work.UBBInputs8.boxPInd V A i Φ x * Work.UBBInputs8.boxPInd V A i Φ x * fib (x i))
          = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * fib (x i) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
      have e2 : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            Work.UBBInputs8.boxPInd V A i Φ x * Work.UBBInputs8.boxPInd V A i Φ x)
          = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
      rw [← e1, h, e2]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hper i), ← Finset.mul_sum]
    simp only [Work.BoseFixB1S.boxFlatCount]

/-! ## 3. The weighted Cauchy–Schwarz at the box projections -/

/-- **The single-slot weighted Cauchy–Schwarz at the box projections.**  For a measurable
nonnegative fibre `fib` integrable on the box `A ⊆ acube ℓ` of volume `V > 0` and a continuous
state `Φ`, the `fib(xᵢ)`-weighted pairing of the two FS box projections obeys

  `|∫ Q_{B,i}Φ·fib(xᵢ)·P_{B,i}Φ| ≤ √(∫ (Q_{B,i}Φ)²·fib(xᵢ))·√(∫ (P_{B,i}Φ)²·fib(xᵢ))` .

This is `L²`-Cauchy–Schwarz at the weight `fib(xᵢ)`, i.e.
`int_abs_mul_le_sqrt_mul_sqrt` applied to `Q_{B,i}Φ·√fib(xᵢ)` and `P_{B,i}Φ·√fib(xᵢ)`.  The two
weighted squares are integrable: both projections carry the box indicator `1_A(xᵢ)`, hence their
weighted squares are `(bounded on the box) × (indicator·fib)(xᵢ)`, which is the shape of
`integrableOn_coord_fib`. -/
theorem boxQIPICsfibB1 {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfm : Measurable fib) (hfib0 : ∀ z, 0 ≤ fib z)
    (hfibint : MeasureTheory.IntegrableOn fib A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (i : Fin N) :
    |∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
          * (Work.UBBInputs8.boxPInd V A i Φ x)|
      ≤ Real.sqrt (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 * fib (x i))
        * Real.sqrt (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * fib (x i)) := by
  classical
  rcases N with _ | n
  · exact i.elim0
  -- `Φ` is bounded on the compact box
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact (n + 1) hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox (n + 1) ℓ) (f := Φ) hΦc.continuousOn
  have hΦb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ, |Φ x| ≤ C := fun x hx => by
    simpa [Real.norm_eq_abs] using hC x hx
  -- the two projections: measurability and `L∞` bounds on the box
  have hQm : Measurable (Work.UBBInputs8.boxQInd V A i Φ) := by
    show Measurable (fun x : Submission.BoseGases.X (n + 1) =>
      A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x - Work.UBBInputs8.boxPInd V A i Φ x)
    exact (((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul hΦc.measurable).sub
      (measurable_boxPInd V A hA i hΦc.measurable)
  have hPm : Measurable (Work.UBBInputs8.boxPInd V A i Φ) :=
    measurable_boxPInd V A hA i hΦc.measurable
  have hPb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ,
      |Work.UBBInputs8.boxPInd V A i Φ x| ≤ C :=
    abs_boxPInd_le hℓ hV hA hVeq hAc i hΦb
  have hind1 : ∀ x : Submission.BoseGases.X (n + 1),
      |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
    intro x
    by_cases hxi : x i ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
  have hQb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ,
      |Work.UBBInputs8.boxQInd V A i Φ x| ≤ 2 * C := by
    intro x hx
    have h1 : |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ≤ C := by
      rw [abs_mul]
      calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x| ≤ 1 * C :=
            mul_le_mul (hind1 x) (hΦb x hx) (abs_nonneg _) (by norm_num)
        _ = C := one_mul C
    calc |Work.UBBInputs8.boxQInd V A i Φ x|
        = |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
            - Work.UBBInputs8.boxPInd V A i Φ x| := rfl
      _ ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x|
            + |Work.UBBInputs8.boxPInd V A i Φ x| := abs_sub _ _
      _ ≤ C + C := add_le_add h1 (hPb x hx)
      _ = 2 * C := by ring
  -- the slot-`i` mean, and the pointwise structure of the two projections
  set mean : Submission.BoseGases.X (n + 1) → ℝ :=
    fun x => (1 / V) * ∫ z in A, Φ (Function.update x i z) with hmean
  have hPpt : ∀ x : Submission.BoseGases.X (n + 1),
      Work.UBBInputs8.boxPInd V A i Φ x = mean x * A.indicator (fun _ => (1 : ℝ)) (x i) := by
    intro x
    simp only [Work.UBBInputs8.boxPInd, hmean]
  have hQpt : ∀ x : Submission.BoseGases.X (n + 1),
      Work.UBBInputs8.boxQInd V A i Φ x
        = A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x - mean x) := by
    intro x
    simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, hmean]
    ring
  -- integrability of the two weighted squares
  have hPint : Integrable (fun x : Submission.BoseGases.X (n + 1) =>
      (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * fib (x i))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)) := by
    have hFm : AEStronglyMeasurable (fun x : Submission.BoseGases.X (n + 1) =>
        (Work.UBBInputs8.boxPInd V A i Φ x * Work.UBBInputs8.boxPInd V A i Φ x)
          * A.indicator (fun _ => (1 : ℝ)) (x i))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)) :=
      ((hPm.mul hPm).mul (((measurable_const.indicator hA).comp (measurable_pi_apply i)))).aestronglyMeasurable
    have hFb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ,
        |(Work.UBBInputs8.boxPInd V A i Φ x * Work.UBBInputs8.boxPInd V A i Φ x)
          * A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ C ^ 2 := by
      intro x hx
      have h1 : |Work.UBBInputs8.boxPInd V A i Φ x
          * Work.UBBInputs8.boxPInd V A i Φ x| ≤ C ^ 2 := by
        rw [abs_of_nonneg (mul_self_nonneg _)]
        simpa [pow_two] using
          sq_le_sq' (abs_le.mp (hPb x hx)).1 (abs_le.mp (hPb x hx)).2
      rw [abs_mul]
      calc |Work.UBBInputs8.boxPInd V A i Φ x * Work.UBBInputs8.boxPInd V A i Φ x|
            * |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ C ^ 2 * 1 :=
            mul_le_mul h1 (hind1 x) (abs_nonneg _) (by positivity)
        _ = C ^ 2 := mul_one _
    have h := integrableOn_coord_fib (N := n + 1) (ℓ := ℓ) hℓ i hA hAc hFm hFb
      (fib := fib) hfibint
    refine h.congr ?_
    filter_upwards with x
    rw [hPpt x, pow_two]
    by_cases hxi : x i ∈ A
    · simp only [Set.indicator_of_mem hxi]
      ring
    · simp only [Set.indicator_of_notMem hxi]
      ring
  have hQint : Integrable (fun x : Submission.BoseGases.X (n + 1) =>
      (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 * fib (x i))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)) := by
    have hFm : AEStronglyMeasurable (fun x : Submission.BoseGases.X (n + 1) =>
        (Work.UBBInputs8.boxQInd V A i Φ x * Work.UBBInputs8.boxQInd V A i Φ x)
          * A.indicator (fun _ => (1 : ℝ)) (x i))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)) :=
      ((hQm.mul hQm).mul (((measurable_const.indicator hA).comp (measurable_pi_apply i)))).aestronglyMeasurable
    have hFb : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ,
        |(Work.UBBInputs8.boxQInd V A i Φ x * Work.UBBInputs8.boxQInd V A i Φ x)
          * A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ (2 * C) ^ 2 := by
      intro x hx
      have h1 : |Work.UBBInputs8.boxQInd V A i Φ x
          * Work.UBBInputs8.boxQInd V A i Φ x| ≤ (2 * C) ^ 2 := by
        rw [abs_of_nonneg (mul_self_nonneg _)]
        simpa [pow_two] using
          sq_le_sq' (abs_le.mp (hQb x hx)).1 (abs_le.mp (hQb x hx)).2
      rw [abs_mul]
      calc |Work.UBBInputs8.boxQInd V A i Φ x * Work.UBBInputs8.boxQInd V A i Φ x|
            * |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ (2 * C) ^ 2 * 1 :=
            mul_le_mul h1 (hind1 x) (abs_nonneg _) (by positivity)
        _ = (2 * C) ^ 2 := mul_one _
    have h := integrableOn_coord_fib (N := n + 1) (ℓ := ℓ) hℓ i hA hAc hFm hFb
      (fib := fib) hfibint
    refine h.congr ?_
    filter_upwards with x
    rw [hQpt x, pow_two]
    by_cases hxi : x i ∈ A
    · simp only [Set.indicator_of_mem hxi]
      ring
    · simp only [Set.indicator_of_notMem hxi]
      ring
  -- the weighted `L²` square roots are measured by the two weighted squares
  have hQ2 : Integrable (fun x : Submission.BoseGases.X (n + 1) =>
      (Work.UBBInputs8.boxQInd V A i Φ x * Real.sqrt (fib (x i))) ^ 2)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)) := by
    refine hQint.congr ?_
    filter_upwards with x
    rw [mul_pow, Real.sq_sqrt (hfib0 (x i))]
  have hP2 : Integrable (fun x : Submission.BoseGases.X (n + 1) =>
      (Work.UBBInputs8.boxPInd V A i Φ x * Real.sqrt (fib (x i))) ^ 2)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)) := by
    refine hPint.congr ?_
    filter_upwards with x
    rw [mul_pow, Real.sq_sqrt (hfib0 (x i))]
  -- the pointwise collapse of the weighted product
  have hpt : ∀ x : Submission.BoseGases.X (n + 1),
      (Work.UBBInputs8.boxQInd V A i Φ x * Real.sqrt (fib (x i)))
          * (Work.UBBInputs8.boxPInd V A i Φ x * Real.sqrt (fib (x i)))
        = Work.UBBInputs8.boxQInd V A i Φ x * fib (x i) * Work.UBBInputs8.boxPInd V A i Φ x := by
    intro x
    rw [show (Work.UBBInputs8.boxQInd V A i Φ x * Real.sqrt (fib (x i)))
          * (Work.UBBInputs8.boxPInd V A i Φ x * Real.sqrt (fib (x i)))
        = Work.UBBInputs8.boxQInd V A i Φ x * Work.UBBInputs8.boxPInd V A i Φ x
          * (Real.sqrt (fib (x i)) * Real.sqrt (fib (x i))) by ring,
      Real.mul_self_sqrt (hfib0 (x i))]
    ring
  -- Cauchy–Schwarz
  have hCS := int_abs_mul_le_sqrt_mul_sqrt
    (μ := MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ))
    (f := fun x : Submission.BoseGases.X (n + 1) =>
      Work.UBBInputs8.boxQInd V A i Φ x * Real.sqrt (fib (x i)))
    (g := fun x : Submission.BoseGases.X (n + 1) =>
      Work.UBBInputs8.boxPInd V A i Φ x * Real.sqrt (fib (x i)))
    (hQm.mul (Measurable.sqrt (hfm.comp (measurable_pi_apply i)))).aestronglyMeasurable
    (hPm.mul (Measurable.sqrt (hfm.comp (measurable_pi_apply i)))).aestronglyMeasurable
    hQ2 hP2
  have e2 : (∫ x : Submission.BoseGases.X (n + 1),
        (Work.UBBInputs8.boxQInd V A i Φ x * Real.sqrt (fib (x i))) ^ 2
        ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)))
      = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 * fib (x i) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    rw [mul_pow, Real.sq_sqrt (hfib0 (x i))]
  have e3 : (∫ x : Submission.BoseGases.X (n + 1),
        (Work.UBBInputs8.boxPInd V A i Φ x * Real.sqrt (fib (x i))) ^ 2
        ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)))
      = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * fib (x i) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    rw [mul_pow, Real.sq_sqrt (hfib0 (x i))]
  calc |∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        Work.UBBInputs8.boxQInd V A i Φ x * fib (x i) * Work.UBBInputs8.boxPInd V A i Φ x|
      = |∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Work.UBBInputs8.boxQInd V A i Φ x * Real.sqrt (fib (x i)))
            * (Work.UBBInputs8.boxPInd V A i Φ x * Real.sqrt (fib (x i)))| := by
        rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => (hpt x).symm))]
    _ ≤ ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          |(Work.UBBInputs8.boxQInd V A i Φ x * Real.sqrt (fib (x i)))
            * (Work.UBBInputs8.boxPInd V A i Φ x * Real.sqrt (fib (x i)))| := by
        simpa [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_integral_norm
          (μ := MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ))
          (fun x : Submission.BoseGases.X (n + 1) =>
            (Work.UBBInputs8.boxQInd V A i Φ x * Real.sqrt (fib (x i)))
              * (Work.UBBInputs8.boxPInd V A i Φ x * Real.sqrt (fib (x i))))
    _ ≤ Real.sqrt (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x * Real.sqrt (fib (x i))) ^ 2)
          * Real.sqrt (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxPInd V A i Φ x * Real.sqrt (fib (x i))) ^ 2) := hCS
    _ = Real.sqrt (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 * fib (x i))
          * Real.sqrt (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * fib (x i)) := by rw [e2, e3]

/-! ## 4. The target -/

theorem boxPMassCsB1 {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfm : Measurable fib) (hfib0 : ∀ z, 0 ≤ fib z)
    (hfibint : MeasureTheory.IntegrableOn fib A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
          * (Work.UBBInputs8.boxPInd V A i Φ x)) ^ 2
      ≤ (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 * fib (x i))
        * (((∫ z in A, fib z) / V) * Work.BoseFixB1S.boxFlatCount V ℓ A Φ) := by
  classical
  refine sum_sqrt_cs_sq_le (F := fun i : Fin N => ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
          * (Work.UBBInputs8.boxPInd V A i Φ x))
    (Q := fun i : Fin N => ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 * fib (x i))
    (P := fun i : Fin N => ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * fib (x i))
    (κ := (∫ z in A, fib z) / V)
    (S := Work.BoseFixB1S.boxFlatCount V ℓ A Φ) ?_ ?_ ?_ ?_
  · intro i
    exact integral_nonneg_of_ae (ae_of_all _ (fun x => mul_nonneg (sq_nonneg _) (hfib0 _)))
  · intro i
    exact integral_nonneg_of_ae (ae_of_all _ (fun x => mul_nonneg (sq_nonneg _) (hfib0 _)))
  · intro i
    exact boxQIPICsfibB1 hℓ hV hA hVeq hAc hfm hfib0 hfibint hΦc i
  · exact boxPIndFibSumB1 hℓ hV hA hVeq hAc hfibint hΦc

end

end Work.BoseFixB1S
