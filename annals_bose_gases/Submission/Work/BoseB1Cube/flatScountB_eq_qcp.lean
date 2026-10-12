import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.peelChiSq_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.flatScountB_eq_qcp`

The cutoff-weighted count `flatScountB M ℓ d u Φ = ∫_{abox n ℓ} Φ² Σᵢχ_{B(u)}(xᵢ)²`
(`Work.BoseFixB1.flatScountB`, `Work.BoseFixB1.nCountB`) is, slot by slot, the `χ²`-mass of
FS's box decomposition `Φ = P_{B,i}Φ + Q_{B,i}Φ` against the two ind-actored projections
`Work.UBBInputs8.boxPInd` / `boxQInd`:

    flatScountB = Σᵢ∫(χ·QᵢΦ)² + 2Σᵢ∫χ²(QᵢΦ)(PᵢΦ) + Σᵢ∫(χ·PᵢΦ)² .

The mathematics is the pointwise identity

    χ(xᵢ)·Φ = χ(xᵢ)·PᵢΦ + χ(xᵢ)·QᵢΦ ,

which holds because `Pᵢ + Qᵢ = 1_{B(u)}(xᵢ)·Φ` (the definition of `boxQInd`) and because the
cutoff `χ_{B(u)}` is **supported in the sliding box** `B(u) = dlBox ℓ d u`
(`Work.BoseFixB1S.chiSmallB_support_subset_dlBox`), so `χ·1_{B(u)} = χ`.  Squaring and using
`QᵢΦ = 1_{B(u)}(xᵢ)Φ − PᵢΦ` gives the per-slot identity; the integral version follows by
splitting the sum inside the integral (`flattenScountB_eq_sum`) and the integrand
(`MeasureTheory.integral_add`), the integrability of the three pieces being the boundedness on
the compact box `abox n ℓ` of `Φ`, of `χ` and of the two projections
(`Work.BoseFixB1S.integrableOn_sq_of_bound`, `integrableOn_mul_of_bound`,
`abs_boxPInd_le`).

Added here: the per-slot identity `chiQPC_expand_slot` and the target.
-/

namespace Work.BoseB1Cube

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The per-slot expansion.**  For one slot `i`, the `χ²`-weighted square of `Φ` is the sum of
the `χ²`-weighted squares of the excited part `QᵢΦ` and of the condensate part `PᵢΦ`, plus twice
the (weighted) cross term. -/
theorem chiQPC_expand_slot {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) (i : Fin n) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2)
      = (∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiSmallB M ℓ d u (x i)
            * Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2)
        + 2 * (∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
              * Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x
              * Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x)
        + (∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.chiSmallB M ℓ d u (x i)
              * Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2) := by
  set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set χ : E3 → ℝ := Submission.BoseGases.chiSmallB M ℓ d u with hχdef
  set P : Submission.BoseGases.X n → ℝ := Work.UBBInputs8.boxPInd V A i Φ with hPdef
  set Q : Submission.BoseGases.X n → ℝ := Work.UBBInputs8.boxQInd V A i Φ with hQdef
  have hAmeas : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hVeq : V = (MeasureTheory.volume : MeasureTheory.Measure E3).real A := by
    rw [hVdef, hAdef]; exact Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox n ℓ) (f := Φ) hΦc.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB _ (Submission.BoseGases.zero_mem_abox hℓ.le))
  have hΦb : ∀ x ∈ Submission.BoseGases.abox n ℓ, |Φ x| ≤ B :=
    fun x hx => by simpa [Real.norm_eq_abs] using hB x hx
  have hPmeas : Measurable P := by
    rw [hPdef]; exact Work.BoseFixB1S.measurable_boxPInd V A hAmeas i hΦc.measurable
  have hPb : ∀ x ∈ Submission.BoseGases.abox n ℓ, |P x| ≤ B := by
    intro x hx
    rw [hPdef]
    exact Work.BoseFixB1S.abs_boxPInd_le hℓ hV hAmeas hVeq hAc i hΦb x hx
  have hQeq : Q = fun x => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x - P x := by
    rw [hQdef, hPdef]; rfl
  have hPQ : ∀ x : Submission.BoseGases.X n,
      A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x = P x + Q x := by
    intro x; rw [hQeq]; ring
  have hχcont : Continuous χ := by
    rw [hχdef]; exact Work.BoseFixB1S.chiSmallB_continuous hM ℓ d u
  have hχbd : ∀ z : E3,
      |χ z| ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
    intro z; rw [hχdef]; exact Work.BoseFixB1S.abs_chiSmallB_le_supB hM u z
  have hCnn : 0 ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
    le_trans (abs_nonneg _) (hχbd 0)
  have hQmeas : Measurable Q := by
    rw [hQeq]
    exact (((measurable_const.indicator hAmeas).comp (measurable_pi_apply i)).mul
      hΦc.measurable).sub hPmeas
  have hQb : ∀ x ∈ Submission.BoseGases.abox n ℓ, |Q x| ≤ 2 * B := by
    intro x hx
    rw [hQeq]
    have h1 : |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ≤ B := by
      have h2 : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
        by_cases h : x i ∈ A
        · rw [Set.indicator_of_mem h]; norm_num
        · rw [Set.indicator_of_notMem h]; norm_num
      rw [abs_mul]
      calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x|
          ≤ 1 * B := mul_le_mul h2 (hΦb x hx) (abs_nonneg _) zero_le_one
        _ = B := one_mul B
    calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x + -P x|
        ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| + |-P x| := abs_add_le _ _
      _ = |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| + |P x| := by rw [abs_neg]
      _ ≤ B + B := add_le_add h1 (hPb x hx)
      _ = 2 * B := by ring
  have hχimeas : Measurable (fun x : Submission.BoseGases.X n => χ (x i)) :=
    hχcont.measurable.comp (measurable_pi_apply i)
  have hIQ2 : IntegrableOn (fun x : Submission.BoseGases.X n => (χ (x i) * Q x) ^ 2)
      (Submission.BoseGases.abox n ℓ) :=
    Work.BoseFixB1S.integrableOn_sq_of_bound hℓ (hχimeas.mul hQmeas) (fun x hx => by
      rw [abs_mul]
      exact mul_le_mul (hχbd (x i)) (hQb x hx) (abs_nonneg _) hCnn)
  have hIP2 : IntegrableOn (fun x : Submission.BoseGases.X n => (χ (x i) * P x) ^ 2)
      (Submission.BoseGases.abox n ℓ) :=
    Work.BoseFixB1S.integrableOn_sq_of_bound hℓ (hχimeas.mul hPmeas) (fun x hx => by
      rw [abs_mul]
      exact mul_le_mul (hχbd (x i)) (hPb x hx) (abs_nonneg _) hCnn)
  have hIQP : IntegrableOn (fun x : Submission.BoseGases.X n => (χ (x i)) ^ 2 * Q x * P x)
      (Submission.BoseGases.abox n ℓ) :=
    Work.BoseFixB1S.integrableOn_mul_of_bound hℓ ((hχimeas.pow_const 2).mul hQmeas) hPmeas
      (Cf := (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
        * (2 * B))
      (Cg := B)
      (fun x hx => by
        rw [abs_mul]
        have h2 : |(χ (x i)) ^ 2|
            ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2 := by
          rw [abs_of_nonneg (sq_nonneg _), ← sq_abs (χ (x i))]
          exact pow_le_pow_left₀ (abs_nonneg _) (hχbd (x i)) 2
        exact mul_le_mul h2 (hQb x hx) (abs_nonneg _) (by positivity))
      (fun x hx => hPb x hx)
  -- the pointwise identity, on the support of the cutoff
  have hpw : ∀ x : Submission.BoseGases.X n,
      (Φ x) ^ 2 * (χ (x i)) ^ 2
        = ((χ (x i) * Q x) ^ 2 + 2 * ((χ (x i)) ^ 2 * Q x * P x)) + (χ (x i) * P x) ^ 2 := by
    intro x
    have hsupp := Work.BoseFixB1S.chiSmallB_support_subset_dlBox (M := M) hM hℓ hd u
    have hχind : χ (x i) * A.indicator (fun _ => (1 : ℝ)) (x i) = χ (x i) := by
      by_cases h : x i ∈ A
      · rw [Set.indicator_of_mem h, mul_one]
      · rw [Set.indicator_of_notMem h, mul_zero]
        have h0 : χ (x i) = 0 := by
          by_contra hne
          exact h (hsupp (Function.mem_support.mpr hne))
        rw [h0]
    have hkey : χ (x i) * Φ x = χ (x i) * P x + χ (x i) * Q x := by
      have h2 : χ (x i) * (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) = χ (x i) * Φ x := by
        rw [← mul_assoc, hχind]
      calc χ (x i) * Φ x
          = χ (x i) * (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) := h2.symm
        _ = χ (x i) * (P x + Q x) := by rw [hPQ x]
        _ = χ (x i) * P x + χ (x i) * Q x := by ring
    calc (Φ x) ^ 2 * (χ (x i)) ^ 2 = (χ (x i) * Φ x) ^ 2 := by ring
      _ = (χ (x i) * P x + χ (x i) * Q x) ^ 2 := by rw [hkey]
      _ = _ := by ring
  -- split the integral of the sum into the three pieces
  have hsplit1 : (∫ x in Submission.BoseGases.abox n ℓ,
        ((χ (x i) * Q x) ^ 2 + 2 * ((χ (x i)) ^ 2 * Q x * P x)) + (χ (x i) * P x) ^ 2)
      = (∫ x in Submission.BoseGases.abox n ℓ,
          ((χ (x i) * Q x) ^ 2 + 2 * ((χ (x i)) ^ 2 * Q x * P x)))
        + (∫ x in Submission.BoseGases.abox n ℓ, (χ (x i) * P x) ^ 2) :=
    integral_add (hIQ2.add (hIQP.const_mul 2)) hIP2
  have hsplit2 : (∫ x in Submission.BoseGases.abox n ℓ,
          ((χ (x i) * Q x) ^ 2 + 2 * ((χ (x i)) ^ 2 * Q x * P x)))
      = (∫ x in Submission.BoseGases.abox n ℓ, (χ (x i) * Q x) ^ 2)
        + (∫ x in Submission.BoseGases.abox n ℓ, 2 * ((χ (x i)) ^ 2 * Q x * P x)) :=
    integral_add hIQ2 (hIQP.const_mul 2)
  have hsplit3 : (∫ x in Submission.BoseGases.abox n ℓ, 2 * ((χ (x i)) ^ 2 * Q x * P x))
      = 2 * (∫ x in Submission.BoseGases.abox n ℓ, (χ (x i)) ^ 2 * Q x * P x) :=
    integral_const_mul 2 _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpw), hsplit1, hsplit2, hsplit3]

theorem flatScountB_eq_qcp {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    Work.BoseFixB1.flatScountB M ℓ d u Φ
      = (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiSmallB M ℓ d u (x i)
            * Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2)
        + 2 * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
              * Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x
              * Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x)
        + (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.chiSmallB M ℓ d u (x i)
              * Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2) := by
  rw [Work.BoseB1Cube.flatScountB_eq_sum (M := M) hM hℓ u hΦc]
  have hsum : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2)
      = ∑ i : Fin n,
          ((∫ x in Submission.BoseGases.abox n ℓ,
              (Submission.BoseGases.chiSmallB M ℓ d u (x i)
                * Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2)
            + 2 * (∫ x in Submission.BoseGases.abox n ℓ,
                (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
                  * Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) i Φ x
                  * Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) i Φ x)
            + (∫ x in Submission.BoseGases.abox n ℓ,
                (Submission.BoseGases.chiSmallB M ℓ d u (x i)
                  * Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                      (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2)) :=
    Finset.sum_congr rfl (fun i _ => chiQPC_expand_slot hM hℓ hd u hV hΦc i)
  rw [hsum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]

end Work.BoseB1Cube
