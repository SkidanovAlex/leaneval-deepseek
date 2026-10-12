import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPIndFlat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1B

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The pointwise collapse -/

/-- **The pointwise identity.**  With `Pᵢ = boxPInd V A i Φ` and `Qᵢ = boxQInd V A i Φ`,

  `Φ(x)²·δ(xᵢ) = (PᵢΦ)²·δ(xᵢ) + (QᵢΦ)·(2·PᵢΦ + QᵢΦ)·δ(xᵢ)`.

The two ingredients are `PᵢΦ + QᵢΦ = 1_A(xᵢ)·Φ` (the definition of `Qᵢ`) and `δ = 1_A·δ`, the
latter being the support hypothesis. -/
theorem fibreDeviation_pointwise {N : ℕ} (V : ℝ) {A : Set E3} {δ : E3 → ℝ}
    (hδsupp : ∀ z, z ∉ A → δ z = 0) (i : Fin N) (Φ : X N → ℝ) (x : X N) :
    (Φ x) ^ 2 * δ (x i)
      = (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * δ (x i)
        + ((Work.UBBInputs8.boxQInd V A i Φ x)
            * (2 * Work.UBBInputs8.boxPInd V A i Φ x + Work.UBBInputs8.boxQInd V A i Φ x))
          * δ (x i) := by
  by_cases hxi : x i ∈ A
  · have hind : A.indicator (fun _ => (1 : ℝ)) (x i) = 1 :=
      Set.indicator_of_mem hxi (fun _ => (1 : ℝ))
    simp only [Work.UBBInputs8.boxPInd, Work.UBBInputs8.boxQInd, hind]
    ring
  · have hδ0 : δ (x i) = 0 := hδsupp (x i) hxi
    simp only [Work.UBBInputs8.boxPInd, Work.UBBInputs8.boxQInd,
      Set.indicator_of_notMem hxi, hδ0]
    ring

/-! ## 2. Bounds on the box -/

/-- A uniform bound of a continuous state on the analysis box. -/
theorem exists_abox_bound' {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ abox N ℓ, |Φ x| ≤ C := by
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x hx => by
    have h := hC x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)⟩

/-- **The box projection is bounded on the box** — for *every* `V > 0`, no relation between `V`
and the volume of `A` being needed.  (`Work.BoseFixB1S.abs_boxPInd_le` is the version at
`V = |A|`.) -/
theorem exists_boxPInd_bound {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) (i : Fin N) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd V A i Φ x| ≤ Cp := by
  obtain ⟨C, hC0, hCb⟩ := exists_abox_bound' hℓ hΦc
  have hfin : (volume : Measure E3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  refine ⟨(1 / V) * C * (volume A).toReal, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (by positivity) hC0) ENNReal.toReal_nonneg
  · intro x hx
    have hInt : ‖∫ z in A, Φ (Function.update x i z)‖ ≤ C * (volume A).toReal :=
      MeasureTheory.norm_setIntegral_le_of_norm_le_const hfin (fun z hz => by
        rw [Real.norm_eq_abs]
        exact hCb _ (Submission.BoseGases.update_mem_abox i hx (hAc hz)))
    have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
      by_cases h : x i ∈ A <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    rw [Work.UBBInputs8.boxPInd]
    calc |(1 / V) * (∫ z in A, Φ (Function.update x i z))
            * A.indicator (fun _ => (1 : ℝ)) (x i)|
        = (1 / V) * ‖∫ z in A, Φ (Function.update x i z)‖
            * |A.indicator (fun _ => (1 : ℝ)) (x i)| := by
          rw [abs_mul, abs_mul, abs_of_pos (one_div_pos.mpr hV), Real.norm_eq_abs]
      _ ≤ (1 / V) * (C * (volume A).toReal) * 1 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hInt (by positivity)) hind
            (abs_nonneg _) (mul_nonneg (by positivity) (mul_nonneg hC0 ENNReal.toReal_nonneg))
      _ = (1 / V) * C * (volume A).toReal := by ring

/-- The complementary projection is bounded whenever the projection is. -/
theorem exists_boxQInd_bound {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) (i : Fin N) :
    ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxQInd V A i Φ x| ≤ Cq := by
  obtain ⟨Cp, hCp0, hCpb⟩ := exists_boxPInd_bound hℓ hV hA hAc hΦc i
  obtain ⟨C, hC0, hCb⟩ := exists_abox_bound' hℓ hΦc
  refine ⟨C + Cp, add_nonneg hC0 hCp0, fun x hx => ?_⟩
  have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
    by_cases h : x i ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have h1 : |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ≤ C := by
    rw [abs_mul]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x| ≤ 1 * C :=
          mul_le_mul hind (hCb x hx) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  have h2 : Work.UBBInputs8.boxQInd V A i Φ x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x - Work.UBBInputs8.boxPInd V A i Φ x := rfl
  rw [h2]
  exact le_trans (abs_sub _ _) (add_le_add h1 (hCpb x hx))

/-! ## 3. Integrability on the box -/

/-- Bounded measurable times a bounded slot-fibre deviation is integrable on the box. -/
theorem integrableOn_slot_mul_delta {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {δ : E3 → ℝ} (hδmeas : Measurable δ) {D : ℝ} (hD : ∀ z, |δ z| ≤ D)
    {f : X N → ℝ} (hfm : Measurable f) {C : ℝ}
    (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ C) (i : Fin N) :
    IntegrableOn (fun x : X N => f x * δ (x i)) (abox N ℓ) volume :=
  Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hfm
    (hδmeas.comp (measurable_pi_apply i)) (Cf := C) (Cg := D) hfb
    (fun x _ => hD (x i))

/-! ## 4. The vanishing of the `P`-part (`∫ Pᵢ²·δ(xᵢ) = 0`) -/

/-- **The `P`-part of the fibre deviation integrates to zero.**  Peeling the slot `i`
(`Submission.BoseGases.abox_integral_peel`) exhibits the integrand as a product of a function of
the remaining coordinates `r` with `1_A(y)·δ(y)`, and the `y`-integral collapses to `∫_A δ = 0`
(`Work.BoseFixB1S.setIntegral_indicator_one_mul`).

This is the local copy of the delegated
`Work.BoseFixB1B.fibreDeviation_pPartZero` (whose module sits behind the currently
being-edited `Submission.Work.BoseFixB1S.flatArmSliding` in the import graph); it keeps the
verification cone of `fibreDeviation_le` inside stable corpus modules. -/
theorem fibreDeviation_pPartZero_local {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    {δ : E3 → ℝ} (hδmeas : Measurable δ) (hδsupp : ∀ z, z ∉ A → δ z = 0)
    (hδmean : ∫ z in A, δ z = 0) {D : ℝ} (hD : ∀ z, |δ z| ≤ D)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) (i : Fin N) :
    (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * δ (x i)) = 0 := by
  classical
  rcases N with _ | n
  · exact Fin.elim0 i
  obtain ⟨Cp, hCp0, hCpb⟩ := exists_boxPInd_bound hℓ hV hA hAc hΦc i
  have hint : IntegrableOn (fun x : X (n + 1) =>
      (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * δ (x i)) (abox (n + 1) ℓ) volume := by
    refine integrableOn_slot_mul_delta hℓ hδmeas hD
      ((Work.BoseFixB1S.measurable_boxPInd V A hA i hΦc.measurable).pow_const 2)
      (C := Cp ^ 2) ?_ i
    intro x hx
    rw [abs_of_nonneg (sq_nonneg (Work.UBBInputs8.boxPInd V A i Φ x)), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hCpb x hx) 2
  rw [Submission.BoseGases.abox_integral_peel (n := n) (ℓ := ℓ) i
    (F := fun x : X (n + 1) => (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * δ (x i)) hint]
  have hfib : ∀ r : X n, (∫ y in acube ℓ,
      (Work.UBBInputs8.boxPInd V A i Φ (Submission.BoseGases.kcInsN n i (y, r))) ^ 2
        * δ ((Submission.BoseGases.kcInsN n i (y, r)) i)) = 0 := by
    intro r
    have hpoint : ∀ y : E3,
        (Work.UBBInputs8.boxPInd V A i Φ (Submission.BoseGases.kcInsN n i (y, r))) ^ 2
          * δ ((Submission.BoseGases.kcInsN n i (y, r)) i)
        = (A.indicator (fun _ => (1 : ℝ)) y * δ y)
          * ((1 / V) * ∫ z in A, Φ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2 := by
      intro y
      rw [Work.BoseFixB1S.boxPInd_kcInsN, Submission.BoseGases.kc_insN_apply_same]
      by_cases hy : y ∈ A
      · simp only [Set.indicator_of_mem hy]
        ring
      · simp only [Set.indicator_of_notMem hy, hδsupp y hy]
        ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint),
      MeasureTheory.integral_mul_const]
    have hzero : (∫ y in acube ℓ, A.indicator (fun _ => (1 : ℝ)) y * δ y) = 0 := by
      rw [Work.BoseFixB1S.setIntegral_indicator_one_mul hA hAc δ]
      exact hδmean
    rw [hzero, zero_mul]
  simp only [hfib, MeasureTheory.integral_zero]

/-! ## 5. The finite Cauchy–Schwarz -/

/-- `Σᵢ (aᵢ + 2√aᵢ√bᵢ) ≤ Σaᵢ + 2√(Σaᵢ)√(Σbᵢ)` for nonnegative `a`, `b`. -/
theorem fibreDeviation_sum_sqrt_le {N : ℕ} (a b : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i) :
    ∑ i : Fin N, (a i + 2 * Real.sqrt (a i) * Real.sqrt (b i))
      ≤ (∑ i : Fin N, a i) + 2 * Real.sqrt (∑ i : Fin N, a i)
          * Real.sqrt (∑ i : Fin N, b i) := by
  have h := Real.sum_sqrt_mul_sqrt_le Finset.univ (f := a) (g := b) ha hb
  have h' : ∑ i : Fin N, Real.sqrt (a i) * Real.sqrt (b i)
      ≤ Real.sqrt (∑ i : Fin N, a i) * Real.sqrt (∑ i : Fin N, b i) := by
    simpa using h
  have h1 : ∑ i : Fin N, (a i + 2 * Real.sqrt (a i) * Real.sqrt (b i))
      = (∑ i : Fin N, a i) + 2 * ∑ i : Fin N, (Real.sqrt (a i) * Real.sqrt (b i)) := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h1]
  linarith

/-! ## 6. The assembly -/

/-- **The assembly.**  Given the two per-slot inputs — the vanishing of the `P`-part integral
(`hP`) and the `q`-part bound (`hQ`) — the summed fibre-deviation inequality follows. -/
theorem fibreDeviation_le_of_slots {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    {δ : E3 → ℝ} (hδmeas : Measurable δ) (hδsupp : ∀ z, z ∉ A → δ z = 0)
    {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ z, |δ z| ≤ D)
    {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (hP : ∀ i : Fin N, (∫ x in abox N ℓ,
            (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * δ (x i)) = 0)
    (hQ : ∀ i : Fin N, (∫ x in abox N ℓ,
            ((Work.UBBInputs8.boxQInd V A i Φ x)
              * (2 * Work.UBBInputs8.boxPInd V A i Φ x + Work.UBBInputs8.boxQInd V A i Φ x))
              * δ (x i))
          ≤ D * ((∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
                + 2 * Real.sqrt (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
                    * Real.sqrt (∫ x in abox N ℓ,
                        (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2))) :
    (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ i : Fin N, δ (x i)))
      ≤ D * (Work.UBBInputs8.cnPlusBoxInd ℓ A V Φ
              + 2 * Real.sqrt (Work.UBBInputs8.cnPlusBoxInd ℓ A V Φ)
                  * Real.sqrt (Work.BoseFixB1S.boxFlatCount V ℓ A Φ)) := by
  classical
  -- bounds of the three slot functions
  obtain ⟨Cb, hCb0, hCbb⟩ := exists_abox_bound' hℓ hΦc
  have hintPhi : ∀ i : Fin N,
      IntegrableOn (fun x : X N => (Φ x) ^ 2 * δ (x i)) (abox N ℓ) volume := by
    intro i
    refine integrableOn_slot_mul_delta hℓ hδmeas hD (hΦc.measurable.pow_const 2)
      (C := Cb ^ 2) ?_ i
    intro x hx
    rw [abs_of_nonneg (sq_nonneg (Φ x)), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg (Φ x)) (hCbb x hx) 2
  have hintP : ∀ i : Fin N, IntegrableOn (fun x : X N =>
      (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * δ (x i)) (abox N ℓ) volume := by
    intro i
    obtain ⟨Cp, hCp0, hCpb⟩ := exists_boxPInd_bound hℓ hV hA hAc hΦc i
    refine integrableOn_slot_mul_delta hℓ hδmeas hD
      ((Work.BoseFixB1S.measurable_boxPInd V A hA i hΦc.measurable).pow_const 2)
      (C := Cp ^ 2) ?_ i
    intro x hx
    rw [abs_of_nonneg (sq_nonneg (Work.UBBInputs8.boxPInd V A i Φ x)),
      ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hCpb x hx) 2
  have hintQ : ∀ i : Fin N, IntegrableOn (fun x : X N =>
      ((Work.UBBInputs8.boxQInd V A i Φ x)
        * (2 * Work.UBBInputs8.boxPInd V A i Φ x + Work.UBBInputs8.boxQInd V A i Φ x))
        * δ (x i)) (abox N ℓ) volume := by
    intro i
    obtain ⟨Cp, hCp0, hCpb⟩ := exists_boxPInd_bound hℓ hV hA hAc hΦc i
    obtain ⟨Cq, hCq0, hCqb⟩ := exists_boxQInd_bound hℓ hV hA hAc hΦc i
    have hQm : Measurable (Work.UBBInputs8.boxQInd V A i Φ) := by
      have h1 : Measurable (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) :=
        ((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul hΦc.measurable
      exact h1.sub (Work.BoseFixB1S.measurable_boxPInd V A hA i hΦc.measurable)
    have hPm : Measurable (Work.UBBInputs8.boxPInd V A i Φ) :=
      Work.BoseFixB1S.measurable_boxPInd V A hA i hΦc.measurable
    refine integrableOn_slot_mul_delta hℓ hδmeas hD
      (hQm.mul ((hPm.const_mul 2).add hQm)) (C := Cq * (2 * Cp + Cq)) ?_ i
    intro x hx
    show |Work.UBBInputs8.boxQInd V A i Φ x
        * (2 * Work.UBBInputs8.boxPInd V A i Φ x + Work.UBBInputs8.boxQInd V A i Φ x)|
      ≤ Cq * (2 * Cp + Cq)
    rw [abs_mul]
    refine mul_le_mul (hCqb x hx) ?_ (abs_nonneg _) hCq0
    calc |2 * Work.UBBInputs8.boxPInd V A i Φ x + Work.UBBInputs8.boxQInd V A i Φ x|
        ≤ |2 * Work.UBBInputs8.boxPInd V A i Φ x| + |Work.UBBInputs8.boxQInd V A i Φ x| :=
          abs_add_le _ _
      _ = 2 * |Work.UBBInputs8.boxPInd V A i Φ x| + |Work.UBBInputs8.boxQInd V A i Φ x| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      _ ≤ 2 * Cp + Cq := add_le_add (mul_le_mul_of_nonneg_left (hCpb x hx) (by norm_num))
          (hCqb x hx)
  -- step 1: the sum/integral interchange
  have hsum : (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ i : Fin N, δ (x i)))
      = ∑ i : Fin N, ∫ x in abox N ℓ, (Φ x) ^ 2 * δ (x i) := by
    rw [← MeasureTheory.integral_finsetSum Finset.univ
      (f := fun i : Fin N => fun x : X N => (Φ x) ^ 2 * δ (x i))]
    · apply integral_congr_ae
      filter_upwards with x
      rw [Finset.mul_sum]
    · intro i _
      exact hintPhi i
  rw [hsum]
  -- step 2: slotwise the identity `Φ²δ = P²δ + Q(2P+Q)δ`
  have hsplit : ∀ i : Fin N, (∫ x in abox N ℓ, (Φ x) ^ 2 * δ (x i))
      = (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * δ (x i))
        + ∫ x in abox N ℓ,
            ((Work.UBBInputs8.boxQInd V A i Φ x)
              * (2 * Work.UBBInputs8.boxPInd V A i Φ x + Work.UBBInputs8.boxQInd V A i Φ x))
              * δ (x i) := by
    intro i
    rw [← MeasureTheory.integral_add (hintP i) (hintQ i)]
    apply integral_congr_ae
    filter_upwards with x
    exact fibreDeviation_pointwise V hδsupp i Φ x
  -- final arithmetic
  have ha : ∀ i : Fin N, 0 ≤ ∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 :=
    fun i => MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  have hb : ∀ i : Fin N, 0 ≤ ∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 :=
    fun i => MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  have hcs := fibreDeviation_sum_sqrt_le
    (fun i : Fin N => ∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
    (fun i : Fin N => ∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2) ha hb
  have hident1 : (∑ i : Fin N, ∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
      = Work.UBBInputs8.cnPlusBoxInd ℓ A V Φ := rfl
  have hident2 : (∑ i : Fin N, ∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)
      = Work.BoseFixB1S.boxFlatCount V ℓ A Φ := rfl
  calc ∑ i : Fin N, ∫ x in abox N ℓ, (Φ x) ^ 2 * δ (x i)
      = ∑ i : Fin N, ((∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2 * δ (x i))
          + ∫ x in abox N ℓ,
              ((Work.UBBInputs8.boxQInd V A i Φ x)
                * (2 * Work.UBBInputs8.boxPInd V A i Φ x + Work.UBBInputs8.boxQInd V A i Φ x))
                * δ (x i)) :=
        Finset.sum_congr rfl (fun i _ => hsplit i)
    _ = ∑ i : Fin N, ((0 : ℝ) + ∫ x in abox N ℓ,
              ((Work.UBBInputs8.boxQInd V A i Φ x)
                * (2 * Work.UBBInputs8.boxPInd V A i Φ x + Work.UBBInputs8.boxQInd V A i Φ x))
                * δ (x i)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hP i]
    _ ≤ ∑ i : Fin N, D * ((∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
              + 2 * Real.sqrt (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
                  * Real.sqrt (∫ x in abox N ℓ,
                      (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        simpa using hQ i
    _ = D * ∑ i : Fin N, ((∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
              + 2 * Real.sqrt (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
                  * Real.sqrt (∫ x in abox N ℓ,
                      (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)) := by
        rw [Finset.mul_sum]
    _ ≤ D * (Work.UBBInputs8.cnPlusBoxInd ℓ A V Φ
              + 2 * Real.sqrt (Work.UBBInputs8.cnPlusBoxInd ℓ A V Φ)
                  * Real.sqrt (Work.BoseFixB1S.boxFlatCount V ℓ A Φ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hD0
        rw [hident1, hident2] at hcs
        simpa using hcs

end Work.BoseFixB1B
