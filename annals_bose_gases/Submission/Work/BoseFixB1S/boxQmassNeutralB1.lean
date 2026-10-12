import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxQfibPeelB1
import Submission.Work.BoseFixB1S.boxQsharpSpecB1
import Submission.Work.BoseFixB1S.n0PairPairingB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-- The box indicator is bounded by `1`. -/
private lemma abs_boxInd_le_one {A : Set E3} (t : E3) : |A.indicator (fun _ => (1 : ℝ)) t| ≤ 1 := by
  by_cases ht : t ∈ A
  · rw [Set.indicator_of_mem ht]; norm_num
  · rw [Set.indicator_of_notMem ht]; norm_num

/-- Linearity of the box integral in the explicit-application form. -/
private lemma integral_add_lambda {N : ℕ} {ℓ : ℝ} {f g : X N → ℝ}
    (hf : IntegrableOn f (abox N ℓ) volume) (hg : IntegrableOn g (abox N ℓ) volume) :
    (∫ x in abox N ℓ, f x + g x) = (∫ x in abox N ℓ, f x) + (∫ x in abox N ℓ, g x) :=
  MeasureTheory.integral_add hf hg

/-- **Per-slot count identity.**  For each slot `i` the box projections split the box-supported
square: `∫(P_iΦ)² + ∫(Q_iΦ)² = ∫ 1_A(xᵢ)·Φ²`. -/
theorem flatAddQSlotNeutralB1 {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) (i : Fin N) :
    (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)
        + (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
      = ∫ x in abox N ℓ, A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 := by
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC _ (zero_mem_abox hℓ.le))
  have hbΦ : ∀ x ∈ abox N ℓ, |Φ x| ≤ C := fun x hx => by
    simpa [Real.norm_eq_abs] using hC x hx
  have hbP : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd V A i Φ x| ≤ C :=
    abs_boxPInd_le (N := N) (A := A) hℓ hV hA hVeq hAc i hbΦ
  have hbXi : ∀ x ∈ abox N ℓ, |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ≤ C := by
    intro x hx
    calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x|
        = |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x| := abs_mul _ _
      _ ≤ 1 * C := mul_le_mul (abs_boxInd_le_one (x i)) (hbΦ x hx) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  have hbQ : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxQInd V A i Φ x| ≤ 2 * C := by
    intro x hx
    have h2 : Work.UBBInputs8.boxQInd V A i Φ x
        = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
          - Work.UBBInputs8.boxPInd V A i Φ x := rfl
    rw [h2]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
            - Work.UBBInputs8.boxPInd V A i Φ x|
        ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x|
            + |Work.UBBInputs8.boxPInd V A i Φ x| := abs_sub _ _
      _ ≤ C + C := add_le_add (hbXi x hx) (hbP x hx)
      _ = 2 * C := by ring
  have hmΦ : Measurable Φ := hΦc.measurable
  have him : Measurable (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) :=
    (((measurable_const.indicator hA).comp (measurable_pi_apply i))).mul hmΦ
  have hmP : Measurable (Work.UBBInputs8.boxPInd V A i Φ) :=
    measurable_boxPInd V A hA i hmΦ
  have hmQ : Measurable (Work.UBBInputs8.boxQInd V A i Φ) := by
    have h2 : Work.UBBInputs8.boxQInd V A i Φ
        = fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
            - Work.UBBInputs8.boxPInd V A i Φ x := rfl
    rw [h2]
    exact him.sub hmP
  have hIP : IntegrableOn (fun x : X N => (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)
      (abox N ℓ) volume := integrableOn_sq_of_bound (N := N) hℓ hmP hbP
  have hIQ : IntegrableOn (fun x : X N => (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
      (abox N ℓ) volume := integrableOn_sq_of_bound (N := N) hℓ hmQ hbQ
  have hIX : IntegrableOn
      (fun x : X N => (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2) (abox N ℓ) volume :=
    integrableOn_sq_of_bound (N := N) hℓ him hbXi
  have hIPQ : IntegrableOn
      (fun x : X N => Work.UBBInputs8.boxPInd V A i Φ x * Work.UBBInputs8.boxQInd V A i Φ x)
      (abox N ℓ) volume := integrableOn_mul_of_bound (N := N) hℓ hmP hmQ hbP hbQ
  have hPG : IntegrableOn
      (fun x : X N => (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2
        + 2 * (Work.UBBInputs8.boxPInd V A i Φ x * Work.UBBInputs8.boxQInd V A i Φ x))
      (abox N ℓ) volume := hIP.add (hIPQ.const_mul 2)
  have horth : (∫ x in abox N ℓ,
      Work.UBBInputs8.boxPInd V A i Φ x * Work.UBBInputs8.boxQInd V A i Φ x) = 0 := by
    simpa only [Work.UBBInputs8.boxQInd] using
      (Work.BoseSplit.pIndOrth (N := N) (ℓ := ℓ) (volA := V) hℓ hV hA hVeq hAc i hΦc)
  have hpt : ∀ x : X N,
      (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2
        = (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2
          + 2 * (Work.UBBInputs8.boxPInd V A i Φ x * Work.UBBInputs8.boxQInd V A i Φ x)
          + (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 := by
    intro x
    have hsum : Work.UBBInputs8.boxPInd V A i Φ x + Work.UBBInputs8.boxQInd V A i Φ x
        = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x := by
      simp only [Work.UBBInputs8.boxQInd]
      ring
    rw [← hsum]
    ring
  have hpt2 : ∀ x : X N, (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2
      = A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 := by
    intro x
    by_cases hxi : x i ∈ A
    · rw [Set.indicator_of_mem hxi]; ring
    · rw [Set.indicator_of_notMem hxi]; ring
  have hX' : (∫ x in abox N ℓ, (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2)
      = ∫ x in abox N ℓ, (A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2) :=
    integral_congr_ae (Filter.Eventually.of_forall hpt2)
  have hmain : (∫ x in abox N ℓ, (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2)
      = (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)
          + (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) := by
    calc (∫ x in abox N ℓ, (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2)
        = ∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2
            + 2 * (Work.UBBInputs8.boxPInd V A i Φ x * Work.UBBInputs8.boxQInd V A i Φ x)
            + (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = (∫ x in abox N ℓ, ((Work.UBBInputs8.boxPInd V A i Φ x) ^ 2
              + 2 * (Work.UBBInputs8.boxPInd V A i Φ x * Work.UBBInputs8.boxQInd V A i Φ x)))
            + (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) :=
          integral_add_lambda hPG hIQ
      _ = ((∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)
              + 2 * (∫ x in abox N ℓ,
                  Work.UBBInputs8.boxPInd V A i Φ x * Work.UBBInputs8.boxQInd V A i Φ x))
            + (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) := by
          rw [integral_add_lambda hIP (hIPQ.const_mul 2), MeasureTheory.integral_const_mul]
      _ = (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)
            + (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2) := by
          rw [horth]; ring
  exact hmain.symm.trans hX'

/-- **FS's `n₀ + n₊ = n` identity, in expectation** (summed form of `flatAddQSlotNeutralB1`). -/
theorem flatCountIdentityNeutralB1 {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    Work.BoseFixB1S.boxFlatCount V ℓ A Φ + Work.BoseFixB1S.boxQCount V ℓ A Φ
      = ∫ x in abox N ℓ,
          (∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i)) * (Φ x) ^ 2 := by
  have hslot : ∀ i : Fin N,
      (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)
          + (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
        = ∫ x in abox N ℓ, A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 :=
    fun i => flatAddQSlotNeutralB1 (N := N) (ℓ := ℓ) (V := V) hℓ hV hA hVeq hAc hΦc i
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  have hbΦ : ∀ x ∈ abox N ℓ, |Φ x| ≤ C := fun x hx => by
    simpa [Real.norm_eq_abs] using hC x hx
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC _ (zero_mem_abox hℓ.le))
  have hmΦ : Measurable Φ := hΦc.measurable
  have hInt : ∀ i : Fin N, IntegrableOn
      (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2) (abox N ℓ) volume := by
    intro i
    have him : Measurable (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2) :=
      (((measurable_const.indicator hA).comp (measurable_pi_apply i))).mul (hmΦ.pow_const 2)
    have hb : ∀ x ∈ abox N ℓ, |A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2| ≤ C ^ 2 := by
      intro x hx
      calc |A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2|
          = |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x| ^ 2 := by
            rw [abs_mul, abs_pow]
        _ ≤ 1 * C ^ 2 := by
            refine mul_le_mul (abs_boxInd_le_one (x i)) ?_ (pow_nonneg (abs_nonneg _) 2)
              zero_le_one
            exact pow_le_pow_left₀ (abs_nonneg _) (hbΦ x hx) 2
        _ = C ^ 2 := one_mul _
    exact IntegrableOn.of_bound (abox_lt_top N ℓ hℓ.le) him.aestronglyMeasurable (|C ^ 2|) (by
      rw [ae_restrict_iff' (abox_measurable N ℓ)]
      refine ae_of_all _ (fun x hx => ?_)
      rw [Real.norm_eq_abs]
      exact le_trans (hb x hx) (le_abs_self _))
  have hsum1 : (∑ i : Fin N, ((∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)
        + (∫ x in abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)))
      = ∑ i : Fin N, ∫ x in abox N ℓ,
          A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 :=
    Finset.sum_congr rfl fun i _ => hslot i
  rw [Work.BoseFixB1S.boxFlatCount, Work.BoseFixB1S.boxQCount, ← Finset.sum_add_distrib, hsum1,
    ← MeasureTheory.integral_finset_sum Finset.univ (fun i _ => hInt i)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
      = (∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i)) * (Φ x) ^ 2
  rw [Finset.sum_mul]

/-- **The count identity** `n₀ + n₊ = N` at a normalised state supported in the `A`-occupancy
sector. -/
theorem countIdentityNeutralB1 {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1)
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (abox N ℓ)),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A) :
    Work.BoseFixB1S.boxFlatCount V ℓ A Φ + Work.BoseFixB1S.boxQCount V ℓ A Φ = (N : ℝ) := by
  have h1 := flatCountIdentityNeutralB1 (N := N) (ℓ := ℓ) (V := V) hℓ hV hA hVeq hAc hΦc
  rw [h1]
  have h2 : (∫ x in abox N ℓ,
        (∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i)) * (Φ x) ^ 2)
      = ∫ x in abox N ℓ, (N : ℝ) * (Φ x) ^ 2 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hsupp] with x hx
    by_cases h : Φ x = 0
    · simp [h]
    · have hi : ∀ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i) = 1 :=
        fun i => Set.indicator_of_mem (hx h i) _
      have hsum : (∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i)) = (N : ℝ) := by
        rw [Finset.sum_congr rfl (fun i _ => hi i)]
        simp
      rw [hsum]
  rw [h2, MeasureTheory.integral_const_mul, hnorm]
  ring

/-- **The `QP`-cross mass against `n₀·n₊`.** -/
theorem boxQPairMassNeutralB1 {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1)
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (abox N ℓ)),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A)
    (hcS2 : Work.BoseFixB1S.boxFlatCount V ℓ A Φ ^ 2 - Work.BoseFixB1S.boxFlatCount V ℓ A Φ
      ≤ Work.BoseFixB1S.boxPairCount V ℓ A Φ) :
    (∑ i : Fin N, ∑ j : Fin N, ∫ x in abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) * (Work.UBBInputs8.boxPInd V A j Φ x))
      ≤ Work.BoseFixB1S.boxFlatCount V ℓ A Φ * Work.BoseFixB1S.boxQCount V ℓ A Φ := by
  have hpair := n0PairPairingB1 (N := N) (ℓ := ℓ) (volA := V) hℓ hV hA hVeq hAc hΦc hsupp
  have hcount := countIdentityNeutralB1 (N := N) (ℓ := ℓ) (V := V) hℓ hV hA hVeq hAc hΦc
    hnorm hsupp
  rw [hpair]
  have hN : (N : ℝ) = Work.BoseFixB1S.boxFlatCount V ℓ A Φ
      + Work.BoseFixB1S.boxQCount V ℓ A Φ := hcount.symm
  rw [hN]
  nlinarith [hcS2]

/-- **The sharp `q`-side fibre mass.**  See the module docstring. -/
theorem boxQmassNeutralB1 {N : ℕ} {ℓ V c : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) (hc : 0 ≤ c)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ} (hfm : Measurable fib) (hfib0 : ∀ z, 0 ≤ fib z)
    {Cf : ℝ} (hfible : ∀ z ∈ A, fib z ≤ Cf)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) = 1)
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A)
    (hcS2 : Work.BoseFixB1S.boxFlatCount V ℓ A Φ ^ 2 - Work.BoseFixB1S.boxFlatCount V ℓ A Φ
      ≤ Work.BoseFixB1S.boxPairCount V ℓ A Φ) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        fib (x i) * (Work.BoseFixB1S.n0FunOp V A
          (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
          (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2)
      ≤ 2 * Cf * (Work.BoseFixB1S.boxFlatCount V ℓ A Φ * Work.BoseFixB1S.boxQCount V ℓ A Φ
          + (1 + c) * Work.BoseFixB1S.boxQCount V ℓ A Φ) := by
  have hAne : A.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hVeq
    simp at hVeq
    linarith
  obtain ⟨z, hz⟩ := hAne
  have hCf0 : 0 ≤ Cf := le_trans (hfib0 z) (hfible z hz)
  have hpeel := boxQfibPeelB1 (N := N) (ℓ := ℓ) (V := V)
    (g := fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
    hℓ hV hA hVeq hAc hfm hfib0 hfible hΦc
  have hsharp := boxQsharpSpecB1 (N := N) (ℓ := ℓ) (V := V) (c := c) hℓ hV hc hA hVeq hAc hΦc
  have hpair := boxQPairMassNeutralB1 (N := N) (ℓ := ℓ) (V := V)
    hℓ hV hA hVeq hAc hΦc hnorm hsupp hcS2
  have h1 : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        fib (x i) * (Work.BoseFixB1S.n0FunOp V A
          (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
          (Work.UBBInputs8.boxQInd V A i Φ)) x ^ 2)
      ≤ Cf * (2 * ((∑ i : Fin N, ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) * (Work.UBBInputs8.boxPInd V A j Φ x))
          + (1 + c) * Work.BoseFixB1S.boxQCount V ℓ A Φ)) :=
    le_trans hpeel (mul_le_mul_of_nonneg_left hsharp hCf0)
  have h2 : (∑ i : Fin N, ∑ j : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) * (Work.UBBInputs8.boxPInd V A j Φ x))
      ≤ Work.BoseFixB1S.boxFlatCount V ℓ A Φ * Work.BoseFixB1S.boxQCount V ℓ A Φ := hpair
  nlinarith [h1, h2, hCf0]

end Work.BoseFixB1S
