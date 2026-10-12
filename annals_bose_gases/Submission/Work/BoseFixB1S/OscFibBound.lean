import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxOneValue
import Submission.Work.BoseFixB1S.boxPQw_mass_le
import Submission.Work.BoseFixB1S.n0SlotDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.OscFibBound`

The fibre-oscillation bound for the FS box projection `P_{B,i}`:

    ∫_{abox N ℓ} (P_{B,i}(g(·ᵢ)Ψ))² ≤ Cosc² · ∫_{abox N ℓ} (1_A(xᵢ)·Ψ)²     whenever
    ∫_A g² ≤ Cosc²·|A| .

This is the estimate in which a sup-norm bound on the fibre is replaced by its `L²(A)` bound
(the covariance Cauchy–Schwarz of the oscillation form of `commutatorPairingB1`).

The proof peels the slot `i` out of both sides (`boxPInd_peel` / `AindMulSqPeelOsc`) and uses the
fibre-wise Cauchy–Schwarz `(∫_A g·Ψ)² ≤ (∫_A g²)(∫_AΨ²)` with the `L²`-version
`integral_mul_sq_le_memLp`.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 0. Cauchy–Schwarz with `L²` hypotheses -/

theorem integral_mul_sq_le_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f g : α → ℝ} (hfm : MemLp f (ENNReal.ofReal 2) μ) (hgm : MemLp g (ENNReal.ofReal 2) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, (f x) ^ 2 ∂μ) * (∫ x, (g x) ^ 2 ∂μ) := by
  have h1 : MemLp (fun x => |f x|) (ENNReal.ofReal 2) μ := hfm.norm
  have h2 : MemLp (fun x => |g x|) (ENNReal.ofReal 2) μ := hgm.norm
  have hmain := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) (μ := μ)
    Real.HolderConjugate.two_two (ae_of_all _ (fun _ => abs_nonneg _))
    (ae_of_all _ (fun _ => abs_nonneg _)) h1 h2
  have hsq1 : (fun x => |f x| ^ (2 : ℝ)) = fun x => (f x) ^ 2 := by
    funext x
    rw [Real.rpow_two, sq_abs]
  have hsq2 : (fun x => |g x| ^ (2 : ℝ)) = fun x => (g x) ^ 2 := by
    funext x
    rw [Real.rpow_two, sq_abs]
  rw [hsq1, hsq2] at hmain
  have hnonf : 0 ≤ ∫ x, (f x) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hnong : 0 ≤ ∫ x, (g x) ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have habs : |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x| * |g x| ∂μ := by
    calc |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x * g x| ∂μ := abs_integral_le_integral_abs
      _ = ∫ x, |f x| * |g x| ∂μ := by
          apply integral_congr_ae
          filter_upwards with x
          rw [abs_mul]
  have hsqrtf : ((∫ x, (f x) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 = ∫ x, (f x) ^ 2 ∂μ := by
    rw [← Real.rpow_two, ← Real.rpow_mul hnonf,
      show (1 / 2 : ℝ) * 2 = 1 by norm_num, Real.rpow_one]
  have hsqrtg : ((∫ x, (g x) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 = ∫ x, (g x) ^ 2 ∂μ := by
    rw [← Real.rpow_two, ← Real.rpow_mul hnong,
      show (1 / 2 : ℝ) * 2 = 1 by norm_num, Real.rpow_one]
  have hX2 : (∫ x, |f x| * |g x| ∂μ) ^ 2
      ≤ (∫ x, (f x) ^ 2 ∂μ) * (∫ x, (g x) ^ 2 ∂μ) := by
    have h0 : 0 ≤ ∫ x, |f x| * |g x| ∂μ :=
      integral_nonneg (fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hs := pow_le_pow_left₀ h0 hmain 2
    rw [mul_pow, hsqrtf, hsqrtg] at hs
    exact hs
  have hle := abs_le.mp habs
  calc (∫ x, f x * g x ∂μ) ^ 2
      ≤ (∫ x, |f x| * |g x| ∂μ) ^ 2 := sq_le_sq' hle.1 hle.2
    _ ≤ (∫ x, (f x) ^ 2 ∂μ) * (∫ x, (g x) ^ 2 ∂μ) := hX2

/-! ## 1. The peel of the `A`-indicator slot square -/

theorem acube_integral_AindMulSq {n : ℕ} {ℓ : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) (i : Fin (n + 1)) (Ψ : X (n + 1) → ℝ) (r : X n) :
    (∫ y : E3 in acube ℓ, (Aind A ((kcInsN n i (y, r)) i) * Ψ (kcInsN n i (y, r))) ^ 2)
      = ∫ t in A, Ψ (kcInsN n i (t, r)) ^ 2 := by
  have hstep : (∫ y : E3 in acube ℓ,
        (Aind A ((kcInsN n i (y, r)) i) * Ψ (kcInsN n i (y, r))) ^ 2)
      = ∫ y : E3 in acube ℓ,
          A.indicator (fun _ => (1 : ℝ)) y * (Ψ (kcInsN n i (y, r)) ^ 2) := by
    apply setIntegral_congr_fun (acube_measurable ℓ)
    intro y hy
    show (Aind A ((kcInsN n i (y, r)) i) * Ψ (kcInsN n i (y, r))) ^ 2
      = A.indicator (fun _ => (1 : ℝ)) y * (Ψ (kcInsN n i (y, r)) ^ 2)
    rw [kc_insN_apply_same]
    show (Aind A y * Ψ (kcInsN n i (y, r))) ^ 2
      = A.indicator (fun _ => (1 : ℝ)) y * (Ψ (kcInsN n i (y, r)) ^ 2)
    calc (Aind A y * Ψ (kcInsN n i (y, r))) ^ 2
        = (A.indicator (fun _ => (1 : ℝ)) y * A.indicator (fun _ => (1 : ℝ)) y)
          * (Ψ (kcInsN n i (y, r)) ^ 2) := by
            rw [show Aind A y = A.indicator (fun _ => (1 : ℝ)) y from rfl]; ring
      _ = A.indicator (fun _ => (1 : ℝ)) y * (Ψ (kcInsN n i (y, r)) ^ 2) := by
          rw [show A.indicator (fun _ => (1 : ℝ)) y * A.indicator (fun _ => (1 : ℝ)) y
              = A.indicator (fun _ => (1 : ℝ)) y from Aind_mul_self A y]
  rw [hstep, setIntegral_indicator_one_mul hA hAc]

theorem AindMulSqPeelOsc {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {A : Set E3} (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ) (i : Fin (n + 1))
    {Ψ : X (n + 1) → ℝ} (hΨ : GoodState ℓ Ψ) :
    (∫ x in abox (n + 1) ℓ, (Aind A (x i) * Ψ x) ^ 2)
      = ∫ r in abox n ℓ, ∫ t in A, Ψ (kcInsN n i (t, r)) ^ 2 := by
  obtain ⟨hΨm, C, hΨb⟩ := hΨ
  have hmeas : Measurable (fun x : X (n + 1) => Aind A (x i) * Ψ x) :=
    (measurable_sigAt A hA i).mul hΨm
  have hbound : ∀ x ∈ abox (n + 1) ℓ, |Aind A (x i) * Ψ x| ≤ max C 0 := by
    intro x hx
    rw [abs_mul]
    calc |Aind A (x i)| * |Ψ x| ≤ 1 * max C 0 :=
          mul_le_mul (Aind_abs_le_one A (x i))
            (le_trans (hΨb x hx) (le_max_left _ _)) (abs_nonneg _) zero_le_one
      _ = max C 0 := one_mul _
  have hF : IntegrableOn (fun x : X (n + 1) => (Aind A (x i) * Ψ x) ^ 2)
      (abox (n + 1) ℓ) volume :=
    integrableOn_sq_of_bound hℓ hmeas hbound
  rw [Submission.BoseGases.abox_integral_peel_gen (i := i)
    (F := fun x : X (n + 1) => (Aind A (x i) * Ψ x) ^ 2) hF]
  apply integral_congr_ae
  filter_upwards with r
  exact acube_integral_AindMulSq hA hAc i Ψ r

/-! ## 2. The `oneRest` Cauchy–Schwarz bound -/

theorem oneRestSqIntegralLeOsc {n : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {g : E3 → ℝ} (hgm : Measurable g)
    (hgint : IntegrableOn (fun z => g z ^ 2) A)
    {Cosc : ℝ} (hCosc : ∫ z in A, g z ^ 2 ≤ Cosc ^ 2 * volA)
    {Ψ : X (n + 1) → ℝ} (hΨ : GoodState ℓ Ψ) (i : Fin (n + 1)) :
    (∫ r in abox n ℓ, (Q0C.oneRest volA A i (fun y => g (y i) * Ψ y) r) ^ 2)
      ≤ (Cosc ^ 2 / volA) * ∫ r in abox n ℓ, ∫ t in A, Ψ (kcInsN n i (t, r)) ^ 2 := by
  obtain ⟨hΨm, C, hΨb⟩ := hΨ
  have hAfin : (volume : Measure E3) A < ⊤ := volume_A_lt_top hℓ hAc
  haveI hfinA : IsFiniteMeasure ((volume : Measure E3).restrict A) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hAfin)
  haveI hfinAb : IsFiniteMeasure ((volume : Measure (X n)).restrict (abox n ℓ)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt (abox_lt_top n ℓ hℓ.le))
  -- the pointwise (in `r`) Cauchy–Schwarz bound
  have hCS : ∀ r ∈ abox n ℓ,
      (Q0C.oneRest volA A i (fun y => g (y i) * Ψ y) r) ^ 2
        ≤ (1 / volA ^ 2) * (∫ z in A, g z ^ 2)
            * (∫ t in A, Ψ (kcInsN n i (t, r)) ^ 2) := by
    intro r hr
    rw [Q0C.oneRest_def]
    have hsub : (∫ u in A, g ((kcInsN n i (u, r)) i) * Ψ (kcInsN n i (u, r)))
        = ∫ u in A, g u * Ψ (kcInsN n i (u, r)) := by
      apply setIntegral_congr_fun hA
      intro u hu
      show g ((kcInsN n i (u, r)) i) * Ψ (kcInsN n i (u, r)) = g u * Ψ (kcInsN n i (u, r))
      rw [kc_insN_apply_same]
    rw [hsub]
    have hgm' : AEStronglyMeasurable (fun u : E3 => g u)
        ((volume : Measure E3).restrict A) := hgm.aestronglyMeasurable
    have hΨm' : AEStronglyMeasurable (fun t : E3 => Ψ (kcInsN n i (t, r)))
        ((volume : Measure E3).restrict A) :=
      (hΨm.comp ((kcInsN n i).measurable.comp
        (by fun_prop : Measurable fun t : E3 => (t, r)))).aestronglyMeasurable
    have hmf : MemLp (fun u : E3 => g u) (ENNReal.ofReal 2)
        ((volume : Measure E3).restrict A) := by
      have h := (memLp_two_iff_integrable_sq hgm').mpr hgint
      simpa only [← show ENNReal.ofReal (2 : ℝ) = 2 from by norm_num] using h
    have hmg : MemLp (fun t : E3 => Ψ (kcInsN n i (t, r))) (ENNReal.ofReal 2)
        ((volume : Measure E3).restrict A) :=
      MemLp.of_bound hΨm' (max C 0) (by
        rw [ae_restrict_iff' hA]
        refine ae_of_all _ (fun t ht => ?_)
        rw [Real.norm_eq_abs]
        calc |Ψ (kcInsN n i (t, r))| ≤ C := hΨb _ (kcInsN_mem_abox hAc i ht hr)
          _ ≤ max C 0 := le_max_left _ _)
    have hcs := integral_mul_sq_le_memLp hmf hmg
    have hcs' : (∫ u in A, g u * Ψ (kcInsN n i (u, r))) ^ 2
        ≤ (∫ z in A, g z ^ 2) * (∫ t in A, Ψ (kcInsN n i (t, r)) ^ 2) := hcs
    calc (1 / volA * ∫ u in A, g u * Ψ (kcInsN n i (u, r))) ^ 2
        = (1 / volA) ^ 2 * (∫ u in A, g u * Ψ (kcInsN n i (u, r))) ^ 2 := by ring
      _ ≤ (1 / volA) ^ 2
            * ((∫ z in A, g z ^ 2) * (∫ t in A, Ψ (kcInsN n i (t, r)) ^ 2)) :=
          mul_le_mul_of_nonneg_left hcs' (sq_nonneg _)
      _ = (1 / volA ^ 2) * (∫ z in A, g z ^ 2)
            * (∫ t in A, Ψ (kcInsN n i (t, r)) ^ 2) := by ring
  -- the dominating function is integrable
  have hbase_int : Integrable (fun r : X n => ∫ t in A, Ψ (kcInsN n i (t, r)) ^ 2)
      ((volume : Measure (X n)).restrict (abox n ℓ)) := by
    have hFsq : IntegrableOn (fun x : X (n + 1) => (Aind A (x i) * Ψ x) ^ 2)
        (abox (n + 1) ℓ) volume :=
      integrableOn_sq_of_bound hℓ ((measurable_sigAt A hA i).mul hΨm) (by
        intro x hx
        rw [abs_mul]
        calc |Aind A (x i)| * |Ψ x| ≤ 1 * max C 0 :=
              mul_le_mul (Aind_abs_le_one A (x i))
                (le_trans (hΨb x hx) (le_max_left _ _)) (abs_nonneg _) zero_le_one
          _ = max C 0 := one_mul _)
    have hpeel := Submission.BoseGases.abox_peel_inner_integrable_gen (n := n) (ℓ := ℓ) i
      (fun x : X (n + 1) => (Aind A (x i) * Ψ x) ^ 2) hFsq
    refine Integrable.congr hpeel (Filter.Eventually.of_forall (fun r => ?_))
    exact acube_integral_AindMulSq hA hAc i Ψ r
  have hdom_int : Integrable (fun r : X n => (1 / volA ^ 2) * (∫ z in A, g z ^ 2)
      * (∫ t in A, Ψ (kcInsN n i (t, r)) ^ 2))
      ((volume : Measure (X n)).restrict (abox n ℓ)) :=
    hbase_int.const_mul _
  have hf_int : Integrable
      (fun r : X n => (Q0C.oneRest volA A i (fun y => g (y i) * Ψ y) r) ^ 2)
      ((volume : Measure (X n)).restrict (abox n ℓ)) := by
    refine Integrable.mono' hdom_int ?_ ?_
    · have h1 : AEStronglyMeasurable
          (fun r : X n => Q0C.oneRest volA A i (fun y => g (y i) * Ψ y) r)
          ((volume : Measure (X n)).restrict (abox n ℓ)) := by
        simpa only [Q0C.oneRest_def, Function.comp_apply, Pi.mul_apply] using
          (Q0C.aem_oneRest (ℓ := ℓ) volA A i
            ((hgm.comp (measurable_pi_apply i)).mul hΨm)).const_mul (1 / volA)
      exact h1.pow 2
    · filter_upwards [self_mem_ae_restrict (abox_measurable n ℓ)] with r hr
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hCS r hr
  have hmono := setIntegral_mono_ae_restrict hf_int hdom_int (by
    filter_upwards [self_mem_ae_restrict (abox_measurable n ℓ)] with r hr
    exact hCS r hr)
  -- evaluate the dominating integral
  have hval : (∫ r in abox n ℓ, (1 / volA ^ 2) * (∫ z in A, g z ^ 2)
        * (∫ t in A, Ψ (kcInsN n i (t, r)) ^ 2))
      = (1 / volA ^ 2) * (∫ z in A, g z ^ 2)
        * (∫ r in abox n ℓ, ∫ t in A, Ψ (kcInsN n i (t, r)) ^ 2) := by
    rw [integral_const_mul]
  rw [hval] at hmono
  refine le_trans hmono ?_
  have hbound : (1 / volA ^ 2) * (∫ z in A, g z ^ 2) ≤ Cosc ^ 2 / volA := by
    have h1 : (1 / volA ^ 2) * (∫ z in A, g z ^ 2) ≤ (1 / volA ^ 2) * (Cosc ^ 2 * volA) :=
      mul_le_mul_of_nonneg_left hCosc (by positivity)
    have h2 : (1 / volA ^ 2) * (Cosc ^ 2 * volA) = Cosc ^ 2 / volA := by
      field_simp
      try ring
    linarith [h1, h2]
  have hbase0 : 0 ≤ ∫ r in abox n ℓ, ∫ t in A, Ψ (kcInsN n i (t, r)) ^ 2 :=
    integral_nonneg (fun r => integral_nonneg (fun t => sq_nonneg _))
  exact mul_le_mul_of_nonneg_right hbound hbase0

/-! ## 3. The oscillation bound for the box projection -/

theorem boxPInd_mul_sq_le_osc_local {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {g : E3 → ℝ} (hgm : Measurable g)
    (hgint : IntegrableOn (fun z => g z ^ 2) A)
    {Cosc : ℝ} (hCosc : ∫ z in A, g z ^ 2 ≤ Cosc ^ 2 * volA)
    {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) (i : Fin N) :
    ∫ x in abox N ℓ, (UBBInputs8.boxPInd volA A i (fun y => g (y i) * Ψ y) x) ^ 2
      ≤ Cosc ^ 2 * ∫ x in abox N ℓ, (Aind A (x i) * Ψ x) ^ 2 := by
  cases N with
  | zero => exact i.elim0
  | succ n =>
    have hL := boxPInd_self (m := n) (ℓ := ℓ) (vA := volA) (A := A) hA i
      (fun y : X (n + 1) => g (y i) * Ψ y)
    have hvol_eq : (∫ t in acube ℓ, A.indicator (fun _ => (1 : ℝ)) t) = volA := by
      have h1 : (∫ t in acube ℓ, A.indicator (fun _ => (1 : ℝ)) t) = ∫ t in A, (1 : ℝ) := by
        simpa using setIntegral_indicator_one_mul hA hAc (fun _ : E3 => (1 : ℝ))
      rw [h1, MeasureTheory.setIntegral_const, smul_eq_mul, mul_one,
        MeasureTheory.Measure.real_def, hvolA]
    have hR := AindMulSqPeelOsc (n := n) (ℓ := ℓ) hℓ hA hAc i hΨ
    have hC := oneRestSqIntegralLeOsc (n := n) (ℓ := ℓ) (volA := volA) hℓ hvol hA hvolA hAc
      hgm hgint hCosc hΨ i
    rw [hL, hvol_eq, hR]
    calc volA * (∫ r in abox n ℓ, (Q0C.oneRest volA A i (fun y => g (y i) * Ψ y) r) ^ 2)
        ≤ volA * ((Cosc ^ 2 / volA)
            * ∫ r in abox n ℓ, ∫ t in A, Ψ (kcInsN n i (t, r)) ^ 2) :=
          mul_le_mul_of_nonneg_left hC (le_of_lt hvol)
      _ = Cosc ^ 2 * (∫ r in abox n ℓ, ∫ t in A, Ψ (kcInsN n i (t, r)) ^ 2) := by
          field_simp
          try ring

end Work.BoseFixB1S
