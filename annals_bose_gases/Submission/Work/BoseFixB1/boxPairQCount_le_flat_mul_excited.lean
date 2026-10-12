import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxFlatSqJensen
import Submission.Work.BoseFixB1S.boxPairQCount_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

open Submission.BoseGases

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 1. The per-slot `Q`-square identity -/

/-- **Per-slot identity**: `∫_{abox}(Q_iΦ)² = ∫_{abox} 1_A(x i)·Φ² − ∫_{abox}(P_iΦ)²`, valid for
every continuous `Φ` (no support assumption).  Pointwise,
`(Q_iΦ)² = σ_iΦ² − 2·Φ·(P_iΦ) + (P_iΦ)²` with `σ_i = 1_A(x i)` (using `σ_i² = σ_i` and
`σ_i·P_iΦ = P_iΦ`), and `∫ Φ·(P_iΦ) = ∫(P_iΦ)²` is `Q0C.one_self_N`. -/
theorem boxQInd_sq_integral_sub {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (i : Fin N) :
    (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
      = (∫ x in Submission.BoseGases.abox N ℓ,
            A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
        - ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 := by
  obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  have hΦb : ∀ x ∈ abox N ℓ, |Φ x| ≤ C := fun x hx => by
    simpa [Real.norm_eq_abs] using hC x hx
  have hΦm : Measurable Φ := hΦc.measurable
  have hσm : Measurable (fun x : Submission.BoseGases.X N =>
      A.indicator (fun _ => (1 : ℝ)) (x i)) :=
    (measurable_const.indicator hA).comp (measurable_pi_apply i)
  have hum : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA i hΦm
  have hub : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ C :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i hΦb
  have hσb : ∀ x : Submission.BoseGases.X N,
      |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := fun x => by
    by_cases hx : x i ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  -- the pointwise expansion
  have hpt : ∀ x : Submission.BoseGases.X N,
      (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2
        = A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2
          - 2 * (Φ x * Work.UBBInputs8.boxPInd volA A i Φ x)
          + (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 := by
    intro x
    rw [Work.UBBInputs8.boxQInd]
    by_cases hx : x i ∈ A
    · simp only [Set.indicator_of_mem hx]
      ring
    · have hzero : Work.UBBInputs8.boxPInd volA A i Φ x = 0 := by
        simp only [Work.UBBInputs8.boxPInd, Set.indicator_of_notMem hx, mul_zero]
      rw [Set.indicator_of_notMem hx, hzero]
      ring
  -- integrability of the three summands
  have hF1 : IntegrableOn (fun x : Submission.BoseGases.X N =>
      A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2) (abox N ℓ) volume := by
    have h := Work.BoseFixB1S.integrableOn_mul_of_bound (N := N) hℓ
      (f := fun x : Submission.BoseGases.X N => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
      (g := Φ) (hσm.mul hΦm) hΦm
      (Cf := 1 * C) (Cg := C) ?_ hΦb
    · refine h.congr ?_
      filter_upwards with x
      ring
    · intro x hx
      rw [abs_mul]
      exact mul_le_mul (hσb x) (hΦb x hx) (abs_nonneg _) zero_le_one
  have hF2 : IntegrableOn (fun x : Submission.BoseGases.X N =>
      2 * (Φ x * Work.UBBInputs8.boxPInd volA A i Φ x)) (abox N ℓ) volume :=
    (Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hΦm hum hΦb hub).const_mul 2
  have hF3 : IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) (abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_sq_of_bound hℓ hum hub
  -- linearity and the peel
  have hEq : (∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
      = (∫ x in Submission.BoseGases.abox N ℓ,
            A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
        - ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 := by
    have h1 : (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            (A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2
              - 2 * (Φ x * Work.UBBInputs8.boxPInd volA A i Φ x)
              + (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) := by
      apply setIntegral_congr_fun (abox_measurable N ℓ)
      intro x hx
      exact hpt x
    have e1 : (∫ x in Submission.BoseGases.abox N ℓ,
        (((fun x : Submission.BoseGases.X N =>
              A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
            - (fun x : Submission.BoseGases.X N =>
                2 * (Φ x * Work.UBBInputs8.boxPInd volA A i Φ x)))
            + fun x : Submission.BoseGases.X N =>
                (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) x)
        = (∫ x in Submission.BoseGases.abox N ℓ,
              ((fun x : Submission.BoseGases.X N =>
                  A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
                - fun x : Submission.BoseGases.X N =>
                    2 * (Φ x * Work.UBBInputs8.boxPInd volA A i Φ x)) x)
          + ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 :=
      integral_add (hF1.sub hF2) hF3
    have e2 : (∫ x in Submission.BoseGases.abox N ℓ,
        ((fun x : Submission.BoseGases.X N =>
            A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
          - fun x : Submission.BoseGases.X N =>
              2 * (Φ x * Work.UBBInputs8.boxPInd volA A i Φ x)) x)
        = (∫ x in Submission.BoseGases.abox N ℓ,
              A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
          - ∫ x in Submission.BoseGases.abox N ℓ,
              2 * (Φ x * Work.UBBInputs8.boxPInd volA A i Φ x) :=
      integral_sub hF1 hF2
    simp only [Pi.sub_apply, Pi.add_apply] at e1 e2
    rw [h1, e1, e2, MeasureTheory.integral_const_mul,
      Work.BoseFixB1S.Q0C.one_self_N hℓ hvol hA hvolA hAc i hΦc]
    ring
  exact hEq

/-! ## 2. The corrected sharp count bound -/

/-- **The correct sharp count bound**: the ordered `PQ`-pair count is at most
`boxFlatCount · (N − boxFlatCount)` for a state with `∫Φ² = 1`.  This is the combination of the
corpus's `boxPairQCount_eq` (`LHS ≤ (N−1)n₀ − cS₂`) with the Jensen inequality `Q0C.count_ge`
(`cS₂ ≥ n₀² − n₀`); it needs no hypothesis beyond the normalisation. -/
theorem boxPairQCount_le_flat_mul_flatDif {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hI : ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 = 1) :
    (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) ^ 2)
      ≤ Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
        * ((N : ℝ) - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ) := by
  have hpair := Work.BoseFixB1S.boxPairQCount_eq hℓ hvol hA hvolA hAc hΦc
  have hjensen := Work.BoseFixB1S.Q0C.count_ge hℓ hvol hA hvolA hAc hΦc hI
  nlinarith [hpair, hjensen]

/-! ## 3. The repaired statement (with the missing hypothesis) -/

/-- If the state has no mass outside `A^N` (`R`-free, `R_i := 1 − 1_A(x i)`), then the excited
count is exactly `N − boxFlatCount`. -/
theorem boxQCount_eq_N_sub_flatCount_of_Rfree {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ)
    (hvol : 0 < volA) {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hI : ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 = 1)
    (hR : ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (1 - A.indicator (fun _ => (1 : ℝ)) (x i)) * (Φ x) ^ 2 = 0) :
    Work.BoseFixB1S.boxQCount volA ℓ A Φ
      = (N : ℝ) - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ := by
  have hΦm : Measurable Φ := hΦc.measurable
  -- each `Q`-square integral splits as `∫σ_iΦ² − ‖P_iΦ‖²`
  have hstep : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
        = (∫ x in Submission.BoseGases.abox N ℓ,
              A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
          - ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 :=
    fun i => boxQInd_sq_integral_sub hℓ hvol hA hvolA hAc hΦc i
  -- the total `σ`-mass is `N` when there is no `R`-mass
  have hsplit : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2) = (N : ℝ) := by
    have h1 : ∀ i : Fin N,
        (∫ x in Submission.BoseGases.abox N ℓ,
            A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
          = 1 - ∫ x in Submission.BoseGases.abox N ℓ,
              (1 - A.indicator (fun _ => (1 : ℝ)) (x i)) * (Φ x) ^ 2 := by
      intro i
      obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
        (s := abox N ℓ) (f := Φ) hΦc.continuousOn
      have hΦb : ∀ x ∈ abox N ℓ, |Φ x| ≤ C := fun x hx => by
        simpa [Real.norm_eq_abs] using hC x hx
      have hσb' : ∀ x : Submission.BoseGases.X N,
          |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := fun x => by
        by_cases hx : x i ∈ A <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
      have hm1 : IntegrableOn (fun x : Submission.BoseGases.X N =>
          A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2) (abox N ℓ) volume := by
        have h := Work.BoseFixB1S.integrableOn_mul_of_bound (N := N) hℓ
          (f := fun x : Submission.BoseGases.X N =>
            A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
          (g := Φ)
          (((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul hΦm) hΦm
          (Cf := 1 * C) (Cg := C) ?_ hΦb
        · refine h.congr ?_
          filter_upwards with x
          ring
        · intro x hx
          rw [abs_mul]
          exact mul_le_mul (hσb' x) (hΦb x hx) (abs_nonneg _) zero_le_one
      have hm2 : IntegrableOn (fun x : Submission.BoseGases.X N =>
          (1 - A.indicator (fun _ => (1 : ℝ)) (x i)) * (Φ x) ^ 2) (abox N ℓ) volume := by
        have h := Work.BoseFixB1S.integrableOn_mul_of_bound (N := N) hℓ
          (f := fun x : Submission.BoseGases.X N =>
            (1 - A.indicator (fun _ => (1 : ℝ)) (x i)) * Φ x)
          (g := Φ)
          ((measurable_const.sub ((measurable_const.indicator hA).comp
            (measurable_pi_apply i))).mul hΦm) hΦm
          (Cf := 1 * C) (Cg := C) ?_ hΦb
        · refine h.congr ?_
          filter_upwards with x
          ring
        · intro x hx
          rw [abs_mul]
          have hle : |(1 : ℝ) - A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
            by_cases hxi : x i ∈ A <;>
              simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
          exact mul_le_mul hle (hΦb x hx) (abs_nonneg _) zero_le_one
      have hEq : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)
          = (∫ x in Submission.BoseGases.abox N ℓ,
                A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
            + ∫ x in Submission.BoseGases.abox N ℓ,
                (1 - A.indicator (fun _ => (1 : ℝ)) (x i)) * (Φ x) ^ 2 := by
        rw [← integral_add hm1 hm2]
        apply setIntegral_congr_fun (abox_measurable N ℓ)
        intro x hx
        ring
      linarith [hEq, hI]
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_sub_distrib, hR, sub_zero]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hcongr : (∑ i : Fin N,
      ∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
      = ∑ i : Fin N,
          ((∫ x in Submission.BoseGases.abox N ℓ,
              A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
            - ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) :=
    Finset.sum_congr rfl (fun i _ => hstep i)
  rw [Work.BoseFixB1S.boxQCount, Work.BoseFixB1S.boxFlatCount, hcongr,
    Finset.sum_sub_distrib, hsplit]

/-- **The repaired statement**: the requested conclusion holds once the state is known to have
no mass outside `A^N`, i.e. `Σ_i ∫_{abox}(1 − 1_A(x i))Φ² = 0` (equivalently `n₊ = N − n₀`).
The requested statement is the special case `hR` *omitted*, which is false — see the header. -/
theorem boxPairQCount_le_flat_mul_excited_of_Rfree {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ)
    (hvol : 0 < volA) {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hI : ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 = 1)
    (hR : ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (1 - A.indicator (fun _ => (1 : ℝ)) (x i)) * (Φ x) ^ 2 = 0) :
    (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) ^ 2)
      ≤ Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
        * Work.BoseFixB1S.boxQCount volA ℓ A Φ := by
  have hmain := boxPairQCount_le_flat_mul_flatDif hℓ hvol hA hvolA hAc hΦc hI
  have hQ := boxQCount_eq_N_sub_flatCount_of_Rfree hℓ hvol hA hvolA hAc hΦc hI hR
  rw [hQ]
  exact hmain

/-- **The repaired statement, support form**: the requested conclusion holds when `Φ` vanishes
wherever one coordinate leaves `A` (equivalently `Φ` is supported in `A^N`). -/
theorem boxPairQCount_le_flat_mul_excited_of_supp {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ)
    (hvol : 0 < volA) {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hI : ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 = 1)
    (hSupp : ∀ x ∈ Submission.BoseGases.abox N ℓ, Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A) :
    (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) ^ 2)
      ≤ Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
        * Work.BoseFixB1S.boxQCount volA ℓ A Φ := by
  refine boxPairQCount_le_flat_mul_excited_of_Rfree hℓ hvol hA hvolA hAc hΦc hI ?_
  have hzero : ∀ i : Fin N, (∫ x in Submission.BoseGases.abox N ℓ,
      (1 - A.indicator (fun _ => (1 : ℝ)) (x i)) * (Φ x) ^ 2) = 0 := by
    intro i
    have hae : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
        (1 - A.indicator (fun _ => (1 : ℝ)) (x i)) * (Φ x) ^ 2 = 0 := by
      filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
      by_cases h : Φ x = 0
      · rw [h]
        ring
      · rw [Set.indicator_of_mem (hSupp x hx h i)]
        ring
    exact integral_eq_zero_of_ae hae
  rw [Finset.sum_congr rfl (fun i _ => hzero i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_zero]

/-! ## 4. The requested statement (verbatim) — **REFUTED**

See the module header: the statement below is *false* (a counterexample with `N = 2`, `ℓ = 1`
and a continuous state gives `LHS = 2/3 > 4/9 = boxFlatCount · boxQCount`).  It is kept here
verbatim only so that the refutation is self-contained. -/

theorem boxPairQCount_le_flat_mul_excited {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hI : ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 = 1) :
    (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) ^ 2)
      ≤ Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
        * Work.BoseFixB1S.boxQCount volA ℓ A Φ := by
  sorry

end Work.BoseFixB1
