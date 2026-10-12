import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.Gen.boxPInd_add_good
import Submission.Work.BoseFixB1S.Gen.boxPInd_mem_good
import Submission.Work.BoseFixB1S.boxPInd_sq_le_self
import Submission.Work.BoseFixB1S.mfPairBoxWBoundB1
import Submission.Work.hlocWire.boxPInd_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal
open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-- The state `x ↦ 1_A(x j)·Φ x` is `good` (measurable and bounded on balls) as soon as `Φ` is. -/
private theorem indicator_mul_mem_good {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (j : Fin N) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : Φ ∈ Work.BoseFixB1S.Gen.good N) :
    (fun y : Submission.BoseGases.X N => A.indicator (fun _ => (1 : ℝ)) (y j) * Φ y)
      ∈ Work.BoseFixB1S.Gen.good N := by
  obtain ⟨hΦm, hΦb⟩ := Work.BoseFixB1S.Gen.mem_good_iff.mp hΦ
  refine Work.BoseFixB1S.Gen.mem_good_iff.mpr ⟨?_, ?_⟩
  · exact ((measurable_const.indicator hA).comp (measurable_pi_apply j)).mul hΦm
  · intro Rs
    obtain ⟨C, hC⟩ := hΦb Rs
    refine ⟨max C 0, fun x hx => ?_⟩
    have h1 : |A.indicator (fun _ => (1 : ℝ)) (x j)| ≤ 1 := by
      by_cases h : x j ∈ A
      · rw [Set.indicator_of_mem h]; norm_num
      · rw [Set.indicator_of_notMem h]; norm_num
    calc |A.indicator (fun _ => (1 : ℝ)) (x j) * Φ x|
        = |A.indicator (fun _ => (1 : ℝ)) (x j)| * |Φ x| := abs_mul _ _
      _ ≤ 1 * C := mul_le_mul h1 (hC x hx) (abs_nonneg _) (by norm_num)
      _ ≤ max C 0 := by rw [one_mul]; exact le_max_left _ _

/-- The box indicator is bounded by `1`. -/
private theorem abs_indicator_one_le (A : Set (EuclideanSpace ℝ (Fin 3)))
    (y : EuclideanSpace ℝ (Fin 3)) :
    |A.indicator (fun _ => (1 : ℝ)) y| ≤ 1 := by
  by_cases h : y ∈ A
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]; norm_num

/-- The ordered distinct-pair sum as an iterated double sum. -/
private theorem sum_pairSet_eq_doubleSum' {N : ℕ} (g : Fin N × Fin N → ℝ) :
    (∑ p ∈ Submission.BoseGases.pairSet N, g p)
      = ∑ i : Fin N, ∑ j : Fin N, if i ≠ j then g (i, j) else 0 := by
  rw [Submission.BoseGases.pairSet, Finset.sum_filter, Fintype.sum_prod_type]

/-- **The per-pair defect estimate.**  At the box projections of `abox N ℓ` with box `A`, the
squared defect between the bare pair multiplication `1_A(x_i)·(1_A(x_j)·Φ)` and the pair
projection `P_i P_j Φ`, weighted by a pair kernel `W` with `0 ≤ W ≤ Cw`, is paid by the two
slot-`Q` counts with constant `2·Cw`. -/
private theorem mfPairDefectPerPair {N : ℕ} {ℓ V : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hℓ : 0 < ℓ) (hV : 0 < V) (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
        Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A)
    {W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (Cw : ℝ) (hCwnn : 0 ≤ Cw) (hWnn : ∀ x y, 0 ≤ W x y) (hWle : ∀ x y, W x y ≤ Cw)
    (i j : Fin N) :
    ∫ x in Submission.BoseGases.abox N ℓ,
        ((A.indicator (fun _ => (1 : ℝ)) (x i)
            * (A.indicator (fun _ => (1 : ℝ)) (x j) * Φ x))
          - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x) ^ 2
        * W (x i) (x j)
      ≤ 2 * Cw * ((∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
          + (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A j Φ x) ^ 2)) := by
  classical
  -- the projections act on the class of measurable states bounded on every ball
  have hΦgood : Φ ∈ Work.BoseFixB1S.Gen.good N :=
    Work.BoseFixB1S.Gen.continuous_mem_good hΦc
  have hPjgood : Work.UBBInputs8.boxPInd V A j Φ ∈ Work.BoseFixB1S.Gen.good N :=
    Work.BoseFixB1S.Gen.boxPInd_mem_good hℓ hA hAc j hΦgood
  -- additivity and homogeneity of `Pᵢ` at `good` states: `Pᵢ(Φ − PⱼΦ) = PᵢΦ − PᵢPⱼΦ`
  have hPi : Work.UBBInputs8.boxPInd V A i (Φ - Work.UBBInputs8.boxPInd V A j Φ)
      = Work.UBBInputs8.boxPInd V A i Φ
        - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) := by
    have harg : Φ - Work.UBBInputs8.boxPInd V A j Φ
        = Φ + (-1 : ℝ) • Work.UBBInputs8.boxPInd V A j Φ := by
      funext y
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hsum := Work.BoseFixB1S.Gen.boxPInd_add_good (volA := V) hℓ hA hAc i hΦgood
      ((Work.BoseFixB1S.Gen.good N).smul_mem (-1 : ℝ) hPjgood)
    rw [harg, hsum, Work.hlocWire.boxPInd_smul V A i (Work.UBBInputs8.boxPInd V A j Φ) (-1),
      neg_one_smul]
    abel
  -- bounds and measurability on the box
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox N ℓ) (f := Φ) hΦc.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 (Submission.BoseGases.zero_mem_abox hℓ.le))
  have hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ C :=
    fun x hx => by simpa [Real.norm_eq_abs] using hC x hx
  have hPjb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd V A j Φ x| ≤ C :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc j hΦb
  have hPijb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x| ≤ C :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hPjb
  have hQib : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd V A i Φ x| ≤ 2 * C :=
    Work.BoseFixB1S.abs_boxQInd_le hℓ hV hA hVeq hAc i hΦb
  have hQjb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd V A j Φ x| ≤ 2 * C :=
    Work.BoseFixB1S.abs_boxQInd_le hℓ hV hA hVeq hAc j hΦb
  have hΦm : Measurable Φ := hΦc.measurable
  have hPjm : Measurable (Work.UBBInputs8.boxPInd V A j Φ) :=
    Work.BoseFixB1S.measurable_boxPInd V A hA j hΦm
  have hQim : Measurable (Work.UBBInputs8.boxQInd V A i Φ) :=
    Work.BoseFixB1S.measurable_boxQInd V hA i hΦm
  have hQjm : Measurable (Work.UBBInputs8.boxQInd V A j Φ) :=
    Work.BoseFixB1S.measurable_boxQInd V hA j hΦm
  have hΨm : Measurable (fun x : Submission.BoseGases.X N =>
      Φ x - Work.UBBInputs8.boxPInd V A j Φ x) := hΦm.sub hPjm
  have hΨb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Φ x - Work.UBBInputs8.boxPInd V A j Φ x| ≤ 2 * C := fun x hx =>
    calc |Φ x - Work.UBBInputs8.boxPInd V A j Φ x|
        ≤ |Φ x| + |Work.UBBInputs8.boxPInd V A j Φ x| := abs_sub _ _
      _ ≤ C + C := add_le_add (hΦb x hx) (hPjb x hx)
      _ = 2 * C := by ring
  -- the defect
  set D : Submission.BoseGases.X N → ℝ := fun x =>
    A.indicator (fun _ => (1 : ℝ)) (x i) * (A.indicator (fun _ => (1 : ℝ)) (x j) * Φ x)
      - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x with hDdef
  have hDm : Measurable D := by
    rw [hDdef]
    exact (((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul
      (((measurable_const.indicator hA).comp (measurable_pi_apply j)).mul hΦm)).sub
        (Work.BoseFixB1S.measurable_boxPInd V A hA i hPjm)
  have hDb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |D x| ≤ 2 * C := by
    intro x hx
    have hInd : |A.indicator (fun _ => (1 : ℝ)) (x i)
        * (A.indicator (fun _ => (1 : ℝ)) (x j) * Φ x)| ≤ C := by
      rw [abs_mul, abs_mul]
      calc |A.indicator (fun _ => (1 : ℝ)) (x i)|
            * (|A.indicator (fun _ => (1 : ℝ)) (x j)| * |Φ x|)
          ≤ 1 * (1 * C) :=
            mul_le_mul (abs_indicator_one_le A (x i))
              (mul_le_mul (abs_indicator_one_le A (x j)) (hΦb x hx) (abs_nonneg _)
                (by norm_num)) (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
        _ ≤ C := by linarith
    simp only [hDdef]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i) * (A.indicator (fun _ => (1 : ℝ)) (x j) * Φ x)
          - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x|
        ≤ |A.indicator (fun _ => (1 : ℝ)) (x i)
            * (A.indicator (fun _ => (1 : ℝ)) (x j) * Φ x)|
          + |Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x| := abs_sub _ _
      _ ≤ C + C := add_le_add hInd (hPijb x hx)
      _ = 2 * C := by ring
  -- integrability of the three squared objects
  have hDint : IntegrableOn (fun x => (D x) ^ 2) (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_sq_of_bound hℓ hDm hDb
  have hQint : IntegrableOn (fun x => (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
      (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_sq_of_bound hℓ hQim hQib
  have hQjint : IntegrableOn (fun x => (Work.UBBInputs8.boxQInd V A j Φ x) ^ 2)
      (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_sq_of_bound hℓ hQjm hQjb
  have hPint : IntegrableOn
      (fun x => (Work.UBBInputs8.boxPInd V A i (Φ - Work.UBBInputs8.boxPInd V A j Φ) x) ^ 2)
      (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_sq_of_bound hℓ
      (Work.BoseFixB1S.measurable_boxPInd V A hA i hΨm)
      (fun x hx => Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hΨb x hx)
  -- `D` agrees a.e. with `Φ − PᵢPⱼΦ` on the box (the box-support hypothesis)
  have hDae : D =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
      (fun x => Φ x - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x) := by
    filter_upwards [hsupp] with x hx
    have hInd : A.indicator (fun _ => (1 : ℝ)) (x i)
        * (A.indicator (fun _ => (1 : ℝ)) (x j) * Φ x) = Φ x := by
      by_cases h0 : Φ x = 0
      · simp [h0]
      · rw [Set.indicator_of_mem (hx h0 i), Set.indicator_of_mem (hx h0 j)]
        simp
    simp only [hDdef]
    rw [hInd]
  -- the split `D = QᵢΦ + Pᵢ(Φ − PⱼΦ)`
  have hDsplit : D =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
      (fun x => Work.UBBInputs8.boxQInd V A i Φ x
        + Work.UBBInputs8.boxPInd V A i (Φ - Work.UBBInputs8.boxPInd V A j Φ) x) := by
    filter_upwards [hDae, hsupp] with x hxD hx
    rw [hxD, hPi]
    have hInd : A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x = Φ x := by
      by_cases h0 : Φ x = 0
      · simp [h0]
      · rw [Set.indicator_of_mem (hx h0 i)]
        simp
    simp only [Work.UBBInputs8.boxQInd, Pi.sub_apply]
    rw [hInd]
    ring
  -- the pointwise square estimate
  have hpt : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      (D x) ^ 2 ≤ 2 * (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2
        + 2 * (Work.UBBInputs8.boxPInd V A i (Φ - Work.UBBInputs8.boxPInd V A j Φ) x) ^ 2 := by
    filter_upwards [hDsplit] with x hx
    rw [hx]
    nlinarith [sq_nonneg (Work.UBBInputs8.boxQInd V A i Φ x
      - Work.UBBInputs8.boxPInd V A i (Φ - Work.UBBInputs8.boxPInd V A j Φ) x)]
  have hstep1 : (∫ x in Submission.BoseGases.abox N ℓ, (D x) ^ 2)
      ≤ 2 * (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
        + 2 * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd V A i (Φ - Work.UBBInputs8.boxPInd V A j Φ) x) ^ 2) := by
    have hmono := MeasureTheory.integral_mono_ae hDint
      ((hQint.const_mul 2).add (hPint.const_mul 2)) hpt
    simp only [Pi.add_apply] at hmono
    rw [MeasureTheory.integral_add (hQint.const_mul 2) (hPint.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmono
    exact hmono
  -- the contraction and the identification of the `j`-count
  have hcontr : (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd V A i (Φ - Work.UBBInputs8.boxPInd V A j Φ) x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x - Work.UBBInputs8.boxPInd V A j Φ x) ^ 2 :=
    Work.BoseFixB1S.boxPInd_sq_le_self hℓ hV hA hVeq hAc i hΨm hΨb
  have hid : (∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x - Work.UBBInputs8.boxPInd V A j Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxQInd V A j Φ x) ^ 2 := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hsupp] with x hx
    have hInd : A.indicator (fun _ => (1 : ℝ)) (x j) * Φ x = Φ x := by
      by_cases h0 : Φ x = 0
      · simp [h0]
      · rw [Set.indicator_of_mem (hx h0 j)]
        simp
    simp only [Work.UBBInputs8.boxQInd, Pi.sub_apply]
    rw [hInd]
  -- the weighted step
  have hstepW : (∫ x in Submission.BoseGases.abox N ℓ, (D x) ^ 2 * W (x i) (x j))
      ≤ Cw * (∫ x in Submission.BoseGases.abox N ℓ, (D x) ^ 2) := by
    by_cases hint : IntegrableOn (fun x => (D x) ^ 2 * W (x i) (x j))
      (Submission.BoseGases.abox N ℓ) volume
    · have hCWint : IntegrableOn (fun x => Cw * (D x) ^ 2)
          (Submission.BoseGases.abox N ℓ) volume := hDint.const_mul Cw
      have hpt' : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
          (D x) ^ 2 * W (x i) (x j) ≤ Cw * (D x) ^ 2 := by
        filter_upwards with x
        have h1 : (D x) ^ 2 * W (x i) (x j) ≤ (D x) ^ 2 * Cw :=
          mul_le_mul_of_nonneg_left (hWle (x i) (x j)) (sq_nonneg _)
        linarith [h1]
      have hmono := MeasureTheory.integral_mono_ae hint hCWint hpt'
      rwa [MeasureTheory.integral_const_mul] at hmono
    · rw [MeasureTheory.integral_undef hint]
      exact mul_nonneg hCwnn (MeasureTheory.integral_nonneg_of_ae (Eventually.of_forall
        (fun x => sq_nonneg (D x))))
  have hend : (∫ x in Submission.BoseGases.abox N ℓ, (D x) ^ 2)
      ≤ 2 * (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
        + 2 * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A j Φ x) ^ 2) := by
    linarith [hstep1, hcontr, hid]
  calc ∫ x in Submission.BoseGases.abox N ℓ, (D x) ^ 2 * W (x i) (x j)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          ((A.indicator (fun _ => (1 : ℝ)) (x i)
              * (A.indicator (fun _ => (1 : ℝ)) (x j) * Φ x))
            - Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A j Φ) x) ^ 2
          * W (x i) (x j) := hDdef ▸ rfl
    _ ≤ Cw * (∫ x in Submission.BoseGases.abox N ℓ, (D x) ^ 2) := hstepW
    _ ≤ Cw * (2 * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
          + 2 * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A j Φ x) ^ 2)) :=
        mul_le_mul_of_nonneg_left hend hCwnn
    _ = 2 * Cw * ((∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2)
          + (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A j Φ x) ^ 2)) := by ring

/-! ## The pair-sum bookkeeping -/

/-- The pair-defect sum of the target statement (the left-hand side). -/
private abbrev mfDefectSum {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet n,
    ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      ((Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.1)
          * ((Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)
        - Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.1
            (Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.2 Φ) x) ^ 2
      * Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2)

/-- Each of the two slot-sums over `pairSet n` is at most `n` times the total. -/
private theorem pairSet_sum_fst_le {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ p ∈ Submission.BoseGases.pairSet n, f p.1) ≤ (n : ℝ) * ∑ i : Fin n, f i := by
  rw [sum_pairSet_eq_doubleSum']
  calc (∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then f i else 0))
      ≤ ∑ i : Fin n, ∑ _j : Fin n, f i := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        by_cases h : i = j
        · simpa [h] using hf i
        · simp [h]
    _ = ∑ i : Fin n, (n : ℝ) * f i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (n : ℝ) * ∑ i : Fin n, f i := by rw [Finset.mul_sum]

/-- The partner slot-sum over `pairSet n` obeys the same bound. -/
private theorem pairSet_sum_snd_le {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ p ∈ Submission.BoseGases.pairSet n, f p.2) ≤ (n : ℝ) * ∑ i : Fin n, f i := by
  rw [sum_pairSet_eq_doubleSum']
  calc (∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then f j else 0))
      ≤ ∑ _i : Fin n, ∑ j : Fin n, f j := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        by_cases h : i = j
        · simpa [h] using hf j
        · simp [h]
    _ = (n : ℝ) * ∑ j : Fin n, f j := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The summed pair bound: `Σ_{i≠j}(f i + f j) ≤ 2n Σ_i f i` for `f ≥ 0`. -/
private theorem pairSet_sum_add_le {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ p ∈ Submission.BoseGases.pairSet n, (f p.1 + f p.2))
      ≤ 2 * (n : ℝ) * ∑ i : Fin n, f i := by
  rw [Finset.sum_add_distrib]
  have h1 := pairSet_sum_fst_le f hf
  have h2 := pairSet_sum_snd_le f hf
  linarith

/-- **The target theorem with the uniform kernel bound supplied as a hypothesis.** -/
private theorem mfPairDefectLeB1_aux {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hvrad : _root_.BoseGases.IsRadial v) (hav : 0 < _root_.BoseGases.a v) {Bv : ℝ}
    (hvb : ∀ y : EuclideanSpace ℝ (Fin 3), |v y| ≤ Bv) (hBv : 0 ≤ Bv)
    (Cw : ℝ) (hCwnn : 0 ≤ Cw)
    (hCw : ∀ (μ : ℝ), 0 ≤ μ → 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) →
        0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d →
        R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16 →
        R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 →
        ∀ (u x y : EuclideanSpace ℝ (Fin 3)), |Work.BoseFixB1S.boxW h μ u x y| ≤ Cw) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (μ : ℝ), 0 ≤ μ → 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) →
        0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d →
        R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16 →
        R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 →
        ∀ (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)),
          Continuous Φ → Work.BoseFixB1S.mfSupp v μ n Φ u →
          0 < Work.BoseFixB1S.mfV v μ u →
          mfDefectSum h μ n Φ u ≤ K * (n : ℝ) * Work.BoseFixB1S.mfQ v μ n Φ u := by
  classical
  refine ⟨4 * Cw, by positivity, ?_⟩
  intro μ hμ hℓ hd hR16 hRχ n Φ u hΦc hsupp hV
  -- the geometry of the sliding box
  have hAmeas : MeasurableSet (Work.BoseFixB1S.boxA v μ u) :=
    Work.SmallBoxSliding.measurableSet_dlBox _ _ _
  have hAc : Work.BoseFixB1S.boxA v μ u ⊆
      Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) :=
    Work.SmallBoxSliding.dlBox_subset_acube _ _ _
  have hVeq : Work.BoseFixB1S.mfV v μ u
      = (MeasureTheory.volume (Work.BoseFixB1S.boxA v μ u)).toReal := by
    rw [Work.BoseFixB1S.mfV_def, Work.BoseFixB1S.boxA,
      Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hsupp' : ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
      Φ x ≠ 0 → ∀ i : Fin n, x i ∈ Work.BoseFixB1S.boxA v μ u := hsupp
  have hWnn : ∀ x y : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseFixB1S.boxW h μ u x y :=
    fun x y => Work.BoseFixB1.wSmall_v_nonneg (v := v) hv _ _ _ _ x y
  have hWle : ∀ x y : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1S.boxW h μ u x y ≤ Cw :=
    fun x y => le_trans (le_abs_self _) (hCw μ hμ hℓ hd hR16 hRχ u x y)
  -- the per-slot `Q`-counts
  set a : Fin n → ℝ := fun i =>
    ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Work.UBBInputs8.boxQInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) i Φ x) ^ 2
    with hadef
  have hann : ∀ i : Fin n, 0 ≤ a i := fun i =>
    MeasureTheory.integral_nonneg_of_ae (Eventually.of_forall (fun x => sq_nonneg _))
  -- the per-pair estimate
  have hper : ∀ p ∈ Submission.BoseGases.pairSet n,
      (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          ((Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.1)
              * ((Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)
            - Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.1
                (Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.2 Φ) x) ^ 2
          * Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2))
        ≤ 2 * Cw * (a p.1 + a p.2) := by
    intro p hp
    have hmain := mfPairDefectPerPair (N := n)
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (V := Work.BoseFixB1S.mfV v μ u)
      (A := Work.BoseFixB1S.boxA v μ u) hℓ hV hAmeas hVeq hAc hΦc hsupp'
      (W := fun x y => Work.BoseFixB1S.boxW h μ u x y) Cw hCwnn hWnn hWle p.1 p.2
    simpa only [hadef] using hmain
  have hsum_le : mfDefectSum h μ n Φ u
      ≤ ∑ p ∈ Submission.BoseGases.pairSet n, 2 * Cw * (a p.1 + a p.2) :=
    Finset.sum_le_sum hper
  have hpull : (∑ p ∈ Submission.BoseGases.pairSet n, 2 * Cw * (a p.1 + a p.2))
      = 2 * Cw * (∑ p ∈ Submission.BoseGases.pairSet n, (a p.1 + a p.2)) := by
    rw [Finset.mul_sum]
  have hsum2 : (∑ p ∈ Submission.BoseGases.pairSet n, (a p.1 + a p.2))
      ≤ 2 * (n : ℝ) * ∑ i : Fin n, a i := pairSet_sum_add_le a hann
  have hmfQ : Work.BoseFixB1S.mfQ v μ n Φ u = ∑ i : Fin n, a i := by
    rw [Work.BoseFixB1S.mfQ_def, hadef]
    rfl
  calc mfDefectSum h μ n Φ u
      ≤ ∑ p ∈ Submission.BoseGases.pairSet n, 2 * Cw * (a p.1 + a p.2) := hsum_le
    _ = 2 * Cw * (∑ p ∈ Submission.BoseGases.pairSet n, (a p.1 + a p.2)) := hpull
    _ ≤ 2 * Cw * (2 * (n : ℝ) * ∑ i : Fin n, a i) :=
        mul_le_mul_of_nonneg_left hsum2 (by linarith [hCwnn] : (0 : ℝ) ≤ 2 * Cw)
    _ = (4 * Cw) * (n : ℝ) * Work.BoseFixB1S.mfQ v μ n Φ u := by
        rw [hmfQ]
        ring

theorem mfPairDefectLeB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hvrad : _root_.BoseGases.IsRadial v) (hav : 0 < _root_.BoseGases.a v) {Bv : ℝ}
    (hvb : ∀ y : EuclideanSpace ℝ (Fin 3), |v y| ≤ Bv) (hBv : 0 ≤ Bv) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (μ : ℝ), 0 ≤ μ → 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) →
        0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d →
        R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16 →
        R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 →
        ∀ (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)),
          Continuous Φ → Work.BoseFixB1S.mfSupp v μ n Φ u →
          0 < Work.BoseFixB1S.mfV v μ u →
          (∑ p ∈ Submission.BoseGases.pairSet n,
              ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (((Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.1)
                    * ((Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x))
                  - (Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.1
                      (Work.UBBInputs8.boxPInd (Work.BoseFixB1S.mfV v μ u) (Work.BoseFixB1S.boxA v μ u) p.2 Φ) x)) ^ 2
                * Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2))
            ≤ K * (n : ℝ) * Work.BoseFixB1S.mfQ v μ n Φ u := by
  obtain ⟨Cw, hCwnn, hCw⟩ := mfPairBoxWBoundB1 (v := v) h hR hv_supp hav hvb hBv
  exact mfPairDefectLeB1_aux h hv hv1 hR hv_supp hvrad hav hvb hBv Cw hCwnn hCw

end

end Work.BoseFixB1S
