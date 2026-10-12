import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.BoxPairIntGenC2.boxC2SumC2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxC2SumC` -- the box `(c2)` sum identity, weak hypotheses

The box analogue of `Submission.BoseGases.c2_sum` at an arbitrary measurable box `A` of volume
`volA` and a window `χ` vanishing off `A`, for merely *continuous* `χ` and `Φ` (the sibling
statement `Work.BoseFixB1.boxC2SumC2` assumes `ContDiff`; none of the lemmas underneath need
it).  The proof replays the assembly of `boxC2SumC2`; the per-pair input is reproved below as
`boxPair_perPairC_weak`, exactly as `boxPair_perPairC2` was proved, with `ContDiff` relaxed to
`Continuous`.
-/

namespace Work.BoseFixB1S

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal
open _root_.BoseGases Submission.BoseGases
open Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The per-pair box assembly for a continuous window and a continuous state -/

lemma boxPair_perPairC_weak {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {χ : E3 → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦ : Continuous Φ)
    (i : Fin (N + 2)) (j' : Fin (N + 1)) (p : E3) :
    (volA⁻¹ : ℂ) * (∫ r2 in Submission.BoseGases.abox N ℓ,
        boxPairSlot A Φ (boxWinModeC volA A χ (-p)) (boxWinModeC volA A χ p) i j' r2
          * boxPairMean A Φ i j' r2)
      = (volA : ℂ) * ∫ y in A, ∫ z in A,
          (χ y : ℂ) * (χ z : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ))
            * ((boxPairFibreFun volA ℓ A Φ i (i.succAbove j') y z : ℝ) : ℂ) := by
  have hΦc : Continuous Φ := hΦ
  obtain ⟨B, hB0, hB⟩ := exists_bound_abox (N := N + 2) hℓ hΦc
  obtain ⟨Cχ, hCχ⟩ := hχs.exists_bound_of_continuous hχc
  have hCχ0 : 0 ≤ max Cχ 0 := le_max_right _ _
  have hCχb : ∀ z : E3, ‖χ z‖ ≤ max Cχ 0 := fun z => le_trans (hCχ z) (le_max_left _ _)
  -- the bound for the doubly `Q`-projected state on doubly inserted configurations
  have hQbound : ∀ (y z : E3), y ∈ A → z ∈ A → ∀ r2 ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd volA A (i.succAbove j')
        (Work.UBBInputs8.boxQInd volA A i Φ)
          (Submission.BoseGases.ins2 i j' y z r2)| ≤ 4 * B := by
    intro y z hy hz r2 hr2
    have hx : ∀ j, (Submission.BoseGases.ins2 i j' y z r2) j ∈ Submission.BoseGases.acube ℓ :=
      Work.BoseFixB1S.Q0C.ins2_mem_abox hAc i j' hy hz hr2
    have h1 : ∀ w : Submission.BoseGases.X (N + 2),
        (∀ j, w j ∈ Submission.BoseGases.acube ℓ) → |Φ w| ≤ B := fun w hw => by
      rw [← Real.norm_eq_abs]; exact hB w hw
    have h2 : ∀ w : Submission.BoseGases.X (N + 2),
        (∀ j, w j ∈ Submission.BoseGases.acube ℓ) →
        |Work.UBBInputs8.boxQInd volA A i Φ w| ≤ 2 * B :=
      fun w hw => abs_boxQInd_le_two_mul hℓ hvolpos hAc hvolA h1 i w hw
    have h3 : ∀ w : Submission.BoseGases.X (N + 2),
        (∀ j, w j ∈ Submission.BoseGases.acube ℓ) →
        |Work.UBBInputs8.boxQInd volA A (i.succAbove j')
          (Work.UBBInputs8.boxQInd volA A i Φ) w| ≤ 2 * (2 * B) :=
      fun w hw => abs_boxQInd_le_two_mul hℓ hvolpos hAc hvolA h2 (i.succAbove j') w hw
    have h4 := h3 _ hx
    linarith
  -- measurability of the two factors
  have hkernm : Measurable (fun q : Submission.BoseGases.X N × (E3 × E3) =>
      (χ q.2.1 : ℂ) * (χ q.2.2 : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ p (q.2.1 - q.2.2) : ℝ) : ℂ))) := by
    refine Measurable.mul ?_ ?_
    · exact (Complex.continuous_ofReal.measurable.comp
        (hχc.measurable.comp measurable_snd.fst)).mul
        (Complex.continuous_ofReal.measurable.comp
          (hχc.measurable.comp measurable_snd.snd))
    · refine Complex.measurable_exp.comp ?_
      refine Measurable.const_mul ?_ Complex.I
      exact Complex.continuous_ofReal.measurable.comp
        (continuous_inner.measurable.comp
          (measurable_const.prodMk (measurable_snd.fst.sub measurable_snd.snd)))
  have hQQm : Measurable (fun q : Submission.BoseGases.X N × (E3 × E3) =>
      ((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
        (Work.UBBInputs8.boxQInd volA A i Φ)
          (Submission.BoseGases.ins2 i j' q.2.1 q.2.2 q.1) : ℝ) : ℂ)) := by
    refine Complex.continuous_ofReal.measurable.comp ?_
    refine (Work.SlotWord.measurable_boxQInd volA A hA (i.succAbove j') ?_).comp ?_
    · exact Work.SlotWord.measurable_boxQInd volA A hA i hΦc.measurable
    · unfold Submission.BoseGases.ins2
      exact (Submission.BoseGases.kcInsN (N + 1) i).measurable.comp
        (Measurable.prodMk measurable_snd.fst
          ((Submission.BoseGases.kcInsN N j').measurable.comp
            (Measurable.prodMk measurable_snd.snd measurable_fst)))
  have hHm : Measurable (fun q : Submission.BoseGases.X N × (E3 × E3) =>
      ((χ q.2.1 : ℂ) * (χ q.2.2 : ℂ)
          * Complex.exp (Complex.I * ((inner ℝ p (q.2.1 - q.2.2) : ℝ) : ℂ)))
        * ((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
            (Work.UBBInputs8.boxQInd volA A i Φ)
              (Submission.BoseGases.ins2 i j' q.2.1 q.2.2 q.1) : ℝ) : ℂ)) :=
    hkernm.mul hQQm
  -- the bound for `H`
  have hHb : ∃ C : ℝ, 0 ≤ C ∧ ∀ r2 ∈ Submission.BoseGases.abox N ℓ,
      ∀ y ∈ A, ∀ z ∈ A,
      ‖(χ y : ℂ) * (χ z : ℂ)
          * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ))
        * ((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
            (Work.UBBInputs8.boxQInd volA A i Φ)
              (Submission.BoseGases.ins2 i j' y z r2) : ℝ) : ℂ)‖
        ≤ C := by
    refine ⟨(max Cχ 0) ^ 2 * (4 * B), by positivity, fun r2 hr2 y hy z hz => ?_⟩
    have h1 : ‖(χ y : ℂ) * (χ z : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ))‖ ≤ (max Cχ 0) ^ 2 := by
      rw [Complex.norm_mul, Complex.norm_mul]
      have hexp : ‖Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      rw [hexp, mul_one]
      have hy' : ‖(χ y : ℂ)‖ ≤ max Cχ 0 := by simpa using hCχb y
      have hz' : ‖(χ z : ℂ)‖ ≤ max Cχ 0 := by simpa using hCχb z
      calc ‖(χ y : ℂ)‖ * ‖(χ z : ℂ)‖ ≤ (max Cχ 0) * (max Cχ 0) :=
            mul_le_mul hy' hz' (norm_nonneg _) hCχ0
        _ = (max Cχ 0) ^ 2 := by ring
    have h2 : ‖((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
        (Work.UBBInputs8.boxQInd volA A i Φ)
          (Submission.BoseGases.ins2 i j' y z r2) : ℝ) : ℂ)‖ ≤ 4 * B := by
      rw [norm_ofReal_eq_abs]
      exact hQbound y z hy hz r2 hr2
    calc ‖((χ y : ℂ) * (χ z : ℂ)
          * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ)))
        * ((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
            (Work.UBBInputs8.boxQInd volA A i Φ)
              (Submission.BoseGases.ins2 i j' y z r2) : ℝ) : ℂ)‖
        = ‖(χ y : ℂ) * (χ z : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ))‖
          * ‖((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
              (Work.UBBInputs8.boxQInd volA A i Φ)
                (Submission.BoseGases.ins2 i j' y z r2) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_mul]
      _ ≤ (max Cχ 0) ^ 2 * (4 * B) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  -- measurability of the slot mean
  have hMm : Measurable (boxPairMean A Φ i j') := by
    have hmap : Measurable (fun q : (E3 × Submission.BoseGases.X N) × E3 =>
        Submission.BoseGases.ins2 i j' q.1.1 q.2 q.1.2) := by
      unfold Submission.BoseGases.ins2
      exact (Submission.BoseGases.kcInsN (N + 1) i).measurable.comp
        (Measurable.prodMk measurable_fst.fst
          ((Submission.BoseGases.kcInsN N j').measurable.comp
            (Measurable.prodMk measurable_snd measurable_fst.snd)))
    have hsm : StronglyMeasurable (Function.uncurry fun (q : E3 × Submission.BoseGases.X N)
        (w : E3) => ((Φ (Submission.BoseGases.ins2 i j' q.1 w q.2) : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp hΦc).stronglyMeasurable.comp_measurable hmap
    have h1 := StronglyMeasurable.integral_prod_right
      (ν := (MeasureTheory.volume : Measure E3).restrict A) hsm
    have h2 := StronglyMeasurable.integral_prod_left'
      (μ := (MeasureTheory.volume : Measure E3).restrict A) h1
    have h3 : boxPairMean A Φ i j' = fun r2 : Submission.BoseGases.X N =>
        ∫ y in A, ∫ z in A, ((Φ (Submission.BoseGases.ins2 i j' y z r2) : ℝ) : ℂ) := rfl
    rw [h3]
    exact h2.measurable
  -- the bound for the slot mean
  have hMb : ∃ C : ℝ, 0 ≤ C ∧ ∀ r2 ∈ Submission.BoseGases.abox N ℓ,
      ‖boxPairMean A Φ i j' r2‖ ≤ C := by
    have hfin : (MeasureTheory.volume : Measure E3) A < ⊤ :=
      lt_of_le_of_lt (MeasureTheory.measure_mono hAc)
        (by rw [Submission.BoseGases.acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_lt_top)
    refine ⟨volA ^ 2 * B, by positivity, fun r2 hr2 => ?_⟩
    have hinnerbound : ∀ y ∈ A, ‖∫ z in A,
        ((Φ (Submission.BoseGases.ins2 i j' y z r2) : ℝ) : ℂ)‖ ≤ B * volA := by
      intro y hy
      have h2 : ‖∫ z in A, ((Φ (Submission.BoseGases.ins2 i j' y z r2) : ℝ) : ℂ)‖
          ≤ B * (MeasureTheory.volume : Measure E3).real A := by
        refine norm_setIntegral_le_of_norm_le_const hfin (fun z hz => ?_)
        rw [norm_ofReal_eq_abs, ← Real.norm_eq_abs]
        exact hB _ (Work.BoseFixB1S.Q0C.ins2_mem_abox hAc i j' hy hz hr2)
      rw [MeasureTheory.Measure.real, ← hvolA] at h2
      exact h2
    have houterbound : ‖∫ y in A, ∫ z in A,
        ((Φ (Submission.BoseGases.ins2 i j' y z r2) : ℝ) : ℂ)‖ ≤ (B * volA) * volA := by
      have h2 := norm_setIntegral_le_of_norm_le_const hfin (fun y hy => hinnerbound y hy)
      rw [MeasureTheory.Measure.real, ← hvolA] at h2
      exact h2
    have hcomm : (B * volA) * volA = volA ^ 2 * B := by ring
    calc ‖boxPairMean A Φ i j' r2‖
        = ‖∫ y in A, ∫ z in A, ((Φ (Submission.BoseGases.ins2 i j' y z r2) : ℝ) : ℂ)‖ := rfl
      _ ≤ (B * volA) * volA := houterbound
      _ = volA ^ 2 * B := hcomm
  -- the triple Fubini
  have hswap := Work.BoseFixB1.C2Pieces.box_pair_slotMean_swap (N := N) (ℓ := ℓ) (A := A) hA hℓ hAc
    (H := fun r2 y z => (χ y : ℂ) * (χ z : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ))
        * ((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
            (Work.UBBInputs8.boxQInd volA A i Φ)
              (Submission.BoseGases.ins2 i j' y z r2) : ℝ) : ℂ))
    (M := boxPairMean A Φ i j') hHm hHb hMm hMb
  -- measurability of the projected factors in `r2`
  have hins2m : ∀ y z : E3, Measurable (fun r2 : Submission.BoseGases.X N =>
      Submission.BoseGases.ins2 i j' y z r2) := by
    intro y z
    unfold Submission.BoseGases.ins2
    exact (Submission.BoseGases.kcInsN (N + 1) i).measurable.comp
      (Measurable.prodMk measurable_const
        ((Submission.BoseGases.kcInsN N j').measurable.comp
          (Measurable.prodMk measurable_const measurable_id)))
  have hPIndm : ∀ {M : ℕ} (j : Fin M) {Ψ : Submission.BoseGases.X M → ℝ}, Measurable Ψ →
      Measurable (Work.UBBInputs8.boxPInd volA A j Ψ) := by
    intro M j Ψ hΨ
    have h1 : Measurable (fun x : Submission.BoseGases.X M =>
        A.indicator (fun _ => (1 : ℝ)) (x j)) :=
      (measurable_const.indicator hA).comp (measurable_pi_apply j)
    have h2 : Measurable (fun x : Submission.BoseGases.X M =>
        ∫ u in A, Ψ (Function.update x j u)) := by
      have hsm : StronglyMeasurable (Function.uncurry
          fun (x : Submission.BoseGases.X M) (u : E3) => Ψ (Function.update x j u)) :=
        hΨ.stronglyMeasurable.comp_measurable (by fun_prop)
      exact (hsm.integral_prod_right
        (ν := (MeasureTheory.volume : Measure E3).restrict A)).measurable
    unfold Work.UBBInputs8.boxPInd
    exact (measurable_const.mul h2).mul h1
  -- the pointwise inner identity
  have hinner_pt : ∀ y ∈ A, ∀ z ∈ A,
      (∫ r2 in Submission.BoseGases.abox N ℓ,
          ((χ y : ℂ) * (χ z : ℂ)
              * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ))
            * ((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
                (Work.UBBInputs8.boxQInd volA A i Φ)
                  (Submission.BoseGases.ins2 i j' y z r2) : ℝ) : ℂ))
            * boxPairMean A Φ i j' r2)
        = ((volA ^ 2 : ℝ) : ℂ) * (((χ y : ℂ) * (χ z : ℂ)
              * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ)))
            * ((boxPairFibreFun volA ℓ A Φ i (i.succAbove j') y z : ℝ) : ℂ)) := by
    intro y hy z hz
    have hfinab : (MeasureTheory.volume : Measure (Submission.BoseGases.X N))
        (Submission.BoseGases.abox N ℓ) < ⊤ := Submission.BoseGases.abox_lt_top N ℓ hℓ.le
    have hfinA : (MeasureTheory.volume : Measure E3) A < ⊤ :=
      lt_of_le_of_lt (MeasureTheory.measure_mono hAc)
        (by rw [Submission.BoseGases.acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_lt_top)
    -- the slot mean identity
    have hPM : ∀ r2 ∈ Submission.BoseGases.abox N ℓ,
        boxPairMean A Φ i j' r2
          = ((volA ^ 2 : ℝ) : ℂ) * ((Work.UBBInputs8.boxPInd volA A i
              (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ))
                (Submission.BoseGases.ins2 i j' y z r2) : ℂ) :=
      fun r2 hr2 => boxPairMean_eq_volA_sq_mul_pairInd hA hℓ hAc hvolA hvolpos hΦc
        i j' hr2 hy hz
    -- bound for the `P`-factor
    have hPPval : ∀ r2 : Submission.BoseGases.X N,
        (Work.UBBInputs8.boxPInd volA A i
            (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ))
          (Submission.BoseGases.ins2 i j' y z r2)
        = (volA ^ 2)⁻¹ * (∫ u in A, ∫ w in A, Φ (Submission.BoseGases.ins2 i j' u w r2)) := by
      intro r2
      have h := pairInd_eq_volA_sq_mul hℓ hAc hvolpos hΦc i j' r2 hy hz
      rw [h]
      have hne : volA ^ 2 ≠ 0 := by positivity
      field_simp
    have hJb : ∀ r2 ∈ Submission.BoseGases.abox N ℓ,
        ‖∫ u in A, ∫ w in A, Φ (Submission.BoseGases.ins2 i j' u w r2)‖ ≤ B * volA * volA := by
      intro r2 hr2
      have h2 : ‖∫ u in A, ∫ w in A, Φ (Submission.BoseGases.ins2 i j' u w r2)‖
          ≤ (B * (MeasureTheory.volume : Measure E3).real A)
            * (MeasureTheory.volume : Measure E3).real A :=
        norm_setIntegral_le_of_norm_le_const hfinA (fun u hu =>
          norm_setIntegral_le_of_norm_le_const hfinA (fun w hw =>
            hB _ (Work.BoseFixB1S.Q0C.ins2_mem_abox hAc i j' hu hw hr2)))
      rw [MeasureTheory.Measure.real, ← hvolA] at h2
      exact le_trans h2 (le_of_eq (by ring))
    have hPPb : ∀ r2 ∈ Submission.BoseGases.abox N ℓ,
        |(Work.UBBInputs8.boxPInd volA A i
            (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ))
          (Submission.BoseGases.ins2 i j' y z r2)| ≤ B := by
      intro r2 hr2
      rw [hPPval r2, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (volA ^ 2)⁻¹)]
      have hJabs : |∫ u in A, ∫ w in A, Φ (Submission.BoseGases.ins2 i j' u w r2)|
          ≤ B * volA * volA := by
        simpa only [Real.norm_eq_abs] using hJb r2 hr2
      calc (volA ^ 2)⁻¹ * |∫ u in A, ∫ w in A, Φ (Submission.BoseGases.ins2 i j' u w r2)|
          ≤ (volA ^ 2)⁻¹ * (B * volA * volA) :=
            mul_le_mul_of_nonneg_left hJabs (by positivity)
        _ = B := by
            have hne : volA ^ 2 ≠ 0 := by positivity
            field_simp
    have hQQb : ∀ r2 ∈ Submission.BoseGases.abox N ℓ,
        |(Work.UBBInputs8.boxQInd volA A (i.succAbove j')
            (Work.UBBInputs8.boxQInd volA A i Φ))
          (Submission.BoseGases.ins2 i j' y z r2)| ≤ 4 * B :=
      fun r2 hr2 => hQbound y z hy hz r2 hr2
    have hQQm : Measurable (fun r2 : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd volA A (i.succAbove j')
            (Work.UBBInputs8.boxQInd volA A i Φ))
          (Submission.BoseGases.ins2 i j' y z r2)) :=
      (Work.SlotWord.measurable_boxQInd volA A hA (i.succAbove j')
        (Work.SlotWord.measurable_boxQInd volA A hA i hΦc.measurable)).comp (hins2m y z)
    have hPPm : Measurable (fun r2 : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A i
            (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ))
          (Submission.BoseGases.ins2 i j' y z r2)) :=
      (hPIndm i (hPIndm (i.succAbove j') hΦc.measurable)).comp (hins2m y z)
    -- substitute the slot mean
    rw [integral_congr_ae ((MeasureTheory.ae_restrict_mem
        (Submission.BoseGases.abox_measurable N ℓ)).mono
      (fun r2 hr2 => by rw [hPM r2 hr2]))]
    rw [show (∫ r2 in Submission.BoseGases.abox N ℓ,
          ((χ y : ℂ) * (χ z : ℂ)
              * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ))
            * ((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
                (Work.UBBInputs8.boxQInd volA A i Φ)
                  (Submission.BoseGases.ins2 i j' y z r2) : ℝ) : ℂ))
            * (((volA ^ 2 : ℝ) : ℂ) * ((Work.UBBInputs8.boxPInd volA A i
                (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ))
                  (Submission.BoseGases.ins2 i j' y z r2) : ℂ)))
        = ((volA ^ 2 : ℝ) : ℂ) * ∫ r2 in Submission.BoseGases.abox N ℓ,
            ((χ y : ℂ) * (χ z : ℂ)
                * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ)))
              * (((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
                    (Work.UBBInputs8.boxQInd volA A i Φ)
                      (Submission.BoseGases.ins2 i j' y z r2) : ℝ) : ℂ)
                * ((Work.UBBInputs8.boxPInd volA A i
                    (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ))
                      (Submission.BoseGases.ins2 i j' y z r2) : ℂ)) from by
      rw [← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun r2 => ?_)
      ring]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    -- complexification of the `r2`-integral of `QQ·PP`
    have hprod : (∫ r2 in Submission.BoseGases.abox N ℓ,
          ((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
              (Work.UBBInputs8.boxQInd volA A i Φ)
                (Submission.BoseGases.ins2 i j' y z r2) : ℝ) : ℂ)
            * ((Work.UBBInputs8.boxPInd volA A i
                (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ))
                  (Submission.BoseGases.ins2 i j' y z r2) : ℂ))
        = ((∫ r2 in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd volA A (i.succAbove j')
              (Work.UBBInputs8.boxQInd volA A i Φ)
                (Submission.BoseGases.ins2 i j' y z r2))
            * (Work.UBBInputs8.boxPInd volA A i
                (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ))
                  (Submission.BoseGases.ins2 i j' y z r2) : ℝ) : ℂ) := by
      rw [show (∫ r2 in Submission.BoseGases.abox N ℓ,
            ((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
                (Work.UBBInputs8.boxQInd volA A i Φ)
                  (Submission.BoseGases.ins2 i j' y z r2) : ℝ) : ℂ)
              * ((Work.UBBInputs8.boxPInd volA A i
                  (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ))
                    (Submission.BoseGases.ins2 i j' y z r2) : ℂ))
          = ∫ r2 in Submission.BoseGases.abox N ℓ,
              (((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
                  (Work.UBBInputs8.boxQInd volA A i Φ)
                    (Submission.BoseGases.ins2 i j' y z r2))
                * (Work.UBBInputs8.boxPInd volA A i
                    (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ))
                      (Submission.BoseGases.ins2 i j' y z r2) : ℝ) : ℂ) from by
        refine integral_congr_ae (Filter.Eventually.of_forall fun r2 => ?_)
        simp only []
        rw [← Complex.ofReal_mul]]
      refine Complex.ofRealCLM.integral_comp_comm
        (φ := fun r2 : Submission.BoseGases.X N =>
          (Work.UBBInputs8.boxQInd volA A (i.succAbove j')
            (Work.UBBInputs8.boxQInd volA A i Φ)
              (Submission.BoseGases.ins2 i j' y z r2))
          * (Work.UBBInputs8.boxPInd volA A i
              (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ))
                (Submission.BoseGases.ins2 i j' y z r2)) ?_
      refine IntegrableOn.of_bound hfinab (hQQm.mul hPPm).aestronglyMeasurable (4 * B * B) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (Submission.BoseGases.abox_measurable N ℓ)] with r2 hr2
      rw [Real.norm_eq_abs, abs_mul]
      calc |(Work.UBBInputs8.boxQInd volA A (i.succAbove j')
              (Work.UBBInputs8.boxQInd volA A i Φ))
            (Submission.BoseGases.ins2 i j' y z r2)|
            * |(Work.UBBInputs8.boxPInd volA A i
              (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ))
                (Submission.BoseGases.ins2 i j' y z r2)|
          ≤ (4 * B) * B := mul_le_mul (hQQb r2 hr2) (hPPb r2 hr2) (abs_nonneg _) (by positivity)
        _ = 4 * B * B := by ring
    rw [hprod]
    rw [boxPairFibreFun_succAbove]
    refine congrArg (fun t : ℂ => ((χ y : ℂ) * (χ z : ℂ)
      * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ))) * t) ?_
    rw [show (∫ r2 in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd volA A (i.succAbove j')
            (Work.UBBInputs8.boxQInd volA A i Φ)
              (Submission.BoseGases.ins2 i j' y z r2))
          * (Work.UBBInputs8.boxPInd volA A i
              (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ))
                (Submission.BoseGases.ins2 i j' y z r2))
        = ∫ r2 in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i
              (Work.UBBInputs8.boxPInd volA A (i.succAbove j') Φ))
                (Submission.BoseGases.ins2 i j' y z r2)
          * (Work.UBBInputs8.boxQInd volA A (i.succAbove j')
              (Work.UBBInputs8.boxQInd volA A i Φ))
                (Submission.BoseGases.ins2 i j' y z r2) from by
      refine integral_congr_ae (Filter.Eventually.of_forall fun r2 => ?_)
      simp only []
      ring]

  -- assemble
  have hslot : ∀ r2 : Submission.BoseGases.X N,
      boxPairSlot A Φ (boxWinModeC volA A χ (-p)) (boxWinModeC volA A χ p) i j' r2
        = ∫ y in A, ∫ z in A,
            ((χ y : ℂ) * (χ z : ℂ)
              * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ)))
              * ((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
                  (Work.UBBInputs8.boxQInd volA A i Φ))
                    (Submission.BoseGases.ins2 i j' y z r2) : ℂ) :=
    fun r2 => Work.BoseFixB1.BoxPairIntGenC2.boxPairSlot_winModeC2 hA hℓ hAc hvolA hvolpos
      hχc hχs hχsupp hΦ i j' r2 p
  have hstep1 : (∫ r2 in Submission.BoseGases.abox N ℓ,
        boxPairSlot A Φ (boxWinModeC volA A χ (-p)) (boxWinModeC volA A χ p) i j' r2
          * boxPairMean A Φ i j' r2)
      = ∫ r2 in Submission.BoseGases.abox N ℓ,
          (∫ y in A, ∫ z in A,
              ((χ y : ℂ) * (χ z : ℂ)
                * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ)))
                * ((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
                    (Work.UBBInputs8.boxQInd volA A i Φ))
                      (Submission.BoseGases.ins2 i j' y z r2) : ℂ))
            * boxPairMean A Φ i j' r2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun r2 => ?_)
    simp only []
    rw [hslot r2]
  rw [hstep1, hswap]
  have hstep2 : (∫ y in A, ∫ z in A, ∫ r2 in Submission.BoseGases.abox N ℓ,
        ((χ y : ℂ) * (χ z : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ))
          * ((Work.UBBInputs8.boxQInd volA A (i.succAbove j')
              (Work.UBBInputs8.boxQInd volA A i Φ))
                (Submission.BoseGases.ins2 i j' y z r2) : ℂ))
          * boxPairMean A Φ i j' r2)
      = ∫ y in A, ∫ z in A, ((volA ^ 2 : ℝ) : ℂ) * (((χ y : ℂ) * (χ z : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ)))
          * ((boxPairFibreFun volA ℓ A Φ i (i.succAbove j') y z : ℝ) : ℂ)) := by
    refine integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hA] with y hy
    refine integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hA] with z hz
    exact hinner_pt y hy z hz
  rw [hstep2]
  simp_rw [MeasureTheory.integral_const_mul]
  push_cast
  have hne : (volA : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hvolpos)
  field_simp
theorem boxC2SumC {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦ : Continuous Φ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    (∫ x in Submission.BoseGases.abox (N + 2) ℓ, (Φ x : ℂ)
        * Work.BoseFixB1.boxTauDagGenC volA A (Work.BoseFixB1.boxWinModeC volA A χ (-p))
          (Work.BoseFixB1.boxTauDagGenC volA A (Work.BoseFixB1.boxWinModeC volA A χ p)
            (fun y => (Φ y : ℂ))) x)
      = (volA : ℂ) * Work.BoseFixB1.boxPairDensFourier volA ℓ A χ Φ p := by
  have hΦc : Continuous Φ := hΦ
  obtain ⟨Cχ, hCχ⟩ := hχs.exists_bound_of_continuous hχc
  have hCχ0 : 0 ≤ max Cχ 0 := le_max_right _ _
  have hCχb : ∀ z : EuclideanSpace ℝ (Fin 3), ‖χ z‖ ≤ max Cχ 0 :=
    fun z => le_trans (hCχ z) (le_max_left _ _)
  -- the τ-pair peel
  have hpeel := Work.BoseFixB1.BoxPairIntGenC2.boxTauDagGenC_pairReduceC2 (N := N) (ℓ := ℓ) (volA := volA) (A := A)
    hA hℓ hAc hvolA hvolpos hΦc
    (boxWinModeC volA A χ (-p)) (boxWinModeC volA A χ p)
    (boxWinModeC_measurable hA hχc (-p))
    (boxWinModeC_measurable hA hχc p)
    (boxWinModeC_norm_le hℓ hAc hvolA hvolpos hCχ0 hCχb (-p))
    (boxWinModeC_norm_le hℓ hAc hvolA hvolpos hCχ0 hCχb p)
    (fun z hz => boxWinModeC_eq_zero_of_notMem hz)
    (fun z hz => boxWinModeC_eq_zero_of_notMem hz)
    (boxWinModeC_setIntegral_eq_zero hA hℓ hAc hvolA hvolpos hχc hχs p)
  rw [hpeel]
  -- the per-pair assembly
  have hpair : ∀ i : Fin (N + 2), ∀ j' : Fin (N + 1),
      (volA⁻¹ : ℂ) * (∫ r2 in Submission.BoseGases.abox N ℓ,
          boxPairSlot A Φ (boxWinModeC volA A χ (-p)) (boxWinModeC volA A χ p) i j' r2
            * boxPairMean A Φ i j' r2)
        = (volA : ℂ) * ∫ y in A, ∫ z in A,
            (χ y : ℂ) * (χ z : ℂ)
              * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ))
              * ((boxPairFibreFun volA ℓ A Φ i (i.succAbove j') y z : ℝ) : ℂ) :=
    fun i j' => boxPair_perPairC_weak hA hℓ hAc hvolA hvolpos hχc hχs hχsupp hΦ i j' p
  -- the reindexing of the pair sum
  have hre : (∑ q ∈ Submission.BoseGases.pairSet (N + 2),
        ∫ y in A, ∫ z in A,
          (χ y : ℂ) * (χ z : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ))
            * ((boxPairFibreFun volA ℓ A Φ q.1 q.2 y z : ℝ) : ℂ))
      = ∑ i : Fin (N + 2), ∑ j' : Fin (N + 1),
          ∫ y in A, ∫ z in A,
            (χ y : ℂ) * (χ z : ℂ)
              * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ))
              * ((boxPairFibreFun volA ℓ A Φ i (i.succAbove j') y z : ℝ) : ℂ) := by
    rw [Submission.BoseGases.pairSet]
    exact Commons.Algebra.BigOperators.sum_pairSet_eq_succAbove (n := N + 1)
      (F := fun a b : Fin (N + 2) => ∫ y in A, ∫ z in A,
          (χ y : ℂ) * (χ z : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ p (y - z) : ℝ) : ℂ))
            * ((boxPairFibreFun volA ℓ A Φ a b y z : ℝ) : ℂ))
  unfold boxPairDensFourier
  rw [hre]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j' _ => ?_
  exact hpair i j'

end Work.BoseFixB1S
