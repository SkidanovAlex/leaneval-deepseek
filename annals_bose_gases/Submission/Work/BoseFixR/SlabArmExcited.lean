import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.perBoxCrudeLower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/SlabArmExcited` — the excited arm of the sliding per-box bound

This is Step 2 (= "arm A") of the dichotomy recorded in
`Submission/Work/BoseFixR/PerBoxWordCrudeHigh.lean`: for a state whose *excited* count of the
sliding box dominates its `B(u)`-occupancy count, the sliding word `sbWord` is bounded below by
`−(C (μ²(a v)·χ_M(u) + μ(a v)))·‖Φ‖²`.

## The mathematics (and why the constants are free)

Write `ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`, `M = (paramsAt μ (a v)).M`,
`B = dlBox ℓ d u`, `A = a v`, `n₊ = cnPlusBoxInd ℓ B (boxMass ℓ d u) Φ` and

`cnt = Σ_i ∫_{abox n ℓ} Φ² 1_B(x_i)`.

The three inputs are all **proved** in the corpus:

* **the definitional gap payment** (`Work.BoseFixB1.perBoxF_pieces.sbKin_ge_mu_av_cnPlus`):
  `sbKin = tbGapCoeff (ℓd) ε_T · n₊ + tBwordKinInd` with `tBwordKinInd ≥ 0`, and FS's régime
  `2(1+π⁻²)(ℓd c'√(μA))² ≤ ε_T` holds for *every* fixed `c' ≥ 0` once `μA³` is small
  (`Work.BoseFixB1.perBoxF_thick.gapRegime_of_adm`), since the gap coefficient grows like
  `t^{-13/1292}/(2(1+π⁻²))`. Hence `sbKin ≥ c'² μ A · n₊` for arbitrary fixed `c'`;
* **the linear fibre bound** (`Work.BoseFixB1.perBoxF_localised.fibSum_le`, from
  `Work.BoseFixB1B.fibre_chiB_le`): `fibSum ≤ K_av · A · Σ_i∫Φ²χ_{B(u)}(x_i)` in the FS régime
  `R ≤ ℓd/16`, `R ≤ ℓ χ_{R0}` (`Work.BoseFixB1.regime_sideAt_ge`), and the pair term is `≥ 0`
  (`Work.BoseFixB1.perBoxF_localised.pairSum_nonneg`, from `0 ≤ v`);
* **the support of the cutoff** (`Work.BoseFixB1B.chiSmallB_le_const_mul_indicator`): the
  smooth cutoff is dominated by its own box indicator, `χ_{B(u)} ≤ C_χ · 1_B`, whence
  `Σ_i∫Φ²χ_{B(u)}(x_i) ≤ C_χ · cnt` (`chiSum_le_countIntegral` below).

With `cnt ≤ 2 n₊` (the arm-A hypothesis) the two loss terms cancel against the gap payment:

  `sbWord ≥ c'² μA n₊ − μ K_av A C_χ cnt ≥ μA n₊ (c'² − 2 K_av C_χ) ≥ 0`

once `c'² ≥ 2 K_av C_χ`, which is a *fixed* condition on the free constant `c'` (the threshold
`ε₀` shrinks as `c'` grows).  In particular the conclusion holds with `C = 0`.

The `crudeThreshold ≤ occChi` hypothesis of the statement is the *other* arm's hypothesis and is
not needed here; it is kept because the statement is the requested interface.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixR

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The cutoff count versus the box-indicator count -/

/-- **The `χ_{B(u)}`-weighted count is dominated by the box-indicator count.**  Since the smooth
cutoff vanishes off `B(u)` and is bounded there by `chiSupAbs·chiSmallDecay M`
(`Work.BoseFixB1B.chiSmallB_le_const_mul_indicator`),

`Σ_i ∫ Φ² χ_{B(u)}(x_i) ≤ (chiSupAbs·chiSmallDecay M) · Σ_i ∫ Φ² 1_{B(u)}(x_i)`. -/
theorem chiSum_le_countIntegral {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) :
    Work.BoseFixB1.chiSum M ℓ d u Φ
      ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) *
        (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)) := by
  classical
  set Cs : ℝ := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M with hCs
  have hCs0 : 0 ≤ Cs := by
    rw [hCs]
    exact mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg M)
  set B : Set (EuclideanSpace ℝ (Fin 3)) := Submission.BoseGases.dlBox ℓ d u with hB
  have hBmeas : MeasurableSet B := by
    rw [hB]
    exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  -- the pointwise domination of the cutoff by its box indicator
  have hpt : ∀ z : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.chiSmallB M ℓ d u z ≤ Cs * B.indicator (fun _ => (1 : ℝ)) z := by
    intro z
    by_cases hz : z ∈ B
    · rw [Set.indicator_of_mem hz, mul_one, hCs]
      exact Work.BoseFixB1.chiSmallB_le_Cs (M := M) hM u z
    · rw [Set.indicator_of_notMem hz, mul_zero]
      rw [hB] at hz
      by_contra hcon
      exact hz (Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd
        (ne_of_gt (lt_of_not_ge hcon)))
  -- integrability of the pieces
  have hΦ2 : IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
      (Submission.BoseGases.abox n ℓ) :=
    Submission.BoseGases.integrableOn_abox_of_continuous hℓ (hΦc.pow 2)
  have hfi : ∀ i : Fin n, IntegrableOn (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * B.indicator (fun _ => (1 : ℝ)) (x i)) (Submission.BoseGases.abox n ℓ) := by
    intro i
    have hmeas : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
        (Φ x) ^ 2 * B.indicator (fun _ => (1 : ℝ)) (x i))
        ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
      ((hΦc.pow 2).aestronglyMeasurable).mul
        ((((measurable_const : Measurable (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ))).indicator
            hBmeas).comp (continuous_apply i).measurable).aestronglyMeasurable)
    refine Integrable.mono' hΦ2 hmeas (Filter.Eventually.of_forall fun x => ?_)
    have hind : |B.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
      by_cases hx : x i ∈ B
      · rw [Set.indicator_of_mem hx]; norm_num
      · rw [Set.indicator_of_notMem hx]; norm_num
    calc ‖(Φ x) ^ 2 * B.indicator (fun _ => (1 : ℝ)) (x i)‖
        = (Φ x) ^ 2 * |B.indicator (fun _ => (1 : ℝ)) (x i)| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
      _ ≤ (Φ x) ^ 2 * 1 := mul_le_mul_of_nonneg_left hind (sq_nonneg _)
      _ = (Φ x) ^ 2 := by ring
  have hbig : IntegrableOn (fun x : Submission.BoseGases.X n =>
      Cs * ((Φ x) ^ 2 * ∑ i : Fin n, B.indicator (fun _ => (1 : ℝ)) (x i)))
      (Submission.BoseGases.abox n ℓ) := by
    have heq : (fun x : Submission.BoseGases.X n =>
        Cs * ((Φ x) ^ 2 * ∑ i : Fin n, B.indicator (fun _ => (1 : ℝ)) (x i)))
        = fun x : Submission.BoseGases.X n => ∑ i : Fin n,
            Cs * ((Φ x) ^ 2 * B.indicator (fun _ => (1 : ℝ)) (x i)) := by
      funext x
      rw [Finset.mul_sum, Finset.mul_sum]
    rw [heq]
    exact MeasureTheory.integrable_finsetSum _ (fun i _ => (hfi i).const_mul Cs)
  -- the monotonicity of the integral
  have hmono : Work.BoseFixB1.chiSum M ℓ d u Φ ≤
      ∫ x in Submission.BoseGases.abox n ℓ,
        Cs * ((Φ x) ^ 2 * ∑ i : Fin n, B.indicator (fun _ => (1 : ℝ)) (x i)) := by
    rw [Work.BoseFixB1.chiSum]
    refine integral_mono_of_nonneg ?_ hbig ?_
    · filter_upwards with x
      exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ =>
        Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u (x i))
    · filter_upwards with x
      have hs : (∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
          ≤ Cs * ∑ i : Fin n, B.indicator (fun _ => (1 : ℝ)) (x i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => hpt (x i)
      calc (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)
          ≤ (Φ x) ^ 2 * (Cs * ∑ i : Fin n, B.indicator (fun _ => (1 : ℝ)) (x i)) :=
            mul_le_mul_of_nonneg_left hs (sq_nonneg _)
        _ = Cs * ((Φ x) ^ 2 * ∑ i : Fin n, B.indicator (fun _ => (1 : ℝ)) (x i)) := by ring
  rw [MeasureTheory.integral_const_mul] at hmono
  have hsum_eq : (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * ∑ i : Fin n, B.indicator (fun _ => (1 : ℝ)) (x i))
      = ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * B.indicator (fun _ => (1 : ℝ)) (x i) := by
    have h1 : (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        ∑ i : Fin n, B.indicator (fun _ => (1 : ℝ)) (x i))
        = fun x : Submission.BoseGases.X n => ∑ i : Fin n,
            (Φ x) ^ 2 * B.indicator (fun _ => (1 : ℝ)) (x i) := by
      funext x
      rw [Finset.mul_sum]
    rw [h1]
    exact MeasureTheory.integral_finsetSum _ (fun i _ => hfi i)
  rw [hsum_eq] at hmono
  exact hmono

/-! ## 2. The excited arm -/

theorem SlabArmExcited {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ K C : ℝ, 0 < ε₀ ∧ 0 < K ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          (Work.BoseFixR.crudeThreshold v K μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                (Φ : Submission.BoseGases.X n → ℝ)) →
          Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Φ : Submission.BoseGases.X n → ℝ)
            ≥ (1 / 2 : ℝ) * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
                  (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator
                    (fun _ => (1 : ℝ)) (x i)) →
          -(C * (μ ^ 2 * _root_.BoseGases.a v
                * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              + μ * _root_.BoseGases.a v))
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  classical
  -- ### the constants (all `v`-dependent but `μ`-independent)
  let Cs : ℝ := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue
  let Kav : ℝ := 16 * π * Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue
      / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue
  let csq : ℝ := 2 * Kav * Cs + 1
  let c' : ℝ := Real.sqrt csq
  have hCs0 : 0 ≤ Cs := by
    show (0 : ℝ) ≤ Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue
    exact mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg Work.BoseBox.mValue)
  have hKav0 : 0 ≤ Kav := by
    show (0 : ℝ) ≤ 16 * π * Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue
      / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue
    refine div_nonneg ?_ (le_of_lt (Work.SmallBoxSliding.smallConvLower_pos Work.BoseBox.mValue))
    exact mul_nonneg (mul_nonneg (by positivity)
      Submission.BoseGases.chiSupAbs_nonneg)
      (Submission.BoseGases.chiSmallDecay_nonneg Work.BoseBox.mValue)
  have hcsq0 : 0 < csq := by
    show (0 : ℝ) < 2 * Kav * Cs + 1
    have h0 : 0 ≤ 2 * Kav * Cs := mul_nonneg (mul_nonneg (by norm_num) hKav0) hCs0
    linarith
  have hc'0 : 0 ≤ c' := by
    show (0 : ℝ) ≤ Real.sqrt csq
    exact Real.sqrt_nonneg _
  have hc'2 : c' ^ 2 = csq := by
    show Real.sqrt csq ^ 2 = csq
    exact Real.sq_sqrt hcsq0.le
  have hkey : 2 * Kav * Cs ≤ c' ^ 2 := by
    rw [hc'2]
    show 2 * Kav * Cs ≤ 2 * Kav * Cs + 1
    linarith
  obtain ⟨εg, hεg, hgreg⟩ := Work.BoseFixB1.gapRegime_of_adm (v := v) hav (c' := c') hc'0
  obtain ⟨εr, hεr, hrreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min εg εr, 1, 0, lt_min hεg hεr, one_pos, le_refl 0, ?_⟩
  intro μ hAdm n Φ u hthr hexc
  -- ### the local notation
  let nps : ℝ := Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Φ : Submission.BoseGases.X n → ℝ)
  let cnt : ℝ := ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator
          (fun _ => (1 : ℝ)) (x i)
  let fib : ℝ := Work.BoseFixB1.fibSum h Work.BoseBox.mValue
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      (Φ : Submission.BoseGases.X n → ℝ)
  let pair : ℝ := Work.BoseFixB1.pairSum v Work.BoseBox.mValue
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      (Φ : Submission.BoseGases.X n → ℝ)
  let sbk : ℝ := Work.BoseFixB1.sbKin (v := v) μ Work.BoseBox.mValue u
      (Φ : Submission.BoseGases.X n → ℝ)
  -- ### the basic facts about the admissible point
  have hAdmg : Work.BoseBoxFix.Adm v εg μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmr : Work.BoseBoxFix.Adm v εr μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  obtain ⟨hR16, hRχ⟩ := hrreg μ hAdm.1 hAdmr.2.1
  have hμ : 0 < μ := hAdm.1
  have hA0 : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
    Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ Work.BoseBox.mValue := by norm_num [Work.BoseBox.mValue]
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  -- ### the arm hypothesis, in the direction used
  have hexc' : (1 / 2 : ℝ) * cnt ≤ nps := hexc
  have hcnt2 : cnt ≤ 2 * nps := by linarith
  -- ### the definitional excited-count payment
  have hgap := Work.BoseFixB1.sbKin_ge_mu_av_cnPlus (v := v) (μ := μ) (c' := c')
    (M := Work.BoseBox.mValue) (u := u) (Φ := (Φ : Submission.BoseGases.X n → ℝ))
    hA0 hμ.le hc'0 (mul_pos hd hℓ) (Work.BoseFixB1.adm_eT_pos hAdm)
    (hgreg μ hAdmg) (Work.BoseFixB1.tBwordKinInd_nonneg _)
  have h1 : c' ^ 2 * μ * _root_.BoseGases.a v * nps ≤ sbk := hgap
  -- ### the fibre loss
  have hfib := Work.BoseFixB1.fibSum_le (v := v) (h := h) (R0 := R) hv hvrad hR hv_supp
    (M := Work.BoseBox.mValue) hM1 hℓ hd hR16 hRχ u hΦc
  have hchi := chiSum_le_countIntegral (M := Work.BoseBox.mValue) hM1 hℓ hd u hΦc
  have hfib1 : fib ≤ Kav * _root_.BoseGases.a v * (Cs * cnt) := by
    refine le_trans hfib ?_
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hKav0 hA0)
    exact hchi
  have hfib2 : fib ≤ Kav * _root_.BoseGases.a v * (Cs * (2 * nps)) := by
    refine le_trans hfib1 ?_
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hKav0 hA0)
    exact mul_le_mul_of_nonneg_left hcnt2 hCs0
  have hfibμ : μ * fib ≤ μ * (Kav * _root_.BoseGases.a v * (Cs * (2 * nps))) :=
    mul_le_mul_of_nonneg_left hfib2 hμ.le
  -- ### the pair term
  have hpair : 0 ≤ pair := Work.BoseFixB1.pairSum_nonneg (v := v) hv (M := Work.BoseBox.mValue)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (u := u)
    (Φ := (Φ : Submission.BoseGases.X n → ℝ))
  -- ### the arithmetic of the cancellation
  have h4 : 0 ≤ c' ^ 2 * μ * _root_.BoseGases.a v * nps
      - μ * (Kav * _root_.BoseGases.a v * (Cs * (2 * nps))) := by
    have hnps0 : 0 ≤ nps := by
      show 0 ≤ Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Φ : Submission.BoseGases.X n → ℝ)
      rw [Work.UBBInputs8.cnPlusBoxInd]
      exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
    have hfac : c' ^ 2 * μ * _root_.BoseGases.a v * nps
        - μ * (Kav * _root_.BoseGases.a v * (Cs * (2 * nps)))
        = μ * _root_.BoseGases.a v * nps * (c' ^ 2 - 2 * Kav * Cs) := by ring
    rw [hfac]
    exact mul_nonneg (mul_nonneg (mul_nonneg hμ.le hA0) hnps0) (by linarith [hkey])
  -- ### the split of the sliding word
  have hsb : Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)
      = sbk + (-(μ * fib) + pair) := by
    rw [Work.BoseFixB1.sbWord]
    rw [Work.BoseFixB1.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1 hAdm
      hΦc u hR16 hRχ]
    simp only [Work.BoseFixB1.M_eq_mValue]
    rfl
  -- ### the conclusion, with `C = 0`
  have hzero : -(0 * (μ ^ 2 * _root_.BoseGases.a v
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        + μ * _root_.BoseGases.a v))
      * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) = 0 := by ring
  rw [hzero, hsb]
  linarith [h1, hfibμ, hpair, h4]

end Work.BoseFixR

