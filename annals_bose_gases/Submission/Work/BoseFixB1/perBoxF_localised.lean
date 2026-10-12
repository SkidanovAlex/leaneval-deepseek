import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.perBoxF_cases
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 0. Small facts about FS's parameters -/

/-- `ε_T > 0` at an admissible point (it is `(μ(a v)³)^{23/1292}`). -/
theorem adm_eT_pos {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ μ : ℝ}
    (h : Work.BoseBoxFix.Adm v ε₀ μ) : 0 < (paramsAt μ (a v)).eT := by
  have ht : 0 < μ * (a v) ^ 3 := mul_pos (adm_mu_pos h) (pow_pos (adm_a_pos h) 3)
  rw [paramsAt_eq_fsParams, fsParams]
  exact Real.rpow_pos_of_pos ht _

/-- The uniform bound `χ_{B(u)} ≤ Cs := chiSupAbs·chiSmallDecay M`. -/
lemma chiSmallB_le_Cs {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u x : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.chiSmallB M ℓ d u x
      ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
  have hb2 : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)
      ≤ Submission.BoseGases.chiSmallDecay M := by
    have hb' := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • x - u)
    rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at hb'
  calc Submission.BoseGases.chiSmallB M ℓ d u x
      ≤ |Submission.BoseGases.chiSmallB M ℓ d u x| := le_abs_self _
    _ ≤ Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) :=
        Work.SmallBoxSliding.abs_chiSmallB_le (M := M) (ℓ := ℓ) (d := d) hM u x
    _ ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
        mul_le_mul_of_nonneg_left hb2 Submission.BoseGases.chiSupAbs_nonneg

/-- **The smooth count is at most `n·Cs²`**, `Cs := chiSupAbs·chiSmallDecay M`. -/
theorem nCountB_le_n_mul {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3))
    {n : ℕ} (x : X n) :
    nCountB M ℓ d u x
      ≤ (n : ℝ) * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2 := by
  have hCs0 : 0 ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg M)
  rw [nCountB]
  calc ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
      ≤ ∑ _i : Fin n, (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := chiSmallB_le_Cs (M := M) hM (ℓ := ℓ) (d := d) u (x i)
        have h2 := Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u (x i)
        nlinarith [h1, h2, hCs0]
    _ = (n : ℝ) * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The linear count is at most `n·Cs`**. -/
theorem sum_chiSmallB_le_n_mul {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (x : X n) :
    (∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
      ≤ (n : ℝ) * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) := by
  calc ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)
      ≤ ∑ _i : Fin n, Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
        Finset.sum_le_sum fun i _ => chiSmallB_le_Cs (M := M) hM (ℓ := ℓ) (d := d) u (x i)
    _ = (n : ℝ) * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 1. The counting functions -/

/-- The `n₊` of the sliding box: the excited count of the small box `dlBox ℓ d u`. -/
noncomputable def nPlus (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  Work.UBBInputs8.cnPlusBoxInd (sideAt μ (a v)) (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
    (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) Φ

/-- The smooth count integral `∫Φ²·nCountB`. -/
noncomputable def scountB (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x

/-- The linear cutoff-count integral `∫Φ²·Σᵢχ_{B(u)}(xᵢ)`. -/
noncomputable def chiSum (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)

/-- The fibre integral `∫Φ²·Σᵢ∫_y w_{1,B(u)}(xᵢ,y)dy`. -/
noncomputable def fibSum {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ)
    (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, (Φ x) ^ 2 *
    ∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
      Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y

/-- The pair integral `∫Φ²·½Σ_{i≠j}w_{B(u)}(xᵢ,xⱼ)`. -/
noncomputable def pairSum (v : EuclideanSpace ℝ (Fin 3) → ℝ) (M : ℕ) (ℓ d : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : X n → ℝ) : ℝ :=
  ∫ x in abox n ℓ, (Φ x) ^ 2 *
    ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
      Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))

/-- The linear cutoff count is monotone in the state's square. -/
theorem chiSum_le {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    {Φ : X n → ℝ} (hΦc : Continuous Φ) :
    chiSum M ℓ d u Φ
      ≤ (n : ℝ) * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * ∫ x in abox n ℓ, (Φ x) ^ 2 := by
  rw [chiSum]
  have hCs0 : 0 ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg M)
  have hcB : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmallB M ℓ d u z) := by
    unfold Submission.BoseGases.chiSmallB
    exact (Submission.BoseGases.chiScale_continuous ℓ).mul
      ((chiSmall_continuous hM).comp (by fun_prop))
  have hcont1 : Continuous (fun x : X n => (Φ x) ^ 2 *
      ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)) := by
    refine (hΦc.pow 2).mul ?_
    refine continuous_finsetSum _ fun i _ => ?_
    exact hcB.comp (continuous_apply i)
  have hcont2 : Continuous (fun x : X n =>
      (n : ℝ) * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        * (Φ x) ^ 2) :=
    continuous_const.mul (hΦc.pow 2)
  have hmono : (∫ x in abox n ℓ, (Φ x) ^ 2 *
        ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
      ≤ ∫ x in abox n ℓ, ((n : ℝ) * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M)) * (Φ x) ^ 2 := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) ?_ ?_
    · exact mul_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun i _ => Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u (x i))
    · exact ContinuousOn.integrableOn_compact (Work.UBBInputs9.B.abox_isCompact n ℓ)
        hcont2.continuousOn
    · exact Filter.Eventually.of_forall fun x => by
        have h1 := sum_chiSmallB_le_n_mul (M := M) hM (ℓ := ℓ) (d := d) u x
        have h2 : 0 ≤ (Φ x) ^ 2 := sq_nonneg _
        have h3 : (Φ x) ^ 2 * (∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
            ≤ (Φ x) ^ 2 * ((n : ℝ)
                * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) :=
          mul_le_mul_of_nonneg_left h1 h2
        calc (Φ x) ^ 2 * (∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
            ≤ (Φ x) ^ 2 * ((n : ℝ)
                * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) := h3
          _ = ((n : ℝ) * (Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmallDecay M)) * (Φ x) ^ 2 := by ring
  rw [integral_const_mul] at hmono
  calc (∫ x in abox n ℓ, (Φ x) ^ 2 *
        ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
      ≤ ((n : ℝ) * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay M)) * (∫ x in abox n ℓ, (Φ x) ^ 2) := hmono
    _ = (n : ℝ) * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay M) * (∫ x in abox n ℓ, (Φ x) ^ 2) := by ring

/-- **The smooth-count integral is at most `n·Cs²·∫Φ²`.** -/
theorem scountB_le {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    {Φ : X n → ℝ} (hΦc : Continuous Φ) :
    scountB M ℓ d u Φ
      ≤ (n : ℝ) * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
          * ∫ x in abox n ℓ, (Φ x) ^ 2 := by
  rw [scountB]
  have hcB : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmallB M ℓ d u z) := by
    unfold Submission.BoseGases.chiSmallB
    exact (Submission.BoseGases.chiScale_continuous ℓ).mul
      ((chiSmall_continuous hM).comp (by fun_prop))
  have hcont_n : Continuous (fun x : X n => nCountB M ℓ d u x) := by
    simp only [nCountB]
    exact continuous_finsetSum _ fun i _ => (hcB.comp (continuous_apply i)).pow 2
  have hcont2 : Continuous (fun x : X n =>
      (n : ℝ) * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
        * (Φ x) ^ 2) := continuous_const.mul (hΦc.pow 2)
  have hmono : (∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
      ≤ ∫ x in abox n ℓ, ((n : ℝ) * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay M) ^ 2) * (Φ x) ^ 2 := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) ?_ ?_
    · exact mul_nonneg (sq_nonneg _) (perBoxMFCase_nCountB_nonneg x)
    · exact ContinuousOn.integrableOn_compact (Work.UBBInputs9.B.abox_isCompact n ℓ)
        hcont2.continuousOn
    · exact Filter.Eventually.of_forall fun x => by
        have h : (Φ x) ^ 2 * nCountB M ℓ d u x
            ≤ (Φ x) ^ 2 * ((n : ℝ) * (Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmallDecay M) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (nCountB_le_n_mul (M := M) (ℓ := ℓ) (d := d) hM u x) (sq_nonneg (Φ x))
        calc (Φ x) ^ 2 * nCountB M ℓ d u x
            ≤ (Φ x) ^ 2 * ((n : ℝ) * (Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmallDecay M) ^ 2) := h
          _ = (n : ℝ) * (Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmallDecay M) ^ 2 * (Φ x) ^ 2 := by ring
  rw [integral_const_mul] at hmono
  calc (∫ x in abox n ℓ, (Φ x) ^ 2 * nCountB M ℓ d u x)
      ≤ ((n : ℝ) * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay M) ^ 2) * (∫ x in abox n ℓ, (Φ x) ^ 2) := hmono
    _ = (n : ℝ) * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay M) ^ 2
          * (∫ x in abox n ℓ, (Φ x) ^ 2) := by ring

/-- **The pair integral is nonnegative** for `0 ≤ v` (the localised pair kernel is pointwise
nonnegative, and `Φ² ≥ 0`). -/
theorem pairSum_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v) {M : ℕ} {ℓ d : ℝ}
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : X n → ℝ) :
    0 ≤ pairSum v M ℓ d u Φ := by
  rw [pairSum]
  refine integral_nonneg fun x => ?_
  refine mul_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) ?_)
  refine Finset.sum_nonneg fun p _ => ?_
  exact perBoxMFCase_wSmallPair_nonneg (f := v)
    (M := M) (ℓ := ℓ) (d := d) (u := u) (x := x p.1) (y := x p.2) hv

/-- **The fibre integral is dominated by the linear cutoff integral** (FS's
`wSmall1Pair_fibre_le_chiB` pointwise, integrated; the pointwise nonnegativity of the fibre is
`perBoxFWeight_holds.wSmall1Pair_fibre_nonneg`). -/
theorem fibSum_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hR0 : 0 < R0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} {Φ : X n → ℝ} (hΦc : Continuous Φ) :
    fibSum h M ℓ d u Φ
      ≤ (16 * π * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
          / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v)
          * chiSum M ℓ d u Φ := by
  rw [fibSum, chiSum]
  have hcB : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmallB M ℓ d u z) := by
    unfold Submission.BoseGases.chiSmallB
    exact (Submission.BoseGases.chiScale_continuous ℓ).mul
      ((chiSmall_continuous hM).comp (by fun_prop))
  have hcont2 : Continuous (fun x : X n =>
      (16 * π * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
          / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v)
        * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))) :=
    continuous_const.mul ((hΦc.pow 2).mul (continuous_finsetSum _ fun i _ =>
      hcB.comp (continuous_apply i)))
  have hmono : (∫ x in abox n ℓ, (Φ x) ^ 2 *
        ∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
      ≤ ∫ x in abox n ℓ,
          ((16 * π * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
              / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v))
            * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) ?_ ?_
    · refine mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => ?_)
      exact wSmall1Pair_fibre_nonneg (v := v) (M := M) hR0 hv hvrad hv_supp h u (x i)
    · exact ContinuousOn.integrableOn_compact (Work.UBBInputs9.B.abox_isCompact n ℓ)
        hcont2.continuousOn
    · exact Filter.Eventually.of_forall fun x => by
        have hKav0 : 0 ≤ 16 * π * Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay M / Work.SmallBoxSliding.smallConvLower M := by
          refine div_nonneg (mul_nonneg (mul_nonneg (by positivity)
            Submission.BoseGases.chiSupAbs_nonneg)
            (Submission.BoseGases.chiSmallDecay_nonneg M)) ?_
          exact le_of_lt (Work.SmallBoxSliding.smallConvLower_pos M)
        have hfib : ∀ i : Fin n,
            ∫ y in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y
              ≤ (16 * π * Submission.BoseGases.chiSupAbs
                  * Submission.BoseGases.chiSmallDecay M
                  / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v)
                  * Submission.BoseGases.chiSmallB M ℓ d u (x i) := by
          intro i
          refine le_trans (le_abs_self _) ?_
          exact wSmall1Pair_fibre_le_chiB (v := v) (R0 := R0) hv_supp hR0 hv hvrad h hM hℓ hd
            hR hRχ u (x i)
        have hsum : (∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
            ≤ (16 * π * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
                / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v)
                * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) := by
          calc (∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
              ≤ ∑ i : Fin n, (16 * π * Submission.BoseGases.chiSupAbs
                    * Submission.BoseGases.chiSmallDecay M
                    / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v)
                    * Submission.BoseGases.chiSmallB M ℓ d u (x i) :=
                Finset.sum_le_sum fun i _ => hfib i
            _ = (16 * π * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
                  / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v)
                  * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) := by
                rw [Finset.mul_sum]
        calc (Φ x) ^ 2 * (∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
            ≤ (Φ x) ^ 2 * ((16 * π * Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmallDecay M
                / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v)
                * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)) :=
              mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
          _ = ((16 * π * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
                / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v))
                * ((Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)) := by
              ring
  rw [integral_const_mul] at hmono
  calc (∫ x in abox n ℓ, (Φ x) ^ 2 *
        ∑ i : Fin n, ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
      ≤ ((16 * π * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
            / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v))
          * (∫ x in abox n ℓ, (Φ x) ^ 2
              * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)) := hmono
    _ = (16 * π * Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
          / Work.SmallBoxSliding.smallConvLower M) * (_root_.BoseGases.a v)
          * (∫ x in abox n ℓ, (Φ x) ^ 2
              * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)) := by ring

/-! ## 3. The gap payment (FS `eq:appgapestimate`) -/

/-- `n₊ ≥ 0` (it is a sum of integrals of squares). -/
theorem nPlus_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : X n → ℝ) :
    0 ≤ nPlus v μ u Φ := by
  rw [nPlus, Work.UBBInputs8.cnPlusBoxInd]
  exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _

/-- **The excited count of the small box is paid by the kinetic gap** at the coefficient
`eT/(2(1+π⁻²)(dℓ)²) = tbGapCoeff (dℓ) eT`, i.e. FS `eq:appgapestimate` in the sharp form in which
the whole gap coefficient is available (the nonnegativity of the spectral half is
`Work.BoseFixB1.tBwordKinInd_nonneg`). -/
theorem nPlus_gap_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {M : ℕ}
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : X n → ℝ) :
    (paramsAt μ (a v)).eT
        / (2 * (1 + (Real.pi ^ 2)⁻¹)
          * ((paramsAt μ (a v)).d * sideAt μ (a v)) ^ 2)
      * nPlus v μ u Φ ≤ sbKin (v := v) μ M u Φ := by
  have hker := tBwordKinInd_nonneg (a := sideAt μ (a v))
    (A := dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
    (volA := boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
    (χ := chiB (sideAt μ (a v)) (paramsAt μ (a v)).d u) (c := sbCut μ (a v)) Φ
  have hgap := sbKin_ge_gapPart (v := v) (μ := μ) (M := M) (u := u) Φ hker
  rw [nPlus]
  refine le_trans ?_ hgap
  refine mul_le_mul_of_nonneg_right ?_ (nPlus_nonneg (v := v) μ u Φ)
  -- the coefficient identity: eT/(2(1+π⁻²)(dℓ)²) = tbGapCoeff (dℓ) eT
  rw [Work.SmallBoxTBWord.tbGapCoeff, Work.SmallBoxTBWord.tbPiFactor]
  field_simp
  linarith


end Work.BoseFixB1
