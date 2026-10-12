import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB3.CS.Pieces.qcross_bar_om_pair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `qcross_bar_om_pair_weighted` — the two-parameter AM–GM budget for the `ω`-pairing

The *weighted* (two-parameter Young) version of the `ω`-pairing AM–GM of
`CS/Pieces/qcross_bar_om_pair.lean`.  Where the latter uses the fixed FS budget
`(9/2, 1/2, 1/16)`, the present lemma records that the same pointwise pairing can be
split **freely** between the two Young parameters `t, ε > 0`: with `|ω| ≤ 1` and
`0 ≤ W ≤ wt`,

  `|F|·|B − ω·S|·W ≤ (t + 1/(4ε))·F²·W + (1/(4t))·B²·wt + ε·S²·W`,

which after integration over `abox N ℓ` (with `W = |w₁|` and `wt = w`) is exactly the
statement below.  The freedom lets one shift mass between the `Q̄_L`-square and the
`4Q`-square.

The proof is the same shape as the unweighted one: pointwise Young + integrability of the
three majorants (`sq_slot_wPair_abs_integrable`, `q4B_sq_w_integrable`).

## Main results

* `weighted_amgm_budget` — the two-parameter pointwise budget;
* `qcross_bar_om_pair_weighted` — its integration over the box.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.BoseFixB3.CS.Pieces

open _root_.BoseGases Submission.BoseGases

/-- **The two-parameter Young/AM–GM budget of the `ω`-pairing.**  With `|ω| ≤ 1`,
`0 ≤ W ≤ wt` and `QQ := BB − ω·SS`, for any `t, ε > 0`,

`|F|·|BB − ω·SS|·W ≤ (t + 1/(4ε))·F²·W + (1/(4t))·BB²·wt + ε·SS²·W`.

(The two pairings are `|F||BB| ≤ t·F²·W + (1/(4t))BB²·wt` — using `W ≤ wt` — and
`|F||SS| ≤ (1/(4ε))F²·W + ε·SS²·W`; both are instances of
`4λ(λ A² W + (1/(4λ))B² wt − A B W) = W(2λA − B)² + B²(wt − W)` (`B = |BB|`), resp.
`4ε((1/(4ε))F²W + εS²W − |F||S|W) = W(|F| − 2ε|S|)²`.) -/
lemma weighted_amgm_budget {om W wt F SS BB t ε : ℝ}
    (hom : |om| ≤ 1) (hW : 0 ≤ W) (hWwt : W ≤ wt) (ht : 0 < t) (hε : 0 < ε) :
    |F| * |BB - om * SS| * W
      ≤ (t + 1 / (4 * ε)) * F ^ 2 * W + (1 / (4 * t)) * BB ^ 2 * wt + ε * SS ^ 2 * W := by
  have hBBle : |BB - om * SS| ≤ |BB| + |SS| := by
    calc |BB - om * SS| = |BB + -(om * SS)| := by rw [sub_eq_add_neg]
      _ ≤ |BB| + |-(om * SS)| := abs_add_le _ _
      _ = |BB| + |om * SS| := by rw [abs_neg]
      _ = |BB| + |om| * |SS| := by rw [abs_mul]
      _ ≤ |BB| + 1 * |SS| := by
          have := mul_le_mul_of_nonneg_right hom (abs_nonneg SS)
          linarith
      _ = |BB| + |SS| := by ring
  have h1 : |F| * |BB| * W ≤ t * F ^ 2 * W + (1 / (4 * t)) * BB ^ 2 * wt := by
    have hid : 4 * t * (t * F ^ 2 * W + (1 / (4 * t)) * BB ^ 2 * wt - |F| * |BB| * W)
        = (2 * t * |F| - |BB|) ^ 2 * W + BB ^ 2 * (wt - W) := by
      rw [← sq_abs F, ← sq_abs BB]
      field_simp
      ring
    nlinarith [hid, sq_nonneg (2 * t * |F| - |BB|), sq_nonneg BB, hW,
      mul_nonneg (sq_nonneg (2 * t * |F| - |BB|)) hW,
      mul_nonneg (sq_nonneg BB) (sub_nonneg.mpr hWwt), ht]
  have h2 : |F| * |SS| * W ≤ (1 / (4 * ε)) * F ^ 2 * W + ε * SS ^ 2 * W := by
    have hid : 4 * ε * ((1 / (4 * ε)) * F ^ 2 * W + ε * SS ^ 2 * W - |F| * |SS| * W)
        = (|F| - 2 * ε * |SS|) ^ 2 * W := by
      rw [← sq_abs F, ← sq_abs SS]
      field_simp
      ring
    nlinarith [hid, mul_nonneg (sq_nonneg (|F| - 2 * ε * |SS|)) hW, hW, hε]
  have h3 : |F| * (|BB| + |SS|) * W
      ≤ (t * F ^ 2 * W + (1 / (4 * t)) * BB ^ 2 * wt)
        + ((1 / (4 * ε)) * F ^ 2 * W + ε * SS ^ 2 * W) := by
    have e : |F| * (|BB| + |SS|) * W = |F| * |BB| * W + |F| * |SS| * W := by ring
    rw [e]
    linarith
  calc |F| * |BB - om * SS| * W ≤ |F| * (|BB| + |SS|) * W :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBBle (abs_nonneg F)) hW
    _ ≤ _ := h3
    _ = (t + 1 / (4 * ε)) * F ^ 2 * W + (1 / (4 * t)) * BB ^ 2 * wt + ε * SS ^ 2 * W := by
        ring

theorem qcross_bar_om_pair_weighted {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv1 : MeasureTheory.MemLp v 1 MeasureTheory.volume) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {fc : Work.BoseBoxFix.LowCut} {κ : ℝ} {i j : Fin N} (hij : i ≠ j)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    |∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB3.highSlot fc κ ℓ j
            (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ)) x
          * (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) x
             - Classical.choose h (x i - x j)
               * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x
                  + Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ) x))
          * Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j)|
      ≤ (t + 1 / (4 * ε)) * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB3.highSlot fc κ ℓ j
              (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ)) x) ^ 2
              * |Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j)|)
        + (1 / (4 * t)) * (∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) x) ^ 2
              * Submission.BoseGases.wLoc ℓ v 0 (x i) (x j))
        + ε * (∫ x in Submission.BoseGases.abox N ℓ,
            (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x
              + Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ) x) ^ 2
              * |Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) (x j)|) := by
  classical
  rw [Work.BoseFixB3.wLoc_zero_eq_wPair ℓ (g0 v h),
      Work.BoseFixB3.wLoc_zero_eq_wPair ℓ v]
  let μ : Measure (X N) := volume.restrict (abox N ℓ)
  let Ψ : X N → ℝ := aP ℓ i (aQ ℓ j Φ)
  let FF : X N → ℝ := fun x => Work.BoseFixB3.highSlot fc κ ℓ j Ψ x
  let SS : X N → ℝ := fun x => (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)
  let BB : X N → ℝ := fun x => q4B ℓ (omC (Classical.choose h)) Φ (i, j) x
  let omx : X N → ℝ := fun x => Classical.choose h (x i - x j)
  let QQ : X N → ℝ := fun x => BB x - omx x * SS x
  let WW : X N → ℝ := fun x => |wPair ℓ (g0 v h) (x i) (x j)|
  let wt : X N → ℝ := fun x => wPair ℓ v (x i) (x j)
  let MAJ : X N → ℝ := fun x => (t + 1 / (4 * ε)) * ((FF x) ^ 2 * WW x)
    + (1 / (4 * t)) * ((BB x) ^ 2 * wt x) + ε * ((SS x) ^ 2 * WW x)
  have hΨc : Continuous Ψ := by
    dsimp [Ψ]
    exact aP_continuous hℓ i (aQ_continuous hℓ j hΦc)
  have hSSc : Continuous SS := by
    dsimp [SS]
    exact (aP_continuous hℓ j (aQ_continuous hℓ i hΦc)).add
      (aQ_continuous hℓ j (aP_continuous hℓ i hΦc))
  have hg0i : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hg0supp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → g0 v h z = 0 :=
    fun z hz => g0_zero_of_norm_ge hv_supp hz h
  have hWint : Integrable (fun x : X N => WW x) μ := by
    have hs : IntegrableOn (fun x : X N => |wPair ℓ (g0 v h) (x i) (x j)|)
        (abox N ℓ) volume := by
      simpa using (sq_slot_wPair_abs_integrable hℓ hg0i hg0supp hRℓ hij
        (S := fun _ : X N => (1 : ℝ)) continuous_const)
    simpa [WW, μ, IntegrableOn] using hs
  have hΨ2W : Integrable (fun x : X N => (Ψ x) ^ 2 * WW x) μ := by
    have hs : IntegrableOn (fun x : X N => (Ψ x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        (abox N ℓ) volume := by
      simpa [Ψ] using (sq_slot_wPair_abs_integrable hℓ hg0i hg0supp hRℓ hij (S := Ψ) hΨc)
    simpa [WW, μ, IntegrableOn] using hs
  have hS2W : Integrable (fun x : X N => (SS x) ^ 2 * WW x) μ := by
    have hs : IntegrableOn (fun x : X N => (SS x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        (abox N ℓ) volume := by
      simpa using (sq_slot_wPair_abs_integrable hℓ hg0i hg0supp hRℓ hij (S := SS) hSSc)
    simpa [WW, μ, IntegrableOn] using hs
  have hB2wt : Integrable (fun x : X N => (BB x) ^ 2 * wt x) μ := by
    have hs := q4B_sq_w_integrable hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv1 hij hΦc
    simpa [BB, wt, μ, IntegrableOn] using hs
  have hmeas : AEStronglyMeasurable (fun x : X N => (FF x) ^ 2 * WW x) μ := by
    have hhs := highSlot_stronglyMeasurable (fc := fc) (κ := κ) (ℓ := ℓ) j (Ψ := Ψ) hΨc
    have hfm : AEMeasurable (fun x : X N => FF x) μ := by
      simpa [FF] using hhs.aemeasurable
    exact ((hfm.pow_const 2).mul hWint.aemeasurable).aestronglyMeasurable
  have hFF2W : Integrable (fun x : X N => (FF x) ^ 2 * WW x) μ := by
    rcases lt_or_ge (0 : ℝ) κ with hκ | hκ
    · obtain ⟨C, hC0, hCb⟩ :=
        highSlot_bound_of_pos (fc := fc) (κ := κ) (ℓ := ℓ) hκ hℓ (n := N) j (Ψ := Ψ) hΨc
      have hmaj : Integrable (fun x : X N => (C ^ 2) * WW x) μ := hWint.const_mul (C ^ 2)
      have hae_mem : ∀ᵐ x ∂μ, x ∈ abox N ℓ := by
        have h := MeasureTheory.ae_restrict_mem (μ := (volume : Measure (X N))) (s := abox N ℓ)
          (abox_compact N hℓ).isClosed.measurableSet
        simpa [μ] using h
      refine Integrable.mono' hmaj hmeas ?_
      filter_upwards [hae_mem] with x hx
      have hb : |FF x| ≤ C := by simpa [FF, Ψ] using hCb x hx
      have hWnn : 0 ≤ WW x := abs_nonneg _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (FF x)), abs_of_nonneg hWnn]
      have hsq : (FF x) ^ 2 ≤ C ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      exact mul_le_mul_of_nonneg_right hsq hWnn
    · have hle : ∀ᵐ x ∂μ, (FF x) ^ 2 ≤ 4 * (Ψ x) ^ 2 := by
        have h := highSlot_sq_le_of_nonpos_aux (fc := fc) (κ := κ) (ℓ := ℓ) hκ hℓ
          (n := N) j (Ψ := Ψ) hΨc
        simpa [FF, μ] using h
      have hmaj : Integrable (fun x : X N => 4 * ((Ψ x) ^ 2 * WW x)) μ := by
        simpa [WW] using hΨ2W.const_mul 4
      refine Integrable.mono' hmaj hmeas ?_
      filter_upwards [hle] with x hx
      have hnn : 0 ≤ WW x := abs_nonneg _
      calc ‖(FF x) ^ 2 * WW x‖ = (FF x) ^ 2 * WW x := by
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (FF x)), abs_of_nonneg hnn]
        _ ≤ (4 * (Ψ x) ^ 2) * WW x := mul_le_mul_of_nonneg_right hx hnn
        _ = 4 * ((Ψ x) ^ 2 * WW x) := by ring
  have hU : Integrable MAJ μ := by
    have h1 : Integrable (fun x : X N =>
        (t + 1 / (4 * ε)) * ((FF x) ^ 2 * WW x) + (1 / (4 * t)) * ((BB x) ^ 2 * wt x)) μ :=
      (hFF2W.const_mul (t + 1 / (4 * ε))).add (hB2wt.const_mul (1 / (4 * t)))
    refine (h1.add (hS2W.const_mul ε)).congr ?_
    filter_upwards with x
    rfl
  have hWnn : ∀ x : X N, 0 ≤ WW x := fun x => abs_nonneg _
  have homxb : ∀ᵐ x ∂μ, |omx x| ≤ 1 := by
    dsimp [omx, μ]
    simpa using (w0_abs_le_one_box_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij)
  have hWlewt : ∀ᵐ x ∂μ, WW x ≤ wt x := by
    dsimp [WW, wt, μ]
    simpa using (w1_abs_le_w_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij)
  have hmain : ∀ᵐ x ∂μ,
      |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))| ≤ MAJ x := by
    filter_upwards [homxb, hWlewt] with x homx1 hWle
    have hb : |FF x| * |BB x - omx x * SS x| * WW x
        ≤ (t + 1 / (4 * ε)) * (FF x) ^ 2 * WW x + (1 / (4 * t)) * (BB x) ^ 2 * wt x
          + ε * (SS x) ^ 2 * WW x :=
      weighted_amgm_budget homx1 (hWnn x) hWle ht hε
    have habs : |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))|
        = |FF x| * |BB x - omx x * SS x| * WW x := by
      have hQQx : QQ x = BB x - omx x * SS x := rfl
      rw [hQQx, abs_mul, abs_mul, ← mul_assoc]
    have hMAJ : MAJ x = (t + 1 / (4 * ε)) * (FF x) ^ 2 * WW x
        + (1 / (4 * t)) * (BB x) ^ 2 * wt x + ε * (SS x) ^ 2 * WW x := by
      simp only [MAJ]
      ring
    rw [habs, hMAJ]
    exact hb
  have hL1 : |∫ x in abox N ℓ,
        (FF x) * (QQ x) * wPair ℓ (g0 v h) (x i) (x j)|
      ≤ ∫ x in abox N ℓ, |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))| := by
    have hEq : (fun x : X N => (FF x) * (QQ x) * wPair ℓ (g0 v h) (x i) (x j))
        =ᵐ[μ] (fun x : X N => FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))) := by
      refine ae_of_all _ (fun x => ?_)
      ring
    calc
      |∫ x in abox N ℓ,
          (FF x) * (QQ x) * wPair ℓ (g0 v h) (x i) (x j)|
          = |∫ x : X N, FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j)) ∂μ| := by
            congr 1
            rw [integral_congr_ae (μ := μ) hEq]
      _ ≤ ∫ x : X N, |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))| ∂μ := by
            exact abs_integral_le_integral_abs (μ := μ)
  have hL2 : (∫ x in abox N ℓ, |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))|)
      ≤ ∫ x in abox N ℓ, MAJ x := by
    refine integral_mono_of_nonneg (μ := μ) ?_ hU ?_
    · filter_upwards with x
      exact abs_nonneg _
    · exact hmain
  have hL3 : (∫ x : X N, MAJ x ∂μ)
      = (t + 1 / (4 * ε)) * (∫ x : X N, (FF x) ^ 2 * WW x ∂μ)
        + (1 / (4 * t)) * (∫ x : X N, (BB x) ^ 2 * wt x ∂μ)
        + ε * (∫ x : X N, (SS x) ^ 2 * WW x ∂μ) := by
    have hT1 : Integrable (fun x : X N => (t + 1 / (4 * ε)) * ((FF x) ^ 2 * WW x)) μ :=
      hFF2W.const_mul (t + 1 / (4 * ε))
    have hT2 : Integrable (fun x : X N => (1 / (4 * t)) * ((BB x) ^ 2 * wt x)) μ :=
      hB2wt.const_mul (1 / (4 * t))
    have hT3 : Integrable (fun x : X N => ε * ((SS x) ^ 2 * WW x)) μ :=
      hS2W.const_mul ε
    have h12 : Integrable (fun x : X N =>
        (t + 1 / (4 * ε)) * ((FF x) ^ 2 * WW x)
          + (1 / (4 * t)) * ((BB x) ^ 2 * wt x)) μ := hT1.add hT2
    calc
      (∫ x, MAJ x ∂μ)
          = (∫ x, (((t + 1 / (4 * ε)) * ((FF x) ^ 2 * WW x)
              + (1 / (4 * t)) * ((BB x) ^ 2 * wt x)) + ε * ((SS x) ^ 2 * WW x)) ∂μ) := by
              apply integral_congr_ae
              filter_upwards with x
              simp only [MAJ]
      _ = (∫ x, (t + 1 / (4 * ε)) * ((FF x) ^ 2 * WW x)
              + (1 / (4 * t)) * ((BB x) ^ 2 * wt x) ∂μ)
          + (∫ x, ε * ((SS x) ^ 2 * WW x) ∂μ) := integral_add h12 hT3
      _ = (∫ x, (t + 1 / (4 * ε)) * ((FF x) ^ 2 * WW x) ∂μ)
          + (∫ x, (1 / (4 * t)) * ((BB x) ^ 2 * wt x) ∂μ)
          + (∫ x, ε * ((SS x) ^ 2 * WW x) ∂μ) := by
              rw [integral_add hT1 hT2]
      _ = (t + 1 / (4 * ε)) * (∫ x, (FF x) ^ 2 * WW x ∂μ)
          + (1 / (4 * t)) * (∫ x, (BB x) ^ 2 * wt x ∂μ)
          + ε * (∫ x, (SS x) ^ 2 * WW x ∂μ) := by
              rw [integral_const_mul, integral_const_mul, integral_const_mul]
  calc
    |∫ x in abox N ℓ,
        (FF x) * (QQ x) * wPair ℓ (g0 v h) (x i) (x j)|
        ≤ ∫ x in abox N ℓ, |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))| := hL1
    _ ≤ ∫ x in abox N ℓ, MAJ x := hL2
    _ = (t + 1 / (4 * ε)) * (∫ x : X N, (FF x) ^ 2 * WW x ∂μ)
        + (1 / (4 * t)) * (∫ x : X N, (BB x) ^ 2 * wt x ∂μ)
        + ε * (∫ x : X N, (SS x) ^ 2 * WW x ∂μ) := by
          simpa [μ] using hL3
    _ = (t + 1 / (4 * ε)) * (∫ x in abox N ℓ,
          (FF x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        + (1 / (4 * t)) * (∫ x in abox N ℓ,
            ((BB x) ^ 2 * wPair ℓ v (x i) (x j)))
        + ε * (∫ x in abox N ℓ,
            (SS x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|) := by
          simp [μ, FF, SS, BB, WW, wt, Ψ, add_assoc]

end Work.BoseFixB3.CS.Pieces
