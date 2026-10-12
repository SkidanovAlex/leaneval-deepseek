import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.PCFU.KchiFrU_eq_periodisation
import Submission.Work.BoseBoxFock.PCFU.chBslotAux
import Submission.Work.BoseBoxFock.PCFU.uvSmearImageSumBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.Bdecomp` — the `(B)`-slot decomposition of the cubic dictionary

The `χ̂`-weighted `univ` frame `KχfrU` (the periodisation of the UV-smoothed weight, PROVED in
`KchiFrU_eq_periodisation`) decomposes, after subtracting the direct `χ_Λ ⋆ W₁` pairing, into

* the **smoothing error** `χ_Λ ⋆ (ψ_Λ ⋆ W₁ − W₁)`, and
* the **lattice images** `Σ'_{d ≠ 0} (ψ_Λ ⋆ W₁)(· − w + ℓ·latVec d)`,

which are exactly the two pieces the `(B)`-slot's estimate needs (`chiStarE_le` and `chB_img_le`).

## Route (all ingredients proved)

Writing `ℓ = ellH v μ`, `W₁ = W1fun v h ℓ`, `ψ_Λ ⋆ W₁ = uvSmear fu (uvRad ℓ N) W₁`, `χ = chiLam ℓ`:

1. **periodisation** (`KchiFrU_eq_periodisation`):
   `KχfrU z = ∫_w χ(w)·Σ'_d (ψ_Λ ⋆ W₁)(z − w + ℓ•latVec d)`;
2. **splitting off `d = 0`** (`Summable.tsum_eq_add_tsum_ite`, applied to the summable family
   `d ↦ ↑((ψ_Λ ⋆ W₁)(z − w + ℓ•latVec d))` — `summable_shift_latVec` + the rapid decay
   `uvSmear_rapidDecay`), which exposes the images as a `tsum` of the `d ≠ 0` terms;
3. **additivity of the Bochner integral** on the three pieces, whose integrability is:
   * `χ·(ψ_Λ ⋆ W₁)(z − ·)` and `χ·W₁(z − ·)`: `χ` is bounded (`chiLam_le_chiSupAbs`) and the
     weight is `L¹` (`uvSmear_rapidDecay` for the first, `hI` for the second);
   * `χ·Σ'_{d≠0}(ψ_Λ ⋆ W₁)(z − · + ℓd)`: `χ` is supported in `closedBall 0 (ℓ/2)`
     (`chiLam_eq_zero_of_half_lt`), and on that ball the image sum is *uniformly* bounded
     (`uvSmearImageSumBound`);
4. **the flip** `∫_y χ(y)W₁(y − z) dy = ∫_w χ(w)W₁(z − w) dw`, which needs only the evenness of
   `W₁` (substitutions `y ↦ y + z`, `y ↦ −y` and `w ↦ z − w`);
5. **the `d ≠ 0` sum is the real `tsum`** of the target (`Complex.ofReal_tsum`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-- The integration flip: the `W₁`-side of the `(B)`-slot kernel is invariant under `y ↦ -y`. -/
lemma chiLam_W1fun_integral_flip {ℓ : ℝ} {W1 : E3 → ℝ}
    (hev : ∀ x : E3, W1 (-x) = W1 x) (z : E3) :
    (∫ y : E3, ((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ) : ℂ) * ((W1 (y - z) : ℝ) : ℂ))
      = ∫ w : E3, ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) * ((W1 (z - w) : ℝ) : ℂ) := by
  have h1 : (∫ y : E3, ((Work.BoseK15.corpusBox.chiLam ℓ y : ℝ) : ℂ) * ((W1 (y - z) : ℝ) : ℂ))
      = ∫ t : E3, ((Work.BoseK15.corpusBox.chiLam ℓ (t + z) : ℝ) : ℂ) * ((W1 t : ℝ) : ℂ) := by
    have hh := MeasureTheory.integral_sub_right_eq_self (μ := (volume : Measure E3))
      (fun t : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ (t + z) : ℝ) : ℂ) * ((W1 t : ℝ) : ℂ)) z
    simpa only [sub_add_cancel] using hh
  have h3 : (∫ t : E3, ((Work.BoseK15.corpusBox.chiLam ℓ (t + z) : ℝ) : ℂ) * ((W1 t : ℝ) : ℂ))
      = ∫ s : E3, ((Work.BoseK15.corpusBox.chiLam ℓ (z - s) : ℝ) : ℂ) * ((W1 s : ℝ) : ℂ) := by
    have hh := MeasureTheory.integral_neg_eq_self
      (fun t : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ (t + z) : ℝ) : ℂ) * ((W1 t : ℝ) : ℂ))
      (volume : Measure E3)
    have hpt : ∀ t : E3, ((Work.BoseK15.corpusBox.chiLam ℓ (-t + z) : ℝ) : ℂ)
        * ((W1 (-t) : ℝ) : ℂ)
        = ((Work.BoseK15.corpusBox.chiLam ℓ (z - t) : ℝ) : ℂ) * ((W1 t : ℝ) : ℂ) := by
      intro t
      rw [show -t + z = z - t by abel, hev t]
    rw [show (fun t : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ (-t + z) : ℝ) : ℂ)
        * ((W1 (-t) : ℝ) : ℂ))
        = (fun s : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ (z - s) : ℝ) : ℂ)
        * ((W1 s : ℝ) : ℂ)) from funext hpt] at hh
    exact hh.symm
  have h2 : (∫ w : E3, ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) * ((W1 (z - w) : ℝ) : ℂ))
      = ∫ s : E3, ((Work.BoseK15.corpusBox.chiLam ℓ (z - s) : ℝ) : ℂ) * ((W1 s : ℝ) : ℂ) := by
    have hh := MeasureTheory.integral_sub_left_eq_self
      (fun s : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ s : ℝ) : ℂ) * ((W1 (z - s) : ℝ) : ℂ))
      (volume : Measure E3) z
    simpa only [sub_sub_cancel] using hh.symm
  exact h1.trans (h3.trans h2.symm)

/-- `(1+‖x‖)^{-4}` is integrable in `ℝ³`, in the `zpow` spelling produced by the decay lemmas. -/
private lemma integrable_zpow_four :
    Integrable (fun x : E3 => (1 + ‖x‖) ^ (-(4 : ℤ))) (volume : Measure E3) := by
  have hbase : Integrable (fun x : E3 => (1 + ‖x‖) ^ (-(4 : ℝ))) (volume : Measure E3) :=
    integrable_one_add_norm (E := E3) (μ := (volume : Measure E3)) (r := 4) (by
      rw [finrank_euclideanSpace, Fintype.card_fin]; norm_num)
  refine hbase.congr (Filter.Eventually.of_forall fun x => ?_)
  exact Real.rpow_neg_natCast (1 + ‖x‖) 4

theorem Bdecomp {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {fu : Work.BoseBoxFix.LowCut}
    {μ : ℝ} {N : ℕ} (hℓ0 : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (hN : 1 ≤ N)
    (hI : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))
    (hcs : HasCompactSupport (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))
    (hev : ∀ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (-x)
      = Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x)
    (z : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
        - (∫ y : EuclideanSpace ℝ (Fin 3), Complex.ofReal (Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) y)
            * Complex.ofReal (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (y - z)))
      = (∫ w : EuclideanSpace ℝ (Fin 3), Complex.ofReal (Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w)
            * Complex.ofReal (Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
                (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (z - w)
              - Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (z - w)))
        + (∫ w : EuclideanSpace ℝ (Fin 3), Complex.ofReal (Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w)
            * Complex.ofReal (∑' d : Fin 3 → ℤ, if d = 0 then 0 else
              (Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
                (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                (z - w + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d)))) := by
  classical
  let ℓ : ℝ := Work.BoseBoxFock.ellH v μ
  let W1 : E3 → ℝ := Work.BoseFixR.W1fun v h ℓ
  let U : E3 → ℝ := Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad ℓ N) W1
  let χ : E3 → ℝ := Work.BoseK15.corpusBox.chiLam ℓ
  let T : E3 → ℂ := fun w => ∑' d : Fin 3 → ℤ,
    if d = 0 then (0 : ℂ) else ((U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)
  have hℓ : 0 < ℓ := Work.BoseBoxFock.ellH_pos v μ
  have hΛ : 0 < Work.BoseBoxFock.uvRad ℓ N := by
    rw [Work.BoseBoxFock.uvRad]
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  -- ## the periodisation identity
  have hK : Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
      = ∫ w : E3, ((χ w : ℝ) : ℂ)
          * (∑' d : Fin 3 → ℤ, ((U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)) := by
    have hIe : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) := hI
    have hcse : HasCompactSupport (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) := hcs
    have heve : ∀ x : E3, Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (-x)
        = Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x := hev
    exact Work.BoseBoxFock.PCFU.KchiFrU_eq_periodisation (v := v) (h := h) (fu := fu)
      (μ := μ) (N := N) hℓ0 hN hIe hcse heve z
  -- ## summability of the lattice family
  have hsumm : ∀ q : E3,
      Summable (fun d : Fin 3 → ℤ => ((U (q + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)) := by
    intro q
    obtain ⟨C, hC0, hC⟩ := Work.BoseBoxFock.uvSmear_rapidDecay fu hΛ (f := W1) hI hcs 4
    refine Work.BoseBoxFock.summable_shift_latVec (Φ := fun x : E3 => ((U x : ℝ) : ℂ))
      (C := C) hC0 ?_ hℓ q
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hC x
  -- ## the pointwise split of the lattice sum
  have hsplit : ∀ w : E3,
      (∑' d : Fin 3 → ℤ, ((U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
        = ((U (z - w) : ℝ) : ℂ) + T w := by
    intro w
    have hs := hsumm (z - w)
    rw [hs.tsum_eq_add_tsum_ite (0 : Fin 3 → ℤ)]
    congr 1
    rw [show Work.BoseBoxFock.latVec (0 : Fin 3 → ℤ) = (0 : E3) by
      ext i; simp [Work.BoseBoxFock.latVec], smul_zero, add_zero]
  -- ## the integrability of the pieces
  have hχcont : Continuous (fun w : E3 => ((χ w : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Work.BoseK15.corpusBox.chiLam_cont ℓ)
  have hχbd : ∀ w : E3, ‖((χ w : ℝ) : ℂ)‖ ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := by
    intro w
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Work.BoseBoxFock.PCFU.chiLam_nonneg' ℓ w)]
    exact Work.BoseBoxFock.PCFU.chiLam_le_chiSupAbs ℓ w
  have hUcont : Continuous U := Work.BoseBoxFock.uvSmear_continuous fu hΛ hI
  have hUint : Integrable U := by
    obtain ⟨C, hC0, hC⟩ := Work.BoseBoxFock.uvSmear_rapidDecay fu hΛ (f := W1) hI hcs 4
    refine Integrable.mono' (integrable_zpow_four.const_mul C)
      (Work.BoseBoxFock.uvSmear_continuous fu hΛ hI).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hC x
  have hU0int : Integrable (fun w : E3 => ((χ w : ℝ) : ℂ) * ((U (z - w) : ℝ) : ℂ)) :=
    ((hUint.comp_sub_left z).ofReal).bdd_mul hχcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hχbd)
  have hW1int : Integrable (fun w : E3 => ((χ w : ℝ) : ℂ) * ((W1 (z - w) : ℝ) : ℂ)) :=
    ((hI.comp_sub_left z).ofReal).bdd_mul hχcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hχbd)
  obtain ⟨Cimg, hCimg0, hbound⟩ :=
    Work.BoseBoxFock.PCFU.uvSmearImageSumBound (fu := fu) (Λ := Work.BoseBoxFock.uvRad ℓ N)
      (f := W1) hΛ hI hcs (ℓ := ℓ) hℓ z
  have hTmeas : AEStronglyMeasurable T (volume : Measure E3) := by
    refine AEStronglyMeasurable.tsum (fun d : Fin 3 → ℤ => ?_)
    by_cases hd : d = 0
    · refine (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : E3 => (0 : ℂ))
        (volume : Measure E3)).congr (Filter.Eventually.of_forall fun w => ?_)
      simp [hd]
    · have hlin : Continuous (fun w : E3 => z - w + ℓ • Work.BoseBoxFock.latVec d) :=
        (continuous_const.sub continuous_id).add continuous_const
      have hcont : Continuous (fun w : E3 => ((U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp (hUcont.comp hlin)
      exact hcont.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun w => by simp [hd])
  have hχint : Integrable (fun w : E3 => Cimg * χ w) (volume : Measure E3) := by
    have hχcs : HasCompactSupport χ :=
      HasCompactSupport.of_support_subset_isCompact (Work.BoseK15.corpusBox.boxL_compact ℓ)
        (Work.BoseK15.corpusBox.chiLam_supp hℓ)
    have hχRcont : Continuous χ := Work.BoseK15.corpusBox.chiLam_cont ℓ
    exact (hχRcont.integrable_of_hasCompactSupport hχcs).const_mul Cimg
  have hTint : Integrable (fun w : E3 => ((χ w : ℝ) : ℂ) * T w) (volume : Measure E3) := by
    refine Integrable.mono' hχint (hχcont.aestronglyMeasurable.mul hTmeas) ?_
    filter_upwards with w
    rcases le_or_gt ‖w‖ (ℓ / 2) with hw | hw
    · have hmem : w ∈ Metric.closedBall (0 : E3) (ℓ / 2) := by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hw
      have hTs : ‖T w‖ ≤ Cimg := by
        have hnorm : Summable (fun d : Fin 3 → ℤ =>
            ‖U (z - w + ℓ • Work.BoseBoxFock.latVec d)‖) :=
          Summable.of_nonneg_of_le (fun d => norm_nonneg _)
            (fun d => le_of_eq (by rw [Complex.norm_real, Real.norm_eq_abs]))
            ((hsumm (z - w)).norm)
        have hitenorm : Summable (fun d : Fin 3 → ℤ =>
            ‖if d = 0 then (0 : ℂ)
              else ((U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)‖) := by
          refine Summable.of_nonneg_of_le (fun d => norm_nonneg _) (fun d => ?_) hnorm
          by_cases hd : d = 0
          · rw [if_pos hd]; simp only [norm_zero]; exact norm_nonneg _
          · rw [if_neg hd, Complex.norm_real, Real.norm_eq_abs]
        refine le_trans (norm_tsum_le_tsum_norm hitenorm) ?_
        refine le_trans (Summable.tsum_le_tsum (fun d => ?_) hitenorm hnorm) ?_
        · by_cases hd : d = 0
          · rw [if_pos hd]; simp only [norm_zero]; exact norm_nonneg _
          · rw [if_neg hd, Complex.norm_real, Real.norm_eq_abs]
        · exact hbound w hmem
      calc ‖((χ w : ℝ) : ℂ) * T w‖ = χ w * ‖T w‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (Work.BoseBoxFock.PCFU.chiLam_nonneg' ℓ w)]
        _ ≤ χ w * Cimg :=
            mul_le_mul_of_nonneg_left hTs (Work.BoseBoxFock.PCFU.chiLam_nonneg' ℓ w)
        _ = Cimg * χ w := by ring
    · have hχ0 : χ w = 0 := Work.BoseBoxFock.PCFU.chiLam_eq_zero_of_half_lt hℓ hw
      rw [hχ0]
      simp
  have hCU1 : Integrable (fun w : E3 => ((χ w : ℝ) : ℂ) * ((U (z - w) - W1 (z - w) : ℝ) : ℂ)) := by
    refine (hU0int.sub hW1int).congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.sub_apply, Complex.ofReal_sub]
    ring
  -- ## the pointwise product identity
  have hpt : ∀ w : E3, ((χ w : ℝ) : ℂ)
        * (∑' d : Fin 3 → ℤ, ((U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
      = ((χ w : ℝ) : ℂ) * ((U (z - w) - W1 (z - w) : ℝ) : ℂ)
        + ((χ w : ℝ) : ℂ) * ((W1 (z - w) : ℝ) : ℂ) + ((χ w : ℝ) : ℂ) * T w := by
    intro w
    rw [hsplit w]
    push_cast
    ring
  -- ## the main integral identity
  have hstep : (∫ w : E3, ((χ w : ℝ) : ℂ)
        * (∑' d : Fin 3 → ℤ, ((U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)))
      = ∫ w : E3, (((χ w : ℝ) : ℂ) * ((U (z - w) - W1 (z - w) : ℝ) : ℂ)
          + ((χ w : ℝ) : ℂ) * ((W1 (z - w) : ℝ) : ℂ)) + ((χ w : ℝ) : ℂ) * T w :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => by simp only [hpt w])
  have hAB : Integrable (fun w : E3 => ((χ w : ℝ) : ℂ) * ((U (z - w) - W1 (z - w) : ℝ) : ℂ)
      + ((χ w : ℝ) : ℂ) * ((W1 (z - w) : ℝ) : ℂ)) := hCU1.add hW1int
  have hAB2 : (∫ w : E3, ((χ w : ℝ) : ℂ) * ((U (z - w) - W1 (z - w) : ℝ) : ℂ)
        + ((χ w : ℝ) : ℂ) * ((W1 (z - w) : ℝ) : ℂ))
      = (∫ w : E3, ((χ w : ℝ) : ℂ) * ((U (z - w) - W1 (z - w) : ℝ) : ℂ))
        + (∫ w : E3, ((χ w : ℝ) : ℂ) * ((W1 (z - w) : ℝ) : ℂ)) :=
    MeasureTheory.integral_add hCU1 hW1int
  have hABC : (∫ w : E3, (((χ w : ℝ) : ℂ) * ((U (z - w) - W1 (z - w) : ℝ) : ℂ)
        + ((χ w : ℝ) : ℂ) * ((W1 (z - w) : ℝ) : ℂ)) + ((χ w : ℝ) : ℂ) * T w)
      = (∫ w : E3, ((χ w : ℝ) : ℂ) * ((U (z - w) - W1 (z - w) : ℝ) : ℂ)
          + ((χ w : ℝ) : ℂ) * ((W1 (z - w) : ℝ) : ℂ)) + (∫ w : E3, ((χ w : ℝ) : ℂ) * T w) :=
    MeasureTheory.integral_add hAB hTint
  have hIntMain : (∫ w : E3, ((χ w : ℝ) : ℂ)
        * (∑' d : Fin 3 → ℤ, ((U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)))
      = (∫ w : E3, ((χ w : ℝ) : ℂ) * ((U (z - w) - W1 (z - w) : ℝ) : ℂ))
        + (∫ w : E3, ((χ w : ℝ) : ℂ) * ((W1 (z - w) : ℝ) : ℂ))
        + (∫ w : E3, ((χ w : ℝ) : ℂ) * T w) := by
    calc (∫ w : E3, ((χ w : ℝ) : ℂ)
          * (∑' d : Fin 3 → ℤ, ((U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)))
        = (∫ w : E3, ((χ w : ℝ) : ℂ) * ((U (z - w) - W1 (z - w) : ℝ) : ℂ)
            + ((χ w : ℝ) : ℂ) * ((W1 (z - w) : ℝ) : ℂ)) + (∫ w : E3, ((χ w : ℝ) : ℂ) * T w) :=
          hstep.trans hABC
      _ = ((∫ w : E3, ((χ w : ℝ) : ℂ) * ((U (z - w) - W1 (z - w) : ℝ) : ℂ))
            + (∫ w : E3, ((χ w : ℝ) : ℂ) * ((W1 (z - w) : ℝ) : ℂ)))
          + (∫ w : E3, ((χ w : ℝ) : ℂ) * T w) := by rw [hAB2]
  -- ## the flip of the `W₁` term
  have hflip : (∫ y : E3, ((χ y : ℝ) : ℂ) * ((W1 (y - z) : ℝ) : ℂ))
      = ∫ w : E3, ((χ w : ℝ) : ℂ) * ((W1 (z - w) : ℝ) : ℂ) :=
    chiLam_W1fun_integral_flip (ℓ := ℓ) (W1 := W1) hev z
  -- ## the `d ≠ 0` sum is the real `tsum` of the target
  have hD : (∫ w : E3, ((χ w : ℝ) : ℂ) * T w)
      = ∫ w : E3, ((χ w : ℝ) : ℂ)
          * ((∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℝ)
              else U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have hTw : T w = ((∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℝ)
        else U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ) := by
      show (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ)
          else ((U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
        = ((∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℝ)
            else U (z - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)
      rw [Complex.ofReal_tsum]
      exact tsum_congr (fun d => by by_cases hd : d = 0 <;> simp [hd])
    simp only [hTw]
  rw [hK, hIntMain, hD, hflip]
  ring

end Work.BoseBoxFock.PCFU
