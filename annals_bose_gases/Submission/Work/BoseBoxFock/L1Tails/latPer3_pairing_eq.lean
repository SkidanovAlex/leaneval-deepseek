import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.L1Tails.DefsC
import Submission.Work.BoseBoxFock.aesm_prod_comp_sub
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-! ## Elementary lattice lemmas -/

lemma latPair_icongr {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : α → E} (h : ∀ a, f a = g a) :
    (∫ a, f a ∂μ) = ∫ a, g a ∂μ :=
  integral_congr_ae (Eventually.of_forall h)

lemma latPair_norm_C (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = ‖r‖ := by simp

lemma latPair_latVec_neg (m : Fin 3 → ℤ) : latVec (-m) = -latVec m := by
  ext i; simp [latVec]

lemma latPair_norm_sub_le {ℓ : ℝ} (hℓ : 0 < ℓ) {w y : E3}
    (hw : w ∈ Work.BoseK15.corpusBox.boxL ℓ) (hy : y ∈ Work.BoseK15.corpusBox.boxL ℓ) :
    ‖w - y‖ ≤ Real.sqrt 3 * ℓ := by
  rw [corpusBox_boxL_eq_cell hℓ] at hw hy
  rw [Work.BoseFixR.mem_cell] at hw hy
  rw [EuclideanSpace.norm_eq]
  have h3 : ∀ i : Fin 3, ‖(w - y).ofLp i‖ ^ 2 ≤ ℓ ^ 2 := by
    intro i
    have hsub : (w - y).ofLp i = w.ofLp i - y.ofLp i := rfl
    have hle : ‖(w - y).ofLp i‖ ≤ ℓ := by
      rw [Real.norm_eq_abs, hsub]
      calc |w.ofLp i - y.ofLp i| ≤ |w.ofLp i| + |y.ofLp i| := abs_sub _ _
        _ ≤ ℓ / 2 + ℓ / 2 := add_le_add (hw i) (hy i)
        _ = ℓ := by ring
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  have h2 : ∑ i : Fin 3, ‖(w - y).ofLp i‖ ^ 2 ≤ 3 * ℓ ^ 2 := by
    calc ∑ i : Fin 3, ‖(w - y).ofLp i‖ ^ 2 ≤ ∑ _i : Fin 3, ℓ ^ 2 :=
          Finset.sum_le_sum (fun i _ => h3 i)
      _ = 3 * ℓ ^ 2 := by simp [Finset.sum_const]
  calc Real.sqrt (∑ i : Fin 3, ‖(w - y).ofLp i‖ ^ 2) ≤ Real.sqrt (3 * ℓ ^ 2) :=
        Real.sqrt_le_sqrt h2
    _ = Real.sqrt 3 * ℓ := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_sq hℓ.le]

lemma latPair_boxL_isCompact (ℓ : ℝ) : IsCompact (Work.BoseK15.corpusBox.boxL ℓ) := by
  have h := Work.BoseB4.isCompact_unitCell.image (continuous_const_smul (ℓ : ℝ))
  rwa [Set.image_smul] at h

/-! ## The periodisation as a finite sum with the minus sign -/

lemma latPair_latPer_eq_sum_neg {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWs : ∀ x, R < ‖x‖ → W x = 0) {z : E3} (hz : ‖z‖ ≤ Real.sqrt 3 * ℓ) :
    LatFourier.latPer ℓ W z
      = ∑ m ∈ LatFourier.latFinSet ℓ R, (W (z - ℓ • latVec m) : ℂ) := by
  rw [LatFourier.latPer]
  have hneg : ∀ m : Fin 3 → ℤ,
      (W (z + ℓ • latVec (-m)) : ℂ) = (W (z - ℓ • latVec m) : ℂ) := by
    intro m
    have h : z + ℓ • latVec (-m) = z - ℓ • latVec m := by
      rw [latPair_latVec_neg, smul_neg]; abel
    rw [h]
  have hkey : (∑' m : Fin 3 → ℤ, (W (z + ℓ • latVec m) : ℂ))
      = ∑' m : Fin 3 → ℤ, (W (z - ℓ • latVec m) : ℂ) := by
    calc ∑' m : Fin 3 → ℤ, (W (z + ℓ • latVec m) : ℂ)
        = ∑' m : Fin 3 → ℤ, (W (z + ℓ • latVec (-m)) : ℂ) :=
          (Equiv.tsum_eq (Equiv.neg (Fin 3 → ℤ))
            (fun m : Fin 3 → ℤ => (W (z + ℓ • latVec m) : ℂ))).symm
      _ = ∑' m : Fin 3 → ℤ, (W (z - ℓ • latVec m) : ℂ) := tsum_congr hneg
  rw [hkey]
  refine tsum_eq_sum (s := LatFourier.latFinSet ℓ R) (fun m hm => ?_)
  have hnot : (R + Real.sqrt 3 * ℓ) / ℓ < ‖latVec m‖ := by
    rw [← not_le]
    intro hc
    exact hm ((LatFourier.mem_latFinSet).mpr hc)
  have h5 : ‖ℓ • latVec m‖ = ℓ * ‖latVec m‖ := LatFourier.latVec_norm_smul ℓ hℓ.le m
  have hgt : R < ‖z - ℓ • latVec m‖ := by
    have h2 : ‖ℓ • latVec m‖ ≤ ‖z - ℓ • latVec m‖ + ‖z‖ := by
      calc ‖ℓ • latVec m‖ = ‖-(ℓ • latVec m)‖ := (norm_neg _).symm
        _ = ‖(z - ℓ • latVec m) - z‖ := by congr 1; abel
        _ ≤ ‖z - ℓ • latVec m‖ + ‖z‖ := norm_sub_le _ _
    have h4 : R + Real.sqrt 3 * ℓ < ℓ * ‖latVec m‖ := by
      rw [div_lt_iff₀ hℓ] at hnot
      linarith [hnot]
    linarith
  rw [hWs _ hgt, Complex.ofReal_zero]

lemma latPair_latPer3_eq_sum_neg {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWs : ∀ x, R < ‖x‖ → W x = 0) {z : E3} (hz : ‖z‖ ≤ Real.sqrt 3 * ℓ) :
    Work.BoseBoxFock.latPer3 ℓ W z
      = ((ℓ ^ 3 : ℝ) : ℂ)
        * ∑ m ∈ LatFourier.latFinSet ℓ R, (W (z - ℓ • latVec m) : ℂ) := by
  rw [Work.BoseBoxFock.latPer3, latPair_latPer_eq_sum_neg hℓ hWs hz]

/-! ## The folded kernel -/

lemma latPair_foldH_eq_zero_of_norm_gt {ℓ : ℝ} (hℓ : 0 < ℓ) {H : E3 → E3 → ℂ}
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ)
    {z : E3} (hz : Real.sqrt 3 * ℓ < ‖z‖) : foldH H z = 0 := by
  rw [foldH]
  have hzero : ∀ y : E3, H (z + y) y = 0 := by
    intro y
    by_contra hne
    obtain ⟨hw, hy⟩ := hHs (z + y) y hne
    have hle : ‖z‖ ≤ Real.sqrt 3 * ℓ := by
      have hzeq : z = (z + y) - y := by abel
      rw [hzeq]
      exact latPair_norm_sub_le hℓ hw hy
    linarith
  rw [show (fun y : E3 => H (z + y) y) = fun _ => (0 : ℂ) from funext hzero]
  simp

lemma latPair_exists_bound_H {ℓ : ℝ} {H : E3 → E3 → ℂ}
    (hHc : Continuous (Function.uncurry H))
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w y, ‖H w y‖ ≤ M := by
  have hBc : IsCompact (Work.BoseK15.corpusBox.boxL ℓ) := latPair_boxL_isCompact ℓ
  obtain ⟨M, hM⟩ := (hBc.prod hBc).exists_bound_of_continuousOn hHc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun w y => ?_⟩
  by_cases h : H w y = 0
  · rw [h]; simp
  · obtain ⟨hw, hy⟩ := hHs w y h
    exact le_trans (hM (w, y) ⟨hw, hy⟩) (le_max_left _ _)

lemma latPair_integrable_indicator_boxL (ℓ : ℝ) :
    Integrable (fun y : E3 =>
      (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) y) volume := by
  have hBc : IsCompact (Work.BoseK15.corpusBox.boxL ℓ) := latPair_boxL_isCompact ℓ
  rw [integrable_indicator_iff hBc.isClosed.measurableSet]
  exact integrableOn_const hBc.measure_lt_top.ne (by simp)

/-! ## The main theorem -/

/-- The fold/periodisation identity for the `χχ`-pairing: the pairing of `latPer3 ℓ W` (the
periodisation of the `L¹` weight `W`) against a smooth box-supported kernel `H` equals `ℓ^3` times
the pairing of `W` against the periodisation of the folded kernel `foldH H u = ∫_y H (u+y) y`.
Route: `latPer3 ℓ W z = ℓ^3 Σ'_m W (z + ℓ•m)` is a finite sum on the relevant range (choose the
finite set of `m` with `‖ℓ•m‖ ≤ R + √3 ℓ` and use `tsum_eq_sum`), so the double integral is a
finite sum of `∫∫ W (w-y+ℓ•m) H w y`; substitute `u = w - y + ℓ•m` (a shear of determinant one,
`MeasureTheory.MeasurePreserving` of `(w,y) ↦ (w-y+ℓ•m, y)`) and resum (`tsum` over the symmetric
finite set, reindexing `m ↦ -m`). -/
theorem latPer3_pairing_eq {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W) (hWs : ∀ x : EuclideanSpace ℝ (Fin 3), R ≤ ‖x‖ → W x = 0)
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H))
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ) :
    (∫ w, ∫ y, Work.BoseBoxFock.latPer3 ℓ W (w - y) * H w y)
      = (ℓ ^ 3 : ℂ) * ∫ z, ((W z : ℝ) : ℂ)
          * Work.BoseBoxFock.L1Tails.latPerC ℓ (Work.BoseBoxFock.L1Tails.foldH H) z := by
  classical
  have hHc : Continuous (Function.uncurry H) := hH.continuous
  have hWs' : ∀ x : E3, R < ‖x‖ → W x = 0 := fun x hx => hWs x hx.le
  obtain ⟨M, hM0, hM⟩ := latPair_exists_bound_H (H := H) hHc hHs
  set f : E3 → ℂ := Work.BoseBoxFock.latPer3 ℓ W with hf
  set F : E3 → ℂ := foldH H with hF
  -- ## a uniform bound for `F`
  obtain ⟨CF, hCF0, hCF⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E3, ‖F z‖ ≤ C := by
    refine ⟨max (∫ y, M * (Work.BoseK15.corpusBox.boxL ℓ).indicator
      (fun _ => (1 : ℝ)) y) 0, le_max_right _ _, fun z => ?_⟩
    have hInt : Integrable (fun y : E3 => M *
        (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) y) volume :=
      (latPair_integrable_indicator_boxL ℓ).const_mul M
    have h1 : ‖F z‖ ≤ ∫ y, M *
        (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) y := by
      rw [hF, foldH]
      calc ‖∫ y, H (z + y) y‖ ≤ ∫ y, ‖H (z + y) y‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ y, M * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) y := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) hInt ?_
            filter_upwards with y
            by_cases hy : y ∈ Work.BoseK15.corpusBox.boxL ℓ
            · rw [Set.indicator_of_mem hy, mul_one]; exact hM (z + y) y
            · rw [Set.indicator_of_notMem hy, mul_zero]
              have hz : H (z + y) y = 0 := by
                by_contra hne
                exact hy (hHs (z + y) y hne).2
              rw [hz, norm_zero]
    exact le_trans h1 (le_max_left _ _)
  -- ## `F` is a.e. strongly measurable
  have hFasm : AEStronglyMeasurable F volume := by
    have hpair : Continuous (fun p : E3 × E3 => (p.1, p.1 - p.2)) := by fun_prop
    have hsm : StronglyMeasurable (fun z : E3 => ∫ x : E3, H x (x - z)) :=
      ((hHc.comp hpair).stronglyMeasurable).integral_prod_left'
    have heq : ∀ z : E3, (∫ x : E3, H x (x - z)) = F z := by
      intro z
      rw [hF, foldH]
      have h := integral_add_left_eq_self (μ := volume) (fun w : E3 => H w (w - z)) z
      have hfun : (fun y : E3 => (fun w : E3 => H w (w - z)) (z + y))
          = fun y : E3 => H (z + y) y := by
        funext y
        show H (z + y) (z + y - z) = H (z + y) y
        rw [show z + y - z = y from by abel]
      rw [hfun] at h
      exact h.symm
    exact hsm.aestronglyMeasurable.congr (Eventually.of_forall fun z => heq z)
  -- ## joint integrability of the pair integrand
  have hJoint : Integrable (fun p : E3 × E3 => f p.2 * H p.1 (p.1 - p.2))
      (volume.prod volume) := by
    have hpair : Continuous (fun p : E3 × E3 => (p.1, p.1 - p.2)) := by fun_prop
    have hcont2 : Continuous (fun p : E3 × E3 => H p.1 (p.1 - p.2)) := hHc.comp hpair
    have hpw : ∀ p : E3 × E3, f p.2 * H p.1 (p.1 - p.2)
        = ∑ m ∈ LatFourier.latFinSet ℓ R,
            ((ℓ ^ 3 : ℝ) : ℂ) * ((W (p.2 - ℓ • latVec m) : ℂ) * H p.1 (p.1 - p.2)) := by
      intro p
      by_cases hHp : H p.1 (p.1 - p.2) = 0
      · rw [hHp, mul_zero]
        exact (Finset.sum_eq_zero (fun m _ => by simp)).symm
      · obtain ⟨hw, hy⟩ := hHs p.1 (p.1 - p.2) hHp
        have hz : ‖p.2‖ ≤ Real.sqrt 3 * ℓ := by
          have hEq : p.2 = p.1 - (p.1 - p.2) := by abel
          rw [hEq]; exact latPair_norm_sub_le hℓ hw hy
        rw [hf, latPair_latPer3_eq_sum_neg hℓ hWs' hz, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        ring
    rw [show (fun p : E3 × E3 => f p.2 * H p.1 (p.1 - p.2))
        = fun p : E3 × E3 => ∑ m ∈ LatFourier.latFinSet ℓ R,
            ((ℓ ^ 3 : ℝ) : ℂ) * ((W (p.2 - ℓ • latVec m) : ℂ) * H p.1 (p.1 - p.2))
        from funext hpw]
    refine integrable_finsetSum _ (fun m _ => ?_)
    set a : E3 := ℓ • latVec m with ha
    have hmaj : Integrable (fun p : E3 × E3 =>
        (‖ℓ ^ 3‖ * M * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) p.1)
          * ‖W (p.2 - a)‖) (volume.prod volume) :=
      Integrable.mul_prod
        ((latPair_integrable_indicator_boxL ℓ).const_mul (‖ℓ ^ 3‖ * M))
        ((hW.comp_sub_right a).norm)
    refine Integrable.mono' hmaj ?_ ?_
    · have hWa : AEStronglyMeasurable (fun z : E3 => W (z - a)) volume :=
        hW.aestronglyMeasurable.comp_quasiMeasurePreserving
          (measurePreserving_add_right volume (-a)).quasiMeasurePreserving
      have h1 : AEStronglyMeasurable (fun p : E3 × E3 => ((W (p.2 - a) : ℝ) : ℂ))
          (volume.prod volume) :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable (hWa.comp_snd)
      have h2 : AEStronglyMeasurable (fun p : E3 × E3 => H p.1 (p.1 - p.2))
          (volume.prod volume) := hcont2.stronglyMeasurable.aestronglyMeasurable
      exact (h1.mul h2).const_mul (((ℓ ^ 3 : ℝ) : ℂ))
    · filter_upwards with p
      have hHp : ‖H p.1 (p.1 - p.2)‖ ≤ M *
          (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) p.1 := by
        by_cases hp1 : p.1 ∈ Work.BoseK15.corpusBox.boxL ℓ
        · rw [Set.indicator_of_mem hp1, mul_one]; exact hM p.1 (p.1 - p.2)
        · rw [Set.indicator_of_notMem hp1, mul_zero]
          have hz : H p.1 (p.1 - p.2) = 0 := by
            by_contra hne
            exact hp1 (hHs p.1 (p.1 - p.2) hne).1
          rw [hz, norm_zero]
      calc ‖(((ℓ ^ 3 : ℝ) : ℂ)) * ((W (p.2 - a) : ℂ) * H p.1 (p.1 - p.2))‖
          = ‖ℓ ^ 3‖ * (‖W (p.2 - a)‖ * ‖H p.1 (p.1 - p.2)‖) := by
            simp only [norm_mul, latPair_norm_C]
        _ ≤ ‖ℓ ^ 3‖ * (‖W (p.2 - a)‖ * (M *
              (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) p.1)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHp (norm_nonneg _))
              (norm_nonneg _)
        _ = (‖ℓ ^ 3‖ * M *
              (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) p.1)
              * ‖W (p.2 - a)‖ := by ring
  -- ## integrability of the `z`-terms
  have hIntTerm : ∀ m : Fin 3 → ℤ,
      Integrable (fun z : E3 => (W (z - ℓ • latVec m) : ℂ) * F z) volume := by
    intro m
    set a : E3 := ℓ • latVec m with ha
    have hmaj : Integrable (fun z : E3 => CF * ‖W (z - a)‖) volume :=
      (hW.comp_sub_right a).norm.const_mul CF
    refine Integrable.mono' hmaj ?_ ?_
    · have hWa : AEStronglyMeasurable (fun z : E3 => W (z - a)) volume :=
        hW.aestronglyMeasurable.comp_quasiMeasurePreserving
          (measurePreserving_add_right volume (-a)).quasiMeasurePreserving
      exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hWa).mul hFasm
    · filter_upwards with z
      calc ‖(W (z - a) : ℂ) * F z‖ = ‖W (z - a)‖ * ‖F z‖ := by
            rw [norm_mul, latPair_norm_C]
        _ ≤ ‖W (z - a)‖ * CF := mul_le_mul_of_nonneg_left (hCF z) (norm_nonneg _)
        _ = CF * ‖W (z - a)‖ := mul_comm _ _
  have hIntTerm2 : ∀ m : Fin 3 → ℤ,
      Integrable (fun u : E3 => (W u : ℂ) * F (u + ℓ • latVec m)) volume := by
    intro m
    have hmaj : Integrable (fun u : E3 => CF * ‖W u‖) volume := hW.norm.const_mul CF
    refine Integrable.mono' hmaj ?_ ?_
    · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hW.aestronglyMeasurable).mul
        (hFasm.comp_quasiMeasurePreserving
          (measurePreserving_add_right volume (ℓ • latVec m)).quasiMeasurePreserving)
    · filter_upwards with u
      calc ‖(W u : ℂ) * F (u + ℓ • latVec m)‖ = ‖W u‖ * ‖F (u + ℓ • latVec m)‖ := by
            rw [norm_mul, latPair_norm_C]
        _ ≤ ‖W u‖ * CF := mul_le_mul_of_nonneg_left (hCF (u + ℓ • latVec m)) (norm_nonneg _)
        _ = CF * ‖W u‖ := mul_comm _ _
  -- ## the finite-sum algebra
  have hdist : (∫ z : E3,
        (∑ m ∈ LatFourier.latFinSet ℓ R, (W (z - ℓ • latVec m) : ℂ)) * F z)
      = ∑ m ∈ LatFourier.latFinSet ℓ R,
          ∫ z : E3, (W (z - ℓ • latVec m) : ℂ) * F z := by
    rw [← integral_finsetSum (s := LatFourier.latFinSet ℓ R)
      (f := fun m z => (W (z - ℓ • latVec m) : ℂ) * F z)]
    · exact latPair_icongr (fun z => by rw [Finset.sum_mul])
    · intro m _
      exact hIntTerm m
  have hsub : (∑ m ∈ LatFourier.latFinSet ℓ R,
        ∫ z : E3, (W (z - ℓ • latVec m) : ℂ) * F z)
      = ∑ m ∈ LatFourier.latFinSet ℓ R,
          ∫ u : E3, (W u : ℂ) * F (u + ℓ • latVec m) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have h := integral_add_left_eq_self (μ := volume)
      (fun u : E3 => (W u : ℂ) * F (u + ℓ • latVec m)) (-(ℓ • latVec m))
    have hfun : (fun x : E3 => (fun u : E3 => (W u : ℂ) * F (u + ℓ • latVec m))
          ((-(ℓ • latVec m)) + x)) = fun x : E3 => (W (x - ℓ • latVec m) : ℂ) * F x := by
      funext x
      show (W ((-(ℓ • latVec m)) + x) : ℂ) * F (((-(ℓ • latVec m)) + x) + ℓ • latVec m)
          = (W (x - ℓ • latVec m) : ℂ) * F x
      rw [show (-(ℓ • latVec m)) + x = x - ℓ • latVec m from by abel,
        show (x - ℓ • latVec m) + ℓ • latVec m = x from by abel]
    rw [hfun] at h
    exact h
  have hredist : (∑ m ∈ LatFourier.latFinSet ℓ R,
        ∫ u : E3, (W u : ℂ) * F (u + ℓ • latVec m))
      = ∫ u : E3, (W u : ℂ)
          * (∑ m ∈ LatFourier.latFinSet ℓ R, F (u + ℓ • latVec m)) := by
    rw [← integral_finsetSum (s := LatFourier.latFinSet ℓ R)
      (f := fun m u => (W u : ℂ) * F (u + ℓ • latVec m))]
    · exact latPair_icongr (fun u => by rw [Finset.mul_sum])
    · intro m _
      exact hIntTerm2 m
  have hper : (∫ u : E3, (W u : ℂ)
        * (∑ m ∈ LatFourier.latFinSet ℓ R, F (u + ℓ • latVec m)))
      = ∫ u : E3, (W u : ℂ) * latPerC ℓ F u := by
    refine latPair_icongr (fun u => ?_)
    by_cases hu : W u = 0
    · rw [hu]; simp
    · have hnorm : ‖u‖ < R := by
        by_contra hc
        rw [not_lt] at hc
        exact hu (hWs u hc)
      have hsum : (∑ m ∈ LatFourier.latFinSet ℓ R, F (u + ℓ • latVec m))
          = latPerC ℓ F u := by
        rw [latPerC]
        refine (tsum_eq_sum (s := LatFourier.latFinSet ℓ R) (fun m hm => ?_)).symm
        have hnot : (R + Real.sqrt 3 * ℓ) / ℓ < ‖latVec m‖ := by
          rw [← not_le]
          intro hc
          exact hm ((LatFourier.mem_latFinSet).mpr hc)
        have h4 : R + Real.sqrt 3 * ℓ < ℓ * ‖latVec m‖ := by
          rw [div_lt_iff₀ hℓ] at hnot
          linarith [hnot]
        have h5 : ‖ℓ • latVec m‖ = ℓ * ‖latVec m‖ :=
          LatFourier.latVec_norm_smul ℓ hℓ.le m
        have hgt : Real.sqrt 3 * ℓ < ‖u + ℓ • latVec m‖ := by
          have h2 : ‖ℓ • latVec m‖ ≤ ‖u + ℓ • latVec m‖ + ‖u‖ := by
            calc ‖ℓ • latVec m‖ = ‖(u + ℓ • latVec m) - u‖ := by congr 1; abel
              _ ≤ ‖u + ℓ • latVec m‖ + ‖u‖ := norm_sub_le _ _
          linarith
        exact latPair_foldH_eq_zero_of_norm_gt hℓ hHs hgt
      rw [hsum]
  have hpoint : ∀ z : E3, f z * F z = ((ℓ ^ 3 : ℝ) : ℂ)
      * (∑ m ∈ LatFourier.latFinSet ℓ R, (W (z - ℓ • latVec m) : ℂ)) * F z := by
    intro z
    by_cases hz : ‖z‖ ≤ Real.sqrt 3 * ℓ
    · rw [hf, latPair_latPer3_eq_sum_neg hℓ hWs' hz]
    · have hz' : Real.sqrt 3 * ℓ < ‖z‖ := lt_of_not_ge hz
      rw [hf, hF, latPair_foldH_eq_zero_of_norm_gt hℓ hHs hz']
      simp
  have hA : (∫ z, f z * F z)
      = ∫ z, ((ℓ ^ 3 : ℝ) : ℂ)
          * (∑ m ∈ LatFourier.latFinSet ℓ R, (W (z - ℓ • latVec m) : ℂ)) * F z :=
    latPair_icongr hpoint
  have hB : (∫ z, ((ℓ ^ 3 : ℝ) : ℂ)
        * (∑ m ∈ LatFourier.latFinSet ℓ R, (W (z - ℓ • latVec m) : ℂ)) * F z)
      = ((ℓ ^ 3 : ℝ) : ℂ) * ∫ z,
          (∑ m ∈ LatFourier.latFinSet ℓ R, (W (z - ℓ • latVec m) : ℂ)) * F z := by
    simp only [mul_assoc]
    rw [integral_const_mul]
  have hC : ((ℓ ^ 3 : ℝ) : ℂ) * (∫ z : E3,
        (∑ m ∈ LatFourier.latFinSet ℓ R, (W (z - ℓ • latVec m) : ℂ)) * F z)
      = ((ℓ ^ 3 : ℝ) : ℂ) * (∑ m ∈ LatFourier.latFinSet ℓ R,
          ∫ z, (W (z - ℓ • latVec m) : ℂ) * F z) := by
    rw [hdist]
  have hD : ((ℓ ^ 3 : ℝ) : ℂ) * (∑ m ∈ LatFourier.latFinSet ℓ R,
        ∫ z, (W (z - ℓ • latVec m) : ℂ) * F z)
      = ((ℓ ^ 3 : ℝ) : ℂ) * (∑ m ∈ LatFourier.latFinSet ℓ R,
          ∫ u, (W u : ℂ) * F (u + ℓ • latVec m)) := by
    rw [hsub]
  have hE : ((ℓ ^ 3 : ℝ) : ℂ) * (∑ m ∈ LatFourier.latFinSet ℓ R,
        ∫ u, (W u : ℂ) * F (u + ℓ • latVec m))
      = ((ℓ ^ 3 : ℝ) : ℂ) * ∫ u, (W u : ℂ)
          * (∑ m ∈ LatFourier.latFinSet ℓ R, F (u + ℓ • latVec m)) := by
    rw [hredist]
  have hF' : ((ℓ ^ 3 : ℝ) : ℂ) * (∫ u : E3, (W u : ℂ)
        * (∑ m ∈ LatFourier.latFinSet ℓ R, F (u + ℓ • latVec m)))
      = ((ℓ ^ 3 : ℝ) : ℂ) * ∫ u, (W u : ℂ) * latPerC ℓ F u := by
    rw [hper]
  have hmain : (∫ z, f z * F z)
      = ((ℓ ^ 3 : ℝ) : ℂ) * ∫ z, (W z : ℂ) * latPerC ℓ F z :=
    hA.trans (hB.trans (hC.trans (hD.trans (hE.trans hF'))))
  -- ## the substitutions
  have hstep1 : ∀ w : E3, (∫ y, f (w - y) * H w y) = ∫ z, f z * H w (w - z) := by
    intro w
    have h := integral_sub_left_eq_self (fun z : E3 => f z * H w (w - z))
      (volume : Measure E3) w
    have hfun : (fun y : E3 => (fun z : E3 => f z * H w (w - z)) (w - y))
        = fun y : E3 => f (w - y) * H w y := by
      funext y
      show f (w - y) * H w (w - (w - y)) = f (w - y) * H w y
      rw [show w - (w - y) = y from by abel]
    rw [hfun] at h
    exact h
  have hstep3 : (∫ z, ∫ w, f z * H w (w - z)) = ∫ z, f z * F z := by
    refine latPair_icongr (fun z => ?_)
    rw [integral_const_mul]
    congr 1
    rw [hF, foldH]
    have h := integral_add_left_eq_self (μ := volume) (fun w : E3 => H w (w - z)) z
    have hfun : (fun y : E3 => (fun w : E3 => H w (w - z)) (z + y))
        = fun y : E3 => H (z + y) y := by
      funext y
      show H (z + y) (z + y - z) = H (z + y) y
      rw [show z + y - z = y from by abel]
    rw [hfun] at h
    exact h.symm
  have hchain : (∫ w, ∫ y, f (w - y) * H w y)
      = ((ℓ ^ 3 : ℝ) : ℂ) * ∫ z, (W z : ℂ) * latPerC ℓ F z := by
    calc (∫ w, ∫ y, f (w - y) * H w y)
        = ∫ w, ∫ z, f z * H w (w - z) := latPair_icongr hstep1
      _ = ∫ z, ∫ w, f z * H w (w - z) := integral_integral_swap hJoint
      _ = ∫ z, f z * F z := hstep3
      _ = ((ℓ ^ 3 : ℝ) : ℂ) * ∫ z, (W z : ℂ) * latPerC ℓ F z := hmain
  rw [hf, hF] at hchain
  have hcoe : ((ℓ ^ 3 : ℝ) : ℂ) = (ℓ ^ 3 : ℂ) := by
    first | rfl | rw [Complex.ofReal_pow] | push_cast | simp
  rw [hcoe] at hchain
  exact hchain

end Work.BoseBoxFock.L1Tails
