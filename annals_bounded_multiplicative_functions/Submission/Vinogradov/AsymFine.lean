/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.Projection
import Submission.Vinogradov.UncertaintyBlock
import Submission.Vinogradov.TentCalc
import Submission.Commons.Measure.Integral.lintegral_moving_ball
import Submission.Commons.Analysis.Convolution.ball_tent_lintegral_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# GLYZ Lemma 3.8 (lower degree decoupling): the assembly

This module hosts the proof of `AsymDecFine` (GLYZ arXiv:1912.09798 Lemma 3.8, equation
(3.10)), the lower-degree decoupling step of §3.4.  The plan (ROADMAP sessions 49 and 51) is:

1. **the restriction to a translate of `H`** — the block sum restricted to `H + z` belongs to
   the class of a plate of the projected curve (this module, section 2);
2. the moving-ball Fubini identity `∫ F = ∫_z ⨍_{B_H(z,r)} F` (the commons
   `Commons.Measure.Integral.lintegral_moving_ball`);
3. the sup comparison on the ball (`TentCalc.phiPlate_shift_ball_le`);
4. the commutation of the `H`-convolution with the plate convolution
   (`LowerDegree.lintegral_ball_convPow_swap`);
5. Corollary 3.7 (`LocalisedDecoupling.curveDecLoc_of_curveDec`) on each translate, followed by
   Minkowski;
6. the tent comparisons — Lemma A.1 (`TentCalc.phiPlate_conv_le`) and Lemma A.2.

-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-! ## 1. Elementary facts about the dyadic pieces -/

lemma pieceCenter_mem_Icc (m : ℕ) (hm : 1 ≤ m) (j : Fin m) :
    pieceCenter m j ∈ Set.Icc (0 : ℝ) 1 := by
  rw [pieceCenter]
  constructor
  · positivity
  · rw [div_le_one (by exact_mod_cast hm)]
    have h : (j.val : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast j.isLt
    linarith

lemma plateHalf_two_le_one {m : ℕ} (hm : 2 ≤ m) : 8 * plateHalf m ≤ 1 := by
  rw [plateHalf_eq]
  have hm2 : (4 : ℝ) ≤ (2 : ℝ) ^ m := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hpos : (0 : ℝ) < 2 * ((2 ^ m : ℕ) : ℝ) := by positivity
  rw [one_div, mul_inv_le_iff₀ hpos]
  push_cast
  nlinarith [hm2]

/-! ## 2. The restriction of a block sum to a translate of `H` -/

/-- **The block sum restricted to a translate `H + z` lies in the class of the projected
curve.**  The sum `∑_{i ∈ blkFin N b' J} f_i` is in the class of the enlarged coarse plate
(`isFourierRep_sum_blkFin`), restriction to the translate `H + z` maps that class to the class
over `projMapLin '' plate` (`isFourierRep_proj_map`), and that plate is contained in a constant
multiple of a plate of the projected curve (`projMapLin_image_plate_subset'`) — provided the
block `J` is separated from `ξ'`. -/
theorem exists_isFourierRep_restrict_translate {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) :
    ∃ lam : ℝ, 1 ≤ lam ∧ ∀ {N b' : ℕ}, 2 ≤ b' → b' ≤ N → ∀ (J : Fin (2 ^ b')) (z : E k)
      (f : Fin (2 ^ N) → E k → ℂ),
      (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) →
      1 / 4 ≤ |pieceCenter (2 ^ b') J - ξ'| →
      IsFourierRep l
        (curvePlate l (projCurveDeriv k l (torsionVec k l hlk ξ'))
          (lam * (8 * plateHalf b')) (pieceCenter (2 ^ b') J))
        (fun y => ∑ i ∈ blkFin N b' J,
          f i (projEmbedLin k l (torsionVec k l hlk ξ') y + z)) := by
  obtain ⟨lam, hlam, hlam'⟩ := projMapLin_image_plate_subset' hl hlk ξ' hξ'
  refine ⟨lam, hlam, ?_⟩
  intro N b' hb' hb'N J z f hf hsep
  have hblk := isFourierRep_sum_blkFin hk hb' hb'N J f hf
  have hiso := isFourierRep_proj_map k l (torsionVec k l hlk ξ') z hblk
  refine hiso.mono ?_
  intro ξ hξ
  exact hlam' (8 * plateHalf b') (pieceCenter (2 ^ b') J)
    (mul_pos (by norm_num) (plateHalf_pos b'))
    (plateHalf_two_le_one hb')
    (pieceCenter_mem_Icc (2 ^ b') Nat.one_le_two_pow J)
    hsep hξ


/-! ## 3. The `H`-directions of the plate gauge are isotropic of size `δ^{k-l+1}‖w‖` -/

/-- **The gauge of the plate at a point of the translate `H` is isotropic in `‖w‖`.**  For
`δ = plateHalf m'` and `|c' - ξ'| ≤ δ` one has
`gauge (plateGaugeLin k δ c' (projEmbedLin k l b w)) ≤ C₀ δ^{k-l+1} ‖w‖`.

The point is that `δ^{k-l+1} = hBallR k l m'` is exactly the critical radius, so this says that
the *whole* `H`-ball of that radius is inside a fixed multiple of the polar plate — and, more
importantly, that the gauge is (up to a constant) the isotropic quantity `‖w‖/r`.  This is what
makes GLYZ's Lemma A.2 an *isotropic* convolution estimate, so no anisotropic reduction is
needed.  The two cases are the vanishing order (`norm_projMapLin_gammaDeriv_le`) for
`i + 1 ≤ k - l` and the crude bound (`norm_projMapLin_le` + `norm_gammaDeriv_le`) otherwise. -/
theorem gauge_plateGaugeLin_projEmbed_le_norm {k l : ℕ} (hk : 1 ≤ k) (hlk : l ≤ k)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (m' : ℕ) (c' : ℝ), c' ∈ Set.Icc (0 : ℝ) 1 →
      |c' - ξ'| ≤ plateHalf m' → ∀ w : E l,
      gauge k hk (plateGaugeLin k (plateHalf m') c'
        (projEmbedLin k l (torsionVec k l hlk ξ') w))
        ≤ C₀ * (plateHalf m') ^ (k - l + 1) * ‖w‖ := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := norm_projMapLin_gammaDeriv_le hlk hξ'
  refine ⟨max C₁ (Real.sqrt k * (k.factorial : ℝ)), le_trans hC₁pos.le (le_max_left _ _), ?_⟩
  intro m' c' hc' hsep w
  have hδ0 : 0 < plateHalf m' := plateHalf_pos m'
  have hδ1 : plateHalf m' ≤ 1 := plateHalf_le_one m'
  rw [gauge]
  refine Finset.sup'_le _ _ fun i _ => ?_
  rw [plateGaugeLin_apply]
  have hinner : ⟪projEmbedLin k l (torsionVec k l hlk ξ') w, gammaDeriv k (i.val + 1) c'⟫
      = ⟪w, projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (i.val + 1) c')⟫ :=
    inner_projEmbed_projMap k l (torsionVec k l hlk ξ') w _
  rw [hinner, abs_mul, abs_of_nonneg (pow_nonneg hδ0.le _)]
  have hstep : (plateHalf m') ^ (i.val + 1)
        * |⟪w, projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (i.val + 1) c')⟫|
      ≤ (plateHalf m') ^ (i.val + 1)
        * (‖w‖ * ‖projMapLin k l (torsionVec k l hlk ξ')
            (gammaDeriv k (i.val + 1) c')‖) :=
    mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (pow_nonneg hδ0.le _)
  have hkey : (plateHalf m') ^ (i.val + 1)
        * ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (i.val + 1) c')‖
      ≤ max C₁ (Real.sqrt k * (k.factorial : ℝ)) * (plateHalf m') ^ (k - l + 1) := by
    by_cases hcase : i.val + 1 ≤ k - l
    · have hb := hC₁ (i.val + 1) (by omega) hcase c' hc'
      have hdK : |c' - ξ'| ^ (k - l + 1 - (i.val + 1))
          ≤ (plateHalf m') ^ (k - l + 1 - (i.val + 1)) :=
        pow_le_pow_left₀ (abs_nonneg _) hsep _
      have hval : (i.val + 1) + (k - l + 1 - (i.val + 1)) = k - l + 1 := by omega
      have hpow : (plateHalf m') ^ (i.val + 1) * (plateHalf m') ^ (k - l + 1 - (i.val + 1))
          = (plateHalf m') ^ (k - l + 1) := by rw [← pow_add, hval]
      calc (plateHalf m') ^ (i.val + 1)
            * ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (i.val + 1) c')‖
          ≤ (plateHalf m') ^ (i.val + 1)
            * (C₁ * |c' - ξ'| ^ (k - l + 1 - (i.val + 1))) :=
              mul_le_mul_of_nonneg_left hb (pow_nonneg hδ0.le _)
        _ ≤ (plateHalf m') ^ (i.val + 1)
            * (C₁ * (plateHalf m') ^ (k - l + 1 - (i.val + 1))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdK hC₁pos.le)
                (pow_nonneg hδ0.le _)
        _ = C₁ * (plateHalf m') ^ (k - l + 1) := by rw [← hpow]; ring
        _ ≤ max C₁ (Real.sqrt k * (k.factorial : ℝ)) * (plateHalf m') ^ (k - l + 1) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hδ0.le _)
    · have hb : ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (i.val + 1) c')‖
          ≤ Real.sqrt k * (k.factorial : ℝ) :=
        le_trans (norm_projMapLin_le k l (orthonormal_torsionVec k l hlk ξ') _)
          (norm_gammaDeriv_le k (by rw [abs_le]; exact ⟨by linarith [hc'.1], hc'.2⟩) (i.val + 1))
      have hexp : k - l + 1 ≤ i.val + 1 := by omega
      have hpow : (plateHalf m') ^ (i.val + 1) ≤ (plateHalf m') ^ (k - l + 1) :=
        pow_le_pow_of_le_one hδ0.le hδ1 hexp
      calc (plateHalf m') ^ (i.val + 1)
            * ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (i.val + 1) c')‖
          ≤ (plateHalf m') ^ (k - l + 1) * (Real.sqrt k * (k.factorial : ℝ)) :=
            mul_le_mul hpow hb (norm_nonneg _) (pow_nonneg hδ0.le _)
        _ = (Real.sqrt k * (k.factorial : ℝ)) * (plateHalf m') ^ (k - l + 1) := by ring
        _ ≤ max C₁ (Real.sqrt k * (k.factorial : ℝ)) * (plateHalf m') ^ (k - l + 1) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hδ0.le _)
  calc (plateHalf m') ^ (i.val + 1)
        * |⟪w, projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (i.val + 1) c')⟫|
      ≤ (plateHalf m') ^ (i.val + 1)
        * (‖w‖ * ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (i.val + 1) c')‖) := hstep
    _ = ((plateHalf m') ^ (i.val + 1)
        * ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (i.val + 1) c')‖) * ‖w‖ := by ring
    _ ≤ (max C₁ (Real.sqrt k * (k.factorial : ℝ)) * (plateHalf m') ^ (k - l + 1)) * ‖w‖ :=
        mul_le_mul_of_nonneg_right hkey (norm_nonneg _)
    _ = max C₁ (Real.sqrt k * (k.factorial : ℝ)) * (plateHalf m') ^ (k - l + 1) * ‖w‖ := by ring


/-! ## 4. The moving-ball (Fubini) identity for the translate `H + z` -/

/-- `projEmbedLin` of an orthonormal family is an isometry. -/
lemma norm_projEmbedLin_eq {k l : ℕ} {b : Fin l → E k} (hb : Orthonormal ℝ b) (y : E l) :
    ‖projEmbedLin k l b y‖ = ‖y‖ := by
  have h1 : ‖projEmbedLin k l b y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    rw [inner_projEmbed_projMap, projMapLin_projEmbedLin k l hb y]
  nlinarith [norm_nonneg (projEmbedLin k l b y), norm_nonneg y]

/-- **The moving-ball identity** (GLYZ (3.11)): a full-space integral is the average, over the
translates of `H`, of the integral over the `H`-ball of radius `r`. -/
lemma lintegral_moving_ball_proj {k l : ℕ} (hlk : l ≤ k) {ξ' : ℝ} {r : ℝ} (hr : 0 < r)
    (F : E k → ℝ≥0∞) (hF : AEMeasurable F) :
    (∫⁻ z : E k, ∫⁻ w in Metric.ball (0 : E l) r,
        F (z + projEmbedLin k l (torsionVec k l hlk ξ') w))
      = ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal) * ∫⁻ x : E k, F x := by
  have h := Commons.Measure.Integral.lintegral_moving_ball k l
    (projEmbedLin k l (torsionVec k l hlk ξ'))
    (norm_projEmbedLin_eq (orthonormal_torsionVec k l hlk ξ')) hr F hF
  rw [h, ENNReal.ofReal_toReal (ne_of_lt (measure_ball_lt_top (μ := volume)))]



/-- The ball tent as an `ofReal` of the explicit real tent. -/
lemma ballTent_eq_ofReal (l : ℕ) (A : ℝ) (c : E l) {R : ℝ} (hR : 0 < R) (w : E l) :
    ballTent l A c R w
      = ENNReal.ofReal (((volume (Metric.ball c R)).toReal)⁻¹
          * (1 + Metric.infDist w (Metric.ball c R) / R) ^ (-A)) := by
  have hpos : 0 < (volume (Metric.ball c R)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos (μ := volume) c hR).ne'
      (measure_ball_lt_top (μ := volume)).ne
  rw [ballTent_apply, ← ENNReal.ofReal_inv_of_pos hpos, ← ENNReal.ofReal_mul (by positivity)]

/-- **GLYZ Lemma A.2 in the form consumed by §3.4.**  The convolution of the plate bump
`φ_{I'}` at level `m'` with the `L¹`-normalised ball bump of the critical `H`-ball
`r = hBallR k l m'` is dominated by `φ_{I'}` itself, pointwise, with a constant independent of
`m'`, `c'` and `y`. -/
theorem ballTent_conv_phiPlate_le {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) {A A' : ℝ} (hA : 0 < A)
    (hA' : A + (l : ℝ) < A') (Cφ : ℝ) (hCφ : 0 ≤ Cφ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m' : ℕ) (c' : ℝ), c' ∈ Set.Icc (0 : ℝ) 1 →
      |c' - ξ'| ≤ plateHalf m' → ∀ y : E k,
      (∫⁻ w : E l, ballTent l A' 0 (hBallR k l m') w
        * ENNReal.ofReal (phiPlate k hk (plateHalf m') c' A Cφ
            (y + projEmbedLin k l (torsionVec k l hlk ξ') w)))
        ≤ ENNReal.ofReal C * ENNReal.ofReal (phiPlate k hk (plateHalf m') c' A Cφ y) := by
  obtain ⟨C₀, hC₀, hC₀b⟩ := gauge_plateGaugeLin_projEmbed_le_norm hk hlk hξ'
  haveI : Inhabited (Fin l) := ⟨⟨0, hl⟩⟩
  haveI : Nontrivial (Fin l → ℝ) := Pi.nontrivial
  haveI : Nontrivial (E l) := inferInstance
  have hA'' : A + (Module.finrank ℝ (E l) : ℝ) < A' := by
    rw [finrank_euclideanSpace, Fintype.card_fin]; exact hA'
  obtain ⟨C', hC'pos, hC'b⟩ := Commons.Analysis.Convolution.ball_tent_lintegral_le (E := E l)
    A A' hA hA'' (max C₀ 1) (le_max_right _ _)
  refine ⟨C', hC'pos.le, fun m' c' hc' hsep y => ?_⟩
  have hδ0 : 0 < plateHalf m' := plateHalf_pos m'
  have hR0 : 0 < hBallR k l m' := hBallR_pos k l m'
  set r : ℝ := hBallR k l m' with hr
  set G : ℝ := gauge k hk (plateGaugeLin k (plateHalf m') c' y) with hG
  set C₁ : ℝ := max C₀ 1 with hC₁
  have hC₁1 : 1 ≤ C₁ := le_max_right _ _
  have hC₀le : C₀ ≤ C₁ := le_max_left _ _
  have hδr : (plateHalf m') ^ (k - l + 1) * r = 1 := by
    rw [hr, hBallR, inv_pow]
    exact mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt hδ0))
  -- the key pointwise comparison of the gauges
  have hgauge : ∀ w : E l, G - C₁ * ‖w‖ / r
      ≤ gauge k hk (plateGaugeLin k (plateHalf m') c'
          (y + projEmbedLin k l (torsionVec k l hlk ξ') w)) := by
    intro w
    have hgv := hC₀b m' c' hc' hsep w
    have hsub : gauge k hk (plateGaugeLin k (plateHalf m') c' y)
          - gauge k hk (plateGaugeLin k (plateHalf m') c'
              (projEmbedLin k l (torsionVec k l hlk ξ') w))
        ≤ gauge k hk (plateGaugeLin k (plateHalf m') c'
            (y + projEmbedLin k l (torsionVec k l hlk ξ') w)) := by
      have h3 : plateGaugeLin k (plateHalf m') c' y
          = plateGaugeLin k (plateHalf m') c'
              (y + projEmbedLin k l (torsionVec k l hlk ξ') w)
            - plateGaugeLin k (plateHalf m') c'
              (projEmbedLin k l (torsionVec k l hlk ξ') w) := by
        rw [map_add]; abel
      rw [h3]
      have h2 := gauge_sub_le k hk
        (plateGaugeLin k (plateHalf m') c' (y + projEmbedLin k l (torsionVec k l hlk ξ') w))
        (plateGaugeLin k (plateHalf m') c' (projEmbedLin k l (torsionVec k l hlk ξ') w))
      linarith
    have hEq : C₀ * ‖w‖ / r = C₀ * ((plateHalf m') ^ (k - l + 1) * ‖w‖) := by
      rw [div_eq_iff (ne_of_gt hR0)]
      calc C₀ * ‖w‖ = C₀ * ‖w‖ * 1 := by ring
        _ = C₀ * ‖w‖ * ((plateHalf m') ^ (k - l + 1) * r) := by rw [hδr]
        _ = (C₀ * ((plateHalf m') ^ (k - l + 1) * ‖w‖)) * r := by ring
    have hw0 : (0:ℝ) ≤ ‖w‖ / r := by positivity
    calc G - C₁ * ‖w‖ / r
        ≤ G - C₀ * ‖w‖ / r := by
          have h1 : C₀ * ‖w‖ / r ≤ C₁ * ‖w‖ / r := by
            apply div_le_div_of_nonneg_right _ hR0.le
            exact mul_le_mul_of_nonneg_right hC₀le (norm_nonneg w)
          linarith
      _ = G - C₀ * ((plateHalf m') ^ (k - l + 1) * ‖w‖) := by rw [hEq]
      _ ≤ gauge k hk (plateGaugeLin k (plateHalf m') c' y)
            - gauge k hk (plateGaugeLin k (plateHalf m') c'
                (projEmbedLin k l (torsionVec k l hlk ξ') w)) := by
          rw [hG]
          have h1 : C₀ * plateHalf m' ^ (k - l + 1) * ‖w‖
              = C₀ * (plateHalf m' ^ (k - l + 1) * ‖w‖) := by ring
          rw [h1] at hgv
          linarith [hgv]
      _ ≤ gauge k hk (plateGaugeLin k (plateHalf m') c'
            (y + projEmbedLin k l (torsionVec k l hlk ξ') w)) := hsub
  -- the pointwise estimate for the integrands
  have hpt : ∀ w : E l,
      ballTent l A' 0 r w * ENNReal.ofReal (phiPlate k hk (plateHalf m') c' A Cφ
          (y + projEmbedLin k l (torsionVec k l hlk ξ') w))
      ≤ ENNReal.ofReal (Cφ * |LinearMap.det (plateGaugeLin k (plateHalf m') c')|)
        * ENNReal.ofReal (((volume (Metric.ball (0:E l) r)).toReal)⁻¹
            * (1 + Metric.infDist w (Metric.ball (0:E l) r) / r) ^ (-A')
            * (max 1 (G - C₁ * ‖w‖ / r)) ^ (-A)) := by
    intro w
    set Bf : ℝ := ((volume (Metric.ball (0:E l) r)).toReal)⁻¹
      * (1 + Metric.infDist w (Metric.ball (0:E l) r) / r) ^ (-A') with hBf
    have hBf0 : 0 ≤ Bf := by
      simp only [hBf]
      exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
        (Real.rpow_nonneg (add_nonneg one_pos.le
          (div_nonneg (Metric.infDist_nonneg) hR0.le)) _)
    have hdet0 : (0:ℝ) ≤ |LinearMap.det (plateGaugeLin k (plateHalf m') c')| := abs_nonneg _
    have h3 : (max 1 (gauge k hk (plateGaugeLin k (plateHalf m') c'
        (y + projEmbedLin k l (torsionVec k l hlk ξ') w)))) ^ (-A)
        ≤ (max 1 (G - C₁ * ‖w‖ / r)) ^ (-A) := by
      refine Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (le_max_left _ _)) ?_ (by linarith)
      exact max_le_max le_rfl (hgauge w)
    calc ballTent l A' 0 r w * ENNReal.ofReal (phiPlate k hk (plateHalf m') c' A Cφ
            (y + projEmbedLin k l (torsionVec k l hlk ξ') w))
        = ENNReal.ofReal Bf * ENNReal.ofReal (Cφ
            * |LinearMap.det (plateGaugeLin k (plateHalf m') c')|
            * (max 1 (gauge k hk (plateGaugeLin k (plateHalf m') c'
                (y + projEmbedLin k l (torsionVec k l hlk ξ') w)))) ^ (-A)) := by
          rw [ballTent_eq_ofReal l A' 0 hR0 w, phiPlate, hBf]
      _ = ENNReal.ofReal (Cφ * |LinearMap.det (plateGaugeLin k (plateHalf m') c')|)
            * (ENNReal.ofReal Bf * ENNReal.ofReal ((max 1 (gauge k hk
                (plateGaugeLin k (plateHalf m') c'
                  (y + projEmbedLin k l (torsionVec k l hlk ξ') w)))) ^ (-A))) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hCφ hdet0)]
          ring
      _ ≤ ENNReal.ofReal (Cφ * |LinearMap.det (plateGaugeLin k (plateHalf m') c')|)
            * (ENNReal.ofReal Bf * ENNReal.ofReal ((max 1 (G - C₁ * ‖w‖ / r)) ^ (-A))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal h3))
      _ = ENNReal.ofReal (Cφ * |LinearMap.det (plateGaugeLin k (plateHalf m') c')|)
            * ENNReal.ofReal (Bf * (max 1 (G - C₁ * ‖w‖ / r)) ^ (-A)) := by
          rw [← ENNReal.ofReal_mul hBf0]
  have hG0 : 0 ≤ G := by rw [hG]; exact gauge_nonneg k hk _
  calc (∫⁻ w : E l, ballTent l A' 0 r w * ENNReal.ofReal (phiPlate k hk (plateHalf m') c' A Cφ
          (y + projEmbedLin k l (torsionVec k l hlk ξ') w)))
      ≤ ∫⁻ w : E l, ENNReal.ofReal (Cφ * |LinearMap.det (plateGaugeLin k (plateHalf m') c')|)
          * ENNReal.ofReal (((volume (Metric.ball (0:E l) r)).toReal)⁻¹
              * (1 + Metric.infDist w (Metric.ball (0:E l) r) / r) ^ (-A')
              * (max 1 (G - C₁ * ‖w‖ / r)) ^ (-A)) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (Cφ * |LinearMap.det (plateGaugeLin k (plateHalf m') c')|)
          * ∫⁻ w : E l, ENNReal.ofReal (((volume (Metric.ball (0:E l) r)).toReal)⁻¹
              * (1 + Metric.infDist w (Metric.ball (0:E l) r) / r) ^ (-A')
              * (max 1 (G - C₁ * ‖w‖ / r)) ^ (-A)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Cφ * |LinearMap.det (plateGaugeLin k (plateHalf m') c')|)
          * (ENNReal.ofReal C' * ENNReal.ofReal ((max 1 G) ^ (-A))) :=
        mul_le_mul' le_rfl (hC'b r G hR0 hG0)
    _ = ENNReal.ofReal C' * ENNReal.ofReal (phiPlate k hk (plateHalf m') c' A Cφ y) := by
        rw [phiPlate, hG]
        calc ENNReal.ofReal (Cφ * |LinearMap.det (plateGaugeLin k (plateHalf m') c')|)
              * (ENNReal.ofReal C'
                * ENNReal.ofReal ((max 1 (gauge k hk (plateGaugeLin k (plateHalf m') c' y))) ^ (-A)))
            = ENNReal.ofReal C'
              * (ENNReal.ofReal (Cφ * |LinearMap.det (plateGaugeLin k (plateHalf m') c')|)
                * ENNReal.ofReal ((max 1 (gauge k hk (plateGaugeLin k (plateHalf m') c' y))) ^ (-A))) := by
              ring
          _ = ENNReal.ofReal C'
              * ENNReal.ofReal (Cφ * |LinearMap.det (plateGaugeLin k (plateHalf m') c')|
                * (max 1 (gauge k hk (plateGaugeLin k (plateHalf m') c' y))) ^ (-A)) := by
              rw [ENNReal.ofReal_mul (mul_nonneg hCφ (abs_nonneg _))]




/-- Integrability of the product of two plate bumps. -/
lemma integrable_phiPlate_mul (k : ℕ) (hk : 1 ≤ k) {δ₁ δ₂ c₁ c₂ : ℝ} (hδ₁ : δ₁ ≠ 0)
    (hδ₂ : δ₂ ≠ 0) (x : E k) :
    Integrable (fun y : E k => phiPlate k hk δ₁ c₁ (gaugeExp k) (gaugeAmp k hk) (x - y)
      * phiPlate k hk δ₂ c₂ (gaugeExp k) (gaugeAmp k hk) y) := by
  have hA1 : (k : ℝ) < gaugeExp k := gaugeExp_gt hk
  refine ((integrable_phiPlate k hk hδ₁ hA1).comp_sub_left x).mul_bdd
    (c := gaugeAmp k hk * |LinearMap.det (plateGaugeLin k δ₂ c₂)|)
    (integrable_phiPlate k hk hδ₂ hA1).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (phiPlate_nonneg k hk _ _ _ _ (gaugeAmp_pos k hk).le y)]
  exact phiPlate_le_const k hk (lt_of_le_of_lt (by positivity) (gaugeExp_gt hk))
    (gaugeAmp_pos k hk).le y

/-- **GLYZ Lemma A.1 in the `ℝ≥0∞` form needed by §3.4**: the convolution of the two plate
bumps (the canonical `platePhi`) is dominated by the fine one. -/
theorem platePhi_conv_le (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ_I δ_J c_I c_J : ℝ) (x : E k),
      0 < δ_J → δ_J ≤ δ_I → δ_I ≤ 1 → c_I ∈ Set.Icc (0 : ℝ) 1 →
      c_J ∈ Set.Icc (0 : ℝ) 1 → |c_J - c_I| ≤ δ_I →
      (∫⁻ y : E k, platePhi k hk δ_I c_I (x - y) * platePhi k hk δ_J c_J y)
        ≤ ENNReal.ofReal C * platePhi k hk δ_J c_J x := by
  obtain ⟨C, hC, hCb⟩ := phiPlate_conv_le k hk (gaugeExp k) (gaugeExp_gt hk)
    (gaugeExp_ge hk) (gaugeAmp k hk) (gaugeAmp_pos k hk)
  refine ⟨C, hC.le, fun δ_I δ_J c_I c_J x hδJ hji hI hcI hcJ hcc => ?_⟩
  have hδI0 : 0 < δ_I := lt_of_lt_of_le hδJ hji
  have hInt : Integrable (fun y : E k =>
      phiPlate k hk δ_I c_I (gaugeExp k) (gaugeAmp k hk) (x - y)
        * phiPlate k hk δ_J c_J (gaugeExp k) (gaugeAmp k hk) y) :=
    integrable_phiPlate_mul k hk (ne_of_gt hδI0) (ne_of_gt hδJ) x
  have hnn : 0 ≤ᵐ[volume] (fun y : E k =>
      phiPlate k hk δ_I c_I (gaugeExp k) (gaugeAmp k hk) (x - y)
        * phiPlate k hk δ_J c_J (gaugeExp k) (gaugeAmp k hk) y) :=
    Filter.Eventually.of_forall fun y => mul_nonneg
      (phiPlate_nonneg k hk _ _ _ _ (gaugeAmp_pos k hk).le _)
      (phiPlate_nonneg k hk _ _ _ _ (gaugeAmp_pos k hk).le y)
  have hEq1 : (∫⁻ y : E k, platePhi k hk δ_I c_I (x - y) * platePhi k hk δ_J c_J y)
      = ∫⁻ y : E k, ENNReal.ofReal
          (phiPlate k hk δ_I c_I (gaugeExp k) (gaugeAmp k hk) (x - y)
            * phiPlate k hk δ_J c_J (gaugeExp k) (gaugeAmp k hk) y) := by
    refine lintegral_congr fun y => ?_
    rw [platePhi_apply, platePhi_apply,
      ← ENNReal.ofReal_mul (phiPlate_nonneg k hk _ _ _ _ (gaugeAmp_pos k hk).le (x - y))]
  have hEq2 : (∫⁻ y : E k, ENNReal.ofReal
        (phiPlate k hk δ_I c_I (gaugeExp k) (gaugeAmp k hk) (x - y)
          * phiPlate k hk δ_J c_J (gaugeExp k) (gaugeAmp k hk) y))
      = ENNReal.ofReal (∫ y : E k,
          phiPlate k hk δ_I c_I (gaugeExp k) (gaugeAmp k hk) (x - y)
            * phiPlate k hk δ_J c_J (gaugeExp k) (gaugeAmp k hk) y) :=
    (ofReal_integral_eq_lintegral_ofReal hInt hnn).symm
  rw [hEq1, hEq2]
  calc ENNReal.ofReal (∫ y : E k,
        phiPlate k hk δ_I c_I (gaugeExp k) (gaugeAmp k hk) (x - y)
          * phiPlate k hk δ_J c_J (gaugeExp k) (gaugeAmp k hk) y)
      ≤ ENNReal.ofReal (C * phiPlate k hk δ_J c_J (gaugeExp k) (gaugeAmp k hk) x) :=
        ENNReal.ofReal_le_ofReal (hCb δ_I δ_J c_I c_J x hδJ hji hI hcI hcJ hcc)
    _ = ENNReal.ofReal C * platePhi k hk δ_J c_J x := by
        rw [platePhi_apply, ENNReal.ofReal_mul hC.le]


end Submission.Vinogradov
