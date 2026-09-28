import Mathlib
import Submission.Work.HP.BCS.Defs
import Submission.Work.HP.BCS.axisTube_abs_inner_le
import Submission.Work.HP.BCS.volume_shell_le

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Work.HP.BCS

variable {k : ℕ}

/-! ## 1. The orthogonal-coordinate map is measure preserving

For a unit vector `w` in a finite-dimensional real inner product space `E`, the map
`Φ (t, ζ) = t • w + ζ` from `ℝ × wᗮ` to `E` is measure preserving. -/
theorem measurePreserving_smul_add_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (w : E) (hw : ‖w‖ = 1) :
    MeasurePreserving (fun p : ℝ × (ℝ ∙ w)ᗮ => p.1 • w + (p.2 : E))
      ((volume : Measure ℝ).prod (volume : Measure (ℝ ∙ w)ᗮ)) volume := by
  have h1 : MeasurePreserving
      (fun p : ℝ × (ℝ ∙ w)ᗮ => (WithLp.toLp 2 p : WithLp 2 (ℝ × (ℝ ∙ w)ᗮ)))
      ((volume : Measure ℝ).prod (volume : Measure (ℝ ∙ w)ᗮ)) volume :=
    WithLp.volume_preserving_toLp ℝ (ℝ ∙ w)ᗮ
  have h2 : MeasurePreserving
      (fun p : WithLp 2 (ℝ × (ℝ ∙ w)ᗮ) =>
        (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.toSpanUnitSingleton w hw)
          (LinearIsometryEquiv.refl ℝ (ℝ ∙ w)ᗮ) p : WithLp 2 ((ℝ ∙ w) × (ℝ ∙ w)ᗮ)))
      volume volume := LinearIsometryEquiv.measurePreserving _
  have h3 : MeasurePreserving
      (fun q : WithLp 2 ((ℝ ∙ w) × (ℝ ∙ w)ᗮ) => (ℝ ∙ w).orthogonalDecomposition.symm q)
      volume volume := LinearIsometryEquiv.measurePreserving _
  have h := h3.comp (h2.comp h1)
  convert h using 1
  ext p
  simp

/-! ## 2. `ofReal (if |t| ≤ L then c else 0)` as an indicator, and its integral -/
lemma ite_abs_eq_indicator (c L : ℝ) :
    (fun t : ℝ => ENNReal.ofReal (if |t| ≤ L then c else 0))
      = (Set.Icc (-L) L).indicator (fun _ => ENNReal.ofReal c) := by
  funext t
  rw [Set.indicator_apply]
  by_cases ht : |t| ≤ L
  · have ht' : t ∈ Set.Icc (-L) L := abs_le.mp ht
    rw [ite_eq_left ht, ite_eq_left ht']
  · have ht' : t ∉ Set.Icc (-L) L := fun h => ht (abs_le.mpr h)
    rw [ite_eq_right ht, ite_eq_right ht', ENNReal.ofReal_zero]

lemma lintegral_ite_abs_le (c L : ℝ) (hL : 0 ≤ L) :
    ∫⁻ t : ℝ, ENNReal.ofReal (if |t| ≤ L then c else 0)
      = ENNReal.ofReal c * ENNReal.ofReal (2 * L) := by
  rw [ite_abs_eq_indicator c L, lintegral_indicator measurableSet_Icc, setLIntegral_const,
    Real.volume_Icc]
  have h2L : L - -L = 2 * L := by ring
  rw [h2L]

/-! ## 3. Real arithmetic for the tube estimate -/
lemma tube_arith {β r s : ℝ} (hβ : 0 < β) (hr : 0 ≤ r) (hrs : r ≤ s) (hs : 1 ≤ s) :
    2 * min s (β * s + (1 + β) * r) * min (2 * (((1 + β) * r) / β)) s ≤ 32 * r * s := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hrs' : 0 ≤ r * s := mul_nonneg hr hs0.le
  have hA0 : 0 ≤ min s (β * s + (1 + β) * r) := le_min hs0.le (by positivity)
  have hB0 : 0 ≤ min (2 * (((1 + β) * r) / β)) s := le_min (by positivity) hs0.le
  have hA_le : min s (β * s + (1 + β) * r) ≤ β * s + (1 + β) * r := min_le_right _ _
  have hB_le : min (2 * (((1 + β) * r) / β)) s ≤ 2 * (((1 + β) * r) / β) := min_le_left _ _
  have hB2 : 2 * (((1 + β) * r) / β) = 2 * (1 + β) * (r / β) := by ring
  by_cases h1 : β * s ≤ r
  · -- β * s ≤ r : then `β ≤ 1`, and the first factor is at most `3 r`
    have hβ1 : β ≤ 1 := by
      have : β * s ≤ 1 * s := by linarith
      exact le_of_mul_le_mul_right this hs0
    have hβr : β * r ≤ r := by
      simpa using mul_le_mul_of_nonneg_right hβ1 hr
    have hA : min s (β * s + (1 + β) * r) ≤ 3 * r := by
      refine le_trans hA_le ?_
      linarith
    have hB : min (2 * (((1 + β) * r) / β)) s ≤ s := min_le_right _ _
    have h3 : min s (β * s + (1 + β) * r) * min (2 * (((1 + β) * r) / β)) s ≤ (3 * r) * s :=
      mul_le_mul hA hB hB0 (by linarith)
    linarith
  · by_cases hβ2 : 1 ≤ β
    · -- β ≥ 1 : the second factor is at most `4 r`
      have hA : min s (β * s + (1 + β) * r) ≤ s := min_le_left _ _
      have hB : min (2 * (((1 + β) * r) / β)) s ≤ 4 * r := by
        refine le_trans hB_le ?_
        rw [hB2]
        have h2' : 2 * (1 + β) ≤ 2 * (2 * β) := by linarith
        have h4 : (0:ℝ) ≤ r / β := by positivity
        calc 2 * (1 + β) * (r / β) ≤ 2 * (2 * β) * (r / β) :=
              mul_le_mul_of_nonneg_right h2' h4
          _ = 4 * r := by field_simp; ring
      have h3 : min s (β * s + (1 + β) * r) * min (2 * (((1 + β) * r) / β)) s ≤ s * (4 * r) :=
        mul_le_mul hA hB hB0 hs0.le
      linarith
    · -- β < 1 and r < β * s
      have hβ1 : β < 1 := not_le.mp hβ2
      have hrβ : r / β < s := by
        rw [div_lt_iff₀ hβ]
        linarith
      have hb2r : (1 + β) * r ≤ 2 * r := by
        have hbr : β * r ≤ r := by
          simpa using mul_le_mul_of_nonneg_right hβ1.le hr
        have e : (1 + β) * r = r + β * r := by ring
        rw [e]; linarith
      have hA : min s (β * s + (1 + β) * r) ≤ β * s + 2 * r := by
        refine le_trans hA_le ?_
        linarith
      have hB : min (2 * (((1 + β) * r) / β)) s ≤ 4 * (r / β) := by
        refine le_trans hB_le ?_
        rw [hB2]
        have h4 : (0:ℝ) ≤ r / β := by positivity
        have h5 : 2 * (1 + β) ≤ 4 := by linarith
        simpa using mul_le_mul_of_nonneg_right h5 h4
      have h3 : min s (β * s + (1 + β) * r) * min (2 * (((1 + β) * r) / β)) s
          ≤ (β * s + 2 * r) * (4 * (r / β)) :=
        mul_le_mul hA hB hB0 (by positivity)
      have hkey : 2 * ((β * s + 2 * r) * (4 * (r / β))) ≤ 24 * r * s := by
        have e : 2 * ((β * s + 2 * r) * (4 * (r / β))) = 8 * s * r + 16 * r * (r / β) := by
          field_simp
          ring
        rw [e]
        have h6 : r * (r / β) ≤ r * s := mul_le_mul_of_nonneg_left hrβ.le hr
        linarith
      have h4 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 2)
      linarith

/-! ## 4. A pointwise bound for the sections of the product tube -/
lemma section_volume_bound {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (m : ℕ) (hm : Module.finrank ℝ W = m) (hm1 : 1 ≤ m)
    {β δ s t : ℝ} (hβ : 0 < β) (hδ : 0 ≤ δ) (hs : 0 ≤ s) :
    volume {ζ : W | t ^ 2 + ‖ζ‖ ^ 2 ≤ s ^ 2 ∧ abs (abs t - β * ‖ζ‖) ≤ δ} ≤
      ENNReal.ofReal (volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * s ^ (m - 1)
        * (if |t| ≤ min s (β * s + δ) then min (2 * (δ / β)) s else 0)) := by
  by_cases hcase : |t| ≤ min s (β * s + δ)
  · rw [ite_eq_left hcase]
    by_cases hts : |t| ≤ s
    · set A : ℝ := max 0 ((|t| - δ) / β) with hAdef
      set B : ℝ := min (Real.sqrt (s ^ 2 - t ^ 2)) ((|t| + δ) / β) with hBdef
      have hA0 : 0 ≤ A := by rw [hAdef]; exact le_max_left 0 _
      have hB0 : 0 ≤ B := by
        rw [hBdef]; exact le_min (Real.sqrt_nonneg _) (by positivity)
      have hsub : {ζ : W | t ^ 2 + ‖ζ‖ ^ 2 ≤ s ^ 2 ∧ abs (abs t - β * ‖ζ‖) ≤ δ}
          ⊆ {ζ : W | A ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ B} := by
        intro ζ hζ
        obtain ⟨h1, h2⟩ := hζ
        have h3 : ‖ζ‖ ^ 2 ≤ s ^ 2 - t ^ 2 := by linarith
        have h4 : ‖ζ‖ ≤ Real.sqrt (s ^ 2 - t ^ 2) := by
          rw [← Real.sqrt_sq (norm_nonneg ζ)]
          exact Real.sqrt_le_sqrt h3
        have h5 : -δ ≤ |t| - β * ‖ζ‖ := (abs_le.mp h2).1
        have h6 : |t| - β * ‖ζ‖ ≤ δ := (abs_le.mp h2).2
        have h7 : β * ‖ζ‖ ≤ |t| + δ := by linarith
        have h8 : |t| - δ ≤ β * ‖ζ‖ := by linarith
        have h9 : ‖ζ‖ ≤ (|t| + δ) / β := by
          rw [le_div_iff₀ hβ]; linarith
        have h10 : (|t| - δ) / β ≤ ‖ζ‖ := by
          rw [div_le_iff₀ hβ]; linarith
        exact ⟨by rw [hAdef]; exact max_le (norm_nonneg ζ) h10,
          by rw [hBdef]; exact le_min h4 h9⟩
      refine (measure_mono hsub).trans ?_
      have hshell := volume_shell_le m hm hm1 A B hA0 hB0
      refine hshell.trans ?_
      apply ENNReal.ofReal_le_ofReal
      have hsqrt_le : Real.sqrt (s ^ 2 - t ^ 2) ≤ s := by
        have h := Real.sqrt_le_sqrt (show s ^ 2 - t ^ 2 ≤ s ^ 2 by linarith [sq_nonneg t])
        rwa [Real.sqrt_sq hs] at h
      have hBs : B ≤ s := by rw [hBdef]; exact le_trans (min_le_left _ _) hsqrt_le
      have hBA : max 0 (B - A) ≤ min (2 * (δ / β)) s := by
        refine max_le (le_min (by positivity) hs) ?_
        have h1 : B ≤ (|t| + δ) / β := by rw [hBdef]; exact min_le_right _ _
        have h2 : (|t| - δ) / β ≤ A := by rw [hAdef]; exact le_max_right _ _
        have h3 : (|t| + δ) / β - (|t| - δ) / β = 2 * (δ / β) := by
          rw [← sub_div]
          ring
        refine le_min ?_ ?_
        · have h4 : B - A ≤ (|t| + δ) / β - (|t| - δ) / β := by linarith
          rw [h3] at h4
          exact h4
        · linarith [hBs, hA0]
      have hBpow : B ^ (m - 1) ≤ s ^ (m - 1) := pow_le_pow_left₀ hB0 hBs _
      have hVr : (0 : ℝ) ≤ volume.real (Metric.ball (0 : W) 1) := measureReal_nonneg
      have hfac : 0 ≤ volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * max 0 (B - A) :=
        mul_nonneg (mul_nonneg hVr (Nat.cast_nonneg m)) (le_max_left 0 _)
      have hstep1 : volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * max 0 (B - A) * B ^ (m - 1)
          ≤ volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * max 0 (B - A) * s ^ (m - 1) :=
        mul_le_mul_of_nonneg_left hBpow hfac
      have hstep2 : volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * max 0 (B - A) * s ^ (m - 1)
          ≤ volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * min (2 * (δ / β)) s * s ^ (m - 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hBA (mul_nonneg hVr (Nat.cast_nonneg m)))
          (pow_nonneg hs _)
      calc volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * max 0 (B - A) * B ^ (m - 1)
          ≤ volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * max 0 (B - A) * s ^ (m - 1) := hstep1
        _ ≤ volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * min (2 * (δ / β)) s * s ^ (m - 1) :=
              hstep2
        _ = volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * s ^ (m - 1) * min (2 * (δ / β)) s := by
              ring
    · -- `|t| > s`: the section is empty
      have hempty : {ζ : W | t ^ 2 + ‖ζ‖ ^ 2 ≤ s ^ 2 ∧ abs (abs t - β * ‖ζ‖) ≤ δ} = ∅ := by
        ext ζ
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro h1 _
        have h3 : s < |t| := lt_of_not_ge hts
        have h2 : s ^ 2 < t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
        nlinarith
      rw [hempty, measure_empty]
      positivity
  · rw [ite_eq_right hcase]
    have hempty : {ζ : W | t ^ 2 + ‖ζ‖ ^ 2 ≤ s ^ 2 ∧ abs (abs t - β * ‖ζ‖) ≤ δ} = ∅ := by
      ext ζ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      by_cases h3 : |t| ≤ s
      · have h5 : min s (β * s + δ) = β * s + δ := by
          rcases le_total (β * s + δ) s with hle | hle
          · exact min_eq_right hle
          · exact absurd h3 (by rw [min_eq_left hle] at hcase; exact hcase)
        have h4 : β * s + δ < |t| := by
          rw [h5] at hcase
          exact not_le.mp hcase
        have h6 : β * s < β * ‖ζ‖ := by
          have := (abs_le.mp h2).2
          linarith
        have h7 : s < ‖ζ‖ := lt_of_mul_lt_mul_left h6 hβ.le
        have h8 : ‖ζ‖ ≤ s := by
          have h9 : ‖ζ‖ ^ 2 ≤ s ^ 2 := by linarith [sq_nonneg t]
          rw [← Real.sqrt_sq (norm_nonneg ζ), ← Real.sqrt_sq hs]
          exact Real.sqrt_le_sqrt h9
        linarith
      · have h4 : s < |t| := not_le.mp h3
        have h5 : s ^ 2 < t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
        nlinarith
    rw [hempty, measure_empty]
    positivity

/-! ## 5. The degenerate (`β = 0`) product-space tube estimate: a slab -/
lemma prod_slab_bound {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (m : ℕ) (hm : Module.finrank ℝ W = m) (hm1 : 1 ≤ m)
    {δ s : ℝ} (hδ : 0 ≤ δ) (hs : 1 ≤ s) :
    ((volume : Measure ℝ).prod (volume : Measure W))
      {p : ℝ × W | p.1 ^ 2 + ‖p.2‖ ^ 2 ≤ s ^ 2 ∧ |p.1| ≤ δ} ≤
      ENNReal.ofReal (32 * (m : ℝ) * volume.real (Metric.ball (0 : W) 1) * δ * s ^ m) := by
  classical
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs
  have hVr : (0 : ℝ) ≤ volume.real (Metric.ball (0 : W) 1) := measureReal_nonneg
  have hmr : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set A : Set (ℝ × W) := {p : ℝ × W | p.1 ^ 2 + ‖p.2‖ ^ 2 ≤ s ^ 2 ∧ |p.1| ≤ δ} with hA
  have hAmeas : MeasurableSet A := by
    rw [hA]
    have h1 : Continuous fun p : ℝ × W => p.1 ^ 2 + ‖p.2‖ ^ 2 := by fun_prop
    have h2 : Continuous fun p : ℝ × W => |p.1| := by fun_prop
    exact ((isClosed_le h1 continuous_const).inter
      (isClosed_le h2 continuous_const)).measurableSet
  rw [Measure.prod_apply hAmeas]
  have hpt : ∀ t : ℝ, volume (Prod.mk t ⁻¹' A) ≤
      (Set.Icc (-δ) δ).indicator
        (fun _ => ENNReal.ofReal (volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * s ^ m)) t := by
    intro t
    by_cases ht : |t| ≤ δ
    · rw [Set.indicator_of_mem (Set.mem_Icc.mpr (abs_le.mp ht)) _]
      have hsub : Prod.mk t ⁻¹' A ⊆ Metric.closedBall (0 : W) s := by
        intro ζ hζ
        rw [hA] at hζ
        simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hζ
        rw [Metric.mem_closedBall, dist_zero_right]
        nlinarith [hζ.1, norm_nonneg ζ]
      refine (measure_mono hsub).trans ?_
      have hshell := volume_shell_le m hm hm1 0 s (le_refl 0) hs0.le
      have hball : Metric.closedBall (0 : W) s = {v : W | 0 ≤ ‖v‖ ∧ ‖v‖ ≤ s} := by
        ext v; simp [Metric.mem_closedBall, dist_zero_right]
      rw [hball]
      refine hshell.trans ?_
      apply ENNReal.ofReal_le_ofReal
      have hsm : s ^ m = s ^ (m - 1) * s := by rw [← pow_succ, Nat.sub_add_cancel hm1]
      rw [max_eq_right (by linarith : (0 : ℝ) ≤ s - 0), hsm]
      nlinarith [hVr, hmr, hs0.le, pow_nonneg hs0.le (m - 1)]
    · rw [Set.indicator_of_notMem (fun h => ht (abs_le.mpr (Set.mem_Icc.mp h))) _]
      have hempty : Prod.mk t ⁻¹' A = ∅ := by
        rw [hA]
        ext ζ
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
          not_and]
        intro _ h2
        exact ht h2
      rw [hempty, measure_empty]
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc]
  have h2δ : δ - -δ = 2 * δ := by ring
  rw [h2δ]
  have hfac : (0 : ℝ) ≤ volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * s ^ m :=
    mul_nonneg (mul_nonneg hVr hmr) (pow_nonneg hs0.le m)
  have hcombine : ENNReal.ofReal (volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * s ^ m)
        * ENNReal.ofReal (2 * δ)
      = ENNReal.ofReal (volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * s ^ m * (2 * δ)) := by
    rw [ENNReal.ofReal_mul hfac]
  rw [hcombine]
  apply ENNReal.ofReal_le_ofReal
  have hX : (0 : ℝ) ≤ volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * δ * s ^ m :=
    mul_nonneg (mul_nonneg (mul_nonneg hVr hmr) hδ) (pow_nonneg hs0.le m)
  have e1 : volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * s ^ m * (2 * δ)
      = 2 * (volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * δ * s ^ m) := by ring
  have e2 : 32 * (m : ℝ) * volume.real (Metric.ball (0 : W) 1) * δ * s ^ m
      = 32 * (volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * δ * s ^ m) := by ring
  rw [e1, e2]
  linarith

/-! ## 6. The product-space tube estimate -/
theorem prod_tube_bound {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (m : ℕ) (hm : Module.finrank ℝ W = m) (hm1 : 1 ≤ m)
    {β r s : ℝ} (hβ : 0 ≤ β) (hr : 0 ≤ r) (hrs : r ≤ s) (hs : 1 ≤ s) :
    ((volume : Measure ℝ).prod (volume : Measure W))
      {p : ℝ × W | p.1 ^ 2 + ‖p.2‖ ^ 2 ≤ s ^ 2 ∧ abs (abs p.1 - β * ‖p.2‖) ≤ (1 + β) * r} ≤
      ENNReal.ofReal (32 * (m : ℝ) * volume.real (Metric.ball (0 : W) 1) * r * s ^ m) := by
  classical
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs
  have hVr : (0 : ℝ) ≤ volume.real (Metric.ball (0 : W) 1) := measureReal_nonneg
  have hmr : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rcases eq_or_lt_of_le hβ with hβ0 | hβpos
  · -- hβ0 : 0 = β, so `β = 0`: a slab
    have hβ0' : β = 0 := hβ0.symm
    subst hβ0'
    have hset : {p : ℝ × W | p.1 ^ 2 + ‖p.2‖ ^ 2 ≤ s ^ 2 ∧ abs (abs p.1 - 0 * ‖p.2‖) ≤ (1 + 0) * r}
        = {p : ℝ × W | p.1 ^ 2 + ‖p.2‖ ^ 2 ≤ s ^ 2 ∧ |p.1| ≤ r} := by
      congr 1
      ext p
      simp
    rw [hset]
    exact prod_slab_bound m hm hm1 hr hs
  · -- `β > 0`
    set A : Set (ℝ × W) :=
      {p : ℝ × W | p.1 ^ 2 + ‖p.2‖ ^ 2 ≤ s ^ 2 ∧ abs (abs p.1 - β * ‖p.2‖) ≤ (1 + β) * r}
      with hA
    have hAmeas : MeasurableSet A := by
      rw [hA]
      have h1 : Continuous fun p : ℝ × W => p.1 ^ 2 + ‖p.2‖ ^ 2 := by fun_prop
      have h2 : Continuous fun p : ℝ × W => abs (abs p.1 - β * ‖p.2‖) := by fun_prop
      exact ((isClosed_le h1 continuous_const).inter
        (isClosed_le h2 continuous_const)).measurableSet
    rw [Measure.prod_apply hAmeas]
    have hδ : (0 : ℝ) ≤ (1 + β) * r := by positivity
    set L₀ : ℝ := min s (β * s + (1 + β) * r) with hL₀def
    set c₀ : ℝ := min (2 * (((1 + β) * r) / β)) s with hc₀def
    have hL₀0 : 0 ≤ L₀ := by rw [hL₀def]; exact le_min hs0.le (by positivity)
    have hC0 : (0 : ℝ) ≤ volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * s ^ (m - 1) :=
      mul_nonneg (mul_nonneg hVr hmr) (pow_nonneg hs0.le _)
    have hpt : ∀ t : ℝ, volume (Prod.mk t ⁻¹' A) ≤
        ENNReal.ofReal (volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * s ^ (m - 1)
          * (if |t| ≤ L₀ then c₀ else 0)) := by
      intro t
      have h1 : Prod.mk t ⁻¹' A
          = {ζ : W | t ^ 2 + ‖ζ‖ ^ 2 ≤ s ^ 2 ∧ abs (abs t - β * ‖ζ‖) ≤ (1 + β) * r} := by
        rw [hA]
        ext ζ
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      rw [h1]
      have h := section_volume_bound (W := W) m hm hm1 (t := t) (s := s) (δ := (1 + β) * r)
        hβpos hδ hs0.le
      rw [← hL₀def, ← hc₀def] at h
      exact h
    refine (lintegral_mono hpt).trans ?_
    have hmeas : Measurable fun t : ℝ => ENNReal.ofReal (if |t| ≤ L₀ then c₀ else 0) := by
      rw [ite_abs_eq_indicator c₀ L₀]
      exact measurable_const.indicator measurableSet_Icc
    have hstep : ∀ t : ℝ, ENNReal.ofReal (volume.real (Metric.ball (0 : W) 1) * (m : ℝ)
          * s ^ (m - 1) * (if |t| ≤ L₀ then c₀ else 0))
        = ENNReal.ofReal (volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * s ^ (m - 1))
          * ENNReal.ofReal (if |t| ≤ L₀ then c₀ else 0) := by
      intro t
      rw [ENNReal.ofReal_mul hC0]
    calc ∫⁻ t, ENNReal.ofReal (volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * s ^ (m - 1)
            * (if |t| ≤ L₀ then c₀ else 0))
        = ENNReal.ofReal (volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * s ^ (m - 1))
            * ∫⁻ t, ENNReal.ofReal (if |t| ≤ L₀ then c₀ else 0) := by
          simp only [hstep]
          rw [lintegral_const_mul _ hmeas]
      _ = ENNReal.ofReal (volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * s ^ (m - 1))
            * (ENNReal.ofReal c₀ * ENNReal.ofReal (2 * L₀)) := by
          rw [lintegral_ite_abs_le c₀ L₀ hL₀0]
      _ = ENNReal.ofReal (volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * s ^ (m - 1)
            * (c₀ * (2 * L₀))) := by
          have hc₀0 : 0 ≤ c₀ := by rw [hc₀def]; exact le_min (by positivity) hs0.le
          rw [← ENNReal.ofReal_mul hc₀0, ← ENNReal.ofReal_mul hC0]
      _ ≤ ENNReal.ofReal (32 * (m : ℝ) * volume.real (Metric.ball (0 : W) 1) * r * s ^ m) := by
          apply ENNReal.ofReal_le_ofReal
          have ha := tube_arith hβpos hr hrs hs
          rw [← hL₀def, ← hc₀def] at ha
          have hp : s ^ m = s ^ (m - 1) * s := by rw [← pow_succ, Nat.sub_add_cancel hm1]
          have h2 : c₀ * (2 * L₀) = 2 * L₀ * c₀ := by ring
          rw [h2]
          calc volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * s ^ (m - 1) * (2 * L₀ * c₀)
              ≤ volume.real (Metric.ball (0 : W) 1) * (m : ℝ) * s ^ (m - 1) * (32 * r * s) :=
                mul_le_mul_of_nonneg_left ha hC0
            _ = 32 * (m : ℝ) * volume.real (Metric.ball (0 : W) 1) * r * s ^ m := by
                rw [hp]; ring

/-! ## 7. The dimension of the orthogonal complement -/
lemma finrank_orthogonal_span_singleton_eq
    (w : EuclideanSpace ℝ (Fin k)) (hk : 1 ≤ k) (hw : w ≠ 0) :
    Module.finrank ℝ (ℝ ∙ w)ᗮ = k - 1 := by
  have h1 : Module.finrank ℝ (ℝ ∙ w) = 1 := by
    rw [finrank_span_singleton hw]
  have h2 := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (ℝ ∙ w)
  rw [h1, finrank_euclideanSpace, Fintype.card_fin] at h2
  omega

/-! ## 8. The main bound -/
theorem coneTube_bound (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : EuclideanSpace ℝ (Fin k)) (c s r : ℝ),
      0 ≤ c → c < ‖a‖ → 0 ≤ r → r ≤ s → 1 ≤ s →
      MeasureTheory.volume (Work.HP.BCS.coneTube a c s r)
        ≤ ENNReal.ofReal (C * r * s ^ (k - 1)) := by
  rcases eq_or_lt_of_le hk with hk1 | hk2
  · -- ### `k = 1`
    subst hk1
    refine ⟨2, by norm_num, ?_⟩
    intro a c s r hc hca hr hrs hs
    have ha : 0 < ‖a‖ := lt_of_le_of_lt hc hca
    have haw : a ≠ 0 := by simpa [norm_eq_zero] using ha.ne'
    have htop : (ℝ ∙ a) = ⊤ := by
      rw [Submodule.eq_top_iff_finrank_eq, finrank_span_singleton haw, finrank_euclideanSpace,
        Fintype.card_fin]
    -- the cone surface is trivial in dimension one
    have hzero : ∀ y : EuclideanSpace ℝ (Fin 1), |inner ℝ a y| = c * ‖y‖ → y = 0 := by
      intro y hy
      have hy' : y ∈ (ℝ ∙ a) := by rw [htop]; trivial
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hy'
      subst ht
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs] at hy
      have h2 : |t| * ‖a‖ * (‖a‖ - c) = 0 := by
        have h3 : |t| * ‖a‖ ^ 2 = c * (|t| * ‖a‖) := by
          rwa [abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg a) 2)] at hy
        nlinarith [h3]
      have ht0 : t = 0 := by
        have hz : |t| = 0 := by
          by_contra hne
          have htne : t ≠ 0 := fun h => hne (by rw [h, abs_zero])
          have hpos : 0 < |t| * ‖a‖ * (‖a‖ - c) :=
            mul_pos (mul_pos (abs_pos.mpr htne) ha) (by linarith)
          rw [h2] at hpos
          exact lt_irrefl 0 hpos
        exact abs_eq_zero.mp hz
      rw [ht0, zero_smul]
    have hTeq : coneTube a c s r = Metric.closedBall 0 r := by
      ext x
      rw [coneTube, Metric.mem_closedBall, dist_zero_right]
      constructor
      · rintro ⟨hxs, y, hy, hxy⟩
        rw [hzero y hy, sub_zero] at hxy
        exact hxy
      · intro hx
        exact ⟨le_trans hx hrs, 0, by simp, by simpa using hx⟩
    have hquot : Real.sqrt Real.pi / Real.Gamma ((1 : ℝ) / 2 + 1) = 2 := by
      have hG : Real.Gamma ((1 : ℝ) / 2 + 1) = Real.sqrt Real.pi / 2 := by
        rw [Real.Gamma_add_one (by norm_num : ((1:ℝ)/2) ≠ 0), Real.Gamma_one_half_eq]
        ring
      rw [hG]
      have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
      field_simp
    have hvol : volume (coneTube a c s r) = ENNReal.ofReal (2 * r) := by
      rw [hTeq, EuclideanSpace.volume_closedBall]
      simp only [Fintype.card_fin, Nat.cast_one, pow_one]
      rw [hquot]
      rw [← ENNReal.ofReal_mul hr]
      ring_nf
    rw [hvol]
    apply ENNReal.ofReal_le_ofReal
    rw [Nat.sub_self, pow_zero, mul_one]
  · -- ### `k ≥ 2`
    have hk1' : 1 ≤ k - 1 := by omega
    set V : ℝ := Real.sqrt Real.pi ^ (k - 1) / Real.Gamma (((k - 1 : ℕ) : ℝ) / 2 + 1) with hVdef
    have hVnn : 0 ≤ V := by
      rw [hVdef]
      have h1 : (0 : ℝ) < Real.Gamma (((k - 1 : ℕ) : ℝ) / 2 + 1) :=
        Real.Gamma_pos_of_pos (by positivity)
      exact div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) h1.le
    refine ⟨32 * ((k - 1 : ℕ) : ℝ) * V + 1, by positivity, ?_⟩
    intro a c s r hc hca hr hrs hs
    have ha : 0 < ‖a‖ := lt_of_le_of_lt hc hca
    set w : EuclideanSpace ℝ (Fin k) := ‖a‖⁻¹ • a with hwdef
    have hw : ‖w‖ = 1 := by
      rw [hwdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg a)),
        inv_mul_cancel₀ ha.ne']
    have hwne : w ≠ 0 := by rw [← norm_pos_iff, hw]; norm_num
    have hdim : Module.finrank ℝ (ℝ ∙ w)ᗮ = k - 1 :=
      finrank_orthogonal_span_singleton_eq w (le_of_lt hk2) hwne
    set γ : ℝ := c / ‖a‖ with hγdef
    have hγ0 : 0 ≤ γ := by rw [hγdef]; positivity
    have hγ1 : γ < 1 := by
      rw [hγdef, div_lt_one ha]
      exact hca
    set β : ℝ := γ / Real.sqrt (1 - γ ^ 2) with hβdef
    have hβ0 : 0 ≤ β := by rw [hβdef]; positivity
    -- the closed superset of the tube, in orthogonal coordinates
    set S : Set (EuclideanSpace ℝ (Fin k)) :=
      {x | ‖x‖ ≤ s ∧ abs (abs (inner ℝ x w) - β * ‖x - (inner ℝ x w) • w‖) ≤ (1 + β) * r}
      with hSdef
    have hSmeas : MeasurableSet S := by
      rw [hSdef]
      have h1 : Continuous fun x : EuclideanSpace ℝ (Fin k) => ‖x‖ := continuous_norm
      have h2 : Continuous fun x : EuclideanSpace ℝ (Fin k) =>
          abs (abs (inner ℝ x w) - β * ‖x - (inner ℝ x w) • w‖) := by fun_prop
      exact ((isClosed_le h1 continuous_const).inter
        (isClosed_le h2 continuous_const)).measurableSet
    have hTS : coneTube a c s r ⊆ S := by
      intro x hx
      rw [coneTube] at hx
      obtain ⟨hxs, y, hy, hxy⟩ := hx
      have hyw : |inner ℝ y w| = γ * ‖y‖ := by
        have h1 : inner ℝ y w = ‖a‖⁻¹ * inner ℝ y a := by
          rw [hwdef, real_inner_smul_right]
        have h2 : inner ℝ y a = inner ℝ a y := real_inner_comm a y
        rw [h1, h2, abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg a)), hy, hγdef]
        field_simp
      have hkey := axisTube_abs_inner_le w hw hγ0 hγ1 hβdef hr hyw hxy
      exact ⟨hxs, by linarith [hkey]⟩
    -- the orthogonal-coordinate map is measure preserving
    have hmp := measurePreserving_smul_add_orthogonal w hw
    set A : Set (ℝ × (ℝ ∙ w)ᗮ) :=
      {p | p.1 ^ 2 + ‖p.2‖ ^ 2 ≤ s ^ 2 ∧ abs (abs p.1 - β * ‖p.2‖) ≤ (1 + β) * r} with hAdef
    have hsub2 : (fun p : ℝ × (ℝ ∙ w)ᗮ => p.1 • w + (p.2 : EuclideanSpace ℝ (Fin k))) ⁻¹' S ⊆ A := by
      intro p hp
      have hp' : p.1 • w + (p.2 : EuclideanSpace ℝ (Fin k)) ∈ S := hp
      rw [hSdef] at hp'
      rw [hAdef]
      obtain ⟨hp1, hp2⟩ := hp'
      have horth0 : inner ℝ w (p.2 : EuclideanSpace ℝ (Fin k)) = 0 :=
        (Submodule.mem_orthogonal (ℝ ∙ w) (p.2 : EuclideanSpace ℝ (Fin k))).mp p.2.2 w
          (Submodule.mem_span_singleton_self w)
      have horth2 : inner ℝ (p.2 : EuclideanSpace ℝ (Fin k)) w = 0 := by
        rw [real_inner_comm w (p.2 : EuclideanSpace ℝ (Fin k)), horth0]
      have hinner : inner ℝ (p.1 • w + (p.2 : EuclideanSpace ℝ (Fin k))) w = p.1 := by
        rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hw, one_pow, mul_one,
          horth2]
        ring
      have hproj : (p.1 • w + (p.2 : EuclideanSpace ℝ (Fin k)))
          - (inner ℝ (p.1 • w + (p.2 : EuclideanSpace ℝ (Fin k))) w) • w = p.2 := by
        rw [hinner]
        abel
      have horth : inner ℝ (p.1 • w) (p.2 : EuclideanSpace ℝ (Fin k)) = 0 := by
        rw [real_inner_smul_left, horth0, mul_zero]
      have hnorm : ‖p.1 • w + (p.2 : EuclideanSpace ℝ (Fin k))‖ ^ 2 = p.1 ^ 2 + ‖p.2‖ ^ 2 := by
        rw [pow_two, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth, norm_smul, hw,
          Real.norm_eq_abs, mul_one, ← pow_two, ← pow_two, sq_abs, Submodule.norm_coe]
      refine ⟨?_, ?_⟩
      · have h1 : ‖p.1 • w + (p.2 : EuclideanSpace ℝ (Fin k))‖ ^ 2 ≤ s ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hp1 2
        rw [hnorm] at h1
        exact h1
      · rw [hproj, hinner] at hp2
        exact hp2
    -- the value of the unit-ball volume in the complement
    have hVr : volume.real (Metric.ball (0 : (ℝ ∙ w)ᗮ) 1) = V := by
      haveI : Nontrivial (ℝ ∙ w)ᗮ :=
        Module.nontrivial_of_finrank_pos (by rw [hdim]; omega)
      have hb := InnerProductSpace.volume_ball (0 : (ℝ ∙ w)ᗮ) 1
      rw [hdim] at hb
      have hb' : volume (Metric.ball (0 : (ℝ ∙ w)ᗮ) 1) = ENNReal.ofReal V := by
        rw [hb]
        simp only [ENNReal.ofReal_one, one_pow, one_mul]
        rw [hVdef]
      change (volume (Metric.ball (0 : (ℝ ∙ w)ᗮ) 1)).toReal = V
      rw [hb', ENNReal.toReal_ofReal hVnn]
    calc volume (coneTube a c s r) ≤ volume S := measure_mono hTS
      _ = (volume.prod volume)
            ((fun p : ℝ × (ℝ ∙ w)ᗮ => p.1 • w + (p.2 : EuclideanSpace ℝ (Fin k))) ⁻¹' S) := by
            rw [← hmp.map_eq, Measure.map_apply hmp.measurable hSmeas]
      _ ≤ (volume.prod volume) A := measure_mono hsub2
      _ ≤ ENNReal.ofReal (32 * ((k - 1 : ℕ) : ℝ) * volume.real (Metric.ball (0 : (ℝ ∙ w)ᗮ) 1)
            * r * s ^ (k - 1)) :=
            prod_tube_bound (k - 1) hdim hk1' hβ0 hr hrs hs
      _ = ENNReal.ofReal (32 * ((k - 1 : ℕ) : ℝ) * V * r * s ^ (k - 1)) := by rw [hVr]
      _ ≤ ENNReal.ofReal ((32 * ((k - 1 : ℕ) : ℝ) * V + 1) * r * s ^ (k - 1)) := by
            apply ENNReal.ofReal_le_ofReal
            have h1 : 0 ≤ r * s ^ (k - 1) :=
              mul_nonneg hr (pow_nonneg (by linarith : (0:ℝ) ≤ s) _)
            nlinarith [h1]

end Work.HP.BCS
