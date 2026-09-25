import Mathlib

open scoped ContDiff

namespace Work.NN.Final.ChartComp

noncomputable section

/-- The normalization map `w ↦ w / ‖w‖`. -/
private def F (w : ℂ) : ℂ := w / ((‖w‖ : ℝ) : ℂ)

/-- `F` is smooth away from the origin. -/
private lemma contDiffOn_F {n : WithTop ℕ∞} :
    ContDiffOn ℝ n F {w : ℂ | w ≠ 0} := by
  have hnorm : ContDiffOn ℝ n (fun w : ℂ => ‖w‖) {w : ℂ | w ≠ 0} :=
    ContDiffOn.norm ℝ (contDiff_id.contDiffOn) (fun x hx => hx)
  have hcast : ContDiffOn ℝ n (fun w : ℂ => (↑‖w‖ : ℂ)) {w : ℂ | w ≠ 0} :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hnorm
  have hinv : ContDiffOn ℝ n (fun w : ℂ => ((↑‖w‖ : ℂ))⁻¹) {w : ℂ | w ≠ 0} :=
    hcast.inv (fun w hw => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw))
  have hfin : ContDiffOn ℝ n (fun w : ℂ => w * ((↑‖w‖ : ℂ))⁻¹) {w : ℂ | w ≠ 0} :=
    (contDiff_id.contDiffOn).mul hinv
  exact hfin.congr (fun w _ => by simp only [F, div_eq_mul_inv])

/-- `F` is homogeneous of degree `0` for positive scalars. -/
private lemma div_norm_smul (c : ℝ) (hc : 0 < c) {y : ℂ} (hy : y ≠ 0) :
    (c • y) / ((‖c • y‖ : ℝ) : ℂ) = y / ((‖y‖ : ℝ) : ℂ) := by
  have hcy : c • y ≠ 0 := smul_ne_zero_iff.mpr ⟨hc.ne', hy⟩
  rw [div_eq_div_iff]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, RCLike.real_smul_eq_coe_mul, Complex.ofReal_mul,
      mul_assoc, mul_left_comm y (↑c)]
    rfl
  · exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hcy)
  · exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)

private lemma F_smul (c : ℝ) (hc : 0 < c) {y : ℂ} (hy : y ≠ 0) : F (c • y) = F y := by
  simp only [F]
  exact div_norm_smul c hc hy

/-- Scaling estimate: the `m`-th derivative of `F` at `x` is bounded in terms of its value
at `c • x`, with an explicit factor `c ^ m`. -/
private lemma norm_iteratedFDeriv_F_smul_le (m : ℕ) {c : ℝ} (hc : 0 < c) {x : ℂ} (hx : x ≠ 0) :
    ‖iteratedFDeriv ℝ m F x‖ ≤ ‖iteratedFDeriv ℝ m F (c • x)‖ * c ^ m := by
  set g : ℂ →L[ℝ] ℂ := c • (1 : ℂ →L[ℝ] ℂ) with hgdef
  have hgx : g x = c • x := by rw [hgdef]; simp
  have hgy : ∀ y, g y = c • y := fun y => by rw [hgdef]; simp
  have hcne : c ≠ 0 := ne_of_gt hc
  have hSopen : IsOpen {w : ℂ | w ≠ 0} := isOpen_ne
  have hpre : g ⁻¹' {w : ℂ | w ≠ 0} = {w : ℂ | w ≠ 0} := by
    ext y
    rw [Set.mem_preimage, hgy y]
    change c • y ≠ 0 ↔ y ≠ 0
    rw [smul_ne_zero_iff]
    exact ⟨fun h => h.2, fun h => ⟨hcne, h⟩⟩
  have hcx : c • x ∈ {w : ℂ | w ≠ 0} := smul_ne_zero_iff.mpr ⟨hcne, hx⟩
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ) g
    ((contDiffOn_F (n := ⊤)).of_le le_top) hSopen.uniqueDiffOn
    (by rw [hpre]; exact hSopen.uniqueDiffOn) (x := x)
    (by
      have h : x ∈ g ⁻¹' {w : ℂ | w ≠ 0} := by rw [hpre]; exact hx
      exact h) (i := m) le_rfl
  have hL : iteratedFDerivWithin ℝ m (F ∘ ⇑g) (g ⁻¹' {w : ℂ | w ≠ 0}) x = iteratedFDeriv ℝ m F x := by
    rw [hpre]
    rw [iteratedFDerivWithin_congr (f₁ := F ∘ ⇑g) (f := F)
      (fun y hy => by
        simp only [Function.comp_apply]
        rw [hgy y]
        exact F_smul c hc hy) hx m]
    exact iteratedFDerivWithin_of_isOpen m hSopen hx
  have hR : (iteratedFDerivWithin ℝ m F {w : ℂ | w ≠ 0} (g x)).compContinuousLinearMap
        (fun _ => g)
      = (iteratedFDeriv ℝ m F (c • x)).compContinuousLinearMap (fun _ => g) := by
    rw [hgx, iteratedFDerivWithin_of_isOpen m hSopen hcx]
  have hkey : iteratedFDeriv ℝ m F x
      = (iteratedFDeriv ℝ m F (c • x)).compContinuousLinearMap (fun _ => g) := by
    rw [← hL, hcomp, hR]
  calc ‖iteratedFDeriv ℝ m F x‖
      = ‖(iteratedFDeriv ℝ m F (c • x)).compContinuousLinearMap (fun _ => g)‖ := by rw [hkey]
    _ ≤ ‖iteratedFDeriv ℝ m F (c • x)‖ * ∏ _i : Fin m, ‖g‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDeriv ℝ m F (c • x)‖ * ‖g‖ ^ m := by
        simp [Finset.prod_const, Fintype.card_fin]
    _ ≤ ‖iteratedFDeriv ℝ m F (c • x)‖ * c ^ m := by
        have hgn : ‖g‖ ≤ c := by
          rw [hgdef]
          refine ContinuousLinearMap.opNorm_le_bound _ (le_of_lt hc) (fun y => ?_)
          rw [smul_apply, one_apply_eq_self, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg g) hgn m) (norm_nonneg _)

theorem exists_bound_iteratedFDeriv_div_norm :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∀ (m : ℕ) (w : ℂ),
      w ≠ 0 → ‖iteratedFDeriv ℝ m (fun w : ℂ => w / ((‖w‖ : ℝ) : ℂ)) w‖ ≤ C m * (1 / ‖w‖) ^ m := by
  have key : ∀ m : ℕ, ∃ B : ℝ, ∀ u : ℂ, u ∈ Metric.sphere (0 : ℂ) 1 →
      ‖iteratedFDeriv ℝ m F u‖ ≤ B := by
    intro m
    have hcontH : ContinuousOn (iteratedFDeriv ℝ m F) {w : ℂ | w ≠ 0} :=
      ContinuousOn.continuousOn_iteratedFDeriv (contDiffOn_F (n := ⊤)) isOpen_ne le_top
    have hcont : ContinuousOn (fun u : ℂ => ‖iteratedFDeriv ℝ m F u‖) (Metric.sphere (0 : ℂ) 1) :=
      (ContinuousOn.norm hcontH).mono (by
        intro u hu
        rw [Metric.mem_sphere, dist_zero_right] at hu
        exact norm_ne_zero_iff.mp (by rw [hu]; norm_num))
    obtain ⟨u0, _, hmax⟩ := IsCompact.exists_isMaxOn (isCompact_sphere (0 : ℂ) 1)
      ⟨1, by simp⟩ hcont
    exact ⟨‖iteratedFDeriv ℝ m F u0‖, fun u hu => hmax hu⟩
  choose B hB using key
  refine ⟨fun m => |B m| + 1, ?_, ?_⟩
  · intro m; positivity
  · intro m w hw
    have hcpos : 0 < 1 / ‖w‖ := by positivity
    have hsphere : (1 / ‖w‖) • w ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hw)]
    have hscale := norm_iteratedFDeriv_F_smul_le m hcpos hw
    have hbu := hB m ((1 / ‖w‖) • w) hsphere
    show ‖iteratedFDeriv ℝ m F w‖ ≤ (|B m| + 1) * (1 / ‖w‖) ^ m
    calc ‖iteratedFDeriv ℝ m F w‖
        ≤ ‖iteratedFDeriv ℝ m F ((1 / ‖w‖) • w)‖ * (1 / ‖w‖) ^ m := hscale
      _ ≤ B m * (1 / ‖w‖) ^ m := mul_le_mul_of_nonneg_right hbu (by positivity)
      _ ≤ (|B m| + 1) * (1 / ‖w‖) ^ m :=
          mul_le_mul_of_nonneg_right (by have h := le_abs_self (B m); linarith) (by positivity)

end

end Work.NN.Final.ChartComp
