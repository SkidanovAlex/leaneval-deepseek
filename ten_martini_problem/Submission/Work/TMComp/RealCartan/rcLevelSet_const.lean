import Mathlib

/-!
# The level set of the maximum is everything (a maximum principle)

Let `F ⊆ ℂ` be open and preconnected, `V : ℂ → ℝ` continuous, `M : ℝ`, with

* `V w ≤ M` for all `w ∈ F` (upper bound), and
* the **sub-mean-value inequality** on circles: for every `z ∈ F` and every `r > 0` with
  `closedBall z r ⊆ F`, one has `V z ≤ circleAverage V z r`.

Then if `V z₀ = M` for some `z₀ ∈ F`, the function is constantly `M` on `F`.

The proof shows that `A = F ∩ {V = M}` is both open (using the mean value inequality together
with the fact that a nonnegative continuous function on a circle whose average vanishes is
identically zero) and closed ambiently, and concludes by the preconnectedness of `F`.
-/

open MeasureTheory Metric Set Real Filter

namespace Work.TMComp.RealCartan

/-- A continuous nonnegative function on `[0, 2π]` with vanishing integral over `(0, 2π]` is
identically zero there. -/
theorem rcIntervalIntegral_eq_zero_Ioc {u : ℝ → ℝ} (hu : Continuous u) (hnn : ∀ θ, 0 ≤ u θ)
    (hint : ∫ θ in (0 : ℝ)..(2 * π), u θ = 0) :
    ∀ θ₀ ∈ Set.Ioc (0 : ℝ) (2 * π), u θ₀ = 0 := by
  intro θ₀ hθ₀
  rw [Set.mem_Ioc] at hθ₀
  obtain ⟨hθpos, hθle⟩ := hθ₀
  by_contra hne
  have hpos : 0 < u θ₀ := lt_of_le_of_ne (hnn θ₀) (Ne.symm hne)
  have hev : ∀ᶠ θ in nhds θ₀, u θ₀ / 2 < u θ := by
    have hε : (0 : ℝ) < u θ₀ / 2 := by linarith
    have ht := (Metric.tendsto_nhds.mp (hu.continuousAt (x := θ₀))) (u θ₀ / 2) hε
    filter_upwards [ht] with θ hθ
    rw [Real.dist_eq] at hθ
    have := abs_lt.mp hθ
    linarith [this.2]
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hev
  set a : ℝ := max 0 (θ₀ - δ / 2) with ha
  have halt : a < θ₀ := by
    rw [ha, max_lt_iff]
    exact ⟨hθpos, by linarith⟩
  have hposOn : ∀ θ ∈ Set.Ioo a θ₀, 0 < u θ := by
    intro θ hθ
    rw [Set.mem_Ioo] at hθ
    obtain ⟨hθa, hθθ⟩ := hθ
    have hd : dist θ θ₀ < δ := by
      rw [Real.dist_eq, abs_of_neg (by linarith : θ - θ₀ < 0)]
      have ha' : θ₀ - δ / 2 ≤ a := by rw [ha]; exact le_max_right _ _
      linarith
    have hδθ := hδ hd
    linarith
  have hposint : 0 < ∫ θ in a..θ₀, u θ :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hu.intervalIntegrable a θ₀) hposOn halt
  have ha0 : 0 ≤ a := by rw [ha]; exact le_max_left _ _
  have e1 : (∫ θ in (0 : ℝ)..a, u θ) + (∫ θ in a..θ₀, u θ) = ∫ θ in (0 : ℝ)..θ₀, u θ :=
    intervalIntegral.integral_add_adjacent_intervals (hu.intervalIntegrable 0 a)
      (hu.intervalIntegrable a θ₀)
  have e2 : (∫ θ in (0 : ℝ)..θ₀, u θ) + (∫ θ in θ₀..(2 * π), u θ)
      = ∫ θ in (0 : ℝ)..(2 * π), u θ :=
    intervalIntegral.integral_add_adjacent_intervals (hu.intervalIntegrable 0 θ₀)
      (hu.intervalIntegrable θ₀ (2 * π))
  have h1 : 0 ≤ ∫ θ in (0 : ℝ)..a, u θ :=
    intervalIntegral.integral_nonneg ha0 (fun θ _ => hnn θ)
  have h3 : 0 ≤ ∫ θ in θ₀..(2 * π), u θ :=
    intervalIntegral.integral_nonneg hθle (fun θ _ => hnn θ)
  linarith [e1, e2, hint, h1, h3, hposint]

/-- If a continuous function `g` is nonnegative on the circle `sphere z r` (`r > 0`) and its
circle average is `≤ 0`, then `g` vanishes on that circle. -/
theorem rcCircleAverage_nonneg_eq_zero {g : ℂ → ℝ} (hg : Continuous g) {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hnn : ∀ ζ ∈ Metric.sphere z r, 0 ≤ g ζ)
    (h0 : Real.circleAverage g z r ≤ 0) :
    ∀ ζ ∈ Metric.sphere z r, g ζ = 0 := by
  have huc : Continuous (fun θ : ℝ => g (circleMap z r θ)) :=
    hg.comp (continuous_circleMap z r)
  have hunn : ∀ θ : ℝ, 0 ≤ g (circleMap z r θ) := by
    intro θ
    apply hnn
    have h := circleMap_mem_sphere' z r θ
    rwa [abs_of_pos hr] at h
  have hint : ∫ θ in (0 : ℝ)..(2 * π), g (circleMap z r θ) = 0 := by
    have hIle : ∫ θ in (0 : ℝ)..(2 * π), g (circleMap z r θ) ≤ 0 := by
      have hp : (0 : ℝ) < (2 * π)⁻¹ := by positivity
      have h : (2 * π)⁻¹ * (∫ θ in (0 : ℝ)..(2 * π), g (circleMap z r θ)) ≤ (2 * π)⁻¹ * 0 := by
        rw [Real.circleAverage_def, smul_eq_mul] at h0
        simpa using h0
      exact (mul_le_mul_iff_of_pos_left hp).mp h
    have hIge : 0 ≤ ∫ θ in (0 : ℝ)..(2 * π), g (circleMap z r θ) :=
      intervalIntegral.integral_nonneg (le_of_lt two_pi_pos) (fun θ _ => hunn θ)
    linarith
  intro ζ hζ
  have hmem : ζ ∈ circleMap z r '' Set.Ioc (0 : ℝ) (2 * π) := by
    rw [image_circleMap_Ioc, abs_of_pos hr]
    exact hζ
  obtain ⟨θ₀, hθ₀, hθ₀eq⟩ := hmem
  rw [← hθ₀eq]
  exact rcIntervalIntegral_eq_zero_Ioc huc hunn hint θ₀ hθ₀

theorem rcLevelSet_const {F : Set ℂ} (hF : IsOpen F) (hFc : IsPreconnected F)
    {V : ℂ → ℝ} (hVc : Continuous V) {M : ℝ} (hle : ∀ w ∈ F, V w ≤ M)
    (hVmean : ∀ z ∈ F, ∀ r : ℝ, 0 < r → Metric.closedBall z r ⊆ F →
      V z ≤ Real.circleAverage V z r)
    {z₀ : ℂ} (hz₀ : z₀ ∈ F) (hM : V z₀ = M) :
    ∀ w ∈ F, V w = M := by
  set A : Set ℂ := F ∩ {w | V w = M} with hA
  have hAopen : IsOpen A := by
    rw [Metric.isOpen_iff]
    intro z hz
    rw [hA] at hz
    obtain ⟨hzF, hzM⟩ := hz
    obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hF z hzF
    refine ⟨ε / 2, by linarith, fun w hw => ?_⟩
    rw [Metric.mem_ball] at hw
    have hwF : w ∈ F := hε (by rw [Metric.mem_ball]; linarith)
    rw [hA]
    refine ⟨hwF, ?_⟩
    rcases eq_or_ne w z with rfl | hwz
    · exact hzM
    · set r : ℝ := ‖w - z‖ with hr
      have hrpos : 0 < r := by rw [hr]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hwz)
      have hrlt : r < ε / 2 := by
        rw [hr]
        rwa [dist_eq_norm] at hw
      have hball : Metric.closedBall z r ⊆ F := by
        intro y hy
        apply hε
        rw [Metric.mem_ball]
        rw [Metric.mem_closedBall] at hy
        linarith
      have hsphere : ∀ ζ ∈ Metric.sphere z r, V ζ = M := by
        have hciV : CircleIntegrable V z r := ContinuousOn.circleIntegrable' hVc.continuousOn
        have hleM : Real.circleAverage V z r ≤ M := by
          apply Real.circleAverage_mono_on_of_le_circle hciV
          intro x hx
          apply hle x
          apply hball
          rw [Metric.mem_closedBall]
          rw [Metric.mem_sphere, abs_of_pos hrpos] at hx
          linarith
        have hcirc_eq : Real.circleAverage V z r = M :=
          le_antisymm hleM (by rw [← hzM]; exact hVmean z hzF r hrpos hball)
        have hgnn : ∀ ζ ∈ Metric.sphere z r, 0 ≤ M - V ζ := by
          intro ζ hζ
          have h1 : V ζ ≤ M := by
            apply hle ζ
            apply hball
            rw [Metric.mem_closedBall]
            rw [Metric.mem_sphere] at hζ
            linarith
          linarith
        have hcg : Real.circleAverage (fun ζ => M - V ζ) z r ≤ 0 := by
          have hsub := Real.circleAverage_fun_sub (f₁ := (fun _ : ℂ => M)) (f₂ := V)
            (circleIntegrable_const M z r) hciV
          rw [hsub, Real.circleAverage_const, hcirc_eq]
          norm_num
        have hzero := rcCircleAverage_nonneg_eq_zero (continuous_const.sub hVc) hrpos hgnn hcg
        intro ζ hζ
        have hM' : M - V ζ = 0 := hzero ζ hζ
        linarith
      have hwsp : w ∈ Metric.sphere z r := by
        rw [Metric.mem_sphere, dist_eq_norm]
      exact hsphere w hwsp
  have hcl : closure A ⊆ {w : ℂ | V w = M} := by
    apply closure_minimal _ (isClosed_eq hVc continuous_const)
    intro w hw
    rw [hA] at hw
    exact hw.2
  have hzA : z₀ ∈ A := by rw [hA]; exact ⟨hz₀, hM⟩
  intro w hw
  by_contra hwne
  have hwncl : w ∉ closure A := fun h => hwne (hcl h)
  have hne : (F ∩ (closure A)ᶜ).Nonempty := ⟨w, hw, hwncl⟩
  have hsub : F ⊆ A ∪ (closure A)ᶜ := by
    intro x hxF
    by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · exact Or.inr (fun hxcl => hxA (by rw [hA]; exact ⟨hxF, hcl hxcl⟩))
  obtain ⟨y, _, hyA, hycl⟩ :=
    hFc A (closure A)ᶜ hAopen isClosed_closure.isOpen_compl hsub ⟨z₀, hz₀, hzA⟩ hne
  exact hycl (subset_closure hyA)

end Work.TMComp.RealCartan
