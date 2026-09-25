import Mathlib
import Submission.Work.Beltrami.Solve
import Submission.Work.Beltrami.Cauchy
import Submission.Work.Beltrami.beltramiCoeff_contDiffOn
import Submission.Work.Beltrami.cutoff_estimates

namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff
open scoped Topology
open Work.Beltrami

/-! ## Elementary algebra of the `∂` and `∂̄` coefficients -/

theorem dzCoeff_add (L M : ℂ →L[ℝ] ℂ) : dzCoeff (L + M) = dzCoeff L + dzCoeff M := by
  simp only [dzCoeff, add_apply]; ring

theorem dzbarCoeff_add (L M : ℂ →L[ℝ] ℂ) : dzbarCoeff (L + M) = dzbarCoeff L + dzbarCoeff M := by
  simp only [dzbarCoeff, add_apply]; ring

theorem dzCoeff_id : dzCoeff (1 : ℂ →L[ℝ] ℂ) = 1 := by
  simp only [dzCoeff, one_apply_eq_self, Complex.I_mul_I]
  norm_num

theorem dzbarCoeff_id : dzbarCoeff (1 : ℂ →L[ℝ] ℂ) = 0 := by
  simp only [dzbarCoeff, one_apply_eq_self, Complex.I_mul_I]
  norm_num

theorem dzCoeff_zero : dzCoeff (0 : ℂ →L[ℝ] ℂ) = 0 := by
  simp [dzCoeff]

theorem dW_add (f g : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : dW (f + g) z = dW f z + dW g z := by
  unfold dW
  rw [fderiv_add hf hg]
  exact dzCoeff_add _ _

theorem dbarW_add (f g : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : dbarW (f + g) z = dbarW f z + dbarW g z := by
  unfold dbarW
  rw [fderiv_add hf hg]
  exact dzbarCoeff_add _ _

theorem dW_id (z : ℂ) : dW (id : ℂ → ℂ) z = 1 := by
  show dzCoeff (fderiv ℝ (id : ℂ → ℂ) z) = 1
  rw [fderiv_id]
  exact dzCoeff_id

theorem dbarW_id (z : ℂ) : dbarW (id : ℂ → ℂ) z = 0 := by
  show dzbarCoeff (fderiv ℝ (id : ℂ → ℂ) z) = 0
  rw [fderiv_id]
  exact dzbarCoeff_id

theorem dW_eq_zero_of_fderiv_eq_zero {f : ℂ → ℂ} {z : ℂ} (h : fderiv ℝ f z = 0) :
    dW f z = 0 := by
  show dzCoeff (fderiv ℝ f z) = 0
  rw [h]
  exact dzCoeff_zero

/-! ## The Beltrami equation, localised at one point -/

/-- The pointwise form of `IsJHolAt_iff_beltrami`, needing only `J z ∘ J z = -1` at `z`. -/
theorem isJHolAt_iff_beltrami_of (J : ℂ → ℂ →L[ℝ] ℂ) (w : ℂ → ℂ) (z : ℂ)
    (hJ : ∀ v : ℂ, J z (J z v) = -v) :
    IsJHolAt J w z ↔
      (1 + Complex.I * (J z 1)) * dW w z + (1 + Complex.I * star (J z 1)) * dbarW w z = 0 := by
  unfold IsJHolAt dW dbarW
  exact (hol_iff_eval_one (J z) hJ (fderiv ℝ w z)).trans
    (eval_one_iff_beltrami (J z) (fderiv ℝ w z))

/-- The Beltrami equation `∂̄w = μ ∂w` at a point, with `μ = beltramiCoeff (J z)`. -/
theorem isJHolAt_iff_beltramiCoeff_of (J : ℂ → ℂ →L[ℝ] ℂ) (w : ℂ → ℂ) (z : ℂ)
    (hJ : ∀ v : ℂ, J z (J z v) = -v) (hden : 1 + Complex.I * star (J z 1) ≠ 0) :
    IsJHolAt J w z ↔ dbarW w z = beltramiCoeff (J z) * dW w z := by
  rw [isJHolAt_iff_beltrami_of J w z hJ, beltramiCoeff]
  constructor
  · intro hm
    have h2 : (1 + Complex.I * star (J z 1)) * dbarW w z
        = -(1 + Complex.I * (J z 1)) * dW w z := by linear_combination hm
    rw [div_mul_eq_mul_div, eq_div_iff hden]
    linear_combination h2
  · intro hm
    rw [hm, div_mul_eq_mul_div]
    field_simp
    ring

/-- **The `ℂ`-picture Newlander--Nirenberg solution.**  Let `J` be a smooth complex structure on
`ℂ` (`J z ∘ J z = -1` near `0`) with `J 0` equal to the standard structure (multiplication by `i`).
Then there is a smooth function `w`, `J`-holomorphic near `0` with invertible (nonzero)
differential at `0`.

The proof is the Beltrami argument: put `mu := beltramiCoeff (J ·)` (so `mu 0 = 0`), cut `mu` off
by a bump function supported in a small disc (this makes `mu` compactly supported with both
`sup ‖mu‖` and its `C^{0,alpha}` constant as small as needed), solve `dbarW v = mu * (1 + dW v)`
with `beltrami_solve`, and set `w := id + v`; the Beltrami equation is equivalent to
`J`-holomorphy by `IsJHolAt_iff_beltramiCoeff`. -/
theorem exists_hol_of_beltrami (H : CauchyEstimates) {J : ℂ → ℂ →L[ℝ] ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hJs : ContDiffOn ℝ ∞ J (Metric.ball 0 ρ))
    (hJ2 : ∀ z ∈ Metric.ball 0 ρ, ∀ v : ℂ, J z (J z v) = -v)
    (hJ0 : J 0 = JstdC 0) :
    ∃ w : ℂ → ℂ, ContDiffAt ℝ ∞ w 0 ∧ fderiv ℝ w 0 ≠ 0 ∧
      ∀ᶠ z in 𝓝 0, ∀ v : ℂ, fderiv ℝ w z (J z v) = Complex.I * fderiv ℝ w z v := by
  classical
  -- the Beltrami coefficient is smooth on a small ball, where the denominator does not vanish
  obtain ⟨ρ', hρ'pos, hρ'le, hμ₀smooth, hden⟩ := beltramiCoeff_contDiffOn hρ hJs hJ0
  have hμ₀0 : (fun z => beltramiCoeff (J z)) 0 = 0 := by
    show beltramiCoeff (J 0) = 0
    rw [hJ0]
    exact beltramiCoeff_JstdC 0
  -- smallness parameters for the contraction
  set α : ℝ := 1 / 2 with hαdef
  have hα : 0 < α := by rw [hαdef]; norm_num
  have hα1 : α < 1 := by rw [hαdef]; norm_num
  set C₀ : ℝ := max H.potConst (H.schConst α) + 1 with hC₀def
  have hC₀pos : 0 < C₀ := by
    have h1 := H.potConst_pos
    have h2 := H.schConst_pos α
    rw [hC₀def]
    linarith [le_max_left H.potConst (H.schConst α)]
  set s : ℝ := min 1 (1 / (32 * C₀)) with hsdef
  have hspos : 0 < s := by
    rw [hsdef]; exact lt_min one_pos (div_pos one_pos (by linarith))
  have hsle : s ≤ 1 / (32 * C₀) := by rw [hsdef]; exact min_le_right _ _
  set ε : ℝ := min (H.smoothDelta s α s 1 / 2) (s / 8) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min (by linarith [H.smoothDelta_pos s α s 1]) (by linarith)
  have hεs : ε ≤ H.smoothDelta s α s 1 := by
    rw [hεdef]
    have h1 : min (H.smoothDelta s α s 1 / 2) (s / 8) ≤ H.smoothDelta s α s 1 / 2 := min_le_left _ _
    linarith [H.smoothDelta_pos s α s 1]
  have hεs8 : ε ≤ s / 8 := by rw [hεdef]; exact min_le_right _ _
  set κ : ℝ := (s - 4 * ε) / 2 with hκdef
  have hκpos : 0 < κ := by rw [hκdef]; linarith
  have hs4ε : s = 4 * ε + 2 * κ := by rw [hκdef]; ring
  have hsmall : SmallEnough H α ε κ 1 := by
    constructor
    · have h1 : (max H.potConst (H.schConst α) + 1) * (1 + 1) * (2 * ε + κ) = C₀ * s := by
        rw [hC₀def, hs4ε]; ring
      rw [h1]
      have h3 : C₀ * (1 / (32 * C₀)) = 1 / 32 := by field_simp
      have h2 : C₀ * s ≤ C₀ * (1 / (32 * C₀)) :=
        mul_le_mul_of_nonneg_left hsle (le_of_lt hC₀pos)
      linarith [h2, h3]
    · have h2 : 2 * (2 * ε + κ) = s := by rw [hs4ε]; ring
      rw [h2]
      exact hεs
  -- the cut-off Beltrami coefficient
  have hρ₂pos : 0 < min ρ' 1 / 2 := by
    have : 0 < min ρ' 1 := lt_min hρ'pos one_pos
    linarith
  have hle : min ρ' 1 / 2 ≤ ρ' := by
    have h1 : min ρ' 1 ≤ ρ' := min_le_left _ _
    linarith
  have hμ₀smooth' : ContDiffOn ℝ ∞ (fun z => beltramiCoeff (J z))
      (Metric.ball 0 (min ρ' 1 / 2)) :=
    hμ₀smooth.mono (Metric.ball_subset_ball hle)
  obtain ⟨δ, μ, hδpos, hδρ₂, hμs, hμc, hμsupp, hagree, hμb, hμK⟩ :=
    cutoff_estimates hρ₂pos hμ₀smooth' hμ₀0 hα hα1 hεpos hκpos
  have hδ1 : δ < 1 := by
    have h1 : min ρ' 1 / 2 ≤ 1 / 2 := by
      have := min_le_right ρ' (1 : ℝ); linarith
    linarith
  have hμsupp' : ∀ z, 1 < ‖z‖ → μ z = 0 :=
    fun z hz => hμsupp z (le_trans (le_of_lt hδ1) (le_of_lt hz))
  obtain ⟨v, hv_s, hv_eq, hv_dW, _hv_dbarW⟩ :=
    beltrami_solve hα hα1 (le_refl 1) hεpos hκpos hμs hμc hμsupp' hμb hμK hsmall
  set w : ℂ → ℂ := fun z => z + v z with hwdef
  have hw_id : w = (id : ℂ → ℂ) + v := by
    rw [hwdef]
    funext z
    rfl
  have hv_diff : ∀ z, DifferentiableAt ℝ v z :=
    fun z => (hv_s.differentiable (by simp)).differentiableAt
  refine ⟨w, ?_, ?_, ?_⟩
  · show ContDiffAt ℝ ∞ (fun z : ℂ => z + v z) 0
    have h := (contDiff_id.add hv_s).contDiffAt (x := (0 : ℂ))
    simpa [hwdef] using h
  · have hdWw : dW w 0 = 1 + dW v 0 := by
      rw [hw_id, dW_add _ _ 0 differentiableAt_id (hv_diff 0), dW_id]
    have hbound : (3 / 4 : ℝ) ≤ ‖dW w 0‖ := by
      rw [hdWw]
      have h2 := norm_sub_le ((1 : ℂ) + dW v 0) (dW v 0)
      have h4 : ((1 : ℂ) + dW v 0) - dW v 0 = 1 := by ring
      rw [h4, norm_one] at h2
      have h3 : ‖dW v 0‖ ≤ 1 / 4 := hv_dW 0
      linarith
    intro h0
    have h5 : dW w 0 = 0 := dW_eq_zero_of_fderiv_eq_zero h0
    rw [h5] at hbound
    norm_num at hbound
  · have hminpos : 0 < min (δ / 2) ρ' := lt_min (by linarith) hρ'pos
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hminpos] with z hz
    have hzδ : ‖z‖ < δ / 2 := by
      have h' : dist z 0 < δ / 2 :=
        lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_left _ _)
      rwa [dist_zero_right] at h'
    have hzρ' : z ∈ Metric.ball (0 : ℂ) ρ' := by
      rw [Metric.mem_ball]
      exact lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _)
    have hzρ : z ∈ Metric.ball (0 : ℂ) ρ := Metric.ball_subset_ball hρ'le hzρ'
    have h2 : dW w z = 1 + dW v z := by
      rw [hw_id, dW_add _ _ z differentiableAt_id (hv_diff z), dW_id]
    have h3 : dbarW w z = dbarW v z := by
      rw [hw_id, dbarW_add _ _ z differentiableAt_id (hv_diff z), dbarW_id, zero_add]
    have heq : dbarW w z = beltramiCoeff (J z) * dW w z := by
      rw [h3, hv_eq z, hagree z hzδ, h2]
    exact (isJHolAt_iff_beltramiCoeff_of J w z (hJ2 z hzρ) (hden z hzρ')).mpr heq

end Work.Beltrami
