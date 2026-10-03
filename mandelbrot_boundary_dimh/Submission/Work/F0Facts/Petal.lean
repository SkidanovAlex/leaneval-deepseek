import Mathlib
import Submission.Work.F0Facts.Basic
import Submission.Work.FatouCoord.Main

/-!
# The attracting petal of `f₀`

Instantiation of the `FatouCoord` chapter for `f₀(z) = z + z²`: there are `r > 0` and `M > 1/r`
such that

* `Petal r M ⊆ Basin` (uniform convergence of the iterates on the petal);
* `Petal r M` is connected (it is the intersection of the two discs
  `ball (-(2M)⁻¹) (2M)⁻¹` and `ball 0 r`);
* `Petal r M` contains the real interval `(-M⁻¹, 0)`.
-/

namespace Work.F0Facts

open MandelDim Filter Set Metric Topology
open scoped Topology

noncomputable section

/-! ## The petal as an intersection of two discs -/

/-- `Petal r M = {|z| < r, Re(-1/z) > M}` is the intersection of the two discs with diameters
`[-1/M, 0]` and `[0, r]`. -/
lemma petal_eq_ball {r M : ℝ} (hM : 0 < M) :
    Work.FatouCoord.Petal r M
      = ball (-(((2 * M)⁻¹ : ℝ) : ℂ)) ((2 * M)⁻¹) ∩ ball (0 : ℂ) r := by
  have hc : 0 < (2 * M)⁻¹ := by positivity
  have h2M : 0 < 2 * M := by positivity
  have hinv : (2 * M) * (2 * M)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt h2M)
  ext z
  rw [Work.FatouCoord.mem_Petal, mem_inter_iff, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm,
    sub_neg_eq_add, sub_zero]
  have key : ‖z + (((2 * M)⁻¹ : ℝ) : ℂ)‖ < (2 * M)⁻¹ ↔ z.re < -M * Complex.normSq z := by
    have hsq : ‖z + (((2 * M)⁻¹ : ℝ) : ℂ)‖ ^ 2
        = Complex.normSq z + 2 * (2 * M)⁻¹ * z.re + (2 * M)⁻¹ * (2 * M)⁻¹ := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.conj_ofReal,
        Complex.normSq_ofReal]
      have hm : (z * (((2 * M)⁻¹ : ℝ) : ℂ)).re = (2 * M)⁻¹ * z.re := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [hm]; ring
    have hiff : ‖z + (((2 * M)⁻¹ : ℝ) : ℂ)‖ < (2 * M)⁻¹
        ↔ ‖z + (((2 * M)⁻¹ : ℝ) : ℂ)‖ ^ 2 < ((2 * M)⁻¹) ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hc)).symm
    have hsq' : (2 * M)⁻¹ * (2 * M)⁻¹ = ((2 * M)⁻¹) ^ 2 := by ring
    rw [hiff, hsq, hsq']
    constructor <;> intro h <;> nlinarith [Complex.normSq_nonneg z, hinv, hM, hc]
  rw [key, and_comm]

lemma isConnected_Petal {r M : ℝ} (hM : 0 < M) (hrM : 1 / M < r) :
    IsConnected (Work.FatouCoord.Petal r M) := by
  have hc : 0 < (2 * M)⁻¹ := by positivity
  have hr : 0 < r := lt_trans (by positivity : (0:ℝ) < 1 / M) hrM
  have hmem : -(((2 * M)⁻¹ : ℝ) : ℂ)
      ∈ ball (-(((2 * M)⁻¹ : ℝ) : ℂ)) ((2 * M)⁻¹) ∩ ball (0 : ℂ) r := by
    refine ⟨mem_ball_self hc, ?_⟩
    rw [mem_ball, dist_eq_norm, sub_zero, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 * M)⁻¹)]
    have h2 : (2 * M)⁻¹ < 1 / M := by
      have h : (2 * M)⁻¹ < M⁻¹ := by
        rw [inv_lt_inv₀ (by positivity : (0:ℝ) < 2 * M) (by positivity : (0:ℝ) < M)]
        linarith
      simpa [one_div] using h
    linarith
  rw [petal_eq_ball hM]
  exact ⟨⟨_, hmem⟩, ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected⟩

/-! ## The chart iterates on the petal -/

/-- In the chart `w = -1/z`, the iterates of `f₀` on the petal stay in the region
`Re w > N`, where `N` is the level of the growth estimate. -/
lemma chart_iterate_of_gt {N : ℝ} (hNpos : 0 < N)
    (hN : ∀ w : ℂ, N < w.re → ∀ k : ℕ, N + k / 2 ≤ ((Work.FatouCoord.wMap f0)^[k] w).re)
    {y : ℂ} (hy : N < (Work.FatouCoord.chart y).re) :
    ∀ k : ℕ, Work.FatouCoord.chart (f0^[k] y)
        = (Work.FatouCoord.wMap f0)^[k] (Work.FatouCoord.chart y)
      ∧ N + k / 2 ≤ (Work.FatouCoord.chart (f0^[k] y)).re := by
  intro k
  induction k with
  | zero => exact ⟨rfl, by simpa using le_of_lt hy⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have hpos : 0 < (Work.FatouCoord.chart (f0^[k] y)).re := by
      have hk : (0:ℝ) ≤ (k:ℝ)/2 := by positivity
      linarith
    have hne : f0^[k] y ≠ 0 := by
      intro hz
      rw [hz, Work.FatouCoord.chart_zero] at hpos
      exact lt_irrefl 0 hpos
    have h3 : Work.FatouCoord.chart (f0 (f0^[k] y))
        = Work.FatouCoord.wMap f0 (Work.FatouCoord.chart (f0^[k] y)) :=
      Work.FatouCoord.chart_comp f0 hne
    have h4 : Work.FatouCoord.chart (f0^[k + 1] y)
        = Work.FatouCoord.wMap f0 (Work.FatouCoord.chart (f0^[k] y)) := by
      rw [Function.iterate_succ_apply', h3]
    refine ⟨?_, ?_⟩
    · rw [h4, h1, Function.iterate_succ_apply']
    · rw [h4, h1]
      simpa only [Function.iterate_succ_apply'] using hN (Work.FatouCoord.chart y) hy (k + 1)

/-! ## The petal is contained in the basin -/

/-- If `M` is at least the level `N` of the growth estimate, the iterates converge to `0`
uniformly on the whole petal, so the petal is contained in the parabolic basin. -/
lemma petal_subset_basin {r M N : ℝ} (hr : 0 < r) (hNpos : 0 < N) (hNM : N ≤ M)
    (hN : ∀ w : ℂ, N < w.re → ∀ k : ℕ, N + k / 2 ≤ ((Work.FatouCoord.wMap f0)^[k] w).re) :
    Work.FatouCoord.Petal r M ⊆ Basin := by
  intro z hz
  have hz0 : z ≠ 0 := Work.FatouCoord.ne_zero_of_mem_Petal hz
  have hcw : N < (Work.FatouCoord.chart z).re :=
    lt_of_le_of_lt hNM ((Work.FatouCoord.chart_mem_Petal_iff hr hz0).mp hz).1
  refine ⟨Work.FatouCoord.Petal r M, Work.FatouCoord.isOpen_Petal.mem_nhds hz,
    fun n x _ => trivial, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 1 / (N + K / 2) < ε := by
    have hlim : Tendsto (fun k : ℕ => (N + (k : ℝ) / 2)⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => ((k : ℝ)) / 2) atTop atTop :=
        Filter.Tendsto.atTop_div_const (by norm_num) (tendsto_natCast_atTop_atTop (R := ℝ))
      have h2 : Tendsto (fun k : ℕ => N + (k : ℝ) / 2) atTop atTop :=
        tendsto_atTop_mono (fun k => by have : (0:ℝ) ≤ N := le_of_lt hNpos; linarith) h1
      exact tendsto_inv_atTop_zero.comp h2
    rw [Metric.tendsto_atTop] at hlim
    obtain ⟨K, hK⟩ := hlim ε hε
    refine ⟨K, ?_⟩
    have hK' := hK K le_rfl
    simpa [one_div, dist_eq_norm, Real.norm_eq_abs, sub_zero,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (N + (K:ℝ)/2))] using hK'
  refine Filter.eventually_atTop.mpr ⟨K, fun k hk y hy => ?_⟩
  have hy' : N < (Work.FatouCoord.chart y).re :=
    lt_of_le_of_lt hNM ((Work.FatouCoord.chart_mem_Petal_iff hr
      (Work.FatouCoord.ne_zero_of_mem_Petal hy)).mp hy).1
  obtain ⟨h1, h2⟩ := chart_iterate_of_gt hNpos hN hy' k
  have hpos : 0 < (Work.FatouCoord.chart (f0^[k] y)).re := by
    have hk2 : (0:ℝ) ≤ (k:ℝ)/2 := by positivity
    linarith
  have hne : f0^[k] y ≠ 0 := by
    intro hz
    rw [hz, Work.FatouCoord.chart_zero] at hpos
    exact lt_irrefl 0 hpos
  have hnorm : ‖f0^[k] y‖ = (‖Work.FatouCoord.chart (f0^[k] y)‖)⁻¹ := by
    rw [Work.FatouCoord.norm_chart hne, inv_inv]
  have hle : (‖Work.FatouCoord.chart (f0^[k] y)‖)⁻¹ ≤ (N + (k:ℝ)/2)⁻¹ := by
    have h2' : N + (k:ℝ)/2 ≤ ‖Work.FatouCoord.chart (f0^[k] y)‖ :=
      le_trans h2 (Complex.re_le_norm _)
    have hab : 0 < N + (k:ℝ)/2 := by
      have : (0:ℝ) ≤ (k:ℝ)/2 := by positivity
      linarith
    exact inv_anti₀ hab h2'
  have hle' : (N + (k:ℝ)/2)⁻¹ ≤ (N + (K:ℝ)/2)⁻¹ := by
    have h2' : N + (K:ℝ)/2 ≤ N + (k:ℝ)/2 := by
      have : (K:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
      linarith
    have h3' : 0 < N + (K:ℝ)/2 := by
      have : (0:ℝ) ≤ (K:ℝ)/2 := by positivity
      linarith
    exact inv_anti₀ h3' h2'
  have hKε : (N + (K:ℝ)/2)⁻¹ < ε := by
    rw [one_div] at hK
    exact hK
  rw [dist_eq_norm, zero_sub, norm_neg]
  calc ‖f0^[k] y‖ = (‖Work.FatouCoord.chart (f0^[k] y)‖)⁻¹ := hnorm
    _ ≤ (N + (k:ℝ)/2)⁻¹ := hle
    _ ≤ (N + (K:ℝ)/2)⁻¹ := hle'
    _ < ε := hKε

/-! ## The real interval inside the petal -/

lemma ofReal_mem_petal {r M t : ℝ} (hM : 0 < M) (hrM : 1 / M < r)
    (ht1 : -(1 / M) < t) (ht2 : t < 0) :
    (t : ℂ) ∈ Work.FatouCoord.Petal r M := by
  rw [Work.FatouCoord.mem_Petal, Complex.normSq_ofReal, Complex.norm_real, Complex.ofReal_re]
  refine ⟨?_, ?_⟩
  · rw [Real.norm_eq_abs, abs_of_neg ht2]
    have h1 : -t < 1 / M := by linarith
    linarith
  · have hMt : -1 < M * t := by
      have h1 : (1 / M) * M = 1 := by field_simp
      nlinarith [ht1, hM, h1]
    nlinarith [ht2, hMt, hM, mul_pos (neg_pos.mpr ht2) (by linarith : (0:ℝ) < 1 + M * t)]

/-! ## The petal of `f₀`, assembled -/

/-- There are `r > 0` and `M > 1/r` such that the petal `Petal r M` is connected, contained in
the parabolic basin of `0`, and contains the real interval `(-1/M, 0)`. -/
theorem exists_petal_data :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧ 1 / r < M ∧
      Work.FatouCoord.Petal r M ⊆ Basin ∧ IsConnected (Work.FatouCoord.Petal r M) ∧
      (∀ t : ℝ, -(1 / M) < t → t < 0 → (t : ℂ) ∈ Work.FatouCoord.Petal r M) := by
  obtain ⟨M₁, hM₁, hmap, hconv, hfatou, hinj, himg⟩ :=
    Work.FatouCoord.exists_petal_fatouCoord (parabolicBounds_f0 (r := 1) one_pos)
  obtain ⟨N, hNpos, hNr, hgrowth⟩ :=
    Work.FatouCoord.Estimate.iterate_re_growth (parabolicBounds_f0 (r := 1) one_pos)
  have hNm : N ≤ max M₁ (max N 2) := le_trans (le_max_left N 2) (le_max_right M₁ (max N 2))
  have h2m : (2:ℝ) ≤ max M₁ (max N 2) := le_trans (le_max_right N 2) (le_max_right M₁ (max N 2))
  have hMp : (0:ℝ) < max M₁ (max N 2) := lt_of_lt_of_le (by norm_num) h2m
  have hNM : N ≤ max M₁ (max N 2) := hNm
  refine ⟨1, max M₁ (max N 2), one_pos, hMp, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le hNr hNm
  · exact petal_subset_basin one_pos hNpos hNM hgrowth
  · refine isConnected_Petal hMp ?_
    rw [div_lt_iff₀ hMp]
    linarith
  · intro t ht1 ht2
    have h1M : 1 / max M₁ (max N 2) < 1 := by
      rw [div_lt_iff₀ hMp]
      linarith
    exact ofReal_mem_petal hMp h1M ht1 ht2

end
end Work.F0Facts
