import Mathlib
import Submission.Lib.Unif2.Commons.Analysis.Complex.exists_ball_factorization_of_analyticAt_zero
import Submission.Work.Fatou.Analysis.entireEqPolynomialOfGrowth
import Submission.Work.Fatou.Analysis.globalGrowthOfExterior

open Filter Metric
open scoped Topology

namespace Work.Horn

/-- If `f` is entire and coercive (`‖f z‖ → ∞` as `‖z‖ → ∞`), then the localization of `1/f`
at infinity, namely `w ↦ (f (w⁻¹))⁻¹` extended by `0` at `w = 0`, is analytic at `0`. -/
lemma analyticAt_zero_of_inv_comp_inv {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : ∀ R : ℝ, ∃ M : ℝ, 0 < M ∧ ∀ z : ℂ, M ≤ ‖z‖ → R ≤ ‖f z‖) :
    AnalyticAt ℂ (fun w : ℂ => if w = 0 then 0 else (f (w⁻¹))⁻¹) 0 := by
  set G : ℂ → ℂ := fun w => if w = 0 then 0 else (f (w⁻¹))⁻¹ with hG
  have htop : Tendsto (fun w : ℂ => ‖f (w⁻¹)‖) (𝓝[≠] (0 : ℂ)) atTop := by
    rw [Filter.tendsto_atTop]
    intro a
    obtain ⟨M, hMpos, hM⟩ := h a
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) (inv_pos.mpr hMpos))] with w hw hwb
    have hwne : w ≠ 0 := by simpa using hw
    have hwnorm : ‖w‖ ≤ M⁻¹ := le_of_lt (by simpa [dist_zero_right] using hwb)
    have hnorm : M ≤ ‖w⁻¹‖ := by
      rw [norm_inv]
      exact (le_inv_comm₀ hMpos (norm_pos_iff.mpr hwne)).mpr hwnorm
    exact hM w⁻¹ hnorm
  have hlim0 : Tendsto (fun w : ℂ => (f (w⁻¹))⁻¹) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h2 : Tendsto (fun w : ℂ => ‖f (w⁻¹)‖⁻¹) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
      htop.inv_tendsto_atTop
    simpa only [norm_inv] using h2
  have hlimNE : Tendsto G (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    refine hlim0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hwne : w ≠ 0 := by simpa using hw
    rw [hG]
    simp [hwne]
  have hcont : ContinuousAt G 0 := by
    rw [← continuousWithinAt_compl_self]
    simp only [ContinuousWithinAt]
    have h0 : G 0 = 0 := by simp [hG]
    rw [h0]
    exact hlimNE
  have hd : ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ G z := by
    obtain ⟨M, hMpos, hM⟩ := h 1
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) (inv_pos.mpr hMpos))] with z hz hzb
    have hzne : z ≠ 0 := by simpa using hz
    have hznorm : ‖z‖ ≤ M⁻¹ := le_of_lt (by simpa [dist_zero_right] using hzb)
    have hnorm : M ≤ ‖z⁻¹‖ := by
      rw [norm_inv]
      exact (le_inv_comm₀ hMpos (norm_pos_iff.mpr hzne)).mpr hznorm
    have hfne : f (z⁻¹) ≠ 0 := by
      have h1 : 1 ≤ ‖f (z⁻¹)‖ := hM (z⁻¹) hnorm
      intro h0
      rw [h0] at h1
      norm_num at h1
    have heq : G =ᶠ[𝓝 z] (fun w : ℂ => (f (w⁻¹))⁻¹) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hzne)] with w hw
      have hw' : w ≠ 0 := by simpa using hw
      rw [hG]
      simp [hw']
    rw [Filter.EventuallyEq.differentiableAt_iff heq]
    exact ((hf.differentiableAt (x := z⁻¹)).comp z (differentiableAt_inv hzne)).inv hfne
  exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hcont

/-- If `g` is analytic at `0` and not identically zero on any neighbourhood of `0`, then
`‖g‖` is bounded below by `c ‖z‖ ^ n` for some `n` and some `c > 0` near `0`. -/
lemma exists_pos_lower_bound_of_analyticAt_zero {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0)
    (hne : ¬ ∀ᶠ z in nhds 0, g z = 0) :
    ∃ (n : ℕ) (c : ℝ), 0 < c ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℂ, ‖z‖ < δ → c * ‖z‖ ^ n ≤ ‖g z‖ := by
  rcases eq_or_ne (g 0) 0 with h0 | h0
  · obtain ⟨R, k, ψ, hRpos, _hRlt, _hk1, hψan, hψne, hfact⟩ :=
      Commons.Analysis.Complex.exists_ball_factorization_of_analyticAt_zero (f := g) (c := 0)
        (ρ := 1) one_pos hg h0 hne
    have hψ0an : AnalyticAt ℂ ψ 0 := hψan 0 (Metric.mem_ball_self hRpos)
    have hψ0ne : ψ 0 ≠ 0 := hψne 0 (Metric.mem_ball_self hRpos)
    have hψ0pos : 0 < ‖ψ 0‖ := norm_pos_iff.mpr hψ0ne
    obtain ⟨δ, hδpos, hδ⟩ :=
      Metric.continuousAt_iff.mp hψ0an.continuousAt (‖ψ 0‖ / 2) (half_pos hψ0pos)
    refine ⟨k, ‖ψ 0‖ / 2, half_pos hψ0pos, min R δ, lt_min hRpos hδpos, ?_⟩
    intro z hz
    have hzR : z ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_lt_of_le hz (min_le_left _ _)
    have hzδ : dist z 0 < δ := by
      rw [dist_zero_right]
      exact lt_of_lt_of_le hz (min_le_right _ _)
    have hψz : ‖ψ 0‖ / 2 ≤ ‖ψ z‖ := by
      have h1 : dist (ψ z) (ψ 0) < ‖ψ 0‖ / 2 := hδ hzδ
      rw [dist_eq_norm] at h1
      have h2 : ‖ψ 0‖ - ‖ψ z‖ ≤ ‖ψ z - ψ 0‖ := by
        have h3 := norm_sub_norm_le (ψ 0) (ψ z)
        rwa [norm_sub_rev] at h3
      linarith
    have hfactz : g z = z ^ k * ψ z := by
      simpa using hfact z hzR
    rw [hfactz, norm_mul, norm_pow]
    calc ‖ψ 0‖ / 2 * ‖z‖ ^ k = ‖z‖ ^ k * (‖ψ 0‖ / 2) := mul_comm _ _
      _ ≤ ‖z‖ ^ k * ‖ψ z‖ := mul_le_mul_of_nonneg_left hψz (pow_nonneg (norm_nonneg z) k)
  · have hg0pos : 0 < ‖g 0‖ := norm_pos_iff.mpr h0
    obtain ⟨δ, hδpos, hδ⟩ :=
      Metric.continuousAt_iff.mp hg.continuousAt (‖g 0‖ / 2) (half_pos hg0pos)
    refine ⟨0, ‖g 0‖ / 2, half_pos hg0pos, δ, hδpos, ?_⟩
    intro z hz
    have h1 : dist (g z) (g 0) < ‖g 0‖ / 2 := hδ (by rw [dist_zero_right]; exact hz)
    rw [dist_eq_norm] at h1
    have h2 : ‖g 0‖ - ‖g z‖ ≤ ‖g z - g 0‖ := by
      have h3 := norm_sub_norm_le (g 0) (g z)
      rwa [norm_sub_rev] at h3
    simp only [pow_zero, mul_one]
    linarith

theorem exists_polynomial_of_proper_entire {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Set.univ)
    (hproper : ∀ L : Set ℂ, IsCompact L → IsCompact (f ⁻¹' L)) :
    ∃ P : Polynomial ℂ, ∀ z : ℂ, P.eval z = f z := by
  have hfd : Differentiable ℂ f := differentiableOn_univ.mp hf
  -- Coercivity: `‖f z‖ → ∞` as `‖z‖ → ∞`.
  have hstrict : ∀ R : ℝ, ∃ M : ℝ, 0 < M ∧ ∀ z : ℂ, M < ‖z‖ → R ≤ ‖f z‖ := by
    intro R
    have hK : IsCompact (f ⁻¹' Metric.closedBall (0 : ℂ) R) :=
      hproper _ (isCompact_closedBall (0 : ℂ) R)
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
    refine ⟨max C 0 + 1, by positivity, fun z hz => ?_⟩
    by_contra hcon
    have hlt : ‖f z‖ < R := not_le.mp hcon
    have hzK : z ∈ f ⁻¹' Metric.closedBall (0 : ℂ) R := by
      simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt hlt
    have hCz : ‖z‖ ≤ C := hC z hzK
    have hClt : C < ‖z‖ := lt_of_le_of_lt (le_max_left C 0) (lt_trans (lt_add_one (max C 0)) hz)
    linarith
  have hle : ∀ R : ℝ, ∃ M : ℝ, 0 < M ∧ ∀ z : ℂ, M ≤ ‖z‖ → R ≤ ‖f z‖ := by
    intro R
    obtain ⟨M, hMpos, hM⟩ := hstrict R
    refine ⟨max M 0 + 1, by positivity, fun z hz => hM z ?_⟩
    exact lt_of_lt_of_le (lt_of_le_of_lt (le_max_left M 0) (lt_add_one (max M 0))) hz
  have hGan : AnalyticAt ℂ (fun w : ℂ => if w = 0 then 0 else (f (w⁻¹))⁻¹) 0 :=
    analyticAt_zero_of_inv_comp_inv hfd hle
  -- `G` does not vanish near `0`.
  have hGne : ¬ ∀ᶠ z in nhds (0 : ℂ), (if z = 0 then 0 else (f (z⁻¹))⁻¹) = 0 := by
    intro hcontra
    obtain ⟨M, hMpos, hM⟩ := hle 1
    obtain ⟨η, hηpos, hη⟩ := Metric.eventually_nhds_iff.mp hcontra
    set ρ : ℝ := min η M⁻¹ / 2 with hρdef
    have hMinv : 0 < M⁻¹ := inv_pos.mpr hMpos
    have hρpos : 0 < ρ := by
      rw [hρdef]
      exact div_pos (lt_min hηpos hMinv) two_pos
    have hρη : ρ < η := by
      rw [hρdef]
      have := min_le_left η M⁻¹
      linarith
    have hρM : ρ < M⁻¹ := by
      rw [hρdef]
      have := min_le_right η M⁻¹
      linarith
    set z : ℂ := (ρ : ℂ) with hzdef
    have hznorm : ‖z‖ = ρ := by
      rw [hzdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
    have hz0 : z ≠ 0 := by
      rw [hzdef, Complex.ofReal_ne_zero]
      exact ne_of_gt hρpos
    have hGz0 : (if z = 0 then 0 else (f (z⁻¹))⁻¹) = 0 :=
      hη (by rw [dist_zero_right, hznorm]; exact hρη)
    rw [if_neg hz0] at hGz0
    have hfz0 : f (z⁻¹) = 0 := inv_eq_zero.mp hGz0
    have hMle : M ≤ ‖z⁻¹‖ := by
      rw [norm_inv, hznorm]
      exact (le_inv_comm₀ hMpos hρpos).mpr (le_of_lt hρM)
    have h1 : 1 ≤ ‖f (z⁻¹)‖ := hM (z⁻¹) hMle
    rw [hfz0] at h1
    norm_num at h1
  obtain ⟨n, c, hc, δ, hδpos, hlow⟩ := exists_pos_lower_bound_of_analyticAt_zero hGan hGne
  have h2δpos : 0 < 2 * δ⁻¹ := mul_pos two_pos (inv_pos.mpr hδpos)
  -- Exterior growth of `f`.
  have hgrowth : ∀ z : ℂ, (2 * δ⁻¹) ≤ ‖z‖ → ‖f z‖ ≤ c⁻¹ * ‖z‖ ^ n := by
    intro z hz
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le h2δpos hz
    have hzne : z ≠ 0 := by simpa [norm_pos_iff] using hzpos
    have hzδ : ‖z⁻¹‖ < δ := by
      rw [norm_inv, inv_lt_comm₀ hzpos hδpos]
      linarith
    have hb := hlow (z⁻¹) hzδ
    have hGz : (if z⁻¹ = 0 then 0 else (f ((z⁻¹)⁻¹))⁻¹) = (f z)⁻¹ := by
      rw [if_neg (inv_ne_zero hzne), inv_inv]
    rw [hGz] at hb
    have hpos : 0 < c * ‖z⁻¹‖ ^ n :=
      mul_pos hc (pow_pos (norm_pos_iff.mpr (inv_ne_zero hzne)) n)
    have key : ‖f z‖ ≤ (c * ‖z⁻¹‖ ^ n)⁻¹ := by
      have h := inv_anti₀ hpos hb
      simpa using h
    refine le_trans key ?_
    have hkey : (c * ‖z⁻¹‖ ^ n)⁻¹ = c⁻¹ * ‖z‖ ^ n := by
      rw [mul_inv, norm_inv, inv_pow, inv_inv]
    rw [hkey]
  obtain ⟨C, hC, hbdd⟩ := Work.Fatou.Analysis.globalGrowthOfExterior f hfd.continuous n c⁻¹
    (2 * δ⁻¹) (inv_pos.mpr hc) h2δpos hgrowth
  obtain ⟨P, hP, _⟩ := Work.Fatou.Analysis.entireEqPolynomialOfGrowth f hfd n C hC hbdd
  exact ⟨P, hP⟩

end Work.Horn
