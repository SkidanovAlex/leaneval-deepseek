import Mathlib
import Submission.Work.Analysis.Harmonic.integral_inner_gradient_eq_zero
import Submission.Work.Analysis.integrable_inv_norm_mul

namespace Work.Analysis.Harmonic

open MeasureTheory Filter
open scoped Topology Gradient

/-! ## Auxiliary estimates about the regularised logarithm

The target theorem is proved by regularising `−log‖·−q‖` as
`L_ε z = −(1/2)·log(‖z − q‖² + ε²)` (a smooth function, so that Green's identity applies to
`χ·L_ε` for every `ε > 0`), and passing to the limit `ε → 0⁺` by dominated convergence.  The
lemmas below collect the two real-variable inputs of that limit.
-/

/-- Size of the regularised logarithm: for `0 < ε ≤ 1` and `r > 0`,
`|½ log(r²+ε²)| ≤ 3(1+|log r|)`. -/
theorem abs_half_log_sq_add_le {r ε : ℝ} (hr : 0 < r) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    |(1 / 2) * Real.log (r ^ 2 + ε ^ 2)| ≤ 3 * (1 + |Real.log r|) := by
  have hr2pos : 0 < r ^ 2 := by positivity
  have hε2pos : 0 < ε ^ 2 := by positivity
  have hε2le : ε ^ 2 ≤ 1 := by nlinarith
  have hhalf : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
  have h2log : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  rw [abs_mul, hhalf]
  rcases le_or_gt 1 r with hr1 | hr1
  · have h1 : r ^ 2 ≤ r ^ 2 + ε ^ 2 := by linarith
    have h2 : r ^ 2 + ε ^ 2 ≤ 2 * r ^ 2 := by nlinarith
    have hlog1 : Real.log (r ^ 2) ≤ Real.log (r ^ 2 + ε ^ 2) := Real.log_le_log hr2pos h1
    have hlog2 : Real.log (r ^ 2 + ε ^ 2) ≤ Real.log (2 * r ^ 2) :=
      Real.log_le_log (by linarith) h2
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog2
    rw [Real.log_pow] at hlog1
    push_cast at hlog1 hlog2
    have hlogrn : 0 ≤ Real.log r := Real.log_nonneg hr1
    have hlogpos : 0 ≤ Real.log (r ^ 2 + ε ^ 2) := by linarith
    rw [abs_of_nonneg hlogpos, abs_of_nonneg hlogrn]
    linarith
  · have hrle : r ≤ 1 := le_of_lt hr1
    have h1 : r ^ 2 ≤ r ^ 2 + ε ^ 2 := by linarith
    have h2 : r ^ 2 + ε ^ 2 ≤ 2 := by nlinarith
    have hlog1 : Real.log (r ^ 2) ≤ Real.log (r ^ 2 + ε ^ 2) := Real.log_le_log hr2pos h1
    have hlog2 : Real.log (r ^ 2 + ε ^ 2) ≤ Real.log 2 :=
      Real.log_le_log (by linarith) h2
    rw [Real.log_pow] at hlog1
    push_cast at hlog1
    have hlogrnonpos : Real.log r ≤ 0 := Real.log_nonpos (le_of_lt hr) hrle
    have hkey : Real.log (r ^ 2 + ε ^ 2) ≤ 2 * |Real.log r| + 2 := by
      have : Real.log r = -|Real.log r| := by rw [abs_of_nonpos hlogrnonpos]; ring
      linarith
    have hkey2 : -(2 * |Real.log r| + 2) ≤ Real.log (r ^ 2 + ε ^ 2) := by
      have h2r : 2 * Real.log r = -(2 * |Real.log r|) := by
        rw [abs_of_nonpos hlogrnonpos]; ring
      linarith
    have habs : |Real.log (r ^ 2 + ε ^ 2)| ≤ 2 * |Real.log r| + 2 := abs_le.mpr ⟨hkey2, hkey⟩
    linarith [abs_nonneg (Real.log r)]

/-- `log(1/r) ≤ 2/√r` for `0 < r`. -/
theorem log_inv_le_two_mul_rpow {r : ℝ} (hr : 0 < r) :
    Real.log (1 / r) ≤ 2 * r ^ (-(1 / 2 : ℝ)) := by
  have hx : (0:ℝ) ≤ 1 / r := by positivity
  have h := Real.log_le_rpow_div (x := 1 / r) hx (by norm_num : (0:ℝ) < 1 / 2)
  have heq : (1 / r) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * r ^ (-(1 / 2 : ℝ)) := by
    rw [one_div, Real.inv_rpow (le_of_lt hr), Real.rpow_neg (le_of_lt hr)]
    field_simp
  rwa [heq] at h

/-- `1 + |log r| ≤ C/r` on `(0,R]`, with a constant `C` depending only on `R`. -/
theorem one_add_abs_log_le_const_div {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    1 + |Real.log r| ≤ (max 3 (max R 1 * (1 + |Real.log (max R 1)|))) / r := by
  set R' : ℝ := max R 1 with hR'def
  have hR'1 : 1 ≤ R' := le_max_right _ _
  have hrR' : r ≤ R' := le_trans hrR (le_max_left _ _)
  rw [le_div_iff₀ hr]
  rcases le_or_gt 1 r with hr1 | hr1
  · have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1
    have hlogR' : 0 ≤ Real.log R' := Real.log_nonneg hR'1
    have hlogrR' : Real.log r ≤ Real.log R' := Real.log_le_log hr hrR'
    rw [abs_of_nonneg hlogr, abs_of_nonneg hlogR']
    have h1 : (1 + Real.log r) * r ≤ R' * (1 + Real.log R') :=
      calc (1 + Real.log r) * r ≤ (1 + Real.log R') * R' :=
            mul_le_mul (by linarith) hrR' (le_of_lt hr) (by linarith)
        _ = R' * (1 + Real.log R') := by ring
    exact le_trans h1 (le_max_right _ _)
  · have hrle : r ≤ 1 := le_of_lt hr1
    have hlogrnonpos : Real.log r ≤ 0 := Real.log_nonpos (le_of_lt hr) hrle
    have hloginv : Real.log r⁻¹ ≤ 2 * r ^ (-(1 / 2 : ℝ)) := by
      have := log_inv_le_two_mul_rpow hr
      rwa [one_div] at this
    rw [abs_of_nonpos hlogrnonpos, ← Real.log_inv]
    have hsqrt : r ^ (1 / 2 : ℝ) ≤ 1 := by
      have := Real.rpow_le_rpow (le_of_lt hr) hrle (by norm_num : (0:ℝ) ≤ 1 / 2)
      rwa [Real.one_rpow] at this
    have hrpow : r ^ (-(1 / 2 : ℝ)) * r ≤ 1 := by
      calc r ^ (-(1 / 2 : ℝ)) * r = r ^ (-(1 / 2 : ℝ)) * r ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = r ^ (-(1 / 2 : ℝ) + 1) := by rw [Real.rpow_add hr]
        _ = r ^ (1 / 2 : ℝ) := by norm_num
        _ ≤ 1 := hsqrt
    have h3 : r * Real.log r⁻¹ ≤ 2 := by
      have h4 : r * Real.log r⁻¹ ≤ r * (2 * r ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hloginv (le_of_lt hr)
      nlinarith [h4, hrpow]
    nlinarith [h3, le_of_lt hr, hrle, le_max_left (3:ℝ) (R' * (1 + |Real.log R'|))]

/-- The gradient of the regularised logarithm
`z ↦ −(1/2)·log(‖z−q‖²+ε²)` is `−(‖z−q‖²+ε²)⁻¹ • (z−q)`. -/
theorem gradient_neg_half_log_normSq_add (q z : ℂ) (ε : ℝ) (h : ‖z - q‖ ^ 2 + ε ^ 2 ≠ 0) :
    gradient (fun w : ℂ => -(1 / 2 : ℝ) * Real.log (‖w - q‖ ^ 2 + ε ^ 2)) z
      = -((‖z - q‖ ^ 2 + ε ^ 2)⁻¹) • (z - q) := by
  have hbase : HasFDerivAt (fun w : ℂ => w - q) (ContinuousLinearMap.id ℝ ℂ) z :=
    (hasFDerivAt_id z).sub_const q
  have h1 : HasFDerivAt (fun w : ℂ => ‖w - q‖ ^ 2) (2 • innerSL ℝ (z - q)) z := by
    simpa using hbase.norm_sq
  have h2 : HasFDerivAt (fun w : ℂ => ‖w - q‖ ^ 2 + ε ^ 2) (2 • innerSL ℝ (z - q)) z :=
    h1.add_const (ε ^ 2)
  have h3 : HasFDerivAt (fun w : ℂ => Real.log (‖w - q‖ ^ 2 + ε ^ 2))
      ((‖z - q‖ ^ 2 + ε ^ 2)⁻¹ • (2 • innerSL ℝ (z - q))) z := h2.log h
  have h4 : HasFDerivAt (fun w : ℂ => -(1 / 2 : ℝ) * Real.log (‖w - q‖ ^ 2 + ε ^ 2))
      (-(1 / 2 : ℝ) • ((‖z - q‖ ^ 2 + ε ^ 2)⁻¹ • (2 • innerSL ℝ (z - q)))) z :=
    h3.const_mul (-(1 / 2 : ℝ))
  refine ext_inner_left ℝ fun y => ?_
  rw [real_inner_comm (gradient (fun w : ℂ => -(1 / 2 : ℝ) * Real.log (‖w - q‖ ^ 2 + ε ^ 2)) z) y,
    inner_gradient_left, h4.fderiv]
  simp only [smul_apply, innerSL_apply_apply, real_inner_smul_right, real_inner_comm (z - q) y]
  ring

/-- Leibniz rule for the gradient of a product of two real-valued functions on `ℂ`
(the version `Work.Drive.gradient_mul_real`, reproved here to keep the imports light). -/
theorem gradient_mul_real {f g : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    gradient (fun w => f w * g w) z = f z • gradient g z + g z • gradient f z := by
  show (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ (f * g) z) = _
  rw [fderiv_mul hf hg, map_add, map_smul, map_smul]
  rfl

/-- **The logarithmic test function pairs to zero against a locally harmonic function.** If `h` is harmonic on the open ball `B(q,ρ)` and `χ` is `C¹` with compact support contained in that ball, then `∫_ℂ ⟪∇h, ∇(χ · (−log‖·−q‖))⟫ = 0`. (Proof idea, cut-off plus limit: for `ε > 0` let `θ_ε` be a smooth bump with `θ_ε = 1` on `B(q,ε)`, `tsupport θ_ε ⊆ closedBall q (2ε)` and `‖∇θ_ε‖ ≤ C/ε`; then `χ·L·(1−θ_ε)` (`L = −log‖·−q‖`) is `C¹` with compact support and `h` is harmonic on its support, so Green's identity `integral_inner_gradient_eq_zero` gives `∫ ⟪∇h, ∇(χL(1−θ_ε))⟫ = 0`; finally `∫⟪∇h,∇(χL)⟫ = ∫⟪∇h,∇(χL(1−θ_ε))⟫ + ∫⟪∇h,∇(χLθ_ε)⟫` and the last term tends to `0` as `ε → 0`, by splitting `∇(χLθ_ε) = θ_ε∇(χL) + χL∇θ_ε`: `θ_ε → 0` pointwise off `q` dominated by `1/‖·−q‖` (integrable), and `|χL∇θ_ε| ≲ log(1/‖·−q‖)/‖·−q‖` (integrable) using `1/ε ≤ 2/‖·−q‖` on the support of `∇θ_ε`.) -/
theorem integral_inner_gradient_mul_log_eq_zero {h χ : ℂ → ℝ} {q : ℂ} {ρ : ℝ}
    (hho : ∀ z : ℂ, ‖z - q‖ < ρ → InnerProductSpace.HarmonicAt h z)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hsub : tsupport χ ⊆ Metric.ball q ρ) :
    ∫ z, inner (𝕜 := ℝ) (gradient h z) (gradient (fun z ↦ χ z * (-Real.log ‖z - q‖)) z) = 0 := by
  classical
  -- The target test function, written with `log(‖z-q‖²)` instead of `log‖z-q‖`.
  have hug : (fun z : ℂ => χ z * (-Real.log ‖z - q‖))
      = fun z : ℂ => χ z * (-(1 / 2 : ℝ) * Real.log (‖z - q‖ ^ 2)) := by
    funext z
    rw [Real.log_pow]
    push_cast
    ring
  rw [hug]
  -- ===== the cut-off `ψ`, the harmonic function `H = ψ * h` =====
  obtain ⟨R₀, hR₀⟩ := hχc.isBounded.subset_closedBall (0 : ℂ)
  set R : ℝ := max R₀ 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  obtain ⟨Rq₀, hRq₀⟩ := hχc.isBounded.subset_closedBall q
  set Rq : ℝ := max Rq₀ 1 with hRqdef
  have hRq1 : 1 ≤ Rq := le_max_right _ _
  have hKRq : ∀ z ∈ tsupport χ, ‖z - q‖ ≤ Rq := fun z hz => by
    have h := Metric.mem_closedBall.mp (hRq₀ hz)
    rw [dist_eq_norm] at h
    exact le_trans h (le_max_left _ _)
  have hKball : tsupport χ ⊆ Metric.closedBall 0 R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hKball' : tsupport χ ⊆ Metric.ball 0 (R + 1) := by
    intro z hz
    have h := Metric.mem_closedBall.mp (hKball hz)
    rw [dist_zero_right] at h
    exact Metric.mem_ball.mpr (by rw [dist_zero_right]; linarith)
  have hKU : tsupport χ ⊆ {z : ℂ | InnerProductSpace.HarmonicAt h z} ∩ Metric.ball 0 (R+1) := by
    intro z hz
    exact ⟨hho z (by have h := Metric.mem_ball.mp (hsub hz); rwa [dist_eq_norm] at h), hKball' hz⟩
  obtain ⟨ψ, hψC, hψsupp, V, hVopen, hKV, hψV⟩ :=
    exists_contDiff_eqOn_one_of_isCompact_subset_isOpen hχc
      ((InnerProductSpace.isOpen_setOfPred_harmonicAt h).inter Metric.isOpen_ball) hKU
  set H : ℂ → ℝ := fun z => ψ z * h z with hHdef
  have hHC : ContDiff ℝ 2 H := by
    rw [hHdef]
    refine contDiff_iff_contDiffAt.mpr fun z => ?_
    by_cases hz : z ∈ tsupport ψ
    · exact hψC.contDiffAt.mul ((hψsupp hz).1).1
    · have hzero : (fun y => ψ y * h y) =ᶠ[𝓝 z] 0 := by
        filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hz] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy]
        simp
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  have hsub1 : tsupport H ⊆ tsupport ψ := by
    rw [tsupport, tsupport]
    exact closure_mono fun z hz => by
      rw [Function.mem_support] at hz ⊢
      intro hzψ
      exact hz (by rw [hHdef]; simp [hzψ])
  have hHsupp : tsupport H ⊆ Metric.ball 0 (R+1) := fun z hz => (hψsupp (hsub1 hz)).2
  have hHcs : HasCompactSupport H :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (R+1))
      (fun z hz => Metric.ball_subset_closedBall (hHsupp (subset_tsupport H hz)))
  have hHeq : ∀ z ∈ tsupport χ, H =ᶠ[𝓝 z] h := by
    intro z hz
    filter_upwards [hVopen.mem_nhds (hKV hz)] with y hy
    show ψ y * h y = h y
    rw [hψV hy, Pi.one_apply, one_mul]
  have hgradHeq : ∀ z ∈ tsupport χ, gradient H z = gradient h z :=
    fun z hz => (hHeq z hz).gradient_eq
  have hHharm : ∀ z ∈ tsupport χ, InnerProductSpace.HarmonicAt H z := by
    intro z hz
    have hzh : InnerProductSpace.HarmonicAt h z :=
      hho z (by have h := Metric.mem_ball.mp (hsub hz); rwa [dist_eq_norm] at h)
    exact ⟨(hzh.1).congr_of_eventuallyEq (hHeq z hz),
      (InnerProductSpace.laplacian_congr_nhds (hHeq z hz)).trans hzh.2⟩
  -- ===== the constants of the domination =====
  have hHgradcont : Continuous (gradient H) := by
    have h1 : Continuous (fderiv ℝ H) := hHC.continuous_fderiv (by norm_num)
    exact (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp h1
  obtain ⟨MH₀, hMH₀⟩ : ∃ M : ℝ, ∀ z : ℂ, ‖gradient H z‖ ≤ M := by
    have hcs : HasCompactSupport (gradient H) :=
      IsCompact.of_isClosed_subset hHcs (isClosed_tsupport _)
        (tsupport_gradient_subset H)
    obtain ⟨C', hC'⟩ := hcs.exists_bound_of_continuousOn hHgradcont.continuousOn
    exact ⟨max C' 0, fun z => by
      by_cases hz : z ∈ tsupport (gradient H)
      · exact le_trans (hC' z hz) (le_max_left _ _)
      · rw [image_eq_zero_of_notMem_tsupport hz]; simp⟩
  obtain ⟨Cχ₀, hCχ₀⟩ := hχc.exists_bound_of_continuousOn hχ.continuous.continuousOn
  have hχgradcont : Continuous (gradient χ) := by
    have h1 : Continuous (fderiv ℝ χ) := hχ.continuous_fderiv (by norm_num)
    exact (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp h1
  obtain ⟨Cg₀, hCg₀⟩ := hχc.exists_bound_of_continuousOn hχgradcont.continuousOn
  set MH : ℝ := max MH₀ 0
  set Cχ : ℝ := max Cχ₀ 0
  set Cg : ℝ := max Cg₀ 0
  have hMH : ∀ z : ℂ, ‖gradient H z‖ ≤ MH := fun z => le_trans (hMH₀ z) (le_max_left _ _)
  have hCχ : ∀ z ∈ tsupport χ, ‖χ z‖ ≤ Cχ := fun z hz => le_trans (hCχ₀ z hz) (le_max_left _ _)
  have hCg : ∀ z ∈ tsupport χ, ‖gradient χ z‖ ≤ Cg :=
    fun z hz => le_trans (hCg₀ z hz) (le_max_left _ _)
  have hMHnn : 0 ≤ MH := le_max_right _ _
  have hCχnn : 0 ≤ Cχ := le_max_right _ _
  have hCgnn : 0 ≤ Cg := le_max_right _ _
  set C : ℝ := max 3 (Rq * (1 + |Real.log Rq|))
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  -- the dominating weight `|ψ|`
  have hφcont : Continuous (fun z : ℂ => |ψ z|) := continuous_abs.comp hψC.continuous
  have hφcs : HasCompactSupport (fun z : ℂ => |ψ z|) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (R+1)) ?_
    intro z hz
    rw [Function.mem_support] at hz
    refine Metric.ball_subset_closedBall ((hψsupp (subset_tsupport ψ ?_)).2)
    rw [Function.mem_support]
    intro h0
    exact hz (by rw [h0, abs_zero])
  have hφψ : ∀ z ∈ tsupport χ, |ψ z| = 1 := by
    intro z hz
    rw [hψV (hKV hz), Pi.one_apply, abs_one]
  have hgint : Integrable (fun z : ℂ =>
      (Cχ * MH + 3 * Cg * C * MH) * ((‖z - q‖)⁻¹ * |ψ z|)) :=
    (Work.Analysis.integrable_inv_norm_mul_of_hasCompactSupport q (fun z => |ψ z|)
      hφcont hφcs).const_mul _
  -- ===== the regularising family `uf ε` and Green's identity =====
  set eps : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hepsdef
  have hepspos : ∀ n, 0 < eps n := fun n => by rw [hepsdef]; positivity
  have hepsle : ∀ n, eps n ≤ 1 := fun n => by
    rw [hepsdef, div_le_one (by positivity)]
    have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hepstend : Tendsto eps atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
        tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ)) (g := fun n : ℕ => (n : ℝ) + 1)
          (fun n => by norm_num) tendsto_natCast_atTop_atTop
      exact h2.inv_tendsto_atTop
    simpa [hepsdef, one_div] using h1
  set uf : ℝ → ℂ → ℝ := fun ε z => χ z * (-(1 / 2 : ℝ) * Real.log (‖z - q‖ ^ 2 + ε ^ 2))
    with hufdef
  have hufL_cd : ∀ n, ContDiff ℝ 1
      (fun z : ℂ => -(1 / 2 : ℝ) * Real.log (‖z - q‖ ^ 2 + eps n ^ 2)) := by
    intro n
    have hA : ContDiff ℝ 1 (fun z : ℂ => ‖z - q‖ ^ 2 + eps n ^ 2) :=
      ((contDiff_norm_sq (𝕜 := ℝ)).comp (contDiff_id.sub contDiff_const)).add contDiff_const
    have hB : ContDiff ℝ 1 (fun z : ℂ => Real.log (‖z - q‖ ^ 2 + eps n ^ 2)) :=
      hA.log (fun z => by positivity)
    exact contDiff_const.mul hB
  have hsub_supp : ∀ ε : ℝ, Function.support (uf ε) ⊆ tsupport χ := by
    intro ε z hz
    exact subset_tsupport χ (by
      rw [Function.mem_support] at hz ⊢
      intro h
      exact hz (by rw [hufdef]; simp [h]))
  have hsub_ts : ∀ ε : ℝ, tsupport (uf ε) ⊆ tsupport χ :=
    fun ε => closure_minimal (hsub_supp ε) (isClosed_tsupport χ)
  have huf_cs : ∀ n, HasCompactSupport (uf (eps n)) :=
    fun n => HasCompactSupport.of_support_subset_isCompact hχc (hsub_supp (eps n))
  have huf_cd : ∀ n, ContDiff ℝ 1 (uf (eps n)) := fun n => hχ.mul (hufL_cd n)
  have hgreen : ∀ n, ∫ z, inner (𝕜 := ℝ) (gradient H z) (gradient (uf (eps n)) z) = 0 := by
    intro n
    exact integral_inner_gradient_eq_zero
      (fun z hz => hHharm z (hsub_ts (eps n) hz)) (huf_cd n) (huf_cs n)
  -- ===== the gradient formula for `uf ε` =====
  have heps2pos : ∀ n : ℕ, (0:ℝ) < eps n ^ 2 := fun n => pow_pos (hepspos n) 2
  have hgradL : ∀ (n : ℕ) (z : ℂ), gradient
      (fun w : ℂ => -(1 / 2 : ℝ) * Real.log (‖w - q‖ ^ 2 + eps n ^ 2)) z
        = -((‖z - q‖ ^ 2 + eps n ^ 2)⁻¹) • (z - q) := fun n z =>
    gradient_neg_half_log_normSq_add q z (eps n)
      (by have h2 : (0:ℝ) ≤ ‖z - q‖ ^ 2 := sq_nonneg _; linarith [heps2pos n])
  -- ===== the domination =====
  have hdom : ∀ n : ℕ, ∀ᵐ z ∂(volume : Measure ℂ),
      ‖inner (𝕜 := ℝ) (gradient H z) (gradient (uf (eps n)) z)‖
        ≤ (Cχ * MH + 3 * Cg * C * MH) * ((‖z - q‖)⁻¹ * |ψ z|) := by
    intro n
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton q)] with z hzq
    have hzq' : z ≠ q := by simpa using hzq
    have hrpos : 0 < ‖z - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzq')
    have hr2pos : 0 < ‖z - q‖ ^ 2 + eps n ^ 2 := by linarith [heps2pos n, sq_nonneg (‖z - q‖)]
    by_cases hzK : z ∈ tsupport χ
    · have hdiffχ : DifferentiableAt ℝ χ z := (hχ.differentiable one_ne_zero).differentiableAt
      have hdiffL : DifferentiableAt ℝ
          (fun w : ℂ => -(1 / 2 : ℝ) * Real.log (‖w - q‖ ^ 2 + eps n ^ 2)) z :=
        ((hufL_cd n).differentiable one_ne_zero).differentiableAt
      have huf_eq : uf (eps n)
          = fun w : ℂ => χ w * (-(1 / 2 : ℝ) * Real.log (‖w - q‖ ^ 2 + eps n ^ 2)) := by
        funext w
        rw [hufdef]
      have hb1 : ‖inner (𝕜 := ℝ) (gradient H z) (gradient χ z)‖ ≤ MH * Cg :=
        le_trans (norm_inner_le_norm _ _)
          (mul_le_mul (hMH z) (hCg z hzK) (norm_nonneg _) (le_trans (norm_nonneg _) (hMH 0)))
      have hb2 : ‖inner (𝕜 := ℝ) (gradient H z) (-((‖z - q‖ ^ 2 + eps n ^ 2)⁻¹) • (z - q))‖
          ≤ MH * ((‖z - q‖ ^ 2 + eps n ^ 2)⁻¹ * ‖z - q‖) := by
        have hnorm : ‖-((‖z - q‖ ^ 2 + eps n ^ 2)⁻¹) • (z - q)‖
            = (‖z - q‖ ^ 2 + eps n ^ 2)⁻¹ * ‖z - q‖ := by
          rw [norm_smul, norm_neg,
            Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (‖z - q‖ ^ 2 + eps n ^ 2)⁻¹)]
        exact le_trans (norm_inner_le_norm _ _) (mul_le_mul (hMH z) (le_of_eq hnorm) (norm_nonneg _) hMHnn)
      have hX : (‖z - q‖ ^ 2 + eps n ^ 2)⁻¹ * ‖z - q‖ ≤ (‖z - q‖)⁻¹ := by
        rw [inv_mul_le_iff₀ hr2pos, ← div_eq_mul_inv, le_div_iff₀ hrpos]
        nlinarith [sq_nonneg (eps n)]
      have hlogb : |-(1 / 2 : ℝ) * Real.log (‖z - q‖ ^ 2 + eps n ^ 2)|
          ≤ 3 * (1 + |Real.log ‖z - q‖|) := by
        rw [neg_mul, abs_neg]
        exact abs_half_log_sq_add_le hrpos (hepspos n) (hepsle n)
      have hlogC : 1 + |Real.log ‖z - q‖| ≤ C * (‖z - q‖)⁻¹ := by
        have h := one_add_abs_log_le_const_div (R := Rq) hrpos (hKRq z hzK)
        rwa [max_eq_left hRq1] at h
      have h1b : |χ z| * ‖inner (𝕜 := ℝ) (gradient H z) (-((‖z - q‖ ^ 2 + eps n ^ 2)⁻¹) • (z - q))‖
          ≤ (Cχ * MH) * ((‖z - q‖)⁻¹ * |ψ z|) := by
        rw [hφψ z hzK, mul_one]
        calc |χ z| * ‖inner (𝕜 := ℝ) (gradient H z) (-((‖z - q‖ ^ 2 + eps n ^ 2)⁻¹) • (z - q))‖
            ≤ Cχ * (MH * ((‖z - q‖ ^ 2 + eps n ^ 2)⁻¹ * ‖z - q‖)) :=
              mul_le_mul (hCχ z hzK) hb2 (norm_nonneg _) (by positivity)
          _ = Cχ * MH * ((‖z - q‖ ^ 2 + eps n ^ 2)⁻¹ * ‖z - q‖) := by ring
          _ ≤ Cχ * MH * (‖z - q‖)⁻¹ := mul_le_mul_of_nonneg_left hX (by positivity)
          _ = (Cχ * MH) * (‖z - q‖)⁻¹ := by ring
      have h2b : |-(1 / 2 : ℝ) * Real.log (‖z - q‖ ^ 2 + eps n ^ 2)|
            * ‖inner (𝕜 := ℝ) (gradient H z) (gradient χ z)‖
          ≤ (3 * Cg * C * MH) * ((‖z - q‖)⁻¹ * |ψ z|) := by
        rw [hφψ z hzK, mul_one]
        calc |-(1 / 2 : ℝ) * Real.log (‖z - q‖ ^ 2 + eps n ^ 2)|
              * ‖inner (𝕜 := ℝ) (gradient H z) (gradient χ z)‖
            ≤ |-(1 / 2 : ℝ) * Real.log (‖z - q‖ ^ 2 + eps n ^ 2)| * (MH * Cg) :=
              mul_le_mul_of_nonneg_left hb1 (abs_nonneg _)
          _ ≤ (3 * (1 + |Real.log ‖z - q‖|)) * (MH * Cg) :=
              mul_le_mul_of_nonneg_right hlogb (by positivity)
          _ ≤ (3 * (C * (‖z - q‖)⁻¹)) * (MH * Cg) :=
              mul_le_mul_of_nonneg_right (by linarith [hlogC]) (by positivity)
          _ = (3 * Cg * C * MH) * (‖z - q‖)⁻¹ := by ring
      rw [huf_eq, gradient_mul_real hdiffχ hdiffL]
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      rw [hgradL n z]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine le_trans (add_le_add h1b h2b) ?_
      rw [← add_mul]
    · have hz0 : gradient (uf (eps n)) z = 0 :=
        gradient_eq_zero_of_notMem_tsupport fun hmem => hzK (hsub_ts (eps n) hmem)
      rw [hz0, inner_zero_right, norm_zero]
      refine mul_nonneg ?_ (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (abs_nonneg _))
      exact add_nonneg (mul_nonneg hCχnn hMHnn)
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCgnn) hCpos.le) hMHnn)
  -- ===== measurability =====
  have hmeas : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable
      (fun z : ℂ => inner (𝕜 := ℝ) (gradient H z) (gradient (uf (eps n)) z)) volume := by
    refine Eventually.of_forall fun n => ?_
    have hcont : Continuous (gradient (uf (eps n))) := by
      have h1 : Continuous (fderiv ℝ (uf (eps n))) := (huf_cd n).continuous_fderiv (by norm_num)
      exact (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp h1
    exact (hHgradcont.inner hcont).aestronglyMeasurable
  -- ===== pointwise convergence =====
  have hconv : ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => inner (𝕜 := ℝ) (gradient H z) (gradient (uf (eps n)) z)) atTop
        (𝓝 (inner (𝕜 := ℝ) (gradient H z) (gradient (uf 0) z))) := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton q)] with z hzq
    have hzq' : z ≠ q := by simpa using hzq
    have hrpos : 0 < ‖z - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzq')
    have hnum : ContinuousAt (fun ε : ℝ => ‖z - q‖ ^ 2 + ε ^ 2) 0 :=
      continuousAt_const.add (by
        simpa using (continuous_pow 2 : Continuous fun ε : ℝ => ε ^ 2).continuousAt)
    have hnumpos : (0:ℝ) < ‖z - q‖ ^ 2 + (0:ℝ) ^ 2 := by positivity
    have hnum0 : ‖z - q‖ ^ 2 + (0:ℝ) ^ 2 ≠ 0 := ne_of_gt hnumpos
    have hlogc : ContinuousAt (fun ε : ℝ => Real.log (‖z - q‖ ^ 2 + ε ^ 2)) 0 :=
      hnum.log hnum0
    have hinvc : ContinuousAt (fun ε : ℝ => (‖z - q‖ ^ 2 + ε ^ 2)⁻¹) 0 := hnum.inv₀ hnum0
    set V : ℝ → ℂ := fun ε =>
      (-(1 / 2 : ℝ) * Real.log (‖z - q‖ ^ 2 + ε ^ 2)) • gradient χ z
        + χ z • (-(‖z - q‖ ^ 2 + ε ^ 2)⁻¹ • (z - q)) with hVdef
    have hVcont : ContinuousAt V 0 := by
      rw [hVdef]
      refine ContinuousAt.add ?_ ?_
      · exact (hlogc.const_mul (-(1 / 2 : ℝ))).smul continuousAt_const
      · have hin : ContinuousAt (fun ε : ℝ => (-(‖z - q‖ ^ 2 + ε ^ 2)⁻¹) • (z - q)) 0 :=
          (hinvc.neg).smul_const (z - q)
        exact hin.const_smul (χ z)
    have hVeq : ∀ ε : ℝ, gradient (uf ε) z = V ε := by
      intro ε
      have huf_eq : uf ε
          = fun w : ℂ => χ w * (-(1 / 2 : ℝ) * Real.log (‖w - q‖ ^ 2 + ε ^ 2)) := by
        funext w
        rw [hufdef]
      have hdiffχ : DifferentiableAt ℝ χ z := (hχ.differentiable one_ne_zero).differentiableAt
      have hdiffL : DifferentiableAt ℝ
          (fun w : ℂ => -(1 / 2 : ℝ) * Real.log (‖w - q‖ ^ 2 + ε ^ 2)) z := by
        have h1 : HasFDerivAt (fun w : ℂ => w - q) (ContinuousLinearMap.id ℝ ℂ) z :=
          (hasFDerivAt_id z).sub_const q
        have h2 : HasFDerivAt (fun w : ℂ => ‖w - q‖ ^ 2) (2 • innerSL ℝ (z - q)) z := by
          simpa using h1.norm_sq
        have h3 : HasFDerivAt (fun w : ℂ => ‖w - q‖ ^ 2 + ε ^ 2) (2 • innerSL ℝ (z - q)) z :=
          h2.add_const (ε ^ 2)
        have h4 : (0:ℝ) < ‖z - q‖ ^ 2 + ε ^ 2 := by
          nlinarith [hrpos, norm_nonneg (z - q), sq_nonneg ε]
        exact ((h3.log (ne_of_gt h4)).const_mul (-(1 / 2 : ℝ))).differentiableAt
      have hgl : gradient (fun w : ℂ => -(1 / 2 : ℝ) * Real.log (‖w - q‖ ^ 2 + ε ^ 2)) z
          = -((‖z - q‖ ^ 2 + ε ^ 2)⁻¹) • (z - q) :=
        gradient_neg_half_log_normSq_add q z ε
          (by have h2 : (0:ℝ) < ‖z - q‖ ^ 2 := by nlinarith [hrpos, norm_nonneg (z - q)]
              have h3 : (0:ℝ) ≤ ε ^ 2 := sq_nonneg ε
              linarith)
      rw [huf_eq, gradient_mul_real hdiffχ hdiffL, hgl]
      rw [add_comm, hVdef]
    have h1 : Tendsto (fun n => gradient (uf (eps n)) z) atTop (𝓝 (gradient (uf 0) z)) := by
      have h0 : V 0 = gradient (uf 0) z := (hVeq 0).symm
      rw [← h0]
      exact (hVcont.tendsto.comp hepstend).congr'
        (Eventually.of_forall fun n => (hVeq (eps n)).symm)
    exact Filter.Tendsto.inner tendsto_const_nhds h1
  -- ===== dominated convergence =====
  have hDCT := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure ℂ))
      (l := atTop) (bound := fun z : ℂ => (Cχ * MH + 3 * Cg * C * MH) * ((‖z - q‖)⁻¹ * |ψ z|))
      (F := fun n z => inner (𝕜 := ℝ) (gradient H z) (gradient (uf (eps n)) z))
      (f := fun z => inner (𝕜 := ℝ) (gradient H z) (gradient (uf 0) z))
      hmeas (Eventually.of_forall hdom) hgint hconv
  have hzero : Tendsto (fun n => ∫ z, inner (𝕜 := ℝ) (gradient H z) (gradient (uf (eps n)) z))
      atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (Eventually.of_forall fun n => (hgreen n).symm)
  have hlim0 : (∫ z, inner (𝕜 := ℝ) (gradient H z) (gradient (uf 0) z)) = 0 :=
    tendsto_nhds_unique hDCT hzero
  -- ===== transfer from `H` back to `h` =====
  have hu0 : (fun z : ℂ => χ z * (-(1 / 2 : ℝ) * Real.log (‖z - q‖ ^ 2))) = uf 0 := by
    funext z
    rw [hufdef]
    norm_num
  have hpoint : ∀ z : ℂ, inner (𝕜 := ℝ) (gradient h z) (gradient (uf 0) z)
      = inner (𝕜 := ℝ) (gradient H z) (gradient (uf 0) z) := by
    intro z
    by_cases hz : gradient (uf 0) z = 0
    · rw [hz, inner_zero_right, inner_zero_right]
    · have hzK : z ∈ tsupport χ := by
        refine hsub_ts 0 ?_
        by_contra hmem
        exact hz (gradient_eq_zero_of_notMem_tsupport hmem)
      rw [← hgradHeq z hzK]
  rw [hu0, integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  exact hlim0

end Work.Analysis.Harmonic
