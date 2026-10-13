import Mathlib
import Submission.Work.WilE3.MPsi.rpow_ascent

namespace Work.WilE3.MPsi

open Classical Topology Filter

/-- For the Pi (sup) norm on `Fin k → ℝ`, the square of the norm is at most the sum of the squares
of the coordinates. -/
private theorem norm_sq_le_sum_sq {k : ℕ} (v : Fin k → ℝ) : ‖v‖ ^ 2 ≤ ∑ i, v i ^ 2 := by
  have h1 : ‖v‖ ≤ Real.sqrt (∑ i, v i ^ 2) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    calc |v i| = Real.sqrt (v i ^ 2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt (∑ j, v j ^ 2) := by
          apply Real.sqrt_le_sqrt
          exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  have hS : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  calc ‖v‖ ^ 2 ≤ (Real.sqrt (∑ i, v i ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg v) h1 2
    _ = ∑ i, v i ^ 2 := Real.sq_sqrt hS

/-- The squared-distance function `w ↦ ∑ᵢ (wᵢ - yᵢ)²` is differentiable at `z`. -/
private theorem hasFDerivAt_sumSq {k : ℕ} (y z : Fin k → ℝ) :
    HasFDerivAt (fun x : Fin k → ℝ => ∑ i, (x i - y i) ^ 2)
      (∑ i, ((2 : ℝ) * (z i - y i)) •
        (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)) z := by
  have h : ∀ i : Fin k, HasFDerivAt (fun w : Fin k → ℝ => (w i - y i) ^ 2)
      (((2 : ℝ) * (z i - y i)) • (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)) z := by
    intro i
    have h1 : HasFDerivAt (fun w : Fin k → ℝ => w i - y i)
        (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ) z := by
      simpa using (hasFDerivAt_apply (𝕜 := ℝ) i z).sub_const (y i)
    simpa using h1.pow 2
  have hs := HasFDerivAt.sum (u := Finset.univ) (fun i _ => h i)
  have hfun : (∑ i, fun w : Fin k → ℝ => (w i - y i) ^ 2)
      = fun w => ∑ i, (w i - y i) ^ 2 := by
    funext w; simp [Finset.sum_apply]
  rwa [hfun] at hs

/-- The operator norm of the Fréchet derivative of `x ↦ ∑ᵢ (xᵢ - yᵢ)²` at `z` is at most
`2 ∑ᵢ |zᵢ - yᵢ|`: the domain `Fin k → ℝ` carries the sup norm, so the operator norm of the
differential `v ↦ 2 ∑ᵢ (zᵢ - yᵢ) vᵢ` is controlled by the ℓ¹-norm of the displacement. -/
private theorem norm_fderiv_sumSq_le' {k : ℕ} (y z : Fin k → ℝ) :
    ‖fderiv ℝ (fun x : Fin k → ℝ => ∑ i, (x i - y i) ^ 2) z‖ ≤ 2 * ∑ i, |z i - y i| := by
  have hproj : ∀ i : Fin k, ‖(ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
    intro i
    apply ContinuousLinearMap.opNorm_le_bound
    · norm_num
    · intro v
      simp only [ContinuousLinearMap.proj_apply, Real.norm_eq_abs, one_mul]
      exact norm_le_pi_norm v i
  rw [(hasFDerivAt_sumSq y z).fderiv]
  calc ‖∑ i, ((2 : ℝ) * (z i - y i)) •
        (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)‖
      ≤ ∑ i, ‖((2 : ℝ) * (z i - y i)) •
        (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, 2 * |z i - y i| := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_mul]
        norm_num
        calc 2 * |z i - y i| * ‖(ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)‖
            ≤ 2 * |z i - y i| * 1 := by
              exact mul_le_mul_of_nonneg_left (hproj i) (by positivity)
          _ = 2 * |z i - y i| := by ring
    _ = 2 * ∑ i, |z i - y i| := by rw [Finset.mul_sum]

/-- Gradient inequality `cst · Φ^θ ≤ ‖DΦ‖` on `G ∩ closedBall x0 ρ` ⇒ `Φ` reaches
`((1-θ) cst ρ / (4(k+1)))^(1/(1-θ))` somewhere in `G ∩ closedBall x0 ρ`.  (Namespace
`Work.WilE3.MPsi`.)

Proof: maximise `(max Φ 0)^(1-θ) - α ∑ (x_i - x0_i)^2`, `α = (1-θ) cst / (4 (k+1) ρ)`, over the
compact set `G ∩ closedBall x0 ρ`; the maximiser has `Φ > 0` (its objective value is positive at
`x₀`), so `G ∈ 𝓝` there and `hGo` makes it interior to `G`; if it were in the open ball,
`fderiv = 0` would give `‖D(Φ^(1-θ))‖ ≤ 2αρ = (1-θ)cst/(2(k+1)) < (1-θ) cst`, contradicting the
gradient inequality; so it is on the sphere, where the quadratic term is `≥ α ρ^2`. -/
theorem ascent {k : ℕ} (Φ : (Fin k → ℝ) → ℝ) (hΦ : ContDiff ℝ 1 Φ)
    (G : Set (Fin k → ℝ)) (hG : IsClosed G) (hGo : ∀ x ∈ G, 0 < Φ x → G ∈ 𝓝 x)
    {x0 : Fin k → ℝ} {ρ θ cst : ℝ} (hρ : 0 < ρ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hcst : 0 < cst)
    (hgr : ∀ x ∈ G, dist x x0 ≤ ρ → 0 < Φ x → cst * Φ x ^ θ ≤ ‖fderiv ℝ Φ x‖)
    (hx0 : x0 ∈ G) (hpos : 0 < Φ x0) :
    ∃ z ∈ G, dist z x0 ≤ ρ ∧ ((1 - θ) * cst * ρ / (4 * (k + 1))) ^ (1 / (1 - θ)) ≤ Φ z := by
  have h1θ : 0 < 1 - θ := by linarith
  set α : ℝ := (1 - θ) * cst / (4 * (k + 1) * ρ) with hαdef
  have hαpos : 0 < α := by rw [hαdef]; positivity
  set q : (Fin k → ℝ) → ℝ := fun x => ∑ i, (x i - x0 i) ^ 2 with hqdef
  set Ψ : (Fin k → ℝ) → ℝ := fun x => max (Φ x) 0 with hΨdef
  set f : (Fin k → ℝ) → ℝ := fun x => Ψ x ^ (1 - θ) - α * q x with hfdef
  -- continuity of the objective
  have hqcont : Continuous q := by
    rw [hqdef]
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).sub continuous_const).pow 2
  have hΨcont : Continuous Ψ := by
    rw [hΨdef]; exact hΦ.continuous.max continuous_const
  have hfcont : Continuous f := by
    rw [hfdef]
    exact (hΨcont.rpow_const fun _ => Or.inr h1θ.le).sub (continuous_const.mul hqcont)
  -- the maximiser
  have hKcpt : IsCompact (G ∩ Metric.closedBall x0 ρ) :=
    (isCompact_closedBall x0 ρ).inter_left hG
  have hx0K : x0 ∈ G ∩ Metric.closedBall x0 ρ := by
    refine ⟨hx0, ?_⟩
    rw [Metric.mem_closedBall, dist_self]
    exact hρ.le
  obtain ⟨z, hzK, hzmax⟩ := hKcpt.exists_isMaxOn ⟨x0, hx0K⟩ hfcont.continuousOn
  have hzG : z ∈ G := hzK.1
  have hzdist : dist z x0 ≤ ρ := by simpa [Metric.mem_closedBall] using hzK.2
  have hmax : f x0 ≤ f z := hzmax hx0K
  -- the objective is positive at `x₀`, hence at the maximiser
  have hqx0 : q x0 = 0 := by rw [hqdef]; simp
  have hΨx0 : Ψ x0 = Φ x0 := by rw [hΨdef]; exact max_eq_left hpos.le
  have hfx0 : f x0 = Φ x0 ^ (1 - θ) := by
    rw [hfdef]
    simp [hΨx0, hqx0]
  have hΦx0pow : 0 < Φ x0 ^ (1 - θ) := Real.rpow_pos_of_pos hpos _
  have hfzpos : 0 < f z := lt_of_lt_of_le (by rw [hfx0]; exact hΦx0pow) hmax
  have hqnn : 0 ≤ q z := by rw [hqdef]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hΨzpow : 0 < Ψ z ^ (1 - θ) := by
    have h1 := hfzpos
    rw [hfdef] at h1
    have h2 : 0 ≤ α * q z := mul_nonneg hαpos.le hqnn
    linarith
  have hΨznn : 0 ≤ Ψ z := by rw [hΨdef]; exact le_max_right _ _
  have hΨzpos : 0 < Ψ z := by
    rcases hΨznn.lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : Ψ z ^ (1 - θ) = 0 := by rw [← h]; exact Real.zero_rpow (ne_of_gt h1θ)
      linarith
  have hΦzpos : 0 < Φ z := by
    by_contra hcon
    push Not at hcon
    simp only [hΨdef] at hΨzpos
    rw [max_eq_right hcon] at hΨzpos
    exact absurd hΨzpos (lt_irrefl 0)
  have hΨzeq : Ψ z = Φ z := by rw [hΨdef]; exact max_eq_left hΦzpos.le
  -- `G` is a neighbourhood of the maximiser
  have hzint : z ∈ interior G :=
    mem_interior_iff_mem_nhds.mpr (hGo z hzG hΦzpos)
  rcases lt_or_eq_of_le hzdist with hlt | heq
  · -- CASE A: the maximiser is in the open ball: impossible
    exfalso
    have hKle : ∀ y ∈ interior G ∩ Metric.ball z (ρ - dist z x0), f y ≤ f z := by
      intro y hy
      have h1 : dist y z < ρ - dist z x0 := Metric.mem_ball.mp hy.2
      have h2 : dist y x0 ≤ ρ := by
        have h3 : dist y x0 < ρ := by
          calc dist y x0 ≤ dist y z + dist z x0 := dist_triangle _ _ _
            _ < ρ := by linarith
        exact h3.le
      refine hzmax ⟨interior_subset hy.1, ?_⟩
      simpa [Metric.mem_closedBall] using h2
    have hloc : IsLocalMax f z := by
      have hmem : interior G ∩ Metric.ball z (ρ - dist z x0) ∈ 𝓝 z :=
        (isOpen_interior.inter Metric.isOpen_ball).mem_nhds
          ⟨hzint, by rw [Metric.mem_ball, dist_self]; linarith⟩
      filter_upwards [hmem] with y hy
      exact hKle y hy
    have hfd : fderiv ℝ f z = 0 := hloc.fderiv_eq_zero
    -- the derivative of `Ψ ^ (1 - θ)` agrees with that of `Φ ^ (1 - θ)`
    have hΦd : HasFDerivAt Φ (fderiv ℝ Φ z) z :=
      hΦ.differentiable_one.differentiableAt.hasFDerivAt
    have hevΨ : Ψ =ᶠ[𝓝 z] Φ := by
      filter_upwards [(isOpen_lt continuous_const hΦ.continuous).mem_nhds hΦzpos] with x hx
      rw [hΨdef]; exact max_eq_left hx.le
    have hΨd : HasFDerivAt Ψ (fderiv ℝ Φ z) z := hevΨ.hasFDerivAt_iff.mpr hΦd
    have hLd : HasFDerivAt (fun x => Ψ x ^ (1 - θ))
        (((1 - θ) * Ψ z ^ ((1 - θ) - 1)) • fderiv ℝ Φ z) z :=
      hΨd.rpow_const (Or.inl (ne_of_gt hΨzpos))
    have hqd : HasFDerivAt q (fderiv ℝ q z) z := by
      rw [hqdef]
      exact (hasFDerivAt_sumSq x0 z).fderiv ▸ hasFDerivAt_sumSq x0 z
    have hAqd : HasFDerivAt (fun x => α * q x) (α • fderiv ℝ q z) z := hqd.const_mul α
    have hsub := hLd.sub hAqd
    have hfe : f = (fun x => Ψ x ^ (1 - θ)) - (fun x => α * q x) := by
      rw [hfdef]; funext x; simp [Pi.sub_apply]
    have hsub' : HasFDerivAt f
        (((1 - θ) * Ψ z ^ ((1 - θ) - 1)) • fderiv ℝ Φ z - α • fderiv ℝ q z) z :=
      hfe.symm ▸ hsub
    have hL_eq : ((1 - θ) * Ψ z ^ ((1 - θ) - 1)) • fderiv ℝ Φ z = α • fderiv ℝ q z := by
      have h := hsub'.fderiv
      rw [hfd] at h
      exact sub_eq_zero.mp h.symm
    -- the norm of the gradient of `Φ ^ (1 - θ)`
    have hexp : (1 - θ) - 1 = -θ := by ring
    have hnormL : ‖((1 - θ) * Ψ z ^ ((1 - θ) - 1)) • fderiv ℝ Φ z‖
        = (1 - θ) * Φ z ^ (-θ) * ‖fderiv ℝ Φ z‖ := by
      rw [hΨzeq, norm_smul, Real.norm_eq_abs, abs_mul, hexp,
        abs_of_pos (Real.rpow_pos_of_pos hΦzpos (-θ)), abs_of_nonneg h1θ.le]
    have hnormq : ‖fderiv ℝ q z‖ ≤ 2 * ∑ i, |z i - x0 i| := by
      rw [hqdef]; exact norm_fderiv_sumSq_le' x0 z
    have hsumle : ∑ i, |z i - x0 i| ≤ k * ρ := by
      have h1 : ∀ i : Fin k, |z i - x0 i| ≤ ρ := by
        intro i
        have h2 := norm_le_pi_norm (z - x0) i
        rw [Real.norm_eq_abs, ← dist_eq_norm] at h2
        simpa [Pi.sub_apply] using le_trans h2 hzdist
      calc ∑ i, |z i - x0 i| ≤ ∑ _i : Fin k, ρ := Finset.sum_le_sum fun i _ => h1 i
        _ = k * ρ := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    -- the contradiction
    have hkey : Φ z ^ (-θ) * ‖fderiv ℝ Φ z‖ ≤ k * cst / (2 * (k + 1)) := by
      have h1 : (1 - θ) * (Φ z ^ (-θ) * ‖fderiv ℝ Φ z‖)
          ≤ (1 - θ) * (k * cst / (2 * (k + 1))) := by
        have h2 : (1 - θ) * Φ z ^ (-θ) * ‖fderiv ℝ Φ z‖
            = (1 - θ) * (Φ z ^ (-θ) * ‖fderiv ℝ Φ z‖) := by ring
        rw [← h2, ← hnormL, hL_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hαpos]
        calc α * ‖fderiv ℝ q z‖ ≤ α * (2 * ∑ i, |z i - x0 i|) :=
              mul_le_mul_of_nonneg_left hnormq hαpos.le
          _ ≤ α * (2 * (k * ρ)) :=
              mul_le_mul_of_nonneg_left (by linarith) hαpos.le
          _ = (1 - θ) * (k * cst / (2 * (k + 1))) := by
              rw [hαdef]; field_simp; ring
      exact le_of_mul_le_mul_left h1 h1θ
    have hgrz : cst ≤ Φ z ^ (-θ) * ‖fderiv ℝ Φ z‖ := by
      have h := hgr z hzG hzdist hΦzpos
      have hposθ : 0 < Φ z ^ θ := Real.rpow_pos_of_pos hΦzpos θ
      have h2 : cst ≤ ‖fderiv ℝ Φ z‖ / Φ z ^ θ := (le_div_iff₀ hposθ).mpr h
      have h3 : ‖fderiv ℝ Φ z‖ / Φ z ^ θ = Φ z ^ (-θ) * ‖fderiv ℝ Φ z‖ := by
        rw [div_eq_mul_inv, ← Real.rpow_neg hΦzpos.le θ, mul_comm]
      rwa [h3] at h2
    have hlt2 : k * cst / (2 * (k + 1)) < cst := by
      rw [div_lt_iff₀ (by positivity)]
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith [hcst, hk0]
    linarith
  · -- CASE B: the maximiser is on the sphere
    have hqz : ρ ^ 2 ≤ q z := by
      have hnorm : ‖z - x0‖ = ρ := by rw [dist_eq_norm] at heq; exact heq
      have h1 : ‖z - x0‖ ^ 2 ≤ ∑ i, ((z - x0) i) ^ 2 := norm_sq_le_sum_sq (z - x0)
      have h2 : ∑ i, ((z - x0) i) ^ 2 = q z := by rw [hqdef]; simp [Pi.sub_apply]
      rw [hnorm, h2] at h1
      exact h1
    have hmain : α * ρ ^ 2 < Φ z ^ (1 - θ) := by
      have h1 : Φ x0 ^ (1 - θ) ≤ Ψ z ^ (1 - θ) - α * q z := by
        have hmax' := hmax
        rw [hfx0] at hmax'
        simp only [hfdef] at hmax'
        exact hmax'
      have h2 : α * ρ ^ 2 ≤ α * q z := mul_le_mul_of_nonneg_left hqz hαpos.le
      rw [hΨzeq] at h1
      linarith
    have hAeq : (1 - θ) * cst * ρ / (4 * (k + 1)) = α * ρ ^ 2 := by
      rw [hαdef]
      field_simp
    have hApos : 0 < α * ρ ^ 2 := mul_pos hαpos (pow_pos hρ 2)
    refine ⟨z, hzG, hzdist, ?_⟩
    rw [hAeq]
    exact rpow_ascent hApos hΦzpos.le hθ0 hθ1 hmain

end Work.WilE3.MPsi
