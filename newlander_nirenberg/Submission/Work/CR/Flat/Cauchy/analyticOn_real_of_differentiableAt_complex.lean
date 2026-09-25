import Mathlib
import Submission.Work.CR.Flat.Cauchy.slice_aux
import Submission.Work.CR.Flat.Cauchy.contDiffOn_of_differentiableAt_complex
import Submission.Work.CR.Flat.Cauchy.norm_continuousMultilinearMap_le_of_diagonal

/-!
# Holomorphic functions on open subsets of `ℂⁿ` are real analytic

The main result of this file is `analyticOn_real_of_differentiableAt_complex`: a function
`f : (Fin n → ℂ) → ℂ` which is complex differentiable at every point of an open set `Ω` is real
analytic on `Ω`.

The proof is the classical one.  Around `x ∈ Ω` we pick a ball `ball x ρ ⊆ Ω` on which `f` is
bounded by `M`.  On the slice `t ↦ f (x + t • v)` (a holomorphic function of one variable) the
one-variable Cauchy estimates give the bound

  `‖D^k f x (v, …, v)‖ ≤ k ! M / ρ^k`  for `‖v‖ ≤ 1`,

on the diagonal.  Polarizing (with the admissible constant `k^k/k!` for symmetric multilinear
maps, `norm_continuousMultilinearMap_le_of_diagonal`) and symmetrizing the `k`-th derivative (the
power series coefficients do not have to be symmetric, only their diagonal matters) gives

  `‖symmCM (D^k f x)‖ ≤ M k^k / ρ^k`,

so the Taylor series `∑_k (k!)⁻¹ symmCM (D^k f x)` has radius of convergence at least `ρ/3`
(using `n^n ≤ n! · 3^n`).  Finally the Taylor series of `f` at `x` is obtained from the
one-variable power series of its slices, which converge on the ball of radius `ρ`: for `‖y‖ < ρ`
the slice `t ↦ f (x + t • y)` is holomorphic on `|t| < ρ/‖y‖ > 1`, and its `k`-th Taylor
coefficient is `(k!)⁻¹ D^k f x (y, …, y)` by the chain rule for iterated derivatives
(`iteratedFDeriv_slice`).  Hence `f` is real analytic at `x`.
-/

namespace Work.CR.Flat.Cauchy

open scoped Topology NNReal ENNReal
open Metric Set

noncomputable section

/-- Numerical bound used to control the radius of convergence of the Taylor series of a
holomorphic function: `n ^ n ≤ n ! * 3 ^ n`.  The constant `3` is not optimal (any constant
`> exp 1` works), but it is enough for the application and follows easily from Stirling's formula
`Stirling.le_factorial_stirling` together with `Real.exp_one_lt_three`. -/
lemma pow_self_le_factorial_mul_three_pow (n : ℕ) :
    (n : ℝ) ^ n ≤ (n.factorial : ℝ) * 3 ^ n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    norm_num
  · have hSt := Stirling.le_factorial_stirling n
    have hexp : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have hpow : (0 : ℝ) < (Real.exp 1) ^ n := pow_pos hexp n
    have h2 : Real.sqrt (2 * Real.pi * n) * (n : ℝ) ^ n
        ≤ (n.factorial : ℝ) * (Real.exp 1) ^ n := by
      have h := mul_le_mul_of_nonneg_right hSt hpow.le
      rw [div_pow, mul_assoc, div_mul_cancel₀ _ (ne_of_gt hpow)] at h
      exact h
    have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * n) := by
      rw [Real.one_le_sqrt]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [Real.pi_gt_three, hn1]
    have h3 : (n : ℝ) ^ n ≤ Real.sqrt (2 * Real.pi * n) * (n : ℝ) ^ n := by
      have h := mul_le_mul_of_nonneg_right hsqrt (pow_nonneg (Nat.cast_nonneg n) n)
      rwa [one_mul] at h
    have h5 : (Real.exp 1) ^ n ≤ 3 ^ n :=
      pow_le_pow_left₀ (Real.exp_pos 1).le (le_of_lt Real.exp_one_lt_three) n
    exact le_trans (le_trans h3 h2) (mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg _))

/-- Symmetrization of a continuous multilinear map: the average of its reindexings by all
permutations of the arguments. -/
private noncomputable def symmCM {n k : ℕ} (T : (Fin n → ℂ) [×k]→L[ℝ] ℂ) :
    (Fin n → ℂ) [×k]→L[ℝ] ℂ :=
  ((k.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin k), T.domDomCongr σ

private lemma symmCM_apply {n k : ℕ} (T : (Fin n → ℂ) [×k]→L[ℝ] ℂ)
    (v : Fin k → (Fin n → ℂ)) :
    symmCM T v = ((k.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin k), T (fun i => v (σ i)) := by
  unfold symmCM
  rw [smul_apply, sum_apply]
  simp only [ContinuousMultilinearMap.domDomCongr_apply]

/-- The symmetrization is symmetric. -/
private lemma symmCM_comp_perm {n k : ℕ} (T : (Fin n → ℂ) [×k]→L[ℝ] ℂ)
    (τ : Equiv.Perm (Fin k)) (v : Fin k → (Fin n → ℂ)) :
    symmCM T (fun i => v (τ i)) = symmCM T v := by
  unfold symmCM
  rw [smul_apply, smul_apply, sum_apply, sum_apply]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ ?_
  intro σ
  have h : (Equiv.mulLeft τ) σ = τ * σ := rfl
  rw [h, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  simp only [Equiv.Perm.mul_apply]

/-- The symmetrization has the same diagonal as the original multilinear map. -/
private lemma symmCM_self {n k : ℕ} (T : (Fin n → ℂ) [×k]→L[ℝ] ℂ) (y : Fin n → ℂ) :
    symmCM T (fun _ => y) = T (fun _ => y) := by
  unfold symmCM
  rw [smul_apply, sum_apply]
  simp only [ContinuousMultilinearMap.domDomCongr_apply]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ k.factorial (T fun x => y)]
  rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_smul]

/-- For `g : ℂ → ℂ`, the real `k`-th iterated derivative at `0` evaluated on the constant
tuple `(1, …, 1)` is the complex `k`-th derivative at `0`. -/
private theorem iteratedFDeriv_real_apply_one_eq_iteratedDeriv {k : ℕ} {g : ℂ → ℂ}
    (hg : ContDiffAt ℂ (k : WithTop ℕ∞) g 0) :
    iteratedFDeriv ℝ k g 0 (fun _ => 1) = iteratedDeriv k g 0 := by
  rw [iteratedDeriv_eq_iteratedFDeriv (𝕜 := ℂ)]
  rw [← ContDiffAt.restrictScalars_iteratedFDeriv (𝕜 := ℝ) (𝕜' := ℂ) (f := g) (x := 0)
    (n := k) hg]
  rfl

/-- **Cauchy estimate for a holomorphic function of several variables, in symmetrized form.**

If `f` is complex differentiable on `Ω`, if the closed ball of radius `ρ` around `z` is contained
in `Ω`, and if `‖f‖ ≤ M` on `Ω`, then the symmetrization of the `k`-th derivative of `f` at `z`
is bounded by `M k^k/ρ^k`.

The `k^k` (rather than the optimal `k!`) is the loss in the passage from the diagonal bound to
the operator norm by polarization; it is harmless for the application, since dividing by `k!`
still leaves a geometric bound `~ (e/ρ)^k`. -/
private theorem norm_symmCM_iteratedFDeriv_le {n : ℕ} {Ω : Set (Fin n → ℂ)}
    {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} {ρ M : ℝ} (hρ : 0 < ρ)
    (hball : ∀ w : Fin n → ℂ, ‖w - z‖ ≤ ρ → w ∈ Ω)
    (hhol : ∀ w ∈ Ω, DifferentiableAt ℂ f w) (hM : ∀ w ∈ Ω, ‖f w‖ ≤ M) :
    ∀ k : ℕ, ‖symmCM (iteratedFDeriv ℝ k f z)‖ ≤ M * (k : ℝ) ^ k / ρ ^ k := by
  intro k
  have hz' : z ∈ Metric.ball z ρ := Metric.mem_ball_self hρ
  have hsub : Metric.ball z ρ ⊆ Ω := fun w hw =>
    hball w (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hw))
  have hhol' : ∀ w ∈ Metric.ball z ρ, DifferentiableAt ℂ f w := fun w hw => hhol w (hsub hw)
  have hcdR : ContDiffOn ℝ (k : WithTop ℕ∞) f (Metric.ball z ρ) :=
    contDiffOn_of_differentiableAt_complex Metric.isOpen_ball hhol' k
  -- the bound on the diagonal
  have hdiag : ∀ v : Fin n → ℂ, ‖v‖ ≤ 1 →
      ‖iteratedFDeriv ℝ k f z (fun _ => v)‖ ≤ (k.factorial : ℝ) * M / ρ ^ k := by
    intro v hv
    set g : ℂ → ℂ := fun t => f (z + t • v) with hgdef
    have hslice : iteratedFDeriv ℝ k g 0 (fun _ => 1)
        = iteratedFDeriv ℝ k f z (fun _ => v) := by
      rw [hgdef]
      exact iteratedFDeriv_slice (k := k) Metric.isOpen_ball hcdR hz' v
    rw [← hslice]
    have hgdiff : DifferentiableOn ℂ g (Metric.ball 0 ρ) := by
      rw [hgdef]
      refine DifferentiableOn.comp (f := fun t : ℂ => z + t • v) (g := f)
        (s := Metric.ball 0 ρ) (t := Metric.ball z ρ) ?_ ?_ ?_
      · exact fun w hw => (hhol w (hsub hw)).differentiableWithinAt
      · exact (by fun_prop : DifferentiableOn ℂ (fun t : ℂ => z + t • v) (Metric.ball 0 ρ))
      · intro t ht
        simp only [Metric.mem_ball, dist_eq_norm, sub_zero] at ht ⊢
        calc ‖(z + t • v) - z‖ = ‖t • v‖ := by rw [add_sub_cancel_left]
          _ = ‖t‖ * ‖v‖ := norm_smul _ _
          _ ≤ ‖t‖ * 1 := by gcongr
          _ < ρ := by simpa using ht
    have hgcont : ContinuousOn g (closure (Metric.ball 0 ρ)) := by
      rw [hgdef]
      refine ContinuousOn.comp (f := fun t : ℂ => z + t • v) (g := f)
        (s := closure (Metric.ball 0 ρ)) (t := Ω) ?_ ?_ ?_
      · exact DifferentiableOn.continuousOn (fun w hw => (hhol w hw).differentiableWithinAt)
      · exact (by fun_prop : ContinuousOn (fun t : ℂ => z + t • v) (closure (Metric.ball 0 ρ)))
      · intro t ht
        have ht' : ‖t‖ ≤ ρ := by
          have h1 : dist t 0 ≤ ρ :=
            Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall ht)
          rwa [dist_eq_norm, sub_zero] at h1
        exact hball _ (by calc ‖(z + t • v) - z‖ = ‖t • v‖ := by rw [add_sub_cancel_left]
            _ = ‖t‖ * ‖v‖ := norm_smul _ _
            _ ≤ ρ * 1 := by gcongr
            _ = ρ := by ring)
    have hdcc : DiffContOnCl ℂ g (Metric.ball 0 ρ) := ⟨hgdiff, hgcont⟩
    have hsphere : ∀ t ∈ Metric.sphere 0 ρ, ‖g t‖ ≤ M := by
      intro t ht
      have htρ : ‖t‖ = ρ := by
        have h := Metric.mem_sphere.mp ht
        rwa [dist_eq_norm, sub_zero] at h
      rw [hgdef]
      exact hM _ (hball _ (by
        calc ‖(z + t • v) - z‖ = ‖t • v‖ := by rw [add_sub_cancel_left]
          _ = ‖t‖ * ‖v‖ := norm_smul _ _
          _ = ρ * ‖v‖ := by rw [htρ]
          _ ≤ ρ * 1 := by gcongr
          _ = ρ := by ring))
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hρ hdcc hsphere
    have hgan : AnalyticAt ℂ g 0 :=
      hgdiff.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ))
    have hconv : iteratedFDeriv ℝ k g 0 (fun _ => 1) = iteratedDeriv k g 0 :=
      iteratedFDeriv_real_apply_one_eq_iteratedDeriv (k := k) hgan.contDiffAt
    rw [hconv]
    exact hcauchy
  have hdiagS : ∀ v : Fin n → ℂ, ‖v‖ ≤ 1 →
      ‖symmCM (iteratedFDeriv ℝ k f z) (fun _ => v)‖ ≤ (k.factorial : ℝ) * M / ρ ^ k := by
    intro v hv
    rw [symmCM_self]
    exact hdiag v hv
  calc ‖symmCM (iteratedFDeriv ℝ k f z)‖
      ≤ (k : ℝ) ^ k / (k.factorial : ℝ) * ((k.factorial : ℝ) * M / ρ ^ k) :=
        norm_continuousMultilinearMap_le_of_diagonal (symmCM (iteratedFDeriv ℝ k f z))
          (symmCM_comp_perm _) (D := (k.factorial : ℝ) * M / ρ ^ k) hdiagS
    _ = M * (k : ℝ) ^ k / ρ ^ k := by
        have hk : (k.factorial : ℝ) ≠ 0 := by positivity
        have hρk : ρ ^ k ≠ 0 := pow_ne_zero k (ne_of_gt hρ)
        field_simp

theorem analyticOn_real_of_differentiableAt_complex {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    {f : (Fin n → ℂ) → ℂ} (hhol : ∀ w ∈ Ω, DifferentiableAt ℂ f w) :
    AnalyticOn ℝ f Ω := by
  refine AnalyticOnNhd.analyticOn ?_
  intro x hx
  -- a radius `ρ` whose closed ball around `x` is contained in `Ω`
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx)
  set ρ : ℝ := ε / 2 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hsub : Metric.closedBall x ρ ⊆ Ω :=
    (Metric.closedBall_subset_ball (by rw [hρdef]; linarith)).trans hε
  -- smoothness of a holomorphic function
  have hC : ∀ k : ℕ, ContDiffOn ℝ (k : WithTop ℕ∞) f Ω := fun k =>
    contDiffOn_of_differentiableAt_complex hΩ hhol k
  -- a bound for `f` on the closed ball
  have hcont : ContinuousOn f (Metric.closedBall x ρ) := fun w hw =>
    (hhol w (hsub hw)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall x ρ).exists_bound_of_continuousOn hcont
  have hMnn : 0 ≤ M := le_trans (norm_nonneg (f x)) (hM x (Metric.mem_closedBall_self hρpos.le))
  -- Cauchy estimates for the symmetrized derivatives
  have hEst : ∀ k : ℕ, ‖symmCM (iteratedFDeriv ℝ k f x)‖ ≤ M * (k : ℝ) ^ k / ρ ^ k :=
    norm_symmCM_iteratedFDeriv_le hρpos
      (fun w hw => Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hw))
      (fun w hw => hhol w (hsub hw)) (fun w hw => hM w hw)
  -- the symmetrized Taylor series of `f` at `x`
  set p : FormalMultilinearSeries ℝ (Fin n → ℂ) ℂ :=
    fun k => ((k.factorial : ℝ)⁻¹) • symmCM (iteratedFDeriv ℝ k f x) with hpdef
  set r₀ : ℝ≥0 := ⟨ρ / 3, le_of_lt (by positivity)⟩ with hr₀def
  have hr₀coe : (r₀ : ℝ) = ρ / 3 := rfl
  have hr₀pos : (0 : ℝ≥0) < r₀ := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_zero, hr₀coe]
    positivity
  -- its radius of convergence is at least `ρ / 3`
  have hrad : (r₀ : ℝ≥0∞) ≤ p.radius := by
    refine FormalMultilinearSeries.le_radius_of_bound p M (fun k => ?_)
    have hnorm : ‖p k‖ = (k.factorial : ℝ)⁻¹ * ‖symmCM (iteratedFDeriv ℝ k f x)‖ := by
      show ‖((k.factorial : ℝ)⁻¹) • symmCM (iteratedFDeriv ℝ k f x)‖ = _
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc ‖p k‖ * (r₀ : ℝ) ^ k
        = (k.factorial : ℝ)⁻¹ * ‖symmCM (iteratedFDeriv ℝ k f x)‖ * (ρ / 3) ^ k := by
          rw [hnorm, hr₀coe]
      _ ≤ (k.factorial : ℝ)⁻¹ * (M * (k : ℝ) ^ k / ρ ^ k) * (ρ / 3) ^ k := by
          gcongr
          exact hEst k
      _ = M * ((k : ℝ) ^ k / ((k.factorial : ℝ) * 3 ^ k)) := by
          field_simp
          rw [mul_assoc, ← mul_pow, div_mul_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0)]
      _ ≤ M * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hMnn
          rw [div_le_one (by positivity)]
          exact pow_self_le_factorial_mul_three_pow k
      _ = M := mul_one M
  refine ⟨p, r₀, hrad, ENNReal.coe_lt_coe.mpr hr₀pos, fun {y} hy => ?_⟩
  -- the series converges to `f` on the ball
  have hy1 : (‖y‖₊ : ℝ≥0∞) < (r₀ : ℝ≥0∞) := by
    have h := Metric.mem_eball.mp hy
    rw [edist_nndist, nndist_eq_nnnorm, sub_zero] at h
    exact h
  have hy2 : ‖y‖₊ < r₀ := ENNReal.coe_lt_coe.mp hy1
  have hy3 : ‖y‖ < ρ / 3 := by
    have h : (‖y‖₊ : ℝ) < (r₀ : ℝ) := NNReal.coe_lt_coe.mp hy2
    rw [coe_nnnorm] at h
    rwa [hr₀coe] at h
  set g : ℂ → ℂ := fun t => f (x + t • y) with hgdef
  have hd : DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) ((2 : ℝ≥0) : ℝ)) := by
    intro t ht
    have ht2 : ‖t‖ ≤ 2 := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at ht
      simpa using ht
    have hmem : x + t • y ∈ Ω := by
      apply hsub
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hlt : ‖t‖ * ‖y‖ < ρ :=
        calc ‖t‖ * ‖y‖ ≤ 2 * ‖y‖ := by gcongr
          _ < 2 * (ρ / 3) := by gcongr
          _ < ρ := by linarith
      exact hlt.le
    have hdiff : DifferentiableAt ℂ (fun t : ℂ => x + t • y) t :=
      ((differentiableAt_id (x := t)).smul_const y).const_add x
    have hcomp := (hhol (x + t • y) hmem).comp t hdiff
    simpa only [Function.comp_def, hgdef] using hcomp.differentiableWithinAt
  have hcauchy := DifferentiableOn.hasFPowerSeriesOnBall hd (by norm_num : (0 : ℝ≥0) < 2)
  have hmem1 : (1 : ℂ) ∈ Metric.eball (0 : ℂ) ((2 : ℝ≥0) : ℝ≥0∞) := by
    rw [Metric.mem_eball, edist_nndist]
    simp
  have hsum1 : HasSum (fun k => cauchyPowerSeries g 0 ((2 : ℝ≥0) : ℝ) k (fun _ => (1 : ℂ)))
      (f (x + y)) := by
    have h := hcauchy.hasSum hmem1
    simpa only [Function.comp_def, hgdef, one_smul, zero_add] using h
  set q : FormalMultilinearSeries ℂ ℂ ℂ := cauchyPowerSeries g 0 ((2 : ℝ≥0) : ℝ) with hqdef
  have hrR : HasFPowerSeriesOnBall (𝕜 := ℝ) g (FormalMultilinearSeries.restrictScalars ℝ q)
      0 ((2 : ℝ≥0) : ℝ≥0∞) :=
    HasFPowerSeriesOnBall.restrictScalars hcauchy
  have hcoef : ∀ k, q k (fun _ => (1 : ℂ)) = p k (fun _ => y) := by
    intro k
    have hsm := hrR.factorial_smul (1 : ℂ) k
    have hL : (FormalMultilinearSeries.restrictScalars ℝ q k) (fun _ => (1 : ℂ))
        = q k (fun _ => (1 : ℂ)) := by
      rw [FormalMultilinearSeries.restrictScalars,
        ContinuousMultilinearMap.coe_restrictScalars]
    have hslice : iteratedFDeriv ℝ k g 0 (fun _ => (1 : ℂ))
        = iteratedFDeriv ℝ k f x (fun _ => y) := by
      rw [hgdef]
      exact iteratedFDeriv_slice (k := k) hΩ (hC k) hx y
    have hq : (k.factorial : ℝ) • (q k (fun _ => (1 : ℂ)))
        = symmCM (iteratedFDeriv ℝ k f x) (fun _ => y) := by
      rw [hL] at hsm
      rw [hslice, ← symmCM_self] at hsm
      rwa [← Nat.cast_smul_eq_nsmul ℝ k.factorial (q k (fun _ => (1 : ℂ)))] at hsm
    have hpv : (k.factorial : ℝ) • (p k (fun _ => y))
        = symmCM (iteratedFDeriv ℝ k f x) (fun _ => y) := by
      have h1 : p k (fun _ => y)
          = (k.factorial : ℝ)⁻¹ • (symmCM (iteratedFDeriv ℝ k f x) (fun _ => y)) := by
        show (((k.factorial : ℝ)⁻¹) • symmCM (iteratedFDeriv ℝ k f x)) (fun _ => y) = _
        rw [smul_apply]
      have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      rw [h1, smul_smul, mul_inv_cancel₀ hk, one_smul]
    have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hEq : (k.factorial : ℝ) • (q k (fun _ => (1 : ℂ)))
        = (k.factorial : ℝ) • (p k (fun _ => y)) := by rw [hq, hpv]
    have h := congrArg (fun z => (k.factorial : ℝ)⁻¹ • z) hEq
    simp only [smul_smul, inv_mul_cancel₀ hk, one_smul] at h
    exact h
  exact hsum1.congr_fun (fun k => (hcoef k).symm)

end

end Work.CR.Flat.Cauchy
