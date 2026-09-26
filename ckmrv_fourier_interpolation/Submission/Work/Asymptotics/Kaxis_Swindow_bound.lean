import Mathlib
import Submission.Work.Asymptotics.Kaxis_principal_part_bound
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.Kaxis_local_coincidence
import Submission.Work.Asymptotics.MiddleRange.exists_diffQuotient_lower_general
import Submission.Work.Asymptotics.lipschitz_jInvariantFun_local
import Submission.Work.Asymptotics.KClear_S_vanishing
import Submission.Work.Asymptotics.MiddleRange.exists_j_sub_lower_lambda_near_I
import Submission.Work.Asymptotics.MiddleRange.exists_lambdaFun_lipschitz
import Submission.Work.Asymptotics.MiddleRange.exists_bound_Kfun_of_coincidence
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup Matrix Metric Filter Complex
open scoped Topology

noncomputable section

/-! ## Auxiliary bounds -/

/-- Uniform bound for `AfunFun` on a product of Euclidean closed balls, one of which lies in a
neighbourhood of the bad line. -/
lemma exists_bound_AfunFun_euclid (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (c₁ c₂ : ℂ)
    {r : ℝ} (hr₁ : r < c₁.im) (hr₂ : r < c₂.im) :
    ∃ B : ℝ, 0 < B ∧ ∀ (τ z : UpperHalfPlane), ‖(τ : ℂ) - c₁‖ ≤ r → ‖(z : ℂ) - c₂‖ ≤ r →
      ‖AfunFun ℓ d τ z‖ ≤ B := by
  have him₁ : ∀ x : ℂ, x ∈ Metric.closedBall c₁ r → 0 < x.im := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    have h3 : |(x - c₁).im| ≤ ‖x - c₁‖ := Complex.abs_im_le_norm _
    have h4 : (x - c₁).im = x.im - c₁.im := by simp
    have h5 := (abs_le.mp (le_trans h3 hx)).1
    rw [h4] at h5
    linarith
  have him₂ : ∀ x : ℂ, x ∈ Metric.closedBall c₂ r → 0 < x.im := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    have h3 : |(x - c₂).im| ≤ ‖x - c₂‖ := Complex.abs_im_le_norm _
    have h4 : (x - c₂).im = x.im - c₂.im := by simp
    have h5 := (abs_le.mp (le_trans h3 hx)).1
    rw [h4] at h5
    linarith
  have hof₁ : ContinuousOn (fun u : ℂ => UpperHalfPlane.ofComplex u)
      (Metric.closedBall c₁ r) :=
    continuousOn_ofComplex_im_pos.mono (fun u hu => him₁ u hu)
  have hof₂ : ContinuousOn (fun u : ℂ => UpperHalfPlane.ofComplex u)
      (Metric.closedBall c₂ r) :=
    continuousOn_ofComplex_im_pos.mono (fun u hu => him₂ u hu)
  have hpair : ContinuousOn (fun p : ℂ × ℂ =>
      (UpperHalfPlane.ofComplex p.1, UpperHalfPlane.ofComplex p.2))
      (Metric.closedBall c₁ r ×ˢ Metric.closedBall c₂ r) :=
    (hof₁.comp continuous_fst.continuousOn (fun p hp => hp.1)).prodMk
      (hof₂.comp continuous_snd.continuousOn (fun p hp => hp.2))
  obtain ⟨C₀, hC₀⟩ := ((isCompact_closedBall c₁ r).prod (isCompact_closedBall c₂ r)
    ).exists_bound_of_continuousOn
    ((continuous_AfunFun ℓ d).continuousOn.comp hpair (fun p _ => Set.mem_univ _))
  refine ⟨max C₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun τ z hτ hz => ?_⟩
  have hb := hC₀ ((τ : ℂ), (z : ℂ))
    ⟨by rw [Metric.mem_closedBall, dist_eq_norm]; exact hτ,
     by rw [Metric.mem_closedBall, dist_eq_norm]; exact hz⟩
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] at hb
  exact le_trans hb (le_max_left _ _)

/-- **One-zero bound.**  A function holomorphic on the disc `ball c ρ` with a zero at a point of
the half-radius disc is bounded there by `(2M/ρ)·‖z - z₁‖`, where `M` bounds `‖f‖` on the disc. -/
theorem norm_le_mul_dist_of_one_zero {f : ℂ → ℂ} {c : ℂ} {ρ M : ℝ} (hρ : 0 < ρ)
    (hf : DiffContOnCl ℂ f (Metric.ball c ρ)) (hbd : ∀ z ∈ Metric.ball c ρ, ‖f z‖ ≤ M)
    {z₁ : ℂ} (h₁ : z₁ ∈ Metric.ball c (ρ / 2)) (hf₁ : f z₁ = 0) :
    ∀ z ∈ Metric.ball c (ρ / 2), ‖f z‖ ≤ (2 * M / ρ) * ‖z - z₁‖ := by
  intro z hz
  have hz₁ρ : z₁ ∈ Metric.ball c ρ := Metric.ball_subset_ball (by linarith) h₁
  have hgd : DifferentiableOn ℂ (dslope f z₁) (Metric.ball c ρ) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds hz₁ρ)).mpr hf.differentiableOn
  have hfac : ∀ w : ℂ, (w - z₁) * dslope f z₁ w = f w := by
    intro w; simpa using sub_smul_dslope_of_zero hf₁ w
  have hbound : ‖dslope f z₁ z‖ ≤ 2 * M / ρ := by
    have key : ∀ᶠ r in 𝓝[<] ρ, ‖dslope f z₁ z‖ ≤ M / (r - ρ / 2) := by
      filter_upwards [Ioo_mem_nhdsLT (show ρ / 2 < ρ by linarith)] with r hr
      obtain ⟨hrl, hrr⟩ := hr
      have hzr : z ∈ Metric.ball c r := Metric.mem_ball.mpr (by
        have := Metric.mem_ball.mp hz; linarith)
      have hgd' : DiffContOnCl ℂ (dslope f z₁) (Metric.ball c r) :=
        hgd.diffContOnCl_ball (Metric.closedBall_subset_ball hrr)
      have hpos : 0 < r - ρ / 2 := by linarith
      refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hgd' ?_
        (subset_closure hzr)
      intro w hw
      have hws : w ∈ Metric.sphere c r := frontier_ball_subset_sphere hw
      have hwr : dist w c = r := Metric.mem_sphere.mp hws
      have hwρ : w ∈ Metric.ball c ρ := Metric.mem_ball.mpr (by rw [hwr]; exact hrr)
      have hfw := hbd w hwρ
      have hfwn : ‖f w‖ = ‖w - z₁‖ * ‖dslope f z₁ w‖ := by rw [← hfac w, norm_mul]
      have hd₁w : r - ρ / 2 ≤ ‖w - z₁‖ := by
        have ht : r ≤ ‖w - z₁‖ + dist z₁ c := by
          have := dist_triangle w z₁ c
          rw [hwr] at this
          simpa [dist_eq_norm] using this
        have hz₁c : dist z₁ c < ρ / 2 := Metric.mem_ball.mp h₁
        linarith
      rw [le_div_iff₀ hpos]
      calc ‖dslope f z₁ w‖ * (r - ρ / 2)
          ≤ ‖dslope f z₁ w‖ * ‖w - z₁‖ := mul_le_mul_of_nonneg_left hd₁w (norm_nonneg _)
        _ = ‖f w‖ := by rw [hfwn]; ring
        _ ≤ M := hfw
    have hne2 : ρ - ρ / 2 ≠ 0 := by linarith
    have hc : ContinuousAt (fun r : ℝ => M / (r - ρ / 2)) ρ :=
      ContinuousAt.div continuousAt_const (continuousAt_id.sub continuousAt_const) hne2
    have hval : M / (ρ - ρ / 2) = 2 * M / ρ := by
      rw [show ρ - ρ / 2 = ρ / 2 by ring]; field_simp
    have htend : Tendsto (fun r : ℝ => M / (r - ρ / 2)) (𝓝[<] ρ) (𝓝 (2 * M / ρ)) := by
      rw [← hval]; exact hc.tendsto.mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto htend key
  rw [← hfac z, norm_mul]
  calc ‖z - z₁‖ * ‖dslope f z₁ z‖ ≤ ‖z - z₁‖ * (2 * M / ρ) :=
        mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = (2 * M / ρ) * ‖z - z₁‖ := by ring



/-! ## The one-zero bound for `AfunFun` at the `S`-branch -/

/-- The coefficient of a point of `ℍ` is non-zero. -/
lemma coe_ne_zero' (z : UpperHalfPlane) : (z : ℂ) ≠ 0 :=
  fun h => z.im_ne_zero (by rw [← UpperHalfPlane.coe_im z, h]; simp)

/-- **One-zero bound for the cleared CKMRV value function at the `S`-branch.**  For `n = ±1`,
`τ` near the bad-line point `n + i s₀` and `z` near the contour point `i/s₀ = S (i s₀)`, the
value function is dominated by the distance of `z` to the `S`-conjugate branch point
`S (τ - n)` of the coincidence locus. -/
theorem AfunFun_Sbranch_one_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {s₀ : ℝ} (hs₀ : 0 < s₀) :
    ∃ δ ρ C : ℝ, 0 < δ ∧ 0 < ρ ∧ 0 < C ∧
      ∀ (τ z : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) →
        |τ.re - (n : ℝ)| < δ → |τ.im - s₀| < δ →
        ‖(z : ℂ) - Complex.I / (s₀ : ℂ)‖ < ρ →
        ‖AfunFun ℓ d τ z‖ ≤ C *
          ‖(z : ℂ) - (((ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) : UpperHalfPlane)) : ℂ)‖ := by
  set r : ℝ := min (min 1 (s₀ / 2)) (1 / (4 * s₀)) with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]; exact lt_min (lt_min one_pos (by linarith)) (by positivity)
  have hrs₀ : r < s₀ := by
    rw [hrdef]
    have h1 : min (min 1 (s₀ / 2)) (1 / (4 * s₀)) ≤ s₀ / 2 :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hrinv : r < 1 / s₀ := by
    rw [hrdef]
    have h1 : min (min 1 (s₀ / 2)) (1 / (4 * s₀)) ≤ 1 / (4 * s₀) := min_le_right _ _
    have h2 : 1 / (4 * s₀) < 1 / s₀ := by
      rw [div_lt_div_iff₀ (by positivity) hs₀]; linarith
    linarith
  set ρ : ℝ := min (r / 2) (1 / (8 * s₀)) / 2 with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]; exact div_pos (lt_min (by linarith) (by positivity)) (by norm_num)
  have h2ρr : 2 * ρ ≤ r := by
    rw [hρdef]
    have h1 : min (r / 2) (1 / (8 * s₀)) ≤ r / 2 := min_le_left _ _
    linarith
  have h2ρinv : 2 * ρ < 1 / s₀ := by
    rw [hρdef]
    have h1 : min (r / 2) (1 / (8 * s₀)) ≤ 1 / (8 * s₀) := min_le_right _ _
    have h2 : 1 / (8 * s₀) < 1 / s₀ := by
      rw [div_lt_div_iff₀ (by positivity) hs₀]; linarith
    linarith
  set δ : ℝ := min (r / 16) (ρ * s₀ ^ 2 / 16) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (by linarith) (by positivity)
  have h2δr : 2 * δ ≤ r := by
    rw [hδdef]
    have h1 : min (r / 16) (ρ * s₀ ^ 2 / 16) ≤ r / 16 := min_le_left _ _
    linarith
  have hδ16 : δ ≤ r / 16 := by
    rw [hδdef]; exact min_le_left _ _
  have hδsmall : 2 * δ ≤ s₀ / 2 := by linarith [hδ16, hrs₀]
  have h4δρ : 4 * δ / s₀ ^ 2 ≤ ρ := by
    rw [hδdef]
    have h1 : min (r / 16) (ρ * s₀ ^ 2 / 16) ≤ ρ * s₀ ^ 2 / 16 := min_le_right _ _
    have hs2 : 0 < s₀ ^ 2 := by positivity
    rw [div_le_iff₀ hs2]
    nlinarith [h1]
  have h4δρ' : 4 * δ ≤ ρ * s₀ ^ 2 := by
    have hs2 : 0 < s₀ ^ 2 := by positivity
    rw [div_le_iff₀ hs2] at h4δρ
    exact h4δρ
  -- uniform bounds on the two bad-line neighbourhoods
  have him1 : ((1 : ℂ) + (s₀ : ℂ) * Complex.I).im = s₀ := by simp
  have him2 : ((-1 : ℂ) + (s₀ : ℂ) * Complex.I).im = s₀ := by simp
  have himc : (Complex.I / (s₀ : ℂ)).im = s₀⁻¹ := by
    rw [div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm]; simp
  have hcwinv : r < s₀⁻¹ := by rw [← one_div]; exact hrinv
  obtain ⟨B₁, hB₁pos, hb₁⟩ := exists_bound_AfunFun_euclid ℓ d ((1 : ℂ) + (s₀ : ℂ) * Complex.I)
    (Complex.I / (s₀ : ℂ)) (by rw [him1]; exact hrs₀) (by rw [himc]; exact hcwinv)
  obtain ⟨B₂, hB₂pos, hb₂⟩ := exists_bound_AfunFun_euclid ℓ d ((-1 : ℂ) + (s₀ : ℂ) * Complex.I)
    (Complex.I / (s₀ : ℂ)) (by rw [him2]; exact hrs₀) (by rw [himc]; exact hcwinv)
  refine ⟨δ, ρ, max B₁ B₂ / ρ, hδpos, hρpos, by positivity, ?_⟩
  intro τ z n hn hτre hτim hz
  -- the `τ`-neighbourhood of the bad line
  have hτbound : ‖(τ : ℂ) - ((n : ℂ) + (s₀ : ℂ) * Complex.I)‖ ≤ r := by
    have he : (τ : ℂ) - ((n : ℂ) + (s₀ : ℂ) * Complex.I)
        = ((τ.re - (n : ℝ) : ℝ) : ℂ) + ((τ.im - s₀ : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;>
        simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
          Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] <;> ring
    rw [he]
    have h := norm_le_re_im (τ.re - (n : ℝ)) (τ.im - s₀)
    have h1 := (abs_lt.mp hτre).2
    have h2 := (abs_lt.mp hτim).2
    linarith
  -- the uniform bound on the slice disc
  have hkey : ∀ u : ℂ, u ∈ Metric.ball (Complex.I / (s₀ : ℂ)) (2 * ρ) →
      ‖AfunFun ℓ d τ (UpperHalfPlane.ofComplex u)‖ ≤ max B₁ B₂ := by
    intro u hu
    have huρ : ‖u - Complex.I / (s₀ : ℂ)‖ < 2 * ρ := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hu
    have hur : ‖u - Complex.I / (s₀ : ℂ)‖ ≤ r := by linarith
    have huclo : u ∈ Metric.closedBall (Complex.I / (s₀ : ℂ)) (2 * ρ) :=
      Metric.ball_subset_closedBall hu
    have hsubu : 0 < u.im := by
      rw [Metric.mem_closedBall, dist_eq_norm] at huclo
      have h1 : |(u - Complex.I / (s₀ : ℂ)).im| ≤ ‖u - Complex.I / (s₀ : ℂ)‖ :=
        Complex.abs_im_le_norm _
      have h2 : (u - Complex.I / (s₀ : ℂ)).im = u.im - s₀⁻¹ := by
        simp [himc]
      have h3 := (abs_le.mp (le_trans h1 huclo)).1
      rw [h2] at h3
      have h4 : s₀⁻¹ = 1 / s₀ := (one_div s₀).symm
      rw [h4] at h3
      linarith [h2ρinv]
    have huc : ‖(((UpperHalfPlane.ofComplex u : ℍ)) : ℂ) - Complex.I / (s₀ : ℂ)‖ ≤ r := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hsubu]
      exact hur
    rcases hn with h1 | h1
    · subst h1
      have := hb₁ τ (UpperHalfPlane.ofComplex u) (by simpa using hτbound) huc
      exact le_trans this (le_max_left _ _)
    · subst h1
      have := hb₂ τ (UpperHalfPlane.ofComplex u) (by simpa using hτbound) huc
      exact le_trans this (le_max_right _ _)
  -- the slice vanishes at the `S`-conjugate branch point
  have hzero : AfunFun ℓ d τ (ModularGroup.S • ((-(n : ℝ)) +ᵥ τ)) = 0 := by
    have h := AfunFun_S_vadd_zero ℓ d hd n hn ((-(n : ℝ)) +ᵥ τ)
    rwa [vadd_neg_vadd_cancel n τ] at h
  -- the branch point is close to `i/s₀`
  have hnum : ‖(((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ) - ((Work.Kernels.imagAxis s₀ hs₀ : UpperHalfPlane) : ℂ)‖
      < 2 * δ := by
    have he : (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)
          - ((Work.Kernels.imagAxis s₀ hs₀ : UpperHalfPlane) : ℂ)
        = ((τ.re - (n : ℝ) : ℝ) : ℂ) + ((τ.im - s₀ : ℝ) : ℂ) * Complex.I := by
      rw [coe_neg_vadd]
      simp only [Work.Kernels.imagAxis]
      apply Complex.ext <;>
        simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
          Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] <;> ring
    rw [he]
    have h := norm_le_re_im (τ.re - (n : ℝ)) (τ.im - s₀)
    have h1 := (abs_lt.mp hτre).2
    have h2 := (abs_lt.mp hτim).2
    linarith
  have hσnorm : s₀ / 2 ≤ ‖(((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖ := by
    have h1 : ‖((Work.Kernels.imagAxis s₀ hs₀ : UpperHalfPlane) : ℂ)‖ = s₀ :=
      KL.norm_imagAxis s₀ hs₀
    have h3 : ‖((Work.Kernels.imagAxis s₀ hs₀ : UpperHalfPlane) : ℂ)‖
        ≤ ‖(((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖
          + ‖((Work.Kernels.imagAxis s₀ hs₀ : UpperHalfPlane) : ℂ)
              - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖ := by
      have h := norm_add_le (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)
        (((Work.Kernels.imagAxis s₀ hs₀ : UpperHalfPlane) : ℂ)
          - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ))
      rwa [add_sub_cancel] at h
    rw [h1] at h3
    have h4 : ‖((Work.Kernels.imagAxis s₀ hs₀ : UpperHalfPlane) : ℂ)
        - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖ < 2 * δ := by
      rw [norm_sub_rev]; exact hnum
    linarith [hδsmall]
  have hSc : ((ModularGroup.S • Work.Kernels.imagAxis s₀ hs₀ : UpperHalfPlane) : ℂ)
      = Complex.I / (s₀ : ℂ) := by
    rw [KL.coe_S_smul']
    simp only [Work.Kernels.imagAxis]
    rw [_root_.mul_inv_rev, Complex.inv_I, ← Complex.ofReal_inv]
    rw [div_eq_mul_inv, ← Complex.ofReal_inv]
    ring
  have hz₁ : ‖(((ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) : ℍ)) : ℂ) - Complex.I / (s₀ : ℂ)‖ < ρ := by
    rw [← hSc, KL.norm_S_sub_S, KL.norm_imagAxis s₀ hs₀]
    rw [div_lt_iff₀ (mul_pos (by linarith [hσnorm, hs₀]) hs₀)]
    nlinarith [hnum, hσnorm, hs₀, h4δρ']
  -- the one-zero bound for the holomorphic slice
  have hsub : Metric.closedBall (Complex.I / (s₀ : ℂ)) (2 * ρ) ⊆ {u : ℂ | 0 < u.im} := by
    intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm] at hu
    have h1 : |(u - Complex.I / (s₀ : ℂ)).im| ≤ ‖u - Complex.I / (s₀ : ℂ)‖ :=
      Complex.abs_im_le_norm _
    have h4 := (abs_le.mp (le_trans h1 hu)).1
    have h2 : (u - Complex.I / (s₀ : ℂ)).im = u.im - s₀⁻¹ := by simp [himc]
    rw [h2] at h4
    have h6 : s₀⁻¹ = 1 / s₀ := inv_eq_one_div s₀
    rw [h6] at h4
    show (0 : ℝ) < u.im
    linarith [h2ρinv]
  have hslice : DifferentiableOn ℂ (fun u : ℂ => AfunFun ℓ d τ (UpperHalfPlane.ofComplex u))
      {u : ℂ | 0 < u.im} :=
    (UpperHalfPlane.mdifferentiable_iff (f := fun w : ℍ => AfunFun ℓ d τ w)).mp
      (mdifferentiable_AfunFun_snd ℓ d hd τ)
  have hf : DiffContOnCl ℂ (fun u : ℂ => AfunFun ℓ d τ (UpperHalfPlane.ofComplex u))
      (Metric.ball (Complex.I / (s₀ : ℂ)) (2 * ρ)) := hslice.diffContOnCl_ball hsub
  have hzero' : (fun u : ℂ => AfunFun ℓ d τ (UpperHalfPlane.ofComplex u))
      (((ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) : UpperHalfPlane)) : ℂ) = 0 := by
    simp only [UpperHalfPlane.ofComplex_apply]
    exact hzero
  have hz₁ball : (((ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) : UpperHalfPlane)) : ℂ)
      ∈ Metric.ball (Complex.I / (s₀ : ℂ)) (2 * ρ / 2) := by
    rw [Metric.mem_ball, dist_eq_norm, show 2 * ρ / 2 = ρ by ring]
    exact hz₁
  have hone := norm_le_mul_dist_of_one_zero
    (f := fun u : ℂ => AfunFun ℓ d τ (UpperHalfPlane.ofComplex u))
    (c := Complex.I / (s₀ : ℂ)) (ρ := 2 * ρ) (M := max B₁ B₂) (by linarith) hf hkey hz₁ball hzero'
  have hzball : (z : ℂ) ∈ Metric.ball (Complex.I / (s₀ : ℂ)) (2 * ρ / 2) := by
    rw [Metric.mem_ball, dist_eq_norm, show 2 * ρ / 2 = ρ by ring]
    exact hz
  have hfin := hone (z : ℂ) hzball
  have hcoef : 2 * max B₁ B₂ / (2 * ρ) = max B₁ B₂ / ρ := by
    have hρne : (2 : ℝ) * ρ ≠ 0 := by positivity
    field_simp
  rw [hcoef] at hfin
  simpa only [UpperHalfPlane.ofComplex_apply] using hfin

/-- **Lower bound for the `j`-difference at the `S`-branch.**  For `s₀ > 0`, `s₀ ≠ 1`, `n = ±1`,
`τ` near the bad-line point `n + i s₀` and `z` near the contour point `i/s₀ = S (i s₀)`, the
difference `j z - j τ` dominates the distance of `z` to the `S`-conjugate branch point
`S (τ - n) = -1/(τ - n)`. -/
theorem jDiff_lower_Sbranch {s₀ : ℝ} (hs₀ : 0 < s₀) (hs1 : s₀ ≠ 1) :
    ∃ δ ρ c : ℝ, 0 < δ ∧ 0 < ρ ∧ 0 < c ∧
      ∀ (τ z : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) →
        |τ.re - (n : ℝ)| < δ → |τ.im - s₀| < δ →
        ‖(z : ℂ) - Complex.I / (s₀ : ℂ)‖ < ρ →
        c * ‖(z : ℂ) - (((ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) : UpperHalfPlane)) : ℂ)‖
          ≤ ‖Work.Kernels.jInvariantFun z - Work.Kernels.jInvariantFun τ‖ := by
  obtain ⟨ρ₀, hρ₀pos, c₀, hc₀pos, hb⟩ :=
    MiddleRange.exists_diffQuotient_lower_general hs₀ hs1
  set D : ℝ := max (1 / s₀ + 1) (2 / s₀) with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  set ρ : ℝ := min (min (ρ₀ / (4 * s₀ ^ 2)) (1 / (8 * s₀))) 1 / 4 with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact div_pos (lt_min (lt_min (div_pos hρ₀pos (by positivity)) (by positivity)) one_pos)
      (by norm_num)
  have hρsmall : ρ ≤ ρ₀ / (16 * s₀ ^ 2) := by
    rw [hρdef]
    have h1 : min (min (ρ₀ / (4 * s₀ ^ 2)) (1 / (8 * s₀))) 1 ≤ ρ₀ / (4 * s₀ ^ 2) :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have h2 : ρ₀ / (4 * s₀ ^ 2) / 4 = ρ₀ / (16 * s₀ ^ 2) := by ring
    rw [← h2]
    exact div_le_div_of_nonneg_right h1 (by norm_num)
  have hρρ₀ : 2 * ρ * s₀ ^ 2 ≤ ρ₀ := by
    have hs2 : 0 < s₀ ^ 2 := by positivity
    have hb' : 0 < 16 * s₀ ^ 2 := by positivity
    have h4 : ρ * (16 * s₀ ^ 2) ≤ ρ₀ := by
      calc ρ * (16 * s₀ ^ 2) ≤ (ρ₀ / (16 * s₀ ^ 2)) * (16 * s₀ ^ 2) :=
            mul_le_mul_of_nonneg_right hρsmall hb'.le
        _ = ρ₀ := by field_simp
    nlinarith [h4, hρ₀pos, hs2]
  have hρinv : 1 / (2 * s₀) ≤ 1 / s₀ - ρ := by
    rw [hρdef]
    have h1 : min (min (ρ₀ / (4 * s₀ ^ 2)) (1 / (8 * s₀))) 1 ≤ 1 / (8 * s₀) :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    have h2 : min (min (ρ₀ / (4 * s₀ ^ 2)) (1 / (8 * s₀))) 1 / 4 ≤ 1 / (32 * s₀) := by
      have h4 : 1 / (8 * s₀) / 4 = 1 / (32 * s₀) := by ring
      rw [← h4]
      exact div_le_div_of_nonneg_right h1 (by norm_num)
    have h5 : 1 / (2 * s₀) = 1 / s₀ - 1 / (2 * s₀) := by ring
    have h6 : (1 : ℝ) / (32 * s₀) ≤ 1 / (2 * s₀) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    linarith
  have hρ1 : ρ ≤ 1 := by
    rw [hρdef]
    have h1 : min (min (ρ₀ / (4 * s₀ ^ 2)) (1 / (8 * s₀))) 1 ≤ 1 := min_le_right _ _
    linarith
  set δ : ℝ := min (ρ₀ / 8) (s₀ / 8) / 4 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact div_pos (lt_min (by positivity) (by positivity)) (by norm_num)
  have hδsmall : 2 * δ ≤ min ρ₀ (s₀ / 2) := by
    rw [hδdef]
    have h1 : min (ρ₀ / 8) (s₀ / 8) / 4 ≤ ρ₀ / 8 := by
      have := min_le_left (ρ₀ / 8) (s₀ / 8); linarith
    have h2 : min (ρ₀ / 8) (s₀ / 8) / 4 ≤ s₀ / 8 := by
      have := min_le_right (ρ₀ / 8) (s₀ / 8); linarith
    rw [le_min_iff]
    constructor <;> linarith
  have hδr : 2 * δ ≤ ρ₀ := le_trans hδsmall (min_le_left _ _)
  have hδs : 2 * δ ≤ s₀ / 2 := le_trans hδsmall (min_le_right _ _)
  refine ⟨δ, ρ, c₀ / D ^ 2, hδpos, hρpos, by positivity, ?_⟩
  intro τ z n hn hτre hτim hz
  set σ : ℍ := (-(n : ℝ)) +ᵥ τ with hσdef
  -- the `S`-window centre as a point of `ℍ`
  have himc : 0 < (Complex.I / (s₀ : ℂ)).im := by
    rw [div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    positivity
  set c₂ : ℍ := ⟨Complex.I / (s₀ : ℂ), himc⟩ with hc₂def
  have hc₂coe : (c₂ : ℂ) = Complex.I / (s₀ : ℂ) := rfl
  have hc₂norm : ‖(c₂ : ℂ)‖ = 1 / s₀ := by
    rw [hc₂coe]
    have h : Complex.I / (s₀ : ℂ) = ((s₀⁻¹ : ℝ) : ℂ) * Complex.I := by
      rw [div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm]
    rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < s₀⁻¹), inv_eq_one_div]
  have hzlow : 1 / (2 * s₀) ≤ ‖(z : ℂ)‖ := by
    have h1 : ‖(c₂ : ℂ)‖ ≤ ‖(z : ℂ) - (c₂ : ℂ)‖ + ‖(z : ℂ)‖ := by
      have h := norm_add_le ((c₂ : ℂ) - (z : ℂ)) (z : ℂ)
      rw [sub_add_cancel] at h
      rwa [norm_sub_rev] at h
    rw [hc₂norm] at h1
    have h2 : ‖(z : ℂ) - (c₂ : ℂ)‖ < ρ := by rw [hc₂coe]; exact hz
    linarith [hρinv]
  have hzup : ‖(z : ℂ)‖ ≤ D := by
    have h2 : ‖(z : ℂ) - (c₂ : ℂ)‖ < ρ := by rw [hc₂coe]; exact hz
    have h1 : ‖(z : ℂ)‖ ≤ ‖(c₂ : ℂ)‖ + ‖(z : ℂ) - (c₂ : ℂ)‖ := by
      have h := norm_add_le (c₂ : ℂ) ((z : ℂ) - (c₂ : ℂ))
      rwa [add_sub_cancel] at h
    rw [hc₂norm] at h1
    rw [hDdef]
    have h2' : 1 / s₀ + ρ ≤ 1 / s₀ + 1 := by linarith
    have h3 : ‖(z : ℂ)‖ ≤ 1 / s₀ + 1 := by linarith [h1, h2, h2']
    exact le_trans h3 (le_max_left _ _)
  -- the two points for the difference-quotient bound
  have hSc₂ : ((ModularGroup.S • c₂ : ℍ) : ℂ) = (((Work.Kernels.imagAxis s₀ hs₀ : ℍ)) : ℂ) := by
    rw [KL.coe_S_smul']
    simp only [hc₂def, Work.Kernels.imagAxis]
    rw [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv, Complex.inv_I]
    ring
  have hSznear : ‖((ModularGroup.S • z : ℍ) : ℂ)
      - (((Work.Kernels.imagAxis s₀ hs₀ : ℍ)) : ℂ)‖ < ρ₀ := by
    rw [← hSc₂, KL.norm_S_sub_S z c₂, hc₂norm]
    have hznpos : (0 : ℝ) < ‖(z : ℂ)‖ :=
      lt_of_lt_of_le (by positivity : (0:ℝ) < 1 / (2 * s₀)) hzlow
    rw [div_lt_iff₀ (mul_pos hznpos (by positivity : (0:ℝ) < 1 / s₀))]
    have h2 : ‖(z : ℂ) - (c₂ : ℂ)‖ < ρ := by rw [hc₂coe]; exact hz
    have hzw : 1 ≤ ‖(z : ℂ)‖ * (2 * s₀) := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * s₀)] at hzlow
      exact hzlow
    have hmul1 : 2 * ρ * s₀ ^ 2 * ‖(z : ℂ)‖ ≤ ρ₀ * ‖(z : ℂ)‖ :=
      mul_le_mul_of_nonneg_right hρρ₀ (norm_nonneg _)
    have hmul2 : ρ * s₀ ≤ 2 * ρ * s₀ ^ 2 * ‖(z : ℂ)‖ := by
      calc ρ * s₀ = ρ * s₀ * 1 := by ring
        _ ≤ ρ * s₀ * (‖(z : ℂ)‖ * (2 * s₀)) :=
            mul_le_mul_of_nonneg_left hzw (by positivity)
        _ = 2 * ρ * s₀ ^ 2 * ‖(z : ℂ)‖ := by ring
    have hmul3 : ‖(z : ℂ) - (c₂ : ℂ)‖ * s₀ < ρ * s₀ :=
      mul_lt_mul_of_pos_right h2 hs₀
    have hgoal : ‖(z : ℂ) - (c₂ : ℂ)‖ * s₀ < ρ₀ * ‖(z : ℂ)‖ := by linarith
    calc ‖(z : ℂ) - (c₂ : ℂ)‖ = ‖(z : ℂ) - (c₂ : ℂ)‖ * s₀ * (1 / s₀) := by field_simp
      _ < ρ₀ * ‖(z : ℂ)‖ * (1 / s₀) := mul_lt_mul_of_pos_right hgoal (by positivity)
      _ = ρ₀ * (‖(z : ℂ)‖ * (1 / s₀)) := by ring
  have hσnum : ‖(σ : ℂ) - (((Work.Kernels.imagAxis s₀ hs₀ : ℍ)) : ℂ)‖ < 2 * δ := by
    have he : (σ : ℂ) - (((Work.Kernels.imagAxis s₀ hs₀ : ℍ)) : ℂ)
        = ((τ.re - (n : ℝ) : ℝ) : ℂ) + ((τ.im - s₀ : ℝ) : ℂ) * Complex.I := by
      rw [hσdef, coe_neg_vadd]
      simp only [Work.Kernels.imagAxis]
      apply Complex.ext <;>
        simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
          Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] <;> ring
    rw [he]
    have h := norm_le_re_im (τ.re - (n : ℝ)) (τ.im - s₀)
    have h1 := (abs_lt.mp hτre).2
    have h2 := (abs_lt.mp hτim).2
    linarith
  have hσnear : ‖(σ : ℂ) - (((Work.Kernels.imagAxis s₀ hs₀ : ℍ)) : ℂ)‖ < ρ₀ :=
    lt_of_lt_of_le hσnum hδr
  have hσlow : s₀ / 2 ≤ ‖(σ : ℂ)‖ := by
    have h1 : ‖((Work.Kernels.imagAxis s₀ hs₀ : ℍ) : ℂ)‖ = s₀ := KL.norm_imagAxis s₀ hs₀
    have h3 : ‖((Work.Kernels.imagAxis s₀ hs₀ : ℍ) : ℂ)‖ ≤ ‖(σ : ℂ)‖
        + ‖((Work.Kernels.imagAxis s₀ hs₀ : ℍ) : ℂ) - (σ : ℂ)‖ := by
      have h := norm_add_le (σ : ℂ)
        (((Work.Kernels.imagAxis s₀ hs₀ : ℍ) : ℂ) - (σ : ℂ))
      rwa [add_sub_cancel] at h
    have h4 : ‖((Work.Kernels.imagAxis s₀ hs₀ : ℍ) : ℂ) - (σ : ℂ)‖ < 2 * δ := by
      rw [norm_sub_rev]; exact hσnum
    rw [h1] at h3
    linarith [h4, hδs]
  -- the distance formula between `S z` and `σ`
  have hform : ‖((ModularGroup.S • z : ℍ) : ℂ) - (σ : ℂ)‖
      = ‖(z : ℂ) - (((ModularGroup.S • σ : ℍ)) : ℂ)‖
        / (‖(z : ℂ)‖ * ‖(((ModularGroup.S • σ : ℍ)) : ℂ)‖) := by
    have h := KL.norm_S_sub_S z (ModularGroup.S • σ)
    rw [KL.S_smul_S_smul'] at h
    exact h
  have hSpD : ‖(((ModularGroup.S • σ : ℍ)) : ℂ)‖ ≤ D := by
    rw [KL.coe_S_smul', norm_neg, norm_inv, ← one_div]
    have h1 : 1 / ‖(σ : ℂ)‖ ≤ 1 / (s₀ / 2) :=
      one_div_le_one_div_of_le (by positivity) hσlow
    have h2 : 1 / (s₀ / 2) = 2 / s₀ := by field_simp
    rw [h2] at h1
    exact le_trans h1 (le_max_right _ _)
  -- the final chain
  have hj := hb (ModularGroup.S • z) σ hSznear hσnear
  rw [Work.Kernels.KernelFacts.jInvariantFun_S_smul z, jInvariantFun_neg_vadd τ n hn] at hj
  have hdist : ‖(z : ℂ) - (((ModularGroup.S • σ : ℍ)) : ℂ)‖ / D ^ 2
      ≤ ‖((ModularGroup.S • z : ℍ) : ℂ) - (σ : ℂ)‖ := by
    rw [hform,
      div_le_div_iff₀ (by positivity : (0:ℝ) < D ^ 2)
        (mul_pos (norm_pos_iff.mpr (coe_ne_zero' z))
          (norm_pos_iff.mpr (coe_ne_zero' (ModularGroup.S • σ))))]
    have hle : ‖(z : ℂ)‖ * ‖(((ModularGroup.S • σ : ℍ)) : ℂ)‖ ≤ D * D :=
      mul_le_mul hzup hSpD (norm_nonneg _) hDpos.le
    have hsq : D * D = D ^ 2 := by ring
    have hleA : ‖(z : ℂ) - (((ModularGroup.S • σ : ℍ)) : ℂ)‖
        * (‖(z : ℂ)‖ * ‖(((ModularGroup.S • σ : ℍ)) : ℂ)‖)
        ≤ ‖(z : ℂ) - (((ModularGroup.S • σ : ℍ)) : ℂ)‖ * (D * D) :=
      mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    rw [← hsq]
    exact hleA
  calc c₀ / D ^ 2 * ‖(z : ℂ) - (((ModularGroup.S • σ : ℍ)) : ℂ)‖
      = c₀ * (‖(z : ℂ) - (((ModularGroup.S • σ : ℍ)) : ℂ)‖ / D ^ 2) := by ring
    _ ≤ c₀ * ‖((ModularGroup.S • z : ℍ) : ℂ) - (σ : ℂ)‖ :=
        mul_le_mul_of_nonneg_left hdist hc₀pos.le
    _ ≤ ‖Work.Kernels.jInvariantFun z - Work.Kernels.jInvariantFun τ‖ := hj

/-- **The `S`-window bound for the CKMRV kernel on the bad lines.**

The `S`-window `|t - (Im τ)⁻¹| < η ≤ |t - Im τ|` is the neighbourhood of the `S`-conjugate pole
`t = (Im τ)⁻¹ ≈ 1/s₀`; there the kernel is bounded when `s₀ ≠ 1` (the residue of the kernel at
the `S`-branch point `S (τ - n)` vanishes, which is what `AfunFun_Sbranch_one_zero` quantifies),
and for `s₀ = 1` the window is contained in the translate-pole window so that
`Kaxis_principal_part_bound` applies. -/
theorem Kaxis_Swindow_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {s₀ : ℝ} (hs₀ : 0 < s₀) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ (τ : UpperHalfPlane) (n : ℤ) (t η : ℝ) (ht : 0 < t),
        (n = 1 ∨ n = -1) → |τ.re - (n : ℝ)| < δ → |τ.im - s₀| < δ →
        0 < η → η ≤ δ →
        |t - τ.im⁻¹| < η → η ≤ |t - τ.im| →
        Work.Kernels.jInvariantFun τ ≠
          Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t -
          (-Complex.I) * ((n : ℂ) / (2 * (Real.pi : ℂ))) *
            ((t : ℂ) - (τ.im : ℂ) + Complex.I * (((τ.re - (n : ℝ)) : ℝ) : ℂ))⁻¹‖ ≤ C := by
  rcases eq_or_ne s₀ 1 with hs1 | hs1
  · -- ================= `s₀ = 1`: the `S`-window sits inside the pole window =================
    subst hs1
    obtain ⟨δ', C', hδ'pos, hC'nn, hb'⟩ :=
      Kaxis_principal_part_bound ℓ d hd (s₀ := (1 : ℝ)) one_pos
    set δ : ℝ := min (2 * δ' / 3) (1 / 2) with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]
      exact lt_min (by linarith) (by norm_num)
    have hδδ' : δ ≤ 2 * δ' / 3 := by rw [hδdef]; exact min_le_left _ _
    have hδhalf : δ ≤ 1 / 2 := by rw [hδdef]; exact min_le_right _ _
    refine ⟨δ, C', hδpos, hC'nn, ?_⟩
    intro τ n t η ht hn hτre hτim hηpos hηδ ht1 ht2 hjne
    refine hb' τ n t ht hn ?_ ?_ ?_ hjne
    · exact lt_of_lt_of_le hτre (le_trans hδδ' (by linarith))
    · exact lt_of_lt_of_le hτim (le_trans hδδ' (by linarith))
    · -- the `S`-window is inside `|t - τ.im| < 4 δ'`
      have hτim_lo : 1 / 2 ≤ τ.im := by
        have h := (abs_lt.mp hτim).1
        linarith [hδhalf]
      have hηδ' : η ≤ 2 * δ' / 3 := le_trans hηδ hδδ'
      have hinva : |1 / τ.im - τ.im| ≤ 5 * δ := by
        have hnum : |1 - τ.im ^ 2| ≤ δ * (2 + δ) := by
          have heq : (1 : ℝ) - τ.im ^ 2 = (1 - τ.im) * (1 + τ.im) := by ring
          rw [heq, abs_mul, abs_sub_comm 1 τ.im]
          have h3 : |1 + τ.im| ≤ 2 + δ := by
            rw [abs_le]
            have h := abs_lt.mp hτim
            constructor <;> linarith [h.1, h.2]
          exact mul_le_mul (le_of_lt hτim) h3 (abs_nonneg _) (by linarith [hτim_lo])
        have hdiv : 1 / τ.im - τ.im = (1 - τ.im ^ 2) / τ.im := by field_simp
        rw [hdiv, abs_div, abs_of_pos (show (0 : ℝ) < τ.im by linarith [hτim_lo])]
        rw [div_le_iff₀ (show (0 : ℝ) < τ.im by linarith [hτim_lo])]
        nlinarith [hnum, hδhalf, hτim_lo, hδpos]
      have hsplit : |t - τ.im| ≤ |t - τ.im⁻¹| + |τ.im⁻¹ - τ.im| := abs_sub_le t τ.im⁻¹ τ.im
      have hinv1 : |τ.im⁻¹ - τ.im| = |1 / τ.im - τ.im| := by rw [inv_eq_one_div]
      have h1 : |t - τ.im| < η + 5 * δ := by
        rw [hinv1] at hsplit
        linarith [hsplit, ht1, hinva]
      have h2 : η + 5 * δ ≤ 6 * δ := by linarith [hηδ]
      have h3 : 6 * δ ≤ 4 * δ' := by linarith [hδδ']
      linarith [h1, h2, h3]
  · -- ============================ `s₀ ≠ 1` ============================
    obtain ⟨δ₁, ρ₁, C₁, hδ₁pos, hρ₁pos, hC₁pos, hbA⟩ := AfunFun_Sbranch_one_zero ℓ d hd hs₀
    obtain ⟨δ₂, ρ₂, c₂, hδ₂pos, hρ₂pos, hc₂pos, hbJ⟩ := jDiff_lower_Sbranch hs₀ hs1
    set R : ℝ := min ρ₁ ρ₂ with hRdef
    have hRpos : 0 < R := lt_min hρ₁pos hρ₂pos
    have hRρ₁ : R ≤ ρ₁ := min_le_left _ _
    have hRρ₂ : R ≤ ρ₂ := min_le_right _ _
    set c₀ : ℝ := |1 / s₀ - s₀| / 4 with hc₀def
    have hc₀pos : 0 < c₀ := by
      rw [hc₀def]
      have hne : (1 : ℝ) / s₀ - s₀ ≠ 0 := by
        intro h
        have h2 : 1 / s₀ = s₀ := by linarith
        rw [div_eq_iff hs₀.ne'] at h2
        exact hs1 (by nlinarith [h2, hs₀])
      linarith [abs_pos.mpr hne]
    set m : ℝ := min (min δ₁ δ₂) (min R (min (R * s₀ ^ 2) (min (c₀ * s₀ ^ 2) c₀)))
      with hmdef
    have hmpos : 0 < m := by
      rw [hmdef]
      exact lt_min (lt_min hδ₁pos hδ₂pos)
        (lt_min hRpos (lt_min (by positivity) (lt_min (by positivity) hc₀pos)))
    set δ : ℝ := min m (min s₀ 1) / 64 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]
      exact div_pos (lt_min hmpos (lt_min hs₀ one_pos)) (by norm_num)
    have hmδ₁ : m ≤ δ₁ :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have hmδ₂ : m ≤ δ₂ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    have hmR : m ≤ R := le_trans (min_le_right _ _) (min_le_left _ _)
    have hmRs : m ≤ R * s₀ ^ 2 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hmc₀s : m ≤ c₀ * s₀ ^ 2 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hmc₀ : m ≤ c₀ :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hδm : δ ≤ m / 64 := by
      rw [hδdef]
      have h1 : min m (min s₀ 1) ≤ m := min_le_left _ _
      linarith
    have hδδ₁ : δ ≤ δ₁ / 64 := by linarith [hδm, hmδ₁]
    have hδδ₂ : δ ≤ δ₂ / 64 := by linarith [hδm, hmδ₂]
    have hδR : δ ≤ R / 64 := by linarith [hδm, hmR]
    have hδRs : δ ≤ R * s₀ ^ 2 / 16 := by linarith [hδm, hmRs]
    have hδc₀s : δ ≤ c₀ * s₀ ^ 2 / 64 := by linarith [hδm, hmc₀s]
    have hδc₀ : δ ≤ c₀ / 64 := by linarith [hδm, hmc₀]
    have hδs₀4 : δ ≤ s₀ / 4 := by
      have h1 : min m (min s₀ 1) ≤ s₀ := le_trans (min_le_right _ _) (min_le_left _ _)
      have h2 : δ ≤ min m (min s₀ 1) / 64 := by rw [hδdef]
      linarith
    have hδ1half : δ ≤ 1 / 2 := by
      have h1 : min m (min s₀ 1) ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
      have h2 : δ ≤ min m (min s₀ 1) / 64 := by rw [hδdef]
      linarith
    refine ⟨δ, C₁ / c₂ + 1 / (2 * Real.pi * c₀), hδpos, by positivity, ?_⟩
    intro τ n t η ht hn hτre hτim hηpos hηδ ht1 ht2 hjne
    have hτre₁ : |τ.re - (n : ℝ)| < δ₁ := by
      have := hδδ₁; linarith
    have hτre₂ : |τ.re - (n : ℝ)| < δ₂ := by
      have := hδδ₂; linarith
    have hτim₁ : |τ.im - s₀| < δ₁ := by
      have := hδδ₁; linarith
    have hτim₂ : |τ.im - s₀| < δ₂ := by
      have := hδδ₂; linarith
    have hτim_lohalf : s₀ / 2 ≤ τ.im := by
      have h := (abs_lt.mp hτim).1
      linarith [hδs₀4]
    have hτim_lo : 0 < τ.im := by linarith [hτim_lohalf, hs₀]
    -- `|t - 1/τ.im| < η`
    have ht1' : |t - 1 / τ.im| < η := by rwa [inv_eq_one_div] at ht1
    -- the `z`-window hypothesis of the two auxiliary statements
    have hinvsub : |1 / τ.im - 1 / s₀| ≤ 2 * δ / s₀ ^ 2 := by
      have h1 : 1 / τ.im - 1 / s₀ = (s₀ - τ.im) / (τ.im * s₀) := by field_simp
      rw [h1, abs_div, abs_of_pos (by positivity : (0:ℝ) < τ.im * s₀)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h2 : |s₀ - τ.im| ≤ δ := by
        rw [abs_sub_comm]; exact le_of_lt hτim
      have h3 : δ * s₀ ^ 2 ≤ 2 * δ * (τ.im * s₀) := by
        have h4 : s₀ ^ 2 ≤ 2 * τ.im * s₀ := by nlinarith [hτim_lohalf, hs₀]
        calc δ * s₀ ^ 2 ≤ δ * (2 * τ.im * s₀) := mul_le_mul_of_nonneg_left h4 hδpos.le
          _ = 2 * δ * (τ.im * s₀) := by ring
      calc |s₀ - τ.im| * s₀ ^ 2 ≤ δ * s₀ ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ ≤ 2 * δ * (τ.im * s₀) := h3
    have hzwin : |t - 1 / s₀| < R := by
      have hsplit : |t - 1 / s₀| ≤ |t - 1 / τ.im| + |1 / τ.im - 1 / s₀| :=
        abs_sub_le t (1 / τ.im) (1 / s₀)
      have h1 : 2 * δ / s₀ ^ 2 ≤ R / 2 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < s₀ ^ 2)]
        linarith [hδRs]
      linarith [hsplit, ht1', hηδ, hδR, h1]
    have hzcoe : (((Work.Kernels.imagAxis t ht : ℍ)) : ℂ) - Complex.I / (s₀ : ℂ)
        = ((t - 1 / s₀ : ℝ) : ℂ) * Complex.I := by
      rw [show ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I from rfl]
      rw [show Complex.I / (s₀ : ℂ) = ((s₀⁻¹ : ℝ) : ℂ) * Complex.I by
        rw [div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm]]
      push_cast
      ring
    have hznorm : ‖(((Work.Kernels.imagAxis t ht : ℍ)) : ℂ) - Complex.I / (s₀ : ℂ)‖
        = |t - 1 / s₀| := by
      rw [hzcoe, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hz₁ : ‖(((Work.Kernels.imagAxis t ht : ℍ)) : ℂ) - Complex.I / (s₀ : ℂ)‖ < ρ₁ := by
      rw [hznorm]; exact lt_of_lt_of_le hzwin hRρ₁
    have hz₂ : ‖(((Work.Kernels.imagAxis t ht : ℍ)) : ℂ) - Complex.I / (s₀ : ℂ)‖ < ρ₂ := by
      rw [hznorm]; exact lt_of_lt_of_le hzwin hRρ₂
    -- the two auxiliary bounds
    have hA := hbA τ (Work.Kernels.imagAxis t ht) n hn hτre₁ hτim₁ hz₁
    have hJ := hbJ τ (Work.Kernels.imagAxis t ht) n hn hτre₂ hτim₂ hz₂
    -- `|t - τ.im| ≥ c₀`, hence `‖z - z₀‖ ≥ c₀`
    have hc₀step : c₀ ≤ |t - τ.im| := by
      have hbig : |1 / s₀ - s₀| / 2 ≤ |1 / τ.im - τ.im| := by
        have h3 : |1 / s₀ - s₀| ≤ |(1 / s₀ - s₀) - (1 / τ.im - τ.im)| + |1 / τ.im - τ.im| := by
          have h := norm_add_le ((1 / s₀ - s₀) - (1 / τ.im - τ.im)) (1 / τ.im - τ.im)
          rw [sub_add_cancel] at h
          simpa using h
        have h4 : |(1 / s₀ - s₀) - (1 / τ.im - τ.im)| ≤ 2 * δ / s₀ ^ 2 + δ := by
          have he : (1 / s₀ - s₀) - (1 / τ.im - τ.im) = (1 / s₀ - 1 / τ.im) + (τ.im - s₀) := by
            ring
          rw [he]
          refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
          · rw [abs_sub_comm]; exact hinvsub
          · exact le_of_lt hτim
        have h5 : 2 * δ / s₀ ^ 2 ≤ |1 / s₀ - s₀| / 4 := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < s₀ ^ 2)]
          rw [hc₀def] at hδc₀s
          linarith [hδc₀s]
        have h6 : δ ≤ |1 / s₀ - s₀| / 4 := by
          rw [hc₀def] at hδc₀
          linarith [hδc₀]
        linarith
      have hstep : |1 / τ.im - τ.im| / 2 ≤ |t - τ.im| := by
        by_contra hcon
        have hcon' : |t - τ.im| < |1 / τ.im - τ.im| / 2 := lt_of_not_ge hcon
        have h3 : |1 / τ.im - τ.im| ≤ |1 / τ.im - t| + |t - τ.im| :=
          abs_sub_le (1 / τ.im) t τ.im
        have h4 : |1 / τ.im - t| = |t - 1 / τ.im| := abs_sub_comm (1 / τ.im) t
        rw [h4] at h3
        linarith [h3, ht1', ht2, hcon']
      rw [hc₀def]
      linarith [hbig, hstep]
    have hzz₀ : c₀ ≤ ‖(((Work.Kernels.imagAxis t ht : ℍ)) : ℂ)
        - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖ := by
      have he : (((Work.Kernels.imagAxis t ht : ℍ)) : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)
          = ((-(τ.re - (n : ℝ)) : ℝ) : ℂ) + ((t - τ.im : ℝ) : ℂ) * Complex.I := by
        rw [coe_neg_vadd]
        rw [show ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I from rfl]
        apply Complex.ext <;>
          simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
            Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
            UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] <;> ring
      have h2 : |t - τ.im| ≤ ‖(((Work.Kernels.imagAxis t ht : ℍ)) : ℂ)
          - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖ := by
        rw [he]
        have h3 := Complex.abs_im_le_norm
          ((((-(τ.re - (n : ℝ)) : ℝ)) : ℂ) + ((t - τ.im : ℝ) : ℂ) * Complex.I)
        simpa using h3
      linarith [hc₀step, h2]
    -- the vanishing of the `j`-denominator at the branch point gives `z ≠ S (τ - n)`
    have hj₀ : Work.Kernels.jInvariantFun ((-(n : ℝ)) +ᵥ τ) = Work.Kernels.jInvariantFun τ :=
      jInvariantFun_neg_vadd τ n hn
    have hjne' : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
        ≠ Work.Kernels.jInvariantFun ((-(n : ℝ)) +ᵥ τ) := by
      rw [hj₀]; exact hjne.symm
    have hznep : ‖(((Work.Kernels.imagAxis t ht : ℍ)) : ℂ)
        - (((ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) : ℍ)) : ℂ)‖ ≠ 0 := by
      intro h0
      have h1 : Work.Kernels.imagAxis t ht = ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) :=
        UpperHalfPlane.ext (sub_eq_zero.mp (norm_eq_zero.mp h0))
      exact hjne' (by rw [h1, Work.Kernels.KernelFacts.jInvariantFun_S_smul, hj₀])
    -- the kernel identity and the bound for `K`
    have hK := Kfun_eq_neg_A_div ℓ d hd τ (Work.Kernels.imagAxis t ht) n hn hjne'
    have hKnorm : ‖Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht)‖ ≤ C₁ / c₂ := by
      have hdenpos : 0 < ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
          - Work.Kernels.jInvariantFun ((-(n : ℝ)) +ᵥ τ)‖ :=
        norm_pos_iff.mpr (sub_ne_zero.mpr hjne')
      have hJ' : c₂ * ‖(((Work.Kernels.imagAxis t ht : ℍ)) : ℂ)
          - (((ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) : ℍ)) : ℂ)‖
          ≤ ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
              - Work.Kernels.jInvariantFun ((-(n : ℝ)) +ᵥ τ)‖ := by
        rwa [hj₀]
      have hA' : ‖AfunFun ℓ d τ (Work.Kernels.imagAxis t ht)‖
          ≤ C₁ * ‖(((Work.Kernels.imagAxis t ht : ℍ)) : ℂ)
              - (((ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) : ℍ)) : ℂ)‖ := hA
      rw [hK, norm_mul, norm_neg, norm_inv]
      rw [show ‖AfunFun ℓ d τ (Work.Kernels.imagAxis t ht)‖
            * (‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
                - Work.Kernels.jInvariantFun ((-(n : ℝ)) +ᵥ τ)‖)⁻¹
          = ‖AfunFun ℓ d τ (Work.Kernels.imagAxis t ht)‖
            / ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
                - Work.Kernels.jInvariantFun ((-(n : ℝ)) +ᵥ τ)‖ by
        rw [div_eq_mul_inv]]
      rw [div_le_div_iff₀ hdenpos hc₂pos]
      calc ‖AfunFun ℓ d τ (Work.Kernels.imagAxis t ht)‖ * c₂
          ≤ (C₁ * ‖(((Work.Kernels.imagAxis t ht : ℍ)) : ℂ)
              - (((ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) : ℍ)) : ℂ)‖) * c₂ :=
            mul_le_mul_of_nonneg_right hA' hc₂pos.le
        _ = C₁ * (c₂ * ‖(((Work.Kernels.imagAxis t ht : ℍ)) : ℂ)
              - (((ModularGroup.S • ((-(n : ℝ)) +ᵥ τ) : ℍ)) : ℂ)‖) := by ring
        _ ≤ C₁ * ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
              - Work.Kernels.jInvariantFun ((-(n : ℝ)) +ᵥ τ)‖ :=
            mul_le_mul_of_nonneg_left hJ' hC₁pos.le
    -- the principal part is bounded because `‖z - z₀‖ ≥ c₀`
    have hppnorm : ‖((n : ℂ) / (2 * (Real.pi : ℂ))) *
        ((((Work.Kernels.imagAxis t ht : ℍ)) : ℂ) - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ))⁻¹‖
        ≤ 1 / (2 * Real.pi * c₀) := by
      rw [norm_mul, norm_inv]
      have hn1 : ‖(n : ℂ)‖ = 1 := by
        rcases hn with h | h <;> rw [h] <;> norm_num
      have hπ : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
        rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
      have h1 : ‖(n : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
        rw [norm_div, hn1, hπ]
      rw [h1]
      have h2 : ‖(((Work.Kernels.imagAxis t ht : ℍ)) : ℂ)
          - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖⁻¹ ≤ c₀⁻¹ :=
        inv_anti₀ hc₀pos hzz₀
      calc 1 / (2 * Real.pi) * ‖(((Work.Kernels.imagAxis t ht : ℍ)) : ℂ)
            - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ)‖⁻¹
          ≤ 1 / (2 * Real.pi) * c₀⁻¹ :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 1 / (2 * Real.pi * c₀) := by field_simp
    have htarget : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t -
        (-Complex.I) * ((n : ℂ) / (2 * (Real.pi : ℂ))) *
          ((t : ℂ) - (τ.im : ℂ) + Complex.I * (((τ.re - (n : ℝ)) : ℝ) : ℂ))⁻¹
        = Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht)
          - ((n : ℂ) / (2 * (Real.pi : ℂ))) *
            ((((Work.Kernels.imagAxis t ht : ℍ)) : ℂ)
              - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ))⁻¹ := by
      rw [principal_part_eq n t ht τ, Work.Kernels.Kaxis, dif_pos ht]
    rw [htarget]
    calc ‖Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht)
          - ((n : ℂ) / (2 * (Real.pi : ℂ))) *
            ((((Work.Kernels.imagAxis t ht : ℍ)) : ℂ)
              - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ))⁻¹‖
        ≤ ‖Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht)‖
          + ‖((n : ℂ) / (2 * (Real.pi : ℂ))) *
            ((((Work.Kernels.imagAxis t ht : ℍ)) : ℂ)
              - (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ))⁻¹‖ := norm_sub_le _ _
      _ ≤ C₁ / c₂ + 1 / (2 * Real.pi * c₀) := add_le_add hKnorm hppnorm
end

end Work.Asymptotics
