import Submission.NBody.MarchalClusterShapeLimit
import Submission.NBody.MarchalClusterShape

/-!
# Ferrario–Terracini `propo:srcblowup`: the normalised configuration at rescaled times

If the normalised configuration `s` of a colliding cluster converges to `s̄` along a sequence
`λ_n → 0⁺`, then it converges to `s̄` at *every* rescaled time: `s(a λ_n) → s̄` for every fixed
`a > 0`.

For `a ≥ 1` this is immediate (composition with `λ ↦ aλ`).  For `a < 1` one uses the mean value
inequality on `[aλ, λ]` together with `as:lim1` (`u ṡ(u) → 0`): the derivative bound
`‖ṡ(u)‖ ≤ ε'/(aλ)` is uniform on `[aλ, λ]`, whence `‖s(aλ) - s(λ)‖ ≤ ε'(1-a)/a`.

Everything in this file is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set
open scoped BigOperators Topology
open InnerProductSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- **Ferrario–Terracini `propo:srcblowup`.**  If `s(λ) → s̄` as `λ → 0⁺` then, for every fixed
`a > 0`, also `s(a λ) → s̄`.  (For `a ≥ 1` this is immediate; for `a < 1` it follows from the
mean-value inequality and `u ṡ(u) → 0`.) -/
theorem tendsto_clusterShape_comp_mul {m : Fin N → ℝ} {k : Finset (Fin N)} {x : ℝ → EN E N}
    {ε : ℝ} {sbar : EN E N} (hε : 0 < ε)
    (hsd : ∀ u ∈ Ioo (0:ℝ) ε, HasDerivAt (fun τ : ℝ => clusterShape m k (x τ))
      (deriv (fun τ : ℝ => clusterShape m k (x τ)) u) u)
    (hts : Tendsto (fun u : ℝ => u • deriv (fun τ : ℝ => clusterShape m k (x τ)) u)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    (hs : Tendsto (fun t : ℝ => clusterShape m k (x t))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => clusterShape m k (x (a * t)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar) := by
  by_cases ha1 : 1 ≤ a
  · have hcomp : Tendsto (fun t : ℝ => a * t) (nhdsWithin (0:ℝ) (Ioi 0))
        (nhdsWithin (0:ℝ) (Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h0 : Tendsto (fun t : ℝ => t) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) :=
          tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
        have h : Tendsto (fun t : ℝ => a * t) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (a * 0)) :=
          tendsto_const_nhds.mul h0
        rwa [mul_zero] at h
      · filter_upwards [Ioo_mem_nhdsGT hε] with t ht
        exact mul_pos ha ht.1
    exact hs.comp hcomp
  · have hlt : a < 1 := lt_of_not_ge ha1
    have h1a : 0 < 1 - a := by linarith
    have hdist : ∀ ε' > 0, ∀ᶠ y in nhdsWithin (0:ℝ) (Ioi 0),
        ‖clusterShape m k (x (a * y)) - clusterShape m k (x y)‖ ≤ ε' := by
      intro ε' hε'
      have hδpos : 0 < ε' * a / (1 - a) := by positivity
      have hev : ∀ᶠ u in nhdsWithin (0:ℝ) (Ioi 0),
          ‖u • deriv (fun τ : ℝ => clusterShape m k (x τ)) u‖ < ε' * a / (1 - a) := by
        have h := hts.eventually (Metric.ball_mem_nhds (0 : EN E N) hδpos)
        filter_upwards [h] with u hu
        rwa [dist_zero_right] at hu
      rw [eventually_nhdsWithin_iff] at hev
      obtain ⟨r, hrpos, hr⟩ := Metric.eventually_nhds_iff_ball.mp hev
      set ρ : ℝ := min (min r ε) 1 with hρ
      have hρpos : 0 < ρ := by
        rw [hρ]; exact lt_min (lt_min hrpos hε) one_pos
      filter_upwards [Ioo_mem_nhdsGT hρpos] with y hy
      have hy0 : 0 < y := hy.1
      have hyr : y < r := lt_of_lt_of_le hy.2
        (by rw [hρ]; exact le_trans (min_le_left _ _) (min_le_left _ _))
      have hye : y < ε := lt_of_lt_of_le hy.2
        (by rw [hρ]; exact le_trans (min_le_left _ _) (min_le_right _ _))
      have haly : a * y < y := by nlinarith
      have haypos : 0 < a * y := mul_pos ha hy0
      have hderbound : ∀ u ∈ Ico (a * y) y,
          ‖deriv (fun τ : ℝ => clusterShape m k (x τ)) u‖
            ≤ (ε' * a / (1 - a)) / (a * y) := by
        intro u hu
        have hu0 : 0 < u := lt_of_lt_of_le haypos hu.1
        have hur : u < r := lt_trans hu.2 hyr
        have hbu := hr u (Metric.mem_ball.mpr (by
          rw [Real.dist_eq, sub_zero, abs_of_pos hu0]; exact hur)) hu0
        have hscale : ‖u • deriv (fun τ : ℝ => clusterShape m k (x τ)) u‖
            = u * ‖deriv (fun τ : ℝ => clusterShape m k (x τ)) u‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hu0]
        rw [hscale] at hbu
        have hayu : a * y ≤ u := hu.1
        have hd0 : 0 ≤ ‖deriv (fun τ : ℝ => clusterShape m k (x τ)) u‖ := norm_nonneg _
        rw [le_div_iff₀ (mul_pos ha hy0)]
        nlinarith [hbu, hayu, hd0, mul_nonneg hd0 (sub_nonneg.mpr hayu)]
      have hcont : ContinuousOn (fun τ : ℝ => clusterShape m k (x τ)) (Icc (a * y) y) := by
        intro u hu
        have hu0 : 0 < u := lt_of_lt_of_le haypos hu.1
        have hue : u < ε := lt_of_le_of_lt hu.2 hye
        exact ((hsd u ⟨hu0, hue⟩).continuousAt).continuousWithinAt
      have hder : ∀ u ∈ Ico (a * y) y,
          HasDerivWithinAt (fun τ : ℝ => clusterShape m k (x τ))
            (deriv (fun τ : ℝ => clusterShape m k (x τ)) u) (Ici u) u := by
        intro u hu
        have hu0 : 0 < u := lt_of_lt_of_le haypos hu.1
        have hue : u < ε := lt_trans hu.2 hye
        exact (hsd u ⟨hu0, hue⟩).hasDerivWithinAt
      have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment (f := fun τ : ℝ => clusterShape m k (x τ))
        (f' := fun u : ℝ => deriv (fun τ : ℝ => clusterShape m k (x τ)) u)
        (C := (ε' * a / (1 - a)) / (a * y)) hcont hder hderbound y ⟨le_of_lt haly, le_rfl⟩
      have hval : (ε' * a / (1 - a)) / (a * y) * (y - a * y) = ε' := by
        have h1 : (1 : ℝ) - a ≠ 0 := ne_of_gt h1a
        have h2 : a * y ≠ 0 := ne_of_gt haypos
        field_simp
      rw [hval, norm_sub_rev] at hmvt
      exact hmvt
    have hnorm : Tendsto
        (fun y : ℝ => ‖clusterShape m k (x (a * y)) - clusterShape m k (x y)‖)
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
      rw [Metric.tendsto_nhds]
      intro ε' hε'
      filter_upwards [hdist (ε'/2) (by linarith)] with y hy
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
      linarith
    have hdiff : Tendsto (fun y : ℝ => clusterShape m k (x (a * y)) - clusterShape m k (x y))
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0) := by
      rwa [tendsto_zero_iff_norm_tendsto_zero]
    have hsum := hdiff.add hs
    rw [zero_add] at hsum
    refine Filter.Tendsto.congr' ?_ hsum
    filter_upwards with y
    abel


/-- **`propo:srcblowup` for an isolated colliding cluster.**  Every limit of the normalised
configurations is also the limit of the normalised configurations at any rescaled time. -/
theorem tendsto_clusterShape_comp_mul_of_isolated {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε C ν Cv : ℝ} {sbar : EN E N}
    (hm : ∀ i, 0 < m i) (hk2 : 2 ≤ k.card) (hε : 0 < ε) (hC : 0 < C) (hν : 0 < ν)
    (hCv : 0 ≤ Cv)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hE : ∀ t ∈ Ioo (0:ℝ) ε, |clusterRelEnergy m k (x t) (deriv x t)| ≤ C)
    (hW : ∀ t ∈ Ioo (0:ℝ) ε, |crossWork m k (x t) (cmRel m k (x t))| ≤ C)
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x t) t)
    (hd3 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv (deriv x)) (deriv (deriv (deriv x)) t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x t = ∇_[m] (U m) (x t))
    (hsep : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparatedWeak k (x t) ν)
    (hv : ∀ t ∈ Ioo (0:ℝ) ε, ∀ j ∉ k,
      ‖deriv x t j‖ ≤ Cv * Real.sqrt (clusterPotential m k (x t)))
    (hI : Tendsto (fun t : ℝ => clusterInertia m k (x t)) (nhdsWithin (0:ℝ) (Ioi 0)) (nhds 0))
    (hs : Tendsto (fun t : ℝ => clusterShape m k (x t))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => clusterShape m k (x (a * t)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds sbar) := by
  have hpos : ∀ τ ∈ Ioo (0:ℝ) ε, 0 < clusterInertia m k (x τ) :=
    fun τ hτ => clusterInertia_pos hm hk2 (hnc τ hτ)
  have hsd : ∀ u ∈ Ioo (0:ℝ) ε, HasDerivAt (fun τ : ℝ => clusterShape m k (x τ))
      (deriv (fun τ : ℝ => clusterShape m k (x τ)) u) u := by
    intro u hu
    have hev : ∀ᶠ s in 𝓝 u, HasDerivAt x (deriv x s) s := by
      filter_upwards [isOpen_Ioo.mem_nhds hu] with s hs
      exact hx s hs
    have h := hasDerivAt_clusterShape_curve (hpos u hu) hev
    exact h.congr_deriv h.deriv.symm
  have hts := tendsto_mul_deriv_clusterShape (m := m) (k := k) (x := x) (ε := ε) (C := C)
    (ν := ν) (Cv := Cv) hm hk2 hε hC hν hCv hnc hE hW hx hd2 hd3 hode hsep hv hI
  exact tendsto_clusterShape_comp_mul (m := m) (k := k) (x := x) hε hsd hts hs ha

end Submission.NBody
