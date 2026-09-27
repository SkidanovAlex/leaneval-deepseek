import Mathlib

/-!
# Sard-lite, step 2: the cubic estimate at nearby critical points

The analytic input of `green_reduction/sard_covering.lean`: **the values of a `C³` function at two
critical points are cubically close**.  The derivation (this is the whole content of Sard's lemma in
dimension two, and it is what makes the critical values a null set):

* put `φ t = f (x + t • v)` with `v = p - x`; then `φ'(0) = Df x (v) = 0` and
  `φ'(1) = Df p (v) = 0`, because `x` and `p` are critical;
* Taylor's theorem with the mean-value remainder, of order `2` for `φ` and of order `1` for `φ'`,
  gives `|φ 1 - φ 0 - φ'' 0 / 2| ≤ C/2` and `|φ'' 0| ≤ C`, where `C` bounds `|φ'''|`;
* hence `|f p - f x| = |φ 1 - φ 0| ≤ C`, and with `|φ'''| ≤ ‖D³f‖ · ‖v‖³` this is
  `≤ K * ‖p - x‖ ^ 3`.

The two lemmas below are exactly these two steps.  `cubic_one_dim` is the one-variable heart (it is
where `taylor_mean_remainder_bound` enters); `cubic_critical_estimate` is the transport to `ℂ`,
whose only extra ingredient is the chain rule at order `3` along an affine line, i.e.
`iteratedDerivWithin 3 (fun t => f (x + t • v)) (Icc 0 1) t = iteratedFDeriv ℝ 3 f (x + t•v) ![v,v,v]`.
-/

open Set Metric Filter
open scoped Topology Pointwise

namespace Work.SimplyConnected.ABS.green_reduction

/-- **The one-variable cubic estimate.**  If `φ` is `C³` on `[0,1]`, its one-sided derivatives at
the two endpoints vanish, and `C` bounds its third derivative, then `|φ 1 - φ 0| ≤ C`. -/
lemma cubic_one_dim {φ : ℝ → ℝ} {C : ℝ}
    (hφ : ContDiffOn ℝ 3 φ (Set.Icc (0:ℝ) 1))
    (hC : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖iteratedDerivWithin 3 φ (Set.Icc (0:ℝ) 1) t‖ ≤ C)
    (h0 : derivWithin φ (Set.Icc (0:ℝ) 1) 0 = 0)
    (h1 : derivWithin φ (Set.Icc (0:ℝ) 1) 1 = 0) :
    |φ 1 - φ 0| ≤ C := by
  set s : Set ℝ := Set.Icc (0:ℝ) 1 with hs
  have hs01 : (0:ℝ) ∈ s ∧ (1:ℝ) ∈ s := by rw [hs]; norm_num
  -- Step 1: the order-two Taylor expansion of `φ`
  have hT2 := taylor_mean_remainder_bound (f := φ) (a := (0:ℝ)) (b := (1:ℝ)) (C := C) (x := (1:ℝ))
    (n := 2) (by norm_num) hφ (by norm_num) hC
  rw [Real.norm_eq_abs] at hT2
  -- identify the Taylor polynomial
  have htel : taylorWithinEval φ 2 s 0 1
      = φ 0 + derivWithin φ s 0 + (iteratedDerivWithin 2 φ s 0) / 2 := by
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [iteratedDerivWithin_zero, iteratedDerivWithin_one, Finset.sum_singleton,
      Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_mul, sub_zero, smul_eq_mul]
    norm_num
    ring
  rw [htel] at hT2
  rw [h0] at hT2
  have hT2' : |φ 1 - φ 0 - iteratedDerivWithin 2 φ s 0 / 2| ≤ C / 2 := by
    have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [hfac] at hT2
    norm_num at hT2
    convert hT2 using 2
    ring
  -- Step 2: bound the second derivative at `0`
  have hψ : ContDiffOn ℝ 2 (derivWithin φ s) s :=
    hφ.derivWithin (uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1))
      (by norm_num : ((2 : ℕ) : WithTop ℕ∞) + 1 ≤ 3)
  have hCψ : ∀ t ∈ s, ‖iteratedDerivWithin 2 (derivWithin φ s) s t‖ ≤ C := by
    intro t ht
    have h2 : iteratedDerivWithin 2 (derivWithin φ s) s t = iteratedDerivWithin 3 φ s t := by
      simp only [iteratedDerivWithin_succ, iteratedDerivWithin_zero, iteratedDerivWithin_one]
    rw [h2]
    exact hC t ht
  have hT1 := taylor_mean_remainder_bound (f := derivWithin φ s) (a := (0:ℝ)) (b := (1:ℝ))
    (C := C) (x := (1:ℝ)) (n := 1) (by norm_num) hψ (by norm_num) hCψ
  rw [Real.norm_eq_abs] at hT1
  have htelψ : taylorWithinEval (derivWithin φ s) 1 s 0 1
      = derivWithin φ s 0 + iteratedDerivWithin 2 φ s 0 := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.mem_range, zero_add,
      Finset.sum_singleton]
    rw [iteratedDerivWithin_zero, iteratedDerivWithin_one]
    have h3 : derivWithin (derivWithin φ s) s 0 = iteratedDerivWithin 2 φ s 0 := by
      simp only [iteratedDerivWithin_succ, iteratedDerivWithin_zero, iteratedDerivWithin_one]
    rw [h3]
    norm_num
  rw [htelψ, h0, h1] at hT1
  have hbd : |iteratedDerivWithin 2 φ s 0| ≤ C := by
    have hfac : ((Nat.factorial 1 : ℕ) : ℝ) = 1 := by norm_num [Nat.factorial]
    rw [hfac] at hT1
    norm_num at hT1
    simpa using hT1
  -- Step 3: combine
  have hhalf : |iteratedDerivWithin 2 φ s 0 / 2| ≤ C / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith [hbd]
  have hsplit : φ 1 - φ 0 = (φ 1 - φ 0 - iteratedDerivWithin 2 φ s 0 / 2) +
      iteratedDerivWithin 2 φ s 0 / 2 := by ring
  calc |φ 1 - φ 0| = |(φ 1 - φ 0 - iteratedDerivWithin 2 φ s 0 / 2) +
        iteratedDerivWithin 2 φ s 0 / 2| := by
        rw [show (φ 1 - φ 0 - iteratedDerivWithin 2 φ s 0 / 2) +
          iteratedDerivWithin 2 φ s 0 / 2 = φ 1 - φ 0 from by ring]
    _ ≤ |φ 1 - φ 0 - iteratedDerivWithin 2 φ s 0 / 2| +
        |iteratedDerivWithin 2 φ s 0 / 2| := abs_add_le _ _
    _ ≤ C / 2 + C / 2 := add_le_add hT2' hhalf
    _ = C := by ring

/-- **The cubic estimate at nearby critical points, planewise.**  There is a constant `K` (depending
only on the ball and the bound `C` for the third derivative) such that the values of `f` at any two
critical points of the closed ball of radius `r` around `x₀` differ by at most `K * ‖p - x‖ ^ 3`. -/
theorem cubic_critical_estimate {f : ℂ → ℝ} {x₀ : ℂ} {r r' C : ℝ} (hr : 0 < r) (hrr : r < r')
    (hf : ContDiffOn ℝ 3 f (Metric.ball x₀ r'))
    (h3 : ∀ z ∈ Metric.closedBall x₀ r, ‖iteratedFDeriv ℝ 3 f z‖ ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Metric.closedBall x₀ r, fderiv ℝ f x = 0 →
      ∀ p ∈ Metric.closedBall x₀ r, fderiv ℝ f p = 0 → |f p - f x| ≤ K * ‖p - x‖ ^ 3 := by
  have hC0 : 0 ≤ C := by
    have hx0 : x₀ ∈ Metric.closedBall x₀ r := by
      rw [Metric.mem_closedBall, dist_self]; exact le_of_lt hr
    exact le_trans (norm_nonneg _) (h3 x₀ hx0)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx hxc p hp hpc
  set v : ℂ := p - x with hv
  set g : ℝ →L[ℝ] ℂ := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v with hg
  have hg_apply : ∀ t : ℝ, g t = t • v := by
    intro t; rw [hg, ContinuousLinearMap.smulRight_apply]; simp
  set s : Set ℂ := {w : ℂ | x + w ∈ Metric.ball x₀ r'} with hs
  have hs_open : IsOpen s := by
    rw [hs]; exact Metric.isOpen_ball.preimage (by fun_prop)
  set B : Set ℝ := g ⁻¹' s with hB
  have hB_open : IsOpen B := by
    rw [hB]; exact hs_open.preimage g.continuous
  set φ : ℝ → ℝ := fun t => f (x + g t) with hφ
  have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • v ∈ Metric.closedBall x₀ r := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have hxr : ‖x - x₀‖ ≤ r := by
      have := Metric.mem_closedBall.mp hx; rwa [dist_eq_norm] at this
    have hpr : ‖p - x₀‖ ≤ r := by
      have := Metric.mem_closedBall.mp hp; rwa [dist_eq_norm] at this
    have h1t : (0:ℝ) ≤ 1 - t := by linarith
    have h2t : (0:ℝ) ≤ t := ht1
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hid : x + t • v - x₀ = (1 - t) • (x - x₀) + t • (p - x₀) := by
      rw [hv]; module
    rw [hid]
    calc ‖(1 - t) • (x - x₀) + t • (p - x₀)‖
        ≤ ‖(1 - t) • (x - x₀)‖ + ‖t • (p - x₀)‖ := norm_add_le _ _
      _ = (1 - t) * ‖x - x₀‖ + t * ‖p - x₀‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg h1t, abs_of_nonneg h2t]
      _ ≤ (1 - t) * r + t * r := by
            have ha := mul_le_mul_of_nonneg_left hxr h1t
            have hb := mul_le_mul_of_nonneg_left hpr h2t
            linarith
      _ = r := by ring
  have hseg_ball : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • v ∈ Metric.ball x₀ r' := by
    intro t ht
    have h1 := hseg t ht
    rw [Metric.mem_closedBall] at h1
    exact Metric.mem_ball.mpr (lt_of_le_of_lt h1 hrr)
  have hmemB : ∀ t ∈ Set.Icc (0:ℝ) 1, t ∈ B := by
    intro t ht
    have hts : g t ∈ s := by
      rw [hg_apply t, hs]
      exact hseg_ball t ht
    rw [hB]; exact hts
  have hFc : ContDiffOn ℝ 3 (fun z : ℂ => f (x + z)) s := by
    have hinner : ContDiffOn ℝ 3 (fun z : ℂ => x + z) s := by
      have hcd : ContDiff ℝ 3 (fun z : ℂ => x + z) := contDiff_const.add contDiff_id
      exact hcd.contDiffOn
    have hmap : MapsTo (fun z : ℂ => x + z) s (Metric.ball x₀ r') := fun z hz => by
      rw [hs] at hz; exact hz
    have := hf.comp hinner hmap
    simpa [Function.comp_def] using this
  have hφ_contAt : ∀ t ∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ 3 φ t := by
    intro t ht
    have hmem : x + g t ∈ Metric.ball x₀ r' := by
      rw [hg_apply t]; exact hseg_ball t ht
    have hfat : ContDiffAt ℝ 3 f (x + g t) := hf.contDiffAt (Metric.isOpen_ball.mem_nhds hmem)
    have hlin : ContDiffAt ℝ 3 (fun u : ℝ => x + g u) t := by
      have hcd : ContDiff ℝ 3 (fun u : ℝ => x + g u) := contDiff_const.add g.contDiff
      exact hcd.contDiffAt
    have := hfat.comp t hlin
    simpa [hφ, Function.comp_def] using this
  have hFc_bd : ∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖iteratedFDerivWithin ℝ 3 (fun z : ℂ => f (x + z)) s (g t)‖ ≤ C := by
    intro t ht
    have hmem : x + g t ∈ Metric.ball x₀ r' := by
      rw [hg_apply t]; exact hseg_ball t ht
    rw [iteratedFDerivWithin_comp_add_left 3 x (g t)]
    have hvadd : x +ᵥ s = Metric.ball x₀ r' := by
      rw [hs]
      ext y
      constructor
      · rintro ⟨w, hw, rfl⟩; simpa using hw
      · intro hy; exact ⟨y - x, by simpa using hy, by simp⟩
    rw [hvadd]
    have h1 : iteratedFDerivWithin ℝ 3 f (Metric.ball x₀ r') (x + g t)
        = iteratedFDeriv ℝ 3 f (x + g t) :=
      (iteratedFDerivWithin_of_isOpen 3 Metric.isOpen_ball) hmem
    rw [h1, hg_apply t]
    exact h3 (x + t • v) (hseg t ht)
  have hcomp : ∀ t ∈ Set.Icc (0:ℝ) 1, iteratedFDerivWithin ℝ 3 φ B t =
      (iteratedFDerivWithin ℝ 3 (fun z : ℂ => f (x + z)) s (g t)).compContinuousLinearMap
        (fun _ : Fin 3 => g) := by
    intro t ht
    have hts : g t ∈ s := by
      have := hmemB t ht; rw [hB] at this; exact this
    have h := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ) (s := s)
      (n := (3 : WithTop ℕ∞)) g hFc hs_open.uniqueDiffOn hB_open.uniqueDiffOn (x := t) hts
      (i := 3) le_rfl
    simpa [hφ, hB, Function.comp_def] using h
  have hlin0 : HasDerivAt (fun t : ℝ => x + g t) v 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).smul_const v
    have h2 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := h1.const_add x
    have he : (fun t : ℝ => x + t • v) = (fun t : ℝ => x + g t) := by
      funext t; rw [hg_apply t]
    rwa [he] at h2
  have hlin1 : HasDerivAt (fun t : ℝ => x + g t) v 1 := by
    have h1 : HasDerivAt (fun t : ℝ => t • v) v 1 := by
      simpa using (hasDerivAt_id (1:ℝ)).smul_const v
    have h2 : HasDerivAt (fun t : ℝ => x + t • v) v 1 := h1.const_add x
    have he : (fun t : ℝ => x + t • v) = (fun t : ℝ => x + g t) := by
      funext t; rw [hg_apply t]
    rwa [he] at h2
  have hmem0 : x + g (0:ℝ) ∈ Metric.ball x₀ r' := by
    rw [hg_apply]; simpa using hseg_ball 0 (by norm_num)
  have hmem1 : x + g (1:ℝ) ∈ Metric.ball x₀ r' := by
    rw [hg_apply]; simpa using hseg_ball 1 (by norm_num)
  have hcp1 : x + g (1:ℝ) = p := by
    rw [hg_apply, one_smul, hv]; ring
  have hderiv0 : derivWithin φ (Set.Icc (0:ℝ) 1) 0 = 0 := by
    have hd : DifferentiableAt ℝ f (x + g 0) :=
      (hf.contDiffAt (Metric.isOpen_ball.mem_nhds hmem0)).differentiableAt (by norm_num)
    have h : HasDerivAt φ ((fderiv ℝ f (x + g 0)) v) 0 := by
      have := hd.hasFDerivAt.comp_hasDerivAt 0 hlin0
      simpa [hφ, Function.comp_def] using this
    have hdd := h.hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc zero_lt_one).uniqueDiffWithinAt (by norm_num : (0:ℝ) ∈ Set.Icc 0 1))
    rw [hdd, hg_apply, zero_smul, add_zero, hxc]
    simp
  have hderiv1 : derivWithin φ (Set.Icc (0:ℝ) 1) 1 = 0 := by
    have hd : DifferentiableAt ℝ f (x + g 1) :=
      (hf.contDiffAt (Metric.isOpen_ball.mem_nhds hmem1)).differentiableAt (by norm_num)
    have h : HasDerivAt φ ((fderiv ℝ f (x + g 1)) v) 1 := by
      have := hd.hasFDerivAt.comp_hasDerivAt 1 hlin1
      simpa [hφ, Function.comp_def] using this
    have hdd := h.hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc zero_lt_one).uniqueDiffWithinAt (by norm_num : (1:ℝ) ∈ Set.Icc 0 1))
    rw [hdd, hcp1, hpc]
    simp
  have hφ1 : φ 1 = f p := by simp only [hφ, hcp1]
  have hφ0 : φ 0 = f x := by simp only [hφ, hg_apply, zero_smul, add_zero]
  have hbd : ∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖iteratedDerivWithin 3 φ (Set.Icc (0:ℝ) 1) t‖ ≤ C * ‖v‖ ^ 3 := by
    intro t ht
    have htB : t ∈ B := hmemB t ht
    have hcont := hφ_contAt t ht
    have hconv : iteratedDerivWithin 3 φ (Set.Icc (0:ℝ) 1) t = iteratedDerivWithin 3 φ B t := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (n := 3) (uniqueDiffOn_Icc zero_lt_one) hcont ht,
          iteratedDerivWithin_eq_iteratedDeriv (n := 3) hB_open.uniqueDiffOn hcont htB]
    rw [hconv, iteratedDerivWithin_eq_iteratedFDerivWithin, hcomp t ht]
    have hgle : ‖g‖ ≤ ‖v‖ :=
      ContinuousLinearMap.opNorm_le_bound g (norm_nonneg v) fun t => by
        rw [hg_apply, norm_smul, mul_comm]
    have hcmp : ‖(iteratedFDerivWithin ℝ 3 (fun z : ℂ => f (x + z)) s (g t)).compContinuousLinearMap
          (fun _ : Fin 3 => g)‖ ≤ C * ‖v‖ ^ 3 := by
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul (hFc_bd t ht) (pow_le_pow_left₀ (norm_nonneg g) hgle 3) (by positivity) hC0
    calc ‖(iteratedFDerivWithin ℝ 3 (fun z : ℂ => f (x + z)) s (g t)).compContinuousLinearMap
            (fun _ : Fin 3 => g) (fun _ : Fin 3 => (1:ℝ))‖
        ≤ ‖(iteratedFDerivWithin ℝ 3 (fun z : ℂ => f (x + z)) s (g t)).compContinuousLinearMap
            (fun _ : Fin 3 => g)‖ * ∏ i : Fin 3, ‖(fun _ : Fin 3 => (1:ℝ)) i‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖(iteratedFDerivWithin ℝ 3 (fun z : ℂ => f (x + z)) s (g t)).compContinuousLinearMap
            (fun _ : Fin 3 => g)‖ := by simp
      _ ≤ C * ‖v‖ ^ 3 := hcmp
  have hφcd : ContDiffOn ℝ 3 φ (Set.Icc (0:ℝ) 1) := by
    have hinner : ContDiffOn ℝ 3 (fun t : ℝ => x + g t) (Set.Icc (0:ℝ) 1) := by
      have hcd : ContDiff ℝ 3 (fun t : ℝ => x + g t) := contDiff_const.add g.contDiff
      exact hcd.contDiffOn
    have hmap : MapsTo (fun t : ℝ => x + g t) (Set.Icc (0:ℝ) 1) (Metric.ball x₀ r') :=
      fun t ht => by
        show x + g t ∈ Metric.ball x₀ r'
        rw [hg_apply t]
        exact hseg_ball t ht
    have := hf.comp hinner hmap
    simpa [hφ, Function.comp_def] using this
  have hmain : |φ 1 - φ 0| ≤ C * ‖v‖ ^ 3 :=
    cubic_one_dim hφcd hbd hderiv0 hderiv1
  calc |f p - f x| = |φ 1 - φ 0| := by rw [hφ1, hφ0]
    _ ≤ C * ‖v‖ ^ 3 := hmain
    _ = C * ‖p - x‖ ^ 3 := by rw [hv]
    _ ≤ max C 0 * ‖p - x‖ ^ 3 :=
          mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity)

end Work.SimplyConnected.ABS.green_reduction
