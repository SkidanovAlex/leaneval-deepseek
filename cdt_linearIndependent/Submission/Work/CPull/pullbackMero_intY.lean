import Mathlib
import Submission.Work.CPull.defs

/-!
# Area CPull — meromorphic pullback of the formal integral `∫₀ f`

`PullbackMero f Ψ` says: there is a polynomial `P` with `P 0 ≠ 0` and a function `N` holomorphic
on the unit disc such that `Σ aₙ Ψ(z)ⁿ = N z / P z` for `z` near `0`.

Here we prove the "integration" step of the CPull development: if `Σ cₙ Ψ(z)ⁿ = N z` near `0`
(where `c` are the coefficients of `f`), then the same holds for the formal integral of `f`,
`intY f` (coefficients `c (n-1)/n`), with `P = 1`.

The mathematical content is:

* termwise differentiation of the series `η(z) = Σ (a(n-1)/n) Ψ(z)ⁿ` (Weierstrass, via
  `hasDerivAt_tsum_of_isPreconnected`) gives `η' = (deriv Ψ) · N` on a small disc;
* `η` therefore agrees near `0` with `C + H`, where `C` is the sum of the `η`-series at `0` and
  `H` is any primitive of `(deriv Ψ) · N` on the unit disc (which exists by Morera,
  `DifferentiableOn.isExactOn_ball`) — and `C + H` is holomorphic on the whole disc.
-/

namespace Work.CPull

open PowerSeries Metric Filter
open scoped Topology

/-- The coefficients of the formal integral `intY f`: `0` at `0`, `(coeff (n-1) f)/n` at `n ≥ 1`. -/
lemma coeff_intY (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (Submission.CDTPlan.intY f)
      = if n = 0 then 0 else PowerSeries.coeff (n - 1) f / (n : ℚ) := by
  rw [Submission.CDTPlan.intY, PowerSeries.coeff_mk]

/-- Shifting the coefficients to `a (n-1)/n` preserves summability of the coefficient series at a
fixed point `w` (this is the coefficient sequence of the formal integral `intY`). -/
theorem summable_intY_shift {a : ℕ → ℂ} (w : ℂ) (ha : Summable fun n : ℕ => a n * w ^ n) :
    Summable fun n : ℕ => (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * w ^ n := by
  have hmain : Summable fun n : ℕ => (if n = 0 then 0 else a (n - 1) * w ^ (n - 1)) := by
    refine (summable_nat_add_iff 1).mp ?_
    simpa using ha
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => ‖w‖ * ‖(if n = 0 then 0 else a (n - 1) * w ^ (n - 1))‖) ?_ ?_
  · exact hmain.norm.mul_left ‖w‖
  · intro n
    rcases n with _ | m
    · simp
    · simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero m)]
      have hdecomp : a m / (((m : ℕ) + 1 : ℕ) : ℂ) * w ^ (m + 1)
          = (a m * w ^ m) * (w / (((m : ℕ) + 1 : ℕ) : ℂ)) := by
        rw [pow_succ]; ring
      rw [hdecomp, norm_mul, norm_div]
      have hcast : ‖(((m : ℕ) + 1 : ℕ) : ℂ)‖ = ((m : ℝ) + 1) := by
        rw [Complex.norm_natCast]; push_cast; ring
      rw [hcast]
      have hle : ‖w‖ / ((m : ℝ) + 1) ≤ ‖w‖ := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg w, Nat.cast_nonneg (α := ℝ) m]
      calc ‖a m * w ^ m‖ * (‖w‖ / ((m : ℝ) + 1))
          ≤ ‖a m * w ^ m‖ * ‖w‖ := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
        _ = ‖w‖ * ‖a m * w ^ m‖ := by ring

/-- On a closed disc strictly inside the unit disc, a holomorphic `Ψ` has `‖Ψ‖` peaking at an
interior point `z₀` of the disc, and `‖deriv Ψ‖` is bounded by a nonnegative constant `L`. -/
theorem exists_bounds_closedBall {Ψ : ℂ → ℂ} (hΨ : DifferentiableOn ℂ Ψ (Metric.ball 0 1))
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ z₀ ∈ Metric.closedBall (0 : ℂ) α, (∀ z ∈ Metric.closedBall (0 : ℂ) α, ‖Ψ z‖ ≤ ‖Ψ z₀‖) ∧
      ∃ L : ℝ, 0 ≤ L ∧ ∀ z ∈ Metric.closedBall (0 : ℂ) α, ‖deriv Ψ z‖ ≤ L := by
  have hsub : Metric.closedBall (0 : ℂ) α ⊆ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hne : (Metric.closedBall (0 : ℂ) α).Nonempty :=
    ⟨0, by rw [Metric.mem_closedBall, dist_zero_right]; simpa using hα.le⟩
  obtain ⟨z₀, hz₀, hz₀max⟩ := (isCompact_closedBall (0 : ℂ) α).exists_isMaxOn hne
    ((hΨ.mono hsub).continuousOn.norm)
  refine ⟨z₀, hz₀, fun z hz => hz₀max hz, ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) α).exists_bound_of_continuousOn
    ((hΨ.deriv Metric.isOpen_ball).continuousOn.mono hsub)
  exact ⟨max C 0, le_max_right _ _, fun z hz => le_trans (hC z hz) (le_max_left _ _)⟩

/-- Term-by-term derivative identity: if the `a`-series sums to `x` at `w`, then the series whose
`n`-th term is `(a (n-1)/n) * (n * w^(n-1) * D)` (the term-by-term derivative of the "integrated"
series `Σ (a (n-1)/n) Z^n` at `Z = w`, multiplied by `D`) sums to `D * x`. -/
theorem hasSum_intY_deriv {a : ℕ → ℂ} {w D x : ℂ}
    (h : HasSum (fun k : ℕ => a k * w ^ k) x) :
    HasSum (fun n : ℕ => (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * ((n : ℂ) * w ^ (n - 1) * D))
      (D * x) := by
  have hterm : ∀ n : ℕ,
      (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * ((n : ℂ) * w ^ (n - 1) * D)
        = (if n = 0 then 0 else a (n - 1) * w ^ (n - 1) * D) := by
    intro n
    rcases n with _ | m
    · simp
    · simp only [Nat.succ_ne_zero m, if_false, Nat.add_sub_cancel]
      field_simp
  have hg : HasSum (fun n : ℕ => (if n = 0 then 0 else a (n - 1) * w ^ (n - 1) * D)) (x * D) := by
    have hshift : HasSum (fun n : ℕ => (if n + 1 = 0 then 0
        else a (n + 1 - 1) * w ^ (n + 1 - 1) * D)) (x * D) := by
      simpa only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel] using h.mul_right D
    have h1 := (hasSum_nat_add_iff 1
      (f := fun n : ℕ => (if n = 0 then 0 else a (n - 1) * w ^ (n - 1) * D))
      (g := x * D)).mp hshift
    simpa [Finset.sum_range_one] using h1
  rw [mul_comm D x]
  simpa only [hterm] using hg

/-- **Differentiating the germ of the pullback of a formal integral.**  Let `a : ℕ → ℂ`,
`Ψ` holomorphic on the unit disc, and suppose that on the disc of radius `α` the power series
`Σ a k Z^k` sums to `N z` at `Z = Ψ z`.  Assume the uniform bounds `‖Ψ‖ ≤ M`, `‖deriv Ψ‖ ≤ L`
on the closed disc of radius `α` and the domination hypothesis making `Σ ‖a (n-1)‖ M^(n-1) L`
summable, together with summability of the "integrated" series at `0`.  Then the function
`w ↦ Σ' n, (a (n-1)/n) Ψ(w)^n` is complex differentiable on the disc of radius `α`, with
derivative `deriv Ψ z * N z`. -/
theorem germ_hasDerivAt {a : ℕ → ℂ} {Ψ N : ℂ → ℂ} {α M L : ℝ}
    (hΨ : DifferentiableOn ℂ Ψ (Metric.ball 0 1)) (hα : 0 < α) (hα1 : α < 1)
    (hM0 : 0 ≤ M) (hL0 : 0 ≤ L)
    (hMb : ∀ z ∈ Metric.closedBall (0 : ℂ) α, ‖Ψ z‖ ≤ M)
    (hLb : ∀ z ∈ Metric.closedBall (0 : ℂ) α, ‖deriv Ψ z‖ ≤ L)
    (hu : Summable fun n : ℕ => (if n = 0 then 0 else ‖a (n - 1)‖ * M ^ (n - 1)) * L)
    (hN : ∀ z ∈ Metric.ball (0 : ℂ) α, HasSum (fun k : ℕ => a k * Ψ z ^ k) (N z))
    (h0 : Summable fun n : ℕ => (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ 0 ^ n) :
    ∀ z ∈ Metric.ball (0 : ℂ) α,
      HasDerivAt (fun w => ∑' n : ℕ, (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ w ^ n)
        (deriv Ψ z * N z) z := by
  have _hL : 0 ≤ L := hL0
  intro z hz
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) α := by
    rw [Metric.mem_ball, dist_zero_right]; simpa using hα
  have hsub1 : Metric.ball (0 : ℂ) α ⊆ Metric.ball (0 : ℂ) 1 := Metric.ball_subset_ball hα1.le
  have hterm_deriv : ∀ n w, w ∈ Metric.ball (0 : ℂ) 1 →
      HasDerivAt (fun u => (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ u ^ n)
        ((if n = 0 then 0 else a (n - 1) / (n : ℂ)) *
          ((n : ℂ) * Ψ w ^ (n - 1) * deriv Ψ w)) w := by
    intro n w hw
    have hwΨ : HasDerivAt Ψ (deriv Ψ w) w :=
      (hΨ.differentiableAt (Metric.isOpen_ball.mem_nhds hw)).hasDerivAt
    exact (hwΨ.pow n).const_mul _
  have hbound : ∀ n w, w ∈ Metric.ball (0 : ℂ) α →
      ‖(if n = 0 then 0 else a (n - 1) / (n : ℂ)) * ((n : ℂ) * Ψ w ^ (n - 1) * deriv Ψ w)‖
        ≤ (if n = 0 then 0 else ‖a (n - 1)‖ * M ^ (n - 1)) * L := by
    intro n w hw
    have hw' : w ∈ Metric.closedBall (0 : ℂ) α := Metric.ball_subset_closedBall hw
    rcases n with _ | m
    · simp
    · simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero m)]
      have hne : (((m : ℕ) + 1 : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero m
      have hsimp : a m / (((m : ℕ) + 1 : ℕ) : ℂ) * ((((m : ℕ) + 1 : ℕ) : ℂ) * Ψ w ^ m * deriv Ψ w)
          = a m * Ψ w ^ m * deriv Ψ w := by
        field_simp
      rw [hsimp, norm_mul, norm_mul, norm_pow]
      have hΨb : ‖Ψ w‖ ≤ M := hMb w hw'
      have hdb : ‖deriv Ψ w‖ ≤ L := hLb w hw'
      have hpow : ‖Ψ w‖ ^ m ≤ M ^ m := pow_le_pow_left₀ (norm_nonneg _) hΨb m
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)) hdb (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (pow_nonneg hM0 m))
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ => (if n = 0 then 0 else ‖a (n - 1)‖ * M ^ (n - 1)) * L)
    hu Metric.isOpen_ball (convex_ball (0 : ℂ) α).isPreconnected
    (fun n w hw => hterm_deriv n w (hsub1 hw))
    (fun n w hw => hbound n w hw)
    h0mem h0 hz
  have hval : (∑' n : ℕ, (if n = 0 then 0 else a (n - 1) / (n : ℂ)) *
      ((n : ℂ) * Ψ z ^ (n - 1) * deriv Ψ z)) = deriv Ψ z * N z := by
    rw [(hasSum_intY_deriv (a := a) (w := Ψ z) (D := deriv Ψ z) (x := N z) (hN z hz)).tsum_eq]
  simpa only [hval] using hmain

/-- **Meromorphic pullback of the formal integral.**  If the germ at `0` of the pullback of `f`
along `Ψ` is the holomorphic function `N`, then the germ of the pullback of `intY f` extends to a
function holomorphic on the whole unit disc (`P = 1`). -/
theorem pullbackMero_intY {f : PowerSeries ℚ} {Ψ N : ℂ → ℂ}
    (hΨ : DifferentiableOn ℂ Ψ (Metric.ball 0 1))
    (hN : DifferentiableOn ℂ N (Metric.ball 0 1))
    (hgerm : ∀ᶠ z in nhds (0:ℂ),
      HasSum (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * Ψ z ^ n) (N z)) :
    Submission.CDTPlan.PullbackMero (Submission.CDTPlan.intY f) Ψ := by
  classical
  set a : ℕ → ℂ := fun n => ((PowerSeries.coeff n f : ℚ) : ℂ) with ha
  have hcoeff : ∀ n : ℕ, ((PowerSeries.coeff n (Submission.CDTPlan.intY f) : ℚ) : ℂ)
      = (if n = 0 then 0 else a (n - 1) / (n : ℂ)) := by
    intro n
    rw [coeff_intY]
    by_cases hn : n = 0
    · simp [hn]
    · rw [if_neg hn, if_neg hn, Rat.cast_div, ha]
      push_cast
      ring
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hgerm
  set α : ℝ := min δ 1 / 2 with hαdef
  have hαpos : 0 < α := by
    have h1 : 0 < min δ 1 := lt_min hδpos one_pos
    rw [hαdef]; linarith
  have hαδ : α < δ := by
    have h1 : min δ 1 ≤ δ := min_le_left _ _
    rw [hαdef]; linarith
  have hα1 : α < 1 := by
    have h1 : min δ 1 ≤ 1 := min_le_right _ _
    rw [hαdef]; linarith
  obtain ⟨z₀, hz₀mem, hz₀max, L, hL0, hLb⟩ := exists_bounds_closedBall hΨ hαpos hα1
  have hz₀δ : dist z₀ 0 < δ := by
    have h1 : dist z₀ 0 ≤ α := Metric.mem_closedBall.mp hz₀mem
    linarith
  have hsum_z₀ : Summable fun k : ℕ => ‖a k‖ * ‖Ψ z₀‖ ^ k := by
    have hh := hδ hz₀δ
    simpa [a, norm_mul, norm_pow] using hh.summable.norm
  have hshift : Summable fun n : ℕ => (if n = 0 then 0 else ‖a (n - 1)‖ * ‖Ψ z₀‖ ^ (n - 1)) := by
    refine (summable_nat_add_iff 1).mp ?_
    simpa using hsum_z₀
  have hu : Summable fun n : ℕ => (if n = 0 then 0 else ‖a (n - 1)‖ * ‖Ψ z₀‖ ^ (n - 1)) * L :=
    hshift.mul_right L
  have h0 : Summable fun n : ℕ => (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ 0 ^ n := by
    have hh := hδ (show dist (0 : ℂ) 0 < δ by rw [dist_zero_right]; simpa using hδpos)
    exact summable_intY_shift (Ψ 0) hh.summable
  have hbN : ∀ z ∈ Metric.ball (0 : ℂ) α, HasSum (fun k : ℕ => a k * Ψ z ^ k) (N z) := by
    intro z hz
    have h1 : dist z 0 < α := Metric.mem_ball.mp hz
    exact hδ (by linarith)
  have hgerm_deriv := germ_hasDerivAt hΨ hαpos hα1 (norm_nonneg (Ψ z₀)) hL0 hz₀max hLb hu hbN h0
  -- the primitive of `(deriv Ψ) · N`
  have hderivN : DifferentiableOn ℂ (fun z => deriv Ψ z * N z) (Metric.ball 0 1) :=
    (hΨ.deriv Metric.isOpen_ball).mul hN
  obtain ⟨H, hH0, hHderiv⟩ := hderivN.isExactOn_ball.with_val_at 0 0
  set Cc : ℂ := ∑' n : ℕ, (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ 0 ^ n with hCdef
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) α := by
    rw [Metric.mem_ball, dist_zero_right]; simpa using hαpos
  have hsub1 : Metric.ball (0 : ℂ) α ⊆ Metric.ball (0 : ℂ) 1 := Metric.ball_subset_ball hα1.le
  have hconst : ∀ z ∈ Metric.ball (0 : ℂ) α,
      (∑' n : ℕ, (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ z ^ n) = H z + Cc := by
    intro z hz
    have hKderiv : ∀ w ∈ Metric.ball (0 : ℂ) α,
        HasDerivAt ((fun w => ∑' n : ℕ, (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ w ^ n)
          - H) 0 w := by
      intro w hw
      have h1 : HasDerivAt (fun w => ∑' n : ℕ, (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ w ^ n)
          (deriv Ψ w * N w) w := hgerm_deriv w hw
      have h2 : HasDerivAt H (deriv Ψ w * N w) w := hHderiv w (hsub1 hw)
      simpa only [sub_self] using h1.sub h2
    have hdiff : DifferentiableOn ℂ
        ((fun w => ∑' n : ℕ, (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ w ^ n) - H)
        (Metric.ball (0 : ℂ) α) :=
      fun w hw => (hKderiv w hw).differentiableAt.differentiableWithinAt
    have hzero : ∀ w ∈ Metric.ball (0 : ℂ) α,
        deriv ((fun w => ∑' n : ℕ, (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ w ^ n) - H) w = 0 :=
      fun w hw => (hKderiv w hw).deriv
    have hconstK := Metric.isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball (0 : ℂ) α).isPreconnected hdiff hzero h0mem hz
    rw [Pi.sub_apply, hH0, sub_zero, Pi.sub_apply] at hconstK
    have : (∑' n : ℕ, (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ z ^ n) - H z = Cc := by
      rw [hCdef]
      exact hconstK.symm
    linear_combination this
  refine ⟨1, fun z => H z + Cc, by simp, ?_, ?_⟩
  · refine DifferentiableOn.add ?_ (differentiableOn_const Cc)
    exact fun z hz => (hHderiv z hz).differentiableAt.differentiableWithinAt
  · refine Filter.Eventually.mono (Metric.ball_mem_nhds (0 : ℂ) hαpos) ?_
    intro z hz
    have hzsum : Summable fun n : ℕ => (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ z ^ n :=
      summable_intY_shift (Ψ z) (hbN z hz).summable
    have hHasSum : HasSum (fun n : ℕ => (if n = 0 then 0 else a (n - 1) / (n : ℂ)) * Ψ z ^ n)
        (H z + Cc) := by
      have h1 := hzsum.hasSum
      rwa [hconst z hz] at h1
    simpa only [hcoeff, Polynomial.eval_one, div_one] using hHasSum

end Work.CPull
