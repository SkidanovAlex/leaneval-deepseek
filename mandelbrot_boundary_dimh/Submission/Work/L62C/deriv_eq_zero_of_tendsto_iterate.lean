import Mathlib

namespace Work.L62C

open Filter Set
open scoped Topology

/-- **The derivative at the fixed point of a locally uniform limit of iterates is zero.**  If
`F` is holomorphic on the open set `Ω ∋ 0` with `F 0 = 0` and `‖deriv F 0‖ < 1`, and `h` is the
locally uniform limit on `Ω` of the subsequence `F^[φ n]` with `φ` strictly increasing, then
`deriv h 0 = 0`. -/
theorem deriv_eq_zero_of_tendsto_iterate {Ω : Set ℂ} (hΩo : IsOpen Ω) (h0 : (0 : ℂ) ∈ Ω)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F Ω) (hmap : Set.MapsTo F Ω Ω) (hfix : F 0 = 0)
    (hder : ‖deriv F 0‖ < 1) {φ : ℕ → ℕ} (hφ : StrictMono φ) {h : ℂ → ℂ}
    (hlim : TendstoLocallyUniformlyOn (fun n => (F^[φ n])) h atTop Ω) :
    deriv h 0 = 0 := by
  -- The iterates of `F` are holomorphic on `Ω` and differentiable at `0`.
  have hiter : ∀ n : ℕ, DifferentiableOn ℂ (F^[n]) Ω := hF.iterate hmap
  have hF_at : DifferentiableAt ℂ F 0 := hF.differentiableAt (hΩo.mem_nhds h0)
  have hiter_at : ∀ n : ℕ, DifferentiableAt ℂ (F^[n]) 0 := fun n =>
    (hiter n).differentiableAt (hΩo.mem_nhds h0)
  -- All iterates fix `0`.
  have hfixn : ∀ n : ℕ, (F^[n]) 0 = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, hfix]
  -- The multiplier of the `n`-th iterate is the `n`-th power of the multiplier of `F`.
  have hderiv_iter : ∀ n : ℕ, deriv (F^[n]) 0 = (deriv F 0)^n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ']
      rw [deriv_comp (x := 0) (h := F^[n]) (h₂ := F)
        (by rw [hfixn n]; exact hF_at) (hiter_at n)]
      rw [hfixn n, ih, pow_succ']
  -- Weierstrass: the derivatives converge locally uniformly to the derivative of the limit.
  have hderivlim := hlim.deriv (Eventually.of_forall (fun n => hiter (φ n))) hΩo
  have hpt : Tendsto (fun n => deriv ((F^[φ n])) 0) atTop (𝓝 (deriv h 0)) :=
    hderivlim.tendsto_at h0
  have hpt' : Tendsto (fun n => (deriv F 0)^(φ n)) atTop (𝓝 (deriv h 0)) := by
    rw [show (fun n => deriv (F^[φ n]) 0) = fun n => (deriv F 0)^(φ n) from
      funext (fun n => hderiv_iter (φ n))] at hpt
    exact hpt
  -- The multiplier powers tend to `0` because `φ n → ∞` and `‖deriv F 0‖ < 1`.
  have hpow : Tendsto (fun n => (deriv F 0)^(φ n)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hder).comp hφ.tendsto_atTop
  exact tendsto_nhds_unique hpt' hpow

end Work.L62C
