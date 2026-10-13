import Mathlib
import Submission.Work.WilE2.SardDefs

/-!
# Flatness of order `n` implies a Peano-type bound at `flatSet f n`

We prove that at a point `x` where all iterated derivatives of `f` of orders `1, …, n` vanish
(that is, `x ∈ flatSet f n`), the function `f` satisfies

`‖f y - f x‖ ≤ ε * ‖y - x‖ ^ n`

for all `y` close enough to `x`.

The mathematical content is Taylor's formula with integral remainder at order `n - 1` (the
derivatives of orders `1, …, n-1` at `x` vanish, so the Taylor polynomial collapses to the
constant `f x`), together with the continuity of the `n`-th iterated derivative.  The case
`n = 0` is just continuity of `f`.
-/

namespace Work.WilE2

open MeasureTheory Filter

set_option autoImplicit false

set_option maxHeartbeats 1000000

/-- **Taylor (integral remainder) estimate for a function flat to order `k` at `x`.**

If `f` is `C^{k+1}`, its iterated derivatives of orders `1, …, k` vanish at `x`, and the
`(k+1)`-st iterated derivative is bounded by `C` on the segment `[x, y]`, then

`‖f y - f x‖ ≤ C * ‖y - x‖ ^ (k+1) / (k+1)!`.

This is `flatRolleEstimate` without the (unused) flatness hypothesis at the right endpoint. -/
theorem flatTaylorEstimate {n k : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ ((k+1 : ℕ) : WithTop ℕ∞) f) (C : ℝ) (x y : Fin n → ℝ)
    (hx : ∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j f x = 0)
    (hC : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (k+1) f (x + t • (y - x))‖ ≤ C) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ ^ (k+1) / (Nat.factorial (k+1) : ℝ) := by
  -- Taylor's formula at `x` with increment `y - x` is valid on the segment.
  have hcont : ∀ t ∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ ((k : WithTop ℕ∞) + 1) f (x + t • (y - x)) :=
    fun t _ => by simpa using hf.contDiffAt
  have htaylor :=
    map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := x) (y := y - x) (n := k) hcont
  -- All the Taylor terms of order `1, …, k` vanish, so the Taylor sum is just `f x`.
  have hsum : (∑ i ∈ Finset.range (k+1),
      ((i.factorial : ℝ))⁻¹ • (iteratedFDeriv ℝ i f x) (fun _ => y - x)) = f x := by
    rw [Finset.sum_eq_single 0]
    · simp [iteratedFDeriv_zero_apply]
    · intro b hb hne
      have h1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hne
      have h2 : b ≤ k := by rw [Finset.mem_range] at hb; omega
      rw [hx b h1 h2]; simp
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h0
  set I : ℝ := ∫ t in (0:ℝ)..1,
    (1-t)^k • (iteratedFDeriv ℝ (k+1) f (x + t • (y-x))) (fun _ => y - x) with hIdef
  have hfy : f y = f x + ((k.factorial : ℝ))⁻¹ • I := by
    rw [hsum, add_sub_cancel] at htaylor
    exact htaylor
  -- Bound on the remainder integral.
  have hIbound : ‖I‖ ≤ C * ‖y - x‖^(k+1) / ((k+1 : ℕ) : ℝ) := by
    have hpt : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc (0:ℝ) 1 →
        ‖(1-t)^k • (iteratedFDeriv ℝ (k+1) f (x + t • (y-x))) (fun _ => y - x)‖
          ≤ (1-t)^k * (C * ‖y - x‖^(k+1)) := by
      refine Eventually.of_forall fun t ht => ?_
      have htIcc : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
      have h1t : 0 ≤ 1 - t := by linarith [ht.2]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h1t k)]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h1t k)
      calc ‖(iteratedFDeriv ℝ (k+1) f (x + t • (y-x))) (fun _ => y - x)‖
          ≤ ‖iteratedFDeriv ℝ (k+1) f (x + t • (y-x))‖ * ‖y - x‖ ^ (k+1) := by
            refine ContinuousMultilinearMap.le_opNorm_mul_pow_of_le _ ?_
            simp
        _ ≤ C * ‖y - x‖ ^ (k+1) :=
            mul_le_mul_of_nonneg_right (hC t htIcc) (by positivity)
    have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := (0:ℝ)) (b := 1)
      (f := fun t => (1-t)^k • (iteratedFDeriv ℝ (k+1) f (x + t • (y-x))) (fun _ => y - x))
      (g := fun t => (1-t)^k * (C * ‖y-x‖^(k+1))) (by norm_num) hpt
      ((by fun_prop : Continuous fun t : ℝ => (1-t)^k * (C * ‖y-x‖^(k+1))).intervalIntegrable 0 1)
    rw [← hIdef] at hle
    have hconst : (∫ t in (0:ℝ)..1, (1-t)^k * (C * ‖y - x‖^(k+1)))
        = (C * ‖y - x‖^(k+1)) * (∫ t in (0:ℝ)..1, (1-t)^k) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun t _ => mul_comm _ _
    have hpow : (∫ t in (0:ℝ)..1, (1-t)^k) = (((k+1 : ℕ)) : ℝ)⁻¹ := by
      rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => u^k) 1, integral_pow]
      simp
    calc ‖I‖ ≤ ∫ t in (0:ℝ)..1, (1-t)^k * (C * ‖y - x‖^(k+1)) := hle
      _ = (C * ‖y - x‖^(k+1)) * (∫ t in (0:ℝ)..1, (1-t)^k) := hconst
      _ = C * ‖y - x‖^(k+1) / ((k+1 : ℕ) : ℝ) := by rw [hpow, div_eq_mul_inv]
  -- Assemble.
  have hdiff : f y - f x = ((k.factorial : ℝ))⁻¹ • I := by rw [hfy]; abel
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ((k.factorial : ℝ))⁻¹ * ‖I‖
      ≤ ((k.factorial : ℝ))⁻¹ * (C * ‖y - x‖^(k+1) / ((k+1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hIbound (by positivity)
    _ = C * ‖y - x‖^(k+1) / (Nat.factorial (k+1) : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; field_simp

theorem flatSet_top_peano {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ n f) :
    ∀ x ∈ Work.WilE2.flatSet f n, ∀ ε > 0, ∃ ρ > 0, ∀ y, ‖y - x‖ ≤ ρ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ n := by
  intro x hx ε hε
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- `n = 0`: the claim is just continuity of `f` at `x`.
    subst hn0
    have hc : Continuous f := contDiff_zero.mp hf
    have hcont : ContinuousAt f x := hc.continuousAt
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδpos, hδ⟩ := hcont ε hε
    refine ⟨δ/2, by linarith, fun y hy => ?_⟩
    have hlt : dist y x < δ := by
      rw [dist_eq_norm]
      exact lt_of_le_of_lt hy (by linarith)
    have h := hδ hlt
    rw [dist_eq_norm] at h
    simpa using le_of_lt h
  · -- `n ≥ 1`: Taylor's formula at order `n - 1` plus continuity of the `n`-th derivative.
    have hflat : ∀ j, 1 ≤ j → j ≤ n - 1 → iteratedFDeriv ℝ j f x = 0 :=
      fun j h1 h2 => hx j h1 (by omega)
    have hDx : iteratedFDeriv ℝ n f x = 0 := hx n hn le_rfl
    have hcontD : ContinuousAt (fun z : Fin n → ℝ => iteratedFDeriv ℝ n f z) x :=
      hf.continuous_iteratedFDeriv'.continuousAt
    rw [Metric.continuousAt_iff] at hcontD
    obtain ⟨δ, hδpos, hδ⟩ := hcontD (ε * (Nat.factorial n : ℝ)) (by positivity)
    refine ⟨δ/2, by linarith, fun y hy => ?_⟩
    have hyδ : ‖y - x‖ < δ := lt_of_le_of_lt hy (by linarith)
    -- Bound on the `n`-th derivative along the segment `[x, y]`.
    have hC : ∀ t ∈ Set.Icc (0:ℝ) 1,
        ‖iteratedFDeriv ℝ n f (x + t • (y - x))‖ ≤ ε * (Nat.factorial n : ℝ) := by
      intro t ht
      have hz : dist (x + t • (y - x)) x < δ := by
        rw [dist_eq_norm]
        have hsub : x + t • (y - x) - x = t • (y - x) := by abel
        rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        calc t * ‖y - x‖ ≤ 1 * ‖y - x‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
          _ = ‖y - x‖ := one_mul _
          _ < δ := hyδ
      have h1 : ‖iteratedFDeriv ℝ n f (x + t • (y - x))‖ < ε * (Nat.factorial n : ℝ) := by
        simpa [dist_eq_norm, hDx] using hδ hz
      exact le_of_lt h1
    have hf' : ContDiff ℝ (((n - 1) + 1 : ℕ) : WithTop ℕ∞) f := by
      rw [Nat.sub_add_cancel hn]; exact hf
    have hC' : ∀ t ∈ Set.Icc (0:ℝ) 1,
        ‖iteratedFDeriv ℝ ((n - 1) + 1) f (x + t • (y - x))‖ ≤ ε * (Nat.factorial n : ℝ) := by
      intro t ht
      rw [Nat.sub_add_cancel hn]
      exact hC t ht
    have hT := flatTaylorEstimate (n := n) (k := n - 1) f hf' (ε * (Nat.factorial n : ℝ)) x y
      hflat hC'
    rw [Nat.sub_add_cancel hn] at hT
    have hF : (Nat.factorial n : ℝ) ≠ 0 := by positivity
    refine le_trans hT (le_of_eq ?_)
    rw [show (ε * (Nat.factorial n : ℝ)) * ‖y - x‖ ^ n / (Nat.factorial n : ℝ)
        = ε * ‖y - x‖ ^ n by
      rw [mul_comm ε, mul_assoc, mul_div_cancel_left₀ _ hF]]

end Work.WilE2
