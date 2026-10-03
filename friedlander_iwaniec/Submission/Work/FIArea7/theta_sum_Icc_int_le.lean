import Mathlib

namespace Work.FIArea7

/-- Pairing identity over a symmetric integer interval:
the sum over `ℓ ∈ [-L, L]` equals the centre term plus the sum over `k = 1, …, L`
of the pair `F k + F (-k)`. -/
private lemma int_Icc_even_sum (F : ℤ → ℝ) (L : ℕ) :
    ∑ ℓ ∈ Finset.Icc (-(L:ℤ)) (L:ℤ), F ℓ
      = F 0 + ∑ k ∈ Finset.range L, (F ((k:ℤ)+1) + F (-((k:ℤ)+1))) := by
  induction L with
  | zero => simp
  | succ n ih =>
    have hcast : ((n+1 : ℕ) : ℤ) = (n:ℤ) + 1 := by push_cast; ring
    rw [hcast, Finset.Icc_succ_succ]
    have hdisj : Disjoint (Finset.Icc (-(n:ℤ)) (n:ℤ)) ({(-((n:ℤ)+1)), ((n:ℤ)+1)} : Finset ℤ) := by
      rw [Finset.disjoint_left]
      intro x hx hx2
      simp only [Finset.mem_Icc] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
      rcases hx2 with h | h <;> omega
    rw [Finset.sum_union hdisj]
    rw [Finset.sum_pair]
    · rw [ih, Finset.sum_range_succ]
      ring
    · omega

/-- The one-sided sum `∑_{k=1}^{L} θ/(1+(θk)²)` is at most `π/2`, uniformly in `L`. -/
private lemma sum_range_le_pi_half (θ : ℝ) (hθ : 0 < θ) (L : ℕ) :
    ∑ k ∈ Finset.range L, θ/(1+(θ*((k:ℝ)+1))^2) ≤ Real.pi/2 := by
  have hanti : AntitoneOn (fun x : ℝ => θ/(1+(θ*x)^2)) (Set.Icc (0:ℝ) (L:ℝ)) := by
    intro x hx y hy hxy
    have hx0 : 0 ≤ x := hx.1
    have hy0 : 0 ≤ y := hy.1
    have h1 : θ * x ≤ θ * y := by nlinarith [mul_nonneg hx0 hθ.le, mul_nonneg hy0 hθ.le]
    have h2 : (θ*x)^2 ≤ (θ*y)^2 := by
      have := mul_nonneg hθ.le hx0
      nlinarith [sq_nonneg (θ*x), sq_nonneg (θ*y)]
    have h3 : 0 < 1 + (θ*x)^2 := by positivity
    have h4 : 1 + (θ*x)^2 ≤ 1 + (θ*y)^2 := by linarith
    exact div_le_div_of_nonneg_left hθ.le h3 h4
  have h1 := AntitoneOn.sum_le_integral_Ico (a := 0) (b := L)
      (f := fun x : ℝ => θ/(1+(θ*x)^2)) (Nat.zero_le L) (by simpa using hanti)
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] at h1
  have hint : ∫ x in (0:ℝ)..(L:ℝ), θ/(1+(θ*x)^2) = Real.arctan (θ*(L:ℝ)) := by
    have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (L:ℝ),
        HasDerivAt (fun y : ℝ => Real.arctan (θ * y)) (θ / (1 + (θ*x)^2)) x := by
      intro x _
      have hh1 : HasDerivAt (fun y : ℝ => θ * y) θ x := by
        simpa using (hasDerivAt_id x).const_mul θ
      have hh2 : HasDerivAt Real.arctan (1/(1+(θ*x)^2)) (θ*x) := Real.hasDerivAt_arctan (θ*x)
      have hh3 : HasDerivAt (fun y : ℝ => Real.arctan (θ * y))
          (1 / (1 + (θ * x) ^ 2) * θ) x := hh2.comp x hh1
      convert hh3 using 1
      ring
    have hint2 : IntervalIntegrable (fun x : ℝ => θ / (1 + (θ*x)^2))
        MeasureTheory.volume (0:ℝ) (L:ℝ) := by
      apply Continuous.intervalIntegrable
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro x
        positivity
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint2]
    simp [Real.arctan_zero]
  rw [hint] at h1
  have h3 : Real.arctan (θ*(L:ℝ)) < Real.pi/2 := Real.arctan_lt_pi_div_two _
  rw [Finset.range_eq_Ico]
  linarith

theorem theta_sum_Icc_int_le (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (L : ℕ) :
    ∑ ℓ ∈ Finset.Icc (-(L : ℤ)) L, θ / (1 + θ ^ 2 * (ℓ : ℝ) ^ 2) ≤ 1 + Real.pi := by
  have key := sum_range_le_pi_half θ hθ L
  rw [int_Icc_even_sum (fun ℓ : ℤ => θ / (1 + θ^2 * (ℓ:ℝ)^2)) L]
  have hF0 : θ / (1 + θ^2 * ((0:ℤ):ℝ)^2) = θ := by norm_num
  simp only [hF0]
  have hterms : ∀ k : ℕ,
      θ/(1+θ^2*(((k:ℤ)+1 : ℤ):ℝ)^2) + θ/(1+θ^2*(((-((k:ℤ)+1)) : ℤ):ℝ)^2)
      = 2 * (θ/(1+(θ*((k:ℝ)+1))^2)) := by
    intro k
    have h1 : (((k:ℤ)+1 : ℤ) : ℝ) = (k:ℝ)+1 := by push_cast; ring
    have h2 : ((-((k:ℤ)+1) : ℤ) : ℝ) = -((k:ℝ)+1) := by
      have : ((-((k:ℤ)+1) : ℤ) : ℝ) = -(((k:ℤ)+1 : ℤ) : ℝ) := by push_cast; ring
      rw [this, h1]
    rw [h1, h2]
    have hsq : (θ^2 : ℝ) * (-((k:ℝ)+1))^2 = (θ*((k:ℝ)+1))^2 := by ring
    rw [hsq]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterms k)]
  rw [← Finset.mul_sum]
  linarith

end Work.FIArea7
