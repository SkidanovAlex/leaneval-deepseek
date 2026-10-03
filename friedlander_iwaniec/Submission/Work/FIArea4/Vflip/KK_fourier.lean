import Mathlib
import Submission.Work.FIArea4.WdyadDefs2

namespace Work.FIArea4.Vflip

open scoped BigOperators

/-- Re-indexing a `tsum` over the multiples of `r ≠ 0`:
`∑'_m [r | m] c * φ(m/r) * z m = c * ∑'_k φ k * z (r*k)`. -/
lemma tsum_dvd_eq (r : ℤ) (hr : r ≠ 0) (c : ℂ) (φ : ℤ → ℂ) (z : ℤ → ℂ) :
    (∑' m : ℤ, (if r ∣ m then c * φ (m / r) * z m else 0))
      = c * ∑' k : ℤ, φ k * z (r * k) := by
  have hg : Function.Injective (fun k : ℤ => r * k) := by
    intro x y h
    have h2 := congrArg (fun t : ℤ => t / r) h
    rwa [Int.mul_ediv_cancel_left x hr, Int.mul_ediv_cancel_left y hr] at h2
  have hsupp : Function.support (fun m : ℤ => (if r ∣ m then c * φ (m / r) * z m else 0))
      ⊆ Set.range (fun k : ℤ => r * k) := by
    intro m hm
    simp only [Function.mem_support, ne_eq] at hm
    by_contra h
    apply hm
    simp only [Set.mem_range, not_exists] at h
    have hnd : ¬ r ∣ m := fun hd => by
      obtain ⟨k, hk⟩ := hd
      exact h k hk.symm
    rw [if_neg hnd]
  rw [← Function.Injective.tsum_eq hg hsupp]
  rw [show (∑' k : ℤ, (if r ∣ r * k then c * φ (r * k / r) * z (r * k) else 0))
        = ∑' k : ℤ, c * φ k * z (r * k) from tsum_congr (fun k => by
            rw [if_pos (dvd_mul_right r k), Int.mul_ediv_cancel_left k hr])]
  rw [show (∑' k : ℤ, c * φ k * z (r * k)) = ∑' k : ℤ, c * (φ k * z (r * k)) from
        tsum_congr (fun k => by ring)]
  rw [tsum_mul_left]

/-- The discrete Fourier duality `K = (1/q) Σ_m c_m e(ma/q)`: the Fourier coefficient sequence
`c_m = Σ_r [r | m] w_r F((m/r)/q)` (a finite sum over `r ∈ (R, 2R]`) transforms back to the
kernel `K = (1/q) Σ_k F(k/q) Σ_r w_r e(rka/q)`.  Both sides are absolutely convergent. -/
lemma tsum_dual_fourier (q : ℕ) (F : ℝ → ℂ) (R : ℕ) (a : ℕ) (w : ℕ → ℂ)
    (hF : Summable fun k : ℤ => F ((k:ℝ)/(q:ℝ))) :
    (∑' k : ℤ, F ((k:ℝ)/(q:ℝ)) * (∑ r ∈ Finset.Ioc R (2*R), w r *
        Complex.exp (2*Real.pi*Complex.I*(r:ℝ)*(k:ℝ)*(a:ℝ)/(q:ℝ))))
      = ∑' m : ℤ, (∑ r ∈ Finset.Ioc R (2*R),
          if (r:ℤ) ∣ m then w r * F (((m / (r:ℤ) : ℤ) : ℝ)/(q:ℝ)) else 0)
        * Complex.exp (2*Real.pi*Complex.I*(m:ℝ)*(a:ℝ)/(q:ℝ)) := by
  set s : Finset ℕ := Finset.Ioc R (2*R) with hs
  set E : ℕ → ℤ → ℂ := fun r k => Complex.exp (2*Real.pi*Complex.I*(r:ℝ)*(k:ℝ)*(a:ℝ)/(q:ℝ)) with hE
  set z : ℤ → ℂ := fun m => Complex.exp (2*Real.pi*Complex.I*(m:ℝ)*(a:ℝ)/(q:ℝ)) with hz
  have norm_E : ∀ r k, ‖E r k‖ = 1 := by
    intro r k
    simp only [E]
    have harg : 2 * Real.pi * Complex.I * (r:ℝ) * (k:ℝ) * (a:ℝ) / (q:ℝ)
        = ((2 * Real.pi * (r:ℝ) * (k:ℝ) * (a:ℝ) / (q:ℝ) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  have norm_z : ∀ m : ℤ, ‖z m‖ = 1 := by
    intro m
    simp only [z]
    have harg : 2 * Real.pi * Complex.I * (m:ℝ) * (a:ℝ) / (q:ℝ)
        = ((2 * Real.pi * (m:ℝ) * (a:ℝ) / (q:ℝ) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  have hFnorm : Summable fun k : ℤ => ‖F ((k:ℝ)/(q:ℝ))‖ := hF.norm
  have hL : (∑' k : ℤ, F ((k:ℝ)/(q:ℝ)) * (∑ r ∈ s, w r * E r k))
      = ∑ r ∈ s, w r * (∑' k : ℤ, F ((k:ℝ)/(q:ℝ)) * E r k) := by
    have h1 : (∑' k : ℤ, F ((k:ℝ)/(q:ℝ)) * (∑ r ∈ s, w r * E r k))
        = ∑' k : ℤ, ∑ r ∈ s, F ((k:ℝ)/(q:ℝ)) * (w r * E r k) := by
      apply tsum_congr; intro k; rw [Finset.mul_sum]
    rw [h1]
    rw [Summable.tsum_finsetSum (f := fun (r : ℕ) (k : ℤ) =>
        F ((k:ℝ)/(q:ℝ)) * (w r * E r k)) ?_]
    · apply Finset.sum_congr rfl; intro r hr
      have h2 : (∑' k : ℤ, F ((k:ℝ)/(q:ℝ)) * (w r * E r k))
          = ∑' k : ℤ, w r * (F ((k:ℝ)/(q:ℝ)) * E r k) := by
        apply tsum_congr; intro k; ring
      rw [h2, tsum_mul_left]
    · intro r hr
      apply Summable.of_norm_bounded (hFnorm.mul_left ‖w r‖)
      intro k
      rw [norm_mul, norm_mul, norm_E r k, mul_one, mul_comm]
  have hR : (∑' m : ℤ, (∑ r ∈ s,
          (if (r:ℤ) ∣ m then w r * F (((m / (r:ℤ) : ℤ) : ℝ)/(q:ℝ)) else 0)) * z m)
      = ∑ r ∈ s, w r * (∑' k : ℤ, F ((k:ℝ)/(q:ℝ)) * E r k) := by
    have h1 : (∑' m : ℤ, (∑ r ∈ s,
          (if (r:ℤ) ∣ m then w r * F (((m / (r:ℤ) : ℤ) : ℝ)/(q:ℝ)) else 0)) * z m)
        = ∑' m : ℤ, ∑ r ∈ s,
          (if (r:ℤ) ∣ m then w r * F (((m / (r:ℤ) : ℤ) : ℝ)/(q:ℝ)) else 0) * z m := by
      apply tsum_congr; intro m; rw [Finset.sum_mul]
    rw [h1]
    rw [Summable.tsum_finsetSum (f := fun (r : ℕ) (m : ℤ) =>
        (if (r:ℤ) ∣ m then w r * F (((m / (r:ℤ) : ℤ) : ℝ)/(q:ℝ)) else 0) * z m) ?_]
    · apply Finset.sum_congr rfl; intro r hr
      have hmem : R < r ∧ r ≤ 2 * R := by
        have : r ∈ Finset.Ioc R (2*R) := by rwa [hs] at hr
        exact Finset.mem_Ioc.mp this
      have hrne : (r:ℤ) ≠ 0 := by
        have h2 : (0:ℤ) < (r:ℤ) := by exact_mod_cast (show 0 < r by omega)
        omega
      have h2 : (∑' m : ℤ, (if (r:ℤ) ∣ m then w r * F (((m / (r:ℤ) : ℤ) : ℝ)/(q:ℝ)) else 0) * z m)
          = ∑' m : ℤ, (if (r:ℤ) ∣ m then
              w r * (fun k : ℤ => F ((k:ℝ)/(q:ℝ))) (m / (r:ℤ)) * z m else 0) := by
        apply tsum_congr; intro m; by_cases h : (r:ℤ) ∣ m <;> simp [h]
      rw [h2, tsum_dvd_eq (r:ℤ) hrne (w r) (fun k => F ((k:ℝ)/(q:ℝ))) z]
      congr 1
      apply tsum_congr; intro k
      show F ((k:ℝ)/(q:ℝ)) * z ((r:ℤ) * k) = F ((k:ℝ)/(q:ℝ)) * E r k
      rw [show z ((r:ℤ) * k) = E r k from by simp only [z, E]; congr 1; push_cast; ring]
    · intro r hr
      have hmem : R < r ∧ r ≤ 2 * R := by
        have : r ∈ Finset.Ioc R (2*R) := by rwa [hs] at hr
        exact Finset.mem_Ioc.mp this
      have hrne : (r:ℤ) ≠ 0 := by
        have h2 : (0:ℤ) < (r:ℤ) := by exact_mod_cast (show 0 < r by omega)
        omega
      have hg_inj : Function.Injective (fun k : ℤ => (r:ℤ) * k) := by
        intro x y h
        have h3 := congrArg (fun t : ℤ => t / (r:ℤ)) h
        rwa [Int.mul_ediv_cancel_left x hrne, Int.mul_ediv_cancel_left y hrne] at h3
      have hsupp : ∀ m ∉ Set.range (fun k : ℤ => (r:ℤ) * k),
          (if (r:ℤ) ∣ m then w r * F (((m / (r:ℤ) : ℤ) : ℝ)/(q:ℝ)) else 0) * z m = 0 := by
        intro m hm
        simp only [Set.mem_range, not_exists] at hm
        have hnd : ¬ (r:ℤ) ∣ m := fun hd => by
          obtain ⟨k, hk⟩ := hd; exact hm k hk.symm
        rw [if_neg hnd, zero_mul]
      refine (Function.Injective.summable_iff hg_inj hsupp).mp ?_
      show Summable (fun k : ℤ => (if (r:ℤ) ∣ (r:ℤ)*k then
          w r * F ((((r:ℤ)*k / (r:ℤ) : ℤ) : ℝ)/(q:ℝ)) else 0) * z ((r:ℤ)*k))
      rw [show (fun k : ℤ => (if (r:ℤ) ∣ (r:ℤ)*k then
              w r * F ((((r:ℤ)*k / (r:ℤ) : ℤ) : ℝ)/(q:ℝ)) else 0) * z ((r:ℤ)*k))
            = fun k : ℤ => w r * F ((k:ℝ)/(q:ℝ)) * z ((r:ℤ)*k) from by
        funext k
        rw [if_pos (dvd_mul_right (r:ℤ) k), Int.mul_ediv_cancel_left k hrne]]
      apply Summable.of_norm_bounded (hFnorm.mul_left ‖w r‖)
      intro k
      rw [norm_mul, norm_mul, norm_z ((r:ℤ) * k), mul_one, mul_comm]
  rw [hL, hR]

theorem KK_fourier (F : ℝ → ℂ) (R d1 d2 : ℕ) (a : ℕ) (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (hF : Summable fun k : ℤ => F ((k:ℝ)/(Nat.lcm d1 d2 : ℝ))) :
    Work.FIArea4.KK F R d1 d2 a = (1/(Nat.lcm d1 d2 : ℝ)) *
      ∑' m : ℤ, Work.FIArea4.cCoef F R d1 d2 m *
        Complex.exp (2*Real.pi*Complex.I*(m:ℝ)*(a:ℝ)/(Nat.lcm d1 d2 : ℝ)) := by
  have hmain := tsum_dual_fourier (Nat.lcm d1 d2) F R a (Work.FIArea4.wChar d1 d2) hF
  unfold Work.FIArea4.KK Work.FIArea4.cCoef
  rw [hmain]

end Work.FIArea4.Vflip
