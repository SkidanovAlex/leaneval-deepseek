import Mathlib
import Submission.Work.LinnikBurgess.gaussTwoLocal_defs
import Submission.Work.LinnikBurgess.primePow_kernel_char_sum
import Submission.Work.LinnikBurgess.gaussQuad_mul_star
import Submission.Work.LinnikBurgess.vcap_kernel_eq

open scoped BigOperators

namespace Work.LinnikBurgess

/-- `vcap p K x` is always at most `K`. -/
lemma vcap_le (p K x : ℕ) : vcap p K x ≤ K := by
  rw [vcap]; split
  · exact le_rfl
  · exact min_le_right _ _

/-- **Quadratic Gauss-sum bound over `ZMod (p^K)`.**  Let `p` be an odd prime, `K ≥ 1`, `θ` a
primitive `p^K`-th root of unity and `α γ : ZMod (p^K)`.  Then the complete sum
`∑_{w : ZMod (p^K)} θ ^ ((α w + γ w^2).val)` is bounded by `p ^ ((K+g)/2)` when `p^g ∣ α.val`
and vanishes otherwise, where `g = vcap p K (2γ).val = min(v_p(2γ), K)` (with `v_p(0) = K`). -/
theorem gaussQuad_bound {p K : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hK : 1 ≤ K)
    (θ : ℂ) (hθ : IsPrimitiveRoot θ (p ^ K)) (α γ : ZMod (p ^ K)) :
    ‖gaussQuad p K θ α γ‖
      ≤ (if (p ^ vcap p K (2 * γ).val) ∣ α.val
          then (p : ℝ) ^ (((K : ℝ) + (vcap p K (2 * γ).val : ℝ)) / 2) else 0) := by
  have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  set g : ℕ := vcap p K (2 * γ).val with hgdef
  set G : ℂ := gaussQuad p K θ α γ with hGdef
  -- The kernel of multiplication by `2γ` is the kernel of multiplication by `p^g`.
  have hbridge : ∀ h : ZMod (p ^ K), ((2 * γ) * h = 0)
      ↔ (((p ^ g : ℕ) : ZMod (p ^ K)) * h = 0) := by
    intro h
    have h1 := vcap_kernel_eq (p := p) (K := K) hK (2 * γ) h
    rw [← hgdef] at h1
    exact h1
  -- Evaluation of the kernel sum `∑_{2γ h = 0} θ^{(α h).val}`.
  have hKsum : (∑ h : ZMod (p ^ K), if (2 * γ) * h = 0 then θ ^ ((α * h).val) else 0)
      = if p ^ g ∣ α.val then ((p ^ g : ℕ) : ℂ) else 0 := by
    have e1 : (∑ h : ZMod (p ^ K), if (2 * γ) * h = 0 then θ ^ ((α * h).val) else 0)
        = ∑ h ∈ Finset.univ.filter (fun h : ZMod (p ^ K) => (2 * γ) * h = 0),
            θ ^ ((α * h).val) := by
      rw [Finset.sum_filter]
    have e2 : (∑ h ∈ Finset.univ.filter (fun h : ZMod (p ^ K) => (2 * γ) * h = 0),
            θ ^ ((α * h).val))
        = ∑ h ∈ Finset.univ.filter
            (fun h : ZMod (p ^ K) => ((p ^ g : ℕ) : ZMod (p ^ K)) * h = 0),
            θ ^ ((α * h).val) := by
      refine Finset.sum_congr ?_ (fun h _ => rfl)
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hbridge h
    rw [e1, e2]
    exact primePow_kernel_char_sum (vcap_le p K (2 * γ).val) hθ α
  -- Norm-squared identity: `‖G‖² = p^K · (p^g if p^g ∣ α.val else 0)`.
  have hnorm : ‖G‖ ^ 2 = (p : ℝ) ^ K * (if p ^ g ∣ α.val then (p : ℝ) ^ g else 0) := by
    have h1 : ‖G * star G‖ = ‖G‖ ^ 2 := by rw [norm_mul, norm_star, pow_two]
    have hcoll := gaussQuad_mul_star hp2 hK hθ α γ
    rw [← hGdef] at hcoll
    rw [← h1, hcoll, hKsum]
    rw [norm_mul, Complex.norm_natCast, Nat.cast_pow]
    congr 1
    by_cases hc : p ^ g ∣ α.val
    · rw [if_pos hc, if_pos hc, Complex.norm_natCast, Nat.cast_pow]
    · rw [if_neg hc, if_neg hc, norm_zero]
  set e : ℝ := ((K : ℝ) + (g : ℝ)) / 2 with hedef
  by_cases hc : p ^ g ∣ α.val
  · rw [if_pos hc]
    have hsq : ‖G‖ ^ 2 = ((p : ℝ) ^ e) ^ 2 := by
      rw [hnorm, if_pos hc]
      have hpK : (p : ℝ) ^ K = (p : ℝ) ^ ((K : ℕ) : ℝ) := (Real.rpow_natCast (p:ℝ) K).symm
      have hpg : (p : ℝ) ^ g = (p : ℝ) ^ ((g : ℕ) : ℝ) := (Real.rpow_natCast (p:ℝ) g).symm
      rw [hpK, hpg, ← Real.rpow_add hpR, pow_two, ← Real.rpow_add hpR]
      congr 1
      rw [hedef]; ring
    exact le_of_eq ((pow_left_inj₀ (norm_nonneg G) (Real.rpow_nonneg hpR.le e)
      (by norm_num : (2:ℕ) ≠ 0)).mp hsq)
  · rw [if_neg hc]
    have hz : ‖G‖ ^ 2 = 0 := by rw [hnorm, if_neg hc, mul_zero]
    have hzero : ‖G‖ = 0 := by nlinarith [norm_nonneg G]
    rw [hzero]

end Work.LinnikBurgess
