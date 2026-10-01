import Mathlib
import Submission.Work.LinnikBurgess.gaussTwoLocal_defs
import Submission.Work.LinnikBurgess.peel_gauss
import Submission.Work.LinnikBurgess.vcap_kernel_eq
import Submission.Work.LinnikBurgess.primePow_kernel_char_sum
import Submission.Work.LinnikBurgess.lfSmall.gaussSumTwoPow

/-!
# The quadratic Gauss sum over `ZMod (p^K)` for odd `p`

For an odd prime `p`, `K ≥ 1`, a primitive `p^K`-th root of unity `θ` and `α γ : ZMod (p^K)` we
prove

`gaussQuad p K θ α γ * conj (gaussQuad p K θ α γ) = p^K · ∑_{h : 2γh = 0} θ^((αh).val)`

and deduce, with `g = vcap p K (2γ).val` (the `p`-adic valuation of `2γ`, capped at `K`),

`‖gaussQuad p K θ α γ‖ ≤ p^((K+g)/2)` if `p^g ∣ α.val`, and `= 0` otherwise.

This is the `p`-odd analogue of `Work.LinnikBurgess.lfSmall.gaussSumTwoPow`.
-/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess.lfSmall

/-- On the kernel of multiplication by `2γ` (with `p` odd, so `2` is invertible) the quadratic
part `γ h²` vanishes: `2γh = 0` gives `γh = 0`, hence `γh² = (γh)h = 0`. -/
private lemma gamma_mul_sq_eq_zero {p K : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (γ h : ZMod (p ^ K)) (hh : (2 * γ) * h = 0) : γ * h ^ 2 = 0 := by
  have h2u : IsUnit (2 : ZMod (p ^ K)) := isUnit_two_zmod (p := p) (e := K) hp2
  have h2 : (2 : ZMod (p ^ K)) * (γ * h) = 0 := by rw [← mul_assoc]; exact hh
  have hgh : γ * h = 0 := (IsUnit.mul_right_eq_zero h2u).mp h2
  rw [pow_two, ← mul_assoc, hgh, zero_mul]

/-- `vcap p K x ≤ K`. -/
private lemma vcap_le_p (p K x : ℕ) : vcap p K x ≤ K := by
  unfold vcap
  split
  · exact le_rfl
  · exact Nat.min_le_right _ _

/-- **The `|G|²` computation for the odd-`p` quadratic Gauss sum.**
`G · conj G = p^K · ∑_{h : 2γh = 0} θ^((αh).val)`. -/
theorem gaussQuad_mul_star_odd {p K : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hK : 1 ≤ K)
    {θ : ℂ} (hθ : IsPrimitiveRoot θ (p ^ K)) (α γ : ZMod (p ^ K)) :
    gaussQuad p K θ α γ * (starRingEnd ℂ) (gaussQuad p K θ α γ)
      = ((p ^ K : ℕ) : ℂ)
        * (∑ h : ZMod (p ^ K), if (2 * γ) * h = 0 then θ ^ ((α * h).val) else 0) := by
  haveI : NeZero (p ^ K) := ⟨pow_ne_zero K (Fact.out : p.Prime).ne_zero⟩
  have hconj : (starRingEnd ℂ) (gaussQuad p K θ α γ)
      = ∑ w : ZMod (p ^ K), θ ^ ((-(α * w + γ * w ^ 2)).val) := by
    rw [gaussQuad, map_sum]
    exact Finset.sum_congr rfl (fun w _ => conj_theta_pow_val hθ (α * w + γ * w ^ 2))
  have h1 : gaussQuad p K θ α γ * (starRingEnd ℂ) (gaussQuad p K θ α γ)
      = ∑ w : ZMod (p ^ K), ∑ w' : ZMod (p ^ K),
          θ ^ (((α * w + γ * w ^ 2) - (α * w' + γ * w' ^ 2)).val) := by
    rw [hconj, gaussQuad, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun w' _ => ?_))
    rw [← theta_pow_val_add hθ.pow_eq_one (α * w + γ * w ^ 2) (-(α * w' + γ * w' ^ 2))]
    congr 1
    ring
  rw [h1]
  let F : ZMod (p ^ K) × ZMod (p ^ K) → ℂ := fun q =>
    θ ^ (((α * q.1 + γ * q.1 ^ 2) - (α * q.2 + γ * q.2 ^ 2)).val)
  have e1 : (∑ w : ZMod (p ^ K), ∑ w' : ZMod (p ^ K),
        θ ^ (((α * w + γ * w ^ 2) - (α * w' + γ * w' ^ 2)).val)) = ∑ q, F q := by
    rw [Fintype.sum_prod_type]
  have e2 : (∑ q : ZMod (p ^ K) × ZMod (p ^ K), F q)
      = ∑ q : ZMod (p ^ K) × ZMod (p ^ K), F (q.1 + q.2, q.2) := sum_prod_shift F
  have e3 : (∑ q : ZMod (p ^ K) × ZMod (p ^ K), F (q.1 + q.2, q.2))
      = ∑ h : ZMod (p ^ K), ∑ w' : ZMod (p ^ K), F (h + w', w') := by
    rw [Fintype.sum_prod_type]
  have e4 : (∑ h : ZMod (p ^ K), ∑ w' : ZMod (p ^ K), F (h + w', w'))
      = ∑ h : ZMod (p ^ K), ∑ w' : ZMod (p ^ K),
          θ ^ (((α * (h + w') + γ * (h + w') ^ 2) - (α * w' + γ * w' ^ 2)).val) := rfl
  rw [e1, e2, e3, e4]
  have h4 : ∀ h w' : ZMod (p ^ K),
      (α * (h + w') + γ * (h + w') ^ 2) - (α * w' + γ * w' ^ 2)
        = (α * h + γ * h ^ 2) + ((2 * γ) * h) * w' := by
    intro h w'
    ring
  simp_rw [h4]
  have h5 : ∀ h : ZMod (p ^ K),
      (∑ w' : ZMod (p ^ K), θ ^ (((α * h + γ * h ^ 2) + ((2 * γ) * h) * w').val))
        = θ ^ ((α * h + γ * h ^ 2).val)
            * (if (2 * γ) * h = 0 then ((p ^ K : ℕ) : ℂ) else 0) := by
    intro h
    exact sum_theta_val_add_mul hθ (α * h + γ * h ^ 2) ((2 * γ) * h)
  simp_rw [h5]
  have h6 : ∀ h : ZMod (p ^ K),
      θ ^ ((α * h + γ * h ^ 2).val) * (if (2 * γ) * h = 0 then ((p ^ K : ℕ) : ℂ) else 0)
        = ((p ^ K : ℕ) : ℂ) * (if (2 * γ) * h = 0 then θ ^ ((α * h).val) else 0) := by
    intro h
    by_cases hh : (2 * γ) * h = 0
    · have hgs : γ * h ^ 2 = 0 := gamma_mul_sq_eq_zero hp2 γ h hh
      rw [if_pos hh, if_pos hh, hgs, add_zero, mul_comm]
    · rw [if_neg hh, if_neg hh, mul_zero, mul_zero]
  simp_rw [h6]
  rw [Finset.mul_sum]

/-- **Quadratic Gauss-sum bound over `ZMod (p^K)`** (`p` odd).  With `g = vcap p K (2γ).val`,

`‖∑_{w} θ^((α w + γ w²).val)‖ ≤ p^((K+g)/2)` if `p^g ∣ α.val`, and the sum vanishes otherwise. -/
theorem gaussQuad_bound_odd {p K : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hK : 1 ≤ K)
    {θ : ℂ} (hθ : IsPrimitiveRoot θ (p ^ K)) (α γ : ZMod (p ^ K)) :
    ‖gaussQuad p K θ α γ‖
      ≤ (if (p ^ vcap p K (2 * γ).val) ∣ α.val
          then (p : ℝ) ^ ((((K : ℕ) : ℝ) + ((vcap p K (2 * γ).val : ℕ) : ℝ)) / 2) else 0) := by
  haveI : NeZero (p ^ K) := ⟨pow_ne_zero K (Fact.out : p.Prime).ne_zero⟩
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  set g : ℕ := vcap p K (2 * γ).val with hgdef
  set G : ℂ := gaussQuad p K θ α γ with hGdef
  have hgK : g ≤ K := by rw [hgdef]; exact vcap_le_p p K (2 * γ).val
  -- the kernel of `2γ` is the kernel of `p^g`
  have hbridge : ∀ h : ZMod (p ^ K), ((2 * γ) * h = 0)
      ↔ (((p ^ g : ℕ) : ZMod (p ^ K)) * h = 0) := by
    intro h
    have h1 := vcap_kernel_eq (p := p) (K := K) hK (2 * γ) h
    rwa [← hgdef] at h1
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
    exact primePow_kernel_char_sum hgK hθ α
  have hnorm : ‖G‖ ^ 2 = (p : ℝ) ^ K * (if p ^ g ∣ α.val then (p : ℝ) ^ g else 0) := by
    have h1 : ‖G * (starRingEnd ℂ) G‖ = ‖G‖ ^ 2 := by
      rw [norm_mul, starRingEnd_apply, norm_star, pow_two]
    have hcoll := gaussQuad_mul_star_odd hp2 hK hθ α γ
    rw [← hGdef] at hcoll
    rw [← h1, hcoll, hKsum, norm_mul, Complex.norm_natCast, Nat.cast_pow]
    congr 1
    by_cases hc : p ^ g ∣ α.val
    · rw [if_pos hc, if_pos hc, Complex.norm_natCast, Nat.cast_pow]
    · rw [if_neg hc, if_neg hc, norm_zero]
  set e : ℝ := (((K : ℕ) : ℝ) + ((g : ℕ) : ℝ)) / 2 with hedef
  by_cases hc : p ^ g ∣ α.val
  · rw [if_pos hc]
    have hsq : ‖G‖ ^ 2 = ((p : ℝ) ^ e) ^ 2 := by
      rw [hnorm, if_pos hc]
      have hpK : (p : ℝ) ^ K = (p : ℝ) ^ ((K : ℕ) : ℝ) := (Real.rpow_natCast (p : ℝ) K).symm
      have hpg : (p : ℝ) ^ g = (p : ℝ) ^ ((g : ℕ) : ℝ) := (Real.rpow_natCast (p : ℝ) g).symm
      rw [hpK, hpg, ← Real.rpow_add hpR, pow_two, ← Real.rpow_add hpR]
      congr 1
      rw [hedef]; ring
    have hnG : ‖G‖ = (p : ℝ) ^ e :=
      (pow_left_inj₀ (norm_nonneg G) (Real.rpow_nonneg hpR.le e) (by norm_num)).mp hsq
    rw [hGdef] at hnG
    rw [hnG, hedef]
  · rw [if_neg hc]
    have hz : ‖G‖ ^ 2 = 0 := by rw [hnorm, if_neg hc, mul_zero]
    have hzero : ‖G‖ = 0 := by nlinarith [norm_nonneg G]
    rw [hGdef] at hzero
    rw [hzero]

end Work.LinnikBurgess.lfSmall
