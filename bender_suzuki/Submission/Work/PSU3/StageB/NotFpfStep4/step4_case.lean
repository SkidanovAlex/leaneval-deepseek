import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.NotFpfStep4

theorem step4_case {K : Type} [Field K] [CharP K 2] (μ : K ≃+* K) (σ : K →+* K)
    (hμF : ∀ x : K, σ x = x → σ (μ x) = μ x)
    {c τ v : K} (hc : μ c = c) (hcσ : σ c = c⁻¹) (hcF : σ c ≠ c)
    (hτ : σ τ = τ) (hv : σ v = v)
    (h9 : (v + c) * (1 + μ τ * μ v) = (μ τ + c⁻¹) * (1 + τ * v))
    (hv1 : v ≠ c → 1 + τ * v ≠ 0) :
    (c + c⁻¹ + μ τ) * τ = (c + c⁻¹ + μ (μ τ)) * (μ τ) := by
  -- `v ≠ c`: if `v = c` then `c⁻¹ = σ c = σ v = v = c`, contradicting `σ c ≠ c`.
  have hvc : v ≠ c := by
    intro h
    have hcc : c⁻¹ = c := by rw [← hcσ, ← h, hv]
    exact hcF (by rw [hcσ]; exact hcc)
  -- `c + c⁻¹ ≠ 0`: otherwise (characteristic `2`) `c = c⁻¹`, so `σ c = c`.
  have hsum : c + c⁻¹ ≠ 0 := by
    intro h
    have hcc : c = c⁻¹ := by
      calc c = -c⁻¹ := eq_neg_of_add_eq_zero_left h
        _ = c⁻¹ := CharTwo.neg_eq c⁻¹
    exact hcF (by rw [hcσ]; exact hcc.symm)
  have hμτ' : σ (μ τ) = μ τ := hμF τ hτ
  have hμv' : σ (μ v) = μ v := hμF v hv
  have hcinv : σ c⁻¹ = c := by rw [map_inv₀, hcσ, inv_inv]
  -- Apply `σ` to `h9`.  Since `v` and `τ` are `σ`-fixed and `μ` maps the fixed field
  -- into itself, `σ(μ τ) = μ τ` and `σ(μ v) = μ v`, so only the `c`-data changes.
  have h9σ : (v + c⁻¹) * (1 + μ τ * μ v) = (μ τ + c) * (1 + τ * v) := by
    have h := congrArg σ h9
    simp only [map_mul, map_add, map_one] at h
    rw [hv, hcσ, hμτ', hμv', hτ] at h
    rw [hcinv] at h
    exact h
  -- Add the two instances of the relation.  In characteristic `2` this collapses to
  -- `(c + c⁻¹) * (1 + μ τ * μ v) = (c + c⁻¹) * (1 + τ * v)`.
  have hAeq : (c + c⁻¹) * (1 + μ τ * μ v) = (c + c⁻¹) * (1 + τ * v) := by
    have key : (v + c) * (1 + μ τ * μ v) + (v + c⁻¹) * (1 + μ τ * μ v)
        = (μ τ + c⁻¹) * (1 + τ * v) + (μ τ + c) * (1 + τ * v) :=
      (congrArg (fun t => t + (v + c⁻¹) * (1 + μ τ * μ v)) h9).trans
        (congrArg (fun t => (μ τ + c⁻¹) * (1 + τ * v) + t) h9σ)
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) key
  -- Since `c + c⁻¹ ≠ 0` we cancel it.
  have hAAB : 1 + μ τ * μ v = 1 + τ * v := mul_left_cancel₀ hsum hAeq
  have hprod : μ τ * μ v = τ * v := add_left_cancel hAAB
  have hB : 1 + τ * v ≠ 0 := hv1 hvc
  have hA0 : 1 + μ τ * μ v ≠ 0 := by rw [hAAB]; exact hB
  -- Cancel the common nonzero factor in `h9` to get `v + c = μ τ + c⁻¹`.
  have hvc4 : v + c = μ τ + c⁻¹ := by
    have h9' : (v + c) * (1 + μ τ * μ v) = (μ τ + c⁻¹) * (1 + μ τ * μ v) := by
      rw [h9, hAAB]
    exact mul_right_cancel₀ hA0 h9'
  have hμτeq : μ τ = v + c + c⁻¹ := by
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hvc4
  -- `μ` fixes `c` and hence also `c⁻¹`.
  have hμμτ : μ (μ τ) = μ v + c + c⁻¹ := by
    rw [hμτeq, map_add, map_add, hc, map_inv₀, hc]
  -- Both bracketed factors simplify to `v` and `μ v` respectively.
  have hL : c + c⁻¹ + μ τ = v := by rw [hμτeq]; ring_nf; simp [CharTwo.two_eq_zero]
  have hR : c + c⁻¹ + μ (μ τ) = μ v := by rw [hμμτ]; ring_nf; simp [CharTwo.two_eq_zero]
  rw [hL, hR, mul_comm (μ v) (μ τ), hprod, mul_comm τ v]

end Work.PSU3.StageB.NotFpfStep4
