import Mathlib

namespace Work.Parab.invOrbit

open Filter
open scoped Topology

/-- One step of the chain rule for the Abel equation `φ (t + 1) = f₀ (φ t)`.

If `U` is open, `φ` is holomorphic on `U`, the Abel equation holds on `U`, and `f₀` is
differentiable at `φ t`, then `deriv φ (t + 1) = deriv f₀ (φ t) * deriv φ t`.  (The
differentiability of `f₀` at `φ t` is a genuine hypothesis: the Abel equation alone does
not force `f₀` to be differentiable there.) -/
theorem abel_step {f₀ φ : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hφdiff : DifferentiableOn ℂ φ U)
    (habel : ∀ t ∈ U, t + 1 ∈ U → φ (t + 1) = f₀ (φ t))
    {t : ℂ} (ht : t ∈ U) (ht1 : t + 1 ∈ U)
    (hf : DifferentiableAt ℂ f₀ (φ t)) :
    deriv φ (t + 1) = deriv f₀ (φ t) * deriv φ t := by
  have hφt : DifferentiableAt ℂ φ t := hφdiff.differentiableAt (hU.mem_nhds ht)
  -- the two functions `s ↦ φ (s + 1)` and `f₀ ∘ φ` agree near `t`
  have heq : (fun s => φ (s + 1)) =ᶠ[𝓝 t] (f₀ ∘ φ) := by
    filter_upwards [hU.mem_nhds ht,
      (continuous_add_const (1 : ℂ)).continuousAt.preimage_mem_nhds (hU.mem_nhds ht1)]
      with s hs hs1
    exact habel s hs hs1
  calc deriv φ (t + 1) = deriv (fun s => φ (s + 1)) t := (deriv_comp_add_const φ 1 t).symm
    _ = deriv (f₀ ∘ φ) t := heq.deriv_eq
    _ = deriv f₀ (φ t) * deriv φ t := deriv_comp t hf hφt

theorem abel_chain_deriv {f₀ φ : ℂ → ℂ} {U : Set ℂ} {u : ℂ} {n : ℕ}
    (hU : IsOpen U) (hφdiff : DifferentiableOn ℂ φ U)
    (habel : ∀ t ∈ U, t + 1 ∈ U → φ (t + 1) = f₀ (φ t))
    (hu : ∀ k : ℕ, k ≤ n → u + (k : ℂ) ∈ U)
    (hder : deriv φ u ≠ 0)
    (hfnz : ∀ k : ℕ, k < n → deriv f₀ (φ (u + (k : ℂ))) ≠ 0) :
    deriv φ (u + (n : ℂ)) ≠ 0 := by
  have key : ∀ k : ℕ, k ≤ n → deriv φ (u + (k : ℂ)) ≠ 0 := by
    intro k
    induction k with
    | zero => intro _; simpa using hder
    | succ m ih =>
      intro hk
      have hmle : m ≤ n := le_trans (Nat.le_succ m) hk
      have hmU : u + (m : ℂ) ∈ U := hu m hmle
      have hm1U : (u + (m : ℂ)) + 1 ∈ U := by
        have := hu (m + 1) hk
        simpa only [Nat.cast_succ, add_assoc] using this
      -- `deriv f₀ (φ (u + m)) ≠ 0` forces `f₀` to be differentiable there
      have hf : DifferentiableAt ℂ f₀ (φ (u + (m : ℂ))) := by
        by_contra h
        exact hfnz m (Nat.lt_of_succ_le hk) (deriv_zero_of_not_differentiableAt h)
      have hstep := abel_step hU hφdiff habel hmU hm1U hf
      have hco : u + ((m + 1 : ℕ) : ℂ) = (u + (m : ℂ)) + 1 := by push_cast; ring
      rw [hco, hstep]
      exact mul_ne_zero (hfnz m (Nat.lt_of_succ_le hk)) (ih hmle)
  exact key n le_rfl

end Work.Parab.invOrbit
