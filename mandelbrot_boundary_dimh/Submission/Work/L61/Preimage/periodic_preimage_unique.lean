import Submission.Work.L61.Basic

/-! At most one point of `g ⁻¹' {w₀}` is periodic (Shishikura's Lemma 6.1, first line of its
proof).  This is pure dynamics.  If `f^[n] p = p` with `n ≥ 1` then `f^[n] (f p) = f p`, so
`w₀ = f p` is periodic with period `n`; hence `f^[n] w₀ = w₀ = f^[m] w₀` and
`p = f^[n-1] w₀ = f^[n-1] (f^[m] w₀) = f^[n-1+m] w₀`, while likewise `q = f^[m-1+n] w₀`. -/

namespace Work.L61

open MandelDim Set Function Metric Filter
open scoped Topology

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

theorem periodic_preimage_unique {d : ParabData f₀ D₀} {w₀ p q : ℂ}
    (hp : g d p = w₀) (hq : g d q = w₀)
    (hpp : ∃ n : ℕ, 1 ≤ n ∧ (g d)^[n] p = p)
    (hqq : ∃ m : ℕ, 1 ≤ m ∧ (g d)^[m] q = q) : p = q := by
  obtain ⟨n, hn1, hn⟩ := hpp
  obtain ⟨m, hm1, hm⟩ := hqq
  let f : ℂ → ℂ := g d
  have hn' : f^[n] p = p := hn
  have hm' : f^[m] q = q := hm
  have hp' : f p = w₀ := hp
  have hq' : f q = w₀ := hq
  -- `p` and `q` are the (n-1)-th resp. (m-1)-th predecessor of `w₀`
  have hp_eq : p = f^[n - 1] w₀ := by
    have h1 : f^[n] p = f^[n - 1] (f p) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [Function.iterate_succ_apply]
    rw [hn', hp'] at h1
    exact h1
  have hq_eq : q = f^[m - 1] w₀ := by
    have h1 : f^[m] q = f^[m - 1] (f q) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega]
      rw [Function.iterate_succ_apply]
    rw [hm', hq'] at h1
    exact h1
  -- `w₀` is periodic with periods `n` and `m`
  have hpern : f^[n] w₀ = w₀ := by
    calc f^[n] w₀ = f^[n] (f p) := by rw [hp']
      _ = f^[n + 1] p := by rw [Function.iterate_succ_apply]
      _ = f (f^[n] p) := by rw [Function.iterate_succ_apply']
      _ = f p := by rw [hn']
      _ = w₀ := hp'
  have hperm : f^[m] w₀ = w₀ := by
    calc f^[m] w₀ = f^[m] (f q) := by rw [hq']
      _ = f^[m + 1] q := by rw [Function.iterate_succ_apply]
      _ = f (f^[m] q) := by rw [Function.iterate_succ_apply']
      _ = f q := by rw [hm']
      _ = w₀ := hq'
  calc p = f^[n - 1] w₀ := hp_eq
    _ = f^[n - 1] (f^[m] w₀) := by rw [hperm]
    _ = f^[(n - 1) + m] w₀ := by rw [Function.iterate_add_apply]
    _ = f^[(m - 1) + n] w₀ := by congr 1; omega
    _ = f^[m - 1] (f^[n] w₀) := by rw [Function.iterate_add_apply]
    _ = f^[m - 1] w₀ := by rw [hpern]
    _ = q := hq_eq.symm

end

end Work.L61
