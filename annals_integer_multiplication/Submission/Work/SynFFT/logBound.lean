import Mathlib
import Submission.Work.SynFFT.defs

namespace Work.SynFFT

/-- Product of a list of powers of two: `∏ t ∈ l, 2^{f t} = 2^{∑ t ∈ l, f t}`. -/
private lemma prod_eq_pow_sum {l : List ℕ} {f : ℕ → ℕ} (h : ∀ t ∈ l, t = 2 ^ f t) :
    l.prod = 2 ^ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons t ts ih =>
    have ht : t = 2 ^ f t := h t (by simp)
    have hts : ∀ u ∈ ts, u = 2 ^ f u := fun u hu => h u (by simp [hu])
    calc (t :: ts).prod = t * ts.prod := rfl
      _ = t * 2 ^ (ts.map f).sum := by rw [ih hts]
      _ = 2 ^ (f t) * 2 ^ (ts.map f).sum := by conv_lhs => rw [ht]
      _ = 2 ^ (f t + (ts.map f).sum) := by rw [← pow_add]
      _ = 2 ^ ((t :: ts).map f).sum := rfl

/-- Each `t ∈ ts` is a power of two with exponent `≥ 1`, so `ts.prod = 2^{Σ log₂ t}` and
`ts.prod * r ≥ 2^{Σ log₂ t + 1}`; hence `Σ log₂ t < log₂ (ts.prod * r)`. -/
theorem logBound (r : ℕ) (ts : List ℕ) (p : ℕ) (hr : 2 ≤ r) (hp : 100 ≤ p)
    (hpow : ∀ t ∈ ts, ∃ k : ℕ, 1 ≤ k ∧ t = 2 ^ k) (hprod : ts.prod * r < 2 ^ p) :
    ((ts.map fun t => (Nat.log 2 t : ℝ)).sum) < (Nat.log 2 (ts.prod * r) : ℝ) := by
  have htwo : (1 : ℕ) < 2 := by norm_num
  -- Every element of `ts` is `2 ^ (Nat.log 2 t)`.
  have hlog : ∀ t ∈ ts, t = 2 ^ Nat.log 2 t := by
    intro t ht
    obtain ⟨k, _, hk⟩ := hpow t ht
    rw [hk, Nat.log_pow htwo]
  -- Hence `ts.prod = 2 ^ S` where `S = Σ log₂ t`.
  have hA : ts.prod = 2 ^ (ts.map (fun t => Nat.log 2 t)).sum := prod_eq_pow_sum hlog
  set S : ℕ := (ts.map fun t => Nat.log 2 t).sum with hSdef
  -- `r ≥ 2` gives `2 ^ (S+1) ≤ ts.prod * r`.
  have hle : 2 ^ (S + 1) ≤ ts.prod * r := by
    rw [hA, pow_succ]
    exact Nat.mul_le_mul_left _ hr
  -- Monotonicity of `Nat.log` plus `Nat.log 2 (2 ^ (S+1)) = S+1`.
  have hnat : S < Nat.log 2 (ts.prod * r) := by
    calc S < S + 1 := Nat.lt_succ_self S
      _ = Nat.log 2 (2 ^ (S + 1)) := (Nat.log_pow htwo (S + 1)).symm
      _ ≤ Nat.log 2 (ts.prod * r) := Nat.log_mono_right hle
  -- Cast to `ℝ`.
  have hcast : (ts.map fun t => (Nat.log 2 t : ℝ)).sum = (S : ℝ) := by
    rw [hSdef, Nat.cast_list_sum, List.map_map]
    rfl
  rw [hcast]
  exact_mod_cast hnat

end Work.SynFFT
