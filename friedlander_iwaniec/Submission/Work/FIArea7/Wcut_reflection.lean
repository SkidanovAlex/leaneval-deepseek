import Mathlib
import Submission.Work.FIArea7.FIsymbols

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The reflection `d ↦ M/(4d)` of the large-moduli cut (*FI* §17)

The combinatorial content of the reflection move of *FI* §17 is that, on the divisors `d` of `M/4`
with `d ≥ 1`, the map `d ↦ M/(4d)` is an involution which swaps the cut conditions `X < d` and
`4eX < M` while preserving the divisibility condition `4d ∣ M` and the range `[1, M/4+1]`.  These
two lemmas record the pointwise statements; the target theorem `Wcut_reflection` is then a
`Finset.sum_bij'` along the involution. -/

/-- The reflection `d ↦ M/(4d)` is an involution on the positive divisors `d` of `M/4`
(equivalently, on the `d` with `4d ∣ M`), for `M > 0`. -/
lemma Wcut_reflect_invol {M d : ℕ} (hM : 0 < M) (hd : 4 * d ∣ M) :
    M / (4 * (M / (4 * d))) = d := by
  have h1 : M / (4 * d) * (4 * d) = M := Nat.div_mul_cancel hd
  have hMeq : M = 4 * (M / (4 * d)) * d := by nth_rewrite 1 [← h1]; ring
  have he : 0 < M / (4 * d) := by
    rcases Nat.eq_zero_or_pos (M / (4 * d)) with h | h
    · rw [h, zero_mul] at h1; omega
    · exact h
  nth_rewrite 1 [hMeq]
  exact Nat.mul_div_cancel_left d (by omega)

/-- The reflection maps the "large divisors" `d` of the cut of *FI* (10.17) to the "small
complementary divisors" `e`: if `d ≥ 1`, `4d ∣ M`, `X < d` and `M < 4dX`, then
`e = M/(4d)` satisfies `1 ≤ e`, `e ≤ M/4+1`, `4e ∣ M`, `e < X` and `4eX < M`. -/
lemma Wcut_reflect_mem {M X d : ℕ} (hM : 0 < M)
    (hd : d ∈ (Finset.Icc 1 (M / 4 + 1)).filter (fun d => 4 * d ∣ M ∧ X < d ∧ M < 4 * d * X)) :
    M / (4 * d) ∈ (Finset.Icc 1 (M / 4 + 1)).filter
      (fun e => 4 * e ∣ M ∧ e < X ∧ 4 * e * X < M) := by
  simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
  obtain ⟨⟨hd1, _⟩, hdiv, hXd, hMX⟩ := hd
  have h1 : M / (4 * d) * (4 * d) = M := Nat.div_mul_cancel hdiv
  have hMeq : M = 4 * (M / (4 * d)) * d := by nth_rewrite 1 [← h1]; ring
  have he0 : 0 < M / (4 * d) := by
    rcases Nat.eq_zero_or_pos (M / (4 * d)) with h | h
    · rw [h, zero_mul] at h1; omega
    · exact h
  have hpos : 0 < 4 * (M / (4 * d)) := by omega
  refine ⟨⟨by omega, ?_⟩, ⟨d, hMeq⟩, ?_, ?_⟩
  · have hmul : M / (4 * d) * 4 ≤ M := by
      calc M / (4 * d) * 4 = 4 * (M / (4 * d)) := by ring
        _ ≤ 4 * (M / (4 * d)) * d := Nat.le_mul_of_pos_right _ (by omega)
        _ = M := hMeq.symm
    have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr hmul
    omega
  · exact Nat.div_lt_of_lt_mul hMX
  · calc 4 * (M / (4 * d)) * X < 4 * (M / (4 * d)) * d := (Nat.mul_lt_mul_left hpos).mpr hXd
      _ = M := hMeq.symm

/-- The inverse direction of `Wcut_reflect_mem`: the reflection maps the small complementary
divisors `e` of the right-hand side back to the large divisors `d` of the left-hand side. -/
lemma Wcut_reflect_mem' {M X e : ℕ} (hM : 0 < M)
    (he : e ∈ (Finset.Icc 1 (M / 4 + 1)).filter
      (fun e => 4 * e ∣ M ∧ e < X ∧ 4 * e * X < M)) :
    M / (4 * e) ∈ (Finset.Icc 1 (M / 4 + 1)).filter
      (fun d => 4 * d ∣ M ∧ X < d ∧ M < 4 * d * X) := by
  simp only [Finset.mem_filter, Finset.mem_Icc] at he ⊢
  obtain ⟨⟨he1, _⟩, hdiv, heX, h4eX⟩ := he
  have h1 : M / (4 * e) * (4 * e) = M := Nat.div_mul_cancel hdiv
  have hMeq : M = 4 * (M / (4 * e)) * e := by nth_rewrite 1 [← h1]; ring
  have hd0 : 0 < M / (4 * e) := by
    rcases Nat.eq_zero_or_pos (M / (4 * e)) with h | h
    · rw [h, zero_mul] at h1; omega
    · exact h
  have hpos : 0 < 4 * e := by omega
  refine ⟨⟨by omega, ?_⟩, ⟨e, hMeq⟩, ?_, ?_⟩
  · have hmul : M / (4 * e) * 4 ≤ M := by
      calc M / (4 * e) * 4 = 4 * (M / (4 * e)) := by ring
        _ ≤ 4 * (M / (4 * e)) * e := Nat.le_mul_of_pos_right _ (by omega)
        _ = M := hMeq.symm
    have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr hmul
    omega
  · have hM' : M = (4 * e) * (M / (4 * e)) := by rw [mul_comm]; exact h1.symm
    rw [hM'] at h4eX
    exact (Nat.mul_lt_mul_left hpos).mp h4eX
  · have hpos4d : 0 < 4 * (M / (4 * e)) := by omega
    calc M = 4 * (M / (4 * e)) * e := hMeq
      _ < 4 * (M / (4 * e)) * X := (Nat.mul_lt_mul_left hpos4d).mpr heX

/-- ***FI* §17: the reflection `d ↦ M/(4d)` of the large-moduli cut.**

The partial sum of (10.13) with the (10.17) cut is `2·Σ_{z₁,z₂} ββ̄·log·Σ_{d} (φ(d)/d)(z₂/z₁|d)`
over the `d` with `4d ∣ |Δ|`, `X < d`, `4dX > |Δ|`.  This statement performs the *first* move of
§17 ("since `d` is extremely large it is useful to switch `d` into the complementary divisor of
`|Δ|/4`"): with `M = |Δ|` and `e = M/(4d)`, the cut conditions `X < d`, `M < 4dX` become
`e < X`, `4eX < M`, and the weight `g d` becomes `g (M/(4e))`.  Concretely, for `M ≥ 1`, `X ≥ 1`
and any `g : ℕ → ℝ`,

  `Σ_{d ∈ [1, M/4+1], 4d ∣ M, X < d, M < 4dX} g d
     = Σ_{e ∈ [1, M/4+1], 4e ∣ M, e < X, 4eX < M} g (M/(4e))`.

The two index sets correspond under `d ↦ M/(4d)`, an involution on the divisors `d` of `M/4`
(indeed `4·(M/(4d))·d = M`, and `e < X ⟺ M < 4dX` while `4eX < M ⟺ X < d` for `M > 0`).

In the application `M = |Δ(z₁,z₂)| = Work.FIPlan.absDelta z₁ z₂` and
`g d = (Nat.totient d / d)·(jacobiSym (Re(z̄₁z₂)) d)·logFac z₁ z₂`; the reflected weight is the
paper's `(φ(m)/m)(z₂/z₁|m)` with `m = M/(4e)`, to which *FI* (17.5) applies and then the expansion
`φ(m)/m = Σ_{b∣m} μ(b)/b`.  Reducing `TcutMod` to the right-hand side is what exposes the *small*
divisors `e < X` and hence the congruence sum `Σ_ω (ω|·)` of (17.9). -/
theorem Wcut_reflection {M X : ℕ} (hM : 0 < M) (g : ℕ → ℝ) :
    ∑ d ∈ (Finset.Icc 1 (M / 4 + 1)).filter
        (fun d => 4 * d ∣ M ∧ X < d ∧ M < 4 * d * X), g d
      = ∑ e ∈ (Finset.Icc 1 (M / 4 + 1)).filter
        (fun e => 4 * e ∣ M ∧ e < X ∧ 4 * e * X < M), g (M / (4 * e)) := by
  refine Finset.sum_bij' (fun d _ => M / (4 * d)) (fun e _ => M / (4 * e))
    (fun d hd => Wcut_reflect_mem hM hd) (fun e he => Wcut_reflect_mem' hM he) ?_ ?_ ?_
  · intro a ha
    exact Wcut_reflect_invol hM (Finset.mem_filter.mp ha).2.1
  · intro a ha
    exact Wcut_reflect_invol hM (Finset.mem_filter.mp ha).2.1
  · intro a ha
    rw [Wcut_reflect_invol hM (Finset.mem_filter.mp ha).2.1]

end

end Work.FIArea7
