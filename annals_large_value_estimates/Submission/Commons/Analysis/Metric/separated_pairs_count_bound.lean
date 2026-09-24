import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Norm

namespace Commons.Analysis.Metric

open Finset

/-- **Counting: 1-separated points near a fixed point.**  If every two distinct points of a
finite set `W ⊆ ℝ` are at distance at least `1`, then for any real `u` and any `N : ℕ` the
number of points of `W` within distance `N` of `u` is at most `2N + 1`.

Proof: the map `b ↦ ⌈b - u⌉` is injective on `{b ∈ W : |u - b| ≤ N}` (distinct points are
`≥ 1` apart, so their ceilings w.r.t. `u` differ) and lands in the integer interval
`[-N, N]`, which has `2N + 1` elements. -/
private lemma card_filter_close_le (W : Finset ℝ)
    (hW : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → 1 ≤ |a - b|) (u : ℝ) (N : ℕ) :
    (W.filter (fun b => |u - b| ≤ (N : ℝ))).card ≤ 2 * N + 1 := by
  classical
  set T : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ) with hTdef
  have hcard : (W.filter (fun b => |u - b| ≤ (N : ℝ))).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun b : ℝ => ⌈b - u⌉)
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb
      obtain ⟨hbW, hbabs⟩ := hb
      rw [abs_le] at hbabs
      rw [Finset.mem_coe, hTdef, Finset.mem_Icc]
      constructor
      · have hlow : ((-(N : ℤ) : ℤ) : ℝ) ≤ b - u := by
          push_cast
          linarith [hbabs.2]
        have hmono := Int.ceil_mono hlow
        rwa [Int.ceil_intCast] at hmono
      · rw [Int.ceil_le]
        push_cast
        linarith [hbabs.1]
    · intro b hb b' hb' heq
      rw [Finset.mem_coe, Finset.mem_filter] at hb hb'
      obtain ⟨hbW, _⟩ := hb
      obtain ⟨hb'W, _⟩ := hb'
      rcases lt_trichotomy b b' with hlt | heq' | hgt
      · have hs : 1 ≤ |b - b'| := hW b hbW b' hb'W (ne_of_lt hlt)
        have habs : |b - b'| = b' - b := by rw [abs_of_nonpos (by linarith)]; ring
        rw [habs] at hs
        have h1 : (b - u) + 1 ≤ b' - u := by linarith
        have h2 : ((⌈b - u⌉ : ℤ) : ℝ) < (b - u) + 1 := Int.ceil_lt_add_one (b - u)
        have h3 : b' - u ≤ ((⌈b' - u⌉ : ℤ) : ℝ) := Int.le_ceil (b' - u)
        have hlt2 : ((⌈b - u⌉ : ℤ) : ℝ) < ((⌈b' - u⌉ : ℤ) : ℝ) := by linarith
        have hltZ : ⌈b - u⌉ < ⌈b' - u⌉ := by exact_mod_cast hlt2
        exact absurd heq (ne_of_lt hltZ)
      · exact heq'
      · have hs : 1 ≤ |b - b'| := hW b hbW b' hb'W (ne_of_gt hgt)
        have habs : |b - b'| = b - b' := abs_of_nonneg (by linarith)
        rw [habs] at hs
        have h1 : (b' - u) + 1 ≤ b - u := by linarith
        have h2 : ((⌈b' - u⌉ : ℤ) : ℝ) < (b' - u) + 1 := Int.ceil_lt_add_one (b' - u)
        have h3 : b - u ≤ ((⌈b - u⌉ : ℤ) : ℝ) := Int.le_ceil (b - u)
        have hlt2 : ((⌈b' - u⌉ : ℤ) : ℝ) < ((⌈b - u⌉ : ℤ) : ℝ) := by linarith
        have hltZ : ⌈b' - u⌉ < ⌈b - u⌉ := by exact_mod_cast hlt2
        exact absurd heq.symm (ne_of_lt hltZ)
  have hTc : T.card = 2 * N + 1 := by
    rw [hTdef, Int.card_Icc]
    have h1 : (N : ℤ) + 1 - -(N : ℤ) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h1, Int.toNat_natCast]
  rw [hTc] at hcard
  exact hcard

/-- `∑ b ∈ s, (if p b then c else 0) = c * #(s.filter p)`, used to extract the number of
nearby points as a factor. -/
private lemma sum_ite_card_mul {s : Finset ℝ} (p : ℝ → Prop) [DecidablePred p] (c : ℝ) :
    ∑ b ∈ s, (if p b then c else 0) = ((s.filter p).card : ℝ) * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- **The large-value "pair count" bound.**  For a `1`-separated finite set `W ⊆ ℝ`, an
arbitrary coefficient function `x : ℝ → ℝ` and `N : ℕ`,
`∑_{a,b ∈ W, |a-b| ≤ N} x a x b ≤ (2N+1) ∑_{a ∈ W} x a ^ 2`.

Proof by AM–GM on each pair (`2 x a x b ≤ x a ^ 2 + x b ^ 2`) followed by double counting:
for each (fixed) point there are at most `2N+1` nearby points. -/
private lemma double_sum_le_sep (W : Finset ℝ)
    (hW : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → 1 ≤ |a - b|) (N : ℕ) (x : ℝ → ℝ) :
    (∑ a ∈ W, ∑ b ∈ W, if |a - b| ≤ (N : ℝ) then x a * x b else 0)
      ≤ (2 * (N : ℝ) + 1) * ∑ a ∈ W, x a ^ 2 := by
  classical
  set K : ℝ := 2 * (N : ℝ) + 1 with hKdef
  have hAM : 2 * (∑ a ∈ W, ∑ b ∈ W, if |a - b| ≤ (N : ℝ) then x a * x b else 0)
      ≤ ∑ a ∈ W, ∑ b ∈ W, if |a - b| ≤ (N : ℝ) then x a ^ 2 + x b ^ 2 else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    by_cases hc : |a - b| ≤ (N : ℝ)
    · simp only [hc, if_true]
      have := two_mul_le_add_sq (x a) (x b)
      linarith
    · simp [hc]
  have hcard' : ∀ u : ℝ, ((W.filter (fun b => |u - b| ≤ (N : ℝ))).card : ℝ) ≤ K := by
    intro u
    rw [hKdef]
    have := card_filter_close_le W hW u N
    exact_mod_cast this
  have hQ : (∑ a ∈ W, ∑ b ∈ W, if |a - b| ≤ (N : ℝ) then x a ^ 2 + x b ^ 2 else 0)
      ≤ 2 * (K * (∑ a ∈ W, x a ^ 2)) := by
    have hsplit : (∑ a ∈ W, ∑ b ∈ W, if |a - b| ≤ (N : ℝ) then x a ^ 2 + x b ^ 2 else 0)
        = (∑ a ∈ W, ∑ b ∈ W, if |a - b| ≤ (N : ℝ) then x a ^ 2 else 0)
        + (∑ a ∈ W, ∑ b ∈ W, if |a - b| ≤ (N : ℝ) then x b ^ 2 else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hc : |a - b| ≤ (N : ℝ) <;> simp [hc]
    rw [hsplit]
    have hT1 : (∑ a ∈ W, ∑ b ∈ W, if |a - b| ≤ (N : ℝ) then x a ^ 2 else 0)
        ≤ K * ∑ a ∈ W, x a ^ 2 := by
      calc (∑ a ∈ W, ∑ b ∈ W, if |a - b| ≤ (N : ℝ) then x a ^ 2 else 0)
          ≤ ∑ a ∈ W, K * x a ^ 2 := by
            apply Finset.sum_le_sum
            intro a ha
            rw [sum_ite_card_mul (fun b => |a - b| ≤ (N : ℝ)) (x a ^ 2)]
            exact mul_le_mul_of_nonneg_right (hcard' a) (sq_nonneg (x a))
        _ = K * ∑ a ∈ W, x a ^ 2 := by rw [Finset.mul_sum]
    have hT2 : (∑ a ∈ W, ∑ b ∈ W, if |a - b| ≤ (N : ℝ) then x b ^ 2 else 0)
        ≤ K * ∑ a ∈ W, x a ^ 2 := by
      rw [Finset.sum_comm]
      calc (∑ b ∈ W, ∑ a ∈ W, if |a - b| ≤ (N : ℝ) then x b ^ 2 else 0)
          ≤ ∑ b ∈ W, K * x b ^ 2 := by
            apply Finset.sum_le_sum
            intro b hb
            have hcb : ((W.filter (fun a => |a - b| ≤ (N : ℝ))).card : ℝ) ≤ K := by
              have hfilt : W.filter (fun a => |a - b| ≤ (N : ℝ))
                  = W.filter (fun a => |b - a| ≤ (N : ℝ)) :=
                Finset.filter_congr (fun a _ => by rw [abs_sub_comm])
              rw [hfilt]
              exact hcard' b
            rw [sum_ite_card_mul (fun a => |a - b| ≤ (N : ℝ)) (x b ^ 2)]
            exact mul_le_mul_of_nonneg_right hcb (sq_nonneg (x b))
        _ = K * ∑ a ∈ W, x a ^ 2 := by rw [Finset.mul_sum]
    linarith [hT1, hT2]
  have h2 : 2 * (∑ a ∈ W, ∑ b ∈ W, if |a - b| ≤ (N : ℝ) then x a * x b else 0)
      ≤ 2 * (K * (∑ a ∈ W, x a ^ 2)) := le_trans hAM hQ
  have hfin : (∑ a ∈ W, ∑ b ∈ W, if |a - b| ≤ (N : ℝ) then x a * x b else 0)
      ≤ K * (∑ a ∈ W, x a ^ 2) := by linarith
  rwa [hKdef] at hfin

theorem separated_pairs_count_bound :
    ∀ (W : Finset ℝ), (∀ a ∈ W, ∀ b ∈ W, a ≠ b → 1 ≤ |a - b|) → ∀ (N : ℕ) (c : ℝ → ℂ),
      (∑ a ∈ W, ∑ b ∈ W, if |a - b| ≤ (N : ℝ) then ‖c a‖ * ‖c b‖ else 0)
        ≤ (2 * (N : ℝ) + 1) * ∑ a ∈ W, ‖c a‖ ^ 2 := by
  intro W hW N c
  exact double_sum_le_sep W hW N (fun a => ‖c a‖)

end Commons.Analysis.Metric