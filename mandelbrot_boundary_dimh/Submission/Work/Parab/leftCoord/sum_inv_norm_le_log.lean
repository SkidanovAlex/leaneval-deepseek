import Mathlib
import Submission.Work.Parab.leftCoord.sum_inv_max_le
import Submission.Work.Parab.leftCoord.filter_eq_range_card

/-!
# A logarithmic bound for `∑ 1 / ‖w j‖` along an orbit leaving every left half-plane

Let `c, R > 0` and let `w : ℕ → ℂ` be such that `‖w j‖ ≥ R` for `j < k` and
`Re (w j) + c ≤ Re (w (j+1))` for `j < k`.  Then `∑_{j<k} 1 / ‖w j‖` grows at most
like `log k`:

`sum_inv_norm_le_log`.

The real part `x j = Re (w j)` splits the index range `{0, …, k-1}` into three
contiguous blocks: an initial block on which `x j < 0` (where `|x j| = -x j` decreases
by at least `c` per step), a middle block on which `|x j| < R`, and a terminal block on
which `x j ≥ 0` (where `x j` increases by at least `c` per step).  On each block `|x j|`
dominates an arithmetic progression `c * m`, and `∑ 1 / (c * m)` is bounded by a
multiple of `1 + log k` (the harmonic-number bound `sum_inv_max_le`).
-/

namespace Work.Parab.leftCoord

/-- Iterating the increment hypothesis: from `x j + c ≤ x (j+1)` for all `j < k` we get
`x i + c * d ≤ x (i + d)` whenever `i + d < k`. -/
private lemma iterate_le {x : ℕ → ℝ} {c : ℝ} {k : ℕ}
    (h : ∀ j < k, x j + c ≤ x (j + 1)) :
    ∀ i d, i + d < k → x i + c * (d : ℝ) ≤ x (i + d) := by
  intro i d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h1 : x i + c * (d : ℝ) ≤ x (i + d) := ih (by omega)
    have h2 : x (i + d) + c ≤ x (i + d + 1) := h (i + d) (by omega)
    have h3 : i + (d + 1) = i + d + 1 := by omega
    rw [h3]
    have he : x i + c * ((d + 1 : ℕ) : ℝ) = x i + c * (d : ℝ) + c := by
      push_cast; ring
    rw [he]
    linarith

theorem sum_inv_norm_le_log {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : ℕ → ℂ) (k : ℕ),
      (∀ j < k, R ≤ ‖w j‖) →
      (∀ j < k, (w j).re + c ≤ (w (j + 1)).re) →
      ∑ j ∈ Finset.range k, 1 / ‖w j‖ ≤ C * (1 + Real.log (k + 1)) := by
  classical
  have h2c : (0 : ℝ) < 2 / c := div_pos (by norm_num) hc
  have h2R : (0 : ℝ) < 2 / R := div_pos (by norm_num) hR
  refine ⟨2 / R + 2 / c + 1, by linarith, ?_⟩
  intro w k hnorm hmono
  let x : ℕ → ℝ := fun j => (w j).re
  have hxmono : ∀ j < k, x j + c ≤ x (j + 1) := fun j hj => hmono j hj
  -- every term is dominated by `1 / max R |x j|`
  have hstep1 : ∑ j ∈ Finset.range k, 1 / ‖w j‖ ≤ ∑ j ∈ Finset.range k, 1 / max R |x j| := by
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j < k := Finset.mem_range.mp hj
    have hRnorm : R ≤ ‖w j‖ := hnorm j hj'
    have habs : |x j| ≤ ‖w j‖ := Complex.abs_re_le_norm (w j)
    have hpos : 0 < max R |x j| := lt_of_lt_of_le hR (le_max_left _ _)
    have hle : max R |x j| ≤ ‖w j‖ := max_le hRnorm habs
    exact one_div_le_one_div_of_le hpos hle
  -- the initial segment of indices with `x j < 0`
  let p : ℕ → Prop := fun j => x j < 0
  have hdc : ∀ j < k, p j → ∀ i, i < j → p i := by
    intro j hj hpj i hij
    have hiter := iterate_le hxmono i (j - i) (by omega)
    have hjeq : i + (j - i) = j := by omega
    rw [hjeq] at hiter
    have hci : 0 ≤ c * ((j - i : ℕ) : ℝ) :=
      mul_nonneg (le_of_lt hc) (by positivity)
    show x i < 0
    linarith
  let τ : ℕ := ((Finset.range k).filter p).card
  have hτle : τ ≤ k := by simpa using Finset.card_filter_le (Finset.range k) p
  have hseg : (Finset.range k).filter p = Finset.range τ := filter_eq_range_card hdc
  have hlt : ∀ j, j < τ → x j < 0 := by
    intro j hj
    have hmem : j ∈ (Finset.range k).filter p := by
      rw [hseg]; exact Finset.mem_range.mpr hj
    exact (Finset.mem_filter.mp hmem).2
  have hge : ∀ j, τ ≤ j → j < k → 0 ≤ x j := by
    intro j hjτ hjk
    by_contra hneg
    have hpj : p j := lt_of_not_ge hneg
    have hmem : j ∈ (Finset.range k).filter p :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjk, hpj⟩
    rw [hseg] at hmem
    exact absurd (Finset.mem_range.mp hmem) (not_lt.mpr hjτ)
  -- the negative block: `-x j` dominates the reflected arithmetic progression
  have hpiece1 : ∑ j ∈ Finset.range τ, 1 / max R |x j|
      ≤ ∑ m ∈ Finset.range k, 1 / max R (c * (m : ℝ)) := by
    have h1 : ∑ j ∈ Finset.range τ, 1 / max R |x j|
        ≤ ∑ j ∈ Finset.range τ, 1 / max R (c * (((τ - 1 - j : ℕ)) : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjτ : j < τ := Finset.mem_range.mp hj
      have hxj : x j < 0 := hlt j hjτ
      have habs : |x j| = -x j := abs_of_neg hxj
      have hiter := iterate_le hxmono j (τ - 1 - j) (by omega)
      have hjeq : j + (τ - 1 - j) = τ - 1 := by omega
      rw [hjeq] at hiter
      have hxτ1 : x (τ - 1) < 0 := hlt (τ - 1) (by omega)
      have hbound : c * (((τ - 1 - j : ℕ)) : ℝ) ≤ -x j := by linarith
      rw [habs]
      have hpos : 0 < max R (c * (((τ - 1 - j : ℕ)) : ℝ)) :=
        lt_of_lt_of_le hR (le_max_left _ _)
      have hle : max R (c * (((τ - 1 - j : ℕ)) : ℝ)) ≤ max R (-x j) :=
        max_le (le_max_left _ _) (le_trans hbound (le_max_right _ _))
      exact one_div_le_one_div_of_le hpos hle
    have hsub : ∑ m ∈ Finset.range τ, 1 / max R (c * (m : ℝ))
        ≤ ∑ m ∈ Finset.range k, 1 / max R (c * (m : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hτle)
      intro m hm hnot
      exact le_of_lt (div_pos one_pos (lt_of_lt_of_le hR (le_max_left _ _)))
    refine h1.trans ?_
    rw [Finset.sum_range_reflect (fun m : ℕ => 1 / max R (c * (m : ℝ))) τ]
    exact hsub
  -- the nonnegative block: `x (τ + i)` dominates `c * i`
  have hpiece2 : ∑ i ∈ Finset.range (k - τ), 1 / max R |x (τ + i)|
      ≤ ∑ m ∈ Finset.range k, 1 / max R (c * (m : ℝ)) := by
    have h1 : ∑ i ∈ Finset.range (k - τ), 1 / max R |x (τ + i)|
        ≤ ∑ i ∈ Finset.range (k - τ), 1 / max R (c * (i : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i < k - τ := Finset.mem_range.mp hi
      have hτi : τ + i < k := by omega
      have hbound : c * (i : ℝ) ≤ |x (τ + i)| := by
        rcases Nat.eq_zero_or_pos i with h0 | hpos
        · subst h0; simp
        · have hτk : τ < k := by omega
          have hxτ : 0 ≤ x τ := hge τ le_rfl hτk
          have hiter := iterate_le hxmono τ i hτi
          have hcx : c * (i : ℝ) ≤ x (τ + i) := by linarith
          exact hcx.trans (le_abs_self _)
      have hpos' : 0 < max R (c * (i : ℝ)) := lt_of_lt_of_le hR (le_max_left _ _)
      have hle : max R (c * (i : ℝ)) ≤ max R |x (τ + i)| :=
        max_le (le_max_left _ _) (le_trans hbound (le_max_right _ _))
      exact one_div_le_one_div_of_le hpos' hle
    have hsub : ∑ m ∈ Finset.range (k - τ), 1 / max R (c * (m : ℝ))
        ≤ ∑ m ∈ Finset.range k, 1 / max R (c * (m : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega : k - τ ≤ k))
      intro m hm hnot
      exact le_of_lt (div_pos one_pos (lt_of_lt_of_le hR (le_max_left _ _)))
    exact h1.trans hsub
  have hsplit : ∑ j ∈ Finset.range k, 1 / max R |x j|
      = ∑ j ∈ Finset.range τ, 1 / max R |x j|
        + ∑ i ∈ Finset.range (k - τ), 1 / max R |x (τ + i)| := by
    have h := Finset.sum_range_add (fun j : ℕ => 1 / max R |x j|) τ (k - τ)
    rw [show τ + (k - τ) = k from by omega] at h
    exact h
  have hlogmono : Real.log (k : ℝ) ≤ Real.log ((k : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; simp
    · exact Real.log_le_log (by exact_mod_cast hkpos) (by linarith)
  have hlogL : 0 ≤ Real.log ((k : ℝ) + 1) :=
    Real.log_nonneg (by have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith)
  have hfinal : 2 / R + 2 / c + (2 / c) * Real.log (k : ℝ)
      ≤ (2 / R + 2 / c + 1) * (1 + Real.log (k + 1)) := by
    have hcs : 2 / c ≤ 2 / R + 2 / c + 1 := by linarith
    have hBL : (2 / c) * Real.log (k : ℝ)
        ≤ (2 / R + 2 / c + 1) * Real.log ((k : ℝ) + 1) := by
      calc (2 / c) * Real.log (k:ℝ) ≤ (2 / c) * Real.log ((k : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hlogmono (le_of_lt h2c)
        _ ≤ (2 / R + 2 / c + 1) * Real.log ((k : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right hcs hlogL
    have hexp : (2 / R + 2 / c + 1) * (1 + Real.log (k + 1))
        = (2 / R + 2 / c + 1) + (2 / R + 2 / c + 1) * Real.log ((k : ℝ) + 1) := by ring
    rw [hexp]
    linarith
  calc ∑ j ∈ Finset.range k, 1 / ‖w j‖
      ≤ ∑ j ∈ Finset.range k, 1 / max R |x j| := hstep1
    _ = ∑ j ∈ Finset.range τ, 1 / max R |x j|
        + ∑ i ∈ Finset.range (k - τ), 1 / max R |x (τ + i)| := hsplit
    _ ≤ (1 / R + (1 / c) * (1 + Real.log k)) + (1 / R + (1 / c) * (1 + Real.log k)) :=
        add_le_add (le_trans hpiece1 (sum_inv_max_le hc hR k))
          (le_trans hpiece2 (sum_inv_max_le hc hR k))
    _ = 2 / R + 2 / c + (2 / c) * Real.log (k : ℝ) := by ring
    _ ≤ (2 / R + 2 / c + 1) * (1 + Real.log (k + 1)) := hfinal

end Work.Parab.leftCoord
