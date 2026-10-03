/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow

/-!
# The deficit of the box-norm power on an interval: the geometric half

For `F : ℤ → ℂ` with `‖F‖_∞ ≤ 1`, supported in the interval `symIcc L = [-L, L]`, and for shift
sets `Q i`, the `2 ^ t`-th power of Peluse's box norm satisfies

`‖F‖^{2^t}_{□^t_Q(S)} ≤ 1 - ((2L+1) ∏_i |Q_i|²)⁻¹ · ∑_{h,h'} min (2L+1) (∑_i |h_i - h'_i|)`.

The proof is the elementary one: for fixed shifts `h, h'` the cube term
`∏_ω C^{|ω|} F (x + ω·h + (1-ω)·h')` is supported in the set of `x` with *all* corners
`x + ω·h + (1-ω)·h' ∈ [-L, L]`, which is an interval of length `2L+1 - ∑_i |h_i - h'_i|` (empty when
this is negative); the remaining `2^t-1` factors are bounded by `1`.  Hence the `x`-sum of a fixed
cube term has modulus at most `(2L+1) - min (2L+1) (∑_i |h_i - h'_i|)`, and the claim follows by the
triangle inequality and `∑_{h,h'} (2L+1) = (∏_i |Q_i|)² (2L+1)`.

## Main results

* `Work.Peluse.Ulower.cubeTerm_tsum_norm_le` : the single-corner-pair estimate;
* `Work.Peluse.Ulower.boxNormPow_le_one_sub_deficit` : the deficit bound;
* `Work.Peluse.Ulower.boxNormPow_le_one_sub_v2_of_children` : the assembly, from the three
  one-dimensional arithmetic inputs.
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-! ## Cardinalities -/

lemma symIcc_card (L : ℕ) : (Work.Peluse.symIcc L).card = 2 * L + 1 := by
  rw [Work.Peluse.symIcc, Int.card_Icc]
  omega

lemma card_arithIcc_of_ne_zero {c₀ : ℤ} (hc₀ : c₀ ≠ 0) (D : ℕ) :
    (Work.Peluse.arithIcc c₀ D).card = D := by
  rw [Work.Peluse.arithIcc, Finset.card_image_of_injOn]
  · rw [Nat.card_Icc]
    simp
  · intro a _ b _ hab
    have h : c₀ * (a : ℤ) = c₀ * (b : ℤ) := hab
    have h2 : (a : ℤ) = (b : ℤ) := mul_left_cancel₀ hc₀ h
    exact_mod_cast h2

/-- `((m : ℤ) - k).toNat = m - min m k`. -/
lemma int_toNat_sub_eq (m k : ℕ) : ((m : ℤ) - (k : ℤ)).toNat = m - min m k := by
  have h : ((((m : ℤ) - (k : ℤ)).toNat : ℕ) : ℤ) = ((m - min m k : ℕ) : ℤ) := by
    rcases lt_or_ge k m with hlt | hle
    · rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ (m : ℤ) - (k : ℤ)),
        min_eq_right (by omega : k ≤ m)]
      omega
    · rw [Int.toNat_of_nonpos (by omega : (m : ℤ) - (k : ℤ) ≤ 0),
        min_eq_left (by omega : m ≤ k)]
      omega
  exact_mod_cast h

/-! ## Corner shifts versus the coordinatewise maxima and minima -/

private lemma norm_star_iterate (n : ℕ) (z : ℂ) : ‖(star^[n]) z‖ = ‖z‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', norm_star, ih]

private lemma star_iterate_zero (n : ℕ) : (star^[n]) (0 : ℂ) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih]; simp

lemma cornerShift_le_sum_max {t : ℕ} (h h' : Fin t → ℤ) (ω : Fin t → Bool) :
    Work.Peluse.cornerShift h h' ω ≤ ∑ i, max (h i) (h' i) := by
  rw [Work.Peluse.cornerShift]
  refine Finset.sum_le_sum (fun i _ => ?_)
  split
  · exact le_max_left _ _
  · exact le_max_right _ _

lemma sum_min_le_cornerShift {t : ℕ} (h h' : Fin t → ℤ) (ω : Fin t → Bool) :
    (∑ i, min (h i) (h' i)) ≤ Work.Peluse.cornerShift h h' ω := by
  rw [Work.Peluse.cornerShift]
  refine Finset.sum_le_sum (fun i _ => ?_)
  split
  · exact min_le_left _ _
  · exact min_le_right _ _

lemma exists_cornerShift_eq_sum_max {t : ℕ} (h h' : Fin t → ℤ) :
    ∃ ω : Fin t → Bool, Work.Peluse.cornerShift h h' ω = ∑ i, max (h i) (h' i) := by
  refine ⟨fun i => decide (h' i ≤ h i), ?_⟩
  rw [Work.Peluse.cornerShift]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hc : h' i ≤ h i
  · rw [decide_eq_true_eq.mpr hc]
    simp [max_eq_left hc]
  · rw [decide_eq_false_iff_not.mpr hc]
    simp [max_eq_right (le_of_not_ge hc)]

lemma exists_cornerShift_eq_sum_min {t : ℕ} (h h' : Fin t → ℤ) :
    ∃ ω : Fin t → Bool, Work.Peluse.cornerShift h h' ω = ∑ i, min (h i) (h' i) := by
  refine ⟨fun i => decide (h i ≤ h' i), ?_⟩
  rw [Work.Peluse.cornerShift]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hc : h i ≤ h' i
  · rw [decide_eq_true_eq.mpr hc]
    simp [min_eq_left hc]
  · rw [decide_eq_false_iff_not.mpr hc]
    simp [min_eq_right (le_of_not_ge hc)]

/-- `∑_i max (h i) (h' i) - ∑_i min (h i) (h' i) = ∑_i |h i - h' i|`. -/
lemma sum_max_sub_sum_min {t : ℕ} (h h' : Fin t → ℤ) :
    (∑ i, max (h i) (h' i)) - (∑ i, min (h i) (h' i))
      = ((∑ i : Fin t, (h i - h' i).natAbs : ℕ) : ℤ) := by
  have key2 : ∀ i : Fin t, max (h i) (h' i) - min (h i) (h' i) = |h i - h' i| := by
    intro i
    rw [max_sub_min_eq_abs, abs_sub_comm]
  rw [← Finset.sum_sub_distrib]
  have hcast : ((∑ i : Fin t, (h i - h' i).natAbs : ℕ) : ℤ) = ∑ i : Fin t, |h i - h' i| := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => Int.natCast_natAbs _)
  rw [hcast]
  exact Finset.sum_congr rfl (fun i _ => key2 i)

/-- The cardinality of the interval to which the lower corner `x` is confined by the cube with
shifts `h, h'`:  it is at most `2L+1 - min (2L+1) (∑_i |h i - h' i|)`. -/
lemma card_cornerIcc_le {t : ℕ} (h h' : Fin t → ℤ) (L : ℕ) :
    (Finset.Icc (-(L : ℤ) - ∑ i, min (h i) (h' i))
        ((L : ℤ) - ∑ i, max (h i) (h' i))).card
      ≤ 2 * L + 1 - min (2 * L + 1) (∑ i : Fin t, (h i - h' i).natAbs) := by
  rw [Int.card_Icc]
  have hlen : (L : ℤ) - (∑ i, max (h i) (h' i)) + 1 - (-(L : ℤ) - ∑ i, min (h i) (h' i))
      = ((2 * L + 1 : ℕ) : ℤ) - ((∑ i : Fin t, (h i - h' i).natAbs : ℕ) : ℤ) := by
    have h1 : ((2 * L + 1 : ℕ) : ℤ) = 2 * (L : ℤ) + 1 := by push_cast; ring
    have h2 := sum_max_sub_sum_min h h'
    rw [h1]
    linarith
  rw [hlen, int_toNat_sub_eq]

/-! ## The pair-min sums -/

/-- The total, over all pairs of shift tuples, of `min n (∑_i |h_i - h'_i|)`. -/
def pairMinSum (t : ℕ) (Q : Fin t → Finset ℤ) (n : ℕ) : ℕ :=
  ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i}, ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
    min n (∑ i : Fin t, ((h i).1 - (h' i).1).natAbs)

/-- The same total, evaluated in `ℝ`. -/
def pairMinSumR (t : ℕ) (Q : Fin t → Finset ℤ) (n : ℕ) : ℝ :=
  ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i}, ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
    ((min n (∑ i : Fin t, ((h i).1 - (h' i).1).natAbs) : ℕ) : ℝ)

lemma pairMinSumR_eq (t : ℕ) (Q : Fin t → Finset ℤ) (n : ℕ) :
    pairMinSumR t Q n = (pairMinSum t Q n : ℝ) := by
  rw [pairMinSumR, pairMinSum]
  push_cast
  rfl

/-! ## The single-corner-pair bound -/

/-- The modulus of a cube-term product is at most `1`. -/
lemma norm_cubeTerm_le {t : ℕ} {F : ℤ → ℂ} (hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1)
    (h h' : Fin t → ℤ) (x : ℤ) :
    ‖∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω]) (F (x + Work.Peluse.cornerShift h h' ω))‖
      ≤ 1 := by
  rw [norm_prod]
  calc ∏ ω : Fin t → Bool, ‖(star^[Work.Peluse.weight ω]) (F (x + Work.Peluse.cornerShift h h' ω))‖
      ≤ ∏ _ω : Fin t → Bool, (1 : ℝ) :=
        Finset.prod_le_prod₀ (fun ω _ => norm_nonneg _) (fun ω _ => by
          rw [norm_star_iterate]; exact hF1 _)
    _ = 1 := by simp

/-- **The single-corner-pair bound.**  For fixed shift tuples `h, h'` the `x`-sum of the cube term
has modulus at most `(2L+1) - min (2L+1) (∑_i |h_i - h'_i|)`:  all the corners must lie in
`[-L, L]`, which confines `x` to an interval of that length (empty when the length is negative). -/
theorem cubeTerm_tsum_norm_le {t : ℕ} (Q : Fin t → Finset ℤ) (L : ℕ) {F : ℤ → ℂ}
    (hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1) (hFspan : ∀ x : ℤ, x ∉ Work.Peluse.symIcc L → F x = 0)
    (h h' : (i : Fin t) → {x : ℤ // x ∈ Q i}) :
    ‖∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
        (F (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖
      ≤ ((2 * L + 1 - min (2 * L + 1) (∑ i : Fin t, ((h i).1 - (h' i).1).natAbs) : ℕ) : ℝ) := by
  classical
  obtain ⟨ωmax, hωmax⟩ := exists_cornerShift_eq_sum_max (fun i => (h i).1) (fun i => (h' i).1)
  obtain ⟨ωmin, hωmin⟩ := exists_cornerShift_eq_sum_min (fun i => (h i).1) (fun i => (h' i).1)
  have hvanish : ∀ x : ℤ,
      x ∉ Finset.Icc (-(L : ℤ) - ∑ i, min ((h i).1) ((h' i).1))
        ((L : ℤ) - ∑ i, max ((h i).1) ((h' i).1)) →
      (∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
        (F (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))) = 0 := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    have hx' : x < -(L : ℤ) - ∑ i, min ((h i).1) ((h' i).1)
        ∨ (L : ℤ) - ∑ i, max ((h i).1) ((h' i).1) < x := by
      by_contra hcon
      push Not at hcon
      exact hx ⟨hcon.1, hcon.2⟩
    rcases hx' with hx | hx
    · refine Finset.prod_eq_zero (Finset.mem_univ ωmin) ?_
      rw [hωmin]
      have hzero : F (x + ∑ i, min ((h i).1) ((h' i).1)) = 0 := by
        refine hFspan _ ?_
        rw [Work.Peluse.symIcc, Finset.mem_Icc]
        intro hcon
        omega
      rw [hzero, star_iterate_zero]
    · refine Finset.prod_eq_zero (Finset.mem_univ ωmax) ?_
      rw [hωmax]
      have hzero : F (x + ∑ i, max ((h i).1) ((h' i).1)) = 0 := by
        refine hFspan _ ?_
        rw [Work.Peluse.symIcc, Finset.mem_Icc]
        intro hcon
        omega
      rw [hzero, star_iterate_zero]
  rw [tsum_eq_sum hvanish]
  calc ‖∑ x ∈ Finset.Icc (-(L : ℤ) - ∑ i, min ((h i).1) ((h' i).1))
          ((L : ℤ) - ∑ i, max ((h i).1) ((h' i).1)),
        ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (F (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖
      ≤ ∑ x ∈ Finset.Icc (-(L : ℤ) - ∑ i, min ((h i).1) ((h' i).1))
          ((L : ℤ) - ∑ i, max ((h i).1) ((h' i).1)),
        ‖∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (F (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _x ∈ Finset.Icc (-(L : ℤ) - ∑ i, min ((h i).1) ((h' i).1))
          ((L : ℤ) - ∑ i, max ((h i).1) ((h' i).1)), (1 : ℝ) :=
        Finset.sum_le_sum (fun x _ => norm_cubeTerm_le hF1 _ _ x)
    _ = ((Finset.Icc (-(L : ℤ) - ∑ i, min ((h i).1) ((h' i).1))
          ((L : ℤ) - ∑ i, max ((h i).1) ((h' i).1))).card : ℝ) := by simp
    _ ≤ ((2 * L + 1 - min (2 * L + 1) (∑ i : Fin t, ((h i).1 - (h' i).1).natAbs) : ℕ) : ℝ) := by
        exact_mod_cast card_cornerIcc_le (fun i => (h i).1) (fun i => (h' i).1) L

/-- The elementary real identity behind the deficit bound. -/
lemma deficit_alg (n c P : ℝ) (hn : n ≠ 0) (hc : c ≠ 0) :
    n⁻¹ * c⁻¹ * c⁻¹ * (c ^ 2 * n - P) = 1 - (n * c ^ 2)⁻¹ * P := by
  field_simp

/-! ## The deficit bound -/

/-- **The deficit bound.**  For `‖F‖_∞ ≤ 1` supported in `symIcc L` and arbitrary shift sets `Q i`,

`‖F‖^{2^t}_{□^t_Q([-L,L])} ≤ 1 - ((2L+1) ∏_i |Q_i|²)⁻¹ · ∑_{h,h'} min (2L+1) (∑_i |h_i - h'_i|)`. -/
theorem boxNormPow_le_one_sub_deficit {t : ℕ} (Q : Fin t → Finset ℤ) (hQ : ∀ i, (Q i).Nonempty)
    (L : ℕ) {F : ℤ → ℂ} (hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1)
    (hFspan : ∀ x : ℤ, x ∉ Work.Peluse.symIcc L → F x = 0) :
    Work.Peluse.boxNormPow t Q (Work.Peluse.symIcc L) F ≤
      1 - (((2 * L + 1 : ℕ) : ℝ) * (∏ i : Fin t, ((Q i).card : ℝ)) ^ 2)⁻¹ *
            pairMinSumR t Q (2 * L + 1) := by
  classical
  have hcardα : (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ)
      = ∏ i : Fin t, ((Q i).card : ℝ) := by
    rw [Fintype.card_pi]
    push_cast
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Fintype.card_coe]
  have hcast : ∀ h h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
      (((2 * L + 1 - min (2 * L + 1) (∑ i : Fin t, ((h i).1 - (h' i).1).natAbs) : ℕ) : ℝ))
        = ((2 * L + 1 : ℕ) : ℝ)
          - ((min (2 * L + 1) (∑ i : Fin t, ((h i).1 - (h' i).1).natAbs) : ℕ) : ℝ) :=
    fun h h' => by rw [Nat.cast_sub (min_le_left _ _)]
  have hstep : ∀ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
      ‖∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (F (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖
      ≤ ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
          (((2 * L + 1 - min (2 * L + 1)
            (∑ i : Fin t, ((h i).1 - (h' i).1).natAbs) : ℕ) : ℝ)) := by
    intro h
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum (fun h' _ => cubeTerm_tsum_norm_le Q L hF1 hFspan h h')
  have hinner : ∀ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
      (∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
          (((2 * L + 1 - min (2 * L + 1)
            (∑ i : Fin t, ((h i).1 - (h' i).1).natAbs) : ℕ) : ℝ)))
        = (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) * ((2 * L + 1 : ℕ) : ℝ)
          - ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
              ((min (2 * L + 1)
                (∑ i : Fin t, ((h i).1 - (h' i).1).natAbs) : ℕ) : ℝ) := by
    intro h
    rw [Finset.sum_congr rfl (fun h' _ => hcast h h'), Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  set R : ℂ := ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
      ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (F (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)) with hR
  have hRawb : ‖R‖ ≤ (∏ i : Fin t, ((Q i).card : ℝ)) ^ 2 * ((2 * L + 1 : ℕ) : ℝ)
        - pairMinSumR t Q (2 * L + 1) := by
    rw [hR]
    calc ‖∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
          ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
            ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
              (F (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖
        ≤ ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
            ‖∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
              ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
                (F (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
            ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
              (((2 * L + 1 - min (2 * L + 1)
                (∑ i : Fin t, ((h i).1 - (h' i).1).natAbs) : ℕ) : ℝ)) :=
          Finset.sum_le_sum (fun h _ => hstep h)
      _ = ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
            ((Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) * ((2 * L + 1 : ℕ) : ℝ)
              - ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
                  ((min (2 * L + 1)
                    (∑ i : Fin t, ((h i).1 - (h' i).1).natAbs) : ℕ) : ℝ)) :=
          Finset.sum_congr rfl (fun h _ => hinner h)
      _ = (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ)
            * ((Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) * ((2 * L + 1 : ℕ) : ℝ))
            - ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
                ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
                  ((min (2 * L + 1)
                    (∑ i : Fin t, ((h i).1 - (h' i).1).natAbs) : ℕ) : ℝ) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (∏ i : Fin t, ((Q i).card : ℝ)) ^ 2 * ((2 * L + 1 : ℕ) : ℝ)
            - pairMinSumR t Q (2 * L + 1) := by
          rw [hcardα, pairMinSumR]
          ring
  have hmain : Work.Peluse.boxNormPow t Q (Work.Peluse.symIcc L) F
      = ‖(((2 * L + 1 : ℕ) : ℂ))⁻¹ * (∏ i : Fin t, (((Q i).card : ℕ) : ℂ)⁻¹) *
          (∏ i : Fin t, (((Q i).card : ℕ) : ℂ)⁻¹) * R‖ := by
    rw [Work.Peluse.boxNormPow, Work.Peluse.boxSumPow, Work.Peluse.prodCubeSum_eq, symIcc_card]
  have hnormR : ‖(((2 * L + 1 : ℕ) : ℂ))⁻¹ * (∏ i : Fin t, (((Q i).card : ℕ) : ℂ)⁻¹) *
        (∏ i : Fin t, (((Q i).card : ℕ) : ℂ)⁻¹) * R‖
      = ((2 * L + 1 : ℕ) : ℝ)⁻¹ * (∏ i : Fin t, ((Q i).card : ℝ)⁻¹) *
        (∏ i : Fin t, ((Q i).card : ℝ)⁻¹) * ‖R‖ := by
    have hB : ‖∏ i : Fin t, (((Q i).card : ℕ) : ℂ)⁻¹‖
        = ∏ i : Fin t, ((Q i).card : ℝ)⁻¹ := by
      rw [norm_prod]
      exact Finset.prod_congr rfl (fun i _ => by rw [norm_inv, Complex.norm_natCast])
    simp only [norm_mul, norm_inv, Complex.norm_natCast, hB]
  have hnR0 : ((2 * L + 1 : ℕ) : ℝ) ≠ 0 := by
    have : (2 * L + 1 : ℕ) ≠ 0 := by omega
    exact_mod_cast this
  have hprod0 : (∏ i : Fin t, ((Q i).card : ℝ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun i _ => ?_)
    have : (Q i).card ≠ 0 := (hQ i).card_ne_zero
    exact_mod_cast this
  have hpos : (0 : ℝ) < ((2 * L + 1 : ℕ) : ℝ)⁻¹
      * (∏ i : Fin t, ((Q i).card : ℝ)⁻¹) * (∏ i : Fin t, ((Q i).card : ℝ)⁻¹) := by
    have h1 : (0 : ℝ) < ((2 * L + 1 : ℕ) : ℝ)⁻¹ := by
      rw [inv_pos]; exact_mod_cast (by omega : 0 < 2 * L + 1)
    have h2 : (0 : ℝ) < ∏ i : Fin t, ((Q i).card : ℝ)⁻¹ := by
      refine Finset.prod_pos (fun i _ => ?_)
      rw [inv_pos]
      exact_mod_cast (hQ i).card_pos
    exact mul_pos (mul_pos h1 h2) h2
  calc Work.Peluse.boxNormPow t Q (Work.Peluse.symIcc L) F
      = _ := hmain
    _ = ((2 * L + 1 : ℕ) : ℝ)⁻¹ * (∏ i : Fin t, ((Q i).card : ℝ)⁻¹) *
          (∏ i : Fin t, ((Q i).card : ℝ)⁻¹) * ‖R‖ := hnormR
    _ ≤ ((2 * L + 1 : ℕ) : ℝ)⁻¹ * (∏ i : Fin t, ((Q i).card : ℝ)⁻¹) *
          (∏ i : Fin t, ((Q i).card : ℝ)⁻¹) *
          ((∏ i : Fin t, ((Q i).card : ℝ)) ^ 2 * ((2 * L + 1 : ℕ) : ℝ)
            - pairMinSumR t Q (2 * L + 1)) :=
        mul_le_mul_of_nonneg_left hRawb (le_of_lt hpos)
    _ = 1 - (((2 * L + 1 : ℕ) : ℝ) * (∏ i : Fin t, ((Q i).card : ℝ)) ^ 2)⁻¹ *
            pairMinSumR t Q (2 * L + 1) := by
        rw [Finset.prod_inv_distrib]
        exact deficit_alg ((2 * L + 1 : ℕ) : ℝ) (∏ i : Fin t, ((Q i).card : ℝ))
          (pairMinSumR t Q (2 * L + 1)) hnR0 hprod0

/-! ## The arithmetic step and the assembly -/

/-- The elementary real inequality turning `8 · (pair sum) ≥ D^{2t} · min (m₀D) (4(2L+1))` into the
target deficit. -/
lemma deficit_arith_bound {t D L m0 : ℕ} (ht : 1 ≤ t) (hD : 2 ≤ D) :
    min (((t : ℝ) * (m0 : ℝ) * (D : ℝ)) / (4 * 2 ^ t * ((2 * L + 1 : ℕ) : ℝ)))
        (1 / (2 : ℝ) ^ t)
      ≤ (((2 * L + 1 : ℕ) : ℝ) * (D : ℝ) ^ (2 * t))⁻¹ *
          ((D : ℝ) ^ (2 * t) * (min (m0 * D) (4 * (2 * L + 1)) : ℝ) / 8) := by
  set s : ℝ := ((2 * L + 1 : ℕ) : ℝ) with hs
  have hs0 : 0 < s := by rw [hs]; exact_mod_cast (by omega : 0 < 2 * L + 1)
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hDt : (0 : ℝ) < (D : ℝ) ^ (2 * t) := pow_pos hD0 _
  have hDtne : (D : ℝ) ^ (2 * t) ≠ 0 := ne_of_gt hDt
  have hrhs : (s * (D : ℝ) ^ (2 * t))⁻¹ *
        ((D : ℝ) ^ (2 * t) * (min (m0 * D) (4 * (2 * L + 1)) : ℝ) / 8)
      = min ((m0 : ℝ) * (D : ℝ)) (4 * s) / (8 * s) := by
    have hcast1 : (4 : ℝ) * (2 * (L : ℝ) + 1) = 4 * s := by
      rw [hs]
      push_cast
      ring
    rw [hcast1]
    field_simp
  have hA' : ((t : ℝ) * (m0 : ℝ) * (D : ℝ)) / (4 * 2 ^ t * s)
      ≤ ((m0 : ℝ) * (D : ℝ)) / (8 * s) := by
    have h2t : (8 * (t : ℝ)) ≤ 4 * 2 ^ t := by
      have h := Nat.mul_le_pow (by norm_num : (2 : ℕ) ≠ 1) t
      have h' : (2 * t : ℝ) ≤ 2 ^ t := by exact_mod_cast h
      linarith
    have hnn : (0 : ℝ) ≤ (m0 : ℝ) * (D : ℝ) * s := by positivity
    have hmul := mul_le_mul_of_nonneg_right h2t hnn
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hmul]
  have hB' : (1 : ℝ) / 2 ^ t ≤ 1 / 2 := by
    have h2t : (2 : ℝ) ≤ 2 ^ t := by
      have h : 2 ^ 1 ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
      have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ t := by exact_mod_cast h
      simpa using h2
    exact one_div_le_one_div_of_le (by norm_num) h2t
  rw [hrhs]
  have hmin2 : min ((m0 : ℝ) * (D : ℝ)) (4 * s) / (8 * s)
      = min (((m0 : ℝ) * (D : ℝ)) / (8 * s)) (1 / 2) := by
    have h4 : (4 * s) / (8 * s) = 1 / 2 := by
      rw [mul_div_mul_right 4 8 hsne]
      norm_num
    rw [← min_div_div_right (c := 8 * s) (by linarith [hs0]), h4]
  rw [hmin2]
  exact min_le_min hA' hB'

/-- **The assembly.** -/
theorem boxNormPow_le_one_sub_v2_of_children
    (hA1 : ∀ {D m0 n : ℕ}, 2 ≤ D →
      D ^ 2 * min (m0 * D) (4 * n)
        ≤ 8 * (∑ a ∈ Finset.Icc 1 D, ∑ b ∈ Finset.Icc 1 D, min n (m0 * Nat.dist a b)))
    (hA2 : ∀ (c₀ : ℤ), c₀ ≠ 0 → ∀ (D n : ℕ),
      (∑ a ∈ Work.Peluse.arithIcc c₀ D, ∑ b ∈ Work.Peluse.arithIcc c₀ D, min n ((a - b).natAbs))
        = ∑ a ∈ Finset.Icc 1 D, ∑ b ∈ Finset.Icc 1 D, min n (c₀.natAbs * Nat.dist a b))
    (hB : ∀ (t : ℕ), 1 ≤ t → ∀ {c₀ : ℤ}, c₀ ≠ 0 → ∀ (D n : ℕ),
      D ^ (2 * (t - 1)) * (∑ a ∈ Work.Peluse.arithIcc c₀ D, ∑ b ∈ Work.Peluse.arithIcc c₀ D,
          min n ((a - b).natAbs))
        ≤ pairMinSum t (fun _ : Fin t => Work.Peluse.arithIcc c₀ D) n)
    (t : ℕ) (ht : 1 ≤ t) {c₀ : ℤ} (hc₀ : c₀ ≠ 0) {D L : ℕ} (hD : 2 ≤ D) {F : ℤ → ℂ}
    (hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1) (hFspan : ∀ x : ℤ, x ∉ Work.Peluse.symIcc L → F x = 0) :
    Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc c₀ D) (Work.Peluse.symIcc L) F
      ≤ 1 - min (((t : ℝ) * |(c₀ : ℝ)| * (D : ℝ)) / (4 * 2 ^ t * ((2 * L + 1 : ℕ) : ℝ)))
              (1 / (2 : ℝ) ^ t) := by
  classical
  set Q : Fin t → Finset ℤ := fun _ => Work.Peluse.arithIcc c₀ D with hQdef
  have hQmem : ∀ i : Fin t, c₀ ∈ Q i := by
    intro i
    rw [hQdef]
    exact Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, by ring⟩
  have hQne : ∀ i : Fin t, (Q i).Nonempty := fun i => ⟨c₀, hQmem i⟩
  have hcardQ : ∀ i : Fin t, ((Q i).card : ℝ) = (D : ℝ) := by
    intro i
    have h := card_arithIcc_of_ne_zero (c₀ := c₀) hc₀ D
    rw [hQdef]
    simp only []
    exact_mod_cast h
  have hprod : (∏ i : Fin t, ((Q i).card : ℝ)) = (D : ℝ) ^ t := by
    rw [Finset.prod_congr rfl (fun i _ => hcardQ i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  -- the pair-sum lower bound
  have hpair : (D : ℝ) ^ (2 * t) * (min (c₀.natAbs * D) (4 * (2 * L + 1)) : ℝ)
      ≤ 8 * (pairMinSum t Q (2 * L + 1) : ℝ) := by
    have hA1' := hA1 (D := D) (m0 := c₀.natAbs) (n := 2 * L + 1) hD
    have hA2' := hA2 c₀ hc₀ D (2 * L + 1)
    have hB' := hB t ht hc₀ D (2 * L + 1)
    have hB'' : D ^ (2 * (t - 1)) * (∑ a ∈ Finset.Icc 1 D, ∑ b ∈ Finset.Icc 1 D,
          min (2 * L + 1) (c₀.natAbs * Nat.dist a b))
        ≤ pairMinSum t Q (2 * L + 1) := by
      rw [hQdef]
      rw [← hA2']
      exact hB'
    have hchain : D ^ (2 * t) * min (c₀.natAbs * D) (4 * (2 * L + 1))
        ≤ 8 * pairMinSum t Q (2 * L + 1) := by
      have h1 : D ^ (2 * (t - 1)) * (D ^ 2 * min (c₀.natAbs * D) (4 * (2 * L + 1)))
          ≤ D ^ (2 * (t - 1)) * (8 * (∑ a ∈ Finset.Icc 1 D, ∑ b ∈ Finset.Icc 1 D,
              min (2 * L + 1) (c₀.natAbs * Nat.dist a b))) :=
        Nat.mul_le_mul_left _ hA1'
      have h3 : 8 * (D ^ (2 * (t - 1)) * (∑ a ∈ Finset.Icc 1 D, ∑ b ∈ Finset.Icc 1 D,
              min (2 * L + 1) (c₀.natAbs * Nat.dist a b)))
          ≤ 8 * pairMinSum t Q (2 * L + 1) := Nat.mul_le_mul_left 8 hB''
      have hpow : D ^ (2 * t) = D ^ (2 * (t - 1)) * D ^ 2 := by
        rw [← pow_add]
        congr 1
        omega
      calc D ^ (2 * t) * min (c₀.natAbs * D) (4 * (2 * L + 1))
          = D ^ (2 * (t - 1)) * (D ^ 2 * min (c₀.natAbs * D) (4 * (2 * L + 1))) := by
            rw [hpow]; ring
        _ ≤ D ^ (2 * (t - 1)) * (8 * (∑ a ∈ Finset.Icc 1 D, ∑ b ∈ Finset.Icc 1 D,
              min (2 * L + 1) (c₀.natAbs * Nat.dist a b))) := h1
        _ = 8 * (D ^ (2 * (t - 1)) * (∑ a ∈ Finset.Icc 1 D, ∑ b ∈ Finset.Icc 1 D,
              min (2 * L + 1) (c₀.natAbs * Nat.dist a b))) := by ring
        _ ≤ 8 * pairMinSum t Q (2 * L + 1) := h3
    exact_mod_cast hchain
  -- the deficit bound of the box-norm power
  have hdef := boxNormPow_le_one_sub_deficit Q hQne L hF1 hFspan
  have hdef' : Work.Peluse.boxNormPow t Q (Work.Peluse.symIcc L) F
      ≤ 1 - (((2 * L + 1 : ℕ) : ℝ) * (D : ℝ) ^ (2 * t))⁻¹ *
            (pairMinSum t Q (2 * L + 1) : ℝ) := by
    rw [hprod, pairMinSumR_eq] at hdef
    rw [show ((D : ℝ) ^ t) ^ 2 = (D : ℝ) ^ (2 * t) by rw [← pow_mul]; ring_nf] at hdef
    exact hdef
  have hpos : (0 : ℝ) < (((2 * L + 1 : ℕ) : ℝ) * (D : ℝ) ^ (2 * t))⁻¹ := by
    rw [inv_pos]
    have h1 : (0 : ℝ) < ((2 * L + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * L + 1)
    have h2 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
    exact mul_pos h1 (pow_pos h2 _)
  have hstep2 : (((2 * L + 1 : ℕ) : ℝ) * (D : ℝ) ^ (2 * t))⁻¹ *
        ((D : ℝ) ^ (2 * t) * (min (c₀.natAbs * D) (4 * (2 * L + 1)) : ℝ) / 8)
      ≤ (((2 * L + 1 : ℕ) : ℝ) * (D : ℝ) ^ (2 * t))⁻¹ *
        (pairMinSum t Q (2 * L + 1) : ℝ) := by
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hpos)
    linarith [hpair]
  have hkey : min (((t : ℝ) * ((c₀.natAbs : ℕ) : ℝ) * (D : ℝ)) /
          (4 * 2 ^ t * ((2 * L + 1 : ℕ) : ℝ))) (1 / (2 : ℝ) ^ t)
      ≤ (((2 * L + 1 : ℕ) : ℝ) * (D : ℝ) ^ (2 * t))⁻¹ *
        (pairMinSum t Q (2 * L + 1) : ℝ) :=
    (deficit_arith_bound (t := t) (D := D) (L := L) (m0 := c₀.natAbs) ht hD).trans hstep2
  have habs : ((c₀.natAbs : ℕ) : ℝ) = |(c₀ : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [habs] at hkey
  linarith [hdef', hkey]

end

end Work.Peluse.Ulower
