import Mathlib
import Submission.Work.BG.S02

/-!
# Area BG: `s02_commonSupportSingleton`

A self-contained combinatorial / linear-algebra lemma about two "signed" finite linear
relations on a complex-valued vector `w`.

Let `A, B : Finset α`, `c, d : α → ℤ`, `w : α → ℂ`.  Assume

* `c` is nowhere zero on `A` and `d` nowhere zero on `B` (coefficients of the relations);
* `∑_{a∈A} c a ^ 2 ≤ 3` and `∑_{b∈B} d b ^ 2 ≤ 3` (the relations have **at most three
  terms**, and each coefficient is `±1`);
* `∑_{a∈A} c a * w a = 0` and `∑_{b∈B} d b * w b = 0` (two `ℂ`-linear relations);
* `w` is nowhere zero on `A ∪ B`;
* `∑_{s∈A∩B} c s * d s = 1` (the two relations "overlap with multiplicity one").

Then the common support `A ∩ B` is a **singleton** `{a₀}` and the corresponding product of
coefficients is `1`.

## Mathematical content (the full argument, all of it formalised below)

1. From `∑_{a∈A} c a ^ 2 ≤ 3` and `c a ≠ 0`, every `c a ^ 2` is a positive integer square
   bounded by a single term of the sum, hence `= 1`; so `c a = ±1` and `A.card ≤ 3`
   (`s02_csPmOneBound`).  Symmetrically for `d` on `B`.

2. On `S := A ∩ B` every product `c s * d s` is `±1`, so `∑_{S} c s * d s` is a sum of `±1`'s.
   Writing `T := {s ∈ S : c s * d s = -1}` one has `∑_{S} c s * d s = S.card - 2 * T.card`
   (`s02_csPmOneSumCount`).  With `∑_{S} c s * d s = 1` and `S.card ≤ 3` this forces
   `S.card ∈ {1, 3}` (and `S ≠ ∅`).

3. If `S.card = 3` then `A.card = B.card = 3`, so `A = S = B`; now the two relations are
   relations over the *same* index set `S`, and subtracting them gives
   `∑_{s∈S} (c s - d s) * w s = 0`.  Since `∑_{S} c s * d s = 1` picks out exactly one
   `s₀` with `c s₀ ≠ d s₀` (and `c s = d s` for all other `s`), the sum collapses to the
   single non-zero term `(c s₀ - d s₀) * w s₀`, a contradiction
   (`s02_threeElemContra`).

4. Hence `S.card = 1`, i.e. `S = {a₀}`, and `1 = ∑_{S} c s d s = c a₀ * d a₀`.
-/

namespace Work.BG

/-- **Bound on a signed support.**  If `f` is nowhere zero on `s` and `∑ a ∈ s, f a ^ 2 ≤ 3`,
then `s` has at most three elements and `f` takes only the values `±1` on `s`.

Each `f a ^ 2` is a single (non-negative) term of the sum, hence `≤ 3`; as it is a positive
integer square it equals `1`, so `f a = ±1`.  Counting the `s.card` summands each `≥ 1`
gives `s.card ≤ 3`. -/
theorem s02_csPmOneBound {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℤ)
    (hne : ∀ a ∈ s, f a ≠ 0) (h : ∑ a ∈ s, f a ^ 2 ≤ 3) :
    s.card ≤ 3 ∧ ∀ a ∈ s, f a = 1 ∨ f a = -1 := by
  have hle : ∀ a ∈ s, f a ^ 2 ≤ 3 := fun a ha =>
    le_trans (Finset.single_le_sum (fun i _ => sq_nonneg (f i)) ha) h
  have hsq : ∀ a ∈ s, f a ^ 2 = 1 := by
    intro a ha
    have hna : (f a).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hne a ha)
    have h1 : (1 : ℤ) ≤ ((f a).natAbs : ℤ) := by
      have : 1 ≤ (f a).natAbs := by omega
      exact_mod_cast this
    have h2 : (((f a).natAbs : ℤ)) ^ 2 ≤ 3 := by rw [Int.natAbs_sq]; exact hle a ha
    have h3 : ((f a).natAbs : ℤ) ≤ 1 := by
      by_contra hc; push Not at hc
      nlinarith [sq_nonneg (((f a).natAbs : ℤ) - 1)]
    have hk : (f a).natAbs = 1 := by omega
    rcases Int.natAbs_eq_iff.mp hk with hh | hh
    · rw [hh]; norm_num
    · rw [hh]; norm_num
  refine ⟨?_, fun a ha => sq_eq_one_iff.mp (hsq a ha)⟩
  have hge : ∀ a ∈ s, (1 : ℤ) ≤ f a ^ 2 := fun a ha => by rw [hsq a ha]
  have := Finset.card_nsmul_le_sum s (fun a => f a ^ 2) (1 : ℤ) hge
  rw [nsmul_eq_mul, mul_one] at this
  have : (s.card : ℤ) ≤ 3 := le_trans this h
  exact_mod_cast this

/-- **Sum of a `±1`-valued function.**  If `e a ∈ {1, -1}` for `a ∈ s` and `T` is the set of
`a ∈ s` with `e a = -1`, then `∑ a ∈ s, e a = (s.card : ℤ) - 2 * T.card`: the `+1` terms
contribute `s.card - T.card` and the `-1` terms contribute `-T.card`. -/
theorem s02_csPmOneSumCount {α : Type*} [DecidableEq α] (s : Finset α) (e : α → ℤ)
    (h : ∀ a ∈ s, e a = 1 ∨ e a = -1) :
    ∑ a ∈ s, e a = (s.card : ℤ) - 2 * ((s.filter (fun a => e a = -1)).card : ℤ) := by
  have hneg : ∀ a ∈ s.filter (fun a => e a = -1), e a = -1 := by
    intro a ha; exact (Finset.mem_filter.mp ha).2
  have hpos : ∀ a ∈ s.filter (fun a => ¬ (e a = -1)), e a = 1 := by
    intro a ha
    have hmem := Finset.mem_filter.mp ha
    rcases h a hmem.1 with hh | hh
    · exact hh
    · exact absurd hh hmem.2
  have h1 : ∑ a ∈ s.filter (fun a => e a = -1), e a
      = -(((s.filter (fun a => e a = -1)).card : ℤ)) := by
    rw [Finset.sum_congr rfl hneg, Finset.sum_const, nsmul_eq_mul]; ring
  have h2 : ∑ a ∈ s.filter (fun a => ¬ (e a = -1)), e a
      = (((s.filter (fun a => ¬ (e a = -1))).card : ℤ)) := by
    rw [Finset.sum_congr rfl hpos, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun a => e a = -1) e
  rw [h1, h2] at hsplit
  rw [← hsplit]
  have hcard := Finset.card_filter_add_card_filter_not (s := s) (fun a => e a = -1)
  have hcardZ : (((s.filter (fun a => e a = -1)).card : ℤ))
      + (((s.filter (fun a => ¬ (e a = -1))).card : ℤ)) = (s.card : ℤ) := by
    exact_mod_cast hcard
  linarith

/-- **The three-element obstruction.**  Let `s` carry two `±1`-valued coefficient functions
`c`, `d` and two relations `∑ c a * w a = 0`, `∑ d a * w a = 0` with `w` nowhere zero.  If
`s.card = 3` then `∑ a ∈ s, c a * d a ≠ 1`.

Indeed `c a * d a ∈ {±1}`, and `∑_{a∈s} c a * d a = 1` with three terms forces exactly one
`a₀ ∈ s` with `c a₀ ≠ d a₀` (the other two satisfy `c a = d a`).  Subtracting the two
relations gives `∑_{a∈s} (c a - d a) * w a = 0`, whose only non-zero term is
`(c a₀ - d a₀) * w a₀ = ±2 * w a₀ ≠ 0`, a contradiction. -/
theorem s02_threeElemContra {α : Type*} [DecidableEq α] (s : Finset α) (c d : α → ℤ) (w : α → ℂ)
    (hc : ∀ a ∈ s, c a = 1 ∨ c a = -1) (hd : ∀ a ∈ s, d a = 1 ∨ d a = -1)
    (hw : ∀ a ∈ s, w a ≠ 0)
    (hcs : ∑ a ∈ s, (c a : ℂ) * w a = 0) (hds : ∑ a ∈ s, (d a : ℂ) * w a = 0)
    (hcard : s.card = 3) :
    ∑ a ∈ s, c a * d a ≠ 1 := by
  intro h1
  have he : ∀ a ∈ s, c a * d a = 1 ∨ c a * d a = -1 := by
    intro a ha
    rcases hc a ha with h | h <;> rcases hd a ha with h' | h' <;> rw [h, h'] <;> norm_num
  have hcount : ∑ a ∈ s, c a * d a
      = (s.card : ℤ) - 2 * ((s.filter (fun a => c a * d a = -1)).card : ℤ) := by
    have hneg : ∀ a ∈ s.filter (fun a => c a * d a = -1), c a * d a = -1 := by
      intro a ha; exact (Finset.mem_filter.mp ha).2
    have hpos : ∀ a ∈ s.filter (fun a => ¬ (c a * d a = -1)), c a * d a = 1 := by
      intro a ha
      have hmem := Finset.mem_filter.mp ha
      rcases he a hmem.1 with hh | hh
      · exact hh
      · exact absurd hh hmem.2
    have e1 : ∑ a ∈ s.filter (fun a => c a * d a = -1), c a * d a
        = -(((s.filter (fun a => c a * d a = -1)).card : ℤ)) := by
      rw [Finset.sum_congr rfl hneg, Finset.sum_const, nsmul_eq_mul]; ring
    have e2 : ∑ a ∈ s.filter (fun a => ¬ (c a * d a = -1)), c a * d a
        = (((s.filter (fun a => ¬ (c a * d a = -1))).card : ℤ)) := by
      rw [Finset.sum_congr rfl hpos, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hsplit := Finset.sum_filter_add_sum_filter_not s (fun a => c a * d a = -1)
      (fun a => c a * d a)
    rw [e1, e2] at hsplit
    rw [← hsplit]
    have hcardf := Finset.card_filter_add_card_filter_not (s := s) (fun a => c a * d a = -1)
    have hcardZ : (((s.filter (fun a => c a * d a = -1)).card : ℤ))
        + (((s.filter (fun a => ¬ (c a * d a = -1))).card : ℤ)) = (s.card : ℤ) := by
      exact_mod_cast hcardf
    linarith
  have hTcard : (s.filter (fun a => c a * d a = -1)).card = 1 := by
    have : ((s.filter (fun a => c a * d a = -1)).card : ℤ) = 1 := by
      have h := hcount; rw [h1, hcard] at h; linarith
    omega
  obtain ⟨n, hn⟩ := Finset.card_eq_one.mp hTcard
  have hsub : ∑ a ∈ s, ((c a : ℂ) - (d a : ℂ)) * w a = 0 := by
    have hE : ∑ a ∈ s, ((c a : ℂ) - (d a : ℂ)) * w a
        = ∑ a ∈ s, (c a : ℂ) * w a - ∑ a ∈ s, (d a : ℂ) * w a := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [hE, hcs, hds, sub_zero]
  have hss : ∑ a ∈ s.filter (fun a => c a * d a = -1), ((c a : ℂ) - (d a : ℂ)) * w a
      = ∑ a ∈ s, ((c a : ℂ) - (d a : ℂ)) * w a := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro x hxs hxT
    have hxn : ¬ (c x * d x = -1) := fun hh => hxT (Finset.mem_filter.mpr ⟨hxs, hh⟩)
    rcases he x hxs with h | h
    · have hcd : c x = d x := by
        rcases hc x hxs with hc1 | hc1 <;> rcases hd x hxs with hd1 | hd1 <;>
          rw [hc1, hd1] at h ⊢ <;> omega
      rw [hcd]; ring
    · exact absurd h hxn
  have hcollapse : ∑ a ∈ s.filter (fun a => c a * d a = -1),
      ((c a : ℂ) - (d a : ℂ)) * w a = 0 := by rw [hss, hsub]
  rw [hn, Finset.sum_singleton] at hcollapse
  have hnT : c n * d n = -1 := by
    have : n ∈ s.filter (fun a => c a * d a = -1) := by rw [hn]; exact Finset.mem_singleton_self n
    exact (Finset.mem_filter.mp this).2
  have hns : n ∈ s := by
    have : n ∈ s.filter (fun a => c a * d a = -1) := by rw [hn]; exact Finset.mem_singleton_self n
    exact (Finset.mem_filter.mp this).1
  have hcne : (c n : ℂ) - (d n : ℂ) ≠ 0 := by
    intro hh
    have hcd : c n = d n := by exact_mod_cast (sub_eq_zero.mp hh)
    have : c n * c n = -1 := by rw [← hcd] at hnT; exact hnT
    rcases hc n hns with h | h <;> rw [h] at this <;> norm_num at this
  exact hcne (mul_eq_zero.mp hcollapse |>.resolve_right (hw n hns))

/-- **Common support is a singleton.**

Two signed relations `∑_{a∈A} c a * w a = 0` and `∑_{b∈B} d b * w b = 0` over finite
supports `A, B` of size at most `3` (with all coefficients `±1` and `w ≠ 0` on `A ∪ B`) can
overlap — in the sense `∑_{A∩B} c * d = 1` — only in a single point, where the product of
the two coefficients is `1`. -/
theorem s02_commonSupportSingleton {α : Type*} [DecidableEq α]
    (A B : Finset α) (c d : α → ℤ) (w : α → ℂ)
    (hcne : ∀ a ∈ A, c a ≠ 0) (hdne : ∀ a ∈ B, d a ≠ 0)
    (hc2 : ∑ a ∈ A, c a ^ 2 ≤ 3) (hd2 : ∑ a ∈ B, d a ^ 2 ≤ 3)
    (hcw : ∑ a ∈ A, (c a : ℂ) * w a = 0) (hdw : ∑ a ∈ B, (d a : ℂ) * w a = 0)
    (hw : ∀ a ∈ A ∪ B, w a ≠ 0)
    (hsum : ∑ a ∈ A ∩ B, c a * d a = 1) :
    ∃ a₀, a₀ ∈ A ∧ a₀ ∈ B ∧ A ∩ B = {a₀} ∧ c a₀ * d a₀ = 1 := by
  classical
  obtain ⟨hAcard, hc1⟩ := s02_csPmOneBound A c hcne hc2
  obtain ⟨hBcard, hd1⟩ := s02_csPmOneBound B d hdne hd2
  have hcS : ∀ a ∈ A ∩ B, c a = 1 ∨ c a = -1 :=
    fun a ha => hc1 a (Finset.mem_inter.mp ha).1
  have hdS : ∀ a ∈ A ∩ B, d a = 1 ∨ d a = -1 :=
    fun a ha => hd1 a (Finset.mem_inter.mp ha).2
  have heS : ∀ a ∈ A ∩ B, c a * d a = 1 ∨ c a * d a = -1 := by
    intro a ha
    rcases hcS a ha with h | h <;> rcases hdS a ha with h' | h' <;> rw [h, h'] <;> norm_num
  have hcount := s02_csPmOneSumCount (A ∩ B) (fun a => c a * d a) heS
  have hScard3 : (A ∩ B).card ≤ 3 :=
    le_trans (Finset.card_le_card Finset.inter_subset_left) hAcard
  have hSnonempty : (A ∩ B).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h] at hsum; simp at hsum
  have hodd : ((A ∩ B).card : ℤ)
      = 2 * (((A ∩ B).filter (fun a => c a * d a = -1)).card : ℤ) + 1 := by
    have h := hcount; rw [hsum] at h; linarith
  have hcases : (A ∩ B).card = 1 ∨ (A ∩ B).card = 3 := by
    have hge : 1 ≤ (A ∩ B).card := Finset.card_pos.mpr hSnonempty
    omega
  have hwS : ∀ a ∈ A ∩ B, w a ≠ 0 :=
    fun a ha => hw a (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp ha).1))
  rcases hcases with hcard1 | hcard3
  · obtain ⟨a₀, ha₀⟩ := Finset.card_eq_one.mp hcard1
    have hmem : a₀ ∈ A ∩ B := by rw [ha₀]; exact Finset.mem_singleton_self a₀
    refine ⟨a₀, (Finset.mem_inter.mp hmem).1, (Finset.mem_inter.mp hmem).2, ha₀, ?_⟩
    rw [ha₀, Finset.sum_singleton] at hsum; exact hsum
  · exfalso
    have hAeq : A ∩ B = A :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hBeq : A ∩ B = B :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    have hcw' : ∑ a ∈ A ∩ B, (c a : ℂ) * w a = 0 := by rw [hAeq]; exact hcw
    have hdw' : ∑ a ∈ A ∩ B, (d a : ℂ) * w a = 0 := by rw [hBeq]; exact hdw
    exact s02_threeElemContra (A ∩ B) c d w hcS hdS hwS hcw' hdw' hcard3 hsum

end Work.BG
