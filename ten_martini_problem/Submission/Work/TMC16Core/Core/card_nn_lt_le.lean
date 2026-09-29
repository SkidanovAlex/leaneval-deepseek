import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.nnDist
import Submission.Work.TMC16Core.Trig.nn_mul_div_emod
import Submission.Work.TMC16Core.Trig.sum_emod_coprime
import Submission.Work.TMC16Core.Trig.nn_grid_min_transfer

/-!
# Counting the grid points `2x + k·(p/q)` near an integer

Proof of `Work.TMC16Core.Core.card_nn_lt_le`, by the two standard reductions:

* `k ↦ ((k : ℤ) * p) % q` is a bijection from `{1,…,q}` onto `{0,…,q-1}` (coprimality of `p`
  and `q`), so the cardinality of the sub-filter over `k` equals that over the residues `j`;
* the `q` points `a + j/q` (`j < q`) are `1/q`-spaced, so at most `2 r q + 1` of them can lie
  within distance `r` of an integer.
-/

namespace Work.TMC16Core.Core

open Work.TMC16Core.Basic

/-! ## Auxiliary facts about `nn` -/

/-- `nn w < r` if and only if `w` is within `r` of some integer. -/
private lemma nn_lt_iff_exists (w r : ℝ) : nn w < r ↔ ∃ m : ℤ, |w - (m : ℝ)| < r := by
  constructor
  · intro h; exact ⟨round w, by simpa [nn] using h⟩
  · rintro ⟨m, hm⟩
    have h := round_le w m
    simp only [nn]
    linarith

/-- For `-1/2 ≤ t < 3/2` the nearest integer rounding of `t` is `0` or `1`. -/
private lemma round_eq_zero_or_one {t : ℝ} (h1 : -(1 / 2 : ℝ) ≤ t) (h2 : t < 3 / 2) :
    round t = 0 ∨ round t = 1 := by
  rw [round_eq]
  rcases lt_or_ge (t + 1 / 2) 1 with h | h
  · left; exact Int.floor_eq_on_Ico 0 (t + 1 / 2) ⟨by linarith, by simpa using h⟩
  · right; exact Int.floor_eq_on_Ico 1 (t + 1 / 2) ⟨by linarith, by linarith⟩

/-- For `-1/2 ≤ t < 3/2`, `nn t = min |t| |t - 1|`. -/
private lemma nn_eq_min_abs {t : ℝ} (h1 : -(1 / 2 : ℝ) ≤ t) (h2 : t < 3 / 2) :
    nn t = min (|t|) (|t - 1|) := by
  have hle1 : nn t ≤ |t| := by
    have := round_le t 0
    simpa only [nn, Int.cast_zero, sub_zero] using this
  have hle2 : nn t ≤ |t - 1| := by
    have := round_le t 1
    simpa only [nn, Int.cast_one] using this
  rcases round_eq_zero_or_one h1 h2 with h | h
  · have hn : nn t = |t| := by rw [nn, h]; simp
    have hb : |t| ≤ |t - 1| := by rw [← hn]; exact hle2
    rw [hn]; exact (min_eq_left hb).symm
  · have hn : nn t = |t - 1| := by rw [nn, h]; simp
    have hb : |t - 1| ≤ |t| := by rw [← hn]; exact hle1
    rw [hn]; exact (min_eq_right hb).symm

/-- For `-1/2 ≤ t < 3/2`, `nn t < r` is `|t| < r` or `|t - 1| < r`. -/
private lemma nn_lt_iff_abs {t r : ℝ} (h1 : -(1 / 2 : ℝ) ≤ t) (h2 : t < 3 / 2) :
    nn t < r ↔ |t| < r ∨ |t - 1| < r := by
  rw [nn_eq_min_abs h1 h2, min_lt_iff]

/-! ## Counting the `1/q`-grid -/

/-- **Counting points of a `1/q`-grid near an integer.**  For `q > 0`, `r > 0` and an arbitrary
real `a`, at most `2 r q + 1` of the `q` points `a + j/q` (`j = 0, …, q-1`) are at distance
`< r` from an integer. -/
private lemma card_nn_grid {q : ℕ} (hq : 0 < q) (a r : ℝ) (hr : 0 < r) :
    ((Finset.range q).filter (fun j : ℕ => nn (a + (j : ℝ) / (q : ℝ)) < r)).card
      ≤ 2 * r * (q : ℝ) + 1 := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rcases lt_or_ge (1 / 2 : ℝ) r with hr2 | hr2
  · -- `r > 1/2`: the crude bound `card ≤ q` suffices
    have h1 : ((Finset.range q).filter (fun j : ℕ => nn (a + (j : ℝ) / (q : ℝ)) < r)).card
        ≤ q := by
      simpa using Finset.card_filter_le (Finset.range q)
        (fun j : ℕ => nn (a + (j : ℝ) / (q : ℝ)) < r)
    have h2 : (q : ℝ) ≤ 2 * r * (q : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (q : ℝ) * (2 * r - 1) := mul_nonneg (le_of_lt hqR) (by linarith)
      linarith
    calc ((Finset.range q).filter (fun j : ℕ => nn (a + (j : ℝ) / (q : ℝ)) < r)).card
        ≤ (q : ℝ) := by exact_mod_cast h1
      _ ≤ 2 * r * (q : ℝ) + 1 := h2
  · -- main case: `r ≤ 1/2`
    set s : ℝ := a - (round a : ℝ) with hsdef
    have hsabs : |s| ≤ 1 / 2 := by rw [hsdef]; simpa using abs_sub_round a
    have hsle : s ≤ 1 / 2 := (abs_le.mp hsabs).2
    have hsge : -(1 / 2 : ℝ) ≤ s := (abs_le.mp hsabs).1
    set C : ℝ := (q : ℝ) * (-r - s) with hCdef
    set D : ℝ := (q : ℝ) * (r - s) with hDdef
    -- the `nn`-condition is the two-interval condition `(C,D) ∪ (C+q,D+q)`
    have hpred : ∀ j : ℕ, j < q → (nn (a + (j : ℝ) / (q : ℝ)) < r ↔
        ((C < (j : ℝ) ∧ (j : ℝ) < D)
          ∨ (C + (q : ℝ) < (j : ℝ) ∧ (j : ℝ) < D + (q : ℝ)))) := by
      intro j hj
      have hshift : a + (j : ℝ) / (q : ℝ) = s + (j : ℝ) / (q : ℝ) + ((round a : ℤ) : ℝ) := by
        simp only [hsdef]; ring
      rw [hshift, nn_add_intCast]
      have ht1 : -(1 / 2 : ℝ) ≤ s + (j : ℝ) / (q : ℝ) := by
        have : 0 ≤ (j : ℝ) / (q : ℝ) := by positivity
        linarith
      have ht2 : s + (j : ℝ) / (q : ℝ) < 3 / 2 := by
        have hjq : (j : ℝ) / (q : ℝ) < 1 := by rw [div_lt_one hqR]; exact_mod_cast hj
        linarith
      rw [nn_lt_iff_abs ht1 ht2]
      have e1 : -r < s + (j : ℝ) / (q : ℝ) ↔ C < (j : ℝ) := by
        rw [hCdef, show -r < s + (j : ℝ) / (q : ℝ) ↔ -r - s < (j : ℝ) / (q : ℝ) by
              constructor <;> intro h <;> linarith, lt_div_iff₀ hqR]
        ring_nf
      have e2 : s + (j : ℝ) / (q : ℝ) < r ↔ (j : ℝ) < D := by
        rw [hDdef, show s + (j : ℝ) / (q : ℝ) < r ↔ (j : ℝ) / (q : ℝ) < r - s by
              constructor <;> intro h <;> linarith, div_lt_iff₀ hqR]
        ring_nf
      have e3 : -r < s + (j : ℝ) / (q : ℝ) - 1 ↔ C + (q : ℝ) < (j : ℝ) := by
        rw [hCdef, show -r < s + (j : ℝ) / (q : ℝ) - 1 ↔ 1 - r - s < (j : ℝ) / (q : ℝ) by
              constructor <;> intro h <;> linarith, lt_div_iff₀ hqR]
        ring_nf
      have e4 : s + (j : ℝ) / (q : ℝ) - 1 < r ↔ (j : ℝ) < D + (q : ℝ) := by
        rw [hDdef, show s + (j : ℝ) / (q : ℝ) - 1 < r ↔ (j : ℝ) / (q : ℝ) < 1 + r - s by
              constructor <;> intro h <;> linarith, div_lt_iff₀ hqR]
        ring_nf
      rw [abs_lt, abs_lt]
      constructor
      · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
        · exact Or.inl ⟨e1.mp ha, e2.mp hb⟩
        · exact Or.inr ⟨e3.mp ha, e4.mp hb⟩
      · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
        · exact Or.inl ⟨e1.mpr ha, e2.mpr hb⟩
        · exact Or.inr ⟨e3.mpr ha, e4.mpr hb⟩
    let P' : ℕ → Prop := fun j => (C < (j : ℝ) ∧ (j : ℝ) < D)
      ∨ (C + (q : ℝ) < (j : ℝ) ∧ (j : ℝ) < D + (q : ℝ))
    have hfilter : (Finset.range q).filter (fun j : ℕ => nn (a + (j : ℝ) / (q : ℝ)) < r)
        = (Finset.range q).filter P' := by
      apply Finset.filter_congr
      intro j hj
      exact hpred j (Finset.mem_range.mp hj)
    rw [hfilter]
    have hCD : C < D := by rw [hCdef, hDdef]; nlinarith [hqR, hr]
    -- the integers of `(C,D)` form the interval `[⌊C⌋+1, ⌈D⌉-1]`
    have hmemT : ∀ x : ℤ, x ∈ Finset.Icc (⌊C⌋ + 1) (⌈D⌉ - 1) ↔ C < (x : ℝ) ∧ (x : ℝ) < D := by
      intro x
      rw [Finset.mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(Int.floor_lt).mp (by omega), (Int.lt_ceil).mp (by omega)⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨h1', h2'⟩ : ⌊C⌋ < x ∧ x < ⌈D⌉ :=
          ⟨(Int.floor_lt).mpr h1, (Int.lt_ceil).mpr h2⟩
        exact ⟨by omega, by omega⟩
    -- the injection: a good `j < q` is either already in `(C,D)` or one period to the right
    let g : ℕ → ℤ := fun j => if (j : ℝ) < D then (j : ℤ) else (j : ℤ) - (q : ℤ)
    have himage : (((Finset.range q).filter P').image g) ⊆ Finset.Icc (⌊C⌋ + 1) (⌈D⌉ - 1) := by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      have hjP : P' j := (Finset.mem_filter.mp hj).2
      rw [hmemT]
      by_cases hD : (j : ℝ) < D
      · have hg : g j = (j : ℤ) := by simp only [g, if_pos hD]
        rw [hg]
        push_cast
        rcases hjP with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1, h2⟩
        · exact ⟨by linarith, hD⟩
      · have hg : g j = (j : ℤ) - (q : ℤ) := by simp only [g, if_neg hD]
        rw [hg]
        push_cast
        rcases hjP with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h2 hD
        · exact ⟨by linarith, by linarith⟩
    have hinj : Set.InjOn g ↑((Finset.range q).filter P') := by
      intro j₁ h1 j₂ h2 heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at h1 h2
      by_cases hD1 : (j₁ : ℝ) < D
      · by_cases hD2 : (j₂ : ℝ) < D
        · have : (j₁ : ℤ) = (j₂ : ℤ) := by simpa only [g, if_pos hD1, if_pos hD2] using heq
          exact_mod_cast this
        · exfalso
          have he : (j₁ : ℤ) = (j₂ : ℤ) - (q : ℤ) := by
            simpa only [g, if_pos hD1, if_neg hD2] using heq
          omega
      · by_cases hD2 : (j₂ : ℝ) < D
        · exfalso
          have he : (j₁ : ℤ) - (q : ℤ) = (j₂ : ℤ) := by
            simpa only [g, if_neg hD1, if_pos hD2] using heq
          omega
        · have he : (j₁ : ℤ) - (q : ℤ) = (j₂ : ℤ) - (q : ℤ) := by
            simpa only [g, if_neg hD1, if_neg hD2] using heq
          have : (j₁ : ℤ) = (j₂ : ℤ) := by omega
          exact_mod_cast this
    have hcard : ((Finset.range q).filter P').card
        ≤ (Finset.Icc (⌊C⌋ + 1) (⌈D⌉ - 1) : Finset ℤ).card := by
      rw [← Finset.card_image_of_injOn hinj]
      exact Finset.card_le_card himage
    have hz0 : 0 ≤ ⌈D⌉ - ⌊C⌋ - 1 := by
      have h1 : (⌊C⌋ : ℝ) < D := lt_of_le_of_lt (Int.floor_le C) hCD
      have h2 : ⌊C⌋ < ⌈D⌉ := Int.lt_ceil.mpr h1
      omega
    have hT : (((Finset.Icc (⌊C⌋ + 1) (⌈D⌉ - 1) : Finset ℤ)).card : ℝ) ≤ D - C + 1 := by
      rw [Int.card_Icc]
      have hcast : ((((⌈D⌉ - 1 + 1 - (⌊C⌋ + 1)).toNat : ℕ)) : ℝ)
          = ((⌈D⌉ - ⌊C⌋ - 1 : ℤ) : ℝ) := by
        rw [show (⌈D⌉ - 1 + 1 - (⌊C⌋ + 1) : ℤ) = ⌈D⌉ - ⌊C⌋ - 1 by omega]
        exact_mod_cast (Int.toNat_of_nonneg hz0)
      rw [hcast]
      push_cast
      have h1 : (⌈D⌉ : ℝ) < D + 1 := Int.ceil_lt_add_one D
      have h2 : C - 1 < (⌊C⌋ : ℝ) := by have := Int.lt_floor_add_one C; linarith
      linarith
    calc ((Finset.range q).filter P').card
        ≤ ((Finset.Icc (⌊C⌋ + 1) (⌈D⌉ - 1) : Finset ℤ).card : ℝ) := by exact_mod_cast hcard
      _ ≤ D - C + 1 := hT
      _ = 2 * r * (q : ℝ) + 1 := by rw [hCdef, hDdef]; ring

/-! ## Re-indexing along `k ↦ ((k : ℤ) * p) % q` -/

/-- For `q > 0` and `p` coprime to `q`, the cardinality of the sub-filter over `k ∈ {1,…,q}`
of a predicate of the residue `((k : ℤ) * p) % q` equals that over `j ∈ {0,…,q-1}`. -/
private lemma card_filter_emod_aux {q : ℕ} (hq : 0 < q) {p : ℤ} (hcop : Nat.Coprime p.natAbs q)
    (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.Icc 1 q).filter (fun k : ℕ => P ((((k : ℤ) * p) % (q : ℤ)).toNat))).card
      = ((Finset.range q).filter P).card := by
  have h := Work.TMC16Core.Trig.sum_emod_coprime hq hcop
    (fun z : ℤ => if P z.toNat then (1 : ℝ) else 0)
  simp only [Int.toNat_natCast] at h
  rw [Finset.card_filter, Finset.card_filter]
  apply Nat.cast_injective (R := ℝ)
  push_cast
  exact h

/-! ## The target lemma -/

/-- **Counting grid points near an integer.**  For `q > 0`, `p` coprime to `q` and `r > 0`, at
most `2 r q + 1` of the points `2x + k·(p/q)`, `k = 1..q`, lie within distance `r` of an integer:
the hypothesis `Nat.Coprime p.natAbs q` makes `k ↦ (k*p) % q` a bijection onto `{0,…,q-1}`, so the
`nn`-values are those of the `q`-point grid `s + j/q` (`s = fract (2x)`), which is `1/q`-spaced;
an arc of length `2r` on the circle contains at most `2 r q + 1` of them.  (Reduction: use
`Work.TMC16Core.Trig.nn_mul_div_emod` and `Work.TMC16Core.Trig.sum_emod_coprime`-style
re-indexing to replace `nn (2x + k p/q)` by `nn (s + j/q)`, then count integers `j ∈ [0,q)` with
`j/q` in an interval of length `2r`.) -/
theorem card_nn_lt_le {q : ℕ} (hq : 0 < q) {p : ℤ} (hcop : Nat.Coprime p.natAbs q) (x r : ℝ)
    (hr : 0 < r) :
    ((Finset.Icc 1 q).filter (fun k : ℕ =>
      Work.TMC16Core.Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) < r)).card
      ≤ 2 * r * (q : ℝ) + 1 := by
  set F : ℕ → Prop := fun j => Work.TMC16Core.Basic.nn (2 * x + (j : ℝ) / (q : ℝ)) < r with hF
  have hcongr : ((Finset.Icc 1 q).filter (fun k : ℕ =>
        Work.TMC16Core.Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) < r))
      = (Finset.Icc 1 q).filter (fun k : ℕ => F ((((k : ℤ) * p) % (q : ℤ)).toNat)) := by
    apply Finset.filter_congr
    intro k _
    simp only [hF]
    rw [Work.TMC16Core.Trig.nn_mul_div_emod' hq p x k]
  rw [hcongr, card_filter_emod_aux hq hcop F]
  exact card_nn_grid hq (2 * x) r hr

end Work.TMC16Core.Core
