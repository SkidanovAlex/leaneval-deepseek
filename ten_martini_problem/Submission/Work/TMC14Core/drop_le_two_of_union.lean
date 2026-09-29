import Mathlib
import Submission.Work.TMC14Core.RatRot

/-!
# `drop_le_two_of_union`

A continuous antitone function `ρ : ℝ → ℝ` whose set of *non-integer* values on
an interval `(a,b)` is the trace of a union of **two** open intervals `(u,v) ∪ (w,z)`
can drop by at most `2` over `[a,b]`.

The proof is a counting argument.  If `ρ a - ρ b > 2` then the open interval
`(ρ b, ρ a)` contains two consecutive integers `n < n+1`.  Using the intermediate
value theorem together with antitonicity one produces points

`p1 < q1 < p2 < q2 < p3`

where `ρ q1 = n+1`, `ρ q2 = n` are integers, while `ρ p1`, `ρ p2`, `ρ p3`
are irrational (hence non-integers).  By the hypothesis `q1, q2 ∉ (u,v) ∪ (w,z)`
while `p1, p2, p3 ∈ (u,v) ∪ (w,z)`.  But a union of two intervals cannot realise
the alternating pattern `in/out/in/out/in`: two of the `pᵢ` lie in the same one of
the two intervals and the intervening `qⱼ` must then also lie in it, a contradiction.
-/

open Set

namespace Work.TMC14Core

/-- An irrational real number is never an integer (i.e. never of the form
`(k : ℝ)` for `k : ℤ`). -/
private lemma not_int_of_irrational {t : ℝ} (h : Irrational t) :
    t ∉ Set.range (fun k : ℤ => (k : ℝ)) := by
  rintro ⟨k, hk⟩
  exact h.ne_int k hk.symm

/-- A union of two open intervals cannot alternate "in / out / in / out / in":
if `p1,p2,p3 ∈ (u,v) ∪ (w,z)` and `q1,q2 ∉ (u,v) ∪ (w,z)` with
`p1 < q1 < p2 < q2 < p3`, then `False`. -/
private lemma no_alternation (u v w z p1 q1 p2 q2 p3 : ℝ)
    (h1 : p1 < q1) (h2 : q1 < p2) (h3 : p2 < q2) (h4 : q2 < p3)
    (hp1 : p1 ∈ Set.Ioo u v ∨ p1 ∈ Set.Ioo w z)
    (hp2 : p2 ∈ Set.Ioo u v ∨ p2 ∈ Set.Ioo w z)
    (hp3 : p3 ∈ Set.Ioo u v ∨ p3 ∈ Set.Ioo w z)
    (hq1 : ¬ (q1 ∈ Set.Ioo u v ∨ q1 ∈ Set.Ioo w z))
    (hq2 : ¬ (q2 ∈ Set.Ioo u v ∨ q2 ∈ Set.Ioo w z)) : False := by
  obtain ⟨hq1uv, hq1wz⟩ := not_or.mp hq1
  obtain ⟨hq2uv, hq2wz⟩ := not_or.mp hq2
  -- convexity of an interval: a point between two points of `Ioo s t` lies in it
  have conv : ∀ {s t x y z' : ℝ}, x ∈ Set.Ioo s t → z' ∈ Set.Ioo s t →
      x < y → y < z' → y ∈ Set.Ioo s t := by
    intro s t x y z' hx hz' hxy hyz'
    exact ⟨hx.1.trans hxy, hyz'.trans hz'.2⟩
  rcases hp2 with hp2 | hp2
  · rcases hp1 with hp1 | hp1
    · exact hq1uv (conv hp1 hp2 h1 h2)
    · rcases hp3 with hp3 | hp3
      · exact hq2uv (conv hp2 hp3 h3 h4)
      · exact hq1wz (conv hp1 hp3 h1 ((h2.trans h3).trans h4))
  · rcases hp1 with hp1 | hp1
    · rcases hp3 with hp3 | hp3
      · exact hq1uv (conv hp1 hp3 h1 ((h2.trans h3).trans h4))
      · exact hq2wz (conv hp2 hp3 h3 h4)
    · exact hq1wz (conv hp1 hp2 h1 h2)

theorem drop_le_two_of_union (ρ : ℝ → ℝ) (hcont : Continuous ρ) (hanti : Antitone ρ)
    (a b u v w z : ℝ) (hab : a ≤ b)
    (hsub : ∀ E ∈ Set.Ioo a b, ρ E ∉ Set.range (fun k : ℤ => (k : ℝ)) ↔
      (E ∈ Set.Ioo u v ∨ E ∈ Set.Ioo w z)) :
    ρ a - ρ b ≤ 2 := by
  by_contra h0
  have h0 : 2 < ρ a - ρ b := not_le.mp h0
  -- antitonicity, in the contrapositive form we need
  have hmono : ∀ {x y : ℝ}, ρ x < ρ y → y < x := by
    intro x y hxy
    by_contra hcon
    exact absurd hxy (not_lt_of_ge (hanti (not_lt.mp hcon)))
  -- intermediate value theorem, localised to an open interval
  have ivt : ∀ x0 x1 c : ℝ, x0 ≤ x1 → ρ x1 < c → c < ρ x0 →
      ∃ y ∈ Set.Ioo x0 x1, ρ y = c := by
    intro x0 x1 c hle h1 h2
    obtain ⟨y, hy, hyc⟩ :=
      (intermediate_value_Icc' hle hcont.continuousOn) ⟨le_of_lt h1, le_of_lt h2⟩
    rw [Set.mem_Icc] at hy
    obtain ⟨hx0, hx1⟩ := hy
    refine ⟨y, ⟨?_, ?_⟩, hyc⟩
    · rcases lt_or_eq_of_le hx0 with hlt | heq
      · exact hlt
      · exfalso; rw [heq] at h2; rw [hyc] at h2; exact lt_irrefl c h2
    · rcases lt_or_eq_of_le hx1 with hlt | heq
      · exact hlt
      · exfalso; rw [← heq] at h1; rw [hyc] at h1; exact lt_irrefl c h1
  -- the two consecutive integers `n`, `n+1` inside `(ρ b, ρ a)`
  let n : ℤ := ⌊ρ b⌋ + 1
  have hb_lt_n : ρ b < (n : ℝ) := by
    have h := (Int.floor_le_iff (z := ⌊ρ b⌋) (a := ρ b)).mp le_rfl
    simp only [n]; push_cast; linarith
  have hn_le : (n : ℝ) ≤ ρ b + 1 := by
    have h := Int.floor_le (ρ b)
    simp only [n]; push_cast; linarith
  have hn1 : (n : ℝ) + 1 < ρ a := by linarith
  have hb_lt_n1 : ρ b < (n : ℝ) + 1 := lt_trans hb_lt_n (by linarith)
  have hn_lt_a : (n : ℝ) < ρ a := by linarith
  have hrange_n : (n : ℝ) ∈ Set.range (fun k : ℤ => (k : ℝ)) := ⟨n, rfl⟩
  have hrange_n1 : (n : ℝ) + 1 ∈ Set.range (fun k : ℤ => (k : ℝ)) := by
    refine ⟨n + 1, ?_⟩; push_cast; ring
  -- points where `ρ` equals an integer
  obtain ⟨q2, hq2mem, hq2v⟩ := ivt a b (n : ℝ) hab hb_lt_n hn_lt_a
  obtain ⟨q1, hq1mem, hq1v⟩ := ivt a b ((n : ℝ) + 1) hab hb_lt_n1 hn1
  -- points where `ρ` is irrational (hence non-integer)
  obtain ⟨t2, ht2irr, ht2lo, ht2hi⟩ :=
    exists_irrational_btwn (show (n : ℝ) < (n : ℝ) + 1 by linarith)
  have hb_lt_t2 : ρ b < t2 := lt_trans hb_lt_n ht2lo
  have ht2_lt_a : t2 < ρ a := lt_trans ht2hi hn1
  obtain ⟨p2, hp2mem, hp2v⟩ := ivt a b t2 hab hb_lt_t2 ht2_lt_a
  obtain ⟨t1, ht1irr, ht1lo, ht1hi⟩ := exists_irrational_btwn hn1
  obtain ⟨p1, hp1mem, hp1v⟩ :=
    ivt a q1 t1 (le_of_lt hq1mem.1) (by rw [hq1v]; exact ht1lo) ht1hi
  obtain ⟨t3, ht3irr, ht3lo, ht3hi⟩ := exists_irrational_btwn hb_lt_n
  obtain ⟨p3, hp3mem, hp3v⟩ :=
    ivt q2 b t3 (le_of_lt hq2mem.2) ht3lo (by rw [hq2v]; exact ht3hi)
  -- the ordering `p1 < q1 < p2 < q2 < p3`
  have hpq1 : p1 < q1 := hmono (by rw [hq1v, hp1v]; exact ht1lo)
  have hq1p2 : q1 < p2 := hmono (by rw [hq1v, hp2v]; exact ht2hi)
  have hp2q2 : p2 < q2 := hmono (by rw [hp2v, hq2v]; exact ht2lo)
  have hq2p3 : q2 < p3 := hmono (by rw [hq2v, hp3v]; exact ht3hi)
  -- translate the hypothesis into membership / non-membership in the union
  have hp1B : p1 ∈ Set.Ioo u v ∨ p1 ∈ Set.Ioo w z :=
    (hsub p1 ⟨hp1mem.1, hp1mem.2.trans hq1mem.2⟩).mp
      (not_int_of_irrational (by rw [hp1v]; exact ht1irr))
  have hp2B : p2 ∈ Set.Ioo u v ∨ p2 ∈ Set.Ioo w z :=
    (hsub p2 hp2mem).mp (not_int_of_irrational (by rw [hp2v]; exact ht2irr))
  have hp3B : p3 ∈ Set.Ioo u v ∨ p3 ∈ Set.Ioo w z :=
    (hsub p3 ⟨hq2mem.1.trans hp3mem.1, hp3mem.2⟩).mp
      (not_int_of_irrational (by rw [hp3v]; exact ht3irr))
  have hq1B : ¬ (q1 ∈ Set.Ioo u v ∨ q1 ∈ Set.Ioo w z) := fun hB =>
    (hsub q1 hq1mem).mpr hB (by rw [hq1v]; exact hrange_n1)
  have hq2B : ¬ (q2 ∈ Set.Ioo u v ∨ q2 ∈ Set.Ioo w z) := fun hB =>
    (hsub q2 hq2mem).mpr hB (by rw [hq2v]; exact hrange_n)
  exact no_alternation u v w z p1 q1 p2 q2 p3 hpq1 hq1p2 hp2q2 hq2p3
    hp1B hp2B hp3B hq1B hq2B

end Work.TMC14Core
