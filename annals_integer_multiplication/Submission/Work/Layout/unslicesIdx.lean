import Mathlib
import Submission.Work.Layout.Shared

namespace Work.Layout

open Work.Layout

/-!
# `tgtIdx`/`invIdx2` are inverse bijections of `range (A*n*B)`

The output layout of a flat `A × n × B` array is indexed lexicographically, last index fastest:
the slice-major pair `(s,j)` (`s = a*B + b < A*B`, `j < n`) sits at flat index
`tgtIdx n B s j = (s/B*n + j)*B + s%B = (a*n + j)*B + b`.

Reading it back is a two-step division algorithm: `r / (n*B)` and `r % B` recover the slice
`a*B + b = r/(n*B)*B + r%B`, while `r / B % n` recovers the offset `j`.  All the lemmas below
are elementary consequences of `Nat.div_add_mod`, `Nat.mul_add_div`, `Nat.mul_add_mod` and
`Nat.div_div_eq_div_mul`; the two existence/uniqueness halves of `Nat.div_add_mod` give the two
inverse laws, and the range estimates are the standard monotonicity facts for `Nat.div`/`Nat.mod`.
-/

/-! ## Elementary `Nat` division facts used below -/

/-- Division of `q*B + b` by `B` when `b` is the remainder, i.e. `b < B`. -/
private lemma div_mul_add_of_lt (B b q : ℕ) (hb : b < B) : (q * B + b) / B = q := by
  refine Nat.div_eq_of_lt_le (Nat.le_add_right _ _) ?_
  rw [Nat.succ_mul]
  exact Nat.add_lt_add_left hb _

/-- The corresponding remainder statement. -/
private lemma mod_mul_add_of_lt (B b q : ℕ) (hb : b < B) : (q * B + b) % B = b := by
  rw [Nat.mul_comm q B, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

/-- Products by a positive factor strictly increase them; here `j*B + b < n*B` for `j < n`, `b < B`. -/
private lemma mul_add_lt_mul {n B b j : ℕ} (hj : j < n) (hb : b < B) : j * B + b < n * B := by
  have h1 : j * B + b < j * B + B := Nat.add_lt_add_left hb _
  rw [← Nat.succ_mul] at h1
  exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right B (Nat.succ_le_of_lt hj))

/-! ## The two inverse laws -/

/-- `invIdx2` undoes `tgtIdx`: the pair `(s,j)` is recovered from its flat image.  (No bound on `s`
is needed; `j < n` is.) -/
private lemma invIdx2_tgtIdx_eq (n B s j : ℕ) (hn : 0 < n) (hB : 0 < B) (hj : j < n) :
    invIdx2 n B (tgtIdx n B s j) = (s, j) := by
  have hb : s % B < B := Nat.mod_lt _ hB
  have hlt : j * B + s % B < n * B := mul_add_lt_mul hj hb
  -- `tgtIdx n B s j` written with the factors grouped as `(s/B) * (n*B) + (j*B + s%B)`
  have hdec : tgtIdx n B s j = s / B * (n * B) + (j * B + s % B) := by
    simp only [tgtIdx]; ring
  have hdiv : tgtIdx n B s j / (n * B) = s / B := by
    rw [hdec, Nat.mul_comm (s / B) (n * B), Nat.mul_add_div (Nat.mul_pos hn hB),
      Nat.div_eq_of_lt hlt, Nat.add_zero]
  have hmod : tgtIdx n B s j % B = s % B := by
    simp only [tgtIdx]
    rw [Nat.mul_comm (s / B * n + j) B, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  have hdivB : tgtIdx n B s j / B = s / B * n + j := by
    simp only [tgtIdx]
    rw [Nat.mul_comm (s / B * n + j) B, Nat.mul_add_div hB, Nat.div_eq_of_lt hb, Nat.add_zero]
  have h1 : (invIdx2 n B (tgtIdx n B s j)).1 = s := by
    simp only [invIdx2, hdiv, hmod]
    rw [Nat.mul_comm (s / B) B]
    exact Nat.div_add_mod s B
  have h2 : (invIdx2 n B (tgtIdx n B s j)).2 = j := by
    simp only [invIdx2, hdivB]
    rw [Nat.mul_comm (s / B) n, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  rw [Prod.ext_iff]
  exact ⟨h1, h2⟩

/-- `tgtIdx` undoes `invIdx2`: applying the layout map to the recovered pair gives back the flat
index.  (No bound on `r` is needed.) -/
private lemma tgtIdx_invIdx2_eq (n B r : ℕ) (_hn : 0 < n) (hB : 0 < B) :
    tgtIdx n B (invIdx2 n B r).1 (invIdx2 n B r).2 = r := by
  have hb : r % B < B := Nat.mod_lt _ hB
  have hdiv : (r / (n * B) * B + r % B) / B = r / (n * B) :=
    div_mul_add_of_lt B (r % B) (r / (n * B)) hb
  have hmod : (r / (n * B) * B + r % B) % B = r % B :=
    mod_mul_add_of_lt B (r % B) (r / (n * B)) hb
  -- the slice index `r/(n*B)` is `(r/B)/n`, so it is the quotient of `r/B` by `n`
  have hkey : r / (n * B) * n + r / B % n = r / B := by
    have hc : r / (n * B) = r / B / n := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm n B]
    rw [hc, Nat.mul_comm (r / B / n) n]
    exact Nat.div_add_mod (r / B) n
  calc tgtIdx n B (invIdx2 n B r).1 (invIdx2 n B r).2
      = (r / (n * B) * n + r / B % n) * B + r % B := by
        simp only [tgtIdx, invIdx2, hdiv, hmod]
    _ = (r / B) * B + r % B := by rw [hkey]
    _ = r := by rw [Nat.mul_comm]; exact Nat.div_add_mod r B

/-! ## The range estimates -/

/-- `tgtIdx` maps `range (A*B) × range n` into `range (A*n*B)`. -/
private lemma tgtIdx_lt_range (A n B s j : ℕ) (hB : 0 < B) (hs : s < A * B) (hj : j < n) :
    tgtIdx n B s j < A * n * B := by
  have hb : s % B < B := Nat.mod_lt _ hB
  have ha : s / B < A := by rw [Nat.div_lt_iff_lt_mul hB]; exact hs
  have ha1 : s / B + 1 ≤ A := Nat.succ_le_of_lt ha
  have hkey : s / B * n + j < A * n := by
    have h1 : s / B * n + j < s / B * n + n := Nat.add_lt_add_left hj _
    have h2 : s / B * n + n = (s / B + 1) * n := by rw [Nat.succ_mul]
    rw [h2] at h1
    exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right n ha1)
  have hstep : (s / B * n + j) + 1 ≤ A * n := Nat.succ_le_of_lt hkey
  have h3 : (s / B * n + j) * B + s % B < (s / B * n + j) * B + B :=
    Nat.add_lt_add_left hb _
  have h4 : (s / B * n + j) * B + B = (s / B * n + j + 1) * B := by rw [Nat.succ_mul]
  rw [h4] at h3
  have h5 : (s / B * n + j + 1) * B ≤ (A * n) * B := Nat.mul_le_mul_right B hstep
  simp only [tgtIdx]
  calc (s / B * n + j) * B + s % B < (A * n) * B := lt_of_lt_of_le h3 h5
    _ = A * n * B := by rw [Nat.mul_assoc]

/-- `invIdx2` sends `range (A*n*B)` into `range (A*B) × range n`. -/
private lemma invIdx2_lt_range (A n B r : ℕ) (hn : 0 < n) (hB : 0 < B) (hr : r < A * n * B) :
    (invIdx2 n B r).1 < A * B ∧ (invIdx2 n B r).2 < n := by
  have hb : r % B < B := Nat.mod_lt _ hB
  have hc : r / (n * B) < A := by
    rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos hn hB), ← Nat.mul_assoc]; exact hr
  have hc1 : r / (n * B) + 1 ≤ A := Nat.succ_le_of_lt hc
  constructor
  · simp only [invIdx2]
    have h1 : r / (n * B) * B + r % B < r / (n * B) * B + B := Nat.add_lt_add_left hb _
    have h2 : r / (n * B) * B + B = (r / (n * B) + 1) * B := by rw [Nat.succ_mul]
    rw [h2] at h1
    exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right B hc1)
  · simp only [invIdx2]; exact Nat.mod_lt _ hn

/-- `tgtIdx` and `invIdx2` are inverse bijections of `range (A*n*B)` (output layout of a flat
`A × n × B` array); `invIdx2 r` is the slice-major pair `(s,j)` sent to flat index `r`. -/
theorem unslicesIdx (A n B : ℕ) (hn : 0 < n) (hB : 0 < B) :
    (∀ (s j : ℕ), s < A * B → j < n → tgtIdx n B s j < A * n * B) ∧
    (∀ (s j : ℕ), s < A * B → j < n → invIdx2 n B (tgtIdx n B s j) = (s, j)) ∧
    (∀ r, r < A * n * B → tgtIdx n B (invIdx2 n B r).1 (invIdx2 n B r).2 = r) ∧
    (∀ r, r < A * n * B → (invIdx2 n B r).1 < A * B ∧ (invIdx2 n B r).2 < n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s j hs hj; exact tgtIdx_lt_range A n B s j hB hs hj
  · intro s j _ hj; exact invIdx2_tgtIdx_eq n B s j hn hB hj
  · intro r _; exact tgtIdx_invIdx2_eq n B r hn hB
  · intro r hr; exact invIdx2_lt_range A n B r hn hB hr

end Work.Layout
