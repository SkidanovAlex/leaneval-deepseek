import Mathlib
import Submission.Work.Layout.Shared

set_option autoImplicit false

namespace Work.Layout

open Work.Layout

/-!
# Index arithmetic for the slice-major labelling (`invIdx1` / `keyIdx1`)

A flat `A × m × B` array is indexed lexicographically, last index fastest: the element `(a,j,b)`
has flat index `(a*m + j)*B + b`.  `keyIdx1 m B i` sends this flat index to the *slice-major*
label `(a*B + b)*m + j`, i.e. it reads the element as the `j`-th entry of slice `s = a*B + b` in
slice-major listing.  `invIdx1 m B r` is its inverse (on the range): it recovers the flat index.

All the identities below hold unconditionally (no bound on the index), except the range statement
`invIdx1_lt`, which uses `r < A*m*B`.
-/

/-! ## Elementary div/mod shapes -/

lemma div_m_mul (x j m : ℕ) (hm : 0 < m) (hj : j < m) : (x*m + j)/m = x := by
  have h : x*m + j = m*x + j := by ring
  rw [h, Nat.mul_add_div hm, Nat.div_eq_of_lt hj, Nat.add_zero]

lemma mod_m_mul (x j m : ℕ) (hj : j < m) : (x*m + j) % m = j := by
  rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hj]

lemma div_B_add (a b B : ℕ) (hB : 0 < B) (hb : b < B) : (a*B + b)/B = a := by
  have h : a*B + b = B*a + b := by ring
  rw [h, Nat.mul_add_div hB, Nat.div_eq_of_lt hb, Nat.add_zero]

lemma mod_B_add (a b B : ℕ) (hb : b < B) : (a*B + b) % B = b := by
  rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hb]

/-! ## The mixed-radix cell `(a*m + j)*B + b` -/

lemma div_mB_form (a j b m B : ℕ) (_hm : 0 < m) (hj : j < m) (_hB : 0 < B) (hb : b < B) :
    ((a*m + j)*B + b) / (m*B) = a := by
  apply Nat.div_eq_of_lt_le
  · nlinarith [Nat.zero_le (j*B + b)]
  · nlinarith [Nat.succ_le_of_lt hj, Nat.succ_le_of_lt hb, Nat.zero_le a, Nat.zero_le j]

lemma mod_B_form (a j b m B : ℕ) (hb : b < B) : ((a*m + j)*B + b) % B = b := by
  have h : (a*m+j)*B + b = b + B*((a*m+j)) := by ring
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

lemma div_B_form (a j b m B : ℕ) (hB : 0 < B) (hb : b < B) :
    ((a*m + j)*B + b) / B = a*m + j := by
  have h : (a*m+j)*B + b = B*(a*m+j) + b := by ring
  rw [h, Nat.mul_add_div hB, Nat.div_eq_of_lt hb, Nat.add_zero]

/-! ## Decomposition of a flat index -/

/-- `i/B = (i/(m*B))*m + i/B % m`: the `m`-radix split of the middle counter `i/B`. -/
lemma divB_eq (m B i : ℕ) : i/B = i/(m*B)*m + i/B%m := by
  have h := Nat.div_add_mod (i/B) m
  have hd : (i/B)/m = i/(m*B) := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm B m]
  rw [hd, mul_comm m (i/(m*B))] at h
  exact h.symm

/-- Reading a flat index in the mixed radix of shape `A × m × B`. -/
lemma eq_rep (m B i : ℕ) : i = (i/(m*B)*m + i/B%m)*B + i%B := by
  rw [← divB_eq m B i, mul_comm (i/B) B, Nat.div_add_mod]

/-! ## The two round-trips -/

/-- `invIdx1` is a left inverse of `keyIdx1` (in fact on all of `ℕ`). -/
lemma invIdx1_keyIdx1 (m B i : ℕ) (hm : 0 < m) (hB : 0 < B) :
    invIdx1 m B (keyIdx1 m B i) = i := by
  have hj : i / B % m < m := Nat.mod_lt _ hm
  have hb : i % B < B := Nat.mod_lt _ hB
  set Y := keyIdx1 m B i with hY
  have hYm : Y = (i/(m*B)*B + i%B)*m + i/B%m := rfl
  have h1 : Y / m = i/(m*B)*B + i%B := by rw [hYm]; exact div_m_mul _ _ _ hm hj
  have h2 : Y % m = i/B%m := by rw [hYm]; exact mod_m_mul _ _ _ hj
  have h3 : Y / m / B = i/(m*B) := by rw [h1]; exact div_B_add _ _ _ hB hb
  have h4 : Y / m % B = i%B := by rw [h1]; exact mod_B_add _ _ _ hb
  unfold invIdx1
  rw [h3, h4, h2]
  exact (eq_rep m B i).symm

/-- `keyIdx1` is a left inverse of `invIdx1` (in fact on all of `ℕ`). -/
lemma keyIdx1_invIdx1 (m B r : ℕ) (hm : 0 < m) (hB : 0 < B) :
    keyIdx1 m B (invIdx1 m B r) = r := by
  have hb : r/m%B < B := Nat.mod_lt _ hB
  have hj : r%m < m := Nat.mod_lt _ hm
  set X := invIdx1 m B r with hX
  have hXm : X = (r/m/B*m + r%m)*B + r/m%B := rfl
  have hX1 : X / (m*B) = r/m/B := by rw [hXm]; exact div_mB_form (r/m/B) (r%m) (r/m%B) m B hm hj hB hb
  have hX2 : X % B = r/m%B := by rw [hXm]; exact mod_B_form (r/m/B) (r%m) (r/m%B) m B hb
  have hX3 : X / B = r/m/B*m + r%m := by rw [hXm]; exact div_B_form (r/m/B) (r%m) (r/m%B) m B hB hb
  have hX4 : (r/m/B*m + r%m) % m = r%m := mod_m_mul _ _ _ hj
  unfold keyIdx1
  rw [hX1, hX2, hX3, hX4]
  have h5 : r/m/B*B + r/m%B = r/m := by rw [mul_comm (r/m/B) B, Nat.div_add_mod]
  rw [h5, mul_comm (r/m) m, Nat.div_add_mod]

/-! ## The slice-major description and the range -/

/-- `invIdx1 (s*m + j)` is the flat index of the element `(s,j)` of the `s`-th slice. -/
lemma invIdx1_slice (m B : ℕ) (hm : 0 < m) :
    ∀ s j : ℕ, j < m → invIdx1 m B (s*m+j) = (s/B*m+j)*B + s%B := by
  intro s j hj
  unfold invIdx1
  rw [div_m_mul s j m hm hj, mod_m_mul s j m hj]

/-- `invIdx1` maps `range (A*m*B)` into itself. -/
lemma invIdx1_lt (A m B : ℕ) (hm : 0 < m) (hB : 0 < B) (r : ℕ) (hr : r < A*m*B) :
    invIdx1 m B r < A*m*B := by
  have hj : r%m < m := Nat.mod_lt _ hm
  have hs : r/m < A*B := by
    rw [Nat.div_lt_iff_lt_mul hm]
    nlinarith [hr]
  have hsB : r/m/B < A := by
    rw [Nat.div_lt_iff_lt_mul hB]
    exact hs
  have hb : r/m%B < B := Nat.mod_lt _ hB
  rw [show invIdx1 m B r = (r/m/B*m + r%m)*B + r/m%B from rfl]
  have key : r/m/B*m + r%m + 1 ≤ A*m := by
    have h1 : r/m/B + 1 ≤ A := Nat.succ_le_of_lt hsB
    have h2 : r%m + 1 ≤ m := Nat.succ_le_of_lt hj
    calc r/m/B*m + r%m + 1 ≤ r/m/B*m + m := by omega
      _ = (r/m/B + 1)*m := by ring
      _ ≤ A*m := Nat.mul_le_mul_right m h1
  calc (r/m/B*m + r%m)*B + r/m%B
      < (r/m/B*m + r%m)*B + B := by nlinarith [hb]
    _ = ((r/m/B*m + r%m)+1)*B := by ring
    _ ≤ A*m*B := Nat.mul_le_mul_right B key

/-- Slice-major labelling: `keyIdx1` and `invIdx1` are inverse bijections of `range (A*m*B)`, and
`invIdx1 (s*m+j)` is the flat index of the element `(s,j)` of the `s`-th slice. -/
theorem sliceIdx (A m B : ℕ) (hm : 0 < m) (hB : 0 < B) :
    (∀ i, i < A * m * B → invIdx1 m B (keyIdx1 m B i) = i) ∧
    (∀ r, r < A * m * B → keyIdx1 m B (invIdx1 m B r) = r) ∧
    (∀ r, r < A * m * B → invIdx1 m B r < A * m * B) ∧
    (∀ s j : ℕ, j < m → invIdx1 m B (s * m + j) = (s / B * m + j) * B + s % B) := by
  exact ⟨fun i _ => invIdx1_keyIdx1 m B i hm hB,
         fun r _ => keyIdx1_invIdx1 m B r hm hB,
         fun r hr => invIdx1_lt A m B hm hB r hr,
         fun s j hj => invIdx1_slice m B hm s j hj⟩

end Work.Layout
