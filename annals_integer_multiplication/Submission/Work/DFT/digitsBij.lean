import Mathlib
import Submission.Work.DFT.dftDefs

/-!
# Mixed-radix digits ↔ Horner evaluation: the bijection (paper §2.4)

`HvdH.digits ts m` is the big-endian mixed-radix expansion of `m` in the digit sizes `ts`
(most significant digit first),

* `HvdH.digits (t :: ts) m = (m / ts.prod) % t :: HvdH.digits ts (m % ts.prod)`,

and `HvdH.undigits ts` evaluates a digit list back to a natural number (big-endian Horner),

* `HvdH.undigits (t :: ts) (j :: js) = j * ts.prod + HvdH.undigits ts js`.

For positive radices these two maps are mutually inverse between the range
`{m | m < ts.prod}` and the box `{js | js.length = ts.length, ∀ i, jsᵢ < tsᵢ}`
of bounded digit lists; `digits` is length-preserving and always lands in the box.
-/

namespace Work.DFT

/-- The product of a list of positive naturals is positive. -/
private theorem prod_pos_of_forall {ts : List ℕ} (h : ∀ t ∈ ts, 0 < t) : 0 < ts.prod :=
  List.prod_pos h

/-- Every mixed-radix digit of `m < ts.prod` is bounded by the corresponding radix. -/
private theorem digits_lt_radix : ∀ (ts : List ℕ), (∀ t ∈ ts, 0 < t) →
    ∀ m, m < ts.prod → ∀ i < ts.length, (HvdH.digits ts m).getD i 0 < ts.getD i 0 := by
  intro ts
  induction ts with
  | nil => intro _ m _ i hi; simp at hi
  | cons t ts ih =>
    intro hpos m hm i hi
    have ht : 0 < t := hpos t (by simp)
    have hts : ∀ x ∈ ts, 0 < x := fun x hx => hpos x (by simp [hx])
    have hP : 0 < ts.prod := prod_pos_of_forall hts
    rw [List.prod_cons] at hm
    cases i with
    | zero =>
      rw [HvdH.digits]; simp only [List.getD_cons_zero]
      exact Nat.mod_lt _ ht
    | succ k =>
      rw [HvdH.digits]; simp only [List.getD_cons_succ]
      have hk : k < ts.length := by simp only [List.length_cons] at hi; omega
      exact ih hts (m % ts.prod) (Nat.mod_lt m hP) k hk

/-- A digit list lying in the box `jsᵢ < tsᵢ` evaluates to a value below `ts.prod`. -/
private theorem undigits_lt_prod : ∀ (ts : List ℕ), (∀ t ∈ ts, 0 < t) →
    ∀ js : List ℕ, js.length = ts.length →
    (∀ i < ts.length, js.getD i 0 < ts.getD i 0) → HvdH.undigits ts js < ts.prod := by
  intro ts
  induction ts with
  | nil =>
    intro _ js hlen _
    cases js with
    | nil => simp [HvdH.undigits]
    | cons j js => simp at hlen
  | cons t ts ih =>
    intro hpos js hlen hb
    have ht : 0 < t := hpos t (by simp)
    have hts : ∀ x ∈ ts, 0 < x := fun x hx => hpos x (by simp [hx])
    cases js with
    | nil => simp at hlen
    | cons j js =>
      rw [HvdH.undigits, List.prod_cons]
      have hlen' : js.length = ts.length := by simp only [List.length_cons] at hlen ⊢; omega
      have hj : j < t := by have := hb 0 (by simp); simpa using this
      have hb' : ∀ i < ts.length, js.getD i 0 < ts.getD i 0 := by
        intro i hi
        have := hb (i+1) (by simp only [List.length_cons]; omega); simpa using this
      have hu := ih hts js hlen' hb'
      calc j * ts.prod + HvdH.undigits ts js < j * ts.prod + ts.prod := Nat.add_lt_add_left hu _
        _ = (j+1) * ts.prod := by ring
        _ ≤ t * ts.prod := Nat.mul_le_mul_right ts.prod (Nat.succ_le_of_lt hj)

/-- `digits` is a left inverse of `undigits` on the box of bounded digit lists. -/
private theorem digits_undigits_inv : ∀ (ts : List ℕ), (∀ t ∈ ts, 0 < t) →
    ∀ js : List ℕ, js.length = ts.length →
    (∀ i < ts.length, js.getD i 0 < ts.getD i 0) → HvdH.digits ts (HvdH.undigits ts js) = js := by
  intro ts
  induction ts with
  | nil =>
    intro _ js hlen _
    cases js with
    | nil => simp [HvdH.digits]
    | cons j js => simp at hlen
  | cons t ts ih =>
    intro hpos js hlen hb
    have hts : ∀ x ∈ ts, 0 < x := fun x hx => hpos x (by simp [hx])
    have hP : 0 < ts.prod := prod_pos_of_forall hts
    cases js with
    | nil => simp at hlen
    | cons j js =>
      have hlen' : js.length = ts.length := by simp only [List.length_cons] at hlen ⊢; omega
      have hj : j < t := by have := hb 0 (by simp); simpa using this
      have hb' : ∀ i < ts.length, js.getD i 0 < ts.getD i 0 := by
        intro i hi
        have := hb (i+1) (by simp only [List.length_cons]; omega); simpa using this
      have hu := undigits_lt_prod ts hts js hlen' hb'
      have hih := ih hts js hlen' hb'
      rw [HvdH.undigits, HvdH.digits]
      have hdiv : (j * ts.prod + HvdH.undigits ts js) / ts.prod = j := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hu, Nat.zero_add]
      have hmod : (j * ts.prod + HvdH.undigits ts js) % ts.prod = HvdH.undigits ts js := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
      rw [hdiv, hmod, Nat.mod_eq_of_lt hj, hih]

/-- `undigits` is a left inverse of `digits` on `{m | m < ts.prod}`. -/
private theorem undigits_digits : ∀ (ts : List ℕ), (∀ t ∈ ts, 0 < t) →
    ∀ m, m < ts.prod → HvdH.undigits ts (HvdH.digits ts m) = m := by
  intro ts
  induction ts with
  | nil =>
    intro _ m hm
    have h0 : m = 0 := by simpa [List.prod_nil] using hm
    subst h0; simp [HvdH.undigits]
  | cons t ts ih =>
    intro hpos m hm
    have hts : ∀ x ∈ ts, 0 < x := fun x hx => hpos x (by simp [hx])
    have hP : 0 < ts.prod := prod_pos_of_forall hts
    rw [List.prod_cons] at hm
    rw [HvdH.digits, HvdH.undigits]
    have hmP : m % ts.prod < ts.prod := Nat.mod_lt m hP
    rw [ih hts (m % ts.prod) hmP]
    have hdiv_lt : m / ts.prod < t := by
      rw [Nat.div_lt_iff_lt_mul hP]; exact hm
    rw [Nat.mod_eq_of_lt hdiv_lt, Nat.mul_comm (m / ts.prod) ts.prod]
    exact Nat.div_add_mod m ts.prod

/-- The mixed-radix digit map `m ↦ HvdH.digits ts m` and the Horner evaluation
`HvdH.undigits ts` establish a bijection between `{m | m < ts.prod}` and the box
`{js | js.length = ts.length, ∀ i, jsᵢ < tsᵢ}` of bounded digit lists (for positive
radices): each direction inverts the other, `digits` is length-preserving and lands in
the box, and every list in the box is attained. -/
theorem digitsBij (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) :
    (∀ m < ts.prod, HvdH.undigits ts (HvdH.digits ts m) = m) ∧
    (∀ m < ts.prod, ∀ i < ts.length, (HvdH.digits ts m).getD i 0 < ts.getD i 0) ∧
    (∀ m, (HvdH.digits ts m).length = ts.length) ∧
    (∀ js : List ℕ, js.length = ts.length → (∀ i < ts.length, js.getD i 0 < ts.getD i 0) →
      HvdH.digits ts (HvdH.undigits ts js) = js ∧ HvdH.undigits ts js < ts.prod) := by
  refine ⟨undigits_digits ts hpos, digits_lt_radix ts hpos, digits_length ts, ?_⟩
  intro js hl hb
  exact ⟨digits_undigits_inv ts hpos js hl hb, undigits_lt_prod ts hpos js hl hb⟩

end Work.DFT
