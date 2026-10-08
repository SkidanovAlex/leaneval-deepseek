/-
Auxiliary definitions and basic structure lemmas for the "COMB413" combinatorial lemma of
Bender--Glauberman (J. Algebra 70 (1981), 200-215, p. 213, proof of Theorem 4.3).

The data: `v : J → ι → ℤ` with (h1) every row has support of size 4 and entries with `x ^ 2 ≤ 1`,
(h2) distinct rows are orthogonal, (h3) every column has support of size 0, 1 or 3,
(h4) the rows are `F₂`-independent.

We set up the vocabulary (supports of rows and columns, triple/singleton columns, the meeting
relation, "full" rows) and prove the basic structure:

* `inter_card_cases` : two distinct rows share 0 or 2 columns;
* `even_set_contra`  : no nonempty set of rows meets every column evenly (form of `h4`);
* `tc_card_eq_nb_card` : a row has as many triple columns as it has neighbours;
* `tc_card_cases`    : that number is `0`, `3` or `4`;
* `no_repeat`        : two distinct columns cannot have the same support of size 3.
-/
import Mathlib
import Submission.Work.BG.Thm43Defs

namespace Work.BG

set_option linter.unusedSectionVars false

/-! ## Pure integer/parity helpers -/

theorem z_val_cases {x : ℤ} (h : x ^ 2 ≤ 1) : x = -1 ∨ x = 0 ∨ x = 1 := by
  have h2 : x ≤ 1 := by nlinarith [sq_nonneg x, h]
  have h3 : -1 ≤ x := by nlinarith [sq_nonneg x, h]
  omega

theorem cast_mul_zmod2 {x y : ℤ} (hx : x = -1 ∨ x = 1) (hy : y = -1 ∨ y = 1) :
    ((x : ZMod 2) * (y : ZMod 2)) = 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

theorem zmod2_eq_one_of_odd {n : ℤ} (h : Odd n) : (n : ZMod 2) = 1 := by
  obtain ⟨k, rfl⟩ := h
  push_cast
  have h2 : ((2 : ZMod 2)) = 0 := by decide
  rw [show ((2 : ZMod 2) * (k : ZMod 2) + 1) = 0 * (k : ZMod 2) + 1 by rw [h2],
    zero_mul, zero_add]

theorem zmod2_eq_zero_of_even {n : ℕ} (h : Even n) : (n : ZMod 2) = 0 := by
  obtain ⟨k, rfl⟩ := h
  push_cast
  have h2 : ((2 : ZMod 2)) = 0 := by decide
  rw [show ((k : ZMod 2) + (k : ZMod 2)) = 2 * (k : ZMod 2) by ring, h2, zero_mul]

theorem not_even_and_odd {n : ℤ} (h₁ : Even n) (h₂ : Odd n) : False := by
  obtain ⟨a, ha⟩ := h₁; obtain ⟨b, hb⟩ := h₂; omega

/-! ## The basic structure -/

variable {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
variable (v : J → ι → ℤ)

/-- The support of a row: the coordinates where it does not vanish. -/
def Supp (v : J → ι → ℤ) (j : J) : Finset ι := Finset.univ.filter (fun i => v j i ≠ 0)

/-- The support of a column: the rows where it does not vanish. -/
def ColF (v : J → ι → ℤ) (i : ι) : Finset J := Finset.univ.filter (fun j => v j i ≠ 0)

/-- The triple columns of a row. -/
def TC (v : J → ι → ℤ) (j : J) : Finset ι := (Supp v j).filter (fun i => (ColF v i).card = 3)

/-- The singleton columns of a row. -/
def SC (v : J → ι → ℤ) (j : J) : Finset ι := (Supp v j).filter (fun i => (ColF v i).card = 1)

/-- The rows meeting `j` (sharing at least one column). -/
def NB (v : J → ι → ℤ) (j : J) : Finset J :=
  Finset.univ.filter (fun k => k ≠ j ∧ (Supp v j ∩ Supp v k).Nonempty)

/-- A row is *full* when all four of its columns are triple columns. -/
def Full (v : J → ι → ℤ) (j : J) : Prop := (TC v j).card = 4

/-- The four neighbours of a full row together with the four columns of the row and the four
"second columns" of the edges of the resulting 4-cycle: `ColF p = {j,a,b}`, `ColF q = {j,b,c}`,
`ColF r = {j,c,d}`, `ColF s = {j,d,a}`, `Supp a ∩ Supp b = {p,u}`, `Supp b ∩ Supp c = {q,y}`,
`Supp c ∩ Supp d = {r,z}`, `Supp d ∩ Supp a = {s,x}`. -/
structure C4Data (v : J → ι → ℤ) (j a b c d : J) (p q r s u x y z : ι) : Prop where
  hp : ColF v p = {j, a, b}
  hq : ColF v q = {j, b, c}
  hr : ColF v r = {j, c, d}
  hs : ColF v s = {j, d, a}
  hp3 : (ColF v p).card = 3
  hq3 : (ColF v q).card = 3
  hr3 : (ColF v r).card = 3
  hs3 : (ColF v s).card = 3
  hS : Supp v j = {p, q, r, s}
  hAB : Supp v a ∩ Supp v b = {p, u}
  hBC : Supp v b ∩ Supp v c = {q, y}
  hCD : Supp v c ∩ Supp v d = {r, z}
  hDA : Supp v d ∩ Supp v a = {s, x}
  hup : u ≠ p
  hyq : y ≠ q
  hzr : z ≠ r
  hxs : x ≠ s

theorem mem_Supp (j : J) (i : ι) : i ∈ Supp v j ↔ v j i ≠ 0 := by simp [Supp]
theorem mem_ColF (j : J) (i : ι) : j ∈ ColF v i ↔ v j i ≠ 0 := by simp [ColF]
theorem mem_ColF_supp (j : J) (i : ι) : j ∈ ColF v i ↔ i ∈ Supp v j := by simp [ColF, Supp]

/-- `F₂`-independence, applied to a two-element set of rows: the sum of two distinct rows is odd
somewhere. -/
theorem h4_pair (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    {j k : J} (hjk : j ≠ k) : ∃ i, Odd (v j i + v k i) := by
  obtain ⟨i, hi⟩ := h4 (fun x => if x = j then (1:ℤ) else if x = k then (1:ℤ) else 0)
    ⟨j, by simp⟩
  refine ⟨i, ?_⟩
  have hsum : ∑ x, (if x = j then (1:ℤ) else if x = k then (1:ℤ) else 0) * v x i
      = v j i + v k i := by
    have hsplit : ∀ x, (if x = j then (1:ℤ) else if x = k then (1:ℤ) else 0) * v x i
        = (if x = j then v x i else 0) + (if x = k then v x i else 0) := by
      intro x
      by_cases hxj : x = j
      · subst hxj; simp [hjk]
      · by_cases hxk : x = k
        · subst hxk; simp [hxj]
        · simp [hxj, hxk]
    rw [Finset.sum_congr rfl (fun x _ => hsplit x), Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq' _ _ (fun x => v x i), Finset.sum_ite_eq' _ _ (fun x => v x i)]
    simp
  rwa [hsum] at hi

/-- Orthogonality, restricted to the columns shared by two rows. -/
theorem inter_sum (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0) {j k : J} (hjk : j ≠ k) :
    ∑ i ∈ Supp v j ∩ Supp v k, v j i * v k i = 0 := by
  rw [← h2 j k hjk]
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro i _ hi
  rw [Finset.mem_inter, not_and_or] at hi
  rcases hi with h | h
  · have hv : v j i = 0 := by by_contra hc; exact h (by rw [mem_Supp]; exact hc)
    rw [hv, zero_mul]
  · have hv : v k i = 0 := by by_contra hc; exact h (by rw [mem_Supp]; exact hc)
    rw [hv, mul_zero]

/-- The number of shared columns of two distinct rows is even. -/
theorem even_inter_card (h1 : ∀ j, (Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0) {j k : J} (hjk : j ≠ k) :
    Even (Supp v j ∩ Supp v k).card := by
  have hsum := inter_sum v h2 hjk
  have hZ : (((Supp v j ∩ Supp v k).card : ℕ) : ZMod 2) = 0 := by
    have hstep : (((Supp v j ∩ Supp v k).card : ℕ) : ZMod 2)
        = ((∑ i ∈ Supp v j ∩ Supp v k, v j i * v k i : ℤ) : ZMod 2) := by
      rw [Finset.card_eq_sum_ones]
      push_cast
      refine Finset.sum_congr rfl (fun i hi => ?_)
      obtain ⟨hj, hk⟩ := Finset.mem_inter.mp hi
      have hvj : v j i = -1 ∨ v j i = 1 := by
        rcases z_val_cases ((h1 j).2 i) with h | h | h
        · exact Or.inl h
        · exact absurd h (by rw [mem_Supp] at hj; exact hj)
        · exact Or.inr h
      have hvk : v k i = -1 ∨ v k i = 1 := by
        rcases z_val_cases ((h1 k).2 i) with h | h | h
        · exact Or.inl h
        · exact absurd h (by rw [mem_Supp] at hk; exact hk)
        · exact Or.inr h
      rw [cast_mul_zmod2 hvj hvk]
    rw [hstep, hsum, Int.cast_zero]
  have hZ' : (((((Supp v j ∩ Supp v k).card : ℕ) : ℤ)) : ZMod 2) = 0 := by
    rw [Int.cast_natCast]; exact hZ
  have hdvd : (2 : ℤ) ∣ (((Supp v j ∩ Supp v k).card : ℕ) : ℤ) := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((((Supp v j ∩ Supp v k).card : ℕ) : ℤ)) 2).mp hZ'
    simpa using this
  exact even_iff_two_dvd.mpr (Int.ofNat_dvd.mp hdvd)

/-- A nonempty set of rows meeting every column in an even number of rows contradicts
`F₂`-independence. -/
theorem even_set_contra (h1 : ∀ j, (Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    (n : Finset J) (hn : n.Nonempty)
    (heven : ∀ i, Even (n.filter (fun j => v j i ≠ 0)).card) : False := by
  obtain ⟨j0, hj0⟩ := hn
  obtain ⟨i, hi⟩ := h4 (fun x => if x ∈ n then (1:ℤ) else 0) ⟨j0, by simp [hj0]⟩
  have hsum : ∑ x, (if x ∈ n then (1:ℤ) else 0) * v x i = ∑ x ∈ n, v x i := by
    have hprod : ∀ x, (if x ∈ n then (1:ℤ) else 0) * v x i = (if x ∈ n then v x i else 0) := by
      intro x; by_cases h : x ∈ n <;> simp [h]
    rw [Finset.sum_congr rfl (fun x _ => hprod x), ← Finset.sum_filter]
    congr 1; ext x; simp
  rw [hsum] at hi
  have hodd : ((∑ x ∈ n, v x i : ℤ) : ZMod 2) = 1 := zmod2_eq_one_of_odd hi
  have hzero : ((∑ x ∈ n, v x i : ℤ) : ZMod 2) = 0 := by
    rw [Int.cast_sum]
    rw [show (∑ x ∈ n, ((v x i : ℤ) : ZMod 2))
        = ∑ x ∈ n, (if v x i ≠ 0 then (1 : ZMod 2) else 0) from by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rcases z_val_cases ((h1 x).2 i) with h | h | h <;> simp [h]]
    rw [Finset.sum_boole, zmod2_eq_zero_of_even (heven i)]
  rw [hzero] at hodd
  exact absurd hodd (by decide)

/-- Two distinct rows share `0` or `2` columns. -/
theorem inter_card_cases (h1 : ∀ j, (Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0)
    (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    {j k : J} (hjk : j ≠ k) :
    (Supp v j ∩ Supp v k).card = 0 ∨ (Supp v j ∩ Supp v k).card = 2 := by
  have hev := even_inter_card v h1 h2 hjk
  have hle : (Supp v j ∩ Supp v k).card ≤ 4 := by
    calc (Supp v j ∩ Supp v k).card ≤ (Supp v j).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = 4 := (h1 j).1
  have hne : (Supp v j ∩ Supp v k).card ≠ 4 := by
    intro h4c
    have hsub : Supp v j ⊆ Supp v k := by
      have hEq : Supp v j ∩ Supp v k = Supp v j :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h4c, (h1 j).1])
      rw [← hEq]; exact Finset.inter_subset_right
    have hEq2 : Supp v j = Supp v k :=
      Finset.eq_of_subset_of_card_le hsub (by rw [(h1 j).1, (h1 k).1])
    obtain ⟨i, hi⟩ := h4_pair v h4 hjk
    have hiff : v j i = 0 ↔ v k i = 0 := by
      have h1' : (i ∈ Supp v j) ↔ (i ∈ Supp v k) := by rw [hEq2]
      rw [mem_Supp v j i, mem_Supp v k i] at h1'
      exact not_iff_not.mp h1'
    have heven : Even (v j i + v k i) := by
      by_cases h0 : v j i = 0
      · rw [h0, hiff.mp h0]; exact ⟨0, by ring⟩
      · have hvj : v j i = -1 ∨ v j i = 1 := by
          rcases z_val_cases ((h1 j).2 i) with h | h | h
          · exact Or.inl h
          · exact absurd h h0
          · exact Or.inr h
        have hk0 : v k i ≠ 0 := fun hh => h0 (hiff.mpr hh)
        have hvk : v k i = -1 ∨ v k i = 1 := by
          rcases z_val_cases ((h1 k).2 i) with h | h | h
          · exact Or.inl h
          · exact absurd h hk0
          · exact Or.inr h
        rcases hvj with h | h <;> rcases hvk with h' | h'
        · rw [h, h']; exact ⟨-1, by norm_num⟩
        · rw [h, h']; exact ⟨0, by norm_num⟩
        · rw [h, h']; exact ⟨0, by norm_num⟩
        · rw [h, h']; exact ⟨1, by norm_num⟩
    exact not_even_and_odd heven hi
  obtain ⟨t, ht⟩ := hev
  omega

/-! ## Counting identity, single/singleton split, and C4 rotations -/

theorem tc_card_eq_nb_card
    (h1 : ∀ j, (Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0)
    (h3 : ∀ i, (ColF v i).card ∈ ({0,1,3} : Finset ℕ))
    (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    (j : J) : (TC v j).card = (NB v j).card := by
  have hsplit : (∑ k : J, (Supp v j ∩ Supp v k).card) = ∑ i ∈ Supp v j, (ColF v i).card := by
    have step1 : ∀ k : J,
        (Supp v j ∩ Supp v k).card = ∑ i ∈ Supp v j, (if i ∈ Supp v k then 1 else 0) := by
      intro k
      have hfil : Supp v j ∩ Supp v k = (Supp v j).filter (fun i => i ∈ Supp v k) := by
        ext i; simp
      rw [hfil, Finset.card_filter]
    rw [Finset.sum_congr rfl (fun k _ => step1 k), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [← Finset.card_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ColF, mem_Supp]
  have hleft : (∑ k : J, (Supp v j ∩ Supp v k).card) = 4 + 2 * (NB v j).card := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), Finset.inter_self, (h1 j).1]
    have hrest : ∀ k ∈ (Finset.univ.erase j),
        (Supp v j ∩ Supp v k).card = 2 * (if k ∈ NB v j then 1 else 0) := by
      intro k hk
      rw [Finset.mem_erase] at hk
      obtain ⟨hkj, -⟩ := hk
      by_cases hnb : k ∈ NB v j
      · have hne' : (Supp v j ∩ Supp v k).Nonempty := by
          have h2' := hnb
          simp only [NB, Finset.mem_filter, Finset.mem_univ, true_and] at h2'
          exact h2'.2
        rcases inter_card_cases v h1 h2 h4 (Ne.symm hkj) with h | h
        · rw [Finset.card_eq_zero] at h
          exact absurd hne' (Finset.not_nonempty_iff_eq_empty.mpr h)
        · rw [h, if_pos hnb]
      · have hempty : (Supp v j ∩ Supp v k) = ∅ := by
          rw [← Finset.not_nonempty_iff_eq_empty]
          intro hc
          exact hnb (by
            simp only [NB, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hkj, hc⟩)
        rw [hempty, Finset.card_empty, if_neg hnb]
    rw [Finset.sum_congr rfl hrest,
      show (∑ k ∈ Finset.univ.erase j, 2 * (if k ∈ NB v j then 1 else 0))
        = 2 * (∑ k ∈ Finset.univ.erase j, (if k ∈ NB v j then 1 else 0)) by
          rw [Finset.mul_sum]]
    have hnbj : j ∉ NB v j := by simp [NB]
    have hset : (Finset.univ.erase j).filter (fun k => k ∈ NB v j) = NB v j := by
      apply Finset.Subset.antisymm
      · intro x hx
        rw [Finset.mem_filter] at hx
        exact hx.2
      · intro x hx
        rw [Finset.mem_filter]
        refine ⟨?_, hx⟩
        rw [Finset.mem_erase]
        exact ⟨fun h => hnbj (h ▸ hx), Finset.mem_univ x⟩
    rw [Finset.sum_boole, hset]
    simp only [Nat.cast_id] <;> try ring
  have hright : (∑ i ∈ Supp v j, (ColF v i).card) = 4 + 2 * (TC v j).card := by
    have hterm : ∀ i ∈ Supp v j, (ColF v i).card = 1 + 2 * (if i ∈ TC v j then 1 else 0) := by
      intro i hi
      have hji : j ∈ ColF v i := by rw [mem_ColF]; rw [mem_Supp] at hi; exact hi
      have hc := h3 i
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      have hpos : 1 ≤ (ColF v i).card := Finset.card_pos.mpr ⟨j, hji⟩
      rcases hc with h | h | h
      · omega
      · rw [h]
        have hmem : i ∉ TC v j := by
          intro hmm
          simp only [TC, Finset.mem_filter] at hmm
          omega
        simp [hmem]
      · rw [h]
        have : i ∈ TC v j := by simp [TC, hi, h]
        simp [this]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    rw [← Finset.card_eq_sum_ones, (h1 j).1]
    rw [show (∑ i ∈ Supp v j, 2 * (if i ∈ TC v j then 1 else 0))
        = 2 * (∑ i ∈ Supp v j, (if i ∈ TC v j then 1 else 0)) by rw [Finset.mul_sum]]
    have hset : (Supp v j).filter (fun i => i ∈ TC v j) = TC v j := by
      apply Finset.Subset.antisymm
      · intro x hx; rw [Finset.mem_filter] at hx; exact hx.2
      · intro x hx
        rw [Finset.mem_filter]
        exact ⟨by rw [TC, Finset.mem_filter] at hx; exact hx.1, hx⟩
    rw [Finset.sum_boole, hset]
    simp only [Nat.cast_id] <;> try ring
  omega


theorem no_repeat
    (h1 : ∀ j, (Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0)
    (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    {i i' : ι} (hii : i ≠ i') (hc : ColF v i = ColF v i') (hcard : (ColF v i).card = 3) :
    False := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hEq⟩ := Finset.card_eq_three.mp hcard
  have hEq' : ColF v i' = {p, q, r} := by rw [← hc, hEq]
  have hp_i : v p i ≠ 0 := by rw [← mem_ColF v p i, hEq]; simp
  have hq_i : v q i ≠ 0 := by rw [← mem_ColF v q i, hEq]; simp
  have hr_i : v r i ≠ 0 := by rw [← mem_ColF v r i, hEq]; simp
  have hp_i' : v p i' ≠ 0 := by rw [← mem_ColF v p i', hEq']; simp
  have hq_i' : v q i' ≠ 0 := by rw [← mem_ColF v q i', hEq']; simp
  have hr_i' : v r i' ≠ 0 := by rw [← mem_ColF v r i', hEq']; simp
  have hI : ∀ {x y : J}, x ≠ y → v x i ≠ 0 → v x i' ≠ 0 → v y i ≠ 0 → v y i' ≠ 0 →
      Supp v x ∩ Supp v y = {i, i'} := by
    intro x y hxy hxi hxi' hyi hyi'
    have hsub : ({i, i'} : Finset ι) ⊆ Supp v x ∩ Supp v y := by
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨by rw [mem_Supp]; exact hxi, by rw [mem_Supp]; exact hyi⟩
      · exact Finset.mem_inter.mpr ⟨by rw [mem_Supp]; exact hxi', by rw [mem_Supp]; exact hyi'⟩
    have hcard2 : (Supp v x ∩ Supp v y).card = 2 := by
      rcases inter_card_cases v h1 h2 h4 hxy with h | h
      · exfalso
        have h2le : ({i, i'} : Finset ι).card ≤ (Supp v x ∩ Supp v y).card :=
          Finset.card_le_card hsub
        rw [Finset.card_pair hii, h] at h2le
        omega
      · exact h
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard2, Finset.card_pair hii])).symm
  have e1 := inter_sum v h2 hpq
  rw [hI hpq hp_i hp_i' hq_i hq_i', Finset.sum_pair hii] at e1
  have e2 := inter_sum v h2 hqr
  rw [hI hqr hq_i hq_i' hr_i hr_i', Finset.sum_pair hii] at e2
  have e3 := inter_sum v h2 (Ne.symm hpr)
  rw [hI (Ne.symm hpr) hr_i hr_i' hp_i hp_i', Finset.sum_pair hii] at e3
  have hs : ∀ {x : J}, v x i ≠ 0 → (v x i) ^ 2 = 1 := by
    intro x hx
    have hle := (h1 x).2 i
    have hpos := sq_nonneg (v x i)
    have hne : (v x i) ^ 2 ≠ 0 := pow_ne_zero 2 hx
    omega
  have hs' : ∀ {x : J}, v x i' ≠ 0 → (v x i') ^ 2 = 1 := by
    intro x hx
    have hle := (h1 x).2 i'
    have hpos := sq_nonneg (v x i')
    have hne : (v x i') ^ 2 ≠ 0 := pow_ne_zero 2 hx
    omega
  have keyA : (v p i * v q i) * (v q i * v r i) * (v r i * v p i) = 1 := by
    rw [show (v p i * v q i) * (v q i * v r i) * (v r i * v p i)
        = (v p i) ^ 2 * (v q i) ^ 2 * (v r i) ^ 2 by ring]
    rw [hs hp_i, hs hq_i, hs hr_i]; ring
  have keyB : (v p i' * v q i') * (v q i' * v r i') * (v r i' * v p i') = 1 := by
    rw [show (v p i' * v q i') * (v q i' * v r i') * (v r i' * v p i')
        = (v p i') ^ 2 * (v q i') ^ 2 * (v r i') ^ 2 by ring]
    rw [hs' hp_i', hs' hq_i', hs' hr_i']; ring
  have hA' : v p i' * v q i' = -(v p i * v q i) := by linarith [e1]
  have hB' : v q i' * v r i' = -(v q i * v r i) := by linarith [e2]
  have hC' : v r i' * v p i' = -(v r i * v p i) := by linarith [e3]
  have keyC : (v p i * v q i) * (v q i * v r i) * (v r i * v p i)
      = -((v p i' * v q i') * (v q i' * v r i') * (v r i' * v p i')) := by
    rw [hA', hB', hC']
    ring
  rw [keyA, keyB] at keyC
  omega


theorem tc_sc_card
    (h1 : ∀ j, (Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h3 : ∀ i, (ColF v i).card ∈ ({0,1,3} : Finset ℕ))
    (j : J) : (TC v j).card + (SC v j).card = 4 := by
  have hpart : (Supp v j).filter (fun i => ¬ (ColF v i).card = 3) = SC v j := by
    apply Finset.filter_congr
    intro i hi
    rw [mem_Supp] at hi
    have hji : j ∈ ColF v i := by rw [mem_ColF]; exact hi
    have hpos : 1 ≤ (ColF v i).card := Finset.card_pos.mpr ⟨j, hji⟩
    have hc := h3 i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    constructor
    · intro h
      rcases hc with h' | h' | h' <;> omega
    · intro h
      omega
  have hunion : TC v j ∪ SC v j = Supp v j := by
    rw [← hpart]
    exact Finset.filter_union_filter_not_eq _ _
  have hdisj : Disjoint (TC v j) (SC v j) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [TC, Finset.mem_filter] at hx
    rw [SC, Finset.mem_filter] at hx'
    omega
  rw [← Finset.card_union_of_disjoint hdisj, hunion, (h1 j).1]

theorem exists_singleton_col
    (h1 : ∀ j, (Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h3 : ∀ i, (ColF v i).card ∈ ({0,1,3} : Finset ℕ))
    (j : J) (hnf : (TC v j).card ≠ 4) :
    ∃ i, i ∈ Supp v j ∧ (ColF v i).card = 1 := by
  have hsum := tc_sc_card v h1 h3 j
  have : 0 < (SC v j).card := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp this
  rw [SC, Finset.mem_filter] at hi
  exact ⟨i, hi.1, hi.2⟩

theorem C4Data.rotate1 {j a b c d : J} {p q r s u x y z : ι}
    (h : C4Data v j a b c d p q r s u x y z) :
    C4Data v j b c d a q r s p y u z x :=
  { hp := h.hq, hq := h.hr, hr := h.hs, hs := h.hp
    hp3 := h.hq3, hq3 := h.hr3, hr3 := h.hs3, hs3 := h.hp3
    hS := by rw [h.hS]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    hAB := h.hBC, hBC := h.hCD, hCD := h.hDA, hDA := h.hAB
    hup := h.hyq, hyq := h.hzr, hzr := h.hxs, hxs := h.hup }

theorem C4Data.rotate2 {j a b c d : J} {p q r s u x y z : ι}
    (h : C4Data v j a b c d p q r s u x y z) :
    C4Data v j c d a b r s p q z y x u :=
  { hp := h.hr, hq := h.hs, hr := h.hp, hs := h.hq
    hp3 := h.hr3, hq3 := h.hs3, hr3 := h.hp3, hs3 := h.hq3
    hS := by rw [h.hS]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    hAB := h.hCD, hBC := h.hDA, hCD := h.hAB, hDA := h.hBC
    hup := h.hzr, hyq := h.hxs, hzr := h.hup, hxs := h.hyq }

theorem C4Data.rotate3 {j a b c d : J} {p q r s u x y z : ι}
    (h : C4Data v j a b c d p q r s u x y z) :
    C4Data v j d a b c s p q r x z u y :=
  { hp := h.hs, hq := h.hp, hr := h.hq, hs := h.hr
    hp3 := h.hs3, hq3 := h.hp3, hr3 := h.hq3, hs3 := h.hr3
    hS := by rw [h.hS]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    hAB := h.hDA, hBC := h.hAB, hCD := h.hBC, hDA := h.hCD
    hup := h.hxs, hyq := h.hup, hzr := h.hyq, hxs := h.hzr }


/-! ## Distinctness helpers -/

theorem ne_of_card_three {α : Type*} [DecidableEq α] {x y z : α}
    (h : ({x, y, z} : Finset α).card = 3) : x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  have hyz : ({y, z} : Finset α).card ≤ 2 := by
    rcases eq_or_ne y z with h' | h'
    · subst h'; simp
    · rw [Finset.card_pair h']
  rw [Finset.card_insert_eq_ite] at h
  split at h
  · omega
  · rename_i hx
    have h2 : ({y, z} : Finset α).card = 2 := by omega
    have hyz' : y ≠ z := by
      intro h'
      subst h'
      simp at h2
    refine ⟨?_, ?_, hyz'⟩ <;> intro h'
    · subst h'; exact hx (by simp)
    · subst h'; exact hx (by simp)

theorem ne_of_card_four {α : Type*} [DecidableEq α] {w x y z : α}
    (h : ({w, x, y, z} : Finset α).card = 4) :
    w ≠ x ∧ w ≠ y ∧ w ≠ z ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  have h3 : ({x, y, z} : Finset α).card ≤ 3 := by
    calc ({x, y, z} : Finset α).card ≤ ({y, z} : Finset α).card + 1 := Finset.card_insert_le _ _
      _ ≤ (({z} : Finset α).card + 1) + 1 := by
            have := Finset.card_insert_le y ({z} : Finset α); omega
      _ = 3 := by simp
  rw [Finset.card_insert_eq_ite] at h
  split at h
  · omega
  · rename_i hw
    have hxyz : ({x, y, z} : Finset α).card = 3 := by omega
    obtain ⟨hxy, hxz, hyz⟩ := ne_of_card_three hxyz
    refine ⟨?_, ?_, ?_, hxy, hxz, hyz⟩ <;> intro h'
    · subst h'; exact hw (by simp)
    · subst h'; exact hw (by simp)
    · subst h'; exact hw (by simp)

variable {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]
variable (v : J → ι → ℤ)

namespace C4Data

variable {v : J → ι → ℤ} {j a b c d : J} {p q r s u x y z : ι}

theorem jab_distinct (h : C4Data v j a b c d p q r s u x y z) : j ≠ a ∧ j ≠ b ∧ a ≠ b := by
  have h3 : ({j, a, b} : Finset J).card = 3 := by rw [← h.hp]; exact h.hp3
  exact ne_of_card_three h3

theorem jbc_distinct (h : C4Data v j a b c d p q r s u x y z) : j ≠ b ∧ j ≠ c ∧ b ≠ c := by
  have h3 : ({j, b, c} : Finset J).card = 3 := by rw [← h.hq]; exact h.hq3
  exact ne_of_card_three h3

theorem jcd_distinct (h : C4Data v j a b c d p q r s u x y z) : j ≠ c ∧ j ≠ d ∧ c ≠ d := by
  have h3 : ({j, c, d} : Finset J).card = 3 := by rw [← h.hr]; exact h.hr3
  exact ne_of_card_three h3

theorem jda_distinct (h : C4Data v j a b c d p q r s u x y z) : j ≠ d ∧ j ≠ a ∧ d ≠ a := by
  have h3 : ({j, d, a} : Finset J).card = 3 := by rw [← h.hs]; exact h.hs3
  exact ne_of_card_three h3

theorem pqrs_card (h1 : ∀ j, (Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h : C4Data v j a b c d p q r s u x y z) : ({p, q, r, s} : Finset ι).card = 4 := by
  rw [← h.hS]; exact (h1 j).1

theorem pqrs_distinct (h1 : ∀ j, (Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h : C4Data v j a b c d p q r s u x y z) :
    p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s :=
  ne_of_card_four (pqrs_card (v := v) h1 h)

theorem jabcd_distinct (h1 : ∀ j, (Supp v j).card = 4 ∧ ∀ i, v j i ^ 2 ≤ 1)
    (h2 : ∀ j k, j ≠ k → ∑ i, v j i * v k i = 0)
    (h4 : ∀ n : J → ℤ, (∃ j, Odd (n j)) → ∃ i, Odd (∑ j, n j * v j i))
    (h : C4Data v j a b c d p q r s u x y z) :
    j ≠ a ∧ j ≠ b ∧ j ≠ c ∧ j ≠ d ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  obtain ⟨hja, hjb, hab⟩ := jab_distinct h
  obtain ⟨-, hjc, hbc⟩ := jbc_distinct h
  obtain ⟨-, hjd, hcd⟩ := jcd_distinct h
  obtain ⟨-, -, hda⟩ := jda_distinct h
  obtain ⟨hpq, hpr, hps, hqr, hqs, hrs⟩ := pqrs_distinct (v := v) h1 h
  have hac : a ≠ c := by
    intro hac'
    have heq : ColF v p = ColF v q := by
      rw [h.hp, h.hq, hac']
      ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    exact no_repeat v h1 h2 h4 hpq heq h.hp3
  have hbd : b ≠ d := by
    intro hbd'
    have heq : ColF v q = ColF v r := by
      rw [h.hq, h.hr, hbd']
      ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    exact no_repeat v h1 h2 h4 hqr heq h.hq3
  exact ⟨hja, hjb, hjc, hjd, hab, hac, hda.symm, hbc, hbd, hcd⟩

end C4Data


end Work.BG
