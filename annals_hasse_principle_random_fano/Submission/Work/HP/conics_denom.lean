import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.box_card
import Submission.Work.HP.ConicsDefs

/-!
# `Work.HP.conics_denom`

The number of primitive coefficient vectors `a : Mon 2 2 → ℤ` (ternary quadratic forms) of
Euclidean norm at most `A` grows at least like `A^6`.

`Mon 2 2` is the six-element set of exponent vectors of degree-two monomials in three variables
(`Work.HP.Conics.card_mon`), so the coefficient vector `a` is a vector in `ℤ^6` and
`IsPrim a = (Finset.univ.gcd a = 1)`.

**Proof.**  Count primitive vectors inside the coordinate box `[-B,B]^6` with
`B = ⌊A/√6⌋`; every vector of that box lies in the Euclidean ball of radius `A`.  A vector of
the box is either zero, primitive, or non-primitive and non-zero, and in the last case its gcd
`g` satisfies `2 ≤ g ≤ B` and divides all coordinates, so the vector lies in the set of
`g`-divisible vectors of the box (of size `(2⌊B/g⌋+1)^6`).  Hence

`#(primitive vectors of the box) ≥ (2B+1)^6 - 1 - ∑_{g=2}^{B} (2⌊B/g⌋+1)^6`.

For `2 ≤ g ≤ B` we have `2⌊B/g⌋+1 ≤ 3B/g`, so the subtracted sum is at most
`729 B^6 ∑_{g=2}^{B} 1/g^6`; the series bound `∑_{g=2}^{B} 1/g^6 ≤ 7/320` (by comparison with the
telescoping sum `(1/5)(1/(g-1)^5 - 1/g^5)`) gives `∑ ≤ 5103/320 · B^6 ≤ 16 B^6`, which is at most
`(1/4)(2B+1)^6`.  Thus the box contains at least `(1/2)(2B+1)^6` primitive vectors, which is
`≥ A^6/432` for large `A`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open Filter Finset

namespace Work.HP

/-! ## The coordinate box `[-B,B]^6` in `Mon 2 2 → ℤ` -/

/-- The coordinate box of radius `B` inside `Mon 2 2 → ℤ`, a copy of `[-B,B]^6`. -/
def box6 (B : ℕ) : Finset (Mon 2 2 → ℤ) :=
  Fintype.piFinset (fun _ : Mon 2 2 => Finset.Icc (-(B : ℤ)) (B : ℤ))

/-- The box has `(2B+1)^6` elements. -/
theorem box6_card (B : ℕ) : (box6 B).card = (2 * B + 1) ^ 6 := by
  have h := (box_card (ι := Mon 2 2) B).1
  rw [Conics.card_mon] at h
  have h2 : ((box6 B).card : ℝ) = ((2 * B + 1) ^ 6 : ℕ) := by
    push_cast
    exact h
  exact_mod_cast h2

/-- The vectors of the box all of whose coordinates are divisible by `g` number
`(2⌊B/g⌋+1)^6`. -/
theorem box6_div_card (B g : ℕ) (hg : 1 ≤ g) :
    ((box6 B).filter (fun a => ∀ i, (g : ℤ) ∣ a i)).card = (2 * (B / g) + 1) ^ 6 := by
  have h := (box_card (ι := Mon 2 2) B).2 g hg
  rw [Conics.card_mon] at h
  have h2 : (((box6 B).filter (fun a => ∀ i, (g : ℤ) ∣ a i)).card : ℝ)
      = ((2 * (B / g) + 1) ^ 6 : ℕ) := by
    push_cast
    exact h
  exact_mod_cast h2

/-! ## Primitive and non-primitive vectors of the box -/

/-- The gcd of the coordinates of an integer vector is non-negative. -/
theorem gcd_univ_nonneg (a : Mon 2 2 → ℤ) : 0 ≤ Finset.univ.gcd a :=
  Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd (s := Finset.univ) (f := a))

/-- The gcd of a non-zero vector does not vanish. -/
theorem gcd_univ_ne_zero {a : Mon 2 2 → ℤ} (ha : a ≠ 0) : Finset.univ.gcd a ≠ 0 := by
  rw [Finset.gcd_ne_zero_iff]
  by_contra h
  push Not at h
  exact ha (funext fun i => h i (Finset.mem_univ i))

/-- A non-zero non-primitive vector has a common divisor `g ≥ 2`, the gcd of its coordinates
(which is a natural number). -/
theorem exists_nat_dvd_of_not_prim {a : Mon 2 2 → ℤ} (ha : a ≠ 0)
    (h : Finset.univ.gcd a ≠ 1) : ∃ g : ℕ, 2 ≤ g ∧ ∀ i, (g : ℤ) ∣ a i := by
  have hnn := gcd_univ_nonneg a
  have h0 := gcd_univ_ne_zero ha
  have h2 : (2 : ℤ) ≤ Finset.univ.gcd a := by omega
  have hcast : (((Finset.univ.gcd a).toNat : ℕ) : ℤ) = Finset.univ.gcd a :=
    Int.toNat_of_nonneg hnn
  refine ⟨(Finset.univ.gcd a).toNat, ?_, ?_⟩
  · have : ((2 : ℕ) : ℤ) ≤ (((Finset.univ.gcd a).toNat : ℕ) : ℤ) := by
      rw [hcast]; exact h2
    exact_mod_cast this
  · intro i
    rw [hcast]
    exact Finset.gcd_dvd (Finset.mem_univ i)

/-- Counting bound: the primitive vectors of the box are all vectors of the box, except the
origin and the vectors lying in one of the sets of `g`-divisible vectors, `2 ≤ g ≤ B`. -/
theorem prim_box_lower6 (B : ℕ) :
    ((box6 B).card : ℝ) - 1
        - ∑ g ∈ Finset.Icc 2 B, (2 * ((B / g : ℕ) : ℝ) + 1) ^ 6
      ≤ (((box6 B).filter (fun a => Finset.univ.gcd a = 1)).card : ℝ) := by
  classical
  set Z : Finset (Mon 2 2 → ℤ) := box6 B with hZ
  set P : Finset (Mon 2 2 → ℤ) := Z.filter (fun a => Finset.univ.gcd a = 1) with hP
  set Q : Finset (Mon 2 2 → ℤ) := Z.filter (fun a => ¬ (Finset.univ.gcd a = 1)) with hQ
  set N : Finset (Mon 2 2 → ℤ) := Q.filter (fun a => a ≠ 0) with hN
  have hPQ : P.card + Q.card = Z.card :=
    Finset.card_filter_add_card_filter_not (s := Z) (fun a => Finset.univ.gcd a = 1)
  -- `N` is covered by the union of the `g`-divisible subsets of `Z`
  have hsub : N ⊆ (Finset.Icc 2 B).biUnion (fun g => Z.filter (fun a => ∀ i, (g : ℤ) ∣ a i)) := by
    intro a ha
    rw [hN, Finset.mem_filter] at ha
    obtain ⟨haQ, ha0⟩ := ha
    rw [hQ, Finset.mem_filter] at haQ
    obtain ⟨haZ, hag⟩ := haQ
    obtain ⟨g, hg2, hgdvd⟩ := exists_nat_dvd_of_not_prim ha0 hag
    have hBnd : g ≤ B := by
      obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact ha0 (funext fun i => hcon i)
      have hai : |a i| ≤ (B : ℤ) := by
        rw [hZ, box6, Fintype.mem_piFinset] at haZ
        exact abs_le.mpr (Finset.mem_Icc.mp (haZ i))
      have hgi : (g : ℤ) ≤ |a i| := by
        have hdvd : (g : ℤ) ∣ |a i| := (dvd_abs (g : ℤ) (a i)).2 (hgdvd i)
        exact Int.le_of_dvd (abs_pos.mpr hi) hdvd
      have : (g : ℤ) ≤ (B : ℤ) := le_trans hgi hai
      exact_mod_cast this
    rw [Finset.mem_biUnion]
    exact ⟨g, Finset.mem_Icc.mpr ⟨hg2, hBnd⟩, Finset.mem_filter.mpr ⟨haZ, hgdvd⟩⟩
  have hNle : N.card ≤ ∑ g ∈ Finset.Icc 2 B, (Z.filter (fun a => ∀ i, (g : ℤ) ∣ a i)).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  -- `Q = {0} ∪ N`
  have hQle : Q.card ≤ 1 + N.card := by
    have hsub2 : Q ⊆ ({0} : Finset (Mon 2 2 → ℤ)) ∪ N := by
      intro a ha
      rw [Finset.mem_union]
      by_cases haz : a = 0
      · exact Or.inl (by rw [haz]; simp)
      · exact Or.inr (by rw [hN, Finset.mem_filter]; exact ⟨ha, haz⟩)
    have h1 := Finset.card_le_card hsub2
    have h2 := Finset.card_union_le ({0} : Finset (Mon 2 2 → ℤ)) N
    simp only [Finset.card_singleton] at h1 h2
    omega
  have hsum : (Q.card : ℝ) ≤ 1 + ∑ g ∈ Finset.Icc 2 B, (2 * ((B / g : ℕ) : ℝ) + 1) ^ 6 := by
    have h2 : (N.card : ℝ) ≤ ∑ g ∈ Finset.Icc 2 B, (2 * ((B / g : ℕ) : ℝ) + 1) ^ 6 := by
      have hcast : (N.card : ℝ)
          ≤ ((∑ g ∈ Finset.Icc 2 B, (Z.filter (fun a => ∀ i, (g : ℤ) ∣ a i)).card : ℕ) : ℝ) :=
        by exact_mod_cast hNle
      rw [Nat.cast_sum] at hcast
      refine le_trans hcast (Finset.sum_le_sum ?_)
      intro g hg
      rw [hZ, box6_div_card B g (le_trans (by norm_num : 1 ≤ 2) (Finset.mem_Icc.mp hg).1)]
      push_cast
      exact le_of_eq (by ring)
    have h1 : (Q.card : ℝ) ≤ 1 + (N.card : ℝ) := by exact_mod_cast hQle
    linarith
  have hPZ : (P.card : ℝ) = (Z.card : ℝ) - (Q.card : ℝ) := by
    have : (P.card : ℝ) + (Q.card : ℝ) = (Z.card : ℝ) := by exact_mod_cast hPQ
    linarith
  rw [hPZ]
  linarith

/-! ## Bounds for the sums over `g` -/

/-- `1/g^6` is bounded by a telescoping difference, for `g ≥ 3`. -/
theorem inv_pow6_le (g : ℕ) (hg : 3 ≤ g) :
    (1 : ℝ) / (g : ℝ) ^ 6
      ≤ (1 / 5) * (1 / ((g - 1 : ℕ) : ℝ) ^ 5 - 1 / (g : ℝ) ^ 5) := by
  have hg1 : 1 ≤ g := by omega
  have hgc : (g : ℝ) = ((g - 1 : ℕ) : ℝ) + 1 := by
    have h : g - 1 + 1 = g := Nat.sub_add_cancel hg1
    rw [← h]; push_cast; ring
  have hx0 : (0 : ℝ) < ((g - 1 : ℕ) : ℝ) := by
    have : 0 < g - 1 := by omega
    exact_mod_cast this
  have hx1 : (0 : ℝ) < ((g - 1 : ℕ) : ℝ) + 1 := by linarith
  rw [hgc]
  have key : (5 : ℝ) * (((g - 1 : ℕ) : ℝ)) ^ 5
      ≤ (((((g - 1 : ℕ) : ℝ)) + 1) ^ 5 - (((g - 1 : ℕ) : ℝ)) ^ 5) * ((((g - 1 : ℕ) : ℝ)) + 1) := by
    nlinarith [sq_nonneg (((g - 1 : ℕ) : ℝ)), pow_nonneg hx0.le 3, pow_nonneg hx0.le 4,
      pow_pos hx0 5]
  have h1 : (0 : ℝ) < (((g - 1 : ℕ) : ℝ) + 1) ^ 6 := by positivity
  have h2 : (0 : ℝ) < 5 * (((g - 1 : ℕ) : ℝ)) ^ 5 := by positivity
  rw [div_le_iff₀ h1]
  rw [show (1 / 5 : ℝ) * (1 / ((g - 1 : ℕ) : ℝ) ^ 5 - 1 / (((g - 1 : ℕ) : ℝ) + 1) ^ 5)
        * (((g - 1 : ℕ) : ℝ) + 1) ^ 6
      = (((((g - 1 : ℕ) : ℝ)) + 1) ^ 5 - (((g - 1 : ℕ) : ℝ)) ^ 5) * ((((g - 1 : ℕ) : ℝ)) + 1)
        / (5 * (((g - 1 : ℕ) : ℝ)) ^ 5) by
    rw [div_sub_div]
    field_simp
    ring
    all_goals positivity]
  rw [le_div_iff₀ h2]
  linarith [key]

/-- Telescoping identity `∑_{g=a}^{B} (f (g-1) - f g) = f (a-1) - f B`. -/
theorem sum_Icc_sub_eq (f : ℕ → ℝ) {a B : ℕ} (ha : 1 ≤ a) (haB : a ≤ B) :
    ∑ g ∈ Finset.Icc a B, (f (g - 1) - f g) = f (a - 1) - f B := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le haB
  induction k with
  | zero => simp
  | succ k ih =>
    have haB' : a ≤ a + k := by omega
    rw [Nat.add_succ, Finset.sum_Icc_succ_top (by omega)]
    rw [ih haB']
    have h1 : (a + k + 1 - 1 : ℕ) = a + k := by omega
    rw [h1]
    ring

/-- `∑_{g=2}^{B} 1/g^6 ≤ 7/320` (the true value tends to `ζ(6) - 1 ≈ 0.0173`). -/
theorem sum_inv_pow6_le (B : ℕ) :
    ∑ g ∈ Finset.Icc 2 B, (1 : ℝ) / (g : ℝ) ^ 6 ≤ 7 / 320 := by
  rcases Nat.lt_or_ge B 2 with hBlt | hBge
  · have hempty : Finset.Icc 2 B = ∅ := by
      rw [Finset.Icc_eq_empty_iff]; omega
    rw [hempty, Finset.sum_empty]; norm_num
  · rcases eq_or_lt_of_le hBge with hB2 | hB2
    · -- `B = 2`
      have hset : Finset.Icc 2 B = {2} := by
        subst hB2; ext x; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega
      rw [hset, Finset.sum_singleton]
      norm_num
    · have hsplit : Finset.Icc 2 B = insert 2 (Finset.Icc 3 B) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have htele : ∑ g ∈ Finset.Icc 3 B, ((1 : ℝ) / ((g - 1 : ℕ) : ℝ) ^ 5 - 1 / (g : ℝ) ^ 5)
          = 1 / (2 : ℝ) ^ 5 - 1 / (B : ℝ) ^ 5 := by
        have h := sum_Icc_sub_eq (fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ 5) (a := 3) (B := B)
          (by norm_num) (Nat.succ_le_of_lt hB2)
        simpa using h
      have hle : ∑ g ∈ Finset.Icc 3 B, (1 : ℝ) / (g : ℝ) ^ 6 ≤ 1 / 160 := by
        calc ∑ g ∈ Finset.Icc 3 B, (1 : ℝ) / (g : ℝ) ^ 6
            ≤ ∑ g ∈ Finset.Icc 3 B,
                (1 / 5) * ((1 : ℝ) / ((g - 1 : ℕ) : ℝ) ^ 5 - 1 / (g : ℝ) ^ 5) :=
              Finset.sum_le_sum (fun g hg => inv_pow6_le g (Finset.mem_Icc.mp hg).1)
          _ = (1 / 5) * ∑ g ∈ Finset.Icc 3 B,
                ((1 : ℝ) / ((g - 1 : ℕ) : ℝ) ^ 5 - 1 / (g : ℝ) ^ 5) := by
              rw [Finset.mul_sum]
          _ = (1 / 5) * (1 / (2 : ℝ) ^ 5 - 1 / (B : ℝ) ^ 5) := by rw [htele]
          _ ≤ 1 / 160 := by
              have hB0 : (0 : ℝ) < (B : ℝ) ^ 5 := by
                have : 0 < B := by omega
                positivity
              have hpos : (0 : ℝ) < 1 / (B : ℝ) ^ 5 := one_div_pos.mpr hB0
              linarith
      rw [hsplit, Finset.sum_insert (by rw [Finset.mem_Icc]; omega)]
      have h2 : (1 : ℝ) / (((2 : ℕ) : ℝ)) ^ 6 = 1 / 64 := by norm_num
      rw [h2]
      linarith

/-- The `g`-sum of the box union bound is at most a quarter of the leading term. -/
theorem sum_box_bound6 (B : ℕ) :
    ∑ g ∈ Finset.Icc 2 B, (2 * ((B / g : ℕ) : ℝ) + 1) ^ 6
      ≤ (1 / 4) * (2 * (B : ℝ) + 1) ^ 6 := by
  have hterm : ∀ g ∈ Finset.Icc 2 B,
      (2 * ((B / g : ℕ) : ℝ) + 1) ^ 6 ≤ (729 * (B : ℝ) ^ 6) * (1 / (g : ℝ) ^ 6) := by
    intro g hg
    obtain ⟨hg2, hgB⟩ := Finset.mem_Icc.mp hg
    have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast (by omega : 0 < g)
    have hBg : (1 : ℝ) ≤ (B : ℝ) / g := by
      rw [le_div_iff₀ hgpos, one_mul]; exact_mod_cast hgB
    have h1 : ((B / g : ℕ) : ℝ) ≤ (B : ℝ) / g := by
      rw [le_div_iff₀ hgpos]
      have hd : (((B / g : ℕ) : ℝ)) * (g : ℝ) ≤ (B : ℝ) := by
        exact_mod_cast Nat.div_mul_le_self B g
      linarith
    have h2 : 2 * ((B / g : ℕ) : ℝ) + 1 ≤ 3 * ((B : ℝ) / g) := by linarith
    have hnn : 0 ≤ 2 * ((B / g : ℕ) : ℝ) + 1 := by positivity
    calc (2 * ((B / g : ℕ) : ℝ) + 1) ^ 6 ≤ (3 * ((B : ℝ) / g)) ^ 6 :=
          pow_le_pow_left₀ hnn h2 6
      _ = (729 * (B : ℝ) ^ 6) * (1 / (g : ℝ) ^ 6) := by
          rw [mul_pow, div_pow, div_eq_mul_inv]
          ring
  calc ∑ g ∈ Finset.Icc 2 B, (2 * ((B / g : ℕ) : ℝ) + 1) ^ 6
      ≤ ∑ g ∈ Finset.Icc 2 B, (729 * (B : ℝ) ^ 6) * (1 / (g : ℝ) ^ 6) :=
        Finset.sum_le_sum hterm
    _ = (729 * (B : ℝ) ^ 6) * ∑ g ∈ Finset.Icc 2 B, (1 / (g : ℝ) ^ 6) := by
        rw [Finset.mul_sum]
    _ ≤ (729 * (B : ℝ) ^ 6) * (7 / 320) := by
        refine mul_le_mul_of_nonneg_left (sum_inv_pow6_le B) ?_
        positivity
    _ ≤ (1 / 4) * (2 * (B : ℝ) + 1) ^ 6 := by
        have hB6 : (0 : ℝ) ≤ (B : ℝ) ^ 6 := by positivity
        have h2 : (2 * (B : ℝ)) ^ 6 = 64 * (B : ℝ) ^ 6 := by ring
        have h3 : (729 * (B : ℝ) ^ 6) * (7 / 320) ≤ (1 / 4) * (2 * (B : ℝ)) ^ 6 := by
          rw [h2]
          nlinarith [hB6]
        have h1 : (2 * (B : ℝ)) ^ 6 ≤ (2 * (B : ℝ) + 1) ^ 6 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 6
        have h4 : (1 / 4 : ℝ) * (2 * (B : ℝ)) ^ 6 ≤ (1 / 4) * (2 * (B : ℝ) + 1) ^ 6 :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
        linarith

/-! ## The height ball -/

/-- Every coordinate of an integer vector is bounded by its Euclidean norm. -/
theorem abs_coord_le_eNorm6 (a : Mon 2 2 → ℤ) (m : Mon 2 2) : |(a m : ℝ)| ≤ eNorm a := by
  have h1 : ((a m : ℝ)) ^ 2 ≤ ∑ i, ((a i : ℝ)) ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg ((a i : ℝ))) (Finset.mem_univ m)
  calc |(a m : ℝ)| = Real.sqrt (((a m : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ i, ((a i : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = eNorm a := rfl

/-- The height ball is contained in the coordinate box of radius `⌈A⌉`. -/
theorem primSet_subset_box6 (A : ℝ) (P : (Mon 2 2 → ℤ) → Prop) :
    primSet 2 2 A P ⊆ (↑(box6 ⌈A⌉₊) : Set (Mon 2 2 → ℤ)) := by
  intro a ha
  rw [Finset.mem_coe, box6, Fintype.mem_piFinset]
  intro m
  rw [Finset.mem_Icc]
  have h : |(a m : ℤ)| ≤ (⌈A⌉₊ : ℤ) := by
    have h₁ : |(a m : ℝ)| ≤ (⌈A⌉₊ : ℝ) :=
      le_trans (abs_coord_le_eNorm6 a m) (le_trans ha.2.1 (Nat.le_ceil A))
    exact_mod_cast h₁
  exact abs_le.mp h

/-- The height ball is finite. -/
theorem primSet_finite6 (A : ℝ) (P : (Mon 2 2 → ℤ) → Prop) : (primSet 2 2 A P).Finite :=
  (Finset.finite_toSet _).subset (primSet_subset_box6 A P)

/-! ## The main statement -/

/-- The number of primitive coefficient vectors `a : Mon 2 2 → ℤ` of Euclidean norm at most
`A` grows at least like `A^6`. -/
theorem conics_denom :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ A in Filter.atTop, c * A ^ 6 ≤ Work.HP.primCount 2 2 A (fun _ => True) := by
  refine ⟨1 / 432, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (100 : ℝ)] with A hA
  have hs : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt_lt : Real.sqrt 6 < 3 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3)]
    norm_num
  set B : ℕ := ⌊A / Real.sqrt 6⌋₊ with hB
  have hdiv0 : (0 : ℝ) ≤ A / Real.sqrt 6 := div_nonneg (by linarith) hs.le
  have hBle : (B : ℝ) ≤ A / Real.sqrt 6 := by rw [hB]; exact Nat.floor_le hdiv0
  have hBlt : A / Real.sqrt 6 < (B : ℝ) + 1 := by
    rw [hB]; exact Nat.lt_floor_add_one _
  have hB2 : 2 ≤ B := by
    have h1 : (2 : ℝ) ≤ A / Real.sqrt 6 := by
      rw [le_div_iff₀ hs]
      nlinarith [hsqrt_lt, hs]
    exact Nat.le_floor h1
  -- Step 1: the primitive vectors of the box lie in the height ball.
  have hsubset : ((box6 B).filter (fun a => Finset.univ.gcd a = 1) : Set (Mon 2 2 → ℤ))
      ⊆ primSet 2 2 A (fun _ => True) := by
    intro a ha
    rw [Finset.mem_coe, Finset.mem_filter] at ha
    obtain ⟨hain, hprim⟩ := ha
    rw [box6, Fintype.mem_piFinset] at hain
    refine ⟨hprim, ?_, trivial⟩
    have hcoord : ∀ m, |(a m : ℝ)| ≤ (B : ℝ) := by
      intro m
      have h' : (|a m| : ℤ) ≤ (B : ℤ) := abs_le.mpr (Finset.mem_Icc.mp (hain m))
      exact_mod_cast h'
    have hsq : ∑ m, ((a m : ℝ)) ^ 2 ≤ 6 * (B : ℝ) ^ 2 := by
      calc ∑ m, ((a m : ℝ)) ^ 2 ≤ ∑ m, (B : ℝ) ^ 2 :=
            Finset.sum_le_sum (fun m _ => by
              rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (B : ℝ))]
              exact hcoord m)
        _ = 6 * (B : ℝ) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Conics.card_mon, nsmul_eq_mul]
            norm_num
    calc eNorm a = Real.sqrt (∑ m, ((a m : ℝ)) ^ 2) := rfl
      _ ≤ Real.sqrt (6 * (B : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt 6 * (B : ℝ) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6), Real.sqrt_sq (by positivity)]
      _ ≤ A := by
          rw [le_div_iff₀ hs] at hBle
          linarith
  have hfin : (primSet 2 2 A (fun _ => True)).Finite := primSet_finite6 A _
  have hcard := Set.ncard_le_ncard hsubset hfin
  rw [Set.ncard_coe_finset] at hcard
  have hprimCount : (((box6 B).filter (fun a => Finset.univ.gcd a = 1)).card : ℝ)
      ≤ primCount 2 2 A (fun _ => True) := by
    rw [primCount]
    exact_mod_cast hcard
  -- Step 2: at least half the box consists of primitive vectors.
  have hhalf : (1 / 2) * (2 * (B : ℝ) + 1) ^ 6
      ≤ (((box6 B).filter (fun a => Finset.univ.gcd a = 1)).card : ℝ) := by
    have h1 := prim_box_lower6 B
    have h2 := sum_box_bound6 B
    have h3 : (2 * (B : ℝ) + 1) ^ 6 = ((box6 B).card : ℝ) := by
      rw [box6_card]; push_cast; ring
    rw [← h3] at h1
    have h4 : (12 : ℝ) ≤ (2 * (B : ℝ) + 1) ^ 6 := by
      have hB2' : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB2
      have h5 : (5 : ℝ) ≤ 2 * (B : ℝ) + 1 := by linarith
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) h5 6
      norm_num at this
      linarith
    linarith
  -- Step 3: `(2B+1)^6 ≫ A^6`.
  have hBgt : A / (2 * Real.sqrt 6) < (B : ℝ) := by
    have hA2 : (2 : ℝ) < A / Real.sqrt 6 := by
      rw [lt_div_iff₀ hs]
      nlinarith [hsqrt_lt, hs]
    have h1 : A / (2 * Real.sqrt 6) < A / Real.sqrt 6 - 1 := by
      have hpos : (0 : ℝ) < 2 * Real.sqrt 6 := by positivity
      rw [div_lt_iff₀ hpos]
      have hA2' : 2 * Real.sqrt 6 < A := by nlinarith [hA2, hs]
      have he : (A / Real.sqrt 6 - 1) * (2 * Real.sqrt 6) = 2 * A - 2 * Real.sqrt 6 := by
        field_simp
      rw [he]; linarith
    linarith
  have h216 : (Real.sqrt 6) ^ 6 = 216 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
    rw [show (Real.sqrt 6) ^ 6 = ((Real.sqrt 6) ^ 2) ^ 3 by ring, h]
    norm_num
  have hbound : (1 / 432) * A ^ 6 ≤ (1 / 2) * (2 * (B : ℝ)) ^ 6 := by
    have hA0 : (0 : ℝ) < A := by linarith
    have h2B : A / Real.sqrt 6 < 2 * (B : ℝ) := by
      have h2 : A / Real.sqrt 6 = 2 * (A / (2 * Real.sqrt 6)) := by
        field_simp
      rw [h2]
      linarith
    have h1 : (A / Real.sqrt 6) ^ 6 < (2 * (B : ℝ)) ^ 6 :=
      pow_lt_pow_left₀ h2B (by positivity) (by norm_num : (6 : ℕ) ≠ 0)
    have h2 : (A / Real.sqrt 6) ^ 6 = A ^ 6 / 216 := by
      rw [div_pow, h216]
    rw [h2] at h1
    linarith
  have hmono : (1 / 2) * (2 * (B : ℝ)) ^ 6 ≤ (1 / 2) * (2 * (B : ℝ) + 1) ^ 6 := by
    have h1 : (2 * (B : ℝ)) ≤ (2 * (B : ℝ) + 1) := by linarith
    have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * (B : ℝ)) h1 6
    linarith
  linarith [hbound, hmono, hhalf, hprimCount]

end Work.HP
