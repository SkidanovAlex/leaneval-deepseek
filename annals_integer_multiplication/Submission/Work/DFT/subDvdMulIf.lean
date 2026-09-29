import Mathlib

namespace Work.DFT

/-- If `t ∣ (u : ℤ) - (v : ℤ)` and `u, v < t` (as naturals) then `u = v`:
the difference lies strictly between `-t` and `t`, so divisibility forces it to vanish. -/
private lemma eq_of_dvd_sub_of_lt {t u v : ℕ} (h : (t : ℤ) ∣ (u : ℤ) - (v : ℤ))
    (hu : u < t) (hv : v < t) : u = v := by
  have habs : |(u : ℤ) - (v : ℤ)| < (t : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hz : (u : ℤ) - (v : ℤ) = 0 := Int.eq_zero_of_abs_lt_dvd h habs
  have : (u : ℤ) = (v : ℤ) := by omega
  omega

/-- Product of two `if ... then _ else 0` factors: it is nonzero only when both
conditions hold. -/
private lemma ite_mul_ite (P Q : Prop) [Decidable P] [Decidable Q] (x y : ℂ) :
    (if P then x else 0) * (if Q then y else 0) = if P ∧ Q then x * y else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- The `j = a` case of the key identification: two residues `j, a < t * T'`
agree exactly when they have the same remainder mod `T'` and congruent quotients
`j / T'`, `a / T'` modulo `t`. -/
private lemma eq_of_residue_eq_and_dvd (t T' j a : ℕ) (ht : 0 < t) (hT' : 0 < T')
    (hj : j < t * T') (ha : a < t * T')
    (hP : (t : ℤ) ∣ (((j / T') % t : ℕ) : ℤ) - (((a / T') % t : ℕ) : ℤ))
    (hQ : j % T' = a % T') : j = a := by
  have hjq : j / T' < t := (Nat.div_lt_iff_lt_mul hT').mpr hj
  have haq : a / T' < t := (Nat.div_lt_iff_lt_mul hT').mpr ha
  have hmod : (j / T') % t = (a / T') % t :=
    eq_of_dvd_sub_of_lt hP (Nat.mod_lt _ ht) (Nat.mod_lt _ ht)
  have hnum : j / T' = a / T' := by
    rw [← Nat.mod_eq_of_lt hjq, ← Nat.mod_eq_of_lt haq]
    exact hmod
  calc j = T' * (j / T') + j % T' := (Nat.div_add_mod j T').symm
    _ = T' * (a / T') + a % T' := by rw [hnum, hQ]
    _ = a := Nat.div_add_mod a T'

theorem subDvdMulIf (t T' j a : ℕ) (ht : 0 < t) (hT' : 0 < T')
    (hj : j < t * T') (ha : a < t * T') :
    (if (t : ℤ) ∣ (((j / T') % t : ℕ) : ℤ) - (((a / T') % t : ℕ) : ℤ) then (t : ℂ) else 0) *
      (if j % T' = a % T' then (T' : ℂ) else 0) =
      if j = a then ((t * T' : ℕ) : ℂ) else 0 := by
  have key :
      ((t : ℤ) ∣ (((j / T') % t : ℕ) : ℤ) - (((a / T') % t : ℕ) : ℤ) ∧ j % T' = a % T') ↔
        j = a := by
    constructor
    · rintro ⟨hP, hQ⟩
      exact eq_of_residue_eq_and_dvd t T' j a ht hT' hj ha hP hQ
    · rintro rfl
      exact ⟨by simp, by simp⟩
  have hprod :
      (if (t : ℤ) ∣ (((j / T') % t : ℕ) : ℤ) - (((a / T') % t : ℕ) : ℤ) then (t : ℂ) else 0) *
        (if j % T' = a % T' then (T' : ℂ) else 0)
      = (if ((t : ℤ) ∣ (((j / T') % t : ℕ) : ℤ) - (((a / T') % t : ℕ) : ℤ) ∧
            j % T' = a % T') then ((t * T' : ℕ) : ℂ) else 0) := by
    rw [ite_mul_ite, ← Nat.cast_mul]
  rw [hprod]
  by_cases h : j = a
  · rw [ite_eq_left h, ite_eq_left (key.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun hpq => h (key.mp hpq))]

end Work.DFT
