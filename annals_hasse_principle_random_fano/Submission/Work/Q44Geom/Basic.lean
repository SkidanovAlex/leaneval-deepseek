import Mathlib
import Submission.Work.Q44Geom.Setup
import Submission.Work.HP.lam_basic
import Submission.Work.HP.Q44Child.lam_attained

/-!
# Elementary structure lemmas for `Work.Q44Geom.S_count`

This file contains the definitions of the counting set `Sset c s`, of a *good pair* of lattice
vectors, and the elementary structural facts used in the main counting argument.
-/

set_option autoImplicit false
noncomputable section

namespace Work.Q44Geom

open MvPolynomial

/-- If `f` is invariant under translations by the plane spanned by `b₁, b₂`, then both `b₁`
and `b₂` are invariance directions.  Hence a pair that is not contained in `invSub f` (in the
sense that one of the two vectors is *not* an invariance direction) satisfies the
non-invariance hypothesis of `planes44`. -/
lemma inv_of_inv_pair {f : MvPolynomial (Fin 5) ℚ} {b₁ b₂ : Fin 5 → ℚ}
    (h : ∀ (a b : ℚ) (x : Fin 5 → ℚ),
      MvPolynomial.eval (x + a • b₁ + b • b₂) f = MvPolynomial.eval x f) :
    b₁ ∈ invSub f ∧ b₂ ∈ invSub f := by
  constructor
  · intro x t
    simpa using h t 0 x
  · intro x t
    simpa using h 0 t x

/-- The counting set of `S_count`: primitive rank-`3` sublattices of `ℤ^5` with successive
minima bounded by `s` on which `c` vanishes. -/
def Sset (c : Work.HP.Mon 4 4 → ℤ) (s : Fin 3 → ℝ) : Set (Submodule ℤ (Fin 5 → ℤ)) :=
  {L | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
    (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j) ∧ c ∈ Work.HP.vanishOn L}

/-- A *good pair* for `L`: two independent vectors of `L`, of norm bounded by `s 0` and `s 1`,
one of which is not an invariance direction of `f = f44 c`. -/
def goodPair (c : Work.HP.Mon 4 4 → ℤ) (s : Fin 3 → ℝ)
    (L : Submodule ℤ (Fin 5 → ℤ)) : Prop :=
  ∃ b₁ b₂ : Fin 5 → ℤ, b₁ ∈ L ∧ b₂ ∈ L ∧ LinearIndependent ℤ ![b₁, b₂] ∧
    Work.HP.eNorm b₁ ≤ s 0 ∧ Work.HP.eNorm b₂ ≤ s 1 ∧
    (toRatLM b₁ ∉ invSub (f44 c) ∨ toRatLM b₂ ∉ invSub (f44 c))

/-- For a lattice `L` of rank `3` whose successive minima are bounded by `s`, there are two
independent vectors of `L` of norm at most `s 0` and `s 1`. -/
lemma exists_pair_short (L : Submodule ℤ (Fin 5 → ℤ)) (hLrk : Work.HP.rk L = 3)
    (s : Fin 3 → ℝ) (hs : ∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j) :
    ∃ b₁ b₂ : Fin 5 → ℤ, b₁ ∈ L ∧ b₂ ∈ L ∧ LinearIndependent ℤ ![b₁, b₂] ∧
      Work.HP.eNorm b₁ ≤ s 0 ∧ Work.HP.eNorm b₂ ≤ s 1 := by
  obtain ⟨f, hmem, hind, hnorm⟩ :=
    Work.HP.Q44Child.lam_attained L 2 (by norm_num) (by omega)
  have hind2 : LinearIndependent ℤ ![f 0, f 1] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hsum : (∑ j : Fin 2, g j • f j) = 0 := by
      have h : (∑ j : Fin 2, g j • (![f 0, f 1] j)) = ∑ j : Fin 2, g j • f j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        fin_cases j <;> simp
      rw [h] at hg
      exact hg
    exact (Fintype.linearIndependent_iff.mp hind) g hsum i
  refine ⟨f 0, f 1, hmem 0, hmem 1, hind2, ?_, ?_⟩
  · exact le_trans (hnorm 0) (hs 0)
  · exact le_trans (hnorm 1) (hs 1)

/-- If `L ∈ Sset c s` has no good pair, then two independent vectors of `L` lie in the
invariance lattice `latW (f44 c)`. -/
lemma bad_structure {c : Work.HP.Mon 4 4 → ℤ} {s : Fin 3 → ℝ}
    {L : Submodule ℤ (Fin 5 → ℤ)} (hL : L ∈ Sset c s) (hbad : ¬ goodPair c s L) :
    ∃ x y : Fin 5 → ℤ, x ∈ L ∧ y ∈ L ∧ x ∈ latW (f44 c) ∧ y ∈ latW (f44 c) ∧
      LinearIndependent ℤ ![x, y] := by
  obtain ⟨hprim, hLrk, hs, hvanish⟩ := hL
  obtain ⟨b₁, b₂, hb₁, hb₂, hind, hn₁, hn₂⟩ := exists_pair_short L hLrk s hs
  by_cases h₁ : toRatLM b₁ ∈ invSub (f44 c)
  · by_cases h₂ : toRatLM b₂ ∈ invSub (f44 c)
    · exact ⟨b₁, b₂, hb₁, hb₂, mem_latW_iff.mpr h₁, mem_latW_iff.mpr h₂, hind⟩
    · exact absurd ⟨b₁, b₂, hb₁, hb₂, hind, hn₁, hn₂, Or.inr h₂⟩ hbad
  · exact absurd ⟨b₁, b₂, hb₁, hb₂, hind, hn₁, hn₂, Or.inl h₁⟩ hbad

/-! ## Arithmetic for the final bound -/

theorem arith_1 {a b c : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    a ^ 4 * b ^ 4 ≤ (a * b * c) ^ ((7 : ℝ) / 2) := by
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le ha0 hab
  have hc1 : (1:ℝ) ≤ c := le_trans ha (le_trans hab hbc)
  have hc0 : (0:ℝ) < c := lt_of_lt_of_le zero_lt_one hc1
  have hab0 : (0:ℝ) < a * b := mul_pos ha0 hb0
  have h1 : (a * b) ^ (4:ℝ) = (a * b) ^ ((7:ℝ)/2) * (a * b) ^ ((1:ℝ)/2) := by
    rw [← Real.rpow_add hab0]; norm_num
  have h2 : (a*b)^((1:ℝ)/2) ≤ c := by
    have hab2 : a * b ≤ c ^ 2 := by nlinarith
    calc (a*b)^((1:ℝ)/2) = Real.sqrt (a*b) := by rw [Real.sqrt_eq_rpow]
      _ ≤ Real.sqrt (c^2) := Real.sqrt_le_sqrt hab2
      _ = c := Real.sqrt_sq hc0.le
  have h3 : (a*b*c)^((7:ℝ)/2) = (a*b)^((7:ℝ)/2) * c^((7:ℝ)/2) := by
    rw [Real.mul_rpow (le_of_lt hab0) (le_of_lt hc0)]
  have hmul : a^4 * b^4 ≤ (a*b)^(4:ℝ) := by
    rw [show (a*b)^(4:ℝ) = a^4 * b^4 by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast, mul_pow]]
  rw [h3]
  have h4 : (0:ℝ) ≤ (a*b)^((7:ℝ)/2) := Real.rpow_nonneg (le_of_lt hab0) _
  have h5 : c ≤ c ^ ((7:ℝ)/2) := by
    have := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num : (1:ℝ) ≤ (7:ℝ)/2)
    simpa using this
  calc a ^ 4 * b ^ 4 ≤ (a*b)^(4:ℝ) := hmul
    _ = (a*b)^((7:ℝ)/2) * (a*b)^((1:ℝ)/2) := h1
    _ ≤ (a*b)^((7:ℝ)/2) * c := mul_le_mul_of_nonneg_left h2 h4
    _ ≤ (a*b)^((7:ℝ)/2) * c^((7:ℝ)/2) := mul_le_mul_of_nonneg_left h5 h4

theorem arith_2 {a b c : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    a ^ 4 * b ^ 4 * c ^ 2 ≤ (a * b * c) ^ ((7 : ℝ) / 2) := by
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le ha0 hab
  have hc1 : (1:ℝ) ≤ c := le_trans ha (le_trans hab hbc)
  have hc0 : (0:ℝ) < c := lt_of_lt_of_le zero_lt_one hc1
  have hab0 : (0:ℝ) < a * b := mul_pos ha0 hb0
  have h2 : (a*b)^((1:ℝ)/2) ≤ c := by
    have hab2 : a * b ≤ c ^ 2 := by nlinarith
    calc (a*b)^((1:ℝ)/2) = Real.sqrt (a*b) := by rw [Real.sqrt_eq_rpow]
      _ ≤ Real.sqrt (c^2) := Real.sqrt_le_sqrt hab2
      _ = c := Real.sqrt_sq hc0.le
  have h3 : (a*b*c)^((7:ℝ)/2) = (a*b)^((7:ℝ)/2) * c^((7:ℝ)/2) := by
    rw [Real.mul_rpow (le_of_lt hab0) (le_of_lt hc0)]
  have h4 : (0:ℝ) ≤ (a*b)^((7:ℝ)/2) := Real.rpow_nonneg (le_of_lt hab0) _
  have h1 : (a * b) ^ (4:ℝ) = (a*b)^((7:ℝ)/2) * (a*b)^((1:ℝ)/2) := by
    rw [← Real.rpow_add hab0]; norm_num
  have hmul : a^4 * b^4 ≤ (a*b)^(4:ℝ) := by
    rw [show (a*b)^(4:ℝ) = a^4 * b^4 by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast, mul_pow]]
  have h5 : c ^ 3 ≤ c ^ ((7:ℝ)/2) := by
    have := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num : (3:ℝ) ≤ (7:ℝ)/2)
    simpa using this
  rw [h3]
  calc a^4 * b^4 * c^2 ≤ (a*b)^(4:ℝ) * c^2 :=
        mul_le_mul_of_nonneg_right hmul (by positivity)
    _ = ((a*b)^((7:ℝ)/2) * (a*b)^((1:ℝ)/2)) * c^2 := by rw [h1]
    _ ≤ ((a*b)^((7:ℝ)/2) * c) * c^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h4) (by positivity)
    _ = (a*b)^((7:ℝ)/2) * c^3 := by ring
    _ ≤ (a*b)^((7:ℝ)/2) * c^((7:ℝ)/2) := mul_le_mul_of_nonneg_left h5 h4

theorem arith_3 {a b c : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    a ^ 3 * b ^ 3 * c ^ 3 ≤ (a * b * c) ^ ((7 : ℝ) / 2) := by
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hb1 : (1:ℝ) ≤ b := le_trans ha hab
  have hc1 : (1:ℝ) ≤ c := le_trans hb1 hbc
  have hab1 : (1:ℝ) ≤ a * b := by
    have := mul_le_mul ha hb1 (by norm_num : (0:ℝ) ≤ 1) ha0.le
    simpa using this
  have hab0 : (0:ℝ) < a * b := lt_of_lt_of_le zero_lt_one hab1
  have habc1 : (1:ℝ) ≤ a * b * c := by
    have := mul_le_mul hab1 hc1 (by norm_num : (0:ℝ) ≤ 1) hab0.le
    simpa using this
  have h1 : a^3 * b^3 * c^3 = (a*b*c)^(3:ℝ) := by
    rw [show (a*b*c)^(3:ℝ) = (a*b*c)^(3:ℕ) by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]]
    ring
  rw [h1]
  exact Real.rpow_le_rpow_of_exponent_le habc1 (by norm_num : (3:ℝ) ≤ (7:ℝ)/2)

theorem arith_4 {a b c : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    a ^ 3 * b ^ 5 * c ^ 2 ≤ (a * b * c) ^ ((7 : ℝ) / 2) := by
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le ha0 hab
  have hb1 : (1:ℝ) ≤ b := le_trans ha hab
  have hc1 : (1:ℝ) ≤ c := le_trans hb1 hbc
  have hc0 : (0:ℝ) < c := lt_of_lt_of_le zero_lt_one hc1
  have hab0 : (0:ℝ) < a * b := mul_pos ha0 hb0
  have hna : (0:ℝ) ≤ a ^ ((7:ℝ)/2) := Real.rpow_nonneg ha0.le _
  have hnb : (0:ℝ) ≤ b ^ ((7:ℝ)/2) := Real.rpow_nonneg hb0.le _
  have hnc : (0:ℝ) ≤ c ^ ((7:ℝ)/2) := Real.rpow_nonneg hc0.le _
  have ha3 : a ^ 3 ≤ a ^ ((7:ℝ)/2) := by
    have h := Real.rpow_le_rpow_of_exponent_le ha (by norm_num : (3:ℝ) ≤ (7:ℝ)/2)
    simpa using h
  have hb5 : b ^ 5 ≤ b ^ ((7:ℝ)/2) * c ^ ((3:ℝ)/2) := by
    have h1 : b ^ 5 = b ^ ((7:ℝ)/2) * b ^ ((3:ℝ)/2) := by
      rw [← Real.rpow_add hb0]; norm_num
    rw [h1]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hb0.le hbc (by norm_num)) hnb
  have hstep : a ^ 3 * b ^ 5 ≤ a ^ ((7:ℝ)/2) * (b ^ ((7:ℝ)/2) * c ^ ((3:ℝ)/2)) :=
    mul_le_mul ha3 hb5 (by positivity) hna
  have hc2 : c ^ ((3:ℝ)/2) * c ^ 2 ≤ c ^ ((7:ℝ)/2) := by
    rw [← Real.rpow_natCast c 2, ← Real.rpow_add hc0]
    norm_num
  calc a ^ 3 * b ^ 5 * c ^ 2
      ≤ (a ^ ((7:ℝ)/2) * (b ^ ((7:ℝ)/2) * c ^ ((3:ℝ)/2))) * c ^ 2 :=
        mul_le_mul_of_nonneg_right hstep (by positivity)
    _ = a ^ ((7:ℝ)/2) * b ^ ((7:ℝ)/2) * (c ^ ((3:ℝ)/2) * c ^ 2) := by ring
    _ ≤ a ^ ((7:ℝ)/2) * b ^ ((7:ℝ)/2) * c ^ ((7:ℝ)/2) :=
        mul_le_mul_of_nonneg_left hc2 (mul_nonneg hna hnb)
    _ = (a * b * c) ^ ((7:ℝ)/2) := by
        rw [Real.mul_rpow hab0.le hc0.le, Real.mul_rpow ha0.le hb0.le]

end Work.Q44Geom
