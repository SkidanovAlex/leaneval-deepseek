import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Lucas

namespace Commons.Data.Nat

/-- Parity version of a `MOD 2` congruence. -/
lemma odd_iff_odd_of_modEq_two {x y : ℕ} (h : x ≡ y [MOD 2]) : (Odd x ↔ Odd y) := by
  simp only [Nat.odd_iff]
  rw [h]

/-- The additivity form of the mod-2 Lucas criterion: `(a+b).choose a` is odd iff
`a` and `b` have disjoint binary expansions (equivalently, adding `a` and `b` in base 2
involves no carry). -/
theorem choose_add_odd_iff (a b : ℕ) : Odd ((a + b).choose a) ↔ a &&& b = 0 := by
  suffices H : ∀ N a b, a + b = N → (Odd ((a + b).choose a) ↔ a &&& b = 0) from H _ a b rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro a b hab
    rcases N with _ | N
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha
      subst hb
      norm_num
    · set a' : ℕ := a.div2 with ha'
      set b' : ℕ := b.div2 with hb'
      cases hα : a.bodd <;> cases hβ : b.bodd
      · -- both even
        have ha : a = Nat.bit false a' := by rw [← Nat.bit_bodd_div2 a, hα, ← ha']
        have hb : b = Nat.bit false b' := by rw [← Nat.bit_bodd_div2 b, hβ, ← hb']
        rw [ha, hb] at hab ⊢
        have hlt : a' + b' < N + 1 := by simp at hab; omega
        have hih := ih (a' + b') hlt a' b' rfl
        have h1 : (Nat.bit false a' + Nat.bit false b').choose (Nat.bit false a')
            ≡ (a' + b').choose a' [MOD 2] := by
          have hluc := Choose.choose_modEq_choose_mod_mul_choose_div_nat
            (n := Nat.bit false a' + Nat.bit false b') (k := Nat.bit false a') (p := 2)
          simp only [Nat.bit_false] at hluc
          have e1 : (2 * a' + 2 * b') % 2 = 0 := by omega
          have e2 : (2 * a') % 2 = 0 := by omega
          have e3 : (2 * a' + 2 * b') / 2 = a' + b' := by omega
          have e4 : (2 * a') / 2 = a' := by omega
          rw [e1, e2, e3, e4] at hluc
          simpa using hluc
        rw [odd_iff_odd_of_modEq_two h1, hih, Nat.land_bit]
        simp only [Nat.bit_false, Bool.false_and]
        constructor <;> intro h <;> omega
      · -- a even, b odd
        have ha : a = Nat.bit false a' := by rw [← Nat.bit_bodd_div2 a, hα, ← ha']
        have hb : b = Nat.bit true b' := by rw [← Nat.bit_bodd_div2 b, hβ, ← hb']
        rw [ha, hb] at hab ⊢
        have hlt : a' + b' < N + 1 := by simp at hab; omega
        have hih := ih (a' + b') hlt a' b' rfl
        have h1 : (Nat.bit false a' + Nat.bit true b').choose (Nat.bit false a')
            ≡ (a' + b').choose a' [MOD 2] := by
          have hluc := Choose.choose_modEq_choose_mod_mul_choose_div_nat
            (n := Nat.bit false a' + Nat.bit true b') (k := Nat.bit false a') (p := 2)
          simp only [Nat.bit_false, Nat.bit_true] at hluc
          have e1 : (2 * a' + (2 * b' + 1)) % 2 = 1 := by omega
          have e2 : (2 * a') % 2 = 0 := by omega
          have e3 : (2 * a' + (2 * b' + 1)) / 2 = a' + b' := by omega
          have e4 : (2 * a') / 2 = a' := by omega
          rw [e1, e2, e3, e4] at hluc
          simpa using hluc
        rw [odd_iff_odd_of_modEq_two h1, hih, Nat.land_bit]
        simp only [Nat.bit_false, Bool.false_and]
        constructor <;> intro h <;> omega
      · -- a odd, b even
        have ha : a = Nat.bit true a' := by rw [← Nat.bit_bodd_div2 a, hα, ← ha']
        have hb : b = Nat.bit false b' := by rw [← Nat.bit_bodd_div2 b, hβ, ← hb']
        rw [ha, hb] at hab ⊢
        have hlt : a' + b' < N + 1 := by simp at hab; omega
        have hih := ih (a' + b') hlt a' b' rfl
        have h1 : (Nat.bit true a' + Nat.bit false b').choose (Nat.bit true a')
            ≡ (a' + b').choose a' [MOD 2] := by
          have hluc := Choose.choose_modEq_choose_mod_mul_choose_div_nat
            (n := Nat.bit true a' + Nat.bit false b') (k := Nat.bit true a') (p := 2)
          simp only [Nat.bit_false, Nat.bit_true] at hluc
          have e1 : (2 * a' + 1 + 2 * b') % 2 = 1 := by omega
          have e2 : (2 * a' + 1) % 2 = 1 := by omega
          have e3 : (2 * a' + 1 + 2 * b') / 2 = a' + b' := by omega
          have e4 : (2 * a' + 1) / 2 = a' := by omega
          rw [e1, e2, e3, e4] at hluc
          simpa using hluc
        rw [odd_iff_odd_of_modEq_two h1, hih, Nat.land_bit]
        simp only [Nat.bit_false, Bool.true_and]
        constructor <;> intro h <;> omega
      · -- both odd
        have ha : a = Nat.bit true a' := by rw [← Nat.bit_bodd_div2 a, hα, ← ha']
        have hb : b = Nat.bit true b' := by rw [← Nat.bit_bodd_div2 b, hβ, ← hb']
        rw [ha, hb] at hab ⊢
        have h1 : (Nat.bit true a' + Nat.bit true b').choose (Nat.bit true a')
            ≡ 0 [MOD 2] := by
          have hluc := Choose.choose_modEq_choose_mod_mul_choose_div_nat
            (n := Nat.bit true a' + Nat.bit true b') (k := Nat.bit true a') (p := 2)
          simp only [Nat.bit_true] at hluc
          have e1 : (2 * a' + 1 + (2 * b' + 1)) % 2 = 0 := by omega
          have e2 : (2 * a' + 1) % 2 = 1 := by omega
          have e3 : (2 * a' + 1 + (2 * b' + 1)) / 2 = a' + b' + 1 := by omega
          have e4 : (2 * a' + 1) / 2 = a' := by omega
          rw [e1, e2, e3, e4] at hluc
          simpa using hluc
        rw [odd_iff_odd_of_modEq_two h1]
        refine iff_of_false ?_ ?_
        · simp [Nat.odd_iff]
        · rw [Nat.land_bit]
          simp only [Nat.bit_true, Bool.true_and]
          intro h
          omega

end Commons.Data.Nat