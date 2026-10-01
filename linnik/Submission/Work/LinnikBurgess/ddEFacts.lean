import Mathlib
import Submission.Work.LinnikBurgess.ddLevelDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Divisibility facts for the doubly degenerate coefficients `E₂`, `E₃`

With `Δ_k = ddDsum p e k A C = ∑ A_l^k - ∑ C_l^k` and `E₂ = ddE2 A C`, `E₃ = ddE3 A C` the
quadratic and cubic coefficients of the level-`1` expansion of `prodCoord3`, the two identities

* `2 · E₂ = Δ₁² - Δ₂`
* `2 · (3 · E₃ - Δ₃) = Δ₁³ - 3 · Δ₁ · Δ₂`

hold in `ZMod (p^e)`.  Reducing them modulo `p`, the hypotheses `(D1) p² ∣ Δ₁` and `(D2) p ∣ Δ₂`
give `E₂ ≡ 0`, `3 E₃ ≡ Δ₃ (mod p)`, and `(D3) p ∤ Δ₃` together with `p ≠ 3` makes `E₃` a unit
modulo `p`.  This is `ddEFacts`.
-/

namespace Work.LinnikBurgess

open scoped BigOperators

/-- In `ZMod (p^e)`, an element whose canonical representative is divisible by `p` is a multiple
of `p`. -/
private lemma exists_eq_prime_mul_of_dvd_val {p e : ℕ} [NeZero (p ^ e)] (x : ZMod (p ^ e))
    (h : p ∣ x.val) : ∃ t : ZMod (p ^ e), x = (p : ZMod (p ^ e)) * t := by
  obtain ⟨k, hk⟩ := h
  exact ⟨(k : ZMod (p ^ e)), by rw [← ZMod.natCast_zmod_val x, hk, Nat.cast_mul]⟩

/-- Variant of `exists_eq_prime_mul_of_dvd_val` in additive form. -/
private lemma exists_add_prime_mul_of_dvd_val_sub {p e : ℕ} [NeZero (p ^ e)]
    (a b : ZMod (p ^ e)) (h : p ∣ (a - b).val) :
    ∃ t : ZMod (p ^ e), a = b + (p : ZMod (p ^ e)) * t := by
  obtain ⟨t, ht⟩ := exists_eq_prime_mul_of_dvd_val (a - b) h
  exact ⟨t, sub_eq_iff_eq_add'.mp ht⟩

/-- The quadratic coefficient identity `2 E₂ = Δ₁² - Δ₂`. -/
private lemma two_mul_ddE2 {p e : ℕ} (A C : Fin 3 → ZMod (p ^ e)) :
    2 * ddE2 A C = (ddDsum p e 1 A C) ^ 2 - ddDsum p e 2 A C := by
  simp only [ddE2, ddDsum, Fin.sum_univ_three]
  ring

/-- The cubic coefficient identity `2 (3 E₃ - Δ₃) = Δ₁³ - 3 Δ₁ Δ₂`. -/
private lemma two_mul_three_ddE3_sub {p e : ℕ} (A C : Fin 3 → ZMod (p ^ e)) :
    2 * (3 * ddE3 A C - ddDsum p e 3 A C)
      = (ddDsum p e 1 A C) ^ 3 - 3 * ddDsum p e 1 A C * ddDsum p e 2 A C := by
  simp only [ddE3, ddDsum, Fin.sum_univ_three]
  ring

theorem ddEFacts {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (A C : Fin 3 → ZMod (p ^ e))
    (h1 : (p : ℕ) ^ 2 ∣ (Work.LinnikBurgess.ddDsum p e 1 A C).val)
    (h2 : (p : ℕ) ∣ (Work.LinnikBurgess.ddDsum p e 2 A C).val)
    (h3 : ¬ (p : ℕ) ∣ (Work.LinnikBurgess.ddDsum p e 3 A C).val) :
    (∃ t : ZMod (p ^ e), Work.LinnikBurgess.ddE2 A C = (p : ZMod (p^e)) * t) ∧
    (∃ t : ZMod (p ^ e), 3 * Work.LinnikBurgess.ddE3 A C = Work.LinnikBurgess.ddDsum p e 3 A C + (p : ZMod (p^e)) * t) ∧
    (¬ ∃ t : ZMod (p ^ e), Work.LinnikBurgess.ddE3 A C = (p : ZMod (p^e)) * t) := by
  have hp := (Fact.out : p.Prime)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rcases Nat.eq_zero_or_pos e with he0 | he
  · -- `e = 0`: `ZMod 1` is the zero ring, so `h3` is contradictory
    subst he0
    exfalso
    apply h3
    have hv : (ddDsum p 0 3 A C).val = 0 := by
      have hlt : (ddDsum p 0 3 A C).val < 1 := by simpa using ZMod.val_lt (ddDsum p 0 3 A C)
      omega
    rw [hv]; exact dvd_zero p
  · haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
    have hd : p ∣ p ^ e := by simpa using pow_dvd_pow p (show 1 ≤ e by omega)
    have hφ1 : ZMod.castHom hd (ZMod p) (ddDsum p e 1 A C) = 0 :=
      (Commons.NumberTheory.DirichletCharacter.castHom_eq_zero_iff_dvd_val_one hd _).mpr
        (dvd_trans (show p ∣ p ^ 2 from ⟨p, by ring⟩) h1)
    have hφ2 : ZMod.castHom hd (ZMod p) (ddDsum p e 2 A C) = 0 :=
      (Commons.NumberTheory.DirichletCharacter.castHom_eq_zero_iff_dvd_val_one hd _).mpr h2
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h
      have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1' | h2'
      · exact hp.ne_one h1'
      · exact hp2 h2'
    -- `E₂ ≡ 0 (mod p)`
    have hE2 : ZMod.castHom hd (ZMod p) (ddE2 A C) = 0 := by
      have key : ZMod.castHom hd (ZMod p) (2 * ddE2 A C) = 0 := by
        rw [two_mul_ddE2, map_sub, map_pow, hφ1, hφ2]
        ring
      rw [map_mul, map_ofNat] at key
      exact (mul_eq_zero.mp key).resolve_left h2ne
    -- `3 E₃ ≡ Δ₃ (mod p)`
    have h3E3 : (3 : ZMod p) * ZMod.castHom hd (ZMod p) (ddE3 A C)
        = ZMod.castHom hd (ZMod p) (ddDsum p e 3 A C) := by
      have key : ZMod.castHom hd (ZMod p) (2 * (3 * ddE3 A C - ddDsum p e 3 A C)) = 0 := by
        rw [two_mul_three_ddE3_sub, map_sub, map_mul, map_pow]
        rw [hφ1, hφ2]
        ring
      rw [map_mul, map_ofNat, map_sub, map_mul, map_ofNat] at key
      exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left h2ne)
    have hφ3 : ZMod.castHom hd (ZMod p) (ddDsum p e 3 A C) ≠ 0 := by
      intro h
      exact h3
        ((Commons.NumberTheory.DirichletCharacter.castHom_eq_zero_iff_dvd_val_one hd _).mp h)
    -- hence `E₃` is a unit modulo `p`
    have hφE3 : ZMod.castHom hd (ZMod p) (ddE3 A C) ≠ 0 := by
      intro h
      exact hφ3 (by rw [← h3E3, h, mul_zero])
    refine ⟨?_, ?_, ?_⟩
    · exact exists_eq_prime_mul_of_dvd_val _
        ((Commons.NumberTheory.DirichletCharacter.castHom_eq_zero_iff_dvd_val_one hd _).mp hE2)
    · refine exists_add_prime_mul_of_dvd_val_sub (3 * ddE3 A C) (ddDsum p e 3 A C) ?_
      have : ZMod.castHom hd (ZMod p) (3 * ddE3 A C - ddDsum p e 3 A C) = 0 := by
        rw [map_sub, map_mul, map_ofNat, h3E3, sub_self]
      exact (Commons.NumberTheory.DirichletCharacter.castHom_eq_zero_iff_dvd_val_one hd _).mp this
    · rintro ⟨t, ht⟩
      have hφp : ZMod.castHom hd (ZMod p) (p : ZMod (p^e)) = 0 := by
        rw [map_natCast]; exact (ZMod.natCast_eq_zero_iff p p).mpr (dvd_refl p)
      exact hφE3 (by rw [ht, map_mul, hφp, zero_mul])

end Work.LinnikBurgess
