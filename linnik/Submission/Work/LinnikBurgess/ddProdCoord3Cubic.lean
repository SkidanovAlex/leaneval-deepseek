import Mathlib
import Submission.Work.LinnikBurgess.ddPhi_expansion
import Submission.Work.LinnikBurgess.ddEFacts

set_option linter.style.haveILetI false

namespace Work.LinnikBurgess

open scoped BigOperators

/-- If the canonical representative of `x : ZMod (p^e)` is divisible by `p^k`, then `x` is a
multiple of `(p : ZMod (p ^ e))^k`. -/
lemma exists_eq_prime_pow_mul_of_dvd_val {p e k : ℕ} [NeZero (p ^ e)] (x : ZMod (p ^ e))
    (h : p ^ k ∣ x.val) : ∃ t : ZMod (p ^ e), x = (p : ZMod (p ^ e)) ^ k * t := by
  obtain ⟨m, hm⟩ := h
  refine ⟨(m : ZMod (p ^ e)), ?_⟩
  have hx : x = ((p ^ k * m : ℕ) : ZMod (p ^ e)) := by
    rw [← ZMod.natCast_zmod_val x, hm]
  rw [hx]
  push_cast
  ring

theorem ddProdCoord3Cubic {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (he : 1 ≤ e)
    (A C : Fin 3 → ZMod (p ^ e))
    (h1 : (p : ℕ) ^ 2 ∣ (Work.LinnikBurgess.ddDsum p e 1 A C).val)
    (h2 : (p : ℕ) ∣ (Work.LinnikBurgess.ddDsum p e 2 A C).val)
    (h3 : ¬ (p : ℕ) ∣ (Work.LinnikBurgess.ddDsum p e 3 A C).val) :
    ∃ (a b : ZMod (p ^ e)) (G : Polynomial (ZMod (p ^ e))),
      Work.LinnikBurgess.ddDsum p e 1 A C = (p : ZMod (p ^ e)) ^ 2 * a ∧
      Work.LinnikBurgess.ddE2 A C = (p : ZMod (p ^ e)) * b ∧
      ∀ n : ℕ, Commons.NumberTheory.DirichletCharacter.prodCoord3 p e 1 A C ((n : ℤ) : ZMod (p ^ e))
        = 1 + (p : ZMod (p ^ e)) ^ 3 *
            (a * ((n : ℤ) : ZMod (p ^ e)) + b * ((n : ℤ) : ZMod (p ^ e)) ^ 2
              + Work.LinnikBurgess.ddE3 A C * ((n : ℤ) : ZMod (p ^ e)) ^ 3
              + (p : ZMod (p ^ e)) * G.eval ((n : ℤ) : ZMod (p ^ e))) := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨G₀, hG₀⟩ := ddPhi_expansion (p := p) (e := e) he A C
  obtain ⟨b, hb⟩ := (ddEFacts hp2 hp3 A C h1 h2 h3).1
  obtain ⟨a, ha⟩ := exists_eq_prime_pow_mul_of_dvd_val (p := p) (e := e) (k := 2)
    (ddDsum p e 1 A C) h1
  refine ⟨a, b, G₀, ha, hb, fun n => ?_⟩
  rw [hG₀ n, ha, hb]
  ring

end Work.LinnikBurgess
