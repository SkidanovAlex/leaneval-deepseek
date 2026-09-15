import Mathlib
import Submission.Commons.NumberTheory.Sieve.KPseudorandom_mean

namespace Commons.NumberTheory.Sieve

/-- For a natural number `n` and modulus `p`, the class of `n` in `ZMod p` vanishes exactly when
`p` divides `n`. -/
private lemma zmod_natCast_eq_zero_iff (p n : ℕ) : (n : ZMod p) = 0 ↔ p ∣ n := by
  rw [← Int.natCast_dvd_natCast (m := p) (n := n),
    ← Int.cast_natCast (R := ZMod p)]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd (n : ℤ) p

/-- The rational `a / n` is interpreted by `qmod` exactly as the quotient of `a` by `n` in
`ZMod p`, whenever `p` does not divide the (nonzero) denominator `n`. -/
theorem qmod_rat_div {p : ℕ} [Fact p.Prime] (a : ℤ) (n : ℕ) (hn : n ≠ 0) (hp : ¬ p ∣ n) :
    Commons.NumberTheory.Sieve.qmod p ((a : ℚ) / (n : ℚ))
      = (a : ZMod p) / (n : ZMod p) := by
  set q : ℚ := (a : ℚ) / (n : ℚ) with hqdef
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  have hqeq : q = Rat.divInt a (n : ℤ) := by
    rw [hqdef, Rat.divInt_eq_div]; push_cast; ring
  -- Write `q = num / den` in lowest terms; then `q = a / n` forces `den ∣ n` and, crucially,
  -- the cross-multiplication identity `num * n = a * den`.
  obtain ⟨c, ha, hnd⟩ := Rat.num_den_mk (q := q) (n := a) (d := (n : ℤ)) hnZ hqeq
  have hdvd : (q.den : ℤ) ∣ (n : ℤ) := ⟨c, by rw [hnd, mul_comm]⟩
  have hden_dvd : q.den ∣ n := Int.natCast_dvd_natCast.mp hdvd
  have hcross : (q.num : ℤ) * (n : ℤ) = a * (q.den : ℤ) := by
    rw [ha, hnd]; ring
  have hcast : (q.num : ZMod p) * (n : ZMod p) = (a : ZMod p) * (q.den : ZMod p) := by
    have h := congrArg (fun z : ℤ => (z : ZMod p)) hcross
    push_cast at h
    exact h
  -- Both denominators are invertible: `p ∤ n` and `den ∣ n`.
  have hd : (q.den : ZMod p) ≠ 0 := by
    intro h
    exact hp (((zmod_natCast_eq_zero_iff p q.den).mp h).trans hden_dvd)
  have hnz : (n : ZMod p) ≠ 0 := by
    intro h
    exact hp ((zmod_natCast_eq_zero_iff p n).mp h)
  rw [qmod, div_eq_div_iff hd hnz]
  exact hcast

end Commons.NumberTheory.Sieve
