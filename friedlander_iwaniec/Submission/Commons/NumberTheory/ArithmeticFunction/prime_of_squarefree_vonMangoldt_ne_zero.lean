import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

namespace Commons.NumberTheory.ArithmeticFunction

theorem prime_of_squarefree_vonMangoldt_ne_zero {c : ℕ} (hsf : Squarefree c)
    (hv : ArithmeticFunction.vonMangoldt c ≠ 0) : c.Prime :=
  Nat.squarefree_and_prime_pow_iff_prime.mp
    ⟨hsf, ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hv⟩

end Commons.NumberTheory.ArithmeticFunction