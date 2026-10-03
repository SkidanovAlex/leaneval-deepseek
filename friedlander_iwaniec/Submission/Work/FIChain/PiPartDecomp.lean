/-
# `Submission.Work.FIChain.PiPartDecomp` — the `Π`-part / `Π`-free decomposition of a squarefree `n`

The companion paper's §10 writes an integer `n` (the inner variable of the window sums) as
`n = n₁ · n₀` where `n₁ ∣ Π(Pz)` collects the small prime factors (`p ≤ Pz`) and `n₀` is
coprime to `Π(Pz)` (i.e. satisfies `PiCond Pz n₀`).  The decomposition is the `n₁ ↦ w·n₁`
change of variables of the companion's Theorem 3.

Here `Π(Pz) = ProdP Pz = primorial Pz` is squarefree, and the natural choice
`n₁ = gcd n Π(Pz)`, `n₀ = n / gcd n Π(Pz)` works whenever `n` is squarefree: the quotient
`n / gcd n Π` is automatically coprime to `Π` in that case (squarefreeness is exactly what is
needed — e.g. `n = 4`, `Pz = 2` would fail without it).

Main result: `PiPartDecomp`.
-/
import Mathlib
import Submission.Work.FIChain.BpWinDefs

set_option autoImplicit false

namespace Work.FIChain

/-- For squarefree `n`, the `Π(Pz)`-part `n₁ = gcd n Π(Pz)` and the cofactor
`n₀ = n / gcd n Π(Pz)` give the decomposition `n = n₁ · n₀` with `n₁ ∣ Π(Pz)` and
`PiCond Pz n₀` (i.e. `n₀` has no prime factor `≤ Pz`). -/
theorem PiPartDecomp (Pz n : ℕ) (hn : Squarefree n) :
    ∃ n₁ n₀ : ℕ, n₁ ∣ Work.FIChain.ProdP Pz ∧ Work.FITop4.PiCond Pz n₀ ∧ n = n₁ * n₀ := by
  refine ⟨Nat.gcd n (Work.FIChain.ProdP Pz), n / Nat.gcd n (Work.FIChain.ProdP Pz),
    Nat.gcd_dvd_right _ _, ?_, ?_⟩
  · -- `n₀ = n / gcd n Π` has no prime factor `≤ Pz`.
    intro q hq hqPz hqdvd
    -- `q` divides both `n₀` and (since `q ≤ Pz` is prime) `Π`, hence `q ∣ gcd n Π = n₁`; and
    -- `q ∣ n₀` also gives `q ∣ n`, so `q * q ∣ n₁ * n₀ = n`, contradicting squarefreeness.
    have hqn : q ∣ n := hqdvd.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n (Work.FIChain.ProdP Pz)))
    have hqPi : q ∣ Work.FIChain.ProdP Pz := (hq.dvd_primorial_iff).mpr hqPz
    have hqg : q ∣ Nat.gcd n (Work.FIChain.ProdP Pz) := Nat.dvd_gcd hqn hqPi
    have hs : q * q ∣ n := by
      rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_left n (Work.FIChain.ProdP Pz))]
      exact Nat.mul_dvd_mul hqg hqdvd
    exact (Nat.squarefree_iff_prime_squarefree.mp hn q hq) hs
  · -- `gcd n Π` divides `n`, so multiplying it by the quotient returns `n`.
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left n (Work.FIChain.ProdP Pz))).symm

end Work.FIChain
