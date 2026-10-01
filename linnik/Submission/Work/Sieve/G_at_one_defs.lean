import Mathlib
import Submission.Work.LinnikAreas.Sieve.Defs

/-!
# Auxiliary quantities for Graham's Lemma 9.6, second half (`G(1,χ₀)`)

For a real character `χ₁` mod `q` and level `R` we single out the two quantities that carry the
arithmetic content of `G(1,χ₀) ≤ (q/φ(q)) (Σ_{n ≤ R} a(n)/n)^{-1}`:

* `Qfun χ₁ = ∏_{p | q} (1 + 1/g(p))`, which equals `q/φ(q)` because `g(p) = p - 1` for `p | q`;
* `Zfun χ₁ R k = Σ_{m | rad(q), k·m ≤ R} 1/g(m)`, the local factor at `rad(q)` cut off at level
  `R/k`.

They enter the proof through the exact evaluation of the Selberg weight sums
`Y_k = Σ_{k | d ≤ R, (d,q) = 1} θ_d/h(d) = μ(k) Z_k /(g(k) V(R))`, together with the two
identities `Σ_{(k,q)=1, sf, k ≤ R} Z_k/g(k) = V(R)` and `Q(χ₁) = q/φ(q)`.
-/

open scoped BigOperators
open DirichletCharacter

namespace Work.Sieve

variable {q : ℕ}

/-- `Q(χ₁) = ∏_{p | q} (1 + 1/g(p))`; since `g(p) = p - 1` for `p | q` this is `q / φ(q)`. -/
noncomputable def Qfun [NeZero q] (χ₁ : DirichletCharacter ℂ q) : ℝ :=
  ∏ p ∈ q.primeFactors, (1 + (Work.LinnikAreas.Sieve.gPrime χ₁ p)⁻¹)

/-- The local factor `Z_k = Σ_{m | rad(q), k·m ≤ R} 1/g(m)` of the restricted Selberg sum. -/
noncomputable def Zfun [NeZero q] (χ₁ : DirichletCharacter ℂ q) (R k : ℕ) : ℝ :=
  ∑ m ∈ (Finset.Icc 1 R).filter (fun m => k * m ≤ R ∧ m ∣ ∏ p ∈ q.primeFactors, p),
    1 / Work.LinnikAreas.Sieve.gFun χ₁ m

end Work.Sieve
