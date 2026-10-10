import Mathlib
import Submission.Work.MotK.KleinIdents

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The ruling data of the Crauder–Katz link (G-side)

The design's node `K5` gives the ruling of the target-side exceptional divisor of the
quadro-cubic link by the explicit lines

  `ℓ_c = ℙ(span(A(c), B(c)))`,  `A(c) = dP_c(u₁)`,  `B(c) = dP_c(u₂)`,

where `P = kleinP a b` is the quadratic Pfaffian map, `u_j = b_q(c, e_j)·e₀ − b_q(c, e₀)·e_j` is
the tangent vector of the quadric `{q = 0}` (`q = kleinQ = Σ_k kleinP k`) at `c`, and `dP_c(u)` is
the polarisation `kleinP (c+u) − kleinP c − kleinP u` of the quadratic map `P` in the direction
`u`.  The claim (verified numerically over `𝔽₁₃` for several `(a,b)`) is

  `R(λ·A(c) + μ·B(c)) ∝ c`   for `c ∈ C = V(p₀,…,p₄)`,

i.e. `R` is constant (projectively) on `ℓ_c` for `c ∈ C`; equivalently `ℓ_c` is contained in the
fibre of `R` over `c`, hence (by I2, `kleinP_kleinR`) in the ruling divisor `{s' = 0}` of the
census.  This is the G-side analogue of `Work.MotK.kleinFibre_eq_ker` (which settles the F-side:
the fibres of `P` over `c' ∈ C'` are the *linear* spaces `{x : M(x)·c' = 0}`).

Everything here is over a general commutative ring in the parameters `a b` and the coordinates `c`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotK

variable {R : Type*} [CommRing R]

/-- The `k`-th standard basis vector of `R⁵` (written as a function). -/
def kleinE (k : Fin 5) : Fin 5 → R := Pi.single k 1

/-- The tangent vector `u_k = b_q(c,e_k)·e₀ − b_q(c,e₀)·e_k` of the quadric `q = kleinQ` at `c`
(design `K5`).  Since `b_q` is the polar form of `q`, one has `b_q(c, u_k) = 0`, i.e. `u_k` lies in
the tangent space `T_c{q = 0}`. -/
def kleinTan (a b : R) (c : Fin 5 → R) (k : Fin 5) : Fin 5 → R :=
  fun i => kleinBilin a b c (kleinE k) * kleinE 0 i - kleinBilin a b c (kleinE 0) * kleinE k i

/-- The polarisation of the quadratic Pfaffian map `P = kleinP a b` at `c` in the direction `u`:
`dP_c(u) = kleinP (c+u) − kleinP c − kleinP u`, componentwise. -/
def kleinPolarP (a b : R) (c u : Fin 5 → R) : Fin 5 → R :=
  fun i => kleinP a b (c + u) i - kleinP a b c i - kleinP a b u i

/-- The first ruling vector `A(c) = dP_c(u₁)`. -/
def kleinRuleA (a b : R) (c : Fin 5 → R) : Fin 5 → R := kleinPolarP a b c (kleinTan a b c 1)

/-- The second ruling vector `B(c) = dP_c(u₂)`. -/
def kleinRuleB (a b : R) (c : Fin 5 → R) : Fin 5 → R := kleinPolarP a b c (kleinTan a b c 2)

/-- The point `λ·A(c) + μ·B(c)` of the ruling line `ℓ_c`. -/
def kleinRulePt (a b : R) (c : Fin 5 → R) (l m : R) : Fin 5 → R :=
  fun i => l * kleinRuleA a b c i + m * kleinRuleB a b c i

end Work.MotK
