import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The formal derivative on `𝔽(t)` is additive

`Work.Genus.deriv` is defined on the *canonical* (reduced) representation `f.num / f.denom` given by
`RatFunc.num` / `RatFunc.denom`.  To compute with it one first has to know that the classical
quotient rule

  `(p / q) ↦ (p' q - p q') / q²`

gives the same answer for *any* representation `p / q` of the same rational function.  This is what
`derivAux_congr` below records: if `p * s = r * q` is a polynomial identity (`p/q = r/s` in `𝔽(t)`),
then `derivAux p q = derivAux r s`.  The proof differentiates the polynomial identity (legitimate,
since `Polynomial.derivative` satisfies the product rule) and then does one algebraic
computation in the field `𝔽(t)`; no coprimality/primitivity argument is needed.

With that, additivity is immediate from `RatFunc.num_denom_add`, which exhibits the canonical
representation of `f + g` as a common multiple of the "product" representation
`(f.num * g.denom + f.denom * g.num) / (f.denom * g.denom)`.
-/

namespace Work.Genus.Deriv

open Polynomial

/-- **The quotient rule applied to an arbitrary pair `(p, q)` of polynomials**, as a rational
function: `(p' q - p q') / q²`.  For `q ≠ 0` this depends only on the rational function `p / q`
(`derivAux_congr`), and for the canonical pair `p = f.num`, `q = f.denom` it *is* `Work.Genus.deriv`
(`deriv_eq_derivAux`). -/
noncomputable def derivAux {F : Type*} [Field F] (p q : F[X]) : RatFunc F :=
  (algebraMap F[X] (RatFunc F) p.derivative * algebraMap F[X] (RatFunc F) q
    - algebraMap F[X] (RatFunc F) p * algebraMap F[X] (RatFunc F) q.derivative)
    / (algebraMap F[X] (RatFunc F) q) ^ 2

/-- `Work.Genus.deriv` is `derivAux` evaluated on the canonical numerator/denominator pair. -/
theorem deriv_eq_derivAux {F : Type*} [Field F] (f : RatFunc F) :
    Work.Genus.deriv f = derivAux f.num f.denom := rfl

/-- **The quotient rule is additive in the pair representation.**  For `q₁, q₂ ≠ 0` the quotient
rule applied to the "sum" pair `(p₁ q₂ + p₂ q₁, q₁ q₂)` — which represents `p₁/q₁ + p₂/q₂` — equals
the sum of the two quotient rules.  This is a single `field_simp`/`ring` computation in `𝔽(t)`,
using the product rule for `Polynomial.derivative`. -/
theorem derivAux_add {F : Type*} [Field F] (p₁ p₂ q₁ q₂ : F[X]) (h₁ : q₁ ≠ 0) (h₂ : q₂ ≠ 0) :
    derivAux (p₁ * q₂ + p₂ * q₁) (q₁ * q₂) = derivAux p₁ q₁ + derivAux p₂ q₂ := by
  have hQ₁ : algebraMap F[X] (RatFunc F) q₁ ≠ 0 := RatFunc.algebraMap_ne_zero h₁
  have hQ₂ : algebraMap F[X] (RatFunc F) q₂ ≠ 0 := RatFunc.algebraMap_ne_zero h₂
  simp only [derivAux, derivative_add, derivative_mul]
  simp only [map_add, map_mul]
  field_simp
  first | refl_ring1 | ring

/-- **The quotient rule is independent of the chosen representation.**  If `p * s = r * q` in `𝔽[X]`
(so that `p / q = r / s` in `𝔽(t)`), with `q, s ≠ 0`, then `derivAux p q = derivAux r s`.  No
coprimality assumption is needed: differentiating the polynomial identity `p s = r q` supplies
exactly the relation that makes the numerators `p' q - p q'` and `r' s - r s'` match after
cross-multiplication by the denominators squared. -/
theorem derivAux_congr {F : Type*} [Field F] {p q r s : F[X]} (hq : q ≠ 0) (hs : s ≠ 0)
    (h : p * s = r * q) : derivAux p q = derivAux r s := by
  -- differentiate the polynomial identity
  have hd : p.derivative * s + p * s.derivative
      = r.derivative * q + r * q.derivative := by
    have hh := congrArg derivative h
    rwa [derivative_mul, derivative_mul] at hh
  have hQ : algebraMap F[X] (RatFunc F) q ≠ 0 := RatFunc.algebraMap_ne_zero hq
  have hS : algebraMap F[X] (RatFunc F) s ≠ 0 := RatFunc.algebraMap_ne_zero hs
  -- the same two identities mapped into `𝔽(t)`
  have hpq : algebraMap F[X] (RatFunc F) p * algebraMap F[X] (RatFunc F) s
      = algebraMap F[X] (RatFunc F) r * algebraMap F[X] (RatFunc F) q := by
    rw [← map_mul, ← map_mul, h]
  have hder : algebraMap F[X] (RatFunc F) p.derivative * algebraMap F[X] (RatFunc F) s
      + algebraMap F[X] (RatFunc F) p * algebraMap F[X] (RatFunc F) s.derivative
      = algebraMap F[X] (RatFunc F) r.derivative * algebraMap F[X] (RatFunc F) q
      + algebraMap F[X] (RatFunc F) r * algebraMap F[X] (RatFunc F) q.derivative := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_add, hd]
  simp only [derivAux]
  rw [div_eq_div_iff (pow_ne_zero 2 hQ) (pow_ne_zero 2 hS)]
  linear_combination (norm := first | refl_ring1 | ring1) (algebraMap F[X] (RatFunc F) q * algebraMap F[X] (RatFunc F) s) * hder
    - (algebraMap F[X] (RatFunc F) q.derivative * algebraMap F[X] (RatFunc F) s
        + algebraMap F[X] (RatFunc F) q * algebraMap F[X] (RatFunc F) s.derivative) * hpq

/-- The formal derivative `Work.Genus.deriv` on `F(t)` is additive.  (The quotient rule is
independent of the chosen numerator/denominator representation: scaling `(p, q) ↦ (c p, c q)`
multiplies both `p'q - pq'` and `q²` by `c²`.  Then use `RatFunc.num_denom_add` and
`Polynomial.derivative_add`/`derivative_mul`.) -/
theorem deriv_add {F : Type*} [Field F] (f g : RatFunc F) :
    Work.Genus.deriv (f + g) = Work.Genus.deriv f + Work.Genus.deriv g := by
  -- `num_denom_add` compares the canonical representation of `f + g` with the product one
  have h₁ : Work.Genus.deriv (f + g)
      = derivAux (f.num * g.denom + f.denom * g.num) (f.denom * g.denom) := by
    rw [deriv_eq_derivAux]
    exact derivAux_congr (RatFunc.denom_ne_zero _)
      (mul_ne_zero f.denom_ne_zero g.denom_ne_zero) (RatFunc.num_denom_add f g)
  have h₂ : derivAux (f.num * g.denom + f.denom * g.num) (f.denom * g.denom)
      = derivAux f.num f.denom + derivAux g.num g.denom := by
    rw [mul_comm f.denom g.num]
    exact derivAux_add f.num g.num f.denom g.denom f.denom_ne_zero g.denom_ne_zero
  rw [h₁, h₂, deriv_eq_derivAux f, deriv_eq_derivAux g]

end Work.Genus.Deriv
