/-
# The class decomposition of the pair sum (*FI* §§11–12, 15)

The local variance of *FI* (11.7) is

`E(d) = Σ_{a < d} |Σ_{r̄s ≡ a (d)} α_{rs} (r/d')|²`

(`Work.FIPlan.Evar`), where `d' = oddPart d` and `(r/d')` is the Jacobi symbol.  Writing
`X_a = Σ_{r̄s ≡ a (d)} α_{rs} (r/d')` for the `a`-th class sum, the large-sieve step of §§11–12 and
§15 bounds the pair sum over the congruence `r₁s₂ ≡ r₂s₁ (mod d)` by the geometric mean of the
two variances `E`, by Cauchy–Schwarz applied to `Σ_a X_a conj(Y_a)`.

This file contains the vocabulary only: the Jacobi weight `jw`, the class sum `clsSum`, the pair
sum `pairSum`, and the identification of the two presentations of a single summand.
-/
import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.Evar_le_trivial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The Jacobi weight `(r | d')` of the local variance (11.7), as a complex number: `d' = oddPart d`
is the odd part of `d` (8.15). -/
def jw (d r : ℕ) : ℂ := ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ)

/-- The Jacobi weight is an integer, hence fixed by complex conjugation. -/
@[simp] lemma star_jw (d r : ℕ) : star (jw d r) = jw d r := by simp [jw]

/-- The `a`-th class sum `X_a = Σ_{r̄s ≡ a (d)} α_{rs} (r|d')` of the local variance (11.7): the
sum over the pairs `(r,s)` of the box with `r` coprime to `d` and `s ≡ r a (mod d)`. -/
def clsSum (R S d : ℕ) (α : ℕ → ℕ → ℂ) (a : ℕ) : ℂ :=
  ∑ p ∈ EvarCls R S d a, α p.1 p.2 * jw d p.1

/-- A single summand of the pair sum, in the class-grouped presentation: the pair `(p,q)` of the
box contributes `u_p conj(v_q) (p₁|d')(q₁|d')` when `p₁q₂ ≡ q₁p₂ (mod d)`. -/
def pairTerm (d : ℕ) (u v : ℕ → ℕ → ℂ) (p q : ℕ × ℕ) : ℂ :=
  if ((p.1 * q.2 : ℕ) : ZMod d) = ((q.1 * p.2 : ℕ) : ZMod d) then
    (u p.1 p.2 * jw d p.1) * star (v q.1 q.2 * jw d q.1)
  else 0

/-- The pair sum of the large-sieve step of *FI* §§11–12, 15:
`Σ_{(r₁,s₁),(r₂,s₂)} [r₁s₂ ≡ r₂s₁ (d)] u_{r₁s₁} conj(v_{r₂s₂}) (r₁|d')(r₂|d')`. -/
def pairSum (R S d : ℕ) (u v : ℕ → ℕ → ℂ) : ℂ :=
  ∑ r1 ∈ Finset.Icc 1 (2*R), ∑ s1 ∈ Finset.Icc 1 (2*S),
    ∑ r2 ∈ Finset.Icc 1 (2*R), ∑ s2 ∈ Finset.Icc 1 (2*S),
      (if ((r1*s2 : ℕ) : ZMod d) = ((r2*s1 : ℕ) : ZMod d) then
        u r1 s1 * star (v r2 s2) *
          ((jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ)
       else 0)

/-- The two presentations of a single summand agree: `u conj(v) (r₁|d')(r₂|d')` (with the two
Jacobi symbols combined under one integer cast) equals `(u (r₁|d')) conj(v (r₂|d'))`. -/
lemma pairTerm_eq (d : ℕ) (u v : ℕ → ℕ → ℂ) (r1 s1 r2 s2 : ℕ) :
    u r1 s1 * star (v r2 s2) *
        ((jacobiSym (r1 : ℤ) (Work.FIPlan.oddPart d) * jacobiSym (r2 : ℤ) (Work.FIPlan.oddPart d) : ℤ) : ℂ)
      = (u r1 s1 * jw d r1) * star (v r2 s2 * jw d r2) := by
  rw [star_mul, star_jw]
  simp only [jw]
  push_cast
  ring

end

end Work.FIArea4
