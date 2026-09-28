import Mathlib
import Submission.Work.HP.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Shared definitions for the non-Archimedean factor (node N11)

Notation: `d` is the degree, `n` the number of variables minus one (so `n+1` variables),
`Mon d n` the set of exponent vectors of degree-`d` monomials, `NN d n = #(Mon d n)`.
-/

noncomputable section
open Finset MvPolynomial
set_option autoImplicit false

namespace Work.HP
namespace NA

/-- `f_a(x) = Σ_m a_m x^m`, coefficients in a commutative ring `R`. -/
def fev {R : Type*} [CommRing R] (d n : ℕ) (a : Mon d n → R) (x : Fin (n + 1) → R) : R :=
  ∑ m, a m * veronese d n x m

/-- `∂_{x_j} f_a(x)`. -/
def dfev {R : Type*} [CommRing R] (d n : ℕ) (a : Mon d n → R) (x : Fin (n + 1) → R)
    (j : Fin (n + 1)) : R :=
  ∑ m, a m * ((m.1 j : ℕ) : R) * ∏ i, x i ^ (if i = j then (m.1 i : ℕ) - 1 else (m.1 i : ℕ))

/-- The gradient vector of `f_a` at `x`. -/
def gradv {R : Type*} [CommRing R] (d n : ℕ) (a : Mon d n → R) (x : Fin (n + 1) → R) :
    Fin (n + 1) → R :=
  fun j => dfev d n a x j

/-- `σ(a;Q)` where `a` is a coefficient vector reduced modulo `Q`. -/
def sigQ (d n : ℕ) (Q : ℕ) (a : Mon d n → ZMod Q) : ℝ :=
  (({b : Fin (n + 1) → ZMod Q | Ideal.span (Set.range b) = ⊤ ∧ fev d n a b = 0}.ncard : ℕ) : ℝ)
    / (Q : ℝ) ^ n

/-- Vectors of `(ZMod Q)^N` generating the unit ideal (i.e. primitive modulo `Q`). -/
def IsPrimMod {N : ℕ} (Q : ℕ) (a : Fin N → ZMod Q) : Prop := Ideal.span (Set.range a) = ⊤

end NA
end Work.HP

namespace Work.HP
namespace NA

/-- `Ideal.span (range a) = ⊤`, for vectors indexed by an arbitrary finite type. -/
def IsPrimGen {ι : Type*} [Fintype ι] (Q : ℕ) (a : ι → ZMod Q) : Prop :=
  Ideal.span (Set.range a) = ⊤

/-- The primitive coefficient vectors modulo `q`. -/
def primFinset (d n q : ℕ) [NeZero q] : Finset (Mon d n → ZMod q) := by
  classical
  exact Finset.univ.filter (fun a => IsPrimGen q a)

end NA
end Work.HP

namespace Work.HP
namespace NA

/-- `p^k ∣ y` inside `ZMod (p^r)`. -/
def vpDvd (p r k : ℕ) (y : ZMod (p ^ r)) : Prop := ∃ c : ZMod (p ^ r), y = (p : ZMod (p ^ r)) ^ k * c

/-- `R^{(e)}(p^r)`: `a` is primitive and has a primitive zero `x` of `f_a` modulo `p^r` at which
the gradient vanishes to order exactly `e` (`f_a(x)` and `∇f_a(x)` live in `ZMod (p^r)`). -/
def Rset (d n p r e : ℕ) (a : Mon d n → ZMod (p ^ r)) : Prop :=
  IsPrimGen (p ^ r) a ∧ ∃ x : Fin (n + 1) → ZMod (p ^ r),
    IsPrimGen (p ^ r) x ∧ fev d n a x = 0 ∧
    (∀ j, vpDvd p r e (gradv d n a x j)) ∧
    (e < r → ¬ (∀ j, vpDvd p r (e + 1) (gradv d n a x j)))

end NA
end Work.HP

namespace Work.HP
namespace NA

/-- Locally soluble coefficients modulo `p^r`: primitive `a` with a primitive zero of `f_a` mod `p^r`. -/
def FlocSet (d n p r : ℕ) (a : Mon d n → ZMod (p ^ r)) : Prop :=
  IsPrimGen (p ^ r) a ∧ ∃ x : Fin (n + 1) → ZMod (p ^ r),
    IsPrimGen (p ^ r) x ∧ fev d n a x = 0

end NA
end Work.HP

namespace Work.HP
namespace NA

/-- The finite set `F^loc(p^r) ⊆ (ZMod (p^r))^{N}` of locally soluble coefficients. -/
def FlocInset (d n p r : ℕ) [NeZero (p ^ r)] : Finset (Mon d n → ZMod (p ^ r)) := by
  classical
  exact (primFinset d n (p ^ r)).filter (FlocSet d n p r)

end NA
end Work.HP
