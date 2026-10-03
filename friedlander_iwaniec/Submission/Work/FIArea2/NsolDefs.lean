import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The congruence count `N(a;q)` of *FI* §8 and the Jacobi-symbol sum `(8.13)`

This file fixes the vocabulary used in `Work.FIArea2.card_solutions_eight_thirteen`
(*FI*, Corollary 8.3, (8.13)):

* `Work.FIArea2.Nsol q a = N(a;q)`, the number of pairs `(γ₁,γ₂)` modulo `q` with
  `a γ₁² ≡ γ₂² (mod q)`;
* `Work.FIArea2.Jsum q a = q Σ_{d|q} (φ(d)/d)(a/d)`, the right-hand side of (8.13);
* the total extensions `NsolF`, `JsumF` to arithmetic functions (value `0` at `q = 0`)
  which make the multiplicativity argument available through `ArithmeticFunction`.
-/

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- **`N(a;q)`**: the number of solutions `(γ₁,γ₂) ∈ (ℤ/q)²` of `aγ₁² ≡ γ₂² (mod q)`.
For `q = 0` we set the value to be `0` (the definition is a total function of `q` so
that it can be used as an arithmetic function). -/
noncomputable def Nsol (q : ℕ) (a : ℕ) : ℕ :=
  if h : q = 0 then 0 else
    letI : NeZero q := ⟨h⟩
    ((Finset.univ : Finset (ZMod q × ZMod q)).filter
      (fun p => (a : ZMod q) * p.1 ^ 2 = p.2 ^ 2)).card

/-- **The right-hand side of (8.13)**: `q Σ_{d|q} (φ(d)/d)(a/d)` with `(a/d)` the Jacobi
symbol. -/
noncomputable def Jsum (q : ℕ) (a : ℤ) : ℝ :=
  (q : ℝ) * ∑ d ∈ q.divisors, ((Nat.totient d : ℝ) / (d : ℝ)) * (jacobiSym a d : ℝ)

lemma Nsol_zero (a : ℕ) : Nsol 0 a = 0 := by simp [Nsol]

/-- The defining expression of `Nsol` for a non-zero modulus. -/
lemma Nsol_eq_filter (q : ℕ) [NeZero q] (a : ℕ) :
    Nsol q a = ((Finset.univ : Finset (ZMod q × ZMod q)).filter
        (fun p => (a : ZMod q) * p.1 ^ 2 = p.2 ^ 2)).card := by
  rw [Nsol, dif_neg (NeZero.ne q)]

lemma Nsol_one (a : ℕ) : Nsol 1 a = 1 := by
  have h : ∀ p : ZMod 1 × ZMod 1, p = (0, 0) := fun p => Subsingleton.elim p _
  rw [Nsol_eq_filter, Finset.card_eq_one]
  exact ⟨(0, 0), by ext p; simp [h p]⟩

lemma Jsum_zero (a : ℤ) : Jsum 0 a = 0 := by simp [Jsum]

lemma Jsum_one (a : ℤ) : Jsum 1 a = 1 := by simp [Jsum]

/-- `Nsol` as an arithmetic function (value `0` at `0`), for the multiplicativity argument. -/
noncomputable def NsolF (a : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun q => (Nsol q a : ℝ), by simp [Nsol]⟩

/-- `Jsum` as an arithmetic function (value `0` at `0`), for the multiplicativity argument. -/
noncomputable def JsumF (a : ℤ) : ArithmeticFunction ℝ :=
  ⟨fun q => if q = 0 then 0 else Jsum q a, by simp⟩

@[simp] lemma NsolF_apply (a : ℕ) (q : ℕ) : NsolF a q = (Nsol q a : ℝ) := rfl

@[simp] lemma NsolF_zero (a : ℕ) : NsolF a 0 = 0 := by simp [NsolF, Nsol]

lemma JsumF_eq (a : ℤ) {q : ℕ} (hq : q ≠ 0) : JsumF a q = Jsum q a := by
  change (if q = 0 then (0 : ℝ) else Jsum q a) = Jsum q a
  rw [if_neg hq]

lemma NsolF_eq (a : ℕ) {q : ℕ} (hq : q ≠ 0) : NsolF a q = (Nsol q a : ℝ) := rfl

end Work.FIArea2
