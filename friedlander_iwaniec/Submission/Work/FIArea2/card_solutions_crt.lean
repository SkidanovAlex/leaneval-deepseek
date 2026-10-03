import Mathlib
import Submission.Work.FIArea2.area2_r3

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

open Finset

/-- Counting the solutions of `a * x ^ 2 = y ^ 2` over a commutative ring is invariant
under a ring isomorphism: the map `(x, y) ↦ (e x, e y)` is a bijection of solution sets. -/
lemma card_solutions_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
    (e : R ≃+* S) (a : R) :
    ((Finset.univ : Finset (R × R)).filter (fun p => a * p.1 ^ 2 = p.2 ^ 2)).card
      = ((Finset.univ : Finset (S × S)).filter (fun p => e a * p.1 ^ 2 = p.2 ^ 2)).card := by
  rw [← Fintype.card_subtype (fun p : R × R => a * p.1 ^ 2 = p.2 ^ 2),
      ← Fintype.card_subtype (fun p : S × S => e a * p.1 ^ 2 = p.2 ^ 2)]
  refine Fintype.card_congr (Equiv.subtypeEquiv (e.prodCongr e) ?_)
  intro p
  constructor
  · intro hp
    have h := congrArg e hp
    simp only [map_mul, map_pow] at h
    simpa using h
  · intro hq
    apply e.injective
    simp only [map_mul, map_pow]
    simpa using hq

/-- The solution set of `(a₁, a₂) * z ^ 2 = w ^ 2` over the product ring `A × B` is the
product of the solution sets of `a₁ * x ^ 2 = y ^ 2` over `A` and `a₂ * x ^ 2 = y ^ 2`
over `B`: a pair `((x₁, x₂), (y₁, y₂))` solves the equation in `A × B` exactly when both
components do. -/
lemma card_solutions_prod_equiv {A B : Type*} [CommRing A] [CommRing B]
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (a1 : A) (a2 : B) :
    ((Finset.univ : Finset ((A × B) × (A × B))).filter
        (fun p => (a1, a2) * p.1 ^ 2 = p.2 ^ 2)).card
      = ((Finset.univ : Finset (A × A)).filter (fun p => a1 * p.1 ^ 2 = p.2 ^ 2)).card
        * ((Finset.univ : Finset (B × B)).filter (fun p => a2 * p.1 ^ 2 = p.2 ^ 2)).card := by
  rw [← Fintype.card_subtype (fun p : (A × B) × (A × B) => (a1, a2) * p.1 ^ 2 = p.2 ^ 2)]
  rw [← Fintype.card_subtype (fun p : A × A => a1 * p.1 ^ 2 = p.2 ^ 2)]
  rw [← Fintype.card_subtype (fun p : B × B => a2 * p.1 ^ 2 = p.2 ^ 2)]
  rw [← Fintype.card_prod]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun p => (⟨(p.1.1.1, p.1.2.1), ?_⟩, ⟨(p.1.1.2, p.1.2.2), ?_⟩)
      invFun := fun q => ⟨((q.1.1.1, q.2.1.1), (q.1.1.2, q.2.1.2)), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h := congrArg Prod.fst p.2; simpa using h
  · have h := congrArg Prod.snd p.2; simpa using h
  · apply Prod.ext
    · simpa using q.1.2
    · simpa using q.2.2
  · intro x; ext <;> rfl
  · intro x; ext <;> rfl

/-- **Multiplicativity of the local solution count under the Chinese remainder theorem.**
For coprime `q₁, q₂`, the number of pairs `(x, y) ∈ (ℤ/(q₁q₂))²` with `a x² ≡ y² (mod q₁q₂)`
equals the product of the corresponding counts modulo `q₁` and modulo `q₂`.  This is the
local factorisation used to reduce a local density to its prime-power factors. -/
theorem card_solutions_crt (a q1 q2 : ℕ) [NeZero q1] [NeZero q2] [NeZero (q1 * q2)]
    (h : Nat.Coprime q1 q2) :
    (((Finset.univ : Finset (ZMod (q1 * q2) × ZMod (q1 * q2))).filter
        (fun p => (a : ZMod (q1 * q2)) * p.1 ^ 2 = p.2 ^ 2)).card : ℝ)
      = (((Finset.univ : Finset (ZMod q1 × ZMod q1)).filter
            (fun p => (a : ZMod q1) * p.1 ^ 2 = p.2 ^ 2)).card : ℝ)
        * (((Finset.univ : Finset (ZMod q2 × ZMod q2)).filter
            (fun p => (a : ZMod q2) * p.1 ^ 2 = p.2 ^ 2)).card : ℝ) := by
  have hφa : (ZMod.chineseRemainder h) (a : ZMod (q1 * q2)) = ((a : ZMod q1), (a : ZMod q2)) := by
    rw [map_natCast]
    rfl
  have hnat : (((Finset.univ : Finset (ZMod (q1 * q2) × ZMod (q1 * q2))).filter
        (fun p => (a : ZMod (q1 * q2)) * p.1 ^ 2 = p.2 ^ 2)).card : ℕ)
      = (((Finset.univ : Finset (ZMod q1 × ZMod q1)).filter
            (fun p => (a : ZMod q1) * p.1 ^ 2 = p.2 ^ 2)).card)
        * (((Finset.univ : Finset (ZMod q2 × ZMod q2)).filter
            (fun p => (a : ZMod q2) * p.1 ^ 2 = p.2 ^ 2)).card) := by
    rw [card_solutions_ringEquiv (ZMod.chineseRemainder h) (a : ZMod (q1 * q2)), hφa]
    exact card_solutions_prod_equiv (a : ZMod q1) (a : ZMod q2)
  rw [hnat, Nat.cast_mul]

end Work.FIArea2
