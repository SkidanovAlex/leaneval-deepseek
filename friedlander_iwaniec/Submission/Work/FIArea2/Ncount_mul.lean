import Mathlib
import Submission.Work.FIArea2.congCount

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

open Finset

/-- Counting the solutions of `a * x ^ 2 = b * y ^ 2` over a commutative ring is invariant
under a ring isomorphism: the map `(x, y) ↦ (e x, e y)` is a bijection of solution sets.
This generalises `card_solutions_ringEquiv` from a single coefficient to two. -/
lemma card_solutions_ringEquiv_mul {R S : Type*} [CommRing R] [CommRing S]
    [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
    (e : R ≃+* S) (a b : R) :
    ((Finset.univ : Finset (R × R)).filter (fun p => a * p.1 ^ 2 = b * p.2 ^ 2)).card
      = ((Finset.univ : Finset (S × S)).filter (fun p => e a * p.1 ^ 2 = e b * p.2 ^ 2)).card := by
  rw [← Fintype.card_subtype (fun p : R × R => a * p.1 ^ 2 = b * p.2 ^ 2),
      ← Fintype.card_subtype (fun p : S × S => e a * p.1 ^ 2 = e b * p.2 ^ 2)]
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

/-- The solution set of `(a₁, a₂) * z ^ 2 = (b₁, b₂) * w ^ 2` over the product ring `A × B`
is the product of the solution sets of `a₁ * x ^ 2 = b₁ * y ^ 2` over `A` and
`a₂ * x ^ 2 = b₂ * y ^ 2` over `B`: a pair `((x₁, x₂), (y₁, y₂))` solves the equation in
`A × B` exactly when both components do.  This generalises `card_solutions_prod_equiv` to
two coefficients. -/
lemma card_solutions_prod_equiv_mul {A B : Type*} [CommRing A] [CommRing B]
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (a1 b1 : A) (a2 b2 : B) :
    ((Finset.univ : Finset ((A × B) × (A × B))).filter
        (fun p => (a1, a2) * p.1 ^ 2 = (b1, b2) * p.2 ^ 2)).card
      = ((Finset.univ : Finset (A × A)).filter (fun p => a1 * p.1 ^ 2 = b1 * p.2 ^ 2)).card
        * ((Finset.univ : Finset (B × B)).filter (fun p => a2 * p.1 ^ 2 = b2 * p.2 ^ 2)).card := by
  rw [← Fintype.card_subtype (fun p : (A × B) × (A × B) => (a1, a2) * p.1 ^ 2 = (b1, b2) * p.2 ^ 2)]
  rw [← Fintype.card_subtype (fun p : A × A => a1 * p.1 ^ 2 = b1 * p.2 ^ 2)]
  rw [← Fintype.card_subtype (fun p : B × B => a2 * p.1 ^ 2 = b2 * p.2 ^ 2)]
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

/-- **The local count `N(a,b;q)` is multiplicative in the modulus.**  For coprime `m`, `n`,
the Chinese remainder isomorphism `ZMod (m * n) ≃+* ZMod m × ZMod n` identifies the pairs
`(γ₁, γ₂)` with `a γ₁² ≡ b γ₂² (mod mn)` with the pairs of solutions modulo `m` and modulo
`n`; the equation is componentwise on the product ring, so the counts multiply. -/
theorem Ncount_mul {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)] (h : m.Coprime n) (a b : ℕ) :
    Work.FIArea2.Ncount (m * n) a b = Work.FIArea2.Ncount m a b * Work.FIArea2.Ncount n a b := by
  unfold Ncount
  have hφa : (ZMod.chineseRemainder h) (a : ZMod (m * n)) = ((a : ZMod m), (a : ZMod n)) := by
    rw [map_natCast]; rfl
  have hφb : (ZMod.chineseRemainder h) (b : ZMod (m * n)) = ((b : ZMod m), (b : ZMod n)) := by
    rw [map_natCast]; rfl
  rw [card_solutions_ringEquiv_mul (ZMod.chineseRemainder h) (a : ZMod (m * n)) (b : ZMod (m * n)),
    hφa, hφb]
  exact card_solutions_prod_equiv_mul (a : ZMod m) (b : ZMod m) (a : ZMod n) (b : ZMod n)

end Work.FIArea2
