import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2.R6

/-- Counting the solutions of `z ^ 2 = a` over a commutative ring is invariant under a
ring isomorphism: the map `z ↦ e z` is a bijection of solution sets (the equation for the
image is `w ^ 2 = e a`). -/
lemma card_sq_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
    (e : R ≃+* S) (a : R) :
    ((Finset.univ : Finset R).filter (fun z => z ^ 2 = a)).card
      = ((Finset.univ : Finset S).filter (fun w => w ^ 2 = e a)).card := by
  rw [← Fintype.card_subtype (fun z : R => z ^ 2 = a),
      ← Fintype.card_subtype (fun w : S => w ^ 2 = e a)]
  refine Fintype.card_congr (Equiv.subtypeEquiv e.toEquiv ?_)
  intro z
  constructor
  · intro hz
    have h := congrArg e hz
    simp only [map_pow] at h
    simpa using h
  · intro hw
    apply e.injective
    simp only [map_pow]
    simpa using hw

/-- The solution set of `w ^ 2 = (a₁, a₂)` over the product ring `A × B` is the product of
the solution sets of `x ^ 2 = a₁` over `A` and `y ^ 2 = a₂` over `B`: a pair `(x, y)`
solves the equation in `A × B` exactly when both components do. -/
lemma card_sq_prod_equiv {A B : Type*} [CommRing A] [CommRing B]
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (a1 : A) (a2 : B) :
    ((Finset.univ : Finset (A × B)).filter (fun w => w ^ 2 = (a1, a2))).card
      = ((Finset.univ : Finset A).filter (fun x => x ^ 2 = a1)).card
        * ((Finset.univ : Finset B).filter (fun y => y ^ 2 = a2)).card := by
  rw [← Fintype.card_subtype (fun w : A × B => w ^ 2 = (a1, a2)),
      ← Fintype.card_subtype (fun x : A => x ^ 2 = a1),
      ← Fintype.card_subtype (fun y : B => y ^ 2 = a2),
      ← Fintype.card_prod]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun w => (⟨w.1.1, ?_⟩, ⟨w.1.2, ?_⟩)
      invFun := fun q => ⟨(q.1.1, q.2.1), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h := congrArg Prod.fst w.2; simpa using h
  · have h := congrArg Prod.snd w.2; simpa using h
  · rw [Prod.pow_mk]; exact Prod.ext q.1.2 q.2.2
  · intro x; ext <;> rfl
  · intro x; ext <;> rfl

/-- **Multiplicativity of the number of square roots modulo a product of coprime moduli.** For
coprime `m, n ≥ 1` and any `a : ℤ`, the number of `z : ZMod (m * n)` with `z ^ 2 = a` is the
product of the corresponding numbers modulo `m` and modulo `n`. Proof: `ZMod.chineseRemainder h`
is a ring isomorphism, `z ^ 2 = a` holds in `ZMod (m * n)` iff both components satisfy the
corresponding equations, and cardinalities multiply. The pattern is already used in
`Submission/Work/FIArea2/card_solutions_crt.lean` (`card_solutions_ringEquiv`,
`card_solutions_prod_equiv`, `card_solutions_crt`) — only the equation here is `z ^ 2 = a`
instead of `a * x ^ 2 = y ^ 2`, so `card_solutions_ringEquiv` transfers verbatim and
`card_solutions_prod_equiv` is replaced by the obvious product splitting for a one-variable
equation (`Fintype.card_congr` + `Fintype.card_prod`). -/
theorem count_sqroot_mul_coprime (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n) (a : ℤ) :
    ((Finset.univ : Finset (ZMod (m * n))).filter (fun z => z ^ 2 = (a : ZMod (m * n)))).card
      = ((Finset.univ : Finset (ZMod m)).filter (fun z => z ^ 2 = (a : ZMod m))).card
        * ((Finset.univ : Finset (ZMod n)).filter (fun z => z ^ 2 = (a : ZMod n))).card := by
  have hφa : (ZMod.chineseRemainder h) (a : ZMod (m * n)) = ((a : ZMod m), (a : ZMod n)) := by
    rw [map_intCast]; rfl
  rw [card_sq_ringEquiv (ZMod.chineseRemainder h) (a : ZMod (m * n)), hφa]
  exact card_sq_prod_equiv (a : ZMod m) (a : ZMod n)

end Work.FIArea2.R6
