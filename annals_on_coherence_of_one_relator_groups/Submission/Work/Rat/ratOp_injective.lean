import Mathlib
import Submission.Work.ORHughesFree.Rat.RTerm

/-!
# `⋄` is injective on the universal rational `U`-semiring `Rat(U)`

`Work.ORHughesFree.RatU U = Rat(U)` is the initial rational `U`-semiring
(`Submission.Work.ORHughesFree.Rat.RTerm`), with rational operation `RatU.ratOp`.

The main result of this file is that `RatU.ratOp` is **injective**.  Since `RatU` is the quotient of
the term algebra by the relation "equal in every rational `U`-semiring", it suffices to produce, for
every rational `U`-semiring `A`, a rational `U`-semiring `M` with an injective `⋄` whose universal
map `Rat(U) → M` recovers the universal map `Rat(U) → A` on first coordinates.

Such an `M` is built here from `A` itself: let `S` be the carrier of `A` and let `ρ u = u · 1` be
the image of `u : U`.  On the product `S × Sᵐᵒᵖ` put

* the semiring structure of the product (`Sᵐᵒᵖ` being `S` with the opposite multiplication),
* the `U`-action by the *shifted* element `(ρ u, ρ u⁻¹)` (a unit of the product, with inverse
  `(ρ u⁻¹, ρ u)`, using `ρ (u * v) = ρ u * ρ v` and `ρ (u⁻¹ * u) = 1`),
* the rational operation `⋄ (x₁, x₂) = (x₁ ⋄, x₁)`.

The rational axiom `(u r v)⋄ = v⁻¹ r⋄ u⁻¹` holds because the two coordinates of the shifted action
move in opposite directions: the first coordinate is scaled by `ρ u` on the left and `ρ v` on the
right, while the second is scaled by `ρ u⁻¹` and `ρ v⁻¹`, and `ρ (u⁻¹) = (ρ u)⁻¹`.

Because the second coordinate of `⋄ (x₁, x₂)` is `op x₁`, the operation `⋄` of this model is
injective.  Moreover the first coordinate of the universal map `Rat(U) → S × Sᵐᵒᵖ` is a morphism of
rational `U`-semirings `Rat(U) → A`, hence (uniqueness of the universal morphism) it *is* the
universal morphism `Rat(U) → A`.  Therefore `x ⋄ = y ⋄` in `Rat(U)` forces `lift x = lift y` in
every rational `U`-semiring, i.e. `x = y` in `Rat(U)`.
-/

namespace Work.Rat

open Work.ORHughesFree

variable {U : Type} [Group U]

/-! ### The "opposite-shift" model -/

/-- The "shift" `(ρ u, ρ u⁻¹) ∈ S × Sᵐᵒᵖ`, where `ρ u = u · 1` is the image of `u` in a rational
`U`-semiring on `S`. -/
noncomputable def oppShift (S : Type) [Semiring S] (rB : RationalUSemiring U S) (u : U) :
    S × Sᵐᵒᵖ :=
  (rB.smul u 1, MulOpposite.op (rB.smul u⁻¹ 1))

/-- The rational operation on `S × Sᵐᵒᵖ`: `⋄ (x₁, x₂) = (x₁ ⋄, x₁)`. -/
noncomputable def oppRatOp (S : Type) [Semiring S] (rB : RationalUSemiring U S)
    (r : S × Sᵐᵒᵖ) : S × Sᵐᵒᵖ :=
  (rB.ratOp r.1, MulOpposite.op r.1)

/-- The left `U`-action on `S × Sᵐᵒᵖ`: multiplication by the shift `(ρ u, ρ u⁻¹)`. -/
noncomputable def oppSmul (S : Type) [Semiring S] (rB : RationalUSemiring U S) (u : U)
    (r : S × Sᵐᵒᵖ) : S × Sᵐᵒᵖ :=
  oppShift S rB u * r

/-- The right `U`-action on `S × Sᵐᵒᵖ`: multiplication by the shift `(ρ v, ρ v⁻¹)`. -/
noncomputable def oppSmulRight (S : Type) [Semiring S] (rB : RationalUSemiring U S)
    (r : S × Sᵐᵒᵖ) (u : U) : S × Sᵐᵒᵖ :=
  r * oppShift S rB u

/-- The shifts are multiplicative. -/
theorem oppShift_mul (S : Type) [Semiring S] (rB : RationalUSemiring U S) (u v : U) :
    oppShift S rB (u * v) = oppShift S rB u * oppShift S rB v := by
  have h1 : rB.smul (u * v) 1 = rB.smul u 1 * rB.smul v 1 := rB.smul_mul u v
  have h2 : rB.smul (u * v)⁻¹ 1 = rB.smul v⁻¹ 1 * rB.smul u⁻¹ 1 := by
    rw [mul_inv_rev, rB.smul_mul]
  show (rB.smul (u * v) 1, MulOpposite.op (rB.smul (u * v)⁻¹ 1))
      = (rB.smul u 1, MulOpposite.op (rB.smul u⁻¹ 1))
        * (rB.smul v 1, MulOpposite.op (rB.smul v⁻¹ 1))
  rw [Prod.mk_mul_mk, h1, h2, MulOpposite.op_mul]

/-- The shift of the identity is the identity. -/
theorem oppShift_one (S : Type) [Semiring S] (rB : RationalUSemiring U S) :
    oppShift S rB 1 = 1 := by
  show (rB.smul 1 1, MulOpposite.op (rB.smul 1⁻¹ 1)) = (1, 1)
  rw [inv_one, rB.smul_one_one, MulOpposite.op_one]

/-- **The rational axiom on `S × Sᵐᵒᵖ`**: because the two coordinates of the shifted action move in
opposite directions, `⋄ (u r v) = v⁻¹ r⋄ u⁻¹` holds for the operation `⋄ (x₁, x₂) = (x₁ ⋄, x₁)`. -/
theorem oppRatOp_smul (S : Type) [Semiring S] (rB : RationalUSemiring U S) (u v : U)
    (r : S × Sᵐᵒᵖ) :
    oppRatOp S rB (oppSmul S rB u (oppSmulRight S rB r v))
      = oppSmulRight S rB (oppSmul S rB v⁻¹ (oppRatOp S rB r)) u⁻¹ := by
  obtain ⟨x₁, x₂⟩ := r
  obtain ⟨ξ⟩ := x₂
  refine Prod.ext ?_ ?_
  · simp only [oppRatOp, oppSmul, oppSmulRight, oppShift, Prod.fst_mul]
    have hsm : rB.smul u (rB.smulRight x₁ v) = rB.smul u 1 * (x₁ * rB.smul v 1) := by
      rw [rB.smulRight_eq_mul x₁ v, rB.smulRight_one v, rB.smul_eq_mul u (x₁ * rB.smul v 1)]
    have hsr : rB.smulRight (rB.smul v⁻¹ (rB.ratOp x₁)) u⁻¹
        = (rB.smul v⁻¹ 1 * rB.ratOp x₁) * rB.smul u⁻¹ 1 := by
      rw [rB.smulRight_eq_mul (rB.smul v⁻¹ (rB.ratOp x₁)) u⁻¹,
        rB.smulRight_one u⁻¹, rB.smul_eq_mul v⁻¹ (rB.ratOp x₁)]
    rw [← hsm, ← hsr]
    exact rB.rat_smul u v x₁
  · simp only [oppRatOp, oppSmul, oppSmulRight, oppShift, Prod.fst_mul, Prod.snd_mul]
    rw [inv_inv, inv_inv, ← MulOpposite.op_mul, ← MulOpposite.op_mul]

/-- **The "opposite-shift" rational `U`-semiring structure** on `S × Sᵐᵒᵖ`. -/
noncomputable def oppModel (S : Type) [Semiring S] (rB : RationalUSemiring U S) :
    RationalUSemiring U (S × Sᵐᵒᵖ) where
  ratOp := oppRatOp S rB
  smul := oppSmul S rB
  smulRight := oppSmulRight S rB
  smul_eq_mul := by
    intro u r
    show oppShift S rB u * r = oppShift S rB u * 1 * r
    rw [mul_one]
  smulRight_eq_mul := by
    intro r u
    show r * oppShift S rB u = r * (1 * oppShift S rB u)
    rw [one_mul]
  smul_mul := by
    intro u v
    show oppShift S rB (u * v) * 1 = oppShift S rB u * 1 * (oppShift S rB v * 1)
    rw [mul_one, mul_one, mul_one, oppShift_mul]
  smul_one_one := by
    show oppShift S rB 1 * 1 = 1
    rw [mul_one, oppShift_one]
  smulRight_one_one := by
    show 1 * oppShift S rB 1 = 1
    rw [one_mul, oppShift_one]
  smulRight_one := by
    intro u
    show 1 * oppShift S rB u = oppShift S rB u * 1
    rw [one_mul, mul_one]
  rat_smul := oppRatOp_smul S rB
  -- `RatU` requires `⋄ 0 = 0` (`RationalUSemiring.ratOp_zero`); for the opposite-shift model this
  -- reads `(rB.ratOp 0, op 0) = 0`, which is `rB.ratOp_zero`.
  ratOp_zero := by
    show (rB.ratOp (0 : S), MulOpposite.op (0 : S)) = (0, 0)
    rw [rB.ratOp_zero]
    rfl

/-! ### The first coordinate of the universal map is the universal map -/

/-- The first coordinate of the universal map of the opposite-shift model, as a ring homomorphism
`Rat(U) →+* S`. -/
noncomputable def oppProj (S : Type) [Semiring S] (rB : RationalUSemiring U S) : RatU U →+* S :=
  (RingHom.fst S Sᵐᵒᵖ).comp (RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB))

/-- The first coordinate of the universal map of the opposite-shift model, as a function. -/
theorem oppProj_apply (S : Type) [Semiring S] (rB : RationalUSemiring U S) (z : RatU U) :
    oppProj S rB z = ((RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB)) z).1 := rfl

/-- **The first coordinate of the universal map of the opposite-shift model is the universal map of
`A`.**  The first coordinate is a morphism of rational `U`-semirings `Rat(U) → A`, and the universal
morphism with this property is unique. -/
theorem fst_lift_oppModel (S : Type) [Semiring S] (rB : RationalUSemiring U S) :
    oppProj S rB = RatU.lift S rB := by
  refine RatU.lift_unique S rB _ ⟨?_, ?_, ?_⟩
  · intro z
    show (RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB) (RatU.rational.ratOp z)).1
        = rB.ratOp ((RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB)) z).1
    rw [(RatU.lift_isHom (S × Sᵐᵒᵖ) (oppModel S rB)).map_rat z]
    rfl
  · intro u z
    show (RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB) (RatU.rational.smul u z)).1
        = rB.smul u ((RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB)) z).1
    rw [(RatU.lift_isHom (S × Sᵐᵒᵖ) (oppModel S rB)).map_smul u z]
    show (oppShift S rB u * (RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB)) z).1
        = rB.smul u ((RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB)) z).1
    rw [Prod.fst_mul]
    show rB.smul u 1 * ((RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB)) z).1
        = rB.smul u ((RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB)) z).1
    rw [rB.smul_eq_mul u ((RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB)) z).1]
  · intro z u
    show (RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB) (RatU.rational.smulRight z u)).1
        = rB.smulRight ((RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB)) z).1 u
    rw [(RatU.lift_isHom (S × Sᵐᵒᵖ) (oppModel S rB)).map_smulRight z u]
    show ((RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB)) z * oppShift S rB u).1
        = rB.smulRight ((RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB)) z).1 u
    rw [Prod.fst_mul]
    show ((RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB)) z).1 * rB.smul u 1
        = rB.smulRight ((RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB)) z).1 u
    rw [← rB.smulRight_one u, ← rB.smulRight_eq_mul ((RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB)) z).1 u]

/-! ### Injectivity -/

/-- **The key step**: if `x ⋄ = y ⋄` in `Rat(U)`, then `x` and `y` have the same image under the
universal map into *every* rational `U`-semiring.  Apply the universal map of the opposite-shift
model of `A` to the hypothesis: the second coordinate of `⋄` on that model is `op` of the first
coordinate, so the first coordinates agree; and the first coordinate is the universal map of `A`. -/
theorem lift_eq_of_ratOp_eq (S : Type) [Semiring S] (rB : RationalUSemiring U S) {x y : RatU U}
    (h : RatU.ratOp x = RatU.ratOp y) : RatU.lift S rB x = RatU.lift S rB y := by
  have key : (oppModel S rB).ratOp ((RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB)) x)
      = (oppModel S rB).ratOp ((RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB)) y) := by
    rw [← (RatU.lift_isHom (S × Sᵐᵒᵖ) (oppModel S rB)).map_rat x,
      ← (RatU.lift_isHom (S × Sᵐᵒᵖ) (oppModel S rB)).map_rat y]
    rw [show RatU.rational.ratOp x = RatU.rational.ratOp y from h]
  have key3 : ((RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB)) x).1
      = ((RatU.lift (S × Sᵐᵒᵖ) (oppModel S rB)) y).1 := by
    have h2 := congrArg Prod.snd key
    simp only [oppModel, oppRatOp] at h2
    exact MulOpposite.op_injective h2
  have h3 : (RatU.lift S rB) x = (RatU.lift S rB) y := by
    rw [← fst_lift_oppModel S rB, oppProj_apply S rB x, oppProj_apply S rB y]
    exact key3
  exact h3

/-- **`⋄` is injective on the universal rational `U`-semiring `Rat(U)`**: if `x ⋄ = y ⋄` then
`x = y`.  Indeed, `x = y` in `Rat(U)` means that `x` and `y` have the same image in every rational
`U`-semiring, which is `lift_eq_of_ratOp_eq`. -/
theorem ratOp_injective {U : Type} [Group U] (x y : Work.ORHughesFree.RatU U) :
    Work.ORHughesFree.RatU.ratOp x = Work.ORHughesFree.RatU.ratOp y → x = y := by
  refine Quotient.inductionOn₂ x y ?_
  intro s t hst
  refine Quotient.sound (fun S _ rB => ?_)
  rw [← RatU.lift_apply S rB s, ← RatU.lift_apply S rB t]
  exact lift_eq_of_ratOp_eq S rB hst

end Work.Rat
