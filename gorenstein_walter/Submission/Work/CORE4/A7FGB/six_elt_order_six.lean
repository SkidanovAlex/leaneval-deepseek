import Mathlib
import Submission.Work.CORE4.A7FGB.injective_mul_pow
import Submission.Work.CORE4.A7FGB.orderOf_mul_pow_eq_six

namespace Work.CORE4.A7FGB

/-!
# Six elements of order `6`

Let `V ≤ R ≤ A₇` where `V` has order `4` and exponent `2` (every element of `V` is an
involution, so `V` is a Klein four group), and let `x ∈ R` be an element of order `3` that
commutes with every element of `V`.  Then `R` contains at least six elements of order `6`.

Concretely, for each of the three non-identity elements `v ∈ V` and each of the two
exponents `a ∈ {1, 2}` the product `v · xᵃ` has order `6`, and the six products are pairwise
distinct.  Both facts are proved in the imported modules:

* `orderOf_mul_pow_eq_six` — every `v · xᵃ` with `v ∈ V ∖ {1}` and `a ∈ {1, 2}` has
  order `6` (orders `2` and `3` are coprime);
* `injective_mul_pow` — the six products are pairwise distinct, since if
  `v₁ x^{a₁} = v₂ x^{a₂}` then `v₂⁻¹ v₁ = x^{a₁-a₂}` lies in `V ⊓ ⟨x⟩ = ⊥`.

The domain has `3 · 2 = 6` elements (`V` has `4` elements, one of which is the identity),
so an injection of it into the elements of `R` of order `6` gives the bound.
-/

/-- Commuting elements of orders `2` and `3` have a product of order `6`. -/
theorem orderOf_mul_eq_six_of_commute {G : Type*} [Group G] {a b : G}
    (hab : a * b = b * a) (ha : orderOf a = 2) (hb : orderOf b = 3) :
    orderOf (a * b) = 6 := by
  have hc : Commute a b := hab
  rw [hc.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [ha, hb]; norm_num), ha, hb]

theorem six_elt_order_six (R V : Subgroup (alternatingGroup (Fin 7))) (x : alternatingGroup (Fin 7))
    (hVR : V ≤ R) (hxR : x ∈ R) (hVcard : Nat.card V = 4) (h2 : ∀ v ∈ V, v * v = 1)
    (hx3 : orderOf x = 3) (hcomm : ∀ v ∈ V, v * x = x * v) :
    6 ≤ Nat.card {g : ↥R // orderOf g = 6} := by
  classical
  -- The map `(v, k) ↦ v · x ^ (k+1)` on the six-element index set.
  let gfun : ({v : ↥V // v ≠ 1} × Fin 2) → alternatingGroup (Fin 7) :=
    fun p => (p.1.val : alternatingGroup (Fin 7)) * x ^ (p.2.val + 1)
  have hgfunR : ∀ p, gfun p ∈ R := fun p =>
    R.mul_mem (hVR p.1.val.2) (R.pow_mem hxR _)
  have hgfun6 : ∀ p, orderOf (gfun p) = 6 := fun p =>
    orderOf_mul_pow_eq_six V x h2 hx3 hcomm p.1.val.2
      (fun h => p.1.2 (Subtype.ext h)) p.2
  have hgfunInj : Function.Injective gfun := injective_mul_pow V x h2 hx3 hcomm
  -- Package `gfun` as a map into the elements of `R` of order `6` (their order is
  -- unchanged under the inclusion `R ↪ A₇`).
  let f : ({v : ↥V // v ≠ 1} × Fin 2) → {g : ↥R // orderOf g = 6} := fun p =>
    ⟨⟨gfun p, hgfunR p⟩, by rw [← Subgroup.orderOf_coe]; exact hgfun6 p⟩
  have hf_inj : Function.Injective f := by
    intro p q hpq
    apply hgfunInj
    have h1 : (f p).1 = (f q).1 := congrArg Subtype.val hpq
    have h2' : ((f p).1 : alternatingGroup (Fin 7)) = ((f q).1 : alternatingGroup (Fin 7)) :=
      congrArg (fun z : ↥R => (z : alternatingGroup (Fin 7))) h1
    simpa [f, gfun] using h2'
  -- The index set has `(4 - 1) * 2 = 6` elements.
  have hcard : Nat.card ({v : ↥V // v ≠ 1} × Fin 2) = 6 := by
    rw [Nat.card_prod, Nat.card_fin]
    have h := Finite.card_option (α := {v : ↥V // v ≠ 1})
    rw [Nat.card_congr (Equiv.optionSubtypeNe (1 : ↥V))] at h
    have hV4 : Nat.card ↥V = 4 := hVcard
    omega
  have := Nat.card_le_card_of_injective f hf_inj
  omega

end Work.CORE4.A7FGB
