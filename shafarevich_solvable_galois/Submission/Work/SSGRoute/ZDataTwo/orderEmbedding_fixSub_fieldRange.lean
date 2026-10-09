import Mathlib
import Submission.Work.SSGRoute.InvAux
import Submission.Work.SSGRoute.InvAux.exists_orderEmbedding
import Submission.Work.SSGRoute.InvAux.exists_nat_ge_of_aeval_eq_zero
import Submission.Work.SSGRoute.InvAux.irreducible_natDegree_le_two
import Submission.Work.SSGRoute.InvAux.fixedFields_ringEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The range of the order embedding of the fixed field of an involution

Let `Ω` be an algebraically closed field of characteristic zero which is algebraic over `ℚ`, and let
`c : Ω ≃+* Ω` be a non-trivial involutive ring automorphism with fixed field `F = Ω^c`
(`Work.SSGRoute.InvAux.fixSub c`).  `F` carries the order whose positive cone is
`Work.SSGRoute.InvAux.cone` (`InvAux.lean`).

Recall (`InvAux/fixedFields_ringEquiv.lean`) that `Work.SSGRoute.InvAux.realAlgSubfield` is the
subfield `ℝ^{alg} = {x : ℝ | IsAlgebraic ℚ x}` of real algebraic numbers, and that for the canonical
order embedding `fixSubEmbed c : F →+*o ℝ` one has `fixSubEmbed c.fieldRange = realAlgSubfield`.

Here we prove the same for an **arbitrary** order embedding
`ρ : F →+*o ℝ` whose positivity cone is `cone`
(`Work.SSGRoute.ZDataTwo.orderEmbedding_fixSub_fieldRange`).

The proof splits into the two inclusions of subfields of `ℝ`:

* `fieldRange_le_realAlgSubfield` (the easy direction): every element of `F` is algebraic over `ℚ`
  and any ring homomorphism `ℚ → ℝ` is the inclusion of `ℚ`, so `ρ` sends algebraic elements to
  algebraic elements.
* `realAlgSubfield_le_fieldRange` (the hard direction): `ρ` induces an ordered ring isomorphism
  `F ≃+* ρ.fieldRange`.  Transporting along it, the range again has the two "real closedness"
  properties (every irreducible polynomial has degree at most two — `irreducible_natDegree_le_two`
  transported; every non-negative element is a square — `isSquareOfCone` transported), and it
  contains `ℚ`.  Hence it contains every real algebraic number by `isAlgebraicMemOfSubfield`.
-/

namespace Work.SSGRoute.ZDataTwo

/-- Every element of the fixed field of an involution of a field algebraic over `ℚ` is algebraic
over `ℚ`. -/
lemma isAlgebraic_fixSub_coe {Ω : Type} [Field Ω] [CharZero Ω] [Algebra.IsAlgebraic ℚ Ω]
    {c : Ω ≃+* Ω} (x : ↥(Work.SSGRoute.InvAux.fixSub c)) : IsAlgebraic ℚ x := by
  haveI : Algebra.IsAlgebraic ℚ ↥(Work.SSGRoute.InvAux.fixSub c) :=
    Algebra.IsAlgebraic.of_injective
      (IsScalarTower.toAlgHom ℚ ↥(Work.SSGRoute.InvAux.fixSub c) Ω) Subtype.coe_injective
  exact Algebra.IsAlgebraic.isAlgebraic x

/-- The range of an order embedding of the fixed field of a non-trivial involution of an
algebraically closed field of characteristic zero which is algebraic over `ℚ` consists of real
algebraic numbers. -/
lemma fieldRange_le_realAlgSubfield {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    [Algebra.IsAlgebraic ℚ Ω] {c : Ω ≃+* Ω} [Fact (c * c = 1)] [Fact (c ≠ 1)]
    (ρ : ↥(Work.SSGRoute.InvAux.fixSub c) →+*o ℝ) :
    (ρ : ↥(Work.SSGRoute.InvAux.fixSub c) →+* ℝ).fieldRange ≤
      Work.SSGRoute.InvAux.realAlgSubfield := by
  intro y hy
  rw [RingHom.mem_fieldRange] at hy
  obtain ⟨x, rfl⟩ := hy
  have hx : IsAlgebraic ℚ x := isAlgebraic_fixSub_coe x
  have hchain : RingHom.comp (algebraMap ℚ ℝ) (RingHom.id ℚ)
      = RingHom.comp (ρ : ↥(Work.SSGRoute.InvAux.fixSub c) →+* ℝ)
          (algebraMap ℚ ↥(Work.SSGRoute.InvAux.fixSub c)) :=
    RingHom.ext_rat _ _
  have hres := IsAlgebraic.ringHom_of_comp_eq (f := RingHom.id ℚ)
    (g := (ρ : ↥(Work.SSGRoute.InvAux.fixSub c) →+* ℝ)) hx
    (RingHom.injective (RingHom.id ℚ)) hchain
  simpa using hres

/-- The range of an order embedding of the fixed field of a non-trivial involution of an
algebraically closed field of characteristic zero which is algebraic over `ℚ` contains every real
algebraic number. -/
lemma realAlgSubfield_le_fieldRange {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    [Algebra.IsAlgebraic ℚ Ω] {c : Ω ≃+* Ω} [Fact (c * c = 1)] [Fact (c ≠ 1)]
    (ρ : ↥(Work.SSGRoute.InvAux.fixSub c) →+*o ℝ)
    (hρ : ∀ x, 0 ≤ ρ x ↔ Work.SSGRoute.InvAux.cone x) :
    Work.SSGRoute.InvAux.realAlgSubfield ≤
      (ρ : ↥(Work.SSGRoute.InvAux.fixSub c) →+* ℝ).fieldRange := by
  intro y hy
  rw [Work.SSGRoute.InvAux.mem_realAlgSubfield] at hy
  -- The range of `ρ`, and the induced ring isomorphism `F ≃+* ρ.fieldRange`.
  let L : Subfield ℝ := (ρ : ↥(Work.SSGRoute.InvAux.fixSub c) →+* ℝ).fieldRange
  let rH : ↥(Work.SSGRoute.InvAux.fixSub c) →+* ↥L :=
    { toFun := fun x => ⟨ρ x, by
        show ρ x ∈ L
        exact RingHom.mem_fieldRange.mpr ⟨x, rfl⟩⟩
      map_one' := Subtype.ext (map_one ρ.toRingHom)
      map_mul' := fun a b => Subtype.ext (map_mul ρ.toRingHom a b)
      map_zero' := Subtype.ext (map_zero ρ.toRingHom)
      map_add' := fun a b => Subtype.ext (map_add ρ.toRingHom a b) }
  let rE : ↥(Work.SSGRoute.InvAux.fixSub c) ≃+* ↥L :=
    RingEquiv.ofBijective rH
      ⟨fun a b hab =>
          RingHom.injective (ρ : ↥(Work.SSGRoute.InvAux.fixSub c) →+* ℝ)
            (by
              have h := congrArg (fun z : ↥L => (z : ℝ)) hab
              simpa [rH] using h),
       fun z => by
          have hz : (z : ℝ) ∈ (ρ : ↥(Work.SSGRoute.InvAux.fixSub c) →+* ℝ).fieldRange := z.2
          obtain ⟨x, hx⟩ := RingHom.mem_fieldRange.mp hz
          exact ⟨x, Subtype.ext hx⟩⟩
  -- The range contains `ℚ`.
  have hrat : ∀ q : ℚ, (q : ℝ) ∈ L := by
    intro q
    have hq : (q : ℝ) ∈ (ρ : ↥(Work.SSGRoute.InvAux.fixSub c) →+* ℝ).fieldRange :=
      RingHom.mem_fieldRange.mpr ⟨(q : ↥(Work.SSGRoute.InvAux.fixSub c)),
        map_ratCast (ρ : ↥(Work.SSGRoute.InvAux.fixSub c) →+* ℝ) q⟩
    exact hq
  -- The isomorphism is order preserving.
  have hmono : ∀ a b : ↥(Work.SSGRoute.InvAux.fixSub c), a ≤ b → rE a ≤ rE b := by
    intro a b hab
    show ρ a ≤ ρ b
    exact ρ.monotone' hab
  -- Irreducible polynomials over the range have degree at most two.
  have hirr : ∀ f : Polynomial ↥L, Irreducible f → f.natDegree ≤ 2 := fun f hf =>
    Work.SSGRoute.InvAux.irreducibleNatDegreeLeTwoOfRingEquiv rE
      (fun g hg =>
        Work.SSGRoute.InvAux.irreducible_natDegree_le_two (Ω := Ω) (Fact.out : c * c = 1) hg)
      f hf
  -- Every non-negative element of the range is a square.
  have hsq : ∀ x : ↥L, 0 ≤ x → IsSquare x := fun x hx =>
    Work.SSGRoute.InvAux.isSquareOfNonnegOfRingEquiv rE hmono
      (fun z hz => by
        have hz' : Work.SSGRoute.InvAux.cone (z - 0) := hz
        rw [sub_zero] at hz'
        exact Work.SSGRoute.InvAux.isSquareOfCone (Ω := Ω) (Fact.out : c * c = 1) hz') hx
  exact Work.SSGRoute.InvAux.isAlgebraicMemOfSubfield L hrat hirr hsq hy

theorem orderEmbedding_fixSub_fieldRange {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    [Algebra.IsAlgebraic ℚ Ω] {c : Ω ≃+* Ω} [Fact (c * c = 1)] [Fact (c ≠ 1)]
    (ρ : ↥(Work.SSGRoute.InvAux.fixSub c) →+*o ℝ)
    (hρ : ∀ x, 0 ≤ ρ x ↔ Work.SSGRoute.InvAux.cone x) :
    (ρ : ↥(Work.SSGRoute.InvAux.fixSub c) →+* ℝ).fieldRange =
      Work.SSGRoute.InvAux.realAlgSubfield :=
  le_antisymm (fieldRange_le_realAlgSubfield ρ) (realAlgSubfield_le_fieldRange ρ hρ)

end Work.SSGRoute.ZDataTwo
