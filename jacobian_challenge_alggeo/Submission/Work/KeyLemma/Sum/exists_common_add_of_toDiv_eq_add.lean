import Mathlib
import Submission.Work.KeyLemma.Sum
import Submission.Work.KeyLemma.Sum.placeOfPoint_injective_aux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.KeyLemma.Sum

open Work.CurveBasics
open Work.KeyLemma.Curve

universe u

variable {k : Type u} [Field k]

/-- At the place of a `k`-point, `toDiv` of a multiset is just the multiplicity at that
point: the fibre of `placeOfPoint` over `placeOfPoint p` is a singleton. -/
theorem toDiv_placeOfPoint (C : Curve k)
    (hinj : Function.Injective (placeOfPoint C)) (s : SumDiv C) (p : Point C) :
    SumDiv.toDiv C s (placeOfPoint C p) = (s p : ℤ) := by
  rw [SumDiv.toDiv_apply, SumDiv.coeffAt, Finsupp.sum, Finset.sum_eq_single p]
  · simp
  · intro b _ hbp
    have hne : placeOfPoint C b ≠ placeOfPoint C p := fun h => hbp (hinj h)
    simp [hne]
  · intro hp
    rw [Finsupp.notMem_support_iff.mp hp]
    simp

/-- If a place is not the image of any `k`-point, then it is not in the support of
`toDiv`. -/
theorem toDiv_eq_zero_of_not_mem_range (C : Curve k) (s : SumDiv C) {Q : C.Place}
    (hQ : ¬ ∃ p : Point C, placeOfPoint C p = Q) : SumDiv.toDiv C s Q = 0 := by
  rw [SumDiv.toDiv_apply, SumDiv.coeffAt, Finsupp.sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases h : placeOfPoint C p = Q
  · exact absurd ⟨p, h⟩ hQ
  · simp [h]

/-- An effective divisor `D` with `D ≤ toDiv C s` is supported in the image of
`placeOfPoint`. -/
theorem exists_point_of_pos {C : Curve k} {A E : C.Div} {s : SumDiv C}
    (hA : A.IsEffective) (hs : SumDiv.toDiv C s = A + E) {Q : C.Place} (hQ : 0 < E Q) :
    ∃ p : Point C, placeOfPoint C p = Q := by
  by_contra h
  have h0 : SumDiv.toDiv C s Q = 0 := toDiv_eq_zero_of_not_mem_range C s h
  have hle : E Q ≤ SumDiv.toDiv C s Q := by
    rw [hs, Finsupp.add_apply]
    linarith [hA Q]
  rw [h0] at hle
  linarith

theorem exists_common_add_of_toDiv_eq_add {k : Type u} [Field k]
    (C : Work.CurveBasics.Curve k) {s s' : Work.KeyLemma.Curve.SumDiv C}
    {A A' E : C.Div} (hA : A.IsEffective) (hA' : A'.IsEffective) (hE : E.IsEffective)
    (hs : Work.KeyLemma.Curve.SumDiv.toDiv C s = A + E)
    (hs' : Work.KeyLemma.Curve.SumDiv.toDiv C s' = A' + E) :
    ∃ sA sA' sE : Work.KeyLemma.Curve.SumDiv C, s = sA + sE ∧ s' = sA' + sE ∧
      Work.KeyLemma.Curve.SumDiv.toDiv C sA = A ∧
      Work.KeyLemma.Curve.SumDiv.toDiv C sA' = A' ∧
      Work.KeyLemma.Curve.SumDiv.toDiv C sE = E := by
  have hinj := Work.KeyLemma.Sum.placeOfPoint_injective_aux C
  -- the candidate common piece
  have hfin : (Function.support
      (fun p : Point C => min (s p) ((E (placeOfPoint C p)).toNat))).Finite := by
    refine Set.Finite.subset (Finset.finite_toSet s.support) ?_
    intro p hp
    rw [Function.mem_support] at hp
    exact Finsupp.mem_support_iff.mpr (fun h => hp (by rw [h]; simp))
  let sE : SumDiv C :=
    Finsupp.ofSupportFinite (fun p : Point C => min (s p) ((E (placeOfPoint C p)).toNat)) hfin
  have hsE_apply : ∀ p : Point C, sE p = min (s p) ((E (placeOfPoint C p)).toNat) :=
    fun p => by simp only [sE]; exact congrFun (Finsupp.ofSupportFinite_coe) p
  have hs_E : ∀ p : Point C, (s p : ℤ) = A (placeOfPoint C p) + E (placeOfPoint C p) := by
    intro p
    rw [← toDiv_placeOfPoint C hinj s p, hs, Finsupp.add_apply]
  have hs'_E : ∀ p : Point C, (s' p : ℤ) = A' (placeOfPoint C p) + E (placeOfPoint C p) := by
    intro p
    rw [← toDiv_placeOfPoint C hinj s' p, hs', Finsupp.add_apply]
  have hmin : ∀ p : Point C, sE p = (E (placeOfPoint C p)).toNat := by
    intro p
    rw [hsE_apply, min_eq_right]
    rw [Int.toNat_le]
    linarith [hA (placeOfPoint C p), hs_E p]
  have hsE_le_s : sE ≤ s := by
    intro p
    rw [hsE_apply]
    exact min_le_left _ _
  have hsE_le_s' : sE ≤ s' := by
    intro p
    rw [hmin]
    rw [Int.toNat_le]
    linarith [hA' (placeOfPoint C p), hs'_E p]
  have htoDiv_sE : SumDiv.toDiv C sE = E := by
    ext Q
    by_cases hQ : ∃ p : Point C, placeOfPoint C p = Q
    · obtain ⟨p, hp⟩ := hQ
      rw [← hp, toDiv_placeOfPoint C hinj sE p, hmin p, Int.toNat_of_nonneg (hE _)]
    · have h0 : SumDiv.toDiv C sE Q = 0 := toDiv_eq_zero_of_not_mem_range C sE hQ
      have hE0 : E Q = 0 := by
        by_contra hne
        obtain ⟨p, hp⟩ := exists_point_of_pos hA hs (lt_of_le_of_ne (hE Q) (Ne.symm hne))
        exact hQ ⟨p, hp⟩
      rw [h0, hE0]
  refine ⟨s - sE, s' - sE, sE, ?_, ?_, ?_, ?_, htoDiv_sE⟩
  · ext p
    simp only [Finsupp.add_apply]
    exact (Nat.sub_add_cancel (Finsupp.le_def.mp hsE_le_s p)).symm
  · ext p
    simp only [Finsupp.add_apply]
    exact (Nat.sub_add_cancel (Finsupp.le_def.mp hsE_le_s' p)).symm
  · have : SumDiv.toDiv C (s - sE) + SumDiv.toDiv C sE = A + E := by
      rw [← SumDiv.toDiv_add, tsub_add_cancel_of_le hsE_le_s, hs]
    rw [htoDiv_sE] at this
    exact add_right_cancel this
  · have : SumDiv.toDiv C (s' - sE) + SumDiv.toDiv C sE = A' + E := by
      rw [← SumDiv.toDiv_add, tsub_add_cancel_of_le hsE_le_s', hs']
    rw [htoDiv_sE] at this
    exact add_right_cancel this

end Work.KeyLemma.Sum
