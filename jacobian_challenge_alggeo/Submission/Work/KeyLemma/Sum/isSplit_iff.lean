import Mathlib
import Submission.Work.KeyLemma.Sum

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.KeyLemma.Sum

open scoped Classical BigOperators
open Work.KeyLemma

universe u

variable {k : Type u} [Field k]

/-- `toDiv` of a multiset supported at a single point `p` with multiplicity `m` is the
single place-divisor at `placeOfPoint C p`. -/
theorem toDiv_single (C : Work.CurveBasics.Curve k) (p : Curve.Point C) (m : ℕ) :
    Curve.SumDiv.toDiv C (Finsupp.single p m) =
      Finsupp.single (Curve.placeOfPoint C p) (m : ℤ) := by
  classical
  ext R
  rw [Curve.SumDiv.toDiv_apply, Curve.SumDiv.coeffAt, Finsupp.sum_single_index]
  · rw [Finsupp.single_apply]
  · split <;> rfl

/-- `toDiv` commutes with finite sums (it is additive). -/
theorem toDiv_finset_sum (C : Work.CurveBasics.Curve k) {ι : Type u}
    (t : Finset ι) (g : ι → Curve.SumDiv C) :
    Curve.SumDiv.toDiv C (∑ Q ∈ t, g Q) = ∑ Q ∈ t, Curve.SumDiv.toDiv C (g Q) := by
  classical
  change (Curve.SumDiv.toDivAddHom C) (∑ Q ∈ t, g Q)
    = ∑ Q ∈ t, (Curve.SumDiv.toDivAddHom C) (g Q)
  rw [map_sum]

/-- A divisor is the sum of its values over its support, placed at the corresponding
points. -/
theorem div_eq_sum_single (C : Work.CurveBasics.Curve k) (D : C.Div) :
    D = ∑ i ∈ D.support, Finsupp.single i (D i) := by
  classical
  ext a
  rw [Finsupp.finsetSum_apply]
  by_cases h : a ∈ D.support
  · rw [Finset.sum_eq_single a]
    · simp
    · intro b hb hba
      rw [Finsupp.single_eq_of_ne (Ne.symm hba)]
    · intro ha; exact absurd h ha
  · simp only [Finsupp.mem_support_iff, not_not] at h
    rw [h]
    symm
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hba : b = a
    · subst hba; rw [h]; simp
    · exact Finsupp.single_eq_of_ne (Ne.symm hba)

/-- An effective divisor of a curve is split over `k` if and only if it is the divisor of a
multiset of `k`-points. -/
theorem isSplit_iff {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    {D : C.Div} (hD : D.IsEffective) :
    Work.KeyLemma.Curve.IsSplit C D ↔
      ∃ s : Work.KeyLemma.Curve.SumDiv C, Work.KeyLemma.Curve.SumDiv.toDiv C s = D := by
  classical
  constructor
  · intro h
    choose p hp using fun Q hQ => h Q hQ
    refine ⟨∑ Q ∈ D.support.attach, Finsupp.single (p Q.1 Q.2) ((D Q.1).toNat), ?_⟩
    rw [toDiv_finset_sum]
    have hterm : ∀ Q : {x // x ∈ D.support},
        Curve.SumDiv.toDiv C (Finsupp.single (p Q.1 Q.2) ((D Q.1).toNat))
          = Finsupp.single Q.1 (D Q.1) := by
      intro Q
      rw [toDiv_single, hp Q.1 Q.2, Int.toNat_of_nonneg (hD Q.1)]
    rw [Finset.sum_congr rfl (fun Q _ => hterm Q)]
    exact (Finset.sum_attach D.support (fun x => Finsupp.single x (D x))).trans
      (div_eq_sum_single C D).symm
  · rintro ⟨s, hs⟩
    intro Q hQ
    have hQ' : Q ∈ (Curve.SumDiv.toDiv C s).support := by rw [hs]; exact hQ
    have hne : (Curve.SumDiv.toDiv C s) Q ≠ 0 := Finsupp.mem_support_iff.mp hQ'
    rw [Curve.SumDiv.toDiv, Finsupp.sum, Finsupp.finsetSum_apply] at hne
    by_contra hcon
    push_neg at hcon
    apply hne
    apply Finset.sum_eq_zero
    intro p hp
    exact Finsupp.single_eq_of_ne (Ne.symm (hcon p))

end Work.KeyLemma.Sum
