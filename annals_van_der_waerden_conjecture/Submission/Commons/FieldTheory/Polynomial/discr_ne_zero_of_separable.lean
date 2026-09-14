import Mathlib.FieldTheory.Separable
import Submission.Commons.FieldTheory.Polynomial.discr_mul

open Polynomial

set_option autoImplicit false

namespace Commons.FieldTheory.Polynomial

noncomputable section

/-- A monic separable polynomial over a field has nonzero discriminant.
(Proof route: separable means no repeated roots over an algebraic closure,
so the discriminant, which equals the square of the Vandermonde product of
the roots, is nonzero; or: extend to a splitting field, where the monic
polynomial is a product of distinct linear factors `∏(X − αᵢ)` and use the
resultant/root identities `Polynomial.resultant_eq_prod_eval` /
`Polynomial.discr` sign conventions already present in
`RingTheory/Polynomial/Resultant/Basic.lean`.  Note the constant case
`discr (C r) = 1`.) -/
theorem discr_ne_zero_of_separable {F : Type*} [Field F] (p : F[X])
    (hp : p.Monic) (hsep : p.Separable) : Polynomial.discr p ≠ 0 := by
  classical
  by_cases hn0 : p.natDegree = 0
  · have hp1 : p = 1 := monic_eq_one_of_natDegree_eq_zero hp hn0
    rw [hp1]
    rw [show (1 : F[X]) = C (1 : F) by simp]
    rw [Polynomial.discr_C]
    norm_num
  · have hn : 0 < p.natDegree := Nat.pos_of_ne_zero hn0
    let L := p.SplittingField
    let φ : F →+* L := algebraMap F L
    let q : L[X] := p.map φ
    have hφi : Function.Injective φ := RingHom.injective φ
    have hqmon : q.Monic := by simpa [q] using hp.map φ
    have hqspl : q.Splits := by
      simpa [q] using IsSplittingField.splits L p
    have hqsep : q.Separable := by
      simpa [q] using ((Polynomial.separable_map φ).mpr hsep)
    have hq_nodup : q.roots.Nodup := nodup_roots hqsep
    have hnd : q.natDegree = p.natDegree := by
      exact natDegree_map_eq_of_injective hφi p
    have hnq : 0 < q.natDegree := by rwa [hnd]
    -- The value of the derivative at each root of `q` is nonzero.
    have hval_ne : ∀ a : L, a ∈ q.roots → eval a q.derivative ≠ 0 := by
      intro a ha
      rw [Splits.eval_root_derivative hqspl hqmon ha]
      refine Multiset.prod_ne_zero ?_
      intro hz
      rcases Multiset.mem_map.mp hz with ⟨b, hb, hz'⟩
      have hba : b ≠ a := (hq_nodup.mem_erase_iff.mp hb).1
      exact sub_ne_zero.mpr (Ne.symm hba) hz'
    -- Therefore the product of these values over all roots is nonzero.
    have hprod_ne : ((q.roots.map fun a => eval a q.derivative).prod) ≠ 0 := by
      refine Multiset.prod_ne_zero ?_
      intro hz
      rcases Multiset.mem_map.mp hz with ⟨a, ha, hz'⟩
      exact hval_ne a ha hz'
    have hdiscq : q.discr ≠ 0 := by
      rw [discr_eq_negOne_pow_prod_deriv q hqmon hqspl hnq]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hprod_ne
    have hφd : φ (Polynomial.discr p) ≠ 0 := by
      rwa [← (discr_map φ p hp)]
    intro h0
    exact hφd (by rw [h0, map_zero])

end

end Commons.FieldTheory.Polynomial