import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false

namespace Work.MotC5N3.LamAS
/-- The transcendence degree of the rational function field `K(t)` over `K` is `1`. -/
lemma trdeg_ratFunc_eq_one {K : Type*} [Field K] : Algebra.trdeg K (RatFunc K) = 1 := by
  haveI : Algebra.IsAlgebraic (Polynomial K) (RatFunc K) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := Polynomial K) (K := RatFunc K)
      (C := RatFunc K)).mpr inferInstance
  have hz : Algebra.trdeg (Polynomial K) (RatFunc K) = 0 := trdeg_eq_zero
  have h := trdeg_add_eq K (Polynomial K) (A := RatFunc K)
  rw [hz, add_zero] at h
  rw [Polynomial.trdeg_of_isDomain] at h
  exact h.symm

/-- The algebraic closure of `K(t)` has transcendence degree `1` over `K`. -/
lemma trdeg_algClosure_ratFunc_eq_one {K : Type*} [Field K] :
    Algebra.trdeg K (AlgebraicClosure (RatFunc K)) = 1 := by
  have h0 : Algebra.trdeg (RatFunc K) (AlgebraicClosure (RatFunc K)) = 0 := trdeg_eq_zero
  have h := trdeg_add_eq K (RatFunc K) (A := AlgebraicClosure (RatFunc K))
  rw [h0, add_zero, trdeg_ratFunc_eq_one] at h
  exact h.symm

/-- **An injective `K`-algebra endomorphism of `AlgebraicClosure (RatFunc K)` is surjective.**
The assertion is false without the hypothesis that the transcendence degree of the algebraic closure
over `K` is finite; here it is `1`.  Full route (transcendence degree, `trdeg`) in
`Submission/Work/MotV5/LamAS/GUIDE_algClosure_endHom.md`. -/
theorem algClosure_algHom_surjective {K : Type*} [Field K]
    (ψ : AlgebraicClosure (RatFunc K) →ₐ[K] AlgebraicClosure (RatFunc K))
    (hψ : Function.Injective ψ) : Function.Surjective ψ := by
  -- `ψ.fieldRange` is a `K`-subfield of `Z = K(t)̄` isomorphic to `Z`, so it also has trdeg `1`.
  have hZ : Algebra.trdeg K (AlgebraicClosure (RatFunc K)) = 1 :=
    trdeg_algClosure_ratFunc_eq_one
  have hL : Algebra.trdeg K ↥(ψ.fieldRange) = 1 := by
    rw [← (ψ.equivFieldRange).trdeg_eq]
    exact hZ
  haveI : FaithfulSMul K ↥(ψ.fieldRange) :=
    (faithfulSMul_iff_algebraMap_injective K ↥(ψ.fieldRange)).mpr (RingHom.injective _)
  -- Additivity of the transcendence degree in the tower `K ≤ ψ.fieldRange ≤ Z` forces
  -- `trdeg ↥ψ.fieldRange Z = 0`; there is no room for a second transcendental element.
  have hb : Algebra.trdeg ↥(ψ.fieldRange) (AlgebraicClosure (RatFunc K)) = 0 := by
    have h := trdeg_add_eq K ↥(ψ.fieldRange) (A := AlgebraicClosure (RatFunc K))
    rw [hL, hZ] at h
    rcases (Cardinal.add_eq_left_iff.mp h) with hle | h0
    · exact absurd (le_trans (le_max_left Cardinal.aleph0 _) hle)
        (not_le_of_gt Cardinal.one_lt_aleph0)
    · exact h0
  -- Hence `Z` is algebraic over the subfield `ψ.fieldRange`, which is algebraically closed
  -- (it is isomorphic to `Z`), so `Z = ψ.fieldRange`.
  haveI : IsAlgClosed ↥(ψ.fieldRange) :=
    IsAlgClosed.of_ringEquiv (AlgebraicClosure (RatFunc K)) ↥(ψ.fieldRange)
      (ψ.equivFieldRange).toRingEquiv
  haveI : Algebra.IsAlgebraic ↥(ψ.fieldRange) (AlgebraicClosure (RatFunc K)) :=
    trdeg_eq_zero_iff.mp hb
  haveI : Algebra.IsIntegral ↥(ψ.fieldRange) (AlgebraicClosure (RatFunc K)) :=
    Algebra.IsAlgebraic.isIntegral
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := ↥(ψ.fieldRange)) (K := AlgebraicClosure (RatFunc K))
  intro z
  obtain ⟨w, hw⟩ := hbij.2 z
  obtain ⟨x, hx⟩ := (AlgHom.mem_fieldRange (f := ψ)).mp w.2
  exact ⟨x, hx.trans hw⟩

end Work.MotC5N3.LamAS