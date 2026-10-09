import Mathlib
import Submission.Work.SSGRoute.InvAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.InvAux

/-!
# Irreducible polynomials over the fixed field of an involution

Let `Ω` be an algebraically closed field of characteristic zero and `c` an involutive
automorphism of `Ω` (`c * c = 1`).  Write `F = Ω^c` for its fixed field.  We show that every
irreducible polynomial over `F` has degree at most `2`.

The key input is `minpoly_natDegree_le_two` (`InvAux.lean`): every element of `Ω` satisfies a
quadratic polynomial over `F`.  Given an irreducible `f` over `F`, algebraic closedness of `Ω`
provides a root `α` of `f`; the minimal polynomial of `α` divides `f`, and since `f` is
irreducible and `minpoly F α` is not a unit they are associated, so the two have the same
degree.  Hence `f.natDegree = (minpoly F α).natDegree ≤ 2`.
-/

/-- Any irreducible polynomial over the fixed field `Ω^c` of an involution `c` of an
algebraically closed field `Ω` of characteristic zero has degree at most two. -/
theorem irreducible_natDegree_le_two {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    {c : Ω ≃+* Ω} (hc : c * c = 1)
    {f : Polynomial ↥(Work.SSGRoute.InvAux.fixSub c)} (hf : Irreducible f) :
    f.natDegree ≤ 2 := by
  -- `f` is a nonzero, nonconstant polynomial.
  have hfdeg : 0 < f.degree := hf.degree_pos
  have hfne : f ≠ 0 := by
    intro h
    rw [h, Polynomial.degree_zero] at hfdeg
    exact not_lt_bot hfdeg
  -- Since `Ω` is algebraically closed, `f` has a root `α ∈ Ω`.
  have hdeg : (f.map (algebraMap ↥(fixSub c) Ω)).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact hfdeg.ne'
  obtain ⟨α, hαroot⟩ :=
    IsAlgClosed.exists_root (f.map (algebraMap ↥(fixSub c) Ω)) hdeg
  have hα : (Polynomial.aeval α) (f.map (algebraMap ↥(fixSub c) Ω)) = 0 := by
    rw [Polynomial.IsRoot.def] at hαroot
    simpa [Polynomial.aeval_def] using hαroot
  have hαroot' : (Polynomial.aeval α) f = 0 := by
    rw [← Polynomial.aeval_map_algebraMap Ω α f]
    exact hα
  -- The minimal polynomial of `α` over `F` divides `f`.
  have hdvd : minpoly ↥(fixSub c) α ∣ f :=
    minpoly.dvd ↥(fixSub c) α hαroot'
  have hgne : minpoly ↥(fixSub c) α ≠ 0 := by
    intro h
    rw [h, zero_dvd_iff] at hdvd
    exact hfne hdvd
  -- `minpoly F α` is not a unit, so irreducibility of `f` makes them associated.
  have hnotunit : ¬ IsUnit (minpoly ↥(fixSub c) α) := by
    intro h
    obtain ⟨r, hr, hCr⟩ := Polynomial.isUnit_iff.mp h
    have haev := minpoly.aeval ↥(fixSub c) α
    rw [← hCr, Polynomial.aeval_C] at haev
    have hr0 : r = 0 := by
      apply Subtype.ext
      simpa using haev
    exact hr.ne_zero hr0
  have hassoc : Associated f (minpoly ↥(fixSub c) α) :=
    ((hf.dvd_iff).mp hdvd).resolve_left hnotunit
  calc f.natDegree ≤ (minpoly ↥(fixSub c) α).natDegree :=
        Polynomial.natDegree_le_of_dvd hassoc.dvd hgne
    _ ≤ 2 := minpoly_natDegree_le_two hc α

end Work.SSGRoute.InvAux
