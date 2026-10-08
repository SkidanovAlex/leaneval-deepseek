import Mathlib
import Submission.Work.BSW.Char.Setup

namespace Work.BSW.Char

/-- The number of ordered pairs `(u, v)` of involutions with `u * v = x` is the coefficient at `x`
of the square of the class sum of the conjugacy class of `t`, when every involution is conjugate to
`t`.

Route: `OddOrder.RepresentationTheory.classSum_mul_apply` writes the coefficient as the cardinality
of `{p : G × G | ConjClasses.mk p.1 = ConjClasses.mk t ∧ ConjClasses.mk p.2 = ConjClasses.mk t ∧
p.1 * p.2 = x}` cast to `ℂ`, while `Work.BSW.invPairCount G x` is the `Set.ncard` of
`{p : G × G | orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ p.1 * p.2 = x}`.  The two sets are equal because
the hypotheses give `ConjClasses.mk u = ConjClasses.mk t ↔ orderOf u = 2` for every `u`:
`←` is `hconj` composed with `ConjClasses.mk_eq_mk_iff_isConj`, and `→` is
`ConjClasses.mk_eq_mk_iff_isConj` plus conjugation-invariance of `orderOf`
(`orderOf (c * u * c⁻¹) = orderOf u`, conveniently via `orderOf_injective` of the conjugation
monoid hom; Mathlib has no `orderOf_conj`, but `Work.ZASS.orderOf_conj` in
`Submission/Work/ZASS/bruhat_decomposition.lean` is one; either prove it locally or import it) and
`ht`.  Then bridge `Set.ncard` and `Finset.card` of `Finset.univ.filter` (e.g. via
`Set.ncard_coe_finset`). -/
theorem invPairCount_eq_coeff_classSum_mul_self {G : Type} [Group G] [Fintype G] [DecidableEq G]
    [DecidableEq (ConjClasses G)] {t : G} (ht : orderOf t = 2)
    (hconj : ∀ u : G, orderOf u = 2 → IsConj u t) (x : G) :
    (Work.BSW.invPairCount G x : ℂ) =
      (OddOrder.GroupTheory.CenterClassSum.classSum (ConjClasses.mk t) *
        OddOrder.GroupTheory.CenterClassSum.classSum (ConjClasses.mk t) :
        MonoidAlgebra ℂ G).coeff x := by
  classical
  -- Conjugation invariance of `orderOf`, proved locally (Mathlib has no `orderOf_conj`).
  have hoc : ∀ c u : G, orderOf (c * u * c⁻¹) = orderOf u := by
    intro c u
    rw [← MulAut.conj_apply]
    exact MulEquiv.orderOf_eq (MulAut.conj c) u
  -- The hypotheses turn membership of the class of `t` into being an involution.
  have hkey : ∀ u : G, ConjClasses.mk u = ConjClasses.mk t ↔ orderOf u = 2 := by
    intro u
    constructor
    · intro h
      obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h)
      rw [← ht, ← hoc c u, hc]
    · intro hu
      exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hconj u hu)
  -- `invPairCount` as a `Finset` cardinality over the class-of-`t` predicate.
  have hcard : Work.BSW.invPairCount G x =
      (Finset.univ.filter (fun p : G × G =>
        ConjClasses.mk p.1 = ConjClasses.mk t ∧ ConjClasses.mk p.2 = ConjClasses.mk t
          ∧ p.1 * p.2 = x)).card := by
    rw [Work.BSW.invPairCount]
    have hset : {p : G × G | orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ p.1 * p.2 = x}
        = ↑(Finset.univ.filter (fun p : G × G =>
            ConjClasses.mk p.1 = ConjClasses.mk t ∧ ConjClasses.mk p.2 = ConjClasses.mk t
              ∧ p.1 * p.2 = x)) := by
      ext p
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq]
      rw [hkey p.1, hkey p.2]
    rw [hset, Set.ncard_coe_finset]
  rw [hcard, OddOrder.RepresentationTheory.classSum_mul_apply]

end Work.BSW.Char
