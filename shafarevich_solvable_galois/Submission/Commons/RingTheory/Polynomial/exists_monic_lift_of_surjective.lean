import Mathlib.Algebra.Polynomial.Lifts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Polynomial

theorem exists_monic_lift_of_surjective {R S : Type*} [Semiring R] [Semiring S] [Nontrivial R]
    [Nontrivial S] (f : R →+* S) (hf : Function.Surjective f) (g : Polynomial S) (hg : g.Monic) :
    ∃ p : Polynomial R, p.Monic ∧ p.natDegree = g.natDegree ∧ p.map f = g := by
  obtain ⟨p, hmap, hdeg, hmon⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic (f := f) (Polynomial.mem_lifts_of_surjective hf g) hg
  exact ⟨p, hmon, hdeg, hmap⟩

end Commons.RingTheory.Polynomial