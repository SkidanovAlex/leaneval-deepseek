import Mathlib
import Submission.Work.Shrinking.FreeOperator
import Submission.Work.SSGRoute.exists_orbit_transversal
import Submission.Work.SSGRoute.exists_equiv_transversal_mul_zmodTwo
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- A finite type `X` with a fixed-point-free involution `σ` is, as a `σ`-set, a disjoint union
of two-element orbits; equivalently it is isomorphic to `Fin d × Multiplicative (ZMod 2)` for
`d` the number of orbits, in such a way that `σ` acts by multiplying the second coordinate by
the generator `ofAdd 1` of `Multiplicative (ZMod 2)`.

This is the set-theoretic input of the "free operator" bookkeeping in Shafarevich's theorem: the
free `Z/2`-set `X` is the free basis set `Fin d × G` of a `G`-operator group for `G = Z/2`. -/
theorem exists_equiv_fin_mul_zmodTwo {X : Type*} [Finite X] (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x)
    (hfree : ∀ x, σ x ≠ x) :
    ∃ (d : ℕ) (e : X ≃ (Fin d × Multiplicative (ZMod 2))),
      ∀ x : X, e (σ x) = Work.Shrinking.freeOperatorGenPerm d
        (Multiplicative.ofAdd (1 : ZMod 2)) (e x) := by
  classical
  -- Choose one representative `r x` from each two-element orbit `{x, σ x}`.
  obtain ⟨r, hidem, hmem, hcomm⟩ := exists_orbit_transversal σ hσ hfree
  -- `x ↦ (r x, 1)` on representatives and `x ↦ (r x, ofAdd 1)` on the other element of the orbit
  -- is a `σ`-equivariant bijection onto `{x // r x = x} × ZMod 2`.
  obtain ⟨e, he⟩ := exists_equiv_transversal_mul_zmodTwo σ hσ hfree r hidem hmem hcomm
  haveI : Fintype X := Fintype.ofFinite X
  -- Relabel the set of representatives `{x // r x = x}` by `Fin d`.
  refine ⟨Fintype.card {x : X // r x = x}, ?_⟩
  refine ⟨e.trans (Equiv.prodCongr (Fintype.equivFin {x : X // r x = x}) (Equiv.refl _)), ?_⟩
  intro x
  rw [Work.Shrinking.freeOperatorGenPerm_apply]
  apply Prod.ext
  · simp [Equiv.trans_apply, Prod.map_fst, (he x).1]
  · simp [Equiv.trans_apply, Prod.map_snd, (he x).2]

end Work.SSGRoute
