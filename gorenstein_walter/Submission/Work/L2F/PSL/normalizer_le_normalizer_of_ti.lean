import Mathlib

namespace Work.L2F.PSL

/-- **TI property ⟹ the normalizer of a nontrivial subgroup is contained in the normalizer of the
ambient subgroup.**  If `U ≤ G` has trivial intersections with its conjugates by elements outside
its normalizer (the TI property), then for any `⊥ ≠ P ≤ U` one has `N_G(P) ≤ N_G(U)`: an
`x ∈ N_G(P)` keeps `P` inside both `U` and `x U x⁻¹`, so these meet nontrivially, which forces
`x ∈ N_G(U)`. -/
theorem normalizer_le_normalizer_of_ti {G : Type*} [Group G] (U P : Subgroup G)
    (hP : P ≤ U) (hne : P ≠ ⊥)
    (hti : ∀ x : G, x ∉ Subgroup.normalizer (U : Set G) →
      U ⊓ U.map (MulAut.conj x).toMonoidHom = ⊥) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (U : Set G) := by
  intro x hx
  by_contra hxU
  -- `x` moves `P` onto itself; if it were outside `N_G(U)` the TI hypothesis would force
  -- `U ⊓ x U x⁻¹ = ⊥`, but `P ≤ U` lies inside that intersection.
  have hdisj := hti x hxU
  have hle : P ≤ U ⊓ U.map (MulAut.conj x).toMonoidHom := by
    refine le_inf hP ?_
    intro p hp
    -- `x⁻¹ p x ∈ P`, so `p = x (x⁻¹ p x) x⁻¹` lies in the conjugate of `U`.
    have hconj : x⁻¹ * p * x ∈ P := (Subgroup.mem_normalizer_iff''.mp hx p).mp hp
    refine ⟨x⁻¹ * p * x, hP hconj, ?_⟩
    show (MulAut.conj x) (x⁻¹ * p * x) = p
    rw [MulAut.conj_apply]
    group
  have : P ≤ ⊥ := hle.trans (le_of_eq hdisj)
  exact hne (le_bot_iff.mp this)

end Work.L2F.PSL
