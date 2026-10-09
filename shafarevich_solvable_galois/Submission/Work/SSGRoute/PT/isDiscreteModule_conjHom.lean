import Mathlib
import Submission.Work.SSGRoute.PT.AlphaPairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Discreteness of `Hom_ℤ(N,C)` with the conjugation action

Let `G` be a topological group and let `N`, `C` be discrete `G`-modules (every element has an open
stabiliser), with `N` finite.  Then the coefficient module `Hom_ℤ(N,C)` with the **conjugation**
action `(g • f)(n) = g • f (g⁻¹ • n)` (`Work.SSGRoute.PT.ConjHom`) is again a discrete `G`-module.

Indeed `f` is determined by the finitely many values `f n`, and

  `U = ⋂_{n ∈ N} (Stab_G(n) ∩ Stab_G(f n))`

is a finite intersection of open subgroups, hence an open neighbourhood of `1` in `G`; if
`g ∈ U` then also `g⁻¹ ∈ U`, so for every `n` we get `g⁻¹ • n = n` and `g • f n = f n`, i.e.
`(g • f) n = g • f (g⁻¹ • n) = g • f n = f n`, whence `g • f = f`.  Thus `Stab_G(f)` contains a
neighbourhood of `1` and, being a subgroup, is open.

This is the input the local class formation needs in order to run the `α`-pairings
(`Work.SSGRoute.PT.alphaZero`, `Work.SSGRoute.PT.alphaTwo`) inside the *coefficient* cohomology
`H^*(G, Hom_ℤ(N,C))`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical

namespace Work.SSGRoute.PT

/-- A finite discrete module `N` and a discrete module `C` give a discrete conjugation module
`Hom_ℤ(N,C)`. -/
theorem isDiscreteModule_conjHom {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {N : Type*} [AddCommGroup N] [DistribMulAction G N] [Finite N]
    (hN : Work.AbsoluteKummer.IsDiscreteModule G N) {C : Type*} [AddCommGroup C]
    [DistribMulAction G C] (hC : Work.AbsoluteKummer.IsDiscreteModule G C) :
    Work.AbsoluteKummer.IsDiscreteModule G (Work.SSGRoute.PT.ConjHom N C) := by
  classical
  intro f
  letI : Fintype N := Fintype.ofFinite N
  -- the finite intersection of open stabilisers
  let U : Set G := ⋂ n : N,
    ((MulAction.stabilizer G n : Set G) ∩ (MulAction.stabilizer G (f n) : Set G))
  have hUopen : IsOpen U :=
    isOpen_iInter_of_finite (fun n => (hN n).inter (hC (f n)))
  have h1U : (1 : G) ∈ U := by
    refine Set.mem_iInter.mpr (fun n => ?_)
    exact ⟨one_mem _, one_mem _⟩
  have hUsub : U ⊆ (MulAction.stabilizer G f : Set G) := by
    intro g hg
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    -- `U` is closed under inverse, being an intersection of open subgroups
    have hg' : g⁻¹ ∈ U := Set.mem_iInter.mpr (fun n => ?_)
    · ext n
      rw [ConjHom.smul_apply,
        MulAction.mem_stabilizer_iff.mp (Set.mem_iInter.mp hg' n).1,
        MulAction.mem_stabilizer_iff.mp (Set.mem_iInter.mp hg n).2]
    · exact ⟨inv_mem (Set.mem_iInter.mp hg n).1, inv_mem (Set.mem_iInter.mp hg n).2⟩
  exact Subgroup.isOpen_of_mem_nhds (MulAction.stabilizer G f)
    (Filter.mem_of_superset (hUopen.mem_nhds h1U) hUsub)

end Work.SSGRoute.PT
