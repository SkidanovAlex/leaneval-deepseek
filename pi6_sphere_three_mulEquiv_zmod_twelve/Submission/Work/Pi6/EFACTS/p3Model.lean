import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Serre.serreC0HurewiczEquiv
import Submission.Work.Serre.attachIncl_const_piMapN_bijective
import Submission.Work.FGThm.serreFGTheorem
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.RatHurewicz.SphereConnectivity
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The Postnikov section `g₃ : S³ → P₃` makes `P₃` a `K(ℤ,3)` range model

`PostnikovData 3 12 g3 s3` says that `g3 : S³ → P₃` is a bijection on `π_i` for `i ≤ 3` and that
`π_i(P₃) = 0` for `3 < i ≤ 12`.  Hence

* `π₃(P₃) ≅ π₃(S³) ≅ ℤ`: the first isomorphism is the bijectivity of `π₃(g3)`, the second is
  Hurewicz in the first non-vanishing degree (`S³` is `2`-connected, the classical connectivity of
  spheres `Work.RatHurewicz.sphereConnected`, and `H₃(S³;ℤ) ≅ ℤ`
  (`Work.Cohomology.sphereHomologyTop`)) packaged as a group isomorphism by
  `Work.Serre.serreC0HurewiczEquiv`;
* `π_i(P₃) = 0` for `i < 3`: surjectivity of `π_i(g3)` from `π_i(S³) = 0`;
* `π_i(P₃) = 0` for `3 < i ≤ 12`: the second half of the Postnikov data.

This is `Work.Serre.IsEMSpaceUpTo ℤ 3 _ 12 P₃ (g3 s3)`, assembled by
`Work.FGThm.isEMSpaceUpTo_of_rangeModel`.
-/

open scoped Topology

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Pi6.EFACTS

noncomputable section

theorem p3Model {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3)) (hg : Work.Pi6.PostnikovData 3 12 g3 Work.Pi6.s3) : Work.Serre.IsEMSpaceUpTo ℤ 3 (by norm_num) 12 P3 (g3 Work.Pi6.s3) := by
  -- `S³` is `2`-connected
  have hconn : ∀ j : ℕ, j < 3 →
      Subsingleton (HomotopyGroup (Fin j) Work.Pi6.S3 Work.Pi6.s3) :=
    fun j hj => Work.RatHurewicz.sphereConnected 3 (by norm_num) Work.Pi6.s3 j hj
  refine Work.FGThm.isEMSpaceUpTo_of_rangeModel (by norm_num) (g3 Work.Pi6.s3) (by norm_num) ?_ ?_
  · -- `π₃(P₃) ≅* Multiplicative ℤ`
    -- `H₃(S³;ℤ) ≅ ℤ`
    obtain ⟨eH⟩ := Work.Cohomology.sphereHomologyTop 3 (by norm_num)
    -- Hurewicz: `π₃(S³) ≅* Multiplicative ℤ`
    obtain ⟨eπ⟩ := Work.Serre.serreC0HurewiczEquiv (X := Work.Pi6.S3) (m := 3) (by norm_num)
      Work.Pi6.s3 hconn eH.toLinearEquiv
    -- `π₃(g3)` is a bijection
    have hbij : Function.Bijective (Work.StemsB.πmap g3 2 Work.Pi6.s3) := by
      have h := hg.1 3 le_rfl Work.Pi6.s3
      rw [Work.Serre.piMapN_eq_pimap_succ g3 2 Work.Pi6.s3] at h
      exact h
    exact ⟨(MulEquiv.ofBijective _ hbij).symm.trans eπ⟩
  · -- vanishing of `π_i(P₃)`, `i ≠ 3`, `i ≤ 12`
    intro i hi hiN
    rcases lt_trichotomy i 3 with h | h | h
    · -- `i < 3`: `π_i(S³) = 0` and `π_i(g3)` is onto
      haveI := hconn i h
      exact (hg.1 i (le_of_lt h) Work.Pi6.s3).2.subsingleton
    · exact absurd h hi
    · -- `3 < i`: the Postnikov data
      exact hg.2 i h hiN (g3 Work.Pi6.s3)

end

end Work.Pi6.EFACTS
