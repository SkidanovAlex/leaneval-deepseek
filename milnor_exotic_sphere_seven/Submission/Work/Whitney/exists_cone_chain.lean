import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Thom.stepDefs
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Whitney.capCycle
import Submission.Work.Cohomology.homologyContractible

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The affine cone over a cycle of `tcmX Y n 1`

`tcmX Y n 1 = Y × (ℝⁿ × ℝ¹)` is, for `Y` a point (i.e. `Subsingleton Y` and `Nonempty Y`),
the contractible space `ℝⁿ⁺¹`; hence its reduced singular homology vanishes and **every** cycle of
positive degree is a boundary.  That is the content of `exists_cone_chain`: the affine cone over a
cycle `c` of degree `n ≥ 1` (the "no primitive, no radial map" cone of
`rankOne_cup_model_NOTES.md` §42i item 1 / §43) is *some* chain `Z` with `∂Z = c`.

We do not build the cone simplex explicitly: the ambient space is contractible, so
`Work.Cohomology.homologyContractible` gives `Hₙ(tcmX Y n 1) = 0`, and exactness at `n` turns
"`c` is a cycle" into "`c` is a boundary".  (The smallness hypothesis `hcS` is not needed for the
existence; it is what guarantees that the *explicit* cone lies in the ball.  It is kept in the
statement for the consumer.)
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.Whitney

theorem exists_cone_chain (Y : Type) [TopologicalSpace Y] [Subsingleton Y] [Nonempty Y] (n : ℕ)
    (hn : 1 ≤ n)
    (c : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Whitney.tcmX Y n 1))).X n)
    (hc : ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.Whitney.tcmX Y n 1))).d n (n - 1)) c = 0)
    (hcS : Work.Cohomology.IsSmallChain
      {x : Work.Whitney.tcmX Y n 1 | Work.Whitney.tcmF Y n 1 x ∈ Work.Thom.Sph Y (n + 1)} ∅ c) :
    ∃ Z : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Whitney.tcmX Y n 1))).X (n + 1),
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.Whitney.tcmX Y n 1))).d (n + 1) n) Z = c := by
  classical
  -- `tcmX Y n 1 = Y × (ℝⁿ × ℝ¹)` is contractible, so its singular homology vanishes in degree `n`.
  haveI hcontr : ContractibleSpace (TopCat.of (Work.Whitney.tcmX Y n 1)) := inferInstance
  let C : ChainComplex (ModuleCat ℤ) ℕ :=
    Work.Cohomology.singularChains ℤ (TopCat.of (Work.Whitney.tcmX Y n 1))
  have hZ : CategoryTheory.Limits.IsZero (C.homology n) :=
    Work.Cohomology.homologyContractible (X := TopCat.of (Work.Whitney.tcmX Y n 1)) n (by omega)
  -- index bookkeeping for the shape `ComplexShape.down ℕ`
  have next_eq : ∀ m : ℕ, (ComplexShape.down ℕ).next m = m - 1 := by
    intro m
    cases m with
    | zero => simp [ChainComplex.next_nat_zero]
    | succ m => simp [ChainComplex.next_nat_succ]
  have prev_eq : ∀ m : ℕ, (ComplexShape.down ℕ).prev m = m + 1 := fun m => ChainComplex.prev ℕ m
  -- exactness of `C_{n+1} --d--> C_n --d--> C_{n-1}` at `n`
  have hEx : (C.sc' (n+1) n (n-1)).Exact :=
    (C.exactAt_iff' (n+1) n (n-1) (prev_eq n) (next_eq n)).1
      ((C.exactAt_iff_isZero_homology n).2 hZ)
  -- hence `range d_{n+1,n} = ker d_{n,n-1}`, and `c` lies in the kernel
  have hrk : LinearMap.range (ModuleCat.Hom.hom (C.d (n+1) n))
      = LinearMap.ker (ModuleCat.Hom.hom (C.d n (n-1))) :=
    CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hEx
  have hmem : c ∈ LinearMap.ker (ModuleCat.Hom.hom (C.d n (n-1))) := by
    rw [LinearMap.mem_ker]
    exact hc
  rw [← hrk] at hmem
  obtain ⟨Z, hZc⟩ := LinearMap.mem_range.mp hmem
  exact ⟨Z, hZc⟩

end Work.Whitney

