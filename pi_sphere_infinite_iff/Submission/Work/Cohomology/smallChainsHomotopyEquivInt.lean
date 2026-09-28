import Mathlib
import Submission.Work.Cohomology.smallChainsHomotopyEquiv
import Submission.Work.Cohomology.smallChains_homology_iso_int
import Submission.Work.Cohomology.exists_sub_small_of_boundary_small
import Submission.Work.Cohomology.SmallChains

/-!
# The small chains are chain homotopy equivalent to the singular chains, for covers by interiors

`Work.Cohomology.smallChainsHomotopyEquiv` proves

`∃ e : HomotopyEquiv (smallChains U V) (singularChains ℤ X), e.hom = smallToSing U V`

for an **open** cover `X = U ∪ V`.  The classical hypothesis needed for the Mayer–Vietoris
sequence is weaker: it suffices that the *interiors* cover, `interior U ∪ interior V = univ`.

As explained in `Submission/Work/Cohomology/smallChains_homology_iso_int.lean`, the openness of `U`
and `V` is used in exactly one place in the whole chain of arguments: the refinement statement
`exists_iter_small` ("some iterate of the barycentric subdivision of a simplex is small"), proved
from the Lebesgue number of the pulled-back cover of `Δⁿ`.  Everything else — the degreewise split
inclusion `smallToSing U V` with retraction `smallProj U V` (`smallProj_spec`, no openness), the
local homotopy `Sd^N ~ id` (`exists_small_homotopy`, no openness), and the contraction
`existsSmallChainsContraction` built from the exactness hypothesis `hD` — is insensitive to
openness.

This file therefore provides the interior version of the one remaining input `hD`
(`exists_sub_small_of_boundary_small_int`), obtained by replacing `exists_iter_small_chain` with
its interior counterpart `exists_iter_small_chain_int`, and then repeats the three line assembly of
`smallChainsHomotopyEquiv`.

## Main result

* `smallChainsHomotopyEquivInt` — the chain homotopy equivalence for a cover by interiors.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- **Exactness of the quotient of the small chains, for a cover by interiors.**  A singular chain
whose boundary is small differs from a boundary by a small chain, assuming only that
`interior U ∪ interior V = univ`.

This is `Work.Cohomology.exists_sub_small_of_boundary_small` with the openness hypotheses on `U`
and `V` (and `U ∪ V = univ`) replaced by the single hypothesis `interior U ∪ interior V = univ`.
The proof is that of the open version with the single refinement step
`exists_iter_small_chain U V hU hV hcov` replaced by its interior counterpart
`exists_iter_small_chain_int U V hcov`; evereything else uses only the local homotopy
`exists_small_homotopy`, which does not see the covering sets. -/
theorem exists_sub_small_of_boundary_small_int (U V : Set X)
    (hcov : interior U ∪ interior V = Set.univ) (n : ℕ)
    (b : (singularChains ℤ X).X n)
    (hb : ((singularChains ℤ X).d n (n - 1)) b
      ∈ smallChainSubmodule U V (n - 1)) :
    ∃ c : (singularChains ℤ X).X (n + 1),
      b - ((singularChains ℤ X).d (n + 1) n) c
        ∈ smallChainSubmodule U V n := by
  -- a high enough iterate of the subdivision makes `b` small
  obtain ⟨N, hN⟩ := exists_iter_small_chain_int U V hcov n b
  -- a chain homotopy from that iterate to the identity whose components preserve small chains
  obtain ⟨T, hT⟩ := exists_small_homotopy X U V N
  -- the homotopy image of the (small) boundary of `b` is small
  have hprev : IsSmallChain U V
      ((ModuleCat.Hom.hom (T.hom (n-1) n))
        ((ModuleCat.Hom.hom ((singularChains ℤ X).d n (n-1))) b)) := by
    rcases n with _ | m
    · -- in degree `0` the boundary is zero, and `T.hom 0 0 = 0` as well
      rw [show (0:ℕ)-1 = 0 from rfl]
      have hz : (T.hom 0 0 : (singularChains ℤ X).X 0 ⟶ (singularChains ℤ X).X 0) = 0 :=
        Homotopy.zero T 0 0 (by rw [ComplexShape.down_Rel]; omega)
      have hd : (((singularChains ℤ X).d 0 0) :
          (singularChains ℤ X).X 0 ⟶ (singularChains ℤ X).X 0) = 0 :=
        HomologicalComplex.shape _ 0 0 (by rw [ComplexShape.down_Rel]; omega)
      rw [hz, hd]
      simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
      exact (smallChainSubmodule U V 0).zero_mem
    · -- in positive degree this is the smallness preserving property of `T`
      exact hT m _ hb
  refine ⟨-((T.hom n (n+1)) b), ?_⟩
  rw [map_neg, sub_neg_eq_add]
  -- the elementwise homotopy formula `Sd^N b = T(∂b) + ∂(T b) + b`
  have hkey := homotopy_apply_eq X N n T b
  have hgoal : b + ((singularChains ℤ X).d (n+1) n) ((T.hom n (n+1)) b)
      = (ModuleCat.Hom.hom ((sdChainMapIter X N).f n)) b
        - (ModuleCat.Hom.hom (T.hom (n-1) n))
            ((ModuleCat.Hom.hom ((singularChains ℤ X).d n (n-1))) b) := by
    rw [hkey]; abel
  rw [hgoal]
  -- `Sd^N b` is small by choice of `N`, and `T (∂b)` is small by `hprev`
  exact IsSmallChain.sub hN hprev

/-- **The small chains are chain homotopy equivalent to the singular chains**, for a cover by
interiors, with the inclusion itself as the forward map.

This is `Work.Cohomology.smallChainsHomotopyEquiv` with the open cover hypothesis
`U ∪ V = univ` (together with `IsOpen U`, `IsOpen V`) replaced by
`interior U ∪ interior V = univ`. -/
theorem smallChainsHomotopyEquivInt {X : TopCat} (U V : Set X)
    (hcov : interior U ∪ interior V = Set.univ) :
    ∃ e : HomotopyEquiv (Work.Cohomology.smallChains U V) (Work.Cohomology.singularChains ℤ X),
      e.hom = Work.Cohomology.smallToSing U V := by
  -- the projection onto the small chains is a retraction of the inclusion ...
  obtain ⟨hcomp, hgenS, hgenN⟩ := smallProj_spec (X := X) U V
  -- ... fixing the generators of the small simplices ...
  have hr2 : ∀ n (σ : Simplex X n) (h : IsSmall U V σ),
      ((smallToSing U V).f n) ((smallProj U V n) (gen X n σ)) = gen X n σ := by
    intro n σ h
    rw [hgenS n σ h]
    exact smallToSing_gen ⟨σ, h⟩
  -- ... while the quotient of the singular chains by the small chains is acyclic; hence there is
  -- a contraction of the complement of the small chains in the singular chains ...
  obtain ⟨κ, h1, h2, h3zero, h3⟩ :=
    existsSmallChainsContraction U V (smallProj U V) hcomp hr2 hgenN
      (exists_sub_small_of_boundary_small_int U V hcov)
  -- ... which exhibits the inclusion as a homotopy equivalence.
  exact homotopyEquivOfRetract (smallToSing U V) (smallProj U V) hcomp κ h1 h2 h3zero h3

end

end Work.Cohomology
