import Mathlib
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.SmallChainsIsoAux
import Submission.Work.Cohomology.exists_small_homotopy
import Submission.Work.Cohomology.exists_iter_small

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cohomology

open CategoryTheory
-- Exactness of the quotient complex `C_*(X)/C^{U,V}_*(X)` of the small chains of an open cover
-- in degree `n`: a chain whose boundary is small differs from a boundary by a small chain.
-- (For `n = 0` the hypothesis is `d 0 (0-1) b ∈ smallChainSubmodule U V (0-1)`, i.e. it is
-- vacuous since `d 0 0 = 0`, and it is then exactly the statement `H₀` of the quotient vanishes.)
-- Proof: take `N` with `sdChainMapIter X N b` small (`exists_iter_small_chain`), let
-- `T : Homotopy (sdChainMapIter X N) 𝟙` be the smallness preserving homotopy
-- (`exists_small_homotopy`), and use the elementwise homotopy formula
-- `Work.Cohomology.homotopy_apply_eq`:  `Sd^N b = T (∂b) + ∂ (T b) + b`, so
-- `b + ∂(T b) = Sd^N b - T (∂ b)` is small because `∂b` is small by hypothesis and both `Sd^N`
-- and the homotopy components of `T` preserve small chains (`iter_sd_small`).
-- Accordingly we take `c = -(T b)`, so that `b - ∂c = b + ∂(T b)`.
theorem exists_sub_small_of_boundary_small {X : TopCat} (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (n : ℕ)
    (b : (Work.Cohomology.singularChains ℤ X).X n)
    (hb : ((Work.Cohomology.singularChains ℤ X).d n (n - 1)) b
      ∈ Work.Cohomology.smallChainSubmodule U V (n - 1)) :
    ∃ c : (Work.Cohomology.singularChains ℤ X).X (n + 1),
      b - ((Work.Cohomology.singularChains ℤ X).d (n + 1) n) c
        ∈ Work.Cohomology.smallChainSubmodule U V n := by
  -- a high enough iterate of the subdivision makes `b` small
  obtain ⟨N, hN⟩ := exists_iter_small_chain U V hU hV hcov n b
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

end Work.Cohomology
