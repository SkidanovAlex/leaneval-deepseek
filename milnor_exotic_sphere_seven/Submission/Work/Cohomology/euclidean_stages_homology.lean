import Mathlib
import Submission.Work.Cohomology.CompactComplDefs
import Submission.Work.Cohomology.Duality.ball_local_homology
import Submission.Work.Cohomology.homologyMV_honest_les
import Submission.Work.Cohomology.free_and_vanishing_ball_compl
import Submission.Work.Cohomology.homology_vanishing_relative_compact
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.homology_zero_free
import Submission.Work.Cohomology.free_submodule_of_free_int
import Submission.Work.Cohomology.EuclideanStageDefs
import Submission.Work.Cohomology.euclidean_stage_split

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Cohomology

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

set_option backward.isDefEq.respectTransparency false


/-! ## Extracting homology of pairs and Mayer-Vietoris vanishing -/

/-- The Mayer-Vietoris map `H_m(U ∩ V) ⟶ H_m(U) ⊞ H_m(V)` is injective when `H_{m+1}(X)` vanishes. -/
theorem mono_homMVF_of_isZero {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (m : ℕ) (h : IsZero (pdHom X (m + 1))) :
    Mono (homMVF X U V m) := by
  have hf : homMVδ X U V hU hV hcov m = 0 := h.eq_zero_of_src _
  have hEx := homMV_exact₁ X U V hU hV hcov m
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hEx
  have hker : LinearMap.ker (ModuleCat.Hom.hom (homMVF X U V m)) = ⊥ := by
    rw [← hEx, show ModuleCat.Hom.hom (homMVδ X U V hU hV hcov m) = 0 from by rw [hf]; rfl]
    simp
  exact (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker_eq_bot.mp hker)

/-! ## The two inputs of the proof -/

/-- **Freeness.**  For finitely many closed balls in `ℝ^N`, the `(N-1)`-st homology of the
complement is a free `ℤ`-module. -/
theorem free_compl_union_balls {N : ℕ} (hN : 1 ≤ N) {k : ℕ}
    (c : Fin k → EuclideanSpace ℝ (Fin N)) (r : Fin k → ℝ) (hr : ∀ j, 0 < r j) :
    Module.Free ℤ ↥((singularChains ℤ
      (TopCat.of (Set.compl (⋃ j, Metric.closedBall (c j) (r j))))).homology (N - 1)) := by
  rcases eq_or_lt_of_le hN with h1 | h2
  · subst h1
    exact homology_zero_free _
  · obtain ⟨n, φ, hφ⟩ := exists_inj_fin_compl_union_convex (N := N) h2
      (Finset.univ : Finset (Fin k)) (fun j => Metric.closedBall (c j) (r j))
      (fun j _ => isCompact_closedBall _ _) (fun j _ => convex_closedBall _ _)
    have hfree : Module.Free ℤ ↥((singularChains ℤ (TopCat.of {x : EuclideanSpace ℝ (Fin N) |
        x ∉ ⋃ j ∈ (Finset.univ : Finset (Fin k)), Metric.closedBall (c j) (r j)})).homology
          (N - 1)) :=
      (injective_into_fun_free φ hφ).2.1
    have hbig : (⋃ j ∈ (Finset.univ : Finset (Fin k)), Metric.closedBall (c j) (r j)) =
        (⋃ j, Metric.closedBall (c j) (r j)) := by
      ext x
      simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left]
    have hset : {x : EuclideanSpace ℝ (Fin N) |
        x ∉ ⋃ j ∈ (Finset.univ : Finset (Fin k)), Metric.closedBall (c j) (r j)} =
        Set.compl (⋃ j, Metric.closedBall (c j) (r j)) := by
      rw [hbig]
      rfl
    exact Module.Free.of_equiv' hfree
      (Classical.choice (homologyIsoOfSetEq hset (N - 1))).toLinearEquiv

/-- **The component condition.**  Under the hypotheses of the statement, every connected component
of `T n` meets `T (n+1)`: every ball of `T n` meets `K ⊆ T (n+1)`, and a connected set meeting a
connected component of `T n` is contained in it. -/
theorem component_meets_next {N : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin N))) (T : ℕ → Set (EuclideanSpace ℝ (Fin N)))
    (hKsub : ∀ n, K ⊆ T n)
    (k : ℕ → ℕ) (c : (n : ℕ) → Fin (k n) → EuclideanSpace ℝ (Fin N))
    (r : (n : ℕ) → Fin (k n) → ℝ)
    (hT : ∀ n, T n = ⋃ j, Metric.closedBall (c n j) (r n j))
    (hmeet : ∀ n j, (Metric.closedBall (c n j) (r n j)) ∩ K ≠ ∅) :
    ∀ n (x : EuclideanSpace ℝ (Fin N)), x ∈ T n →
      ∃ y ∈ T (n+1), x ∈ connectedComponentIn (T n) y := by
  intro n x hx
  have hx' : x ∈ ⋃ j, Metric.closedBall (c n j) (r n j) := by rw [← hT n]; exact hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx'
  obtain ⟨z, hzj, hzK⟩ := Set.nonempty_iff_ne_empty.mpr (hmeet n j)
  refine ⟨z, hKsub (n+1) hzK, ?_⟩
  exact (convex_closedBall (c n j) (r n j)).isPreconnected.subset_connectedComponentIn hzj
    (by rw [hT n]; exact Set.subset_iUnion (fun j => Metric.closedBall (c n j) (r n j)) j) hj

theorem euclidean_stages_homology {N : ℕ} (hN : 1 ≤ N)
    (K : Set (EuclideanSpace ℝ (Fin N)))
    (T : ℕ → Set (EuclideanSpace ℝ (Fin N))) (hmono : ∀ n, T (n+1) ⊆ T n)
    (htop : ∀ n, T (n+1) ⊆ interior (T n))
    (hKsub : ∀ n, K ⊆ T n)
    (k : ℕ → ℕ) (c : (n : ℕ) → Fin (k n) → EuclideanSpace ℝ (Fin N))
    (r : (n : ℕ) → Fin (k n) → ℝ) (hr : ∀ n j, 0 < r n j)
    (hT : ∀ n, T n = ⋃ j, Metric.closedBall (c n j) (r n j))
    (hmeet : ∀ n j, (Metric.closedBall (c n j) (r n j)) ∩ K ≠ ∅) :
    (∀ n, Module.Free ℤ ↥((singularChains ℤ (TopCat.of (Set.compl (T n)))).homology (N - 1))) ∧
    (∀ n, ∃ s : ↥((singularChains ℤ (TopCat.of (Set.compl (T (n+1))))).homology (N - 1)) →ₗ[ℤ]
                ↥((singularChains ℤ (TopCat.of (Set.compl (T n)))).homology (N - 1)),
        s.comp (stageMap T hmono n) = LinearMap.id ∧ Module.Free ℤ ↥(LinearMap.ker s)) := by
  classical
  -- the two auxiliary statements, phrased in the `⋃ j, closedBall` form
  have hsub' : ∀ n, (⋃ j, Metric.closedBall (c (n+1) j) (r (n+1) j)) ⊆
      interior (⋃ j, Metric.closedBall (c n j) (r n j)) := by
    intro n
    rw [← hT (n+1), ← hT n]
    exact htop n
  have hcomp' : ∀ n (x : EuclideanSpace ℝ (Fin N)),
      x ∈ (⋃ j, Metric.closedBall (c n j) (r n j)) →
      ∃ y ∈ (⋃ j, Metric.closedBall (c (n+1) j) (r (n+1) j)),
        x ∈ connectedComponentIn (⋃ j, Metric.closedBall (c n j) (r n j)) y := by
    intro n x hx
    rw [← hT n] at hx
    obtain ⟨y, hy, hxy⟩ := component_meets_next K T hKsub k c r hT hmeet n x hx
    refine ⟨y, ?_, ?_⟩
    · rwa [← hT (n+1)]
    · rwa [← hT n]
  -- replace `T` by the explicit unions everywhere
  have hTfun : T = fun n => ⋃ j, Metric.closedBall (c n j) (r n j) := funext hT
  subst hTfun
  refine ⟨fun n => free_compl_union_balls hN (c n) (r n) (hr n), fun n => ?_⟩
  obtain ⟨s, hs⟩ := euclidean_stage_split (N := N) hN (c := c n) (r := r n) (hr := hr n)
    (c' := c (n+1)) (r' := r (n+1)) (hr' := hr (n+1)) (hsub' n) (hcomp' n)
  refine ⟨s, ?_, ?_⟩
  · have hsm : stageMap (fun n => ⋃ j, Metric.closedBall (c n j) (r n j)) hmono n =
        complMap (⋃ j, Metric.closedBall (c n j) (r n j))
          (⋃ j, Metric.closedBall (c (n+1) j) (r (n+1) j))
          (fun x hx => interior_subset (hsub' n hx)) := rfl
    rw [hsm]
    exact hs
  · haveI hfreeB : Module.Free ℤ ↥((singularChains ℤ
        (TopCat.of (Set.compl (⋃ j, Metric.closedBall (c (n+1) j) (r (n+1) j))))).homology
          (N - 1)) :=
      free_compl_union_balls hN (c (n+1)) (r (n+1)) (hr (n+1))
    exact free_submodule_of_free_int _

end

end Work.Cohomology
