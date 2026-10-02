import Submission.Work.Orient.Closed
import Submission.Work.Cohomology.HomologyPairSequence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-!
# The homology of the complement of a closed set meeting every component

For a compact Hausdorff space `M` charted on `ℝⁿ` (`n ≥ 1`) and a closed **nonempty** subset
`F ⊆ M` meeting every connected component of `M` (the hypothesis `hmeets`: every clopen set
containing `F` is everything), the complement `M ∖ F` has vanishing singular homology in all
degrees `≥ n`:

`H_m(M∖F; ℤ) = 0` for `m ≥ n`.

This is the "noncompact dimension bound" in the form used for the punctured sphere bundle: it
generalises `Work.Tubular.TubeClass.isZero_homology_compl_point_man8_all` (the case `F = {x}`, `n = 8`)
to an arbitrary closed set meeting every component and to every dimension `n ≥ 1`.

The proof is the standard one:

* for `m > n`, the long exact sequence of the pair `(M, M∖F)` has
  `H_{m+1}(M, M∖F) = 0` (Hatcher 3.27 (b), `F` is compact) and `H_m(M) = 0` (Hatcher 3.27 (b) with
  `A = M`), so the inclusion `H_m(M∖F) → H_m(M)` is injective onto `0`;
* for `m = n`, the same exact sequence makes `H_n(M∖F) → H_n(M)` injective with image the kernel of
  the localisation `H_n(M) → H_n(M, M∖F)`; a class in that image has vanishing local class at every
  point of `F`, and the set of points where a local class vanishes is clopen, so by `hmeets` the
  local class vanishes everywhere, and `Work.Orient.eq_zero_of_locClass_eq_zero` (Hatcher 3.27 (a))
  forces the class to be zero.
-/

open CategoryTheory AlgebraicTopology Limits
open scoped Topology

namespace Work.Tubular.PuncturedDiscPair

noncomputable section

open Work.Cohomology

/-- **The homology of the complement of a closed set meeting every component vanishes in degrees
`≥ n`.** -/
theorem isZero_homology_compl_of_clopen_meets {M : TopCat} [T2Space M] [CompactSpace M] {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (hn : 1 ≤ n)
    (F : Set M) (hFc : IsClosed F) (hFne : F.Nonempty)
    (hmeets : ∀ W : Set M, IsClopen W → F ⊆ W → W = Set.univ) :
    ∀ m, n ≤ m → IsZero ((singularChains ℤ (TopCat.of ↥Fᶜ)).homology m) := by
  classical
  -- `H_m(M) = 0` above the dimension (Hatcher 3.27 (b) with `A = M`)
  have hAbs : ∀ m, n < m → IsZero ((singularChains ℤ M).homology m) := by
    intro m hm
    have h := relChains_vanishing_of_compact (n := n) hn (M := M) (Set.univ : Set M)
      isCompact_univ m hm
    rw [Set.compl_univ] at h
    haveI := relChains_empty_homology_iso M m
    exact IsZero.of_iso h (asIso (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (inclChains M (∅ : Set M))) m))
  -- the relative vanishing `H_m(M, M∖F) = 0` above the dimension
  have hRel : ∀ m, n < m → IsZero ((relChains M Fᶜ).homology m) :=
    fun m hm => relChains_vanishing_of_compact (n := n) hn (M := M) F hFc.isCompact m hm
  -- the inclusion `H_n(M∖F) → H_n(M)` is injective
  have hinjn : Function.Injective
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains M Fᶜ) n)) := by
    have hδn : hPairδ M Fᶜ n = 0 := IsZero.eq_zero_of_src (hRel (n + 1) (by omega)) _
    have hrange : (ModuleCat.Hom.hom (hPairδ M Fᶜ n)).range = ⊥ := by
      rw [hδn]; exact LinearMap.range_zero
    have hker : (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (inclChains M Fᶜ) n)).ker = ⊥ := by
      rw [← (hPair_exact₁ M Fᶜ n).moduleCat_range_eq_ker, hrange]
    exact LinearMap.ker_eq_bot.mp hker
  intro m hm
  rcases eq_or_lt_of_le hm with hmn | hmn
  · -- ### the critical degree `m = n`
    subst hmn
    have hkey : ∀ y : (singularChains ℤ (TopCat.of ↥Fᶜ)).homology n,
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains M Fᶜ) n)) y = 0 := by
      intro y
      set c : (singularChains ℤ M).homology n :=
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains M Fᶜ) n)) y with hc
      -- the localisation of `c` at the excluded set `F` vanishes
      have hzero : relLocClass M n c F = 0 := by
        rw [relLocClass]
        have h1 := (hPair_exact₂ M Fᶜ n).moduleCat_range_eq_ker
        have h2 : c ∈ LinearMap.range (ModuleCat.Hom.hom
            (HomologicalComplex.homologyMap (inclChains M Fᶜ) n)) := ⟨y, hc.symm⟩
        rw [h1] at h2
        exact (LinearMap.mem_ker).mp h2
      -- hence the local class vanishes at every point of `F`
      have hFsub : F ⊆ {z : M | Work.Orient.locClass M n c z = 0} := by
        intro z hz
        have hK : ({z} : Set M) ⊆ F := Set.singleton_subset_iff.mpr hz
        have h2 := relLocClass_restrict M n c hK
        rw [hzero, map_zero] at h2
        show Work.Orient.locClass M n c z = 0
        rw [Work.Orient.locClass_eq_relClass]
        exact h2.symm
      -- the vanishing set of the local class is clopen
      have hcl : IsClopen {z : M | Work.Orient.locClass M n c z = 0} := by
        constructor
        · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
          intro z hz
          obtain ⟨K, hK, hzK, hKn⟩ := Work.Orient.exists_isCoordBall_mem_nhds n M z
          filter_upwards [hKn] with w hw
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
          intro hw0
          exact hz ((Work.Orient.relClass_eq_zero_iff_locClass_eq_zero hn hK hzK).mp
            ((Work.Orient.relClass_eq_zero_iff_locClass_eq_zero hn hK hw).mpr hw0))
        · rw [isOpen_iff_mem_nhds]
          intro z hz
          obtain ⟨K, hK, hzK, hKn⟩ := Work.Orient.exists_isCoordBall_mem_nhds n M z
          filter_upwards [hKn] with w hw
          exact (Work.Orient.relClass_eq_zero_iff_locClass_eq_zero hn hK hw).mp
            ((Work.Orient.relClass_eq_zero_iff_locClass_eq_zero hn hK hzK).mpr hz)
      have hall : ∀ z : M, Work.Orient.locClass M n c z = 0 := by
        intro z
        have hW := hmeets {z : M | Work.Orient.locClass M n c z = 0} hcl hFsub
        have : z ∈ ({z : M | Work.Orient.locClass M n c z = 0}) := by rw [hW]; trivial
        exact this
      exact Work.Orient.eq_zero_of_locClass_eq_zero n hn M c hall
    refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => sub_eq_zero.mp (hinjn ?_)⟩
    rw [map_sub, hkey a, hkey b, sub_self, map_zero]
  · -- ### degrees above the dimension
    haveI : Subsingleton ↥((singularChains ℤ M).homology m) :=
      ModuleCat.isZero_iff_subsingleton.mp (hAbs m hmn)
    refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => sub_eq_zero.mp ?_⟩
    have hδ : hPairδ M Fᶜ m = 0 := IsZero.eq_zero_of_src (hRel (m + 1) (by omega)) _
    have hinj : Function.Injective
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains M Fᶜ) m)) := by
      have hrange : (ModuleCat.Hom.hom (hPairδ M Fᶜ m)).range = ⊥ := by
        rw [hδ]; exact LinearMap.range_zero
      have hker : (ModuleCat.Hom.hom
          (HomologicalComplex.homologyMap (inclChains M Fᶜ) m)).ker = ⊥ := by
        rw [← (hPair_exact₁ M Fᶜ m).moduleCat_range_eq_ker, hrange]
      exact LinearMap.ker_eq_bot.mp hker
    apply hinj
    rw [map_sub]
    have hsub : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains M Fᶜ) m)) a
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains M Fᶜ) m)) b :=
      Subsingleton.elim _ _
    rw [hsub, sub_self, map_zero]

end

end Work.Tubular.PuncturedDiscPair
