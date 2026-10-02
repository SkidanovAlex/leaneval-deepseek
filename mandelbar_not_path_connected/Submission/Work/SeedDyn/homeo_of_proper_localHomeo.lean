import Mathlib
import Submission.Work.Top.Defs
import Submission.Work.ParamRays.isPreconnected_lt_norm_of_differentiable
import Submission.Work.SeedDyn.isPathConnected_exteriorDisc
import Submission.Work.SeedDyn.bijective_of_isCoveringMap_singleton_fiber
import Submission.Work.SeedDyn.isLocalHomeomorph_subtypeMap
import Submission.Work.SeedDyn.isProperMap_subtypeMap
import Submission.Work.SeedDyn.isDiscrete_preimage_singleton
import Submission.Work.SeedDyn.exists_unique_preimage_of_far

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set Function Topology Filter

namespace Work.SeedDyn

/-- **A proper local homeomorphism onto the exterior disc is a homeomorphism.**

Let `U ⊆ ℂ` be open, `f : ℂ → ℂ` satisfy `1 < ‖f z‖` on `U`, be a local homeomorphism on `U`,
be "proper into the exterior disc" (`hcpt`), bounded on bounded subsets of `U` (`hbdd`),
injective on the far region `{R ≤ ‖z‖}` (`hR`) and coercive in the sense that `‖f z‖` bounded
forces `‖z‖` bounded (`hgrow`).  Then `f` induces a homeomorphism `U ≃ₜ {w | 1 < ‖w‖}`.

The proof: the induced map `F : U → exteriorDisc` is a proper local homeomorphism, hence (by
`IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn`) a covering map with finite fibres.  The
hypotheses `hbdd`/`hR`/`hgrow` exhibit a point `z₀` whose fibre is a singleton, and a covering map
of a path-connected base with one singleton fibre is bijective
(`bijective_of_isCoveringMap_singleton_fiber`).  A bijective local homeomorphism is a
homeomorphism. -/
theorem homeo_of_proper_localHomeo {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U)
    (hmaps : ∀ z ∈ U, 1 < ‖f z‖)
    (hloc : IsLocalHomeomorphOn f U)
    (hcpt : ∀ K : Set ℂ, IsCompact K → (∀ w ∈ K, 1 < ‖w‖) → IsCompact (U ∩ f ⁻¹' K))
    (hbdd : ∀ R : ℝ, ∃ M : ℝ, ∀ z ∈ U, ‖z‖ ≤ R → ‖f z‖ ≤ M)
    (hR : ∃ R : ℝ, {z : ℂ | R ≤ ‖z‖} ⊆ U ∧ Set.InjOn f {z : ℂ | R ≤ ‖z‖})
    (hgrow : ∀ M : ℝ, ∃ R' : ℝ, ∀ z ∈ U, ‖f z‖ ≤ M → ‖z‖ ≤ R') :
    ∃ e : ↥U ≃ₜ ↥Work.Top.exteriorDisc, ∀ z : ↥U, f z = (e z : ℂ) := by
  set V : Set ℂ := Work.Top.exteriorDisc with hV
  have hVopen : IsOpen V := by
    rw [hV]; exact isOpen_lt continuous_const continuous_norm
  have hm : ∀ z ∈ U, f z ∈ V := by
    intro z hz
    rw [hV]
    exact Work.Top.mem_exteriorDisc.mpr (hmaps z hz)
  set F : ↥U → ↥V := Subtype.map f (fun z hz => hm z hz) with hF
  have hcoe : ∀ z : ↥U, ((F z : ↥V) : ℂ) = f z := fun z => by simp only [hF, Subtype.map_coe]
  have hFloc : IsLocalHomeomorph F := isLocalHomeomorph_subtypeMap hU hVopen hm hloc
  have hcpt' : ∀ K : Set ℂ, IsCompact K → (∀ w ∈ K, w ∈ V) → IsCompact (U ∩ f ⁻¹' K) := by
    intro K hK hw
    refine hcpt K hK fun w hw' => ?_
    have h1 := hw w hw'
    rwa [hV, Work.Top.mem_exteriorDisc] at h1
  have hproper : IsProperMap F := isProperMap_subtypeMap hm hloc.continuousOn hcpt'
  have hfinite : ∀ x : ↥V, (F ⁻¹' {x}).Finite := fun x =>
    (hproper.isCompact_preimage isCompact_singleton).finite
      (isDiscrete_preimage_singleton hFloc x)
  have hcov : IsCoveringMap F := by
    refine isCoveringMap_iff_isCoveringMapOn_univ.mpr ?_
    refine hproper.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn ?_ ?_
    · intro x _
      exact hfinite x
    · simpa using hFloc.isLocalHomeomorphOn
  obtain ⟨z₀, hz₀U, hz₀uniq⟩ := exists_unique_preimage_of_far hmaps hbdd hR hgrow
  set z0 : ↥U := ⟨z₀, hz₀U⟩ with hz0
  have hfib : F ⁻¹' {F z0} = {z0} := by
    ext z
    rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_singleton_iff]
    constructor
    · intro hz
      refine Subtype.ext ((hz₀uniq z z.2).mp ?_)
      have h2 := congrArg (fun w : ↥V => (w : ℂ)) hz
      rwa [hcoe z, hcoe z0] at h2
    · intro hz; rw [hz]
  have hVpc : IsPathConnected V := by rw [hV]; exact isPathConnected_exteriorDisc
  haveI : PathConnectedSpace ↥V := isPathConnected_iff_pathConnectedSpace.mp hVpc
  have hbij : Function.Bijective F := bijective_of_isCoveringMap_singleton_fiber hcov hfib
  refine ⟨hFloc.toHomeomorphOfBijective hbij, fun z => ?_⟩
  show f z = ((F z : ↥V) : ℂ)
  exact (hcoe z).symm

end Work.SeedDyn
