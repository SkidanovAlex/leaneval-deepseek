import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Submission.NK.NUV2.RouteB.CongCountDefs
import Submission.NK.NUV2.RouteB.latticeCosetCount_cone_isBigO
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The congruence-class cone count with a power-saving error term

This file proves `NK.NUV2.RouteB.CongCount.cosetConeCount_of_geoHyp`: for a number field `K`, a
nonzero ideal `𝔪` of `𝓞 K` and an element `c : 𝓞 K`, the number of points of the coset `c + 𝔪`
lying in the fundamental cone with norm `≤ X` equals `X` times the Minkowski main term, up to
`O(X ^ θ)` for some `θ < 1`.

The proof identifies the coset count with the lattice point count of the coset of the ideal
lattice `idealLattice K 𝔪` by the shift `mixedEmbedding K c`: an algebraic integer `α` lies in
the coset `c + 𝔪` exactly when `mixedEmbedding K α - mixedEmbedding K c` lies in the image of `𝔪`
inside the mixed space.  The counting input is the (universe-polymorphic form of the) Minkowski /
boundary-layer estimate for the fundamental cone
(`NK.NUV2.RouteB.latticeCosetCount_cone_isBigO`).

The geometric hypothesis `GeoHyp` passed as an argument is a universe-`0` statement (`∀ K : Type`),
whereas the statement to be proved is universe polymorphic in `K`; the proof therefore proceeds
through the explicit, universe-polymorphic instance of the boundary-layer estimate rather than
through `hGeo`.
-/

namespace NK.NUV2.RouteB.CongCount

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open scoped Classical Pointwise nonZeroDivisors
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]

/-! ## The coset `c + 𝔪` as a coset of the ideal lattice -/

/-- Membership in the ideal lattice attached to a nonzero integral ideal `𝔪`: the elements of the
mixed space which are the canonical image of some `a ∈ 𝔪`. -/
lemma mem_idealLattice_idealUnit (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ 0) (x : mixedSpace K) :
    x ∈ idealLattice K (NK.NUV2.RouteB.idealUnit 𝔪 h𝔪) ↔
      ∃ a : 𝓞 K, a ∈ 𝔪 ∧ mixedEmbedding K a = x := by
  rw [NumberField.mixedEmbedding.mem_idealLattice]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [NK.NUV2.RouteB.idealUnit_coe] at hy
    simp only [FractionalIdeal.coe_mk0] at hy
    obtain ⟨a, ha, hay⟩ := (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 K))).mp hy
    exact ⟨a, ha, congrArg (mixedEmbedding K) hay⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(a : K), ?_, rfl⟩
    rw [NK.NUV2.RouteB.idealUnit_coe]
    simp only [FractionalIdeal.coe_mk0]
    exact (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 K))).mpr ⟨a, ha, rfl⟩

/-- The canonical embedding is additive on differences of algebraic integers. -/
lemma mixedEmbedding_sub (a b : 𝓞 K) :
    mixedEmbedding K (a - b) = mixedEmbedding K a - mixedEmbedding K b := by
  simp only [map_sub]

/-- **The combinatorial identification.**  The points of the coset `c + 𝔪` in the fundamental cone
of norm `≤ X` are in bijection with the points of the coset `mixedEmbedding K c + L` in the
fundamental cone of norm `≤ X`, where `L` is the ideal lattice of `𝔪`. -/
lemma card_cosetConeCount_eq (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ 0) (c : 𝓞 K) (X : ℝ) :
    Nat.card {α : 𝓞 K // α - c ∈ 𝔪 ∧ mixedEmbedding K α ∈ fundamentalCone K ∧
        mixedEmbedding.norm (mixedEmbedding K α) ≤ X}
      = Nat.card {x : mixedSpace K // x - mixedEmbedding K c ∈
            (idealLattice K (NK.NUV2.RouteB.idealUnit 𝔪 h𝔪) : Set (mixedSpace K)) ∧
          x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ X} := by
  classical
  refine Nat.card_congr (Equiv.ofBijective
    (fun a : {α : 𝓞 K // α - c ∈ 𝔪 ∧ mixedEmbedding K α ∈ fundamentalCone K ∧
        mixedEmbedding.norm (mixedEmbedding K α) ≤ X} =>
      ⟨mixedEmbedding K a.1, ?_, a.2.2.1, a.2.2.2⟩) ⟨?_, ?_⟩)
  · exact (mem_idealLattice_idealUnit 𝔪 h𝔪 _).mpr ⟨a.1 - c, a.2.1, mixedEmbedding_sub a.1 c⟩
  · intro a b hab
    have h : (a.1 : K) = (b.1 : K) :=
      NumberField.mixedEmbedding_injective (K := K) (congrArg Subtype.val hab)
    exact Subtype.ext (RingOfIntegers.coe_injective h)
  · intro b
    have hb : ∃ a : 𝓞 K, a ∈ 𝔪 ∧ mixedEmbedding K a = b.1 - mixedEmbedding K c :=
      (mem_idealLattice_idealUnit 𝔪 h𝔪 _).mp b.2.1
    let y : 𝓞 K := Classical.choose hb
    have hy : y ∈ 𝔪 ∧ mixedEmbedding K y = b.1 - mixedEmbedding K c := Classical.choose_spec hb
    refine ⟨⟨y + c, ?_, ?_, ?_⟩, ?_⟩
    · simpa using hy.1
    · simp only [map_add, hy.2, sub_add_cancel]; exact b.2.2.1
    · simp only [map_add, hy.2, sub_add_cancel]; exact b.2.2.2
    · apply Subtype.ext
      simp only [map_add, hy.2, sub_add_cancel]

/-! ## The boundary-layer estimate, universe polymorphically -/

/-- **Minkowski content of the frontier of `normLeOne K`.** The `ε`-neighbourhood of
`frontier (normLeOne K)` in the mixed space has volume `≤ c * ε` for `0 < ε ≤ 1`.
This is the universe-polymorphic form of
`NK.NUV2.RouteB.frontierNormLeOne_cthickening_le_routeB`. -/
lemma frontierNormLeOne_cthickening_le (K : Type*) [Field K] [NumberField K] :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      volume (Metric.cthickening ε (frontier (normLeOne K))) ≤ ENNReal.ofReal (c * ε) := by
  obtain ⟨C, hCpos, hC⟩ :=
    NK.NUV2.Minkowski.frontier_thickening_normLeOne_of_realSpace (K := K)
      (NK.NUV2.Minkowski.frontier_thickening_expMapBasis_paramSet K)
  refine ⟨C, hCpos, fun ε hε hε1 => ?_⟩
  have hcth : ∀ x : mixedSpace K,
      (x ∈ Metric.cthickening ε (frontier (normLeOne K))) ↔
        ∃ p ∈ frontier (normLeOne K), ‖x - p‖ ≤ ε := by
    intro x
    rw [Metric.cthickening_eq_biUnion_closedBall _ hε.le, isClosed_frontier.closure_eq]
    constructor
    · intro hx
      obtain ⟨q, hq, hqx⟩ := Set.mem_iUnion₂.mp hx
      exact ⟨q, hq, by simpa [dist_eq_norm] using Metric.mem_closedBall.mp hqx⟩
    · rintro ⟨q, hq, hqx⟩
      exact Set.mem_iUnion₂.mpr ⟨q, hq,
        Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hqx)⟩
  set S : Set (mixedSpace K) := {x | ∃ p ∈ frontier (normLeOne K), ‖x - p‖ ≤ ε} with hS
  have hfin : volume S ≠ ⊤ := by
    obtain ⟨R, hR⟩ := (isBounded_normLeOne K).closure.exists_norm_le
    have hsub : S ⊆ Metric.closedBall (0 : mixedSpace K) (R + ε) := by
      rintro x ⟨p, hp, hpx⟩
      refine Metric.mem_closedBall.mpr ?_
      calc dist x 0 = ‖x‖ := by rw [dist_eq_norm, sub_zero]
        _ = ‖p + (x - p)‖ := by rw [add_sub_cancel]
        _ ≤ ‖p‖ + ‖x - p‖ := norm_add_le _ _
        _ ≤ R + ε := add_le_add (hR p (frontier_subset_closure hp)) hpx
    exact ne_top_of_le_ne_top ((isCompact_closedBall _ _).measure_lt_top.ne)
      (measure_mono hsub)
  have hset : Metric.cthickening ε (frontier (normLeOne K)) = S := Set.ext fun x => hcth x
  rw [hset]
  calc volume S = ENNReal.ofReal (volume S).toReal := (ENNReal.ofReal_toReal hfin).symm
    _ ≤ ENNReal.ofReal (C * ε) := ENNReal.ofReal_le_ofReal (hC ε hε hε1)

/-- **Lattice point count in the fundamental cone**, universe-polymorphic form: for a number
field `K`, a fractional ideal `I` and a shift `x₀`, the number of points of the coset `x₀ + I`
lying in the fundamental cone with norm `≤ X` is `X` times the Minkowski main term, up to
`O(X ^ θ)` with `θ < 1`. -/
theorem latticeConeCount_isBigO (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)ˣ)
    (x₀ : NumberField.mixedEmbedding.mixedSpace K) :
    ∃ (C θ : ℝ), 0 < C ∧ θ < 1 ∧ ∀ X : ℝ, 1 ≤ X →
      |((Nat.card {a : NumberField.mixedEmbedding.mixedSpace K //
          a - x₀ ∈ (NumberField.mixedEmbedding.idealLattice K I :
            Set (NumberField.mixedEmbedding.mixedSpace K)) ∧
          a ∈ NumberField.mixedEmbedding.fundamentalCone K ∧
          NumberField.mixedEmbedding.norm a ≤ X}) : ℝ)
        - X * (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
            (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
            NumberField.Units.regulator K /
            ((FractionalIdeal.absNorm
                (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) : ℝ) *
              Real.sqrt |((NumberField.discr K : ℤ) : ℝ)|))|
      ≤ C * X ^ θ := by
  have hbd := frontierNormLeOne_cthickening_le K
  have hmain :=
    NK.NUV2.Geom.latticeCosetCount_sub_volume_isBigO
      (NumberField.mixedEmbedding.mixedSpace K) (NumberField.mixedEmbedding.idealLattice K I)
      (NumberField.mixedEmbedding.fundamentalCone.normLeOne K)
      (isBounded_normLeOne K)
      (measurableSet_normLeOne K) hbd x₀
  obtain ⟨C₁, hC₁pos, hC₁⟩ := hmain
  refine ⟨C₁, 1 - (Module.finrank ℝ (NumberField.mixedEmbedding.mixedSpace K) : ℝ)⁻¹,
    hC₁pos, ?_, ?_⟩
  · have hfr : (0 : ℝ) < (Module.finrank ℝ (mixedSpace K) : ℝ) := by
      rw [NumberField.mixedEmbedding.finrank]
      exact_mod_cast Module.finrank_pos
    have : ((Module.finrank ℝ (mixedSpace K) : ℝ))⁻¹ > 0 := inv_pos.mpr hfr
    linarith
  · intro X hX
    rw [NK.NUV2.RouteB.natCard_cone_coset_eq_routeB I x₀ hX]
    have hX' := hC₁ X hX
    rw [mul_div_assoc, NK.NUV2.RouteB.volume_normLeOne_div_covolume I] at hX'
    exact hX'

/-! ## The target -/

/-- **The coset cone count.**  For a number field `K`, a nonzero ideal `𝔪` of `𝓞 K` and `c : 𝓞 K`,
the number of points of the coset `c + 𝔪` lying in the fundamental cone with norm `≤ X` is
`X` times the Minkowski main term of `𝔪`, up to `O(X ^ θ)` with `θ < 1`. -/
theorem cosetConeCount_of_geoHyp (hGeo : NK.NUV2.RouteB.GeoHyp)
    (K : Type*) [Field K] [NumberField K]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ 0)
    (c : NumberField.RingOfIntegers K) :
    ∃ (C θ : ℝ), 0 < C ∧ θ < 1 ∧ ∀ X : ℝ, 1 ≤ X →
      |((NK.NUV2.RouteB.cosetConeCount 𝔪 c X : ℝ) -
        X * NK.NUV2.RouteB.coneMainTerm K
          (FractionalIdeal.mk0 K
            ⟨𝔪, mem_nonZeroDivisors_of_ne_zero h𝔪⟩))| ≤ C * X ^ θ := by
  obtain ⟨C, θ, hC, hθ, hbound⟩ :=
    latticeConeCount_isBigO K (NK.NUV2.RouteB.idealUnit 𝔪 h𝔪) (mixedEmbedding K c)
  refine ⟨C, θ, hC, hθ, fun X hX => ?_⟩
  have hcard := card_cosetConeCount_eq (K := K) 𝔪 h𝔪 c X
  simp only [NK.NUV2.RouteB.cosetConeCount]
  rw [hcard]
  exact hbound X hX

end NK.NUV2.RouteB.CongCount
