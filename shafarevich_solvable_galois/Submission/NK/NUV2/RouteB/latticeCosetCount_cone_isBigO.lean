import Mathlib
import Submission.NK.NUV2.Geom.latticeCosetCount_sub_volume_isBigO
import Submission.NK.NUV2.Minkowski.frontier_thickening_normLeOne
import Submission.NK.NUV2.Minkowski.frontier_thickening_expMapBasis_paramSet
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lattice point count in the fundamental cone

For a number field `K`, a fractional ideal `I` and a shift `x₀`, the number of points of the
coset `x₀ + I` (the ideal lattice of `I` in the mixed space `ℝ^{r₁} × ℂ^{r₂}`) that lie in the
fundamental cone and have norm `≤ X` is asymptotic to

  `X * 2^{r₁} * (2π)^{r₂} * Reg(K) / (|N I| * √|disc K|)`

with a power-saving error term.

The analytic content is the classical Minkowski-content (boundary layer) estimate for the
region `normLeOne K = fundamentalCone K ∩ {N ≤ 1}`, whose frontier has `(n-1)`-dimensional
content: `volume (cthickening ε (frontier (normLeOne K))) ≤ c * ε`
(`NK.NUV2.Geom.volume_cthickening_frontier_normLeOne`).  This is fed into the general lattice
point count with error term (`NK.NUV2.Geom.latticeCosetCount_sub_volume_isBigO`) applied to the
ideal lattice `idealLattice K I` in the mixed space.

The main term is computed in `volume_normLeOne_div_covolume` from Mathlib's
`volume_normLeOne` (the volume of the region) and `covolume_idealLattice` (the covolume of the
ideal lattice).
-/

namespace NK.NUV2.RouteB

set_option autoImplicit false
open scoped Classical Pointwise nonZeroDivisors
open MeasureTheory NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone

variable {K : Type*} [Field K] [NumberField K]

/-- The dilate of `normLeOne K` by `T ^ (1 / [K : ℚ])` is the trace of the fundamental cone by
the norm ball of radius `T`. -/
lemma smul_normLeOne_eq_routeB (T : ℝ) (hT : 0 < T) :
    (T ^ ((Module.finrank ℚ K : ℝ)⁻¹)) • normLeOne K
      = fundamentalCone K ∩ {x : mixedSpace K | mixedEmbedding.norm x ≤ T} := by
  have hc : (0 : ℝ) < T ^ ((Module.finrank ℚ K : ℝ)⁻¹) := Real.rpow_pos_of_pos hT _
  have hcN : (T ^ ((Module.finrank ℚ K : ℝ)⁻¹)) ^ Module.finrank ℚ K = T :=
    Real.rpow_inv_natCast_pow hT.le Module.finrank_pos.ne'
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', mem_normLeOne, smul_mem_iff_mem (inv_ne_zero hc.ne')]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [mixedEmbedding.norm_smul, abs_inv, abs_of_pos hc, inv_pow, hcN] at h2
    rwa [inv_mul_le_iff₀ hT, mul_one] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [mixedEmbedding.norm_smul, abs_inv, abs_of_pos hc, inv_pow, hcN, inv_mul_le_iff₀ hT, mul_one]
    exact h2

/-- The points of the coset `x₀ + I` of the ideal lattice lying in the fundamental cone with norm
`≤ X` are in bijection with the lattice points of `I` in the dilated region `X^{1/n} • normLeOne K`
(by `a ↦ a - x₀`). -/
lemma natCard_cone_coset_eq_routeB
    (I : (FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K)ˣ) (x₀ : mixedSpace K)
    {X : ℝ} (hX : 1 ≤ X) :
    Nat.card {a : mixedSpace K // a - x₀ ∈ (idealLattice K I : Set (mixedSpace K)) ∧
        a ∈ fundamentalCone K ∧ mixedEmbedding.norm a ≤ X}
      = Nat.card {x : idealLattice K I // x₀ + (x : mixedSpace K) ∈
          (X ^ ((Module.finrank ℝ (mixedSpace K) : ℝ)⁻¹)) • normLeOne K} := by
  have hS : (X ^ ((Module.finrank ℝ (mixedSpace K) : ℝ)⁻¹)) • normLeOne K
      = fundamentalCone K ∩ {x : mixedSpace K | mixedEmbedding.norm x ≤ X} := by
    rw [NumberField.mixedEmbedding.finrank]
    exact smul_normLeOne_eq_routeB X (lt_of_lt_of_le one_pos hX)
  have hmem : ∀ a : mixedSpace K,
      (a ∈ (X ^ ((Module.finrank ℝ (mixedSpace K) : ℝ)⁻¹)) • normLeOne K)
      ↔ (a ∈ fundamentalCone K ∧ mixedEmbedding.norm a ≤ X) := fun a => by
        rw [hS]; exact Set.mem_inter_iff a _ _
  have key : Nat.card {a : mixedSpace K // a - x₀ ∈ (idealLattice K I : Set (mixedSpace K)) ∧
        a ∈ fundamentalCone K ∧ mixedEmbedding.norm a ≤ X}
      = Nat.card {a : mixedSpace K // a - x₀ ∈ (idealLattice K I : Set (mixedSpace K)) ∧
        a ∈ (X ^ ((Module.finrank ℝ (mixedSpace K) : ℝ)⁻¹)) • normLeOne K} := by
    refine Nat.card_congr (Equiv.subtypeEquivProp (funext fun a => propext ?_))
    exact ⟨fun h => ⟨h.1, (hmem a).mpr h.2⟩, fun h => ⟨h.1, (hmem a).mp h.2⟩⟩
  rw [key]
  refine Nat.card_congr ?_
  refine
    { toFun := fun a => ⟨⟨a.1 - x₀, a.2.1⟩, ?_⟩
      invFun := fun x => ⟨x₀ + (x.1 : mixedSpace K), ⟨?_, ?_⟩⟩
      left_inv := fun a => Subtype.ext (by simp [add_sub_cancel])
      right_inv := fun x => Subtype.ext (Subtype.ext (by simp [add_sub_cancel_left])) }
  · simpa [add_sub_cancel] using a.2.2
  · simpa [add_sub_cancel_left] using x.1.2
  · exact x.2

/-- **The main term.** The ratio of the volume of `normLeOne K` to the covolume of the ideal
lattice of `I` is `2^{r₁} (2π)^{r₂} Reg(K) / (|N I| √|disc K|)`. -/
lemma volume_normLeOne_div_covolume
    (I : (FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K)ˣ) :
    (volume (normLeOne K)).toReal / ZLattice.covolume (idealLattice K I)
      = 2 ^ InfinitePlace.nrRealPlaces K * (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces K *
          Units.regulator K /
        ((FractionalIdeal.absNorm
            (I : FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K) : ℝ) *
          Real.sqrt |((discr K : ℤ) : ℝ)|) := by
  have hvol : (volume (normLeOne K)).toReal =
      2 ^ InfinitePlace.nrRealPlaces K * Real.pi ^ InfinitePlace.nrComplexPlaces K *
        Units.regulator K := by
    rw [volume_normLeOne]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (Units.regulator_pos K).le]
    rw [NNReal.coe_real_pi]
  rw [hvol, covolume_idealLattice]
  have habs : (FractionalIdeal.absNorm
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) ≠ 0 := by
    intro h
    have h1 : (FractionalIdeal.absNorm
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℚ) = 0 := by
      exact_mod_cast h
    rw [FractionalIdeal.absNorm_eq_zero_iff] at h1
    exact Units.ne_zero I h1
  have hsq : Real.sqrt |((discr K : ℤ) : ℝ)| ≠ 0 := by
    rw [Real.sqrt_ne_zero']
    rw [abs_pos]
    exact_mod_cast NumberField.discr_ne_zero K
  field_simp
  ring_nf
  have h12 : ((1 / 2 : ℝ) ^ InfinitePlace.nrComplexPlaces K) *
      (2 : ℝ) ^ InfinitePlace.nrComplexPlaces K = 1 := by
    rw [← mul_pow]; norm_num
  calc Real.pi ^ InfinitePlace.nrComplexPlaces K * Units.regulator K
      = Real.pi ^ InfinitePlace.nrComplexPlaces K * Units.regulator K * 1 := by ring
    _ = Real.pi ^ InfinitePlace.nrComplexPlaces K * Units.regulator K *
          (((1 / 2 : ℝ) ^ InfinitePlace.nrComplexPlaces K) *
            (2 : ℝ) ^ InfinitePlace.nrComplexPlaces K) := by rw [h12]
    _ = Real.pi ^ InfinitePlace.nrComplexPlaces K * Units.regulator K *
          (1 / 2 : ℝ) ^ InfinitePlace.nrComplexPlaces K *
          (2 : ℝ) ^ InfinitePlace.nrComplexPlaces K := by ring


/-- **Minkowski content of the frontier of the fundamental cone's `normLeOne`.** The
`ε`-neighbourhood of `frontier (normLeOne K)` in the mixed space has volume `≤ c * ε` for
`0 < ε ≤ 1`.  Deduced from the real-space estimate
(`NK.NUV2.Minkowski.frontier_thickening_expMapBasis_paramSet`) via the folding formula and the
`1`-Lipschitz map `normAtAllPlaces`
(`NK.NUV2.Minkowski.frontier_thickening_normLeOne_of_realSpace`). -/
lemma frontierNormLeOne_cthickening_le_routeB (K : Type) [Field K] [NumberField K] :
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

theorem latticeCosetCount_cone_isBigO (K : Type) [Field K] [NumberField K]
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
  -- The two analytic inputs.
  have hbd := frontierNormLeOne_cthickening_le_routeB K
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
    rw [natCard_cone_coset_eq_routeB I x₀ hX]
    have hX' := hC₁ X hX
    rw [mul_div_assoc, volume_normLeOne_div_covolume I] at hX'
    exact hX'

end NK.NUV2.RouteB
