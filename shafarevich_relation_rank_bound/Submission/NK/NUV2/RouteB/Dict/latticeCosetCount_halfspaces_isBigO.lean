import Mathlib
import Submission.NK.NUV2.Geom.latticeCosetCount_sub_volume_isBigO
import Submission.NK.NUV2.Geom.volume_cthickening_frontier_normLeOne_inter_halfspaces

/-!
# Lattice point count in the fundamental cone cut out by half-spaces

For a number field `K`, a fractional ideal `I`, a shift `x₀` and finitely many continuous linear
functionals `f i`, the number of points of the coset `x₀ + I` (the ideal lattice of `I` in the
mixed space `ℝ^{r₁} × ℂ^{r₂}`) that lie in the fundamental cone, satisfy `f i a < 0` and have
norm `≤ X` is asymptotic to

  `X * volume (normLeOne K ∩ {a | ∀ i, f i a < 0}) / covolume (idealLattice K I)`

with a power-saving error term `O(X ^ θ)`, `θ < 1`.

This is the half-space-restricted version of `NK.NUV2.RouteB.latticeCosetCount_cone_isBigO`.
The analytic content is the Minkowski-content (boundary layer) estimate for the region
`P = normLeOne K ∩ {a | ∀ i, f i a < 0}`, whose frontier has `(n-1)`-dimensional content:
`volume (cthickening ε (frontier P)) ≤ c * ε`
(`NK.NUV2.Geom.volume_cthickening_frontier_normLeOne_inter_halfspaces`).  This is fed into the
general lattice point count with error term
(`NK.NUV2.Geom.latticeCosetCount_sub_volume_isBigO`) applied to the ideal lattice
`idealLattice K I` in the mixed space.
-/

namespace NK.NUV2.RouteB.Dict

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory NumberField.mixedEmbedding
open scoped Classical Pointwise ENNReal nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- The open cone cut out by the half-spaces `f i a < 0` is invariant under scaling by a
positive real number. -/
lemma smul_halfspaceSet_eq (ι : Type) (f : ι → mixedSpace K →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c) :
    c • {a : mixedSpace K | ∀ i, f i a < 0} = {a : mixedSpace K | ∀ i, f i a < 0} := by
  ext a
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne']
  constructor
  · intro h i
    have hi := h i
    rw [map_smul, smul_eq_mul] at hi
    have h1 : c⁻¹ * f i a < c⁻¹ * 0 := by rwa [mul_zero]
    exact lt_of_mul_lt_mul_left h1 (le_of_lt (inv_pos.mpr hc))
  · intro h i
    rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hc) (h i)

/-- The dilate of `normLeOne K` by `T ^ (1 / [K : ℚ])` is the trace of the fundamental cone by
the norm ball of radius `T`. -/
lemma smul_normLeOne_eq_dict (T : ℝ) (hT : 0 < T) :
    (T ^ ((Module.finrank ℚ K : ℝ)⁻¹)) • fundamentalCone.normLeOne K
      = fundamentalCone K ∩ {x : mixedSpace K | mixedEmbedding.norm x ≤ T} := by
  have hc : (0 : ℝ) < T ^ ((Module.finrank ℚ K : ℝ)⁻¹) := Real.rpow_pos_of_pos hT _
  have hcN : (T ^ ((Module.finrank ℚ K : ℝ)⁻¹)) ^ Module.finrank ℚ K = T :=
    Real.rpow_inv_natCast_pow hT.le Module.finrank_pos.ne'
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', fundamentalCone.mem_normLeOne,
    fundamentalCone.smul_mem_iff_mem (inv_ne_zero hc.ne')]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [mixedEmbedding.norm_smul, abs_inv, abs_of_pos hc, inv_pow, hcN] at h2
    rwa [inv_mul_le_iff₀ hT, mul_one] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [mixedEmbedding.norm_smul, abs_inv, abs_of_pos hc, inv_pow, hcN, inv_mul_le_iff₀ hT,
      mul_one]
    exact h2

/-- The dilate of `normLeOne K ∩ {a | ∀ i, f i a < 0}` by `T ^ (1 / [K : ℚ])` is the trace of
the fundamental cone by the norm ball of radius `T`, cut out by the same half-spaces. -/
lemma smul_normLeOne_inter_halfspaces_eq_dict
    (ι : Type) [Fintype ι] (f : ι → mixedSpace K →L[ℝ] ℝ) (T : ℝ) (hT : 0 < T) :
    (T ^ ((Module.finrank ℚ K : ℝ)⁻¹)) •
        (fundamentalCone.normLeOne K ∩ {a : mixedSpace K | ∀ i, f i a < 0})
      = fundamentalCone K ∩ {a : mixedSpace K | ∀ i, f i a < 0} ∩
        {a : mixedSpace K | mixedEmbedding.norm a ≤ T} := by
  have hc : (0 : ℝ) < T ^ ((Module.finrank ℚ K : ℝ)⁻¹) := Real.rpow_pos_of_pos hT _
  rw [Set.smul_set_inter₀ hc.ne', smul_normLeOne_eq_dict T hT, smul_halfspaceSet_eq ι f hc]
  ext a
  simp only [Set.mem_inter_iff]
  tauto

/-- The points of the coset `x₀ + I` of the ideal lattice lying in the fundamental cone, in the
half-spaces `f i a < 0`, with norm `≤ X` are in bijection with the lattice points of `I` in the
dilated region `X^{1/n} • (normLeOne K ∩ {a | ∀ i, f i a < 0})` (by `a ↦ a - x₀`). -/
lemma natCard_halfspaces_coset_eq_dict
    (I : (FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K)ˣ) (x₀ : mixedSpace K)
    (ι : Type) [Fintype ι] (f : ι → mixedSpace K →L[ℝ] ℝ) {X : ℝ} (hX : 1 ≤ X) :
    Nat.card {a : mixedSpace K //
        a - x₀ ∈ (idealLattice K I : Set (mixedSpace K)) ∧
        a ∈ fundamentalCone K ∧ (∀ i : ι, f i a < 0) ∧ mixedEmbedding.norm a ≤ X}
      = Nat.card {x : idealLattice K I // x₀ + (x : mixedSpace K) ∈
          (X ^ ((Module.finrank ℝ (mixedSpace K) : ℝ)⁻¹)) •
            (fundamentalCone.normLeOne K ∩ {a : mixedSpace K | ∀ i, f i a < 0})} := by
  have hS : (X ^ ((Module.finrank ℝ (mixedSpace K) : ℝ)⁻¹)) •
        (fundamentalCone.normLeOne K ∩ {a : mixedSpace K | ∀ i, f i a < 0})
      = fundamentalCone K ∩ {a : mixedSpace K | ∀ i, f i a < 0} ∩
        {a : mixedSpace K | mixedEmbedding.norm a ≤ X} := by
    rw [NumberField.mixedEmbedding.finrank]
    exact smul_normLeOne_inter_halfspaces_eq_dict ι f X (lt_of_lt_of_le one_pos hX)
  have hmem : ∀ a : mixedSpace K,
      (a ∈ (X ^ ((Module.finrank ℝ (mixedSpace K) : ℝ)⁻¹)) •
          (fundamentalCone.normLeOne K ∩ {a : mixedSpace K | ∀ i, f i a < 0}))
      ↔ (a ∈ fundamentalCone K ∧ (∀ i : ι, f i a < 0) ∧ mixedEmbedding.norm a ≤ X) := by
    intro a
    rw [hS]
    exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
  have key : Nat.card {a : mixedSpace K //
        a - x₀ ∈ (idealLattice K I : Set (mixedSpace K)) ∧
        a ∈ fundamentalCone K ∧ (∀ i : ι, f i a < 0) ∧ mixedEmbedding.norm a ≤ X}
      = Nat.card {a : mixedSpace K //
        a - x₀ ∈ (idealLattice K I : Set (mixedSpace K)) ∧
        a ∈ (X ^ ((Module.finrank ℝ (mixedSpace K) : ℝ)⁻¹)) •
          (fundamentalCone.normLeOne K ∩ {a : mixedSpace K | ∀ i, f i a < 0})} := by
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

theorem latticeCosetCount_halfspaces_isBigO
    (K : Type) [Field K] [NumberField K]
    (I : (FractionalIdeal (nonZeroDivisors (RingOfIntegers K)) K)ˣ)
    (x₀ : mixedSpace K)
    (ι : Type) [Fintype ι] (f : ι → mixedSpace K →L[ℝ] ℝ) :
    ∃ (C θ : ℝ), 0 < C ∧ θ < 1 ∧ ∀ X : ℝ, 1 ≤ X →
      |((Nat.card {a : mixedSpace K //
          a - x₀ ∈ (idealLattice K I : Set (mixedSpace K)) ∧
          a ∈ fundamentalCone K ∧
          (∀ i : ι, f i a < 0) ∧
          mixedEmbedding.norm a ≤ X}) : ℝ)
        - X * (volume (fundamentalCone.normLeOne K ∩ {a : mixedSpace K | ∀ i, f i a < 0})).toReal
            / ZLattice.covolume (idealLattice K I)|
      ≤ C * X ^ θ := by
  classical
  have hPmeas : MeasurableSet
      (fundamentalCone.normLeOne K ∩ {a : mixedSpace K | ∀ i : ι, f i a < 0}) := by
    refine (fundamentalCone.measurableSet_normLeOne K).inter ?_
    have hEq : {a : mixedSpace K | ∀ i : ι, f i a < 0}
        = ⋂ i : ι, {a : mixedSpace K | f i a < (0:ℝ)} := by
      ext a; simp
    rw [hEq]
    exact MeasurableSet.iInter (fun i => measurableSet_Iio.preimage (f i).continuous.measurable)
  have hPbdd : Bornology.IsBounded
      (fundamentalCone.normLeOne K ∩ {a : mixedSpace K | ∀ i : ι, f i a < 0}) :=
    (fundamentalCone.isBounded_normLeOne K).subset Set.inter_subset_left
  have hbd : ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      volume (Metric.cthickening ε
        (frontier (fundamentalCone.normLeOne K ∩ {a : mixedSpace K | ∀ i : ι, f i a < 0})))
        ≤ ENNReal.ofReal (c * ε) :=
    NK.NUV2.Geom.volume_cthickening_frontier_normLeOne_inter_halfspaces K ι f
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    NK.NUV2.Geom.latticeCosetCount_sub_volume_isBigO (mixedSpace K) (idealLattice K I)
      (fundamentalCone.normLeOne K ∩ {a : mixedSpace K | ∀ i : ι, f i a < 0})
      hPbdd hPmeas hbd x₀
  refine ⟨C₁, 1 - (Module.finrank ℝ (mixedSpace K) : ℝ)⁻¹, hC₁pos, ?_, ?_⟩
  · have hfr : (0 : ℝ) < (Module.finrank ℝ (mixedSpace K) : ℝ) := by
      rw [NumberField.mixedEmbedding.finrank]
      exact_mod_cast Module.finrank_pos
    have := inv_pos.mpr hfr
    linarith
  · intro X hX
    rw [natCard_halfspaces_coset_eq_dict I x₀ ι f hX]
    exact hC₁ X hX

end NK.NUV2.RouteB.Dict
