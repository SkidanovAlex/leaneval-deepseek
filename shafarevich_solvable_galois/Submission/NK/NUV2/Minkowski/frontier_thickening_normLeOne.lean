import Mathlib
import Submission.NK.NUV2.Minkowski.frontier_thickening_expMapBasis_paramSet
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.NUV2.Minkowski

open scoped Classical Pointwise
open MeasureTheory NumberField
open NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone
open NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]

/-- `normAtAllPlaces` does not increase distances. -/
theorem norm_normAtAllPlaces_sub_le (x y : mixedSpace K) :
    ‖normAtAllPlaces x - normAtAllPlaces y‖ ≤ ‖x - y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun w => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  have hle (a b : mixedSpace K) :
      normAtPlace w a ≤ normAtPlace w (a - b) + normAtPlace w b := by
    have h := normAtPlace_add_le w (a - b) b
    rwa [sub_add_cancel] at h
  have h1 : normAtPlace w x ≤ normAtPlace w (x - y) + normAtPlace w y := hle x y
  have h2 : normAtPlace w y ≤ normAtPlace w (x - y) + normAtPlace w x := by
    have h := hle y x
    rw [show y - x = -(x - y) by abel, normAtPlace_neg] at h
    exact h
  have h3 : normAtPlace w (x - y) ≤ ‖x - y‖ := by
    rw [norm_eq_sup'_normAtPlace]
    exact Finset.le_sup' (f := fun w => normAtPlace w (x - y)) (Finset.mem_univ w)
  rw [abs_le]
  constructor <;> linarith

/-- `frontier` is compatible with preimages under continuous maps. -/
theorem frontier_preimage_subset_of_continuous {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) (s : Set Y) :
    frontier (f ⁻¹' s) ⊆ f ⁻¹' frontier s := by
  intro x hx
  rw [frontier_eq_closure_inter_closure] at hx
  rw [Set.mem_preimage, frontier_eq_closure_inter_closure]
  refine ⟨?_, ?_⟩
  · have h1 : f x ∈ f '' closure (f ⁻¹' s) := Set.mem_image_of_mem f hx.1
    exact closure_mono (Set.image_preimage_subset f s)
      (image_closure_subset_closure_image hf h1)
  · have h2 : x ∈ closure (f ⁻¹' sᶜ) := hx.2
    have h3 : f x ∈ f '' closure (f ⁻¹' sᶜ) := Set.mem_image_of_mem f h2
    exact closure_mono (Set.image_preimage_subset f sᶜ)
      (image_closure_subset_closure_image hf h3)

/-- The image under `normAtAllPlaces` of the frontier of `normLeOne K` is contained in the
frontier of `expMapBasis '' paramSet K`. -/
theorem normAtAllPlaces_image_frontier_normLeOne_subset :
    normAtAllPlaces '' frontier (normLeOne K) ⊆ frontier (expMapBasis '' paramSet K) := by
  rw [normLeOne_eq_preimage, Set.image_subset_iff]
  exact frontier_preimage_subset_of_continuous (continuous_normAtAllPlaces K) _

/-- The `ε`-neighbourhood of the frontier of `normLeOne K` is contained in the preimage under
`normAtAllPlaces` of the `ε`-neighbourhood of the frontier of `expMapBasis '' paramSet K`. -/
theorem frontier_thick_subset_preimage (ε : ℝ) :
    {x : mixedSpace K | ∃ p ∈ frontier (normLeOne K), ‖x - p‖ ≤ ε} ⊆
      normAtAllPlaces ⁻¹' {y : realSpace K |
        ∃ q ∈ frontier (expMapBasis '' paramSet K), ‖y - q‖ ≤ ε} := by
  rintro x ⟨p, hp, hpx⟩
  exact ⟨normAtAllPlaces p,
    ⟨normAtAllPlaces_image_frontier_normLeOne_subset (Set.mem_image_of_mem _ hp),
      le_trans (norm_normAtAllPlaces_sub_le x p) hpx⟩⟩


/-- The frontier of `expMapBasis '' paramSet K` is bounded (it lies in the compact set
`compactSet K`). -/
theorem frontier_expMapBasis_paramSet_subset_compactSet :
    frontier (expMapBasis '' paramSet K) ⊆ compactSet K :=
  (frontier_subset_closure).trans
    ((isCompact_compactSet K).isClosed.closure_subset_iff.mpr
      ((Set.image_mono subset_closure).trans (expMapBasis_closure_subset_compactSet K)))

open ENNReal in
/-- **Reduction of the Minkowski estimate in the mixed space to the real space.** If the
`ε`-neighbourhood of the frontier of `expMapBasis '' paramSet K` in `realSpace K` has volume
`O(ε)`, then so does the `ε`-neighbourhood of the frontier of `normLeOne K` in `mixedSpace K`.

The link is the folding formula `volume_eq_two_pow_mul_two_pi_pow_mul_integral`: the
`ε`-neighbourhood in the mixed space is contained in a set which is invariant under replacing
every coordinate by its norm, and `normAtAllPlaces` is `1`-Lipschitz. -/
theorem frontier_thickening_normLeOne_of_realSpace
    (h : ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (volume {y : realSpace K | ∃ q ∈ frontier (expMapBasis '' paramSet K), ‖y - q‖ ≤ ε}).toReal
        ≤ C * ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (volume {x : mixedSpace K | ∃ p ∈ frontier (normLeOne K), ‖x - p‖ ≤ ε}).toReal
        ≤ C * ε := by
  classical
  obtain ⟨C₁, hC₁pos, hC₁⟩ := h
  obtain ⟨R₀, hR₀⟩ :=
    ((isCompact_compactSet K).isBounded.subset
      (frontier_expMapBasis_paramSet_subset_compactSet (K := K))).exists_norm_le
  have hRB : ∀ q ∈ frontier (expMapBasis '' paramSet K), ‖q‖ ≤ max R₀ 1 :=
    fun q hq => (hR₀ q hq).trans (le_max_left _ _)
  have hcard : Fintype.card { w : InfinitePlace K // IsComplex w } = nrComplexPlaces K := rfl
  refine ⟨(2 : ℝ) ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K *
    (max R₀ 1 + 1) ^ nrComplexPlaces K * C₁, by positivity, fun ε hε hε1 => ?_⟩
  have hcth : ∀ y : realSpace K,
      y ∈ Metric.cthickening ε (frontier (expMapBasis '' paramSet K)) ↔
        ∃ q ∈ frontier (expMapBasis '' paramSet K), ‖y - q‖ ≤ ε := by
    intro y
    rw [Metric.cthickening_eq_biUnion_closedBall _ hε.le, isClosed_frontier.closure_eq]
    constructor
    · intro hy
      obtain ⟨q, hq, hqy⟩ := Set.mem_iUnion₂.mp hy
      exact ⟨q, hq, by simpa [dist_eq_norm] using Metric.mem_closedBall.mp hqy⟩
    · rintro ⟨q, hq, hqy⟩
      exact Set.mem_iUnion₂.mpr ⟨q, hq,
        Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hqy)⟩
  have hVne : volume (Metric.cthickening ε (frontier (expMapBasis '' paramSet K))) ≠ ⊤ := by
    have hsub : Metric.cthickening ε (frontier (expMapBasis '' paramSet K)) ⊆
        Metric.closedBall 0 (max R₀ 1 + ε) := by
      intro y hy
      obtain ⟨q, hq, hqy⟩ := (hcth y).mp hy
      refine Metric.mem_closedBall.mpr ?_
      calc dist y 0 = ‖y‖ := by rw [dist_eq_norm, sub_zero]
        _ = ‖q + (y - q)‖ := by rw [add_sub_cancel]
        _ ≤ ‖q‖ + ‖y - q‖ := norm_add_le _ _
        _ ≤ max R₀ 1 + ε := add_le_add (hRB q hq) hqy
    refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
    rw [(volume : Measure (realSpace K)).addHaar_closedBall (0 : realSpace K)
      (by positivity : (0 : ℝ) ≤ max R₀ 1 + ε)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt measure_ball_lt_top)
  -- the `ε`-neighbourhood is contained in a norm-stable set
  have hAB : {x : mixedSpace K | ∃ p ∈ frontier (normLeOne K), ‖x - p‖ ≤ ε} ⊆
      normAtAllPlaces ⁻¹' Metric.cthickening ε (frontier (expMapBasis '' paramSet K)) := by
    intro x hx
    have h1 := frontier_thick_subset_preimage (K := K) ε hx
    rw [Set.mem_preimage] at h1 ⊢
    exact (hcth (normAtAllPlaces x)).mpr h1
  have hstab : normAtAllPlaces ⁻¹' normAtAllPlaces ''
      (normAtAllPlaces ⁻¹' Metric.cthickening ε (frontier (expMapBasis '' paramSet K))) =
      normAtAllPlaces ⁻¹' Metric.cthickening ε (frontier (expMapBasis '' paramSet K)) := by
    refine Set.eq_of_subset_of_subset ?_ (Set.subset_preimage_image _ _)
    rintro x ⟨y, hy, hxy⟩
    rw [Set.mem_preimage] at hy ⊢
    rw [← hxy]
    exact hy
  have hmA' : MeasurableSet (normAtAllPlaces ⁻¹'
      Metric.cthickening ε (frontier (expMapBasis '' paramSet K))) :=
    Metric.isClosed_cthickening.measurableSet.preimage (continuous_normAtAllPlaces K).measurable
  have hfold := volume_eq_two_pow_mul_two_pi_pow_mul_integral (K := K) hstab hmA'
  -- bound the weight on the image
  have hweight : ∀ y ∈ normAtAllPlaces '' (normAtAllPlaces ⁻¹'
      Metric.cthickening ε (frontier (expMapBasis '' paramSet K))),
      ∏ w : { w : InfinitePlace K // IsComplex w }, ENNReal.ofReal (y ↑w)
        ≤ ENNReal.ofReal ((max R₀ 1 + 1) ^ nrComplexPlaces K) := by
    intro y hy
    have hyb : ∀ w : InfinitePlace K, y w ≤ max R₀ 1 + 1 := by
      intro w
      obtain ⟨q, hq, hqy⟩ := (hcth y).mp (Set.image_preimage_subset _ _ hy)
      have h1 : ‖y‖ ≤ max R₀ 1 + 1 := by
        calc ‖y‖ = ‖q + (y - q)‖ := by rw [add_sub_cancel]
          _ ≤ ‖q‖ + ‖y - q‖ := norm_add_le _ _
          _ ≤ max R₀ 1 + ε := add_le_add (hRB q hq) hqy
          _ ≤ max R₀ 1 + 1 := by linarith
      exact le_trans (le_trans (le_abs_self _) (norm_le_pi_norm y w)) h1
    calc ∏ w : { w : InfinitePlace K // IsComplex w }, ENNReal.ofReal (y ↑w)
        ≤ ∏ _w : { w : InfinitePlace K // IsComplex w },
            ENNReal.ofReal (max R₀ 1 + 1) :=
          Finset.prod_le_prod₀ (fun i _ => bot_le) (fun i _ => ENNReal.ofReal_le_ofReal (hyb i))
      _ = (ENNReal.ofReal (max R₀ 1 + 1)) ^ nrComplexPlaces K := by
          rw [Finset.prod_const, Finset.card_univ, hcard]
      _ = ENNReal.ofReal ((max R₀ 1 + 1) ^ nrComplexPlaces K) :=
          (ENNReal.ofReal_pow (by positivity) _).symm
  have hint : ∫⁻ (y : realSpace K) in normAtAllPlaces '' (normAtAllPlaces ⁻¹'
        Metric.cthickening ε (frontier (expMapBasis '' paramSet K))),
        ∏ w : { w : InfinitePlace K // IsComplex w }, ENNReal.ofReal (y ↑w)
      ≤ ENNReal.ofReal ((max R₀ 1 + 1) ^ nrComplexPlaces K) *
          volume (Metric.cthickening ε (frontier (expMapBasis '' paramSet K))) := by
    have h1 : ∫⁻ (y : realSpace K) in normAtAllPlaces '' (normAtAllPlaces ⁻¹'
          Metric.cthickening ε (frontier (expMapBasis '' paramSet K))),
          ∏ w : { w : InfinitePlace K // IsComplex w }, ENNReal.ofReal (y ↑w)
        ≤ ∫⁻ (y : realSpace K) in normAtAllPlaces '' (normAtAllPlaces ⁻¹'
          Metric.cthickening ε (frontier (expMapBasis '' paramSet K))),
          ENNReal.ofReal ((max R₀ 1 + 1) ^ nrComplexPlaces K) :=
      setLIntegral_mono (g := fun _ : realSpace K =>
        ENNReal.ofReal ((max R₀ 1 + 1) ^ nrComplexPlaces K)) measurable_const hweight
    refine h1.trans ?_
    rw [setLIntegral_const]
    exact mul_le_mul_right (measure_mono (Set.image_preimage_subset _ _)) _
  -- putting everything together
  have hC₁' : (volume (Metric.cthickening ε (frontier (expMapBasis '' paramSet K)))).toReal
      ≤ C₁ * ε := by
    rw [show Metric.cthickening ε (frontier (expMapBasis '' paramSet K)) =
        {y : realSpace K | ∃ q ∈ frontier (expMapBasis '' paramSet K), ‖y - q‖ ≤ ε} from
      Set.ext fun y => hcth y]
    exact hC₁ ε hε hε1
  have hvol : volume {x : mixedSpace K | ∃ p ∈ frontier (normLeOne K), ‖x - p‖ ≤ ε} ≤
      ENNReal.ofReal ((2 : ℝ) ^ nrRealPlaces K) *
        (ENNReal.ofReal ((2 * Real.pi) ^ nrComplexPlaces K) *
          (ENNReal.ofReal ((max R₀ 1 + 1) ^ nrComplexPlaces K) *
            volume (Metric.cthickening ε (frontier (expMapBasis '' paramSet K))))) := by
    have h2 : (2 : ℝ≥0∞) ^ nrRealPlaces K =
        ENNReal.ofReal ((2 : ℝ) ^ nrRealPlaces K) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    have h3 : ENNReal.ofReal (2 * Real.pi) ^ nrComplexPlaces K =
        ENNReal.ofReal ((2 * Real.pi) ^ nrComplexPlaces K) :=
      (ENNReal.ofReal_pow (by positivity) _).symm
    calc volume {x : mixedSpace K | ∃ p ∈ frontier (normLeOne K), ‖x - p‖ ≤ ε}
        ≤ volume (normAtAllPlaces ⁻¹'
            Metric.cthickening ε (frontier (expMapBasis '' paramSet K))) := measure_mono hAB
      _ = 2 ^ nrRealPlaces K * ENNReal.ofReal (2 * Real.pi) ^ nrComplexPlaces K *
            ∫⁻ (y : realSpace K) in normAtAllPlaces '' (normAtAllPlaces ⁻¹'
              Metric.cthickening ε (frontier (expMapBasis '' paramSet K))),
              ∏ w : { w : InfinitePlace K // IsComplex w }, ENNReal.ofReal (y ↑w) := hfold
      _ ≤ 2 ^ nrRealPlaces K * ENNReal.ofReal (2 * Real.pi) ^ nrComplexPlaces K *
            (ENNReal.ofReal ((max R₀ 1 + 1) ^ nrComplexPlaces K) *
              volume (Metric.cthickening ε (frontier (expMapBasis '' paramSet K)))) :=
          mul_le_mul_right hint _
      _ = ENNReal.ofReal ((2 : ℝ) ^ nrRealPlaces K) *
            (ENNReal.ofReal ((2 * Real.pi) ^ nrComplexPlaces K) *
              (ENNReal.ofReal ((max R₀ 1 + 1) ^ nrComplexPlaces K) *
                volume (Metric.cthickening ε (frontier (expMapBasis '' paramSet K))))) := by
          rw [h2, h3, mul_assoc]
  calc (volume {x : mixedSpace K | ∃ p ∈ frontier (normLeOne K), ‖x - p‖ ≤ ε}).toReal
      ≤ (ENNReal.ofReal ((2 : ℝ) ^ nrRealPlaces K) *
          (ENNReal.ofReal ((2 * Real.pi) ^ nrComplexPlaces K) *
            (ENNReal.ofReal ((max R₀ 1 + 1) ^ nrComplexPlaces K) *
              volume (Metric.cthickening ε (frontier (expMapBasis '' paramSet K)))))).toReal :=
        ENNReal.toReal_mono
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVne))) hvol
    _ = (2 : ℝ) ^ nrRealPlaces K * ((2 * Real.pi) ^ nrComplexPlaces K *
          ((max R₀ 1 + 1) ^ nrComplexPlaces K *
            (volume (Metric.cthickening ε (frontier (expMapBasis '' paramSet K)))).toReal)) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
          ENNReal.toReal_ofReal (by positivity)]
    _ ≤ (2 : ℝ) ^ nrRealPlaces K * ((2 * Real.pi) ^ nrComplexPlaces K *
          ((max R₀ 1 + 1) ^ nrComplexPlaces K * (C₁ * ε))) := by
        gcongr
    _ = ((2 : ℝ) ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K *
          (max R₀ 1 + 1) ^ nrComplexPlaces K * C₁) * ε := by ring

/-- **Minkowski content of the frontier of `normLeOne K`.** The `ε`-neighbourhood of the frontier
of the fundamental cone with norm `≤ 1` has volume `≤ C · ε` for `0 < ε ≤ 1`.

Useful Mathlib facts: `normLeOne K = fundamentalCone K ∩ {norm ≤ 1}`,
`normLeOne_eq_preimage : normLeOne K = normAtAllPlaces ⁻¹' (expMapBasis '' paramSet K)`,
`normAtAllPlaces_normLeOne_eq_image`, `isBounded_normLeOne`, `volume_frontier_normLeOne`,
`expMapBasis_apply'`, `abs_det_fderiv_expMapBasis`,
`volume_eq_two_pow_mul_two_pi_pow_mul_integral` (folding formula for `normAtAllPlaces`),
and `volume_thickening_box_image_le` in
`Submission/Work/NUV2/Minkowski/volume_thickening_box_image_le.lean` (a Lipschitz image of a
`k`-dimensional box has `ε`-neighbourhood volume `O(ε^(dim - k))`,
so `O(ε)` for `k = dim - 1`). -/
theorem frontier_thickening_normLeOne (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (volume {x : mixedSpace K | ∃ p ∈ frontier (normLeOne K), ‖x - p‖ ≤ ε}).toReal
        ≤ C * ε :=
  frontier_thickening_normLeOne_of_realSpace (frontier_thickening_expMapBasis_paramSet K)

end NK.NUV2.Minkowski
