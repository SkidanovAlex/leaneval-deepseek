import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Separation.CompletelyRegular

namespace Commons.Measure.EuclideanSpace

open MeasureTheory Metric Set
open scoped ENNReal BigOperators Pointwise
open Classical

/-- The unit cube `[0,1]^d` in `ℝ^d`. -/
def unitCube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

theorem unitCube_closed (d : ℕ) : IsClosed (unitCube d) := by
  have h : unitCube d = (fun x : EuclideanSpace ℝ (Fin d) => x.ofLp) ⁻¹'
      Set.pi Set.univ (fun _ : Fin d => Icc (0:ℝ) 1) := by
    ext x
    simp only [unitCube, mem_setOf_eq, mem_preimage, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Icc]
  rw [h]
  exact (isClosed_set_pi (fun i _ => isClosed_Icc)).preimage (by fun_prop)

theorem unitCube_norm_sub_le (d : ℕ) {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ unitCube d) (hy : y ∈ unitCube d) : ‖x - y‖ ≤ Real.sqrt d := by
  have h1 : ‖x - y‖ ^ 2 ≤ (d : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ i : Fin d, (x - y).ofLp i ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          have hxi := hx i
          have hyi := hy i
          have hxy : (x - y).ofLp i = x i - y i := by simp
          rw [hxy]
          nlinarith [hxi.1, hxi.2, hyi.1, hyi.2]
      _ = (d : ℝ) := by simp
  calc ‖x - y‖ = Real.sqrt (‖x - y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt d := Real.sqrt_le_sqrt h1

theorem unitCube_zero_mem (d : ℕ) : (0 : EuclideanSpace ℝ (Fin d)) ∈ unitCube d := by
  intro i; simpa using zero_le_one' ℝ

theorem volume_unitCube_lt_top (d : ℕ) : (volume : Measure (EuclideanSpace ℝ (Fin d))) (unitCube d) ≠ ⊤ := by
  have hsub : unitCube d ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) (Real.sqrt d) := by
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    have := unitCube_norm_sub_le d hx (unitCube_zero_mem d)
    rwa [sub_zero] at this
  refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
  exact measure_closedBall_lt_top.ne

/-! ## Polar coordinates -/

theorem lintegral_polar (d : ℕ) [NeZero d] (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ x, g x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) =
      ∫⁻ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        ∫⁻ r : Ioi (0:ℝ), g (r.1 • (θ : EuclideanSpace ℝ (Fin d)))
          ∂(Measure.volumeIoiPow (d - 1))
        ∂(Measure.toSphere (volume : Measure (EuclideanSpace ℝ (Fin d)))) := by
  have hmp := Measure.measurePreserving_homeomorphUnitSphereProd
    (volume : Measure (EuclideanSpace ℝ (Fin d)))
  rw [finrank_euclideanSpace_fin] at hmp
  have h1 : ∫⁻ x, g x ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))
      = ∫⁻ a : ↥({0}ᶜ : Set (EuclideanSpace ℝ (Fin d))), g ↑a
          ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).comap Subtype.val) := by
    conv_lhs => rw [← restrict_compl_singleton (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (0 : _)]
    exact (lintegral_subtype_comap (measurableSet_singleton (0:_)).compl g).symm
  rw [h1]
  have h2 : ∫⁻ a : ↥({0}ᶜ : Set (EuclideanSpace ℝ (Fin d))), g ↑a
        ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).comap Subtype.val)
      = ∫⁻ p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × Ioi (0:ℝ),
          g ↑((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin d))).symm p)
        ∂((Measure.toSphere (volume : Measure (EuclideanSpace ℝ (Fin d)))).prod
          (Measure.volumeIoiPow (d - 1))) := by
    rw [← hmp.map_eq,
      (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin d))).measurableEmbedding.lintegral_map
        (fun p : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 × Ioi (0:ℝ) =>
          g ↑((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin d))).symm p))]
    apply lintegral_congr; intro a
    simp
  rw [h2]
  rw [lintegral_prod]
  · apply lintegral_congr; intro θ
    apply lintegral_congr; intro r
    simp [homeomorphUnitSphereProd_symm_apply_coe]
  · exact (hg.comp (measurable_subtype_coe.comp
      (homeomorphUnitSphereProd _).symm.measurable)).aemeasurable

theorem lintegral_volumeIoiPow (n : ℕ) (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ r : ↥(Ioi (0:ℝ)), H r ∂(Measure.volumeIoiPow n)
      = ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r ^ n) * H r ∂(volume : Measure ℝ) := by
  have h1 : ∫⁻ r : ↥(Ioi (0:ℝ)), H r ∂(Measure.volumeIoiPow n)
      = ∫⁻ r : ↥(Ioi (0:ℝ)), ENNReal.ofReal (r.1 ^ n) * H ↑r
          ∂((volume : Measure ℝ).comap Subtype.val) := by
    rw [Measure.volumeIoiPow]
    exact lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (hH.comp measurable_subtype_coe)
  rw [h1]
  exact lintegral_subtype_comap measurableSet_Ioi (fun r : ℝ => ENNReal.ofReal (r ^ n) * H r)

theorem lintegral_polar_density (d : ℕ) [NeZero d] (g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ x, g x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) =
      ∫⁻ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
        ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r ^ (d - 1)) * g (r • (θ : EuclideanSpace ℝ (Fin d)))
          ∂(volume : Measure ℝ)
        ∂(Measure.toSphere (volume : Measure (EuclideanSpace ℝ (Fin d)))) := by
  rw [lintegral_polar d g hg]
  apply lintegral_congr; intro θ
  exact lintegral_volumeIoiPow (d-1) (fun r : ℝ => g (r • (θ : EuclideanSpace ℝ (Fin d))))
    (hg.comp (by fun_prop))

/-- Arithmetic lemma for ENNReal. -/
theorem ennreal_arith {VE C s : ℝ≥0∞} (hC0 : C ≠ 0) (hC : C ≠ ⊤) (hs0 : s ≠ 0) (hs : s ≠ ⊤)
    (hV : VE ≠ ⊤) : (C * (VE / (2 * C * s))) * s = VE / 2 := by
  have h2Cs0 : (2:ℝ≥0∞) * C * s ≠ 0 := by simp [hC0, hs0]
  have htop1 : (C * (VE / (2 * C * s))) * s ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hC (ENNReal.div_ne_top hV h2Cs0)) hs
  have htop2 : VE / 2 ≠ ⊤ := ENNReal.div_ne_top hV (by norm_num)
  have hC0' : C.toReal ≠ 0 := fun h => hC0 (ENNReal.toReal_eq_zero_iff C |>.mp h |>.resolve_right hC)
  have hs0' : s.toReal ≠ 0 := fun h => hs0 (ENNReal.toReal_eq_zero_iff s |>.mp h |>.resolve_right hs)
  apply (ENNReal.toReal_eq_toReal_iff' htop1 htop2).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat]
  field_simp

/-- **Directional pigeonhole (extraction form).**  There is a direction `θ` on the unit sphere
such that the radial measure of `E` along the ray `y + ℝ≥0 • θ` is at least
`|E| / (2 √d ^ (d-1) * |S^{d-1}|)`. -/
theorem exists_direction_lower_bound (d : ℕ) [NeZero d] (E : Set (EuclideanSpace ℝ (Fin d)))
    (y : EuclideanSpace ℝ (Fin d)) (hyQ : y ∈ unitCube d) (hE : MeasurableSet E)
    (hEQ : E ⊆ unitCube d) (hvol : 0 < (volume E).toReal) :
    ∃ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      (volume E) / (2 * ENNReal.ofReal ((Real.sqrt d) ^ (d - 1)) *
          (Measure.toSphere (volume : Measure (EuclideanSpace ℝ (Fin d))) Set.univ))
        ≤ ∫⁻ r in Ioi (0:ℝ), (if y + r • (θ : EuclideanSpace ℝ (Fin d)) ∈ E then 1 else 0) := by
  classical
  set σ : Measure (sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    Measure.toSphere (volume : Measure (EuclideanSpace ℝ (Fin d))) with hσdef
  set C : ℝ≥0∞ := ENNReal.ofReal ((Real.sqrt d) ^ (d - 1)) with hCdef
  set A : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 → ℝ≥0∞ :=
    fun θ => ∫⁻ r in Ioi (0:ℝ), (if y + r • (θ : EuclideanSpace ℝ (Fin d)) ∈ E then 1 else 0)
    with hAdef
  have hsd : (1 : ℝ) ≤ Real.sqrt d := by
    rw [Real.one_le_sqrt]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hC0 : C ≠ 0 := by
    rw [hCdef]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (lt_of_lt_of_le one_pos hsd) _)).ne'
  have hCtop : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hσfin : σ Set.univ ≠ ⊤ := (IsFiniteMeasure.measure_univ_lt_top (μ := σ)).ne
  have hσne : σ Set.univ ≠ 0 := by
    intro h
    have h' : σ = 0 := Measure.measure_univ_eq_zero.mp h
    rw [hσdef] at h'
    exact Measure.toSphere_ne_zero (volume : Measure (EuclideanSpace ℝ (Fin d))) h'
  have hVtop : volume E ≠ ⊤ := ne_top_of_le_ne_top (volume_unitCube_lt_top d) (measure_mono hEQ)
  have hV0 : volume E ≠ 0 := by
    intro h; rw [h] at hvol; simp at hvol
  have hSmeas : MeasurableSet ((fun z : EuclideanSpace ℝ (Fin d) => y + z) ⁻¹' E) :=
    hE.preimage (by fun_prop)
  have hgmeas : Measurable
      (fun z : EuclideanSpace ℝ (Fin d) => (if y + z ∈ E then (1:ℝ≥0∞) else 0)) :=
    Measurable.indicator measurable_const hSmeas
  have hpolar := lintegral_polar_density d
    (fun z : EuclideanSpace ℝ (Fin d) => (if y + z ∈ E then (1:ℝ≥0∞) else 0)) hgmeas
  have htrans : ∫⁻ z : EuclideanSpace ℝ (Fin d), (if y + z ∈ E then (1:ℝ≥0∞) else 0)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) = volume E := by
    have hmp := measurePreserving_add_right
      (volume : Measure (EuclideanSpace ℝ (Fin d))) y
    have h := hmp.lintegral_comp
      (f := E.indicator (1 : EuclideanSpace ℝ (Fin d) → ℝ≥0∞))
      (Measurable.indicator measurable_const hE)
    rw [lintegral_indicator_one hE] at h
    rw [← h]
    apply lintegral_congr
    intro z
    have hcomm : z + y ∈ E ↔ y + z ∈ E := by rw [add_comm]
    by_cases hz : y + z ∈ E
    · simp only [if_pos hz,
        Set.indicator_of_mem (f := (1 : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)) (hcomm.mpr hz),
        Pi.one_apply]
    · simp only [if_neg hz,
        Set.indicator_of_notMem (f := (1 : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)) (fun h => hz (hcomm.mp h))]
  have hpol : volume E = ∫⁻ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r ^ (d-1)) *
        (if y + r • (θ : EuclideanSpace ℝ (Fin d)) ∈ E then 1 else 0)) ∂σ := by
    rw [← htrans]
    exact hpolar
  have hbound : ∀ θ : sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r ^ (d-1)) *
        (if y + r • (θ : EuclideanSpace ℝ (Fin d)) ∈ E then 1 else 0)) ≤ C * A θ := by
    intro θ
    have hpt : ∀ r : ℝ, r ∈ Ioi (0:ℝ) →
        ENNReal.ofReal (r ^ (d-1)) * (if y + r • (θ : EuclideanSpace ℝ (Fin d)) ∈ E then 1 else 0)
          ≤ C * (if y + r • (θ : EuclideanSpace ℝ (Fin d)) ∈ E then 1 else 0) := by
      intro r hr
      by_cases h : y + r • (θ : EuclideanSpace ℝ (Fin d)) ∈ E
      · simp only [if_pos h, mul_one]
        rw [hCdef]
        apply ENNReal.ofReal_le_ofReal
        have hrle : r ≤ Real.sqrt d := by
          have h1 : y + r • (θ : EuclideanSpace ℝ (Fin d)) ∈ unitCube d := hEQ h
          have h2 := unitCube_norm_sub_le d h1 hyQ
          rw [add_sub_cancel_left] at h2
          rwa [norm_smul, mem_sphere_zero_iff_norm.mp θ.2, mul_one, Real.norm_eq_abs,
            abs_of_pos hr] at h2
        exact pow_le_pow_left₀ hr.le hrle _
      · simp [if_neg h]
    calc ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r ^ (d-1)) *
            (if y + r • (θ : EuclideanSpace ℝ (Fin d)) ∈ E then 1 else 0)
        ≤ ∫⁻ r in Ioi (0:ℝ), C * (if y + r • (θ : EuclideanSpace ℝ (Fin d)) ∈ E then 1 else 0) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
          exact hpt r hr
      _ = C * A θ := by
          rw [lintegral_const_mul' C _ (by rw [hCdef]; exact ENNReal.ofReal_ne_top), hAdef]
  by_contra hcon
  push_neg at hcon
  have h1 : ∫⁻ θ, A θ ∂σ ≤ (volume E / (2 * C * σ Set.univ)) * σ Set.univ := by
    calc ∫⁻ θ, A θ ∂σ ≤ ∫⁻ θ, (fun _ => volume E / (2 * C * σ Set.univ)) θ ∂σ :=
          lintegral_mono fun θ => (hcon θ).le
      _ = _ := lintegral_const _
  have h2 : volume E ≤ (C * (volume E / (2 * C * σ Set.univ))) * σ Set.univ := by
    conv_lhs => rw [hpol]
    calc ∫⁻ θ, (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r ^ (d-1)) *
            (if y + r • (θ : EuclideanSpace ℝ (Fin d)) ∈ E then 1 else 0)) ∂σ
        ≤ ∫⁻ θ, C * A θ ∂σ := lintegral_mono hbound
      _ ≤ ∫⁻ θ, (fun _ => C * (volume E / (2 * C * σ Set.univ))) θ ∂σ := by
          apply lintegral_mono; intro θ
          exact (ENNReal.mul_lt_mul_right hC0 hCtop (hcon θ)).le
      _ = _ := lintegral_const _
  rw [ennreal_arith hC0 hCtop hσne hσfin hVtop] at h2
  exact absurd h2 (not_le.mpr (ENNReal.half_lt_self hV0 hVtop))

/-- In the trivial Euclidean space, the total volume is `1`. -/
theorem volume_univ_euclidean_fin_zero :
    (volume : Measure (EuclideanSpace ℝ (Fin 0))) Set.univ = 1 := by
  have h1 : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
    rw [volume_pi, Measure.pi_univ]
    simp
  have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 0)
  rw [← hmp.map_eq] at h1
  rw [Measure.map_apply hmp.measurable MeasurableSet.univ] at h1
  simpa using h1

/-- **Directional pigeonhole.** If `E` is a measurable subset of the unit cube
`Q = [0,1]^d ⊂ ℝ^d` of positive volume and `y ∈ Q`, then there is a segment starting at `y`
staying in `Q` which meets `E` in a definite proportion of its length: there is a constant
`c > 0` (depending only on `d`) such that `(volume {t ∈ [0,1] | y + t • v ∈ E}).toReal ≥
c * (volume E).toReal` for some `v` with `y + t • v ∈ Q` for all `t ∈ [0,1]`. -/
theorem exists_segment_large_intersection (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (E : Set (EuclideanSpace ℝ (Fin d)))
      (y : EuclideanSpace ℝ (Fin d)),
      y ∈ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} →
      MeasurableSet E →
      E ⊆ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1} →
      0 < (volume E).toReal →
      ∃ v : EuclideanSpace ℝ (Fin d),
        (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
          y + t • v ∈ {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i ∧ x i ≤ 1}) ∧
        c * (volume E).toReal ≤
          (volume {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧ y + t • v ∈ E}).toReal := by

  classical
  by_cases hd0 : d = 0
  · subst hd0
    refine ⟨1/2, by norm_num, by norm_num, ?_⟩
    intro E y hyQ hE hEQ hvol
    have hEne : E.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rw [h] at hvol
      simp at hvol
    obtain ⟨z, hz⟩ := hEne
    have hyE : y ∈ E := by
      rw [Subsingleton.elim y z]
      exact hz
    refine ⟨0, ?_, ?_⟩
    · intro t ht
      simpa using hyQ
    · have hset : {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧ y + t • (0 : EuclideanSpace ℝ (Fin 0)) ∈ E}
          = Set.Icc (0:ℝ) 1 := by
        ext t
        simp [hyE]
      have hVE : (volume E).toReal ≤ 1 := by
        have h1 : (volume (Set.univ : Set (EuclideanSpace ℝ (Fin 0)))).toReal = 1 := by
          rw [volume_univ_euclidean_fin_zero, ENNReal.toReal_one]
        rw [← h1]
        exact ENNReal.toReal_mono
          (by rw [volume_univ_euclidean_fin_zero]; exact ENNReal.one_ne_top)
          (measure_mono (subset_univ E))
      rw [hset, Real.volume_Icc]
      rw [show (1:ℝ) - 0 = 1 by norm_num, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1)]
      linarith
  · haveI : NeZero d := ⟨hd0⟩
    set σ : Measure (sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
      Measure.toSphere (volume : Measure (EuclideanSpace ℝ (Fin d))) with hσdef
    set s : ℝ := (σ Set.univ).toReal with hsdef
    refine ⟨min (1/2) (1 / (1 + 2 * (Real.sqrt d) ^ d * s)), ?_, ?_, ?_⟩
    · apply lt_min (by norm_num)
      apply one_div_pos.mpr
      have h1 : (0:ℝ) ≤ (Real.sqrt d) ^ d := pow_nonneg (Real.sqrt_nonneg d) d
      have h2 : (0:ℝ) ≤ s := ENNReal.toReal_nonneg
      nlinarith [mul_nonneg h1 h2]
    · exact (min_le_left _ _).trans (by norm_num)
    · intro E y hyQ hE hEQ hvol
      obtain ⟨θ₀, hθ₀⟩ := exists_direction_lower_bound d E y hyQ hE hEQ hvol
      have hσfin : σ Set.univ ≠ ⊤ := (IsFiniteMeasure.measure_univ_lt_top (μ := σ)).ne
      have hσne : σ Set.univ ≠ 0 := by
        intro h
        have h' : σ = 0 := Measure.measure_univ_eq_zero.mp h
        rw [hσdef] at h'
        exact Measure.toSphere_ne_zero (volume : Measure (EuclideanSpace ℝ (Fin d))) h'
      have hCtop : ENNReal.ofReal ((Real.sqrt d) ^ (d - 1)) ≠ ⊤ := ENNReal.ofReal_ne_top
      have hVtop : volume E ≠ ⊤ := ne_top_of_le_ne_top (volume_unitCube_lt_top d) (measure_mono hEQ)
      have hV0 : volume E ≠ 0 := by
        intro h; rw [h] at hvol; simp at hvol
      have hsd : (1:ℝ) ≤ Real.sqrt d := by
        rw [Real.one_le_sqrt]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
      have hsqpos : 0 < Real.sqrt d := lt_of_lt_of_le one_pos hsd
      have hspos : 0 < s := by
        rw [hsdef]
        exact ENNReal.toReal_pos hσne hσfin
      -- the exit radius
      set S : Set ℝ := {t : ℝ | 0 ≤ t ∧ y + t • (θ₀ : EuclideanSpace ℝ (Fin d)) ∈ unitCube d}
        with hSdef
      have hSne : S.Nonempty := ⟨0, le_refl 0, by simpa using (show y ∈ unitCube d from hyQ)⟩
      have hSle : ∀ t ∈ S, t ≤ Real.sqrt d := by
        intro t ht
        have h2 := unitCube_norm_sub_le d ht.2 hyQ
        rw [add_sub_cancel_left] at h2
        rwa [norm_smul, mem_sphere_zero_iff_norm.mp θ₀.2, mul_one, Real.norm_eq_abs,
          abs_of_nonneg ht.1] at h2
      have hSbd : BddAbove S := ⟨_, hSle⟩
      have hScl : IsClosed S := by
        have hEq : S = Set.Ici (0:ℝ) ∩
            {t : ℝ | y + t • (θ₀ : EuclideanSpace ℝ (Fin d)) ∈ unitCube d} := by
          rw [hSdef]
          ext t
          exact Iff.rfl
        rw [hEq]
        exact IsClosed.inter isClosed_Ici ((unitCube_closed d).preimage (by fun_prop))
      set R : ℝ := sSup S with hRdef
      have hRmem : R ∈ S := by
        rw [hRdef]
        exact hScl.csSup_mem hSne hSbd
      have hR0 : 0 ≤ R := hRmem.1
      have hRd : R ≤ Real.sqrt d := by
        rw [hRdef]
        exact csSup_le hSne hSle
      have hyRQ : y + R • (θ₀ : EuclideanSpace ℝ (Fin d)) ∈ unitCube d := hRmem.2
      have hboundS : ∀ t : ℝ, 0 ≤ t → y + t • (θ₀ : EuclideanSpace ℝ (Fin d)) ∈ E → t ≤ R := by
        intro t ht0 htE
        rw [hRdef]
        exact le_csSup hSbd ⟨ht0, hEQ htE⟩
      -- the two sets
      set Spos : Set ℝ := {r : ℝ | r ∈ Ioi (0:ℝ) ∧
        y + r • (θ₀ : EuclideanSpace ℝ (Fin d)) ∈ E} with hSposdef
      set Snonneg : Set ℝ := {t : ℝ | 0 ≤ t ∧
        y + t • (θ₀ : EuclideanSpace ℝ (Fin d)) ∈ E} with hSnonnegdef
      have hSpos_meas : MeasurableSet Spos := by
        rw [hSposdef]
        exact measurableSet_Ioi.inter (hE.preimage (by fun_prop))
      have hAeq : (∫⁻ r in Ioi (0:ℝ), (if y + r • (θ₀ : EuclideanSpace ℝ (Fin d)) ∈ E
            then 1 else 0)) = volume Spos := by
        rw [← lintegral_indicator measurableSet_Ioi]
        rw [show (∫⁻ r, (Set.Ioi (0:ℝ)).indicator
              (fun r : ℝ => (if y + r • (θ₀ : EuclideanSpace ℝ (Fin d)) ∈ E then (1:ℝ≥0∞) else 0)) r
              ∂(volume : Measure ℝ))
            = ∫⁻ r, (Spos.indicator (1 : ℝ → ℝ≥0∞)) r ∂(volume : Measure ℝ) from
          lintegral_congr fun r => ?_]
        · rw [lintegral_indicator_one hSpos_meas]
        · by_cases hr : r ∈ Ioi (0:ℝ) <;>
            by_cases hE' : y + r • (θ₀ : EuclideanSpace ℝ (Fin d)) ∈ E
          · rw [Set.indicator_of_mem hr, if_pos hE',
              Set.indicator_of_mem (show r ∈ Spos from ⟨hr, hE'⟩), Pi.one_apply]
          · rw [Set.indicator_of_mem hr, if_neg hE',
              Set.indicator_of_notMem (show r ∉ Spos from fun h => hE' h.2)]
          · rw [Set.indicator_of_notMem hr,
              Set.indicator_of_notMem (show r ∉ Spos from fun h => hr h.1)]
          · rw [Set.indicator_of_notMem hr,
              Set.indicator_of_notMem (show r ∉ Spos from fun h => hr h.1)]
      have hApos : 0 < volume Spos := by
        rw [← hAeq]
        exact lt_of_lt_of_le (ENNReal.div_pos hV0
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hCtop) hσfin)) hθ₀
      have hRpos : 0 < R := by
        have hne : Spos.Nonempty := by
          by_contra h
          rw [Set.not_nonempty_iff_eq_empty] at h
          rw [h] at hApos
          simp at hApos
        obtain ⟨t, ht⟩ := hne
        exact lt_of_lt_of_le ht.1 (hboundS t ht.1.le ht.2)
      have hRne : R ≠ 0 := ne_of_gt hRpos
      refine ⟨R • (θ₀ : EuclideanSpace ℝ (Fin d)), ?_, ?_⟩
      · intro t ht
        show y + t • (R • (θ₀ : EuclideanSpace ℝ (Fin d))) ∈ unitCube d
        intro i
        have h1 := hyRQ i
        have h2 := hyQ i
        have hkey : (y + t • (R • (θ₀ : EuclideanSpace ℝ (Fin d)))) i
            = (1 - t) * (y i) + t * ((y + R • (θ₀ : EuclideanSpace ℝ (Fin d))) i) := by
          simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          ring
        rw [hkey]
        have h3 : (1 - t) * (y i) ≤ (1 - t) * 1 :=
          mul_le_mul_of_nonneg_left h2.2 (by linarith [ht.2])
        have h4 : t * ((y + R • (θ₀ : EuclideanSpace ℝ (Fin d))) i) ≤ t * 1 :=
          mul_le_mul_of_nonneg_left h1.2 ht.1
        have h5 : 0 ≤ (1 - t) * (y i) := mul_nonneg (by linarith [ht.2]) h2.1
        have h6 : 0 ≤ t * ((y + R • (θ₀ : EuclideanSpace ℝ (Fin d))) i) := mul_nonneg ht.1 h1.1
        exact ⟨by linarith, by linarith⟩
      · -- the measure estimate
        have hSnonneg_eq : Snonneg = Spos ∪ ({0} ∩ Snonneg) := by
          ext t
          constructor
          · intro ht
            rcases lt_or_eq_of_le ht.1 with h | h
            · exact Or.inl ⟨h, ht.2⟩
            · exact Or.inr ⟨h.symm, ht⟩
          · intro ht
            rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact ⟨h1.le, h2⟩
            · exact h2
        have hSnonneg_vol : volume Snonneg = volume Spos := by
          have hnull : volume ({0} ∩ Snonneg) = 0 :=
            measure_mono_null inter_subset_left (Real.volume_singleton (a := (0:ℝ)))
          rw [hSnonneg_eq]
          refine le_antisymm ?_ (measure_mono subset_union_left)
          calc volume (Spos ∪ ({0} ∩ Snonneg))
              ≤ volume Spos + volume ({0} ∩ Snonneg) := measure_union_le _ _
            _ = volume Spos := by rw [hnull, add_zero]
        have hset : {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧
              y + t • (R • (θ₀ : EuclideanSpace ℝ (Fin d))) ∈ E} = R⁻¹ • Snonneg := by
          ext t
          constructor
          · intro ht
            refine ⟨R * t, ⟨mul_nonneg hR0 ht.1.1, ?_⟩, ?_⟩
            · have hmm : (R * t) • (θ₀ : EuclideanSpace ℝ (Fin d))
                  = t • (R • (θ₀ : EuclideanSpace ℝ (Fin d))) := by
                rw [mul_smul, smul_comm]
              rw [hmm]; exact ht.2
            · show R⁻¹ * (R * t) = t
              exact inv_mul_cancel_left₀ hRne t
          · intro ht
            obtain ⟨u, hu, hut⟩ := ht
            have ht_eq : t = R⁻¹ * u := by
              rw [← hut]
              exact smul_eq_mul (R⁻¹) u
            rw [ht_eq]
            have huR : u ≤ R := hboundS u hu.1 hu.2
            have h1 : R⁻¹ * u ∈ Set.Icc (0:ℝ) 1 := by
              constructor
              · exact mul_nonneg (inv_nonneg.mpr hR0) hu.1
              · calc R⁻¹ * u ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left huR (inv_nonneg.mpr hR0)
                  _ = 1 := inv_mul_cancel₀ hRne
            refine ⟨h1, ?_⟩
            have h2 : (R⁻¹ * u) • (R • (θ₀ : EuclideanSpace ℝ (Fin d)))
                = u • (θ₀ : EuclideanSpace ℝ (Fin d)) := by
              rw [smul_smul]
              congr 1
              calc R⁻¹ * u * R = (R⁻¹ * R) * u := by ring
                _ = 1 * u := by rw [inv_mul_cancel₀ hRne]
                _ = u := one_mul u
            rw [h2]; exact hu.2
        have hvolT : volume {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧
              y + t • (R • (θ₀ : EuclideanSpace ℝ (Fin d))) ∈ E}
            = ENNReal.ofReal R⁻¹ * (∫⁻ r in Ioi (0:ℝ),
                (if y + r • (θ₀ : EuclideanSpace ℝ (Fin d)) ∈ E then 1 else 0)) := by
          rw [hset, Measure.addHaar_smul_of_nonneg volume (inv_nonneg.mpr hR0), hSnonneg_vol,
            ← hAeq]
          simp
        have hSpos_sub : Spos ⊆ Set.Ioc (0:ℝ) (Real.sqrt d) := by
          intro t ht
          exact ⟨ht.1, (hboundS t ht.1.le ht.2).trans hRd⟩
        have hAtop : (∫⁻ r in Ioi (0:ℝ), (if y + r • (θ₀ : EuclideanSpace ℝ (Fin d)) ∈ E
            then 1 else 0)) ≠ ⊤ := by
          rw [hAeq]
          refine ne_top_of_le_ne_top ?_ (measure_mono hSpos_sub)
          rw [Real.volume_Ioc]
          exact ENNReal.ofReal_ne_top
        have hM : (volume E).toReal / (2 * (Real.sqrt d) ^ (d - 1) * s)
            ≤ (∫⁻ r in Ioi (0:ℝ), (if y + r • (θ₀ : EuclideanSpace ℝ (Fin d)) ∈ E
                then 1 else 0)).toReal := by
          have h1 : (volume E / (2 * ENNReal.ofReal ((Real.sqrt d) ^ (d - 1)) *
              (Measure.toSphere (volume : Measure (EuclideanSpace ℝ (Fin d))) Set.univ))).toReal
              ≤ (∫⁻ r in Ioi (0:ℝ), (if y + r • (θ₀ : EuclideanSpace ℝ (Fin d)) ∈ E
                  then 1 else 0)).toReal := by
            apply ENNReal.toReal_mono hAtop
            exact hθ₀
          rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
            ENNReal.toReal_ofReal (pow_nonneg (Real.sqrt_nonneg d) _), ← hsdef] at h1
          exact h1
        have hvolTreal : (volume {t : ℝ | t ∈ Set.Icc (0:ℝ) 1 ∧
              y + t • (R • (θ₀ : EuclideanSpace ℝ (Fin d))) ∈ E}).toReal
            = R⁻¹ * (∫⁻ r in Ioi (0:ℝ), (if y + r • (θ₀ : EuclideanSpace ℝ (Fin d)) ∈ E
                then 1 else 0)).toReal := by
          rw [hvolT, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hR0)]
        rw [hvolTreal]
        have hsd' : (Real.sqrt d) ^ d = (Real.sqrt d) ^ (d - 1) * Real.sqrt d := by
          rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne d) with ⟨k, rfl⟩
          simp [pow_succ]
        have hVE0 : 0 ≤ (volume E).toReal := ENNReal.toReal_nonneg
        have hmin : min (1/2) (1 / (1 + 2 * (Real.sqrt d) ^ d * s))
            ≤ 1 / (2 * (Real.sqrt d) ^ d * s) := by
          refine le_trans (min_le_right _ _) ?_
          apply div_le_div_of_nonneg_left (by norm_num)
          · have hx : (0:ℝ) < (Real.sqrt d) ^ d * s :=
              mul_pos (pow_pos hsqpos d) hspos
            linarith
          · linarith
        have hRinv : (Real.sqrt d)⁻¹ ≤ R⁻¹ := (inv_le_inv₀ hsqpos hRpos).mpr hRd
        calc min (1/2) (1 / (1 + 2 * (Real.sqrt d) ^ d * s)) * (volume E).toReal
            ≤ (1 / (2 * (Real.sqrt d) ^ d * s)) * (volume E).toReal :=
              mul_le_mul_of_nonneg_right hmin hVE0
          _ = (Real.sqrt d)⁻¹ * ((volume E).toReal / (2 * (Real.sqrt d) ^ (d - 1) * s)) := by
              rw [hsd']
              field_simp
          _ ≤ R⁻¹ * (∫⁻ r in Ioi (0:ℝ), (if y + r • (θ₀ : EuclideanSpace ℝ (Fin d)) ∈ E
                then 1 else 0)).toReal := by
              apply mul_le_mul hRinv hM
              · positivity
              · positivity

end Commons.Measure.EuclideanSpace