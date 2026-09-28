import Mathlib
import Submission.Work.HP.JcVolDefs
import Submission.Work.HP.JcVolDelta
import Submission.Work.HP.JcVolAlg

/-!
# The chain of reductions computing `𝓙(w,z)` (Browning--Le Boudec--Sawin, Lemma 4.3)

* `volume_norm_sq_Icc`: the volume of an annulus in a finite dimensional real inner product space.
* `volume_Jset_eq_lintegral`: Fubini over the orthogonal decomposition `E = P ⊕ Q`.
* `fibre_eq`: the fibre over `a ∈ P` is an annulus in `Q`.
* `measureReal_fibre`: the real volume of that fibre is `hfun (Λ a)`.
-/

set_option autoImplicit false
noncomputable section

open Filter Finset MeasureTheory
open scoped RealInnerProductSpace ENNReal NNReal

namespace Work.HP
namespace JcVolChain

variable {ι : Type*} [Fintype ι]

lemma abs_le_iff_sq_le_sq {x y : ℝ} (hy : 0 ≤ y) : |x| ≤ y ↔ x ^ 2 ≤ y ^ 2 := by
  rw [sq_le_sq, abs_of_nonneg hy]

/-- On a finite dimensional real inner product space of dimension `d`, the `d`-dimensional
Euclidean Hausdorff measure is the Lebesgue measure. -/
lemma euclidMeasure_eq_volume {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (d : ℕ)
    (h : Module.finrank ℝ V = d) :
    (MeasureTheory.Measure.euclideanHausdorffMeasure d : Measure V) = volume := by
  rw [← h]
  exact InnerProductSpace.euclideanHausdorffMeasure_eq_volume

/-- The volume of the annulus `{x : α ≤ ‖x‖² ≤ β}` in a finite dimensional real inner product
space. -/
theorem volume_norm_sq_Icc {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
    {α β : ℝ} (hαβ : α ≤ β) :
    (volume {x : V | α ≤ ‖x‖ ^ 2 ∧ ‖x‖ ^ 2 ≤ β}).toReal =
      (volume (Metric.closedBall (0 : V) 1)).toReal *
        ((Real.sqrt (max β 0)) ^ (Module.finrank ℝ V) -
          (Real.sqrt (max α 0)) ^ (Module.finrank ℝ V)) := by
  have hd0 : (Module.finrank ℝ V) ≠ 0 := Module.finrank_pos.ne'
  have hballR : ∀ r : ℝ, 0 ≤ r →
      volume.real (Metric.closedBall (0 : V) r) = r ^ (Module.finrank ℝ V) *
        volume.real (Metric.closedBall (0 : V) 1) := by
    intro r hr
    simp only [Measure.real]
    rw [show Metric.closedBall (0 : V) r = Metric.closedBall (0 : V) (r * 1) by rw [mul_one],
      Measure.addHaar_closedBall_mul volume (0 : V) hr (by norm_num : (0:ℝ) ≤ 1), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hr _)]
  have hballoR : ∀ r : ℝ, 0 ≤ r →
      volume.real (Metric.ball (0 : V) r) = r ^ (Module.finrank ℝ V) *
        volume.real (Metric.closedBall (0 : V) 1) := by
    intro r hr
    have h := hballR r hr
    simp only [Measure.real] at h ⊢
    rw [← Measure.addHaar_closedBall_eq_addHaar_ball volume (0 : V) r]
    exact h
  by_cases hβ : β ≤ 0
  · have hzero : volume {x : V | α ≤ ‖x‖ ^ 2 ∧ ‖x‖ ^ 2 ≤ β} = 0 := by
      refine measure_mono_null ?_ (measure_singleton 0)
      intro x ⟨h1, h2⟩
      have hx : ‖x‖ ^ 2 ≤ 0 := le_trans h2 hβ
      have hxn : ‖x‖ = 0 := by nlinarith [hx, norm_nonneg x]
      simpa using (norm_eq_zero.mp hxn : x = 0)
    rw [hzero, ENNReal.toReal_zero, max_eq_right hβ, max_eq_right (le_trans hαβ hβ),
      Real.sqrt_zero, zero_pow hd0, sub_self, mul_zero]
  · have hβ0 : 0 ≤ β := le_of_lt (lt_of_not_ge hβ)
    have hsub : Metric.ball (0 : V) (Real.sqrt (max α 0)) ⊆
        Metric.closedBall (0 : V) (Real.sqrt β) := by
      intro x hx
      rw [Metric.mem_ball, dist_zero_right] at hx
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖x‖ ≤ Real.sqrt (max α 0) := hx.le
        _ ≤ Real.sqrt β := Real.sqrt_le_sqrt (max_le hαβ hβ0)
    have hset : {x : V | α ≤ ‖x‖ ^ 2 ∧ ‖x‖ ^ 2 ≤ β} =
        Metric.closedBall (0 : V) (Real.sqrt β) \ Metric.ball (0 : V) (Real.sqrt (max α 0)) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
        dist_zero_right, not_lt]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · rw [show ‖x‖ = Real.sqrt (‖x‖ ^ 2) from (Real.sqrt_sq (norm_nonneg x)).symm]
          exact Real.sqrt_le_sqrt h2
        · rw [show ‖x‖ = Real.sqrt (‖x‖ ^ 2) from (Real.sqrt_sq (norm_nonneg x)).symm]
          exact Real.sqrt_le_sqrt (max_le h1 (sq_nonneg _))
      · rintro ⟨h1, h2⟩
        have h1' : ‖x‖ ^ 2 ≤ β := by
          have := Real.sq_sqrt hβ0
          nlinarith [h1, norm_nonneg x, Real.sqrt_nonneg β]
        have h2' : max α 0 ≤ ‖x‖ ^ 2 := by
          have := Real.sq_sqrt (le_max_right α 0)
          nlinarith [h2, norm_nonneg x, Real.sqrt_nonneg (max α 0)]
        exact ⟨le_trans (le_max_left α 0) h2', h1'⟩
    have hfinβ : volume (Metric.closedBall (0 : V) (Real.sqrt β)) ≠ ∞ := by
      first
      | exact (MeasureTheory.measure_closedBall_lt_top (μ := (volume : Measure V)) (x := (0:V))
          (r := Real.sqrt β)).ne
      | exact isCompact_closedBall.measure_ne_top
      | finiteness
    rw [hset]
    show volume.real (Metric.closedBall (0 : V) (Real.sqrt β) \ Metric.ball (0 : V) (Real.sqrt (max α 0))) = _
    rw [MeasureTheory.measureReal_sdiff hsub measurableSet_ball hfinβ,
      hballR (Real.sqrt β) (Real.sqrt_nonneg β),
      hballoR (Real.sqrt (max α 0)) (Real.sqrt_nonneg _)]
    simp only [Measure.real]
    rw [max_eq_left hβ0]
    ring

section Fubini
variable (w z : EuclideanSpace ℝ ι)

/-- Fubini over the orthogonal decomposition `E = P ⊕ Q`. -/
theorem volume_Jset_eq_lintegral (h : IsIndep w z) :
    volume (Jset w z) = ∫⁻ (a : ↥(planeP w z)), volume (fibreSet w z a) := by
  have hmap : Measure.map (splitP w z) (volume : Measure (EuclideanSpace ℝ ι)) =
      (volume : Measure (↥(planeP w z) × ↥(perpQ w z))) := (measurePreserving_splitP w z).map_eq
  have hS : MeasurableSet (Jset w z) := (isClosed_Jset w z).measurableSet
  have hSm : MeasurableSet ((splitP w z) '' Jset w z) := by
    rw [MeasurableEquiv.image_eq_preimage_symm]
    exact (splitP w z).symm.measurable hS
  have himg : volume ((splitP w z) '' Jset w z) = volume (Jset w z) := by
    calc volume ((splitP w z) '' Jset w z)
        = (Measure.map (splitP w z) volume) ((splitP w z) '' Jset w z) := by rw [hmap]
      _ = volume ((splitP w z) ⁻¹' ((splitP w z) '' Jset w z)) :=
            Measure.map_apply (splitP w z).measurable hSm
      _ = volume (Jset w z) := by rw [Set.preimage_image_eq _ (splitP w z).injective]
  have hset : ∀ a : ↥(planeP w z), Prod.mk a ⁻¹' ((splitP w z) '' Jset w z) = fibreSet w z a := by
    intro a
    ext s
    simp only [Set.mem_preimage, Set.mem_image, fibreSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨q, hq, hqe⟩
      have h1 : (splitP w z).symm (a, s) = q := by rw [← hqe]; simp
      rw [splitP_symm_apply] at h1
      rwa [h1]
    · intro hs
      exact ⟨(splitP w z).symm (a, s), by rw [splitP_symm_apply]; exact hs, by simp⟩
  rw [← himg, Measure.volume_eq_prod, Measure.prod_apply hSm]
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  exact congrArg volume (hset a)

/-- The fibre over `a : P` is the annulus in `Q` given by the two cone conditions. -/
theorem fibre_eq (a : ↥(planeP w z)) : fibreSet w z a = annSet w z a := by
  ext s
  simp only [fibreSet, annSet, Set.mem_ofPred_eq, Jset]
  set t : EuclideanSpace ℝ ι := (a : EuclideanSpace ℝ ι) + (s : EuclideanSpace ℝ ι) with ht
  set R : ℝ := ‖(a : EuclideanSpace ℝ ι)‖ ^ 2 + ‖(s : EuclideanSpace ℝ ι)‖ ^ 2 with hR
  have hs_w : inner ℝ w (s : EuclideanSpace ℝ ι) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K := planeP w z) (u := w)
      (v := (s : EuclideanSpace ℝ ι)) (Submodule.subset_span (by simp)) s.2
  have hs_z : inner ℝ z (s : EuclideanSpace ℝ ι) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K := planeP w z) (u := z)
      (v := (s : EuclideanSpace ℝ ι)) (Submodule.subset_span (by simp)) s.2
  have hs_a : inner ℝ (s : EuclideanSpace ℝ ι) (a : EuclideanSpace ℝ ι) = 0 :=
    Submodule.inner_left_of_mem_orthogonal (K := planeP w z) (u := (a : EuclideanSpace ℝ ι))
      (v := (s : EuclideanSpace ℝ ι)) a.2 s.2
  have hnorm : ‖t‖ ^ 2 = R := by
    rw [ht, hR]
    simpa [pow_two] using (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero
      (a : EuclideanSpace ℝ ι) (s : EuclideanSpace ℝ ι)).mpr (by rw [real_inner_comm]; exact hs_a)
  have ht0 : 0 ≤ ‖t‖ := norm_nonneg t
  have h1 : inner ℝ w t = inner ℝ w (a : EuclideanSpace ℝ ι) := by
    rw [ht, inner_add_right, hs_w, add_zero]
  have h2 : inner ℝ z t = inner ℝ z (a : EuclideanSpace ℝ ι) := by
    rw [ht, inner_add_right, hs_z, add_zero]
  have hmax : qbar (lamP w z a) = max ((inner ℝ w (a : EuclideanSpace ℝ ι)) ^ 2)
      ((inner ℝ z (a : EuclideanSpace ℝ ι)) ^ 2) := by
    simp [qbar, lamP]
  have key : (max ((inner ℝ w (a : EuclideanSpace ℝ ι)) ^ 2)
        ((inner ℝ z (a : EuclideanSpace ℝ ι)) ^ 2) ≤ R ∧ R ≤ 1) ↔
      (|inner ℝ w (a : EuclideanSpace ℝ ι)| ≤ ‖t‖ ∧ |inner ℝ z (a : EuclideanSpace ℝ ι)| ≤ ‖t‖ ∧
        ‖t‖ ≤ 1) := by
    have hsq : ∀ x : ℝ, |x| ≤ ‖t‖ ↔ x ^ 2 ≤ R := by
      intro x
      rw [abs_le_iff_sq_le_sq ht0, hnorm]
    have hle1 : ‖t‖ ≤ 1 ↔ R ≤ 1 := by
      constructor
      · intro hh; nlinarith [hh, ht0, hnorm]
      · intro hh
        nlinarith [hh, ht0, hnorm, sq_nonneg (‖t‖ - 1)]
    rw [max_le_iff]
    exact ⟨fun h => ⟨(hsq _).mpr h.1.1, (hsq _).mpr h.1.2, hle1.mpr h.2⟩,
      fun h => ⟨⟨(hsq _).mp h.1, (hsq _).mp h.2.1⟩, hle1.mp h.2.2⟩⟩
  rw [h1, h2, hmax]
  exact key.symm

/-- The dimension of `Q = Pᗮ`. -/
theorem finrank_perpQ (h : IsIndep w z) :
    Module.finrank ℝ (perpQ w z) = Fintype.card ι - 2 := by
  have hspan : Submodule.span ℝ {w, z} = Submodule.span ℝ (Set.range ![w, z]) := by
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    tauto
  have h1 : Module.finrank ℝ ↥(planeP w z) = 2 := by
    rw [planeP, hspan, finrank_span_eq_card (b := ![w, z]) h]
    simp
  have h2 := Submodule.finrank_add_finrank_orthogonal (planeP w z)
  have h3 : Module.finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι := by simp
  simp only [perpQ]
  omega

/-- The real volume of the fibre, in terms of `hfun`. -/
theorem measureReal_fibre (hN : 3 ≤ Fintype.card ι) (h : IsIndep w z) (a : ↥(planeP w z)) :
    (volume (fibreSet w z a)).toReal = hfun w z (lamP w z a) := by
  have hd := finrank_perpQ (w := w) (z := z) h
  haveI : Nontrivial ↥(perpQ w z) :=
    Module.nontrivial_of_finrank_pos (by rw [hd]; omega)
  have hq := JcVolAlg.qform_lam h a
  rw [fibre_eq]
  have hset : annSet w z a =
      {s : ↥(perpQ w z) | (qbar (lamP w z a) - ‖(a : EuclideanSpace ℝ ι)‖ ^ 2) ≤ ‖s‖ ^ 2 ∧
        ‖s‖ ^ 2 ≤ (1 - ‖(a : EuclideanSpace ℝ ι)‖ ^ 2)} := by
    ext s
    simp only [annSet, Set.mem_ofPred_eq]
    constructor
    · intro hh; exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
    · intro hh; exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  rw [hset]
  by_cases hc : qbar (lamP w z a) ≤ 1
  · have hαβ : qbar (lamP w z a) - ‖(a : EuclideanSpace ℝ ι)‖ ^ 2 ≤
        1 - ‖(a : EuclideanSpace ℝ ι)‖ ^ 2 := by linarith
    rw [volume_norm_sq_Icc hαβ, hfun, if_pos hc, hd, hq, VQ]
  · have hempty : {s : ↥(perpQ w z) |
        (qbar (lamP w z a) - ‖(a : EuclideanSpace ℝ ι)‖ ^ 2) ≤ ‖s‖ ^ 2 ∧
          ‖s‖ ^ 2 ≤ (1 - ‖(a : EuclideanSpace ℝ ι)‖ ^ 2)} = ∅ := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      linarith
    rw [hempty, measure_empty, ENNReal.toReal_zero, hfun, if_neg hc]

section Reduction
variable (w z : EuclideanSpace ℝ ι)

/-- `qform` is continuous. -/
lemma continuous_qform : Continuous (qform w z) := by
  unfold qform
  fun_prop

/-- `qbar` is continuous. -/
lemma continuous_qbar : Continuous qbar := by
  unfold qbar
  fun_prop

lemma measurable_hfun : Measurable (hfun w z) := by
  have hbranch : Measurable fun u : EuclideanSpace ℝ (Fin 2) =>
      VQ w z * ((Real.sqrt (max (1 - qform w z u) 0)) ^ (Fintype.card ι - 2) -
        (Real.sqrt (max (qbar u - qform w z u) 0)) ^ (Fintype.card ι - 2)) := by
    simp only [qform, qbar]
    fun_prop
  unfold hfun
  exact Measurable.ite (measurableSet_le continuous_qbar.measurable measurable_const) hbranch
    measurable_const

lemma VQ_nonneg : 0 ≤ VQ w z := ENNReal.toReal_nonneg

lemma hfun_nonneg (u : EuclideanSpace ℝ (Fin 2)) : 0 ≤ hfun w z u := by
  by_cases hc : qbar u ≤ 1
  · rw [hfun, if_pos hc]
    have hle : max (qbar u - qform w z u) 0 ≤ max (1 - qform w z u) 0 := by
      refine max_le ?_ (le_max_right _ _)
      exact le_trans (sub_le_sub_right hc _) (le_max_left _ _)
    have hsq : Real.sqrt (max (qbar u - qform w z u) 0) ≤
        Real.sqrt (max (1 - qform w z u) 0) := Real.sqrt_le_sqrt hle
    have hpow := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq (Fintype.card ι - 2)
    exact mul_nonneg (VQ_nonneg w z) (sub_nonneg.mpr hpow)
  · rw [hfun, if_neg hc]

/-- The fibre has finite measure: it is contained in the unit ball of `Q`. -/
theorem volume_fibre_ne_top (h : IsIndep w z) (a : ↥(planeP w z)) :
    volume (fibreSet w z a) ≠ ∞ := by
  have hsub : fibreSet w z a ⊆ Metric.closedBall (0 : ↥(perpQ w z)) 1 := by
    intro s hs
    rw [fibre_eq] at hs
    simp only [Metric.mem_closedBall, dist_zero_right]
    have h2 : ‖s‖ ^ 2 ≤ 1 := by
      have := hs.2
      have h3 : (0:ℝ) ≤ ‖(a : EuclideanSpace ℝ ι)‖ ^ 2 := sq_nonneg _
      linarith
    nlinarith [norm_nonneg s]
  exact ne_top_of_le_ne_top
    (MeasureTheory.measure_closedBall_lt_top (μ := (volume : Measure ↥(perpQ w z)))).ne
    (measure_mono hsub)

/-- The fibre measure is the `ofReal` of `hfun`. -/
theorem volume_fibre_eq (hN : 3 ≤ Fintype.card ι) (h : IsIndep w z) (a : ↥(planeP w z)) :
    volume (fibreSet w z a) = ENNReal.ofReal (hfun w z (lamP w z a)) := by
  rw [← MeasureTheory.ofReal_measureReal (μ := volume) (s := fibreSet w z a)
      (volume_fibre_ne_top w z h a)]
  congr 1
  exact measureReal_fibre w z hN h a

/-- The change of variables for the plane coordinate map `Λ`. -/
theorem map_lamP (h : IsIndep w z) (hnd : (lamP w z).normDet = Real.sqrt (deltaV w z)) :
    Measure.map (lamP w z) (volume : Measure (↥(planeP w z))) =
      (ENNReal.ofReal ((lamP w z).normDet))⁻¹ •
        (volume : Measure (EuclideanSpace ℝ (Fin 2))) := by
  classical
  have hfr : Module.finrank ℝ ↥(planeP w z) = 2 := by
    have hspan : Submodule.span ℝ {w, z} = Submodule.span ℝ (Set.range ![w, z]) := by
      congr 1
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      tauto
    rw [planeP, hspan, finrank_span_eq_card (b := ![w, z]) h]
    simp
  have hnd0 : (lamP w z).normDet ≠ 0 := by
    rw [hnd]
    exact (Real.sqrt_pos.mpr (JcVolDelta h)).ne'
  have hnd0' : ENNReal.ofReal ((lamP w z).normDet) ≠ 0 := by
    rw [hnd]
    exact (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (JcVolDelta h))).ne'
  have hsurj : Function.Surjective (lamP w z) := fun u =>
    ⟨⟨cComb w z u, cComb_mem w z u⟩, JcVolAlg.lam_cComb h u⟩
  let e : ↥(planeP w z) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) := lamP w z
  have hμ : (MeasureTheory.Measure.euclideanHausdorffMeasure (Module.finrank ℝ ↥(planeP w z)) :
      Measure (EuclideanSpace ℝ (Fin 2))) = volume := by
    rw [hfr]
    exact euclidMeasure_eq_volume 2 (by rw [finrank_euclideanSpace_fin])
  refine Measure.ext fun B hB => ?_
  rw [Measure.map_apply (lamP w z).continuous_of_finiteDimensional.measurable hB]
  have himg := LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume e (e ⁻¹' B)
  rw [Set.image_preimage_eq _ hsurj, hμ] at himg
  rw [Measure.smul_apply, smul_eq_mul]
  rw [himg, ← mul_assoc, ENNReal.inv_mul_cancel hnd0' ENNReal.ofReal_ne_top, one_mul]

/-- The main reduction: `𝓙(w,z)` is `δ^{-1/2}` times the explicit two-dimensional integral of
`hfun`. -/
theorem JcVol_eq (hN : 3 ≤ Fintype.card ι) (h : IsIndep w z)
    (hnd : (lamP w z).normDet = Real.sqrt (deltaV w z)) :
    JcVol w z = (Real.sqrt (deltaV w z))⁻¹ * ∫ u, hfun w z u := by
  have hkey : ∫⁻ (a : ↥(planeP w z)), ENNReal.ofReal (hfun w z (lamP w z a)) =
      (ENNReal.ofReal (Real.sqrt (deltaV w z)))⁻¹ *
        ∫⁻ (u : EuclideanSpace ℝ (Fin 2)), ENNReal.ofReal (hfun w z u) := by
    rw [← lintegral_map (measurable_hfun w z).ennreal_ofReal
        (lamP w z).continuous_of_finiteDimensional.measurable, map_lamP w z h hnd,
      lintegral_smul_measure, smul_eq_mul, hnd]
  have hmain : volume (Jset w z) =
      (ENNReal.ofReal (Real.sqrt (deltaV w z)))⁻¹ *
        ∫⁻ (u : EuclideanSpace ℝ (Fin 2)), ENNReal.ofReal (hfun w z u) := by
    rw [volume_Jset_eq_lintegral w z h,
      lintegral_congr fun a => volume_fibre_eq w z hN h a]
    exact hkey
  have hfin : ∀ᵐ u ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      ENNReal.ofReal (hfun w z u) < ∞ :=
    Filter.Eventually.of_forall fun u => ENNReal.ofReal_lt_top
  have hint : ∫ (u : EuclideanSpace ℝ (Fin 2)), (ENNReal.ofReal (hfun w z u)).toReal =
      (∫⁻ (u : EuclideanSpace ℝ (Fin 2)), ENNReal.ofReal (hfun w z u)).toReal :=
    MeasureTheory.integral_toReal (measurable_hfun w z).ennreal_ofReal.aemeasurable hfin
  calc JcVol w z = (volume (Jset w z)).toReal := rfl
    _ = ((ENNReal.ofReal (Real.sqrt (deltaV w z)))⁻¹ *
          ∫⁻ (u : EuclideanSpace ℝ (Fin 2)), ENNReal.ofReal (hfun w z u)).toReal := by
          rw [hmain]
    _ = (ENNReal.ofReal (Real.sqrt (deltaV w z)))⁻¹.toReal *
          (∫⁻ (u : EuclideanSpace ℝ (Fin 2)), ENNReal.ofReal (hfun w z u)).toReal := by
          rw [ENNReal.toReal_mul]
    _ = (ENNReal.ofReal (Real.sqrt (deltaV w z))).toReal⁻¹ *
          (∫⁻ (u : EuclideanSpace ℝ (Fin 2)), ENNReal.ofReal (hfun w z u)).toReal := by
          rw [ENNReal.toReal_inv]
    _ = (Real.sqrt (deltaV w z))⁻¹ *
          (∫⁻ (u : EuclideanSpace ℝ (Fin 2)), ENNReal.ofReal (hfun w z u)).toReal := by
          rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    _ = (Real.sqrt (deltaV w z))⁻¹ * ∫ u, hfun w z u := by
          rw [← hint]
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          simp only [ENNReal.toReal_ofReal (hfun_nonneg w z u)]

end Reduction
section Bounds
variable (w z : EuclideanSpace ℝ ι)

lemma qform_nonneg (h : IsIndep w z) (u : EuclideanSpace ℝ (Fin 2)) : 0 ≤ qform w z u := by
  rw [qform]
  exact div_nonneg (sq_nonneg _) (JcVolDelta h).le

/-- `qform` is bounded by `(‖w‖+‖z‖)²/δ` on the coordinate unit square. -/
theorem qform_bound (h : IsIndep w z) (u : EuclideanSpace ℝ (Fin 2))
    (h0 : |u 0| ≤ 1) (h1 : |u 1| ≤ 1) :
    qform w z u ≤ (‖w‖ + ‖z‖) ^ 2 / deltaV w z := by
  have hδ := JcVolDelta h
  have hle : ‖(u 0) • z - (u 1) • w‖ ≤ ‖w‖ + ‖z‖ := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h2 : |u 0| * ‖z‖ ≤ ‖z‖ := by simpa using mul_le_mul_of_nonneg_right h0 (norm_nonneg z)
    have h3 : |u 1| * ‖w‖ ≤ ‖w‖ := by simpa using mul_le_mul_of_nonneg_right h1 (norm_nonneg w)
    linarith
  have hsq : ‖(u 0) • z - (u 1) • w‖ ^ 2 ≤ (‖w‖ + ‖z‖) ^ 2 := by
    nlinarith [hle, norm_nonneg ((u 0) • z - (u 1) • w), norm_nonneg (‖w‖ + ‖z‖)]
  rw [qform]
  gcongr

/-- `qbar u ≤ 1` implies the coordinates lie in `[-1,1]`. -/
lemma abs_coord_le_one {u : EuclideanSpace ℝ (Fin 2)} (hu : qbar u ≤ 1) :
    |u 0| ≤ 1 ∧ |u 1| ≤ 1 := by
  have h0 : (u 0) ^ 2 ≤ 1 := le_trans (le_max_left _ _) hu
  have h1 : (u 1) ^ 2 ≤ 1 := le_trans (le_max_right _ _) hu
  exact ⟨by nlinarith [h0, sq_nonneg (u 0), abs_nonneg (u 0), sq_abs (u 0)],
    by nlinarith [h1, sq_nonneg (u 1), abs_nonneg (u 1), sq_abs (u 1)]⟩

/-- `hfun` is `VQ` times the normalized integrand `mu`. -/
theorem hfun_eq (u : EuclideanSpace ℝ (Fin 2)) : hfun w z u = VQ w z * mu w z u := by
  rw [hfun, mu]
  split <;> simp [nu]

end Bounds

section Assembly
variable (w z : EuclideanSpace ℝ ι)

/-- The main asymptotic, assuming the four auxiliary facts proved elsewhere. -/
theorem JcVolAsymp_aux (hN : 3 ≤ Fintype.card ι)
    (hnd : ∀ (w z : EuclideanSpace ℝ ι), IsIndep w z →
      (lamP w z).normDet = Real.sqrt (deltaV w z))
    (hest : ∀ (w z : EuclideanSpace ℝ ι), IsIndep w z →
      |(∫ u, mu w z u) - 4 * ((Fintype.card ι : ℝ) - 2) / (Fintype.card ι : ℝ)| ≤
        100 * ((Fintype.card ι : ℝ) + 2) *
          (4 * ((Fintype.card ι : ℝ) - 2) / (Fintype.card ι : ℝ)) *
            min 1 ((‖w‖ + ‖z‖) ^ 2 / deltaV w z))
    (hvq : ∀ (w z : EuclideanSpace ℝ ι), IsIndep w z →
      VQ w z = ballVol (Fintype.card ι - 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w z : EuclideanSpace ℝ ι), LinearIndependent ℝ ![w, z] →
      |JcVol w z - 4 * ((Fintype.card ι : ℝ) - 2) / (Fintype.card ι : ℝ) *
          ballVol (Fintype.card ι - 2) / Real.sqrt (deltaV w z)| ≤
      C * (4 * ((Fintype.card ι : ℝ) - 2) / (Fintype.card ι : ℝ) *
          ballVol (Fintype.card ι - 2) / Real.sqrt (deltaV w z)) *
        min 1 ((‖w‖ + ‖z‖) ^ 2 / deltaV w z) := by
  refine ⟨100 * ((Fintype.card ι : ℝ) + 2), by positivity, fun w z h => ?_⟩
  have hδ := JcVolDelta h
  have hmain := JcVol_eq w z hN h (hnd w z h)
  have hint : ∫ u, hfun w z u = VQ w z * ∫ u, mu w z u := by
    rw [show (fun u => hfun w z u) = fun u => VQ w z * mu w z u from
      funext (hfun_eq w z), integral_const_mul]
  have hest' := hest w z h
  have hvq' := hvq w z h
  set K : ℝ := 4 * ((Fintype.card ι : ℝ) - 2) / (Fintype.card ι : ℝ) *
    ballVol (Fintype.card ι - 2) with hK
  have hVQ0 : 0 ≤ VQ w z := VQ_nonneg w z
  have hsqrt : 0 < Real.sqrt (deltaV w z) := Real.sqrt_pos.mpr hδ
  have hstep : JcVol w z - K / Real.sqrt (deltaV w z) =
      (Real.sqrt (deltaV w z))⁻¹ * (VQ w z * (∫ u, mu w z u) - K) := by
    rw [hmain, hint, div_eq_mul_inv, mul_sub]
    congr 1
    rw [mul_comm K ((Real.sqrt (deltaV w z))⁻¹)]
  have hinner : |VQ w z * (∫ u, mu w z u) - K| ≤
      VQ w z * (100 * ((Fintype.card ι : ℝ) + 2) *
        (4 * ((Fintype.card ι : ℝ) - 2) / (Fintype.card ι : ℝ)) *
          min 1 ((‖w‖ + ‖z‖) ^ 2 / deltaV w z)) := by
    have h1 : VQ w z * (∫ u, mu w z u) - K = VQ w z *
        ((∫ u, mu w z u) - 4 * ((Fintype.card ι : ℝ) - 2) / (Fintype.card ι : ℝ)) := by
      rw [mul_sub]
      congr 1
      rw [hK, hvq']
      ring
    rw [h1, abs_mul, abs_of_nonneg hVQ0]
    exact mul_le_mul_of_nonneg_left hest' hVQ0
  rw [hstep, abs_mul, abs_of_nonneg (inv_nonneg.mpr hsqrt.le)]
  calc (Real.sqrt (deltaV w z))⁻¹ * |VQ w z * (∫ u, mu w z u) - K|
      ≤ (Real.sqrt (deltaV w z))⁻¹ * (VQ w z * (100 * ((Fintype.card ι : ℝ) + 2) *
          (4 * ((Fintype.card ι : ℝ) - 2) / (Fintype.card ι : ℝ)) *
            min 1 ((‖w‖ + ‖z‖) ^ 2 / deltaV w z))) :=
        mul_le_mul_of_nonneg_left hinner (inv_nonneg.mpr hsqrt.le)
    _ = 100 * ((Fintype.card ι : ℝ) + 2) * (4 * ((Fintype.card ι : ℝ) - 2) /
          (Fintype.card ι : ℝ) * ballVol (Fintype.card ι - 2) /
            Real.sqrt (deltaV w z)) * min 1 ((‖w‖ + ‖z‖) ^ 2 / deltaV w z) := by
        rw [hvq']
        ring

end Assembly
end Fubini
end JcVolChain
end Work.HP
