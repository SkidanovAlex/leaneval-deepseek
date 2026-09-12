import Mathlib.Analysis.Convex.Body
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Commons.MeasureTheory.Prod.toReal_prod_apply_section
import Submission.Commons.Topology.Metric.infDist_le_iff
import Submission.Commons.Analysis.Real.sqrt_iff_sq
import Submission.Commons.MeasureTheory.Prod.integral_section_eq_intervalIntegral

open MeasureTheory Metric
open scoped RealInnerProductSpace

namespace Commons.Geometry.Convex.Hadwiger

/-! ### Infrastructure for slicing the parallel body of a lifted convex body

We split `ℝ^{m+1} ≅ ℝ × ℝ^m` (first coordinate vs. the rest), which is a measure
preserving map for the Lebesgue measures, and record the Pythagorean identity
`dist y (lift x)^2 = (split y).1^2 + dist (split y).2 x^2`.
-/

/-- The lift of `x : ℝ^m` into `ℝ^{m+1}` with a zero first coordinate. -/
private noncomputable def liftFun (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cases 0 (fun i : Fin m => x i))

/-- The splitting of `ℝ^{m+1}` into its first coordinate and the remaining ones. -/
private noncomputable def splitFun (m : ℕ) :
    EuclideanSpace ℝ (Fin (m + 1)) → ℝ × EuclideanSpace ℝ (Fin m) :=
  fun y => ((EuclideanSpace.equiv (Fin (m + 1)) ℝ) y 0,
            (EuclideanSpace.equiv (Fin m) ℝ).symm
              (fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ) y i.succ))

private lemma liftFun_ofLp (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    (liftFun m x).ofLp = Fin.cases 0 (fun i : Fin m => x.ofLp i) := by
  simp [liftFun]

private lemma splitFun_fst (m : ℕ) (y : EuclideanSpace ℝ (Fin (m + 1))) :
    (splitFun m y).1 = y.ofLp 0 := rfl

private lemma splitFun_snd (m : ℕ) (y : EuclideanSpace ℝ (Fin (m + 1))) :
    (splitFun m y).2
      = (EuclideanSpace.equiv (Fin m) ℝ).symm (fun i => y.ofLp i.succ) := rfl

private lemma splitFun_snd_ofLp (m : ℕ) (y : EuclideanSpace ℝ (Fin (m + 1))) :
    (splitFun m y).2.ofLp = fun i => y.ofLp i.succ := by
  rw [splitFun_snd]; simp

private lemma splitFun_lift (m : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    splitFun m (liftFun m x) = (0, x) := by
  refine Prod.ext ?_ ?_
  · rw [splitFun_fst, liftFun_ofLp]; simp
  · rw [splitFun_snd, liftFun_ofLp]; simp

/-- The splitting map is measure preserving. -/
private lemma splitFun_measurePreserving (m : ℕ) : MeasurePreserving (splitFun m)
    (volume : Measure (EuclideanSpace ℝ (Fin (m + 1))))
    (volume : Measure (ℝ × EuclideanSpace ℝ (Fin m))) := by
  have h1 : MeasurePreserving (fun y : EuclideanSpace ℝ (Fin (m + 1)) => WithLp.ofLp y)
      volume volume := PiLp.volume_preserving_ofLp (Fin (m + 1))
  have h2 : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0) volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  have h3 : MeasurePreserving (Prod.map id (WithLp.toLp 2) :
      ℝ × (Fin m → ℝ) → ℝ × EuclideanSpace ℝ (Fin m)) volume volume := by
    rw [Measure.volume_eq_prod ℝ (Fin m → ℝ),
      Measure.volume_eq_prod ℝ (EuclideanSpace ℝ (Fin m))]
    exact (MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin m))
  have h4 : splitFun m = (Prod.map id (WithLp.toLp 2)) ∘
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0) ∘ WithLp.ofLp := by
    funext y; rfl
  rw [h4]
  exact h3.comp (h2.comp h1)

/-- Pythagorean identity for the splitting. -/
private lemma dist_lift_sq (m : ℕ) (y : EuclideanSpace ℝ (Fin (m + 1)))
    (x : EuclideanSpace ℝ (Fin m)) :
    dist y (liftFun m x) ^ 2
      = (splitFun m y).1 ^ 2 + dist (splitFun m y).2 x ^ 2 := by
  have hL : dist y (liftFun m x) ^ 2
      = (y.ofLp 0) ^ 2 + ∑ i : Fin m, ‖y.ofLp i.succ - x.ofLp i‖ ^ 2 := by
    rw [dist_eq_norm, PiLp.norm_sq_eq_of_L2]
    rw [Fin.sum_univ_succ (f := fun i : Fin (m + 1) => ‖(y - liftFun m x).ofLp i‖ ^ 2)]
    rw [WithLp.ofLp_sub, liftFun_ofLp]
    simp only [Pi.sub_apply, Fin.cases_zero, Fin.cases_succ, sub_zero, Real.norm_eq_abs, sq_abs]
  have hR : dist (splitFun m y).2 x ^ 2
      = ∑ i : Fin m, ‖y.ofLp i.succ - x.ofLp i‖ ^ 2 := by
    rw [dist_eq_norm, PiLp.norm_sq_eq_of_L2, WithLp.ofLp_sub, splitFun_snd_ofLp]
    simp only [Pi.sub_apply]
  rw [hL, hR, splitFun_fst]

/-! ### The set whose volume we compute, and its `ℝ × ℝ^m` model -/

/-- The `t`-parallel body of `liftFun '' K` inside `ℝ^{m+1}`. -/
private noncomputable def sliceSet (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m)))
    (t : ℝ) : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  {y | ∃ x ∈ (K : Set (EuclideanSpace ℝ (Fin m))),
      dist y ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cases 0 (fun i : Fin m => x i)))
        ≤ t}

/-- The model of `sliceSet` in `ℝ × ℝ^m`: its sections are parallel bodies of `K`. -/
private noncomputable def parSet (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m)))
    (t : ℝ) : Set (ℝ × EuclideanSpace ℝ (Fin m)) :=
  {p | p.1 ∈ Set.Icc (-t) t ∧
      Metric.infDist p.2 (K : Set (EuclideanSpace ℝ (Fin m))) ≤ Real.sqrt (t ^ 2 - p.1 ^ 2)}

/-- The `r`-parallel body of `K`, written with an existential. -/
private noncomputable def parSec (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m)))
    (r : ℝ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x | ∃ k ∈ (K : Set (EuclideanSpace ℝ (Fin m))), dist x k ≤ r}

private lemma sliceSet_eq_liftFun (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m)))
    (t : ℝ) :
    sliceSet m K t
      = {y | ∃ x ∈ (K : Set (EuclideanSpace ℝ (Fin m))), dist y (liftFun m x) ≤ t} := rfl

private lemma mem_parSec (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m))) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    x ∈ parSec m K r ↔ ∃ k ∈ (K : Set (EuclideanSpace ℝ (Fin m))), dist x k ≤ r := Iff.rfl

/-- The `ℝ × ℝ^m` model is exactly the preimage of `sliceSet` under the splitting. -/
private lemma sliceSet_eq (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m))) (t : ℝ)
    (ht : 0 ≤ t) : sliceSet m K t = splitFun m ⁻¹' parSet m K t := by
  rw [sliceSet_eq_liftFun]
  ext y
  rw [Set.mem_ofPred_eq, Set.mem_preimage, parSet, Set.mem_ofPred_eq]
  have key : ∀ x ∈ (K : Set (EuclideanSpace ℝ (Fin m))),
      (dist y (liftFun m x) ≤ t ↔
        (splitFun m y).1 ∈ Set.Icc (-t) t ∧
          dist (splitFun m y).2 x ≤ Real.sqrt (t ^ 2 - (splitFun m y).1 ^ 2)) := by
    intro x _
    rw [Commons.Analysis.Real.sqrt_iff_sq ht (dist_nonneg : (0:ℝ) ≤ dist (splitFun m y).2 x)]
    rw [← dist_lift_sq m y x]
    rw [sq_le_sq, abs_of_nonneg (dist_nonneg : (0:ℝ) ≤ dist y (liftFun m x)), abs_of_nonneg ht]
  constructor
  · rintro ⟨x, hxK, hx⟩
    rw [key x hxK] at hx
    exact ⟨hx.1, (Commons.Topology.Metric.infDist_le_iff K.isCompact K.nonempty _ _).mpr
      ⟨x, hxK, hx.2⟩⟩
  · rintro ⟨hs, hinf⟩
    obtain ⟨x, hxK, hx⟩ :=
      (Commons.Topology.Metric.infDist_le_iff K.isCompact K.nonempty _ _).mp hinf
    exact ⟨x, hxK, (key x hxK).mpr ⟨hs, hx⟩⟩

private lemma parSet_measurableSet (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m)))
    (t : ℝ) : MeasurableSet (parSet m K t) := by
  have h1 : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
      Metric.infDist p.2 (K : Set (EuclideanSpace ℝ (Fin m)))) :=
    (continuous_infDist_pt (K : Set (EuclideanSpace ℝ (Fin m)))).comp continuous_snd
  have h2 : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin m) =>
      Real.sqrt (t ^ 2 - p.1 ^ 2)) :=
    Continuous.sqrt (continuous_const.sub (continuous_fst.pow 2))
  have h3 : IsClosed {p : ℝ × EuclideanSpace ℝ (Fin m) | p.1 ∈ Set.Icc (-t) t} :=
    isClosed_Icc.preimage continuous_fst
  have h4 : IsClosed {p : ℝ × EuclideanSpace ℝ (Fin m) |
      Metric.infDist p.2 (K : Set (EuclideanSpace ℝ (Fin m))) ≤ Real.sqrt (t ^ 2 - p.1 ^ 2)} :=
    isClosed_le h1 h2
  have hEq : parSet m K t = {p : ℝ × EuclideanSpace ℝ (Fin m) | p.1 ∈ Set.Icc (-t) t} ∩
      {p : ℝ × EuclideanSpace ℝ (Fin m) |
        Metric.infDist p.2 (K : Set (EuclideanSpace ℝ (Fin m)))
          ≤ Real.sqrt (t ^ 2 - p.1 ^ 2)} := by
    ext p; rw [parSet]; simp [Set.mem_inter_iff]
  rw [hEq]
  exact (h3.inter h4).measurableSet

/-- Section of the model set at height `s`. -/
private lemma parSet_section (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m)))
    (t s : ℝ) :
    Prod.mk s ⁻¹' parSet m K t
      = if s ∈ Set.Icc (-t) t then parSec m K (Real.sqrt (t ^ 2 - s ^ 2)) else ∅ := by
  by_cases hs : s ∈ Set.Icc (-t) t
  · rw [if_pos hs]
    ext z
    simp only [Set.mem_preimage, parSet, Set.mem_ofPred_eq, hs, true_and, mem_parSec]
    exact Commons.Topology.Metric.infDist_le_iff K.isCompact K.nonempty z _
  · rw [if_neg hs]
    ext z
    simp only [Set.mem_preimage, parSet, Set.mem_ofPred_eq, hs, false_and,
      Set.mem_empty_iff_false]

/-- The model set stays inside a suitable box. -/
private lemma parSet_subset_box (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m)))
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ R : ℝ, parSet m K t ⊆
      Set.Icc (-t) t ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) R := by
  obtain ⟨C, hC⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin m))).mp
      K.isCompact.isBounded
  refine ⟨C + t, ?_⟩
  rintro p ⟨hp1, hp2⟩
  refine ⟨hp1, ?_⟩
  obtain ⟨k, hkK, hk⟩ := K.isCompact.exists_infDist_eq_dist K.nonempty p.2
  have hs2 : p.1 ^ 2 ≤ t ^ 2 := by
    have h1 : 0 ≤ t - p.1 := by linarith [Set.mem_Icc.mp hp1]
    have h2 : 0 ≤ t + p.1 := by linarith [Set.mem_Icc.mp hp1]
    nlinarith [mul_nonneg h1 h2]
  have hroot : Real.sqrt (t ^ 2 - p.1 ^ 2) ≤ t := by
    have h1 : t ^ 2 - p.1 ^ 2 ≤ t ^ 2 := by linarith [sq_nonneg p.1]
    calc Real.sqrt (t ^ 2 - p.1 ^ 2) ≤ Real.sqrt (t ^ 2) := Real.sqrt_le_sqrt h1
      _ = t := Real.sqrt_sq ht
  have hd : dist p.2 k ≤ t := by rw [← hk]; exact le_trans hp2 hroot
  have hk0 : dist k 0 ≤ C := hC hkK
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖p.2‖ = dist p.2 0 := by rw [dist_zero_right]
    _ ≤ dist p.2 k + dist k 0 := dist_triangle _ _ _
    _ ≤ t + C := add_le_add hd hk0
    _ = C + t := by ring

/-- The model set has finite measure. -/
private lemma parSet_volume_ne_top (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m)))
    (t : ℝ) (ht : 0 ≤ t) : (volume.prod volume) (parSet m K t) ≠ ⊤ := by
  obtain ⟨R, hR⟩ := parSet_subset_box m K ht
  refine ne_of_lt (lt_of_le_of_lt (measure_mono hR) ?_)
  rw [Measure.prod_prod]
  exact ENNReal.mul_lt_top isCompact_Icc.measure_lt_top
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) R).measure_lt_top

/-- **Slicing the parallel body of a lifted convex body.**

For a convex body `K ⊆ ℝ^m` and `t ≥ 0`, the `(m+1)`-dimensional volume of the
`t`-neighbourhood of the lifted copy `{0} × K ⊆ ℝ^{m+1}` equals the integral over
`s ∈ [-t,t]` of the `m`-dimensional volume of the `√(t²-s²)`-neighbourhood of `K`. -/
theorem parallel_body_lift_slice (m : ℕ) (K : ConvexBody (EuclideanSpace ℝ (Fin m))) (t : ℝ) (ht : 0 ≤ t) :
    (MeasureTheory.volume
      {y : EuclideanSpace ℝ (Fin (m+1)) |
        ∃ x ∈ (K : Set (EuclideanSpace ℝ (Fin m))),
          dist y ((EuclideanSpace.equiv (Fin (m+1)) ℝ).symm (Fin.cases 0 (fun i : Fin m => x i))) ≤ t}).toReal
    = ∫ s in (-t)..t,
        (MeasureTheory.volume
          {x : EuclideanSpace ℝ (Fin m) |
            ∃ k ∈ (K : Set (EuclideanSpace ℝ (Fin m))), dist x k ≤ Real.sqrt (t^2 - s^2)}).toReal := by
  change (volume (sliceSet m K t)).toReal
    = ∫ s in (-t)..t, (volume (parSec m K (Real.sqrt (t ^ 2 - s ^ 2)))).toReal
  have hmeas : MeasurableSet (parSet m K t) := parSet_measurableSet m K t
  have hfin : (volume.prod volume) (parSet m K t) ≠ ⊤ := parSet_volume_ne_top m K t ht
  have hsec : ∀ s ∈ Set.Icc (-t) t,
      parSec m K (Real.sqrt (t ^ 2 - s ^ 2)) = Prod.mk s ⁻¹' parSet m K t := by
    intro s hs
    rw [parSet_section m K t s, if_pos hs]
  have hcongr : ∫ s in (-t)..t, (volume (parSec m K (Real.sqrt (t ^ 2 - s ^ 2)))).toReal
      = ∫ s in (-t)..t, (volume (Prod.mk s ⁻¹' parSet m K t)).toReal :=
    intervalIntegral.integral_congr (fun s hs => by
      rw [Set.uIcc_of_le (show (-t : ℝ) ≤ t by linarith)] at hs
      rw [hsec s hs])
  rw [hcongr]
  have hsub : parSet m K t ⊆ Set.Icc (-t) t ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin m))) :=
    fun p hp => ⟨hp.1, Set.mem_univ _⟩
  have hint := Commons.MeasureTheory.Prod.integral_section_eq_intervalIntegral
    (a := -t) (b := t) (show (-t : ℝ) ≤ t by linarith) hsub
  have hvol : volume (sliceSet m K t) = (volume.prod volume) (parSet m K t) := by
    rw [sliceSet_eq m K t ht, ← Measure.map_apply (splitFun_measurePreserving m).measurable hmeas,
      (splitFun_measurePreserving m).map_eq,
      Measure.volume_eq_prod ℝ (EuclideanSpace ℝ (Fin m))]
  rw [hvol, Commons.MeasureTheory.Prod.toReal_prod_apply_section hmeas hfin, ← hint]

end Commons.Geometry.Convex.Hadwiger