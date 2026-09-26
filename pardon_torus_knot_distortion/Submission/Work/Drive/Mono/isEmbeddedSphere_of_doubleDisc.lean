import Mathlib
import Submission.Work.InnermostDisk.Slicing
import Submission.Work.CoreTopology.Disk
import Submission.Work.CoreTopology.TorusDichotomyDefs

/-!
# Gluing two discs along their common boundary

If `eA eB : C(𝔻, ℝ³)` are injective continuous maps of the closed unit disc which agree on the
boundary circle and whose images meet only along that boundary, then the union of their images
is an embedded 2-sphere.

The sphere is realized explicitly by `doubleDiscMap`: a point `x` of the unit sphere of `ℝ³` is
sent to the point of the disc over the first two coordinates of `x` — in the disc `eA` if the
third coordinate of `x` is nonnegative, and in the disc `eB` otherwise.  Continuity is gluing
along the two closed hemispheres, which meet on the equator, where the two discs agree by
hypothesis; injectivity is the elementary fact that a point of the sphere is determined by its
first two coordinates together with the sign of its third coordinate.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-! ## The projection of the unit sphere onto the unit disc -/

/-- The first two coordinates of a point of the unit sphere of `ℝ³`, as a point of the closed
unit disc `𝔻 ⊆ ℂ`.  A point of the sphere lies over its projection in the upper hemisphere when
its third coordinate is nonnegative and in the lower hemisphere otherwise. -/
def sphProj (x : Metric.sphere (0 : R3) 1) : Metric.closedBall (0 : ℂ) 1 :=
  ⟨((x : R3) 0 : ℂ) + ((x : R3) 1 : ℂ) * Complex.I, by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hx : ‖(x : R3)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using x.2
    have hle : ((x : R3) 0) ^ 2 + ((x : R3) 1) ^ 2 ≤ 1 := by
      have h := EuclideanSpace.norm_sq_eq (𝕜 := ℝ) (x : R3)
      rw [hx, one_pow, Fin.sum_univ_three] at h
      simp only [Real.norm_eq_abs, sq_abs] at h
      nlinarith [sq_nonneg ((x : R3) 2)]
    have hns : ‖(((x : R3) 0 : ℂ) + ((x : R3) 1 : ℂ) * Complex.I)‖ ^ 2
        = ((x : R3) 0) ^ 2 + ((x : R3) 1) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    nlinarith [norm_nonneg (((x : R3) 0 : ℂ) + ((x : R3) 1 : ℂ) * Complex.I)]⟩

@[simp] theorem sphProj_coe (x : Metric.sphere (0 : R3) 1) :
    ((sphProj x : Metric.closedBall (0 : ℂ) 1) : ℂ)
      = ((x : R3) 0 : ℂ) + ((x : R3) 1 : ℂ) * Complex.I := rfl

/-- On the unit sphere, the squares of the three coordinates sum to one. -/
theorem sph_sq_sum (x : Metric.sphere (0 : R3) 1) :
    ((x : R3) 0) ^ 2 + ((x : R3) 1) ^ 2 + ((x : R3) 2) ^ 2 = 1 := by
  have hx : ‖(x : R3)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using x.2
  have h := EuclideanSpace.norm_sq_eq (𝕜 := ℝ) (x : R3)
  rw [hx, one_pow, Fin.sum_univ_three] at h
  simpa only [Real.norm_eq_abs, sq_abs] using h.symm

/-- The squared norm of the projection of a point of the sphere. -/
theorem norm_sphProj_sq (x : Metric.sphere (0 : R3) 1) :
    ‖((sphProj x : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ ^ 2 = 1 - ((x : R3) 2) ^ 2 := by
  have h : ‖((sphProj x : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ ^ 2
      = ((x : R3) 0) ^ 2 + ((x : R3) 1) ^ 2 := by
    rw [sphProj_coe, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [h]
  have hsum := sph_sq_sum x
  linarith

theorem norm_sphProj_le_one (x : Metric.sphere (0 : R3) 1) :
    ‖((sphProj x : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ ≤ 1 := by
  simpa [Metric.mem_closedBall, dist_zero_right] using (sphProj x).2

/-- The projection of a point of the sphere lies on the boundary circle exactly when the point
lies on the equator. -/
theorem sphProj_norm_eq_one_iff (x : Metric.sphere (0 : R3) 1) :
    ‖((sphProj x : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1 ↔ (x : R3) 2 = 0 := by
  constructor
  · intro h
    have h2 := norm_sphProj_sq x
    rw [h] at h2
    have hzero : ((x : R3) 2) ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero
  · intro h
    have h2 := norm_sphProj_sq x
    rw [h] at h2
    have hnn : 0 ≤ ‖((sphProj x : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ := norm_nonneg _
    nlinarith

theorem fst_eq_of_sphProj_eq {x y : Metric.sphere (0 : R3) 1} (h : sphProj x = sphProj y) :
    (x : R3) 0 = (y : R3) 0 := by
  have := congrArg Complex.re (congrArg (fun z : Metric.closedBall (0 : ℂ) 1 => (z : ℂ)) h)
  simpa [sphProj_coe] using this

theorem snd_eq_of_sphProj_eq {x y : Metric.sphere (0 : R3) 1} (h : sphProj x = sphProj y) :
    (x : R3) 1 = (y : R3) 1 := by
  have := congrArg Complex.im (congrArg (fun z : Metric.closedBall (0 : ℂ) 1 => (z : ℂ)) h)
  simpa [sphProj_coe] using this

theorem snd_sq_eq_of_sphProj_eq {x y : Metric.sphere (0 : R3) 1} (h : sphProj x = sphProj y) :
    ((x : R3) 2) ^ 2 = ((y : R3) 2) ^ 2 := by
  have h0 := fst_eq_of_sphProj_eq h
  have h1 := snd_eq_of_sphProj_eq h
  have hx := sph_sq_sum x
  have hy := sph_sq_sum y
  rw [h0, h1] at hx
  linarith

/-- Two points of the upper closed hemisphere with the same projection are equal. -/
theorem eq_of_sphProj_eq_of_snd_nonneg {x y : Metric.sphere (0 : R3) 1}
    (hx : 0 ≤ (x : R3) 2) (hy : 0 ≤ (y : R3) 2) (h : sphProj x = sphProj y) : x = y := by
  have h0 := fst_eq_of_sphProj_eq h
  have h1 := snd_eq_of_sphProj_eq h
  have h2 : (x : R3) 2 = (y : R3) 2 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (snd_sq_eq_of_sphProj_eq h) with h' | h'
    · exact h'
    · linarith
  refine Subtype.ext (PiLp.ext (fun i => ?_))
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2

/-- Two points of the lower closed hemisphere with the same projection are equal. -/
theorem eq_of_sphProj_eq_of_snd_nonpos {x y : Metric.sphere (0 : R3) 1}
    (hx : (x : R3) 2 ≤ 0) (hy : (y : R3) 2 ≤ 0) (h : sphProj x = sphProj y) : x = y := by
  have h0 := fst_eq_of_sphProj_eq h
  have h1 := snd_eq_of_sphProj_eq h
  have h2 : (x : R3) 2 = (y : R3) 2 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (snd_sq_eq_of_sphProj_eq h) with h' | h'
    · exact h'
    · linarith
  refine Subtype.ext (PiLp.ext (fun i => ?_))
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2

theorem continuous_sphProj : Continuous sphProj := by
  refine Continuous.subtype_mk (by fun_prop) _

/-! ## Points of the sphere over a point of the disc -/

/-- The points of the unit sphere of `ℝ³` whose first two coordinates are those of `z` and whose
third coordinate is `s` (which must satisfy `s² = 1 - ‖z‖²`). -/
def discToSphere (z : Metric.closedBall (0 : ℂ) 1) (s : ℝ)
    (hs : s ^ 2 = 1 - ‖(z : ℂ)‖ ^ 2) : Metric.sphere (0 : R3) 1 :=
  ⟨WithLp.toLp 2 ![(z : ℂ).re, (z : ℂ).im, s], by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    have hsplit : ‖(WithLp.toLp 2 ![(z : ℂ).re, (z : ℂ).im, s] : R3)‖ ^ 2
        = (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 + s ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
      simp only [Real.norm_eq_abs, sq_abs, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    have hre : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = ‖(z : ℂ)‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hnorm : ‖(WithLp.toLp 2 ![(z : ℂ).re, (z : ℂ).im, s] : R3)‖ ^ 2 = 1 := by
      rw [hsplit, hre, hs]
      ring
    nlinarith [norm_nonneg (WithLp.toLp 2 ![(z : ℂ).re, (z : ℂ).im, s] : R3)]⟩

theorem discToSphere_snd (z : Metric.closedBall (0 : ℂ) 1) (s : ℝ)
    (hs : s ^ 2 = 1 - ‖(z : ℂ)‖ ^ 2) : (discToSphere z s hs : R3) 2 = s := rfl

theorem sphProj_discToSphere (z : Metric.closedBall (0 : ℂ) 1) (s : ℝ)
    (hs : s ^ 2 = 1 - ‖(z : ℂ)‖ ^ 2) : sphProj (discToSphere z s hs) = z := by
  refine Subtype.ext ?_
  show (((z : ℂ).re : ℂ) + ((z : ℂ).im : ℂ) * Complex.I) = (z : ℂ)
  exact Complex.re_add_im z

theorem discToSphere_subtype_val (z : Metric.closedBall (0 : ℂ) 1) (s : ℝ)
    (hs : s ^ 2 = 1 - ‖(z : ℂ)‖ ^ 2) :
    (discToSphere z s hs : R3) = WithLp.toLp 2 ![(z : ℂ).re, (z : ℂ).im, s] := rfl

/-- The point of the closed upper hemisphere of the unit sphere over `z : 𝔻`. -/
def discToUpper (z : Metric.closedBall (0 : ℂ) 1) : Metric.sphere (0 : R3) 1 :=
  discToSphere z (Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2)) (by
    have hz : ‖(z : ℂ)‖ ≤ 1 := by
      have h := z.2
      rw [Metric.mem_closedBall, dist_zero_right] at h
      exact h
    rw [Real.sq_sqrt (by nlinarith [norm_nonneg (z : ℂ)])])

/-- The point of the closed lower hemisphere of the unit sphere over `z : 𝔻`. -/
def discToLower (z : Metric.closedBall (0 : ℂ) 1) : Metric.sphere (0 : R3) 1 :=
  discToSphere z (-Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2)) (by
    have hz : ‖(z : ℂ)‖ ≤ 1 := by
      have h := z.2
      rw [Metric.mem_closedBall, dist_zero_right] at h
      exact h
    rw [neg_sq, Real.sq_sqrt (by nlinarith [norm_nonneg (z : ℂ)])])

theorem sphProj_discToUpper (z : Metric.closedBall (0 : ℂ) 1) :
    sphProj (discToUpper z) = z :=
  sphProj_discToSphere z _ _

theorem sphProj_discToLower (z : Metric.closedBall (0 : ℂ) 1) :
    sphProj (discToLower z) = z :=
  sphProj_discToSphere z _ _

theorem discToUpper_snd (z : Metric.closedBall (0 : ℂ) 1) :
    (discToUpper z : R3) 2 = Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2) :=
  discToSphere_snd z _ _

theorem discToLower_snd (z : Metric.closedBall (0 : ℂ) 1) :
    (discToLower z : R3) 2 = -Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2) :=
  discToSphere_snd z _ _

theorem discToUpper_snd_nonneg (z : Metric.closedBall (0 : ℂ) 1) :
    0 ≤ (discToUpper z : R3) 2 := by
  rw [discToUpper_snd z]
  exact Real.sqrt_nonneg _

theorem discToLower_snd_nonpos (z : Metric.closedBall (0 : ℂ) 1) :
    (discToLower z : R3) 2 ≤ 0 := by
  rw [discToLower_snd z]
  exact neg_nonpos.mpr (Real.sqrt_nonneg _)

/-! ## The map glued from the two discs -/

/-- The map from the unit sphere to `ℝ³` which sends the closed upper hemisphere to the disc `eA`
and the closed lower hemisphere to the disc `eB`, via the projection to the first two
coordinates.  The two branches agree on the equator by `hbd`. -/
def doubleDiscMap (eA eB : C(Metric.closedBall (0 : ℂ) 1, R3))
    (hbd : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ = 1 → eA z = eB z) :
    C(Metric.sphere (0 : R3) 1, R3) where
  toFun x := if 0 ≤ (x : R3) 2 then eA (sphProj x) else eB (sphProj x)
  continuous_toFun := by
    refine Continuous.if (p := fun x : Metric.sphere (0 : R3) 1 => 0 ≤ (x : R3) 2) ?_ ?_ ?_
    · intro x hx
      have hcont : Continuous fun y : Metric.sphere (0 : R3) 1 => (y : R3) 2 := by fun_prop
      have hA : IsClosed {y : Metric.sphere (0 : R3) 1 | 0 ≤ (y : R3) 2} :=
        isClosed_Ici.preimage hcont
      have hB : IsClosed {y : Metric.sphere (0 : R3) 1 | (y : R3) 2 ≤ 0} :=
        isClosed_Iic.preimage hcont
      rw [frontier_eq_closure_inter_closure] at hx
      have h1 : 0 ≤ (x : R3) 2 := by
        have h := hx.1
        rwa [hA.closure_eq] at h
      have h2 : (x : R3) 2 ≤ 0 := by
        have hmem : x ∈ closure {y : Metric.sphere (0 : R3) 1 | ¬ (0 ≤ (y : R3) 2)} := hx.2
        have hsub : {y : Metric.sphere (0 : R3) 1 | ¬ (0 ≤ (y : R3) 2)}
            ⊆ {y : Metric.sphere (0 : R3) 1 | (y : R3) 2 ≤ 0} := by
          intro y hy
          exact le_of_lt (lt_of_not_ge hy)
        exact hB.closure_subset_iff.mpr hsub hmem
      have hzero : (x : R3) 2 = 0 := le_antisymm h2 h1
      have hnorm : ‖((sphProj x : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1 :=
        (sphProj_norm_eq_one_iff x).2 hzero
      obtain ⟨θ, hθ⟩ := Work.CoreTopology.exists_circlePoint_eq _ hnorm
      have hpx : sphProj x = Work.CoreTopology.circlePoint θ := Subtype.ext hθ.symm
      have hnθ : ‖((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1 := by
        rw [← hpx]; exact hnorm
      rw [hpx]
      exact hbd _ hnθ
    · exact eA.continuous.comp continuous_sphProj
    · exact eB.continuous.comp continuous_sphProj

@[simp] theorem doubleDiscMap_apply (eA eB : C(Metric.closedBall (0 : ℂ) 1, R3))
    (hbd : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ = 1 → eA z = eB z)
    (x : Metric.sphere (0 : R3) 1) :
    doubleDiscMap eA eB hbd x = if 0 ≤ (x : R3) 2 then eA (sphProj x) else eB (sphProj x) :=
  rfl

theorem doubleDiscMap_injective (eA eB : C(Metric.closedBall (0 : ℂ) 1, R3))
    (hbd : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ = 1 → eA z = eB z)
    (hAinj : Function.Injective eA) (hBinj : Function.Injective eB)
    (hint : ∀ z w : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ < 1 → ‖(w : ℂ)‖ < 1 →
      eA z = eB w → False) :
    Function.Injective (doubleDiscMap eA eB hbd) := by
  intro x y hxy
  rw [doubleDiscMap_apply, doubleDiscMap_apply] at hxy
  by_cases hx : 0 ≤ (x : R3) 2
  · by_cases hy : 0 ≤ (y : R3) 2
    · rw [if_pos hx, if_pos hy] at hxy
      exact eq_of_sphProj_eq_of_snd_nonneg hx hy (hAinj hxy)
    · rw [if_pos hx, if_neg hy] at hxy
      exfalso
      have hy2 : (y : R3) 2 < 0 := lt_of_not_ge hy
      by_cases hny : ‖((sphProj y : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1
      · have : (y : R3) 2 = 0 := (sphProj_norm_eq_one_iff y).1 hny
        linarith
      · have hpy : ‖((sphProj y : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ < 1 :=
          lt_of_le_of_ne (norm_sphProj_le_one y) hny
        by_cases hnx : ‖((sphProj x : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1
        · obtain ⟨θ, hθ⟩ := Work.CoreTopology.exists_circlePoint_eq _ hnx
          have hpx : sphProj x = Work.CoreTopology.circlePoint θ := Subtype.ext hθ.symm
          have hnθ : ‖((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ)‖
              = 1 := by rw [← hpx]; exact hnx
          have heq : sphProj y = Work.CoreTopology.circlePoint θ :=
            hBinj (by rw [← hxy, hpx, hbd _ hnθ])
          rw [heq, hnθ] at hpy
          exact absurd hpy (lt_irrefl 1)
        · exact hint (sphProj x) (sphProj y)
            (lt_of_le_of_ne (norm_sphProj_le_one x) hnx) hpy hxy
  · by_cases hy : 0 ≤ (y : R3) 2
    · rw [if_neg hx, if_pos hy] at hxy
      exfalso
      have hx2 : (x : R3) 2 < 0 := lt_of_not_ge hx
      by_cases hny : ‖((sphProj y : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1
      · obtain ⟨θ, hθ⟩ := Work.CoreTopology.exists_circlePoint_eq _ hny
        have hpy : sphProj y = Work.CoreTopology.circlePoint θ := Subtype.ext hθ.symm
        have hnθ : ‖((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1 := by
          rw [← hpy]; exact hny
        have heq : eB (sphProj x) = eB (Work.CoreTopology.circlePoint θ) := by
          rw [hxy, hpy, hbd _ hnθ]
        have hpx : sphProj x = Work.CoreTopology.circlePoint θ := hBinj heq
        have : (x : R3) 2 = 0 := (sphProj_norm_eq_one_iff x).1 (by rw [hpx, hnθ])
        linarith
      · have hpy : ‖((sphProj y : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ < 1 :=
          lt_of_le_of_ne (norm_sphProj_le_one y) hny
        by_cases hnx : ‖((sphProj x : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1
        · have : (x : R3) 2 = 0 := (sphProj_norm_eq_one_iff x).1 hnx
          linarith
        · exact hint (sphProj y) (sphProj x)
            (lt_of_le_of_ne (norm_sphProj_le_one y) hny)
            (lt_of_le_of_ne (norm_sphProj_le_one x) hnx) hxy.symm
    · rw [if_neg hx, if_neg hy] at hxy
      exact eq_of_sphProj_eq_of_snd_nonpos (le_of_lt (lt_of_not_ge hx))
        (le_of_lt (lt_of_not_ge hy)) (hBinj hxy)

theorem doubleDiscMap_discToUpper (eA eB : C(Metric.closedBall (0 : ℂ) 1, R3))
    (hbd : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ = 1 → eA z = eB z)
    (z : Metric.closedBall (0 : ℂ) 1) :
    doubleDiscMap eA eB hbd (discToUpper z) = eA z := by
  rw [doubleDiscMap_apply, if_pos (discToUpper_snd_nonneg z), sphProj_discToUpper]

theorem doubleDiscMap_discToLower (eA eB : C(Metric.closedBall (0 : ℂ) 1, R3))
    (hbd : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ = 1 → eA z = eB z)
    (z : Metric.closedBall (0 : ℂ) 1) :
    doubleDiscMap eA eB hbd (discToLower z) = eB z := by
  rw [doubleDiscMap_apply]
  by_cases h : 0 ≤ (discToLower z : R3) 2
  · have hv : (discToLower z : R3) 2 = 0 := le_antisymm (discToLower_snd_nonpos z) h
    have hz1 : ‖(z : ℂ)‖ = 1 := by
      rw [← sphProj_discToLower z]
      exact (sphProj_norm_eq_one_iff (discToLower z)).2 hv
    rw [if_pos h, sphProj_discToLower, hbd z hz1]
  · rw [if_neg h, sphProj_discToLower]

theorem range_doubleDiscMap (eA eB : C(Metric.closedBall (0 : ℂ) 1, R3))
    (hbd : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ = 1 → eA z = eB z) :
    Set.range (doubleDiscMap eA eB hbd) = Set.range eA ∪ Set.range eB := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    rw [doubleDiscMap_apply]
    by_cases h : 0 ≤ (x : R3) 2
    · rw [if_pos h]
      exact Or.inl ⟨sphProj x, rfl⟩
    · rw [if_neg h]
      exact Or.inr ⟨sphProj x, rfl⟩
  · rintro (⟨z, rfl⟩ | ⟨z, rfl⟩)
    · exact ⟨discToUpper z, doubleDiscMap_discToUpper eA eB hbd z⟩
    · exact ⟨discToLower z, doubleDiscMap_discToLower eA eB hbd z⟩

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
theorem isEmbeddedSphere_of_doubleDisc
    (eA eB : C(Metric.closedBall (0 : ℂ) 1, R3))
    (hAinj : Function.Injective eA) (hBinj : Function.Injective eB)
    (hbd : ∀ θ : ℝ, eA (Work.CoreTopology.circlePoint θ) = eB (Work.CoreTopology.circlePoint θ))
    (hint : ∀ z w : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ < 1 → ‖(w : ℂ)‖ < 1 →
      eA z = eB w → False) :
    Work.InnermostDisk.IsEmbeddedSphere (Set.range eA ∪ Set.range eB) := by
  have hbd' : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ = 1 → eA z = eB z := by
    intro z hz
    obtain ⟨θ, hθ⟩ := Work.CoreTopology.exists_circlePoint_eq (z : ℂ) hz
    have hz' : z = Work.CoreTopology.circlePoint θ := Subtype.ext hθ.symm
    rw [hz']
    exact hbd θ
  refine ⟨doubleDiscMap eA eB hbd', doubleDiscMap_injective eA eB hbd' hAinj hBinj hint, ?_⟩
  exact range_doubleDiscMap eA eB hbd'

end

end Work.Drive.Mono
