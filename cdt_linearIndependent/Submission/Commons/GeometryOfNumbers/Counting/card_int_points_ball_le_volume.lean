import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Order.CompletePartialOrder

namespace Commons.GeometryOfNumbers.Counting

open MeasureTheory Metric Set
open scoped ENNReal

/-!
# Counting integer points of a Euclidean ball

The elementary geometry-of-numbers bound: the number of integer points `x` in the closed
Euclidean ball of radius `R` in `ℝ^d` is at most the volume of the concentric open ball of radius
`R + √d / 2`.

The proof associates to each such integer point `x` the open unit cube centred at `x`; these cubes
are pairwise disjoint, each has volume one, and the cube centred at `x` is contained in the ball
of radius `‖x‖ + √d/2`. Hence the number of integer points equals the total volume of the cubes,
which is at most the volume of the big ball.
-/

/-- The open unit cube (side length `1`) centred at the integer point `x`, as a subset of the
model space `Fin d → ℝ` of `EuclideanSpace ℝ (Fin d)`. -/
def intUnitBox {d : ℕ} (x : Fin d → ℤ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ fun i => Set.Ioo ((x i : ℝ) - 1 / 2) ((x i : ℝ) + 1 / 2)

/-- The open unit cube (side length `1`) centred at the integer point `x` in
`EuclideanSpace ℝ (Fin d)`. -/
def intUnitCube {d : ℕ} (x : Fin d → ℤ) : Set (EuclideanSpace ℝ (Fin d)) :=
  WithLp.ofLp ⁻¹' intUnitBox x

lemma measurableSet_intUnitBox {d : ℕ} (x : Fin d → ℤ) : MeasurableSet (intUnitBox x) := by
  rw [intUnitBox]
  exact MeasurableSet.univ_pi (fun i => measurableSet_Ioo)

lemma volume_intUnitBox {d : ℕ} (x : Fin d → ℤ) : volume (intUnitBox x) = 1 := by
  rw [intUnitBox, volume_pi_pi]
  have h : ∀ i : Fin d, volume (Set.Ioo ((x i : ℝ) - 1/2) ((x i : ℝ) + 1/2)) = 1 := by
    intro i
    rw [Real.volume_Ioo]
    norm_num
  calc ∏ i : Fin d, volume (Set.Ioo ((x i : ℝ) - 1/2) ((x i : ℝ) + 1/2))
      = ∏ _i : Fin d, (1 : ℝ≥0∞) := Finset.prod_congr rfl (fun i _ => h i)
    _ = 1 := by simp

lemma measurableSet_intUnitCube {d : ℕ} (x : Fin d → ℤ) : MeasurableSet (intUnitCube x) := by
  rw [intUnitCube]
  exact (WithLp.measurable_ofLp 2 (Fin d → ℝ)) (measurableSet_intUnitBox x)

lemma volume_intUnitCube {d : ℕ} (x : Fin d → ℤ) : volume (intUnitCube x) = 1 := by
  rw [intUnitCube,
    (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
      (measurableSet_intUnitBox x).nullMeasurableSet,
    volume_intUnitBox]

lemma int_one_le_abs_cast_sub {a b : ℤ} (h : a ≠ b) : (1 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| := by
  have h0 : a - b ≠ 0 := sub_ne_zero.mpr h
  have h1 : (1 : ℤ) ≤ |a - b| := Int.one_le_abs h0
  have h2 : ((1 : ℤ) : ℝ) ≤ ((|a - b| : ℤ) : ℝ) := by exact_mod_cast h1
  rwa [Int.cast_abs, Int.cast_sub, Int.cast_one] at h2

lemma disjoint_intUnitBox {d : ℕ} {x y : Fin d → ℤ} (hxy : x ≠ y) :
    Disjoint (intUnitBox x) (intUnitBox y) := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra h
    push Not at h
    exact hxy (funext h)
  rw [Set.disjoint_left]
  intro z hzx hzy
  simp only [intUnitBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hzx hzy
  have hx : |z i - (x i : ℝ)| < 1/2 :=
    abs_lt.mpr ⟨by linarith [hzx i], by linarith [hzx i]⟩
  have hy : |z i - (y i : ℝ)| < 1/2 :=
    abs_lt.mpr ⟨by linarith [hzy i], by linarith [hzy i]⟩
  have hbig : (1 : ℝ) ≤ |(x i : ℝ) - (y i : ℝ)| := int_one_le_abs_cast_sub hi
  have htri : |(x i : ℝ) - (y i : ℝ)| ≤ |(x i : ℝ) - z i| + |z i - (y i : ℝ)| := by
    calc |(x i : ℝ) - (y i : ℝ)| = |((x i : ℝ) - z i) + (z i - (y i : ℝ))| := by
          congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hxa : |(x i : ℝ) - z i| = |z i - (x i : ℝ)| := abs_sub_comm _ _
  linarith

lemma disjoint_intUnitCube {d : ℕ} {x y : Fin d → ℤ} (hxy : x ≠ y) :
    Disjoint (intUnitCube x) (intUnitCube y) :=
  (disjoint_intUnitBox hxy).preimage WithLp.ofLp

lemma norm_toLp_intLattice {d : ℕ} (x : Fin d → ℤ) :
    ‖(WithLp.toLp 2 (fun i : Fin d => (x i : ℝ)) : EuclideanSpace ℝ (Fin d))‖ ^ 2
      = ∑ i, ((x i : ℝ)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

/-- The unit cube centred at an integer point of the ball of radius `R` is contained in the ball
of radius `R + √d / 2`. -/
lemma intUnitCube_subset_ball {d : ℕ} (hd : 0 < d) {x : Fin d → ℤ} {R : ℝ}
    (hx : (∑ i, ((x i : ℝ)) ^ 2) ≤ R^2) (hR : 0 ≤ R) :
    intUnitCube x ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (R + Real.sqrt d / 2) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  intro y hy
  rw [intUnitCube, Set.mem_preimage] at hy
  simp only [intUnitBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hy
  set w : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun i : Fin d => (x i : ℝ)) with hw
  have hwle : ‖w‖ ≤ R := by
    have h1 : ‖w‖ ^ 2 ≤ R ^ 2 := by
      rw [hw, norm_toLp_intLattice]; exact hx
    have h2 : |‖w‖| ≤ |R| := sq_le_sq.mp h1
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hR] at h2
    exact h2
  have hdist : ‖y - w‖ < Real.sqrt d / 2 := by
    have hsq : ‖y - w‖ ^ 2 = ∑ i, (y.ofLp i - (x i : ℝ))^2 := by
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hof : (y - w).ofLp i = y.ofLp i - (x i : ℝ) := by simp [hw]
      rw [hof, Real.norm_eq_abs, sq_abs]
    have hlt : ∑ i, (y.ofLp i - (x i : ℝ))^2 < (d : ℝ) * (1/4) := by
      have hsum : ∑ _i : Fin d, ((1 : ℝ)/2)^2 = (d : ℝ) * (1/4) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        norm_num
      rw [← hsum]
      refine Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := Fin d)) (fun i _ => ?_)
      have h1a : -((1 : ℝ)/2) < y.ofLp i - (x i : ℝ) := by linarith [(hy i).1]
      have h1b : y.ofLp i - (x i : ℝ) < (1 : ℝ)/2 := by linarith [(hy i).2]
      have h1 : |y.ofLp i - (x i : ℝ)| < (1 : ℝ)/2 := abs_lt.mpr ⟨h1a, h1b⟩
      have h2 : (y.ofLp i - (x i : ℝ))^2 < ((1 : ℝ)/2)^2 := by
        rw [sq_lt_sq]
        simpa using h1
      exact h2
    have hsqrt : (Real.sqrt d / 2)^2 = (d : ℝ) * (1/4) := by
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
      ring
    rw [← hsq, ← hsqrt] at hlt
    have h1 : |‖y - w‖| < |Real.sqrt d / 2| := sq_lt_sq.mp hlt
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at h1
  have hfin : ‖y‖ < R + Real.sqrt d / 2 := by
    have hle : ‖y‖ ≤ ‖w‖ + ‖y - w‖ := by
      calc ‖y‖ = ‖w + (y - w)‖ := by rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith
  simpa [Metric.mem_ball, dist_eq_norm] using hfin

/-- The set of integer points of the closed ball of radius `R` in `ℝ^d` is finite. -/
lemma finite_int_points_ball {d : ℕ} (R : ℝ) :
    {x : Fin d → ℤ | (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2}.Finite := by
  set M : ℕ := ⌈|R|⌉₊ with hM
  have hcoord : ({n : ℤ | (n : ℝ) ∈ Set.Icc (-(M : ℝ)) (M : ℝ)}).Finite := by
    refine (Set.finite_Icc (-(M : ℤ)) (M : ℤ)).subset ?_
    intro n hn
    simp only [Set.mem_ofPred_eq, Set.mem_Icc] at hn ⊢
    exact ⟨by exact_mod_cast hn.1, by exact_mod_cast hn.2⟩
  refine Set.Finite.subset (Set.Finite.pi (fun _ : Fin d => hcoord)) ?_
  intro x hx
  simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
  intro i
  have hle : ((x i : ℝ)) ^ 2 ≤ R ^ 2 :=
    le_trans (Finset.single_le_sum (fun j _ => sq_nonneg ((x j : ℝ)))
      (Finset.mem_univ i)) hx
  have h2 : |(x i : ℝ)| ≤ |R| := sq_le_sq.mp hle
  have h3 : |(x i : ℝ)| ≤ (M : ℝ) := le_trans h2 (by rw [hM]; exact Nat.le_ceil |R|)
  simp only [Set.mem_Icc]
  exact ⟨by exact_mod_cast (abs_le.mp h3).1, by exact_mod_cast (abs_le.mp h3).2⟩

theorem card_int_points_ball_le_volume {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R) :
    (Nat.card {x : Fin d → ℤ // (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2} : ℝ)
      ≤ (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d))
          (R + Real.sqrt d / 2))).toReal := by
  let S : Set (Fin d → ℤ) := {x | (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2}
  change (Nat.card S : ℝ) ≤
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (R + Real.sqrt d / 2))).toReal
  have hSfin : S.Finite := finite_int_points_ball R
  haveI : Fintype S := hSfin.fintype
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hvol_union : volume (⋃ x ∈ hSfin.toFinset, intUnitCube x) = (hSfin.toFinset.card : ℝ≥0∞) := by
    rw [measure_biUnion_finset (fun x _ y _ hxy => disjoint_intUnitCube hxy)
      (fun x _ => measurableSet_intUnitCube x)]
    have h1 : ∑ p ∈ hSfin.toFinset, volume (intUnitCube p)
        = ∑ _p ∈ hSfin.toFinset, (1 : ℝ≥0∞) :=
      Finset.sum_congr rfl (fun p _ => volume_intUnitCube p)
    rw [h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsub : (⋃ x ∈ hSfin.toFinset, intUnitCube x)
      ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (R + Real.sqrt d / 2) := by
    refine Set.iUnion_subset (fun x => Set.iUnion_subset (fun hx => ?_))
    exact intUnitCube_subset_ball hd ((Set.Finite.mem_toFinset hSfin).mp hx) hR.le
  have hfin_ball : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (R + Real.sqrt d / 2))
      ≠ ⊤ := by
    rw [EuclideanSpace.volume_ball (Fin d) 0 (R + Real.sqrt d / 2)]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have h1 : (hSfin.toFinset.card : ℝ≥0∞)
      ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (R + Real.sqrt d / 2)) := by
    rw [← hvol_union]
    exact measure_mono hsub
  have h2 : ((hSfin.toFinset.card : ℝ≥0∞)).toReal
      ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (R + Real.sqrt d / 2))).toReal :=
    ENNReal.toReal_mono hfin_ball h1
  have h3 : hSfin.toFinset.card = Nat.card S := by
    rw [hSfin.card_toFinset, Nat.card_eq_fintype_card]
  calc (Nat.card S : ℝ) = ((hSfin.toFinset.card : ℝ≥0∞)).toReal := by
        rw [ENNReal.toReal_natCast, h3]
    _ ≤ _ := h2

end Commons.GeometryOfNumbers.Counting