import Mathlib
import Submission.Commons.GeometryOfNumbers.Counting.card_int_points_ball_le_volume
import Submission.Commons.Measure.EuclideanSpace.setIntegral_annulus_radial
import Submission.Commons.Measure.EuclideanSpace.volume_ball_add_two
import Submission.Commons.Measure.EuclideanSpace.volume_ball_succ_integral
import Submission.Commons.MeasureTheory.Integral.sum_eq_integral_card_filter
import Submission.Commons.Analysis.Integral.integral_sq_sub_sq_rpow
import Submission.Commons.Analysis.Integral.sum_Icc_abs_le_integral_of_antitone
import Submission.Commons.Analysis.Gaussian.shell_integral_tail_le
import Submission.Commons.GeometryOfNumbers.Counting.lattice_log_sum_bound

namespace Commons.GeometryOfNumbers.Counting

open _root_.MeasureTheory Metric
open scoped ENNReal

noncomputable section

/-!
# Counting lattice points of an annulus with a monotone radial weight

The main result of this file bounds `∑_{x ∈ ℤ^d, r < ‖x‖ ≤ T} g ‖x‖` for a nonnegative
nonincreasing weight `g` by a radial integral over the annulus of radii `r - √d/2`,
`T + √d/2`.

The proof associates to each lattice point `x` of the annulus its unit cube `intUnitCube x`
(from `card_int_points_ball_le_volume`).  On that cube the weight `g (max (‖y‖ - √d/2) 0)`
dominates `g ‖x‖`, and the cube is contained in the annulus of radii `r - √d/2` and
`T + √d/2`; the polar-coordinate formula `setIntegral_annulus_radial` then evaluates the
integral.
-/

/-- The lattice point `x : Fin d → ℤ` as a point of `EuclideanSpace ℝ (Fin d)`. -/
def intVec {d : ℕ} (x : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (x i : ℝ))

@[simp] lemma intVec_apply {d : ℕ} (x : Fin d → ℤ) (i : Fin d) :
    intVec x i = (x i : ℝ) := rfl

lemma norm_intVec_sq {d : ℕ} (x : Fin d → ℤ) :
    ‖intVec x‖ ^ 2 = ∑ i, ((x i : ℝ)) ^ 2 := norm_toLp_intLattice x

/-- The radial weight `y ↦ g (max (‖y‖ - √d/2) 0)`. -/
def radialWeight {d : ℕ} (g : ℝ → ℝ) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  g (max (‖y‖ - Real.sqrt d / 2) 0)

lemma antitone_radialWeight {d : ℕ} (g : ℝ → ℝ)
    (hmono : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a) :
    Antitone (fun u : ℝ => g (max (u - Real.sqrt d / 2) 0)) := by
  intro u v huv
  exact hmono _ _ (le_max_right _ _)
    (max_le_max (sub_le_sub_right huv _) le_rfl)

lemma measurable_radialWeight {d : ℕ} (g : ℝ → ℝ)
    (hmono : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a) :
    Measurable (radialWeight (d := d) g) := by
  unfold radialWeight
  exact (antitone_radialWeight (d := d) g hmono).measurable.comp (by fun_prop)

lemma antitone_gmax (g : ℝ → ℝ) (s : ℝ)
    (hmono : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a) :
    Antitone (fun u : ℝ => g (max (u - s) 0)) := by
  intro u v huv
  exact hmono _ _ (le_max_right _ _) (max_le_max (sub_le_sub_right huv s) le_rfl)

lemma measurable_gmax (g : ℝ → ℝ) (s : ℝ)
    (hmono : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a) :
    Measurable (fun u : ℝ => g (max (u - s) 0)) :=
  (antitone_gmax g s hmono).measurable

lemma le_g_zero (g : ℝ → ℝ) (hmono : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a) {u : ℝ}
    (hu : 0 ≤ u) : g u ≤ g 0 := hmono 0 u le_rfl hu

lemma radialWeight_le {d : ℕ} (g : ℝ → ℝ)
    (hmono : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a) (y : EuclideanSpace ℝ (Fin d)) :
    radialWeight (d := d) g y ≤ g 0 := le_g_zero g hmono (le_max_right _ _)

lemma radialWeight_nonneg {d : ℕ} (g : ℝ → ℝ) (hpos : ∀ a, 0 ≤ g a)
    (y : EuclideanSpace ℝ (Fin d)) : 0 ≤ radialWeight (d := d) g y := hpos _

/-- The unit cube around a lattice point is contained in the ball of radius `√d/2` about it. -/
lemma intUnitCube_subset_ball_center {d : ℕ} (hd : 0 < d) (x : Fin d → ℤ) :
    intUnitCube x ⊆ Metric.ball (intVec x) (Real.sqrt d / 2) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  intro y hy
  rw [intUnitCube, Set.mem_preimage] at hy
  simp only [intUnitBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hy
  rw [Metric.mem_ball, dist_eq_norm]
  have hsq : ‖y - intVec x‖ ^ 2 = ∑ i, (y i - (x i : ℝ)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h1 : (y - intVec x) i = y i - (x i : ℝ) := by simp [intVec]
    rw [h1, Real.norm_eq_abs, sq_abs]
  have hsqrt : (Real.sqrt d / 2) ^ 2 = (d : ℝ) * (1/4) := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg d)]; ring
  have hsum : ∑ _i : Fin d, ((1 : ℝ)/2)^2 = (d : ℝ) * (1/4) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
  have hlt : ‖y - intVec x‖ ^ 2 < (Real.sqrt d / 2) ^ 2 := by
    rw [hsq, hsqrt, ← hsum]
    refine Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := Fin d)) (fun i _ => ?_)
    have h2 : |y i - (x i : ℝ)| < (1 : ℝ)/2 :=
      abs_lt.mpr ⟨by linarith [(hy i).1], by linarith [(hy i).2]⟩
    rw [sq_lt_sq]; simpa using h2
  have h1 : |‖y - intVec x‖| < |Real.sqrt d / 2| := sq_lt_sq.mp hlt
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at h1

lemma norm_lower_of_mem_intUnitCube {d : ℕ} (hd : 0 < d) (x : Fin d → ℤ)
    {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ intUnitCube x) :
    ‖intVec x‖ - Real.sqrt d / 2 < ‖y‖ := by
  have h := intUnitCube_subset_ball_center hd x hy
  rw [Metric.mem_ball, dist_eq_norm] at h
  have h3 : ‖intVec x‖ ≤ ‖intVec x - y‖ + ‖y‖ := by
    calc ‖intVec x‖ = ‖(intVec x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖intVec x - y‖ + ‖y‖ := norm_add_le _ _
  rw [norm_sub_rev] at h3
  linarith

lemma upper_of_mem_intUnitCube {d : ℕ} (hd : 0 < d) (x : Fin d → ℤ)
    {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ intUnitCube x) :
    ‖y‖ < ‖intVec x‖ + Real.sqrt d / 2 := by
  have hball := intUnitCube_subset_ball (d := d) hd (x := x) (R := ‖intVec x‖)
    (by rw [norm_intVec_sq]) (norm_nonneg _)
  have := hball hy
  rwa [Metric.mem_ball, dist_zero_right] at this

/-- On the unit cube centred at a lattice point `x`, the weight dominates `g ‖x‖`. -/
lemma le_radialWeight_of_mem_intUnitCube {d : ℕ} (hd : 0 < d) (g : ℝ → ℝ)
    (hmono : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a) (x : Fin d → ℤ)
    {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ intUnitCube x) :
    g ‖intVec x‖ ≤ radialWeight (d := d) g y := by
  have hy' := upper_of_mem_intUnitCube hd x hy
  unfold radialWeight
  refine hmono _ _ (le_max_right _ _) ?_
  rw [max_le_iff]
  exact ⟨by linarith, norm_nonneg _⟩

lemma integrableOn_radialWeight_cube {d : ℕ} (g : ℝ → ℝ)
    (hmono : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a) (hpos : ∀ a, 0 ≤ g a)
    (x : Fin d → ℤ) :
    IntegrableOn (radialWeight (d := d) g) (intUnitCube x) volume := by
  refine IntegrableOn.of_bound ?_ ?_ (g 0) ?_
  · rw [volume_intUnitCube]; exact ENNReal.one_lt_top
  · exact (measurable_radialWeight g hmono).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (radialWeight_nonneg g hpos y)]
    exact radialWeight_le g hmono y

lemma integrableOn_const_cube {d : ℕ} (c : ℝ) (x : Fin d → ℤ) :
    IntegrableOn (fun _ : EuclideanSpace ℝ (Fin d) => c) (intUnitCube x) volume := by
  refine IntegrableOn.of_bound ?_ ?_ ‖c‖ ?_
  · rw [volume_intUnitCube]; exact ENNReal.one_lt_top
  · exact aestronglyMeasurable_const
  · filter_upwards with y
    exact le_rfl

lemma value_le_integral_intUnitCube {d : ℕ} (hd : 0 < d) (g : ℝ → ℝ)
    (hmono : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a) (hpos : ∀ a, 0 ≤ g a)
    (x : Fin d → ℤ) :
    g ‖intVec x‖ ≤ ∫ y in intUnitCube x, radialWeight (d := d) g y := by
  have hle : (fun _ : EuclideanSpace ℝ (Fin d) => g ‖intVec x‖)
      ≤ᵐ[volume.restrict (intUnitCube x)] radialWeight (d := d) g := by
    filter_upwards [ae_restrict_mem (measurableSet_intUnitCube x)] with y hy
    exact le_radialWeight_of_mem_intUnitCube hd g hmono x hy
  have hmono_int := integral_mono_ae (integrableOn_const_cube (g ‖intVec x‖) x)
    (integrableOn_radialWeight_cube g hmono hpos x) hle
  rw [setIntegral_const, measureReal_def, volume_intUnitCube, ENNReal.toReal_one,
    one_smul] at hmono_int
  exact hmono_int

/-- **The cube argument.**  For any finite set `F` of lattice points, the sum of `g ‖x‖` over `F`
is at most the integral of the weight over the union of the unit cubes. -/
lemma sum_le_integral_union {d : ℕ} (hd : 0 < d) (g : ℝ → ℝ)
    (hmono : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a) (hpos : ∀ a, 0 ≤ g a)
    (F : Finset (Fin d → ℤ)) :
    ∑ x ∈ F, g ‖intVec x‖ ≤ ∫ y in ⋃ x ∈ F, intUnitCube x, radialWeight (d := d) g y := by
  have hdisj : (F : Set (Fin d → ℤ)).Pairwise (Function.onFun Disjoint (intUnitCube (d := d))) := by
    intro x _ y _ hxy
    exact disjoint_intUnitCube (by simpa using hxy)
  have hunion := integral_biUnion_finset (μ := volume) F
      (fun i _ => measurableSet_intUnitCube i) hdisj
      (fun i _ => integrableOn_radialWeight_cube g hmono hpos i)
  rw [hunion]
  exact Finset.sum_le_sum (fun x _ => value_le_integral_intUnitCube hd g hmono hpos x)

/-- The half-open annulus of radii `a ≤ ‖y‖ < b`. -/
def annulusSet {d : ℕ} (a b : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {y | a ≤ ‖y‖ ∧ ‖y‖ < b}

lemma measurableSet_annulusSet {d : ℕ} (a b : ℝ) : MeasurableSet (annulusSet (d := d) a b) :=
  (measurableSet_le measurable_const continuous_norm.measurable).inter
    (measurableSet_lt continuous_norm.measurable measurable_const)

lemma annulusSet_subset_ball {d : ℕ} (a R : ℝ) :
    annulusSet (d := d) a R ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R := by
  intro y hy
  rw [Metric.mem_ball, dist_zero_right]
  exact hy.2

lemma integrableOn_radialWeight_ball {d : ℕ} (g : ℝ → ℝ)
    (hmono : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a) (hpos : ∀ a, 0 ≤ g a) (R : ℝ) :
    IntegrableOn (radialWeight (d := d) g)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R) volume := by
  refine IntegrableOn.of_bound ?_ ?_ (g 0) ?_
  · exact measure_ball_lt_top
  · exact (measurable_radialWeight g hmono).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (radialWeight_nonneg g hpos y)]
    exact radialWeight_le g hmono y

lemma integrableOn_radialWeight_annulus {d : ℕ} (g : ℝ → ℝ)
    (hmono : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a) (hpos : ∀ a, 0 ≤ g a)
    (a R : ℝ) :
    IntegrableOn (radialWeight (d := d) g) (annulusSet (d := d) a R) volume := by
  refine IntegrableOn.of_bound ?_ ?_ (g 0) ?_
  · exact lt_of_le_of_lt (measure_mono (annulusSet_subset_ball a R)) measure_ball_lt_top
  · exact (measurable_radialWeight g hmono).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (radialWeight_nonneg g hpos y)]
    exact radialWeight_le g hmono y

/-- The union of the unit cubes of lattice points of the ball of radius `T` lies in the ball of
radius `T + √d/2`. -/
lemma integral_union_le_ball {d : ℕ} (hd : 0 < d) (g : ℝ → ℝ)
    (hmono : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a) (hpos : ∀ a, 0 ≤ g a)
    {T : ℝ} (F : Finset (Fin d → ℤ)) (hF : ∀ x ∈ F, ‖intVec x‖ ≤ T) :
    ∫ y in ⋃ x ∈ F, intUnitCube x, radialWeight (d := d) g y
      ≤ ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (T + Real.sqrt d / 2),
          radialWeight (d := d) g y := by
  refine setIntegral_mono_set (integrableOn_radialWeight_ball g hmono hpos _) ?_ ?_
  · filter_upwards with y
    exact radialWeight_nonneg g hpos y
  · refine Filter.Eventually.of_forall (fun y hy => ?_)
    change y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (T + Real.sqrt d / 2)
    change y ∈ ⋃ x ∈ F, intUnitCube x at hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨x, hx⟩ := hy
    rw [Set.mem_iUnion] at hx
    obtain ⟨hxF, hxy⟩ := hx
    have h2 := upper_of_mem_intUnitCube hd x hxy
    rw [Metric.mem_ball, dist_zero_right]
    linarith [hF x hxF]

/-- The union of the unit cubes of lattice points in the annulus `r < ‖x‖ ≤ T` (with
`√d/2 ≤ r`) lies in the annulus of radii `r - √d/2`, `T + √d/2`. -/
lemma integral_union_le_annulus {d : ℕ} (hd : 0 < d) (g : ℝ → ℝ)
    (hmono : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a) (hpos : ∀ a, 0 ≤ g a)
    {r T : ℝ} (hrT : r ≤ T)
    (F : Finset (Fin d → ℤ)) (hF : ∀ x ∈ F, ‖intVec x‖ ≤ T)
    (hFr : ∀ x ∈ F, r < ‖intVec x‖) :
    ∫ y in ⋃ x ∈ F, intUnitCube x, radialWeight (d := d) g y
      ≤ ∫ y in annulusSet (r - Real.sqrt d / 2) (T + Real.sqrt d / 2),
          radialWeight (d := d) g y := by
  have hle : r - Real.sqrt d / 2 ≤ T + Real.sqrt d / 2 := by
    have hs : 0 ≤ Real.sqrt d / 2 := by positivity
    linarith
  refine setIntegral_mono_set
    (integrableOn_radialWeight_annulus g hmono hpos _ _) ?_ ?_
  · filter_upwards with y
    exact radialWeight_nonneg g hpos y
  · refine Filter.Eventually.of_forall (fun y hy => ?_)
    change r - Real.sqrt d / 2 ≤ ‖y‖ ∧ ‖y‖ < T + Real.sqrt d / 2
    change y ∈ ⋃ x ∈ F, intUnitCube x at hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨x, hx⟩ := hy
    rw [Set.mem_iUnion] at hx
    obtain ⟨hxF, hxy⟩ := hx
    refine ⟨?_, ?_⟩
    · have hlow := norm_lower_of_mem_intUnitCube hd x hxy
      have hxr := hFr x hxF
      linarith
    · have h2 := upper_of_mem_intUnitCube hd x hxy
      linarith [hF x hxF]


/-- The polar-coordinate evaluation of the integral of the radial weight over an annulus. -/
lemma integral_annulus_radial_eq {d : ℕ} (hd : 0 < d) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (g : ℝ → ℝ) :
    ∫ y in annulusSet (d := d) a b, radialWeight (d := d) g y
      = (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
          * ∫ u in a..b, u ^ (d - 1) * g (max (u - Real.sqrt d / 2) 0) := by
  have h := Commons.Measure.EuclideanSpace.setIntegral_annulus_radial (n := d) (by omega) ha hab
    (fun u => g (max (u - Real.sqrt d / 2) 0))
  simpa [annulusSet, radialWeight] using h


/-- The number of lattice points of `ℤ^d` in the closed Euclidean ball of radius `T`. -/
def cardBall (d : ℕ) (T : ℝ) : ℕ := (finite_int_points_ball (d := d) T).toFinset.card

/-- The sum of squares decomposes when a last coordinate is appended. -/
lemma sum_sq_snoc {d : ℕ} (y : Fin d → ℤ) (k : ℤ) :
    (∑ i : Fin (d + 1), (((Fin.snoc y k : Fin (d + 1) → ℤ)) i : ℝ) ^ 2)
      = (∑ i : Fin d, ((y i : ℝ)) ^ 2) + (k : ℝ) ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

lemma cardBall_succ_index {T : ℝ} (hT : 0 ≤ T) (k : ℤ) :
    (k : ℝ) ^ 2 ≤ T ^ 2 ↔ k ∈ Finset.Icc (-⌊T⌋) ⌊T⌋ := by
  rw [Finset.mem_Icc]
  constructor
  · intro hk
    have h1 : |(k : ℝ)| ≤ T := by
      have h := sq_le_sq.mp hk
      rwa [abs_of_nonneg hT] at h
    rw [abs_le] at h1
    obtain ⟨h1a, h1b⟩ := h1
    refine ⟨?_, Int.le_floor.mpr h1b⟩
    have h5 : ((-k : ℤ) : ℝ) ≤ T := by push_cast; linarith
    have h2 : -k ≤ ⌊T⌋ := Int.le_floor.mpr h5
    omega
  · intro hk
    obtain ⟨h1, h2⟩ := hk
    have h3 : -T ≤ (k : ℝ) := by
      have h : (-(⌊T⌋ : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
      linarith [Int.floor_le T]
    have h4 : (k : ℝ) ≤ T := by
      have h : (k : ℝ) ≤ ((⌊T⌋ : ℤ) : ℝ) := by exact_mod_cast h2
      linarith [Int.floor_le T]
    rw [sq_le_sq, abs_of_nonneg hT]
    exact abs_le.mpr ⟨h3, h4⟩

/-- **Slicing of a lattice ball.**  Splitting off the last coordinate, the number of lattice
points of the ball in `ℤ^{d+1}` of radius `T` is the sum over the value `k` of the last
coordinate of the numbers of lattice points of the ball in `ℤ^d` of radius `√(T² - k²)`. -/
lemma cardBall_succ (d : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    cardBall (d + 1) T
      = ∑ k ∈ Finset.Icc (-⌊T⌋) ⌊T⌋,
          cardBall d (Real.sqrt (T ^ 2 - (k : ℝ) ^ 2)) := by
  classical
  have hmemF : ∀ x : Fin (d + 1) → ℤ, x ∈ (finite_int_points_ball (d := d + 1) T).toFinset ↔
      (∑ i, ((x i : ℝ)) ^ 2) ≤ T ^ 2 :=
    fun x => Set.Finite.mem_toFinset _
  -- the image of the last-coordinate map is exactly the admissible range
  have himg : Finset.image (fun x : Fin (d + 1) → ℤ => x (Fin.last d))
      (finite_int_points_ball (d := d + 1) T).toFinset = Finset.Icc (-⌊T⌋) ⌊T⌋ := by
    ext k
    rw [Finset.mem_image, ← cardBall_succ_index hT k]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact le_trans (Finset.single_le_sum (fun i _ => sq_nonneg ((x i : ℝ)))
        (Finset.mem_univ (Fin.last d))) ((hmemF x).mp hx)
    · intro hk
      refine ⟨Fin.snoc (α := fun _ : Fin (d + 1) => ℤ) (fun _ : Fin d => (0 : ℤ)) k,
        ?_, by simp⟩
      rw [hmemF]
      have hsum : (∑ i : Fin (d + 1),
          (((Fin.snoc (α := fun _ : Fin (d + 1) => ℤ) (fun _ : Fin d => (0 : ℤ)) k)
            i : ℤ) : ℝ) ^ 2) = (k : ℝ) ^ 2 := by
        rw [sum_sq_snoc]; simp
      rw [hsum]
      exact hk
  -- the cardinality of each fibre
  have hfiber : ∀ k ∈ Finset.Icc (-⌊T⌋) ⌊T⌋,
      ((finite_int_points_ball (d := d + 1) T).toFinset.filter
          (fun x => x (Fin.last d) = k)).card
        = cardBall d (Real.sqrt (T ^ 2 - (k : ℝ) ^ 2)) := by
    intro k hk
    have hk0 : 0 ≤ T ^ 2 - (k : ℝ) ^ 2 :=
      by linarith [(cardBall_succ_index hT k).mpr hk]
    rw [cardBall]
    refine Finset.card_bij (fun x _ => fun i : Fin d => x i.castSucc) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨hx1, hx2⟩ := hx
      refine (Set.Finite.mem_toFinset (finite_int_points_ball (d := d)
        (Real.sqrt (T ^ 2 - (k : ℝ) ^ 2)))).mpr ?_
      show (∑ i : Fin d, ((x i.castSucc : ℝ)) ^ 2) ≤ (Real.sqrt (T ^ 2 - (k : ℝ) ^ 2)) ^ 2
      rw [Real.sq_sqrt hk0]
      have hsum := Fin.sum_univ_castSucc (fun i : Fin (d + 1) => ((x i : ℝ)) ^ 2)
      have hlast : ((x (Fin.last d) : ℝ)) ^ 2 = (k : ℝ) ^ 2 := by rw [hx2]
      linarith [(hmemF x).mp hx1, hsum, hlast]
    · intro x1 hx1 x2 hx2 heq
      rw [Finset.mem_filter] at hx1 hx2
      funext i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact congrFun heq j
      · rw [hx1.2, hx2.2]
    · intro y hy
      have hy' : (∑ i : Fin d, ((y i : ℝ)) ^ 2) ≤ (Real.sqrt (T ^ 2 - (k : ℝ) ^ 2)) ^ 2 :=
        (Set.Finite.mem_toFinset (finite_int_points_ball (d := d)
          (Real.sqrt (T ^ 2 - (k : ℝ) ^ 2)))).mp hy
      refine ⟨Fin.snoc y k, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨?_, by simp⟩
        rw [hmemF, sum_sq_snoc]
        linarith [hy', Real.sq_sqrt hk0]
      · funext i
        simp [Fin.snoc_castSucc]
  rw [cardBall]
  rw [Finset.card_eq_sum_card_image (fun x : Fin (d + 1) → ℤ => x (Fin.last d))
    (finite_int_points_ball (d := d + 1) T).toFinset, himg]
  exact Finset.sum_congr rfl hfiber

/-- Volume of the open unit ball of `ℝ^d`. -/
def volUnitBall (d : ℕ) : ℝ :=
  (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal

lemma volUnitBall_eq (d : ℕ) (hd : 1 ≤ d) :
    volUnitBall d = (Real.sqrt Real.pi) ^ d / Real.Gamma ((d : ℝ) / 2 + 1) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  rw [volUnitBall, EuclideanSpace.volume_ball (Fin d) 0 1, Fintype.card_fin]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1),
    ENNReal.toReal_ofReal (by
      have hpos : 0 < Real.Gamma ((d:ℝ)/2 + 1) := Real.Gamma_pos_of_pos (by positivity)
      positivity)]
  simp

lemma volUnitBall_one : volUnitBall 1 = 2 := by
  rw [volUnitBall_eq 1 le_rfl]
  rw [show (((1:ℕ):ℝ)/2 + 1) = ((1:ℝ)/2 + 1) by norm_num]
  rw [Real.Gamma_add_one (by norm_num : (1/2:ℝ) ≠ 0), Real.Gamma_one_half_eq]
  rw [pow_one]
  have h : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp

lemma volUnitBall_two : volUnitBall 2 = Real.pi := by
  rw [volUnitBall_eq 2 (by norm_num)]
  norm_num [Real.Gamma_two, pow_two, Real.sq_sqrt Real.pi_nonneg]

lemma volUnitBall_pos (d : ℕ) : 0 < volUnitBall d :=
  Commons.Analysis.Gaussian.volume_unitBall_toReal_pos d

lemma volUnitBall_add_two (n : ℕ) (hn : 1 ≤ n) :
    volUnitBall (n + 2) = 2 * Real.pi / ((n : ℝ) + 2) * volUnitBall n :=
  Commons.Measure.EuclideanSpace.volume_ball_add_two n hn

/-- Auxiliary real algebra for the volume comparison. -/
lemma aux_sqrt (a b M : ℝ) (hb : 0 ≤ b) (hM : 0 < M)
    (hIH : 2 * a ≤ b * Real.sqrt (M - 1))
    (hsq : Real.sqrt (M - 1) * (M + 1) ≤ M * Real.sqrt (M + 1)) :
    2 * (2 * Real.pi / M * a) ≤ (2 * Real.pi / (M + 1) * b) * Real.sqrt (M + 1) := by
  have hM1 : 0 < M + 1 := by linarith
  have hstep : 2 * a * (M + 1) ≤ b * (M * Real.sqrt (M + 1)) := by
    have hA : 2 * a * (M + 1) ≤ b * Real.sqrt (M - 1) * (M + 1) := by
      have h := mul_le_mul_of_nonneg_right hIH (le_of_lt hM1)
      linarith [h]
    have hB : b * Real.sqrt (M - 1) * (M + 1) ≤ b * (M * Real.sqrt (M + 1)) := by
      have h := mul_le_mul_of_nonneg_left hsq hb
      linarith [h]
    linarith [hA, hB]
  have hcore : 4 * Real.pi * a * (M + 1) ≤ 2 * Real.pi * b * (M * Real.sqrt (M + 1)) := by
    calc 4 * Real.pi * a * (M + 1) = 2 * Real.pi * (2 * a * (M + 1)) := by ring
      _ ≤ 2 * Real.pi * (b * (M * Real.sqrt (M + 1))) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 2 * Real.pi * b * (M * Real.sqrt (M + 1)) := by ring
  have hEq1 : 2 * (2 * Real.pi / M * a) * (M * (M + 1)) = 4 * Real.pi * a * (M + 1) := by
    field_simp
    ring
  have hEq2 : (2 * Real.pi / (M + 1) * b) * Real.sqrt (M + 1) * (M * (M + 1))
      = 2 * Real.pi * b * (M * Real.sqrt (M + 1)) := by
    field_simp
    try ring
  refine le_of_mul_le_mul_right ?_ (show (0:ℝ) < M * (M + 1) by positivity)
  rw [hEq1, hEq2]
  exact hcore


/-- (A): `2 V_m ≤ V_{m+1} √(m+1)`. -/
lemma two_mul_volUnitBall_le_succ (m : ℕ) (hm : 1 ≤ m) :
    2 * volUnitBall m ≤ volUnitBall (m + 1) * Real.sqrt ((m : ℝ) + 1) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 3 with h3 | h3
    · interval_cases m
      · rw [volUnitBall_one, volUnitBall_two, show (((1:ℕ)):ℝ)+1 = 2 by norm_num]
        nlinarith [Real.pi_gt_three, Real.sqrt_nonneg 2,
          Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
      · rw [volUnitBall_two, volUnitBall_add_two 1 le_rfl, volUnitBall_one,
          show (((2:ℕ)):ℝ)+1 = 3 by norm_num]
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.pi_pos]
    · have hIH := ih (m - 2) (by omega) (by omega : 1 ≤ m - 2)
      have hrec1 := volUnitBall_add_two (m - 2) (by omega)
      have hrec2 := volUnitBall_add_two (m - 1) (by omega)
      rw [show m - 2 + 2 = m by omega] at hrec1
      rw [show m - 1 + 2 = m + 1 by omega] at hrec2
      rw [show (((m-2:ℕ)):ℝ) + 2 = (m:ℝ) by
            rw [Nat.cast_sub (by omega : 2 ≤ m)]; push_cast; ring] at hrec1
      rw [show (((m-1:ℕ)):ℝ) + 2 = (m:ℝ) + 1 by
            rw [Nat.cast_sub (by omega : 1 ≤ m)]; push_cast; ring] at hrec2
      have hIH' : 2 * volUnitBall (m-2) ≤ volUnitBall (m-1) * Real.sqrt ((m:ℝ) - 1) := by
        rw [show m - 2 + 1 = m - 1 by omega] at hIH
        rwa [show (((m-2:ℕ)):ℝ) + 1 = (m:ℝ) - 1 by
            rw [Nat.cast_sub (by omega : 2 ≤ m)]; push_cast; ring] at hIH
      have hsq : Real.sqrt ((m:ℝ) - 1) * ((m:ℝ) + 1) ≤ (m:ℝ) * Real.sqrt ((m:ℝ) + 1) := by
        have h1' : (0:ℝ) ≤ (m:ℝ) - 1 := by
          have : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
          linarith
        have h2' : (0:ℝ) ≤ (m:ℝ) + 1 := by positivity
        have hs : (Real.sqrt ((m:ℝ)-1) * ((m:ℝ)+1))^2 ≤ ((m:ℝ) * Real.sqrt ((m:ℝ)+1))^2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt h1', Real.sq_sqrt h2']
          nlinarith
        have h2 := sq_le_sq.mp hs
        rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h2
      have hMb : (0:ℝ) < (m:ℝ) := by
        have : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
        linarith
      rw [hrec1, hrec2]
      exact aux_sqrt _ _ _ (le_of_lt (volUnitBall_pos (m-1))) hMb hIH' hsq


/-- (ii) auxiliary: iterated volume comparison. -/
lemma volUnitBall_le_add_mul_pow (k m : ℕ) (hm : 1 ≤ m) :
    volUnitBall m ≤ volUnitBall (m + k) * (Real.sqrt (((m + k : ℕ) : ℝ)) / 2) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show m + (k + 1) = (m + k) + 1 by omega, pow_succ]
    have hA := two_mul_volUnitBall_le_succ (m + k) (by omega)
    have hstep : volUnitBall (m + k) ≤ volUnitBall (m + k + 1) * (Real.sqrt (((m + k : ℕ) : ℝ) + 1) / 2) := by
      linarith
    have hcast : (((m + k : ℕ) : ℝ) + 1) = (((m + k + 1 : ℕ) : ℝ)) := by push_cast; ring
    rw [hcast] at hstep
    have hs : Real.sqrt (((m + k : ℕ) : ℝ)) ≤ Real.sqrt (((m + k + 1 : ℕ) : ℝ)) := by
      apply Real.sqrt_le_sqrt
      push_cast
      linarith
    have hp : (Real.sqrt (((m + k : ℕ) : ℝ)) / 2) ^ k
        ≤ (Real.sqrt (((m + k + 1 : ℕ) : ℝ)) / 2) ^ k := by
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)]
      exact hs
    calc volUnitBall m
        ≤ volUnitBall (m + k) * (Real.sqrt (((m + k : ℕ) : ℝ)) / 2) ^ k := ih
      _ ≤ (volUnitBall (m + k + 1) * (Real.sqrt (((m + k + 1 : ℕ) : ℝ)) / 2))
            * (Real.sqrt (((m + k + 1 : ℕ) : ℝ)) / 2) ^ k := by
            exact mul_le_mul hstep hp (pow_nonneg (by positivity) k)
              (mul_nonneg (le_of_lt (volUnitBall_pos _)) (by positivity))
      _ = volUnitBall ((m + k) + 1) * ((Real.sqrt (((m + k + 1 : ℕ) : ℝ)) / 2) ^ k
            * (Real.sqrt (((m + k + 1 : ℕ) : ℝ)) / 2)) := by ring
      _ = volUnitBall (((m + k) + 1)) * (Real.sqrt (((m + k + 1 : ℕ) : ℝ)) / 2) ^ (k + 1) := by
            rw [pow_succ]

/-- (ii) -/
lemma volUnitBall_le_mul_pow (m d : ℕ) (hm : 1 ≤ m) (hmd : m ≤ d) :
    volUnitBall m ≤ volUnitBall d * (Real.sqrt (d : ℝ) / 2) ^ (d - m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmd
  have h := volUnitBall_le_add_mul_pow k m hm
  have hk : m + k - m = k := by omega
  simpa [hk] using h

/-- The number of lattice points in the 1-dimensional ball. -/
lemma cardBall_one_eq (R : ℝ) (hR : 0 ≤ R) :
    (cardBall 1 R : ℝ) = 2 * (⌊R⌋ : ℝ) + 1 := by
  rw [cardBall]
  have hcard : ((Finset.Icc (-⌊R⌋) ⌊R⌋).card : ℤ) = ⌊R⌋ + 1 - (-⌊R⌋) :=
    Int.card_Icc_of_le (-⌊R⌋) ⌊R⌋ (by have := Int.floor_nonneg.mpr hR; omega)
  have hb : ((Finset.Icc (-⌊R⌋) ⌊R⌋).card : ℝ) = 2 * (⌊R⌋ : ℝ) + 1 := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hcard
    push_cast at this
    linarith [this]
  rw [← hb]
  congr 1
  refine Finset.card_bij (fun (x : Fin 1 → ℤ) _ => x 0) ?_ ?_ ?_
  · intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    simp only [Set.mem_ofPred_eq, Fin.sum_univ_one] at hx
    rw [Finset.mem_Icc]
    have h2 : |(x 0 : ℝ)| ≤ R := by
      have h := sq_le_sq.mp hx
      rwa [abs_of_nonneg hR] at h
    rw [abs_le] at h2
    refine ⟨?_, Int.le_floor.mpr h2.2⟩
    have h3 : ((-(x 0) : ℤ) : ℝ) ≤ R := by push_cast; linarith [h2.1]
    have h4 : -(x 0) ≤ ⌊R⌋ := Int.le_floor.mpr h3
    omega
  · intro x1 _ x2 _ heq
    funext i
    fin_cases i
    exact heq
  · intro y hy
    rw [Finset.mem_Icc] at hy
    refine ⟨fun _ => y, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    simp only [Set.mem_ofPred_eq, Fin.sum_univ_one]
    have h1 : (y : ℝ) ≤ R := le_trans (by exact_mod_cast hy.2) (Int.floor_le R)
    have h3 : (-y : ℤ) ≤ ⌊R⌋ := by omega
    have h4 : ((-y : ℤ) : ℝ) ≤ (⌊R⌋ : ℝ) := by exact_mod_cast h3
    push_cast at h4
    have h2 : -(y : ℝ) ≤ R := by linarith [h4, Int.floor_le R]
    nlinarith [h1, h2]

lemma cardBall_one_le (R : ℝ) (hR : 0 ≤ R) : (cardBall 1 R : ℝ) ≤ 2 * R + 1 := by
  rw [cardBall_one_eq R hR]
  linarith [Int.floor_le R]

/-- Slicing a lattice ball along the last coordinate: the number of points is the sum over the
first `d` coordinates of the number of admissible last coordinates. -/
lemma cardBall_succ_fiber (d : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    cardBall (d + 1) T
      = ∑ x' ∈ (Commons.GeometryOfNumbers.Counting.finite_int_points_ball (d := d) T).toFinset,
          cardBall 1 (Real.sqrt (T ^ 2 - ∑ i, ((x' i : ℝ)) ^ 2)) := by
  classical
  rw [cardBall]
  rw [Finset.card_eq_sum_card_image (fun x : Fin (d + 1) → ℤ => fun i : Fin d => x i.castSucc)]
  have himg : Finset.image (fun x : Fin (d + 1) → ℤ => fun i : Fin d => x i.castSucc)
        (Commons.GeometryOfNumbers.Counting.finite_int_points_ball (d := d + 1) T).toFinset
      = (Commons.GeometryOfNumbers.Counting.finite_int_points_ball (d := d) T).toFinset := by
    ext x'
    constructor
    · intro hx
      rw [Finset.mem_image] at hx
      obtain ⟨x, hx, rfl⟩ := hx
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hx ⊢
      have := hx
      rw [Fin.sum_univ_castSucc] at this
      linarith [sq_nonneg ((x (Fin.last d) : ℝ))]
    · intro hx
      rw [Finset.mem_image]
      refine ⟨Fin.snoc x' 0, ?_, ?_⟩
      · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hx ⊢
        rw [sum_sq_snoc]
        simpa using hx
      · funext i
        simp
  rw [himg]
  refine Finset.sum_congr rfl (fun x' hx' => ?_)
  rw [cardBall]
  -- the fibre over `x'` is in bijection with the admissible last coordinates
  refine Finset.card_bij
    (fun (x : Fin (d + 1) → ℤ) _ => fun _ : Fin 1 => x (Fin.last d)) ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hx1, hx2⟩ := hx
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hx1 ⊢
    simp only [Fin.sum_univ_one]
    have hx1' := hx1
    rw [Fin.sum_univ_castSucc] at hx1'
    have hsum : (∑ i : Fin d, ((x i.castSucc : ℝ)) ^ 2)
        = (∑ i : Fin d, ((x' i : ℝ)) ^ 2) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show x i.castSucc = x' i from congrFun hx2 i]
    have hle : ((x (Fin.last d) : ℝ)) ^ 2 ≤ T ^ 2 - ∑ i : Fin d, ((x' i : ℝ)) ^ 2 := by
      rw [← hsum]; linarith
    have hT2 : (0:ℝ) ≤ T ^ 2 - ∑ i : Fin d, ((x' i : ℝ)) ^ 2 := by
      linarith [sq_nonneg ((x (Fin.last d) : ℝ))]
    rw [Real.sq_sqrt hT2]
    exact hle
  · intro x1 hx1 x2 hx2 heq
    rw [Finset.mem_filter] at hx1 hx2
    have hlast : x1 (Fin.last d) = x2 (Fin.last d) := congrFun heq 0
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have h1 : x1 j.castSucc = x' j := congrFun hx1.2 j
      have h2 : x2 j.castSucc = x' j := congrFun hx2.2 j
      rw [h1, h2]
    · exact hlast
  · intro k hk
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hk hx'
    simp only [Fin.sum_univ_one] at hk
    have hT2 : (0:ℝ) ≤ T ^ 2 - ∑ i : Fin d, ((x' i : ℝ)) ^ 2 := by linarith
    rw [Real.sq_sqrt hT2] at hk
    refine ⟨Fin.snoc x' (k 0), ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, sum_sq_snoc]
        linarith [hk]
      · funext i
        simp
    · funext i
      simp
      fin_cases i
      rfl

/-- The filter cardinality is the lattice count at the corresponding radius. -/
lemma filter_card_eq_cardBall {d : ℕ} {T t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t) (htT : t ≤ T) :
    (((Commons.GeometryOfNumbers.Counting.finite_int_points_ball (d := d) T).toFinset.filter
        (fun x => t ≤ Real.sqrt (T ^ 2 - ‖intVec x‖ ^ 2))).card)
      = cardBall d (Real.sqrt (T ^ 2 - t ^ 2)) := by
  rw [cardBall]
  congr 1
  ext x
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hnorm : ‖intVec x‖ ^ 2 = ∑ i, ((x i : ℝ)) ^ 2 := norm_intVec_sq x
  have hsq : Real.sqrt (T ^ 2 - t ^ 2) ^ 2 = T ^ 2 - t ^ 2 := Real.sq_sqrt (by nlinarith)
  constructor
  · rintro ⟨hx1, hx2⟩
    have hxT2 : ‖intVec x‖ ^ 2 ≤ T ^ 2 := by rw [hnorm]; exact hx1
    have hxT : ‖intVec x‖ ≤ T := by
      have := sq_le_sq.mp hxT2
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hT] at this
    have hrad : 0 ≤ T ^ 2 - ‖intVec x‖ ^ 2 := by linarith
    rw [Real.le_sqrt ht hrad] at hx2
    rw [hsq]
    linarith [hnorm]
  · intro hx
    rw [hsq] at hx
    have hx2 : (∑ i, ((x i : ℝ)) ^ 2) ≤ T ^ 2 := by linarith [sq_nonneg t]
    refine ⟨hx2, ?_⟩
    have hrad : 0 ≤ T ^ 2 - ‖intVec x‖ ^ 2 := by rw [hnorm]; linarith
    rw [Real.le_sqrt ht hrad]
    rw [hnorm]
    linarith

/-- **The recursion.**  The number of non-zero lattice points in the ball of radius `T` in
dimension `d+1` is bounded by the corresponding number in dimension `d` plus twice the
integral over `u ∈ (0,T)` of the lattice count at radius `√(T²-u²)`. -/
lemma cardBall_succ_le (d : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (cardBall (d + 1) T : ℝ) - 1
      ≤ ((cardBall d T : ℝ) - 1)
        + 2 * ∫ u in (0 : ℝ)..T, (cardBall d (Real.sqrt (T ^ 2 - u ^ 2)) : ℝ) := by
  classical
  set F : Finset (Fin d → ℤ) :=
    (Commons.GeometryOfNumbers.Counting.finite_int_points_ball (d := d) T).toFinset with hF
  -- the fibre decomposition
  have hfib : cardBall (d + 1) T
      = ∑ x' ∈ F, cardBall 1 (Real.sqrt (T ^ 2 - ∑ i, ((x' i : ℝ)) ^ 2)) :=
    cardBall_succ_fiber d hT
  -- each fibre is bounded by `2√(T²-‖x'‖²)+1`
  have hterm : ∀ x' ∈ F, (cardBall 1 (Real.sqrt (T ^ 2 - ∑ i, ((x' i : ℝ)) ^ 2)) : ℝ)
      ≤ 2 * Real.sqrt (T ^ 2 - ‖intVec x'‖ ^ 2) + 1 := by
    intro x' hx'
    rw [hF] at hx'
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hx'
    have hnorm : ‖intVec x'‖ ^ 2 = ∑ i, ((x' i : ℝ)) ^ 2 := norm_intVec_sq x'
    have hR : 0 ≤ Real.sqrt (T ^ 2 - ∑ i, ((x' i : ℝ)) ^ 2) := Real.sqrt_nonneg _
    have h := cardBall_one_le _ hR
    rw [hnorm]
    exact h
  have hstep1 : (cardBall (d + 1) T : ℝ)
      ≤ (∑ x' ∈ F, (2 * Real.sqrt (T ^ 2 - ‖intVec x'‖ ^ 2) + 1) : ℝ) := by
    rw [hfib]
    push_cast
    exact Finset.sum_le_sum hterm
  -- the layer cake
  have hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → Real.sqrt (T ^ 2 - b ^ 2) ≤ Real.sqrt (T ^ 2 - a ^ 2) := by
    intro a b ha hab
    apply Real.sqrt_le_sqrt
    nlinarith
  have hpos : ∀ a : ℝ, 0 ≤ Real.sqrt (T ^ 2 - a ^ 2) := fun a => Real.sqrt_nonneg _
  have hlayer := Commons.MeasureTheory.Integral.sum_eq_integral_card_filter F
    (fun ρ : ℝ => Real.sqrt (T ^ 2 - ρ ^ 2)) hmono hpos
  rw [hF] at hlayer
  have hsum2 : (∑ x' ∈ F, Real.sqrt (T ^ 2 - ‖intVec x'‖ ^ 2))
      = ∫ t in (0 : ℝ)..(Real.sqrt (T ^ 2 - 0 ^ 2)),
          ((F.filter (fun x => t ≤ Real.sqrt (T ^ 2 - ‖intVec x‖ ^ 2))).card : ℝ) := hlayer
  rw [show T ^ 2 - (0:ℝ) ^ 2 = T ^ 2 by ring, Real.sqrt_sq hT] at hsum2
  -- identify the integrand
  have hcongr : ∀ t ∈ Set.Ioc (0:ℝ) T,
      ((F.filter (fun x => t ≤ Real.sqrt (T ^ 2 - ‖intVec x‖ ^ 2))).card : ℝ)
        = (cardBall d (Real.sqrt (T ^ 2 - t ^ 2)) : ℝ) := by
    intro t ht
    rw [filter_card_eq_cardBall hT ht.1.le ht.2]
  have hint : (∫ t in (0 : ℝ)..T, ((F.filter (fun x => t ≤ Real.sqrt (T ^ 2 - ‖intVec x‖ ^ 2))).card : ℝ))
      = ∫ t in (0 : ℝ)..T, (cardBall d (Real.sqrt (T ^ 2 - t ^ 2)) : ℝ) := by
    rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT]
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    filter_upwards with t ht
    exact hcongr t ht
  have hsum3 : (∑ x' ∈ F, Real.sqrt (T ^ 2 - ‖intVec x'‖ ^ 2))
      = ∫ t in (0 : ℝ)..T, (cardBall d (Real.sqrt (T ^ 2 - t ^ 2)) : ℝ) := by
    rw [← hint]; exact hsum2
  -- conclude
  have hsum1 : (∑ x' ∈ F, (2 * Real.sqrt (T ^ 2 - ‖intVec x'‖ ^ 2) + 1) : ℝ)
      = 2 * (∑ x' ∈ F, Real.sqrt (T ^ 2 - ‖intVec x'‖ ^ 2)) + (F.card : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.mul_sum]
    simp
  have hFcard : (F.card : ℝ) = (cardBall d T : ℝ) := by rw [hF]; rfl
  rw [hsum1, hFcard, hsum3] at hstep1
  linarith

/-- The polynomial upper bound for the number of lattice points. -/
def countPoly (d : ℕ) (T : ℝ) : ℝ :=
  ∑ m ∈ Finset.range d, volUnitBall (m + 1) * ((d.choose (m + 1) : ℕ) : ℝ) * T ^ (m + 1)

/-- The binomial expansion of `(T+s)^d - s^d`. -/
lemma pow_add_sub_pow (d : ℕ) (T s : ℝ) :
    (T + s) ^ d - s ^ d
      = ∑ m ∈ Finset.range d, T ^ (m + 1) * s ^ (d - m - 1) * ((d.choose (m + 1) : ℕ) : ℝ) := by
  rw [add_pow, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, pow_zero, Nat.sub_zero, one_mul]
  rw [add_sub_cancel_right]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finset.mem_range] at hm
  rw [show d - (m + 1) = d - m - 1 by omega]

/-- The shift of the polynomial bound appearing in Pascal's identity. -/
def shiftPoly (d : ℕ) (T : ℝ) : ℝ :=
  ∑ m ∈ Finset.range d, volUnitBall (m + 2) * ((d.choose (m + 1) : ℕ) : ℝ) * T ^ (m + 2)

/-- Pascal's identity for the polynomial bound. -/
lemma countPoly_succ (d : ℕ) (T : ℝ) :
    countPoly (d + 1) T = countPoly d T + 2 * T + shiftPoly d T := by
  have hterm : ∀ m : ℕ,
      volUnitBall (m + 1) * (((d + 1).choose (m + 1) : ℕ) : ℝ) * T ^ (m + 1)
        = volUnitBall (m + 1) * ((d.choose (m + 1) : ℕ) : ℝ) * T ^ (m + 1)
          + volUnitBall (m + 1) * ((d.choose m : ℕ) : ℝ) * T ^ (m + 1) := by
    intro m
    rw [Nat.choose_succ_succ d m]
    push_cast
    ring
  have h1 : countPoly (d + 1) T
      = (∑ m ∈ Finset.range (d + 1), volUnitBall (m + 1) * ((d.choose (m + 1) : ℕ) : ℝ) * T ^ (m + 1))
        + (∑ m ∈ Finset.range (d + 1), volUnitBall (m + 1) * ((d.choose m : ℕ) : ℝ) * T ^ (m + 1)) := by
    rw [countPoly, Finset.sum_congr rfl (fun m _ => hterm m), Finset.sum_add_distrib]
  have hA : (∑ m ∈ Finset.range (d + 1),
        volUnitBall (m + 1) * ((d.choose (m + 1) : ℕ) : ℝ) * T ^ (m + 1)) = countPoly d T := by
    rw [countPoly, Finset.sum_range_succ]
    simp only [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self d), Nat.cast_zero, mul_zero, zero_mul,
      add_zero]
  have hB : (∑ m ∈ Finset.range (d + 1),
        volUnitBall (m + 1) * ((d.choose m : ℕ) : ℝ) * T ^ (m + 1)) = 2 * T + shiftPoly d T := by
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, pow_one, mul_one, zero_add]
    rw [volUnitBall_one]
    have hX : (∑ m ∈ Finset.range d, volUnitBall (m + 2) * ((d.choose (m + 1) : ℕ) : ℝ) * T ^ (m + 2))
        = shiftPoly d T := by rw [shiftPoly]
    linarith [hX]
  rw [h1, hA, hB]
  ring

/-- The integral of `(max (T²-x²) 0)^{(m+1)/2}` over `(0,T)`. -/
lemma integral_max_sq_sub (T : ℝ) (m : ℕ) (hT : 0 ≤ T) :
    (∫ x in (0:ℝ)..T, (max (T ^ 2 - x ^ 2) 0) ^ (((m : ℝ) + 1) / 2))
      = T ^ (m + 2)
          * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 2))) 1)).toReal
        / (2 * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)).toReal) := by
  rw [← Commons.Analysis.Integral.integral_sq_sub_sq_rpow (m + 1) hT]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with x hx
  rw [Set.uIoc_of_le hT] at hx
  rw [show (((m + 1 : ℕ) : ℝ) / 2) = ((m : ℝ) + 1) / 2 by push_cast; ring]
  rw [max_eq_left (by have := hx.2; have := hx.1; nlinarith)]

/-- Auxiliary: the function `x ↦ (max (T²-x²) 0)^{(m+1)/2}` is continuous, nonnegative on
`[0,∞)` and nonincreasing there. -/
lemma sqSub_continuous (T : ℝ) (m : ℕ) :
    Continuous (fun x : ℝ => (max (T ^ 2 - x ^ 2) 0) ^ (((m : ℝ) + 1) / 2)) := by
  apply Continuous.rpow_const
  · fun_prop
  · intro x; right; positivity

lemma sqSub_nonneg (T : ℝ) (m : ℕ) (x : ℝ) :
    0 ≤ (max (T ^ 2 - x ^ 2) 0) ^ (((m : ℝ) + 1) / 2) :=
  Real.rpow_nonneg (le_max_right _ _) _

lemma sqSub_antitone (T : ℝ) (m : ℕ) :
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → (max (T ^ 2 - b ^ 2) 0) ^ (((m : ℝ) + 1) / 2)
      ≤ (max (T ^ 2 - a ^ 2) 0) ^ (((m : ℝ) + 1) / 2) := by
  intro a b ha hab
  apply Real.rpow_le_rpow (le_max_right _ _)
  · exact max_le_max (by nlinarith) le_rfl
  · positivity

/-- **The main induction**: the number of non-zero lattice points is bounded by the polynomial. -/
lemma cardBall_sub_one_le_countPoly : ∀ (d : ℕ), 1 ≤ d → ∀ T : ℝ, 0 ≤ T →
    (cardBall d T : ℝ) - 1 ≤ countPoly d T := by
  intro d
  induction d with
  | zero => intro hd; omega
  | succ d ih =>
    intro hd T hT
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · subst hd0
      have h1 := cardBall_one_le T hT
      have h2 : countPoly 1 T = 2 * T := by
        rw [countPoly, Finset.sum_range_one, volUnitBall_one]
        norm_num
      rw [h2] at *
      linarith
    · have hIH := ih hdpos
      have hsplit := cardBall_succ d hT
      have h0mem : (0 : ℤ) ∈ Finset.Icc (-⌊T⌋) ⌊T⌋ := by
        rw [Finset.mem_Icc]
        exact ⟨by linarith [Int.floor_nonneg.mpr hT], Int.floor_nonneg.mpr hT⟩
      set S : Finset ℤ := (Finset.Icc (-⌊T⌋) ⌊T⌋).erase 0 with hS
      -- decomposition
      have hM : (cardBall (d + 1) T : ℝ) - 1 = ((cardBall d T : ℝ) - 1)
          + ∑ k ∈ S, (cardBall d (Real.sqrt (T ^ 2 - ((k:ℝ)) ^ 2)) : ℝ) := by
        have hsum := Finset.sum_erase_add (Finset.Icc (-⌊T⌋) ⌊T⌋)
          (fun k : ℤ => (cardBall d (Real.sqrt (T ^ 2 - ((k:ℝ)) ^ 2)) : ℝ)) h0mem
        have hf0 : (cardBall d (Real.sqrt (T ^ 2 - ((0:ℤ):ℝ) ^ 2)) : ℝ) = (cardBall d T : ℝ) := by
          rw [show T ^ 2 - ((0:ℤ):ℝ) ^ 2 = T^2 by norm_num, Real.sqrt_sq hT]
        rw [hf0] at hsum
        have hcast : (cardBall (d + 1) T : ℝ)
            = ∑ k ∈ Finset.Icc (-⌊T⌋) ⌊T⌋, (cardBall d (Real.sqrt (T ^ 2 - ((k:ℝ)) ^ 2)) : ℝ) := by
          rw [hsplit]; push_cast; rfl
        rw [hcast, hS]
        linarith [hsum]
      -- each term is bounded by the polynomial
      have hbound : (∑ k ∈ S, (cardBall d (Real.sqrt (T ^ 2 - ((k:ℝ)) ^ 2)) : ℝ))
          ≤ (S.card : ℝ) + ∑ k ∈ S, countPoly d (Real.sqrt (T ^ 2 - ((k:ℝ)) ^ 2)) := by
        rw [show (S.card : ℝ) + ∑ k ∈ S, countPoly d (Real.sqrt (T ^ 2 - ((k:ℝ)) ^ 2))
            = ∑ k ∈ S, (1 + countPoly d (Real.sqrt (T ^ 2 - ((k:ℝ)) ^ 2))) by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]]
        refine Finset.sum_le_sum (fun k hk => ?_)
        have := hIH (Real.sqrt (T ^ 2 - ((k:ℝ)) ^ 2)) (Real.sqrt_nonneg _)
        linarith
      have hcardle : (S.card : ℝ) ≤ 2 * T := by
        have hc : ((Finset.Icc (-⌊T⌋) ⌊T⌋).card : ℤ) = 2 * ⌊T⌋ + 1 := by
          have h := Int.card_Icc_of_le (-⌊T⌋) ⌊T⌋ (by have := Int.floor_nonneg.mpr hT; omega)
          push_cast at h
          linarith [h]
        have hcardnat : ((Finset.Icc (-⌊T⌋) ⌊T⌋).card : ℝ) = 2 * (⌊T⌋ : ℝ) + 1 := by
          have := congrArg (fun z : ℤ => (z : ℝ)) hc
          push_cast at this
          linarith [this]
        rw [hS, Finset.card_erase_of_mem h0mem]
        have hpos : 1 ≤ (Finset.Icc (-⌊T⌋) ⌊T⌋).card := by
          have := Finset.card_pos.mpr ⟨0, h0mem⟩
          omega
        have hcast2 : (((Finset.Icc (-⌊T⌋) ⌊T⌋).card - 1 : ℕ) : ℝ)
            = ((Finset.Icc (-⌊T⌋) ⌊T⌋).card : ℝ) - 1 := by
          rw [Nat.cast_sub hpos]; norm_num
        rw [hcast2]
        linarith [hcardnat, Int.floor_le T]
      -- the shifted sums
      have hshift : (∑ k ∈ S, countPoly d (Real.sqrt (T ^ 2 - ((k:ℝ)) ^ 2))) ≤ shiftPoly d T := by
        have hswap : (∑ k ∈ S, countPoly d (Real.sqrt (T ^ 2 - ((k:ℝ)) ^ 2)))
            = ∑ m ∈ Finset.range d, ∑ k ∈ S,
                (volUnitBall (m + 1) * ((d.choose (m + 1) : ℕ) : ℝ)
                  * (Real.sqrt (T ^ 2 - ((k:ℝ)) ^ 2)) ^ (m + 1)) := by
          simp only [countPoly]
          rw [Finset.sum_comm]
        rw [hswap, shiftPoly]
        refine Finset.sum_le_sum (fun m _ => ?_)
        have hkey : ∀ k ∈ S, (Real.sqrt (T ^ 2 - ((k:ℝ)) ^ 2)) ^ (m + 1)
            = (max (T ^ 2 - |((k:ℝ))| ^ 2) 0) ^ (((m : ℝ) + 1) / 2) := by
          intro k hk
          have hkT : |((k:ℝ))| ≤ T := by
            rw [hS, Finset.mem_erase, Finset.mem_Icc] at hk
            rw [abs_le]
            exact ⟨by
              have : ((-⌊T⌋ : ℤ) : ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.2.1
              push_cast at this; linarith [Int.floor_le T],
              le_trans (by exact_mod_cast hk.2.2) (Int.floor_le T)⟩
          have hnn : (0:ℝ) ≤ T ^ 2 - ((k:ℝ)) ^ 2 := by
            have h2 : |((k:ℝ))| ^ 2 ≤ T ^ 2 := by nlinarith [abs_nonneg ((k:ℝ))]
            nlinarith [sq_abs ((k:ℝ))]
          rw [Commons.Measure.EuclideanSpace.sqrt_pow_eq_rpow _ hnn (m + 1),
            show (((m + 1 : ℕ) : ℝ) / 2) = ((m : ℝ) + 1) / 2 by push_cast; ring]
          rw [show |((k:ℝ))| ^ 2 = ((k:ℝ)) ^ 2 from sq_abs ((k:ℝ)), max_eq_left hnn]
        have hsumS : (∑ k ∈ S, (max (T ^ 2 - |((k:ℝ))| ^ 2) 0) ^ (((m : ℝ) + 1) / 2))
            ≤ 2 * ∫ x in (0:ℝ)..T, (max (T ^ 2 - x ^ 2) 0) ^ (((m : ℝ) + 1) / 2) := by
          have hIcc := Commons.Analysis.Integral.sum_Icc_abs_le_integral_of_antitone
            (sqSub_continuous T m) (fun x _ => sqSub_nonneg T m x) (sqSub_antitone T m) hT
          have h0 := Finset.sum_erase_add (Finset.Icc (-⌊T⌋) ⌊T⌋)
            (fun k : ℤ => (max (T ^ 2 - |((k:ℝ))| ^ 2) 0) ^ (((m : ℝ) + 1) / 2)) h0mem
          simp only [Int.cast_zero, abs_zero] at h0 hIcc
          rw [hS]
          linarith [hIcc, h0]
        calc ∑ k ∈ S, volUnitBall (m + 1) * ((d.choose (m + 1) : ℕ) : ℝ)
              * (Real.sqrt (T ^ 2 - ((k:ℝ)) ^ 2)) ^ (m + 1)
            = volUnitBall (m + 1) * ((d.choose (m + 1) : ℕ) : ℝ)
              * ∑ k ∈ S, (max (T ^ 2 - |((k:ℝ))| ^ 2) 0) ^ (((m : ℝ) + 1) / 2) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun k hk => by rw [hkey k hk])
          _ ≤ volUnitBall (m + 1) * ((d.choose (m + 1) : ℕ) : ℝ)
              * (2 * ∫ x in (0:ℝ)..T, (max (T ^ 2 - x ^ 2) 0) ^ (((m : ℝ) + 1) / 2)) :=
              mul_le_mul_of_nonneg_left hsumS
                (mul_nonneg (le_of_lt (volUnitBall_pos (m+1))) (Nat.cast_nonneg _))
          _ = volUnitBall (m + 2) * ((d.choose (m + 1) : ℕ) : ℝ) * T ^ (m + 2) := by
              rw [integral_max_sq_sub T m hT]
              rw [show (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)).toReal
                    = volUnitBall (m + 1) from rfl,
                  show (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 2))) 1)).toReal
                    = volUnitBall (m + 2) from rfl]
              have hV : volUnitBall (m + 1) ≠ 0 := (volUnitBall_pos (m+1)).ne'
              field_simp
      have hIH' := hIH T hT
      linarith [hM, hbound, hcardle, hshift, countPoly_succ d T, hIH']


/-- The polynomial bound implies the annulus bound. -/
lemma cardBall_le_poly {d : ℕ} (hd : 1 ≤ d) {T : ℝ} (hT : 0 ≤ T) :
    (cardBall d T : ℝ) ≤ 1 + countPoly d T := by
  have h := cardBall_sub_one_le_countPoly d hd T hT
  linarith

/-- The polynomial bound is at most the volume of the annulus of radii `√d/2`, `T + √d/2`. -/
lemma countPoly_le_volume {d : ℕ} (hd : 1 ≤ d) {T : ℝ} (hT : 0 ≤ T) :
    countPoly d T ≤ volUnitBall d * ((T + Real.sqrt d / 2) ^ d - (Real.sqrt d / 2) ^ d) := by
  have hpow := pow_add_sub_pow d T (Real.sqrt d / 2)
  rw [countPoly]
  rw [show volUnitBall d * ((T + Real.sqrt d / 2) ^ d - (Real.sqrt d / 2) ^ d)
      = ∑ m ∈ Finset.range d, volUnitBall d * T ^ (m + 1) * (Real.sqrt (d:ℝ) / 2) ^ (d - m - 1)
          * ((d.choose (m + 1) : ℕ) : ℝ) from by
        rw [hpow, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun m _ => by ring)]
  refine Finset.sum_le_sum (fun m hm => ?_)
  rw [Finset.mem_range] at hm
  have h1 : volUnitBall (m + 1) ≤ volUnitBall d * (Real.sqrt (d:ℝ) / 2) ^ (d - (m + 1)) :=
    volUnitBall_le_mul_pow (m + 1) d (by omega) (by omega)
  rw [show d - (m + 1) = d - m - 1 by omega] at h1
  have hC : (0:ℝ) ≤ ((d.choose (m + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hTp : (0:ℝ) ≤ T ^ (m + 1) := pow_nonneg hT _
  calc volUnitBall (m + 1) * ((d.choose (m + 1) : ℕ) : ℝ) * T ^ (m + 1)
      ≤ (volUnitBall d * (Real.sqrt (d:ℝ) / 2) ^ (d - m - 1)) * ((d.choose (m + 1) : ℕ) : ℝ)
          * T ^ (m + 1) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hC) hTp
    _ = volUnitBall d * T ^ (m + 1) * (Real.sqrt (d:ℝ) / 2) ^ (d - m - 1)
          * ((d.choose (m + 1) : ℕ) : ℝ) := by ring

/-- **The sharp lattice-point count.**  The number of lattice points of the closed ball of
radius `T` in `ℤ^d` is at most `1` plus the volume of the annulus of radii `√d/2`, `T + √d/2`.

It is proved by induction on `d` (`cardBall_sub_one_le_countPoly`): slicing off the last
coordinate with `cardBall_succ`, applying the inductive hypothesis to each slice, bounding the
resulting sum of square roots with `sum_Icc_abs_le_integral_of_antitone`, and comparing the
resulting coefficients with `countPoly_le_volume` using `volUnitBall_le_mul_pow`. -/
lemma cardBall_le_annulus_volume {d : ℕ} (hd : 0 < d) {T : ℝ} (hT : 0 ≤ T) :
    (cardBall d T : ℝ) ≤ 1 + volUnitBall d * ((T + Real.sqrt d / 2) ^ d
      - (Real.sqrt d / 2) ^ d) := by
  have h1 := cardBall_le_poly (d := d) (by omega) hT
  have h2 := countPoly_le_volume (d := d) (by omega) hT
  linarith

/-- The threshold: the largest radius `a ≤ T` with `t ≤ g a`. -/
def threshold (g : ℝ → ℝ) (T t : ℝ) : ℝ :=
  sSup ({a : ℝ | 0 ≤ a ∧ t ≤ g a} ∩ Set.Icc 0 T)

lemma bddAbove_threshold (g : ℝ → ℝ) (T t : ℝ) :
    BddAbove ({a : ℝ | 0 ≤ a ∧ t ≤ g a} ∩ Set.Icc 0 T) := ⟨T, fun _ ha => ha.2.2⟩

lemma nonempty_threshold {g : ℝ → ℝ} {T t : ℝ} (hT : 0 ≤ T) (ht : t ≤ g 0) :
    ({a : ℝ | 0 ≤ a ∧ t ≤ g a} ∩ Set.Icc 0 T).Nonempty := by
  refine ⟨0, ?_, ?_⟩
  · exact ⟨le_refl 0, ht⟩
  · exact ⟨le_refl 0, hT⟩

lemma le_threshold {g : ℝ → ℝ} {T t a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) (hag : t ≤ g a) :
    a ≤ threshold g T t := le_csSup (bddAbove_threshold g T t) ⟨⟨ha, hag⟩, ha, haT⟩

lemma threshold_nonneg {g : ℝ → ℝ} {T t : ℝ} (hT : 0 ≤ T) (ht : t ≤ g 0) :
    0 ≤ threshold g T t := le_threshold (le_refl 0) hT ht

lemma threshold_le {g : ℝ → ℝ} {T t : ℝ} (hT : 0 ≤ T) (ht : t ≤ g 0) :
    threshold g T t ≤ T :=
  csSup_le (nonempty_threshold hT ht) (fun _ hb => hb.2.2)

lemma le_g_of_lt_threshold {g : ℝ → ℝ} (hmono : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a)
    {T t a : ℝ} (hT : 0 ≤ T) (ht : t ≤ g 0) (ha0 : 0 ≤ a) (ha : a < threshold g T t) :
    t ≤ g a := by
  obtain ⟨a', ⟨⟨ha'0, ha't⟩, -⟩, hlt⟩ := exists_lt_of_lt_csSup (nonempty_threshold hT ht) ha
  exact le_trans ha't (hmono a a' ha0 (le_of_lt hlt))

lemma card_filter_add_one_le_cardBall {d : ℕ} {r e : ℝ} (hr : 0 ≤ r)
    (F : Finset (Fin d → ℤ)) (hFr : ∀ x ∈ F, r < ‖intVec x‖) :
    (F.filter (fun x => ‖intVec x‖ ≤ e)).card + 1 ≤ cardBall d e := by
  classical
  rw [cardBall]
  have hsub : insert (0 : Fin d → ℤ) (F.filter (fun x => ‖intVec x‖ ≤ e))
      ⊆ (finite_int_points_ball (d := d) e).toFinset := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · rw [Set.Finite.mem_toFinset]
      show (∑ i, (((0 : Fin d → ℤ) i : ℝ)) ^ 2) ≤ e ^ 2
      have hz : (∑ i, (((0 : Fin d → ℤ) i : ℝ)) ^ 2) = 0 := by simp
      rw [hz]
      exact sq_nonneg e
    · rw [Finset.mem_filter] at hx
      rw [Set.Finite.mem_toFinset]
      have h2 : ‖intVec x‖ ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx.2 2
      rwa [norm_intVec_sq] at h2
  have h0 : (0 : Fin d → ℤ) ∉ F.filter (fun x => ‖intVec x‖ ≤ e) := by
    intro hx
    rw [Finset.mem_filter] at hx
    have hz : ‖intVec (0 : Fin d → ℤ)‖ = 0 := by
      have h : ‖intVec (0 : Fin d → ℤ)‖ ^ 2 = 0 := by
        rw [norm_intVec_sq]; simp
      exact sq_eq_zero_iff.mp h
    have h1 := hFr 0 hx.1
    rw [hz] at h1
    linarith
  calc (F.filter (fun x => ‖intVec x‖ ≤ e)).card + 1
      = (insert (0 : Fin d → ℤ) (F.filter (fun x => ‖intVec x‖ ≤ e))).card :=
        (Finset.card_insert_of_notMem h0).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **Step 2 of the even-`d` assembly.**  The number of lattice points of `F` on which `g` is at
least `t` is at most the volume of the annulus of radii `√d/2` and `√d/2 + min T β_t`. -/
lemma filter_card_le_volume {d : ℕ} (hd : 0 < d) {r T : ℝ} (hr : 0 ≤ r) (hrT : r ≤ T)
    (g : ℝ → ℝ) (F : Finset (Fin d → ℤ)) (hFr : ∀ x ∈ F, r < ‖intVec x‖)
    (hFT : ∀ x ∈ F, ‖intVec x‖ ≤ T)
    {t : ℝ} (ht : t ≤ g 0) :
    ((F.filter (fun x => t ≤ g ‖intVec x‖)).card : ℝ)
      ≤ volUnitBall d * ((Real.sqrt d / 2 + min T (threshold g T t)) ^ d
          - (Real.sqrt d / 2) ^ d) := by
  classical
  have hT : 0 ≤ T := le_trans hr hrT
  rcases Finset.eq_empty_or_nonempty (F.filter (fun x => t ≤ g ‖intVec x‖)) with h0 | hne
  · rw [h0, Finset.card_empty, Nat.cast_zero]
    refine mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr ?_)
    refine pow_le_pow_left₀ (by positivity) ?_ d
    have h1 : (0:ℝ) ≤ min T (threshold g T t) :=
      le_min hT (threshold_nonneg hT ht)
    linarith
  · obtain ⟨y, hy, hymax⟩ := Finset.exists_max_image _ (fun x => ‖intVec x‖) hne
    have hyF : y ∈ F := (Finset.mem_filter.mp hy).1
    have hyt : t ≤ g ‖intVec y‖ := (Finset.mem_filter.mp hy).2
    have heT : ‖intVec y‖ ≤ T := hFT y hyF
    have heβ : ‖intVec y‖ ≤ threshold g T t :=
      le_threshold (norm_nonneg _) heT hyt
    have hemin : ‖intVec y‖ ≤ min T (threshold g T t) := le_min heT heβ
    have hcard1 : (F.filter (fun x => t ≤ g ‖intVec x‖)).card
        ≤ (F.filter (fun x => ‖intVec x‖ ≤ ‖intVec y‖)).card := by
      refine Finset.card_le_card ?_
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hymax x (Finset.mem_filter.mpr hx)⟩
    have hcard2 : (F.filter (fun x => ‖intVec x‖ ≤ ‖intVec y‖)).card + 1
        ≤ cardBall d ‖intVec y‖ := card_filter_add_one_le_cardBall hr F hFr
    have hkey := cardBall_le_annulus_volume hd (norm_nonneg (intVec y))
    have hcard3 : (((F.filter (fun x => t ≤ g ‖intVec x‖)).card : ℕ) : ℝ) ≤ volUnitBall d
        * ((Real.sqrt d / 2 + ‖intVec y‖) ^ d - (Real.sqrt d / 2) ^ d) := by
      have hA : ((F.filter (fun x => t ≤ g ‖intVec x‖)).card : ℝ) + 1
          ≤ (cardBall d ‖intVec y‖ : ℝ) := by
        have h1 : (F.filter (fun x => t ≤ g ‖intVec x‖)).card + 1
            ≤ cardBall d ‖intVec y‖ :=
          le_trans (Nat.add_le_add_right hcard1 1) hcard2
        exact_mod_cast h1
      rw [show (‖intVec y‖ + Real.sqrt d / 2) = (Real.sqrt d / 2 + ‖intVec y‖) from
        add_comm _ _] at hkey
      linarith [hkey]
    refine le_trans hcard3 ?_
    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    refine sub_le_sub_right ?_ _
    exact pow_le_pow_left₀ (by positivity) (by linarith) d


/-- The Lebesgue measure of the annulus of radii `a`, `b`. -/
lemma volume_annulusSet_toReal {d : ℕ} (hd : 0 < d) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (volume (annulusSet (d := d) a b)).toReal = volUnitBall d * (b ^ d - a ^ d) := by
  have h := integral_annulus_radial_eq (d := d) hd ha hab (fun _ => (1:ℝ))
  have h1 : (∫ y in annulusSet (d := d) a b, radialWeight (d := d) (fun _ => (1:ℝ)) y)
      = (volume (annulusSet (d := d) a b)).toReal := by
    rw [show (fun y : EuclideanSpace ℝ (Fin d) => radialWeight (d := d) (fun _ => (1:ℝ)) y)
        = fun _ => (1:ℝ) from funext (fun y => by simp [radialWeight])]
    rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_one]
  have h2 : (∫ u in a..b, u ^ (d - 1) * (fun _ => (1:ℝ)) (max (u - Real.sqrt d / 2) 0))
      = (b ^ d - a ^ d) / d := by
    rw [show (fun u : ℝ => u ^ (d - 1) * (fun _ => (1:ℝ)) (max (u - Real.sqrt d / 2) 0))
        = fun u : ℝ => u ^ (d - 1) from funext (fun u => by simp)]
    have hd1 : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
    rw [integral_pow, hd1]
    have hden : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by rw [← hd1]; push_cast; ring
    rw [hden]
  rw [h1, h2] at h
  rw [h]
  rw [show (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
      = volUnitBall d from rfl]
  have hdR : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  field_simp
  try ring

/-- The layer-cake identity for the radial weight over an annulus. -/
lemma integral_annulus_radialWeight_eq_threshold {d : ℕ} (hd : 0 < d) {T : ℝ} (hT : 0 ≤ T)
    (g : ℝ → ℝ) (hmono : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a) (hpos : ∀ a, 0 ≤ g a) :
    ∫ y in annulusSet (d := d) (Real.sqrt d / 2) (T + Real.sqrt d / 2), radialWeight (d := d) g y
      = ∫ t in (0:ℝ)..(g 0),
          volUnitBall d * ((Real.sqrt d / 2 + threshold g T t) ^ d - (Real.sqrt d / 2) ^ d) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  have hs : 0 ≤ Real.sqrt d / 2 := by positivity
  have hsR : Real.sqrt d / 2 ≤ T + Real.sqrt d / 2 := by linarith
  have hmeas : Measurable (radialWeight (d := d) g) := measurable_radialWeight g hmono
  have hlayer := MeasureTheory.Integrable.integral_eq_integral_Ioc_meas_le
    (μ := volume.restrict (annulusSet (d := d) (Real.sqrt d / 2) (T + Real.sqrt d / 2)))
    (integrableOn_radialWeight_annulus (d := d) g hmono hpos
      (Real.sqrt d / 2) (T + Real.sqrt d / 2))
    (Filter.Eventually.of_forall (radialWeight_nonneg g hpos))
    (Filter.Eventually.of_forall (fun y => radialWeight_le g hmono y))
  have hcongr : ∀ t ∈ Set.Ioc (0:ℝ) (g 0),
      (volume.restrict (annulusSet (d := d) (Real.sqrt d / 2) (T + Real.sqrt d / 2))).real
          {a | t ≤ radialWeight (d := d) g a}
        = volUnitBall d * ((Real.sqrt d / 2 + threshold g T t) ^ d - (Real.sqrt d / 2) ^ d) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1.le
    have htg : t ≤ g 0 := ht.2
    have hβ0 : 0 ≤ threshold g T t := threshold_nonneg hT htg
    have hβT : threshold g T t ≤ T := threshold_le hT htg
    have hLmeas : MeasurableSet ({a : EuclideanSpace ℝ (Fin d) | t ≤ radialWeight (d := d) g a}
        ∩ annulusSet (d := d) (Real.sqrt d / 2) (T + Real.sqrt d / 2)) :=
      (measurableSet_le measurable_const hmeas).inter (measurableSet_annulusSet _ _)
    have hBmeas : MeasurableSet ({a : EuclideanSpace ℝ (Fin d) | t ≤ radialWeight (d := d) g a}) :=
      measurableSet_le measurable_const hmeas
    -- the level set is (up to a null set) the annulus of radii `s`, `s + β_t`
    have hsub1 : annulusSet (d := d) (Real.sqrt d / 2) (Real.sqrt d / 2 + threshold g T t)
        ⊆ {a | t ≤ radialWeight (d := d) g a}
          ∩ annulusSet (d := d) (Real.sqrt d / 2) (T + Real.sqrt d / 2) := by
      intro y hy
      obtain ⟨hy1, hy2⟩ := hy
      refine ⟨?_, hy1, by linarith [hy2, hβT]⟩
      show t ≤ radialWeight (d := d) g y
      have hw : radialWeight (d := d) g y = g (‖y‖ - Real.sqrt d / 2) := by
        unfold radialWeight
        rw [max_eq_left (by linarith)]
      rw [hw]
      exact le_g_of_lt_threshold hmono hT htg (by linarith) (by linarith)
    have hsub2 : {a | t ≤ radialWeight (d := d) g a}
          ∩ annulusSet (d := d) (Real.sqrt d / 2) (T + Real.sqrt d / 2)
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (Real.sqrt d / 2 + threshold g T t) := by
      intro y hy
      obtain ⟨hy1, hy2, hy3⟩ := hy
      rw [Metric.mem_closedBall, dist_zero_right]
      have hw : radialWeight (d := d) g y = g (‖y‖ - Real.sqrt d / 2) := by
        unfold radialWeight
        rw [max_eq_left (by linarith)]
      simp only [Set.mem_ofPred_eq] at hy1
      rw [hw] at hy1
      have := le_threshold (g := g) (T := T) (t := t) (a := ‖y‖ - Real.sqrt d / 2)
        (by linarith) (by linarith) hy1
      linarith
    rw [MeasureTheory.Measure.real, Measure.restrict_apply hBmeas]
    have hfinBall : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (Real.sqrt d / 2)) ≠ ⊤ :=
      (measure_ball_lt_top (μ := volume)).ne
    have hfinClosed : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d))
        (Real.sqrt d / 2 + threshold g T t)) ≠ ⊤ :=
      ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) _).measure_lt_top).ne
    have hfinInter : volume ({a | t ≤ radialWeight (d := d) g a}
        ∩ annulusSet (d := d) (Real.sqrt d / 2) (T + Real.sqrt d / 2)) ≠ ⊤ :=
      ne_top_of_le_ne_top hfinClosed (measure_mono hsub2)
    -- upper bound: the intersection lies in the closed ball minus the inner ball
    have hsub2' : {a | t ≤ radialWeight (d := d) g a}
          ∩ annulusSet (d := d) (Real.sqrt d / 2) (T + Real.sqrt d / 2)
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (Real.sqrt d / 2 + threshold g T t)
          \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (Real.sqrt d / 2) := by
      intro y hy
      refine ⟨hsub2 hy, ?_⟩
      rw [Metric.mem_ball, dist_zero_right]
      exact not_lt.mpr hy.2.1
    have hup : (volume ({a | t ≤ radialWeight (d := d) g a}
          ∩ annulusSet (d := d) (Real.sqrt d / 2) (T + Real.sqrt d / 2))).toReal
        ≤ volUnitBall d * ((Real.sqrt d / 2 + threshold g T t) ^ d - (Real.sqrt d / 2) ^ d) := by
      have hdiff : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d))
          (Real.sqrt d / 2 + threshold g T t)
          \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (Real.sqrt d / 2)) ≠ ⊤ :=
        ne_top_of_le_ne_top hfinClosed (measure_mono Set.diff_subset)
      calc (volume ({a | t ≤ radialWeight (d := d) g a}
            ∩ annulusSet (d := d) (Real.sqrt d / 2) (T + Real.sqrt d / 2))).toReal
          ≤ (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d))
              (Real.sqrt d / 2 + threshold g T t)
              \ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (Real.sqrt d / 2))).toReal :=
            ENNReal.toReal_mono hdiff (measure_mono hsub2')
        _ = (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d))
              (Real.sqrt d / 2 + threshold g T t))).toReal
            - (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (Real.sqrt d / 2))).toReal := by
            rw [MeasureTheory.measure_diff
                (Set.Subset.trans Metric.ball_subset_closedBall
                  (Metric.closedBall_subset_closedBall (by linarith [hβ0])))
                measurableSet_ball.nullMeasurableSet hfinBall,
              MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball,
              ENNReal.toReal_sub_of_le
                (measure_mono (Metric.ball_subset_ball (by linarith [hβ0])))
                (measure_ball_lt_top (μ := volume)).ne]
        _ = volUnitBall d * ((Real.sqrt d / 2 + threshold g T t) ^ d - (Real.sqrt d / 2) ^ d) := by
            rw [volume_ball_toReal d (Real.sqrt d / 2 + threshold g T t) (by omega)
                (by linarith), volume_ball_toReal d (Real.sqrt d / 2) (by omega) hs]
            rw [volUnitBall]
            ring
    -- lower bound
    have hdown : volUnitBall d * ((Real.sqrt d / 2 + threshold g T t) ^ d - (Real.sqrt d / 2) ^ d)
        ≤ (volume ({a | t ≤ radialWeight (d := d) g a}
            ∩ annulusSet (d := d) (Real.sqrt d / 2) (T + Real.sqrt d / 2))).toReal := by
      have h := ENNReal.toReal_mono hfinInter (measure_mono hsub1)
      rw [volume_annulusSet_toReal hd hs (by linarith [hβ0])] at h
      exact h
    exact le_antisymm hup hdown
  rw [intervalIntegral.integral_of_le (hpos 0),
      show (∫ y in annulusSet (d := d) (Real.sqrt d / 2) (T + Real.sqrt d / 2),
          radialWeight (d := d) g y)
        = ∫ ω, radialWeight (d := d) g ω
            ∂(volume.restrict (annulusSet (d := d) (Real.sqrt d / 2) (T + Real.sqrt d / 2))) from rfl,
      hlayer]
  exact setIntegral_congr_fun measurableSet_Ioc (fun t ht => hcongr t ht)



/-- Interval-integrability of the integrand of the main estimate. -/
lemma intervalIntegrable_weight {d : ℕ} (g : ℝ → ℝ)
    (hmono : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a) (hpos : ∀ a, 0 ≤ g a) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => u ^ (d - 1) * g (max (u - Real.sqrt d / 2) 0)) volume a b := by
  set A : ℝ := |a| + |b| + 1 with hA
  have hApos : (0:ℝ) < A := by rw [hA]; linarith [abs_nonneg a, abs_nonneg b]
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound ?_ ?_ (g 0 * A ^ (d - 1)) ?_
  · rw [Set.uIoc, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  · exact ((measurable_id.pow_const _).mul (measurable_gmax g _ hmono)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
    simp only [Set.uIoc, Set.mem_Ioc] at hu
    have habs : |u| ≤ A := by
      rw [abs_le]
      constructor
      · have h1 : -(|a| + |b|) ≤ u := by
          have h2 : -(|a| + |b|) ≤ min a b :=
            le_min (by linarith [neg_abs_le a, abs_nonneg b])
              (by linarith [neg_abs_le b, abs_nonneg a])
          linarith [hu.1]
        rw [hA]; linarith
      · have h1 : u ≤ |a| + |b| := by
          have h2 : max a b ≤ |a| + |b| :=
            max_le (by linarith [le_abs_self a, abs_nonneg b])
              (by linarith [le_abs_self b, abs_nonneg a])
          linarith [hu.2]
        rw [hA]; linarith
    calc ‖u ^ (d - 1) * g (max (u - Real.sqrt d / 2) 0)‖
        = |u| ^ (d - 1) * |g (max (u - Real.sqrt d / 2) 0)| := by
          rw [Real.norm_eq_abs, abs_mul, abs_pow]
      _ ≤ A ^ (d - 1) * g 0 := by
          refine mul_le_mul (pow_le_pow_left₀ (abs_nonneg u) habs _) ?_ (abs_nonneg _)
            (pow_nonneg hApos.le _)
          rw [abs_of_nonneg (hpos _)]
          exact le_g_zero g hmono (le_max_right _ _)
      _ = g 0 * A ^ (d - 1) := by ring


/-- **Main lemma.**  For a nonnegative nonincreasing weight `g`, the sum of `g ‖x‖` over the
lattice points of the annulus `r < ‖x‖ ≤ T` is bounded by the radial integral over the annulus
of radii `r - √d/2` and `T + √d/2` against the shifted weight `g (max (· - √d/2) 0)`. -/
theorem sum_int_points_annulus_le_radial {d : ℕ} (hd : 0 < d) {r T : ℝ} (hr : 0 ≤ r) (hrT : r ≤ T) (g : ℝ → ℝ) (hmono : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a) (hpos : ∀ a, 0 ≤ g a) : (∑ x ∈ (Commons.GeometryOfNumbers.Counting.finite_int_points_ball T).toFinset.filter (fun x => r < ‖(WithLp.toLp 2 (fun i : Fin d => (x i : ℝ)) : EuclideanSpace ℝ (Fin d))‖), g ‖(WithLp.toLp 2 (fun i : Fin d => (x i : ℝ)) : EuclideanSpace ℝ (Fin d))‖) ≤ (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal * ∫ u in (r - Real.sqrt d / 2)..(T + Real.sqrt d / 2), u ^ (d - 1) * g (max (u - Real.sqrt d / 2) 0) := by
  classical
  set F : Finset (Fin d → ℤ) := (finite_int_points_ball T).toFinset.filter
      (fun x => r < ‖(WithLp.toLp 2 (fun i : Fin d => (x i : ℝ)) : EuclideanSpace ℝ (Fin d))‖)
    with hF
  have hFmem : ∀ x ∈ F, x ∈ (finite_int_points_ball T).toFinset := by
    intro x hx
    rw [hF] at hx
    exact (Finset.mem_filter.mp hx).1
  have hFr : ∀ x ∈ F, r < ‖intVec x‖ := by
    intro x hx
    rw [hF] at hx
    exact (Finset.mem_filter.mp hx).2
  have hFle : ∀ x ∈ F, ‖intVec x‖ ≤ T := by
    intro x hx
    have h1 : (∑ i, ((x i : ℝ)) ^ 2) ≤ T ^ 2 :=
      (Set.Finite.mem_toFinset (finite_int_points_ball T)).mp (hFmem x hx)
    have h2 : ‖intVec x‖ ^ 2 ≤ T ^ 2 := by rw [norm_intVec_sq]; exact h1
    have h3 : 0 ≤ T := le_trans hr hrT
    nlinarith [norm_nonneg (intVec x), h2, h3]
  by_cases hrs : Real.sqrt d / 2 ≤ r
  · calc ∑ x ∈ F, g ‖intVec x‖
        ≤ ∫ y in ⋃ x ∈ F, intUnitCube x, radialWeight (d := d) g y :=
          sum_le_integral_union hd g hmono hpos F
      _ ≤ ∫ y in annulusSet (d := d) (r - Real.sqrt d / 2) (T + Real.sqrt d / 2),
            radialWeight (d := d) g y :=
          integral_union_le_annulus hd g hmono hpos hrT F hFle hFr
      _ = (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
            * ∫ u in (r - Real.sqrt d / 2)..(T + Real.sqrt d / 2),
                u ^ (d - 1) * g (max (u - Real.sqrt d / 2) 0) :=
          integral_annulus_radial_eq hd (by linarith) (by
            have hs : (0:ℝ) ≤ Real.sqrt d / 2 := by positivity
            linarith) g
  · -- `r < √d/2`: the unit cubes lie in the ball of radius `T + √d/2`
    have hTs : 0 ≤ T + Real.sqrt d / 2 := by
      have hs : (0:ℝ) ≤ Real.sqrt d / 2 := by positivity
      linarith
    have h1 : ∑ x ∈ F, g ‖intVec x‖
        ≤ ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (T + Real.sqrt d / 2),
            radialWeight (d := d) g y :=
      le_trans (sum_le_integral_union hd g hmono hpos F)
        (integral_union_le_ball hd g hmono hpos F hFle)
    rcases Nat.even_or_odd d with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- even `d`
      have hs : 0 ≤ Real.sqrt d / 2 := by positivity
      have hT : 0 ≤ T := le_trans hr hrT
      have hLHS := Commons.MeasureTheory.Integral.sum_eq_integral_card_filter F g hmono hpos
      -- integrability of the counting function
      have hIntegr : Integrable (fun t : ℝ => ((F.filter (fun x => t ≤ g ‖intVec x‖)).card : ℝ))
          (volume.restrict (Set.Ioc (0:ℝ) (g 0))) := by
        refine Integrable.of_bound ?_ (F.card : ℝ) ?_
        · refine (Antitone.measurable ?_).aestronglyMeasurable
          intro t t' htt'
          show ((F.filter (fun x => t' ≤ g ‖intVec x‖)).card : ℝ)
            ≤ ((F.filter (fun x => t ≤ g ‖intVec x‖)).card : ℝ)
          exact_mod_cast Finset.card_le_card (fun x hx => by
            simp only [Finset.mem_filter] at hx ⊢
            exact ⟨hx.1, le_trans htt' hx.2⟩)
        · filter_upwards with t
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact_mod_cast Finset.card_filter_le F (fun x => t ≤ g ‖intVec x‖)
      -- the threshold is antitone and bounded
      have hβnonneg : ∀ t : ℝ, 0 ≤ threshold g T t := by
        intro t
        rcases Set.eq_empty_or_nonempty ({a : ℝ | 0 ≤ a ∧ t ≤ g a} ∩ Set.Icc 0 T) with he | hne
        · unfold threshold
          rw [he]
          simp
        · obtain ⟨a, ha⟩ := hne
          exact le_trans ha.1.1 (le_csSup (bddAbove_threshold g T t) ha)
      have hβleT : ∀ t : ℝ, threshold g T t ≤ T := by
        intro t
        rcases Set.eq_empty_or_nonempty ({a : ℝ | 0 ≤ a ∧ t ≤ g a} ∩ Set.Icc 0 T) with he | hne
        · unfold threshold
          rw [he]
          simpa using hT
        · exact csSup_le hne (fun a ha => ha.2.2)
      have hβanti : Antitone (fun t : ℝ => threshold g T t) := by
        intro t t' htt'
        show threshold g T t' ≤ threshold g T t
        rcases Set.eq_empty_or_nonempty ({a : ℝ | 0 ≤ a ∧ t' ≤ g a} ∩ Set.Icc 0 T) with he | hne
        · unfold threshold
          rw [he]
          simpa [threshold] using hβnonneg t
        · refine csSup_le_csSup (bddAbove_threshold g T t) hne ?_
          intro a ha
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc] at ha ⊢
          exact ⟨⟨ha.1.1, le_trans htt' ha.1.2⟩, ha.2⟩
      -- integrability of the upper bound
      have hBint : Integrable (fun t : ℝ => volUnitBall d
          * ((Real.sqrt d / 2 + threshold g T t) ^ d - (Real.sqrt d / 2) ^ d))
          (volume.restrict (Set.Ioc (0:ℝ) (g 0))) := by
        refine Integrable.of_bound ?_ (volUnitBall d * ((Real.sqrt d / 2 + T) ^ d)) ?_
        · exact (measurable_const.mul (((measurable_const.add
            hβanti.measurable).pow_const d).sub measurable_const)).aestronglyMeasurable
        · filter_upwards with t
          have h1 : Real.sqrt d / 2 + threshold g T t ≤ Real.sqrt d / 2 + T := by
            linarith [hβleT t]
          have h2 : Real.sqrt d / 2 ≤ Real.sqrt d / 2 + threshold g T t := by linarith [hβnonneg t]
          have h3 : (Real.sqrt d / 2) ^ d ≤ (Real.sqrt d / 2 + threshold g T t) ^ d :=
            pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ Real.sqrt d / 2) h2 d
          have h4 : (Real.sqrt d / 2 + threshold g T t) ^ d
              ≤ (Real.sqrt d / 2 + T) ^ d :=
            pow_le_pow_left₀ (by linarith [hβnonneg t] : (0:ℝ) ≤ Real.sqrt d / 2 + threshold g T t)
              h1 d
          have h0 : (0:ℝ) ≤ (Real.sqrt d / 2) ^ d := pow_nonneg (by positivity) d
          rw [Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (le_of_lt (volUnitBall_pos d)) (by linarith [h3, h0]))]
          calc volUnitBall d * ((Real.sqrt d / 2 + threshold g T t) ^ d - (Real.sqrt d / 2) ^ d)
              ≤ volUnitBall d * (Real.sqrt d / 2 + T) ^ d := by
                refine mul_le_mul_of_nonneg_left (by linarith [h3, h4, h0])
                  (le_of_lt (volUnitBall_pos d))
            _ ≤ volUnitBall d * (Real.sqrt d / 2 + T) ^ d := le_refl _
      -- the pointwise bound integrates
      have hcmp : ∫ t in (0:ℝ)..(g 0), ((F.filter (fun x => t ≤ g ‖intVec x‖)).card : ℝ)
          ≤ ∫ t in (0:ℝ)..(g 0),
              volUnitBall d * ((Real.sqrt d / 2 + threshold g T t) ^ d - (Real.sqrt d / 2) ^ d) := by
        rw [intervalIntegral.integral_of_le (hpos 0), intervalIntegral.integral_of_le (hpos 0)]
        refine MeasureTheory.integral_mono
          (μ := volume.restrict (Set.Ioc (0:ℝ) (g 0)))
          (f := fun t : ℝ => ((F.filter (fun x => t ≤ g ‖intVec x‖)).card : ℝ))
          (g := fun t : ℝ => volUnitBall d
            * ((Real.sqrt d / 2 + threshold g T t) ^ d - (Real.sqrt d / 2) ^ d))
          hIntegr hBint ?_
        intro t
        simp only []
        by_cases ht : t ≤ g 0
        · have hle := filter_card_le_volume hd hr hrT g F hFr hFle ht
          rwa [min_eq_right (threshold_le hT ht)] at hle
        · have htg : g 0 < t := not_le.mp ht
          have hzero : (F.filter (fun x => t ≤ g ‖intVec x‖)).card = 0 := by
            rw [Finset.card_eq_zero]
            refine Finset.filter_eq_empty_iff.mpr (fun x _ hx => ?_)
            exact absurd (le_trans hx (le_g_zero g hmono (norm_nonneg _))) (not_le.mpr htg)
          rw [hzero, Nat.cast_zero]
          exact mul_nonneg (le_of_lt (volUnitBall_pos d))
            (sub_nonneg.mpr (pow_le_pow_left₀
              (by positivity : (0:ℝ) ≤ Real.sqrt d / 2)
              (by linarith [hβnonneg t] : Real.sqrt d / 2 ≤ Real.sqrt d / 2 + threshold g T t)
              d))
      -- the annulus layer cake
      have hann := integral_annulus_radialWeight_eq_threshold hd hT g hmono hpos
      -- the polar formula
      have hpolar := integral_annulus_radial_eq (d := d) hd hs
        (by linarith [hT] : Real.sqrt d / 2 ≤ T + Real.sqrt d / 2) g
      -- the interval comparison
      have hfin : (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
            * ∫ u in (Real.sqrt d / 2)..(T + Real.sqrt d / 2),
                u ^ (d - 1) * g (max (u - Real.sqrt d / 2) 0)
          ≤ (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
            * ∫ u in (r - Real.sqrt d / 2)..(T + Real.sqrt d / 2),
                u ^ (d - 1) * g (max (u - Real.sqrt d / 2) 0) := by
        have hsplit : ∫ u in (r - Real.sqrt d / 2)..(T + Real.sqrt d / 2),
              u ^ (d - 1) * g (max (u - Real.sqrt d / 2) 0)
            = (∫ u in (r - Real.sqrt d / 2)..(Real.sqrt d / 2),
                u ^ (d - 1) * g (max (u - Real.sqrt d / 2) 0))
              + ∫ u in (Real.sqrt d / 2)..(T + Real.sqrt d / 2),
                u ^ (d - 1) * g (max (u - Real.sqrt d / 2) 0) :=
          (intervalIntegral.integral_add_adjacent_intervals
            (intervalIntegrable_weight (d := d) g hmono hpos _ _)
            (intervalIntegrable_weight (d := d) g hmono hpos _ _)).symm
        have hlow : 0 ≤ ∫ u in (r - Real.sqrt d / 2)..(Real.sqrt d / 2),
              u ^ (d - 1) * g (max (u - Real.sqrt d / 2) 0) := by
          have heq : ∫ u in (r - Real.sqrt d / 2)..(Real.sqrt d / 2),
                u ^ (d - 1) * g (max (u - Real.sqrt d / 2) 0)
              = g 0 * ∫ u in (r - Real.sqrt d / 2)..(Real.sqrt d / 2), u ^ (d - 1) := by
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro u hu
            beta_reduce
            have h1 : r - Real.sqrt d / 2 ≤ Real.sqrt d / 2 := by
              have h2 := Real.sqrt_nonneg d
              linarith [not_le.mp hrs]
            rw [Set.uIcc_of_le h1] at hu
            have hz : max (u - Real.sqrt d / 2) 0 = 0 := max_eq_right (by linarith [hu.2])
            rw [hz, mul_comm]
          rw [heq]
          refine mul_nonneg (hpos 0) ?_
          have hpow' : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
          rw [integral_pow, hpow',
            show (((d - 1 : ℕ)) : ℝ) + 1 = (d : ℝ) by
              rw [Nat.cast_sub (by omega : 1 ≤ d)]; ring]
          refine div_nonneg (sub_nonneg.mpr ?_) (by positivity)
          have h3 : (r - Real.sqrt d / 2) ^ d = (Real.sqrt d / 2 - r) ^ d := by
            rw [show r - Real.sqrt d / 2 = -(Real.sqrt d / 2 - r) by ring,
              (show Even d from ⟨m, by omega⟩).neg_pow]
          rw [h3]
          exact pow_le_pow_left₀
            (by have h := not_le.mp hrs; linarith : (0:ℝ) ≤ Real.sqrt d / 2 - r)
            (by linarith [hr] : Real.sqrt d / 2 - r ≤ Real.sqrt d / 2) d
        rw [hsplit, mul_add]
        have h1 : (0:ℝ) ≤ (d : ℝ)
            * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
            * ∫ u in (r - Real.sqrt d / 2)..(Real.sqrt d / 2),
                u ^ (d - 1) * g (max (u - Real.sqrt d / 2) 0) := by
          have h2 := mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ (d : ℝ))
            (le_of_lt (volUnitBall_pos d))) hlow
          simpa only [volUnitBall] using h2
        linarith [h1]
      calc ∑ x ∈ F, g ‖intVec x‖
          = ∫ t in (0:ℝ)..(g 0), ((F.filter (fun x => t ≤ g ‖intVec x‖)).card : ℝ) := hLHS
        _ ≤ ∫ t in (0:ℝ)..(g 0),
              volUnitBall d * ((Real.sqrt d / 2 + threshold g T t) ^ d
                - (Real.sqrt d / 2) ^ d) := hcmp
        _ = ∫ y in annulusSet (d := d) (Real.sqrt d / 2) (T + Real.sqrt d / 2),
              radialWeight (d := d) g y := hann.symm
        _ = (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
              * ∫ u in (Real.sqrt d / 2)..(T + Real.sqrt d / 2),
                  u ^ (d - 1) * g (max (u - Real.sqrt d / 2) 0) := hpolar
        _ ≤ (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
              * ∫ u in (r - Real.sqrt d / 2)..(T + Real.sqrt d / 2),
                  u ^ (d - 1) * g (max (u - Real.sqrt d / 2) 0) := hfin
    · -- odd `d`: the integrand is nonnegative on the extra piece `[r-√d/2, 0]`
      have hball_eq : annulusSet (d := d) 0 (T + Real.sqrt d / 2)
          = Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (T + Real.sqrt d / 2) := by
        ext y
        rw [annulusSet, Metric.mem_ball, dist_zero_right]
        exact ⟨fun h => h.2, fun h => ⟨norm_nonneg y, h⟩⟩
      have h2 : ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (T + Real.sqrt d / 2),
            radialWeight (d := d) g y
          = (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal
            * ∫ u in (0:ℝ)..(T + Real.sqrt d / 2),
                u ^ (d - 1) * g (max (u - Real.sqrt d / 2) 0) := by
        rw [← hball_eq]
        exact integral_annulus_radial_eq hd le_rfl hTs g
      refine le_trans h1 ?_
      rw [h2]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      set f : ℝ → ℝ := fun u => u ^ (d - 1) * g (max (u - Real.sqrt d / 2) 0) with hf
      have hrs' : r < Real.sqrt d / 2 := not_le.mp hrs
      have hlo : r - Real.sqrt d / 2 ≤ T + Real.sqrt d / 2 := by
        have := Real.sqrt_nonneg d; linarith
      -- `d` is odd, so `d - 1` is even and `u ^ (d - 1) ≥ 0` for every real `u`
      have hpow : ∀ u : ℝ, 0 ≤ u ^ (d - 1) := by
        intro u
        have hdk : d - 1 = 2 * m := by omega
        rw [hdk, pow_mul]
        exact pow_nonneg (sq_nonneg u) m
      set f : ℝ → ℝ := fun u => u ^ (d - 1) * g (max (u - Real.sqrt d / 2) 0) with hf
      have hfnn : ∀ u : ℝ, 0 ≤ f u := fun u => mul_nonneg (hpow u) (hpos _)
      have hfmeas : Measurable f := by
        rw [hf]
        exact (measurable_id.pow_const _).mul (measurable_gmax g _ hmono)
      set A : ℝ := |r - Real.sqrt d / 2| + (T + Real.sqrt d / 2) + 1 with hA
      have hApos : 0 < A := by
        rw [hA]; have := abs_nonneg (r - Real.sqrt d / 2); linarith
      have hfint : IntegrableOn f (Set.Ioc (r - Real.sqrt d / 2) (T + Real.sqrt d / 2))
          volume := by
        refine IntegrableOn.of_bound ?_ ?_ (g 0 * A ^ (d - 1)) ?_
        · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
        · exact hfmeas.aestronglyMeasurable
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
          have habs : |u| ≤ A := by
            rw [abs_le]
            constructor
            · have h1 : -A ≤ r - Real.sqrt d / 2 := by
                rw [hA]
                linarith [neg_abs_le (r - Real.sqrt d / 2),
                  abs_nonneg (r - Real.sqrt d / 2), hTs]
              linarith [h1, hu.1]
            · have h1 : T + Real.sqrt d / 2 ≤ A := by
                rw [hA]; linarith [abs_nonneg (r - Real.sqrt d / 2)]
              linarith [hu.2]
          rw [hf]
          calc ‖u ^ (d - 1) * g (max (u - Real.sqrt d / 2) 0)‖
              = |u| ^ (d - 1) * |g (max (u - Real.sqrt d / 2) 0)| := by
                rw [Real.norm_eq_abs, abs_mul, abs_pow]
            _ ≤ A ^ (d - 1) * g 0 := by
                refine mul_le_mul (pow_le_pow_left₀ (abs_nonneg u) habs _) ?_
                  (abs_nonneg _) (pow_nonneg hApos.le _)
                rw [abs_of_nonneg (hpos _)]
                exact le_g_zero g hmono (le_max_right _ _)
            _ = g 0 * A ^ (d - 1) := by ring
      have hsub : Set.Ioc (0:ℝ) (T + Real.sqrt d / 2)
          ⊆ Set.Ioc (r - Real.sqrt d / 2) (T + Real.sqrt d / 2) :=
        fun u hu => ⟨by linarith [hu.1], hu.2⟩
      have hkey : ∫ u in Set.Ioc (0:ℝ) (T + Real.sqrt d / 2), f u
          ≤ ∫ u in Set.Ioc (r - Real.sqrt d / 2) (T + Real.sqrt d / 2), f u := by
        refine setIntegral_mono_set hfint ?_ ?_
        · filter_upwards with u
          exact hfnn u
        · rw [ae_le_set, Set.sdiff_eq_empty.mpr hsub, measure_empty]
      rw [intervalIntegral.integral_of_le hTs, intervalIntegral.integral_of_le hlo]
      exact hkey


end

end Commons.GeometryOfNumbers.Counting
