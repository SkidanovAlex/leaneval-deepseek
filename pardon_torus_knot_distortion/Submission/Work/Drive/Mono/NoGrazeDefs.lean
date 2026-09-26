import Mathlib
import Submission.Work.Drive.Mono.NoBend
import Submission.Work.Drive.Mono.ae_exists_goodV
import Submission.Work.Drive.Mono.finite_flatCrossings
import Submission.Work.Drive.Mono.exists_margin_boxSphere
import Submission.Work.Drive.Mono.exists_margin_off_flatCrossings
import Submission.Work.Drive.Mono.exists_bound_boxNorm_eq
import Submission.Work.Drive.Mono.exists_uniform_sq_bound_vertVel
import Submission.Work.Drive.Mono.exists_bound_deriv2_curve
import Submission.Work.Drive.Mono.Band.heightGood_exists_in

/-!
# Vocabulary for the no-grazing witness

Self-contained definitions and elementary lemmas used by `Work.Drive.Mono.noGraze_witness`
(and by the delegated lemmas about it): the flat height of the knot relative to the cutting
plane, the slab height in a tilt direction, the finite set of crossings, and the
normalised orthogonal projection of the standard direction.

The definitions duplicate, under new names, the vocabulary of
`Submission/Work/Drive/Mono/GrazeWitness.lean`, so that the proof here does not depend on that
file.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology RealInnerProductSpace

noncomputable section

/-! ## Heights -/

/-- The flat height of the knot with the cutting level subtracted. -/
def flatHeight (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : ℝ → ℝ :=
  fun t => (K.curve t) (σ 2) - (c (σ 2) + u)

theorem flatHeight_apply (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (u t : ℝ) :
    flatHeight K c σ u t = (K.curve t) (σ 2) - (c (σ 2) + u) := rfl

/-- The height of the knot in the direction `v`, with the cutting level subtracted. -/
def slabHeight (K : Knot) (c : R3) (u : ℝ) (v : R3) : ℝ → ℝ :=
  fun t => inner ℝ v (K.curve t) - (inner ℝ v c + u)

theorem slabHeight_apply (K : Knot) (c : R3) (u : ℝ) (v : R3) (t : ℝ) :
    slabHeight K c u v t = inner ℝ v (K.curve t) - (inner ℝ v c + u) := rfl

/-- The difference of the slab height and the flat height. -/
theorem slabHeight_sub_flatHeight (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (t : ℝ) :
    slabHeight K c u v t - flatHeight K c σ u t
      = inner ℝ (v - Work.BoxShrink.shiftVσ σ 1) (K.curve t - c) := by
  rw [slabHeight_apply, flatHeight_apply, ← inner_shiftVσ_one σ (K.curve t),
    ← inner_shiftVσ_one σ c, inner_sub_left, inner_sub_right, inner_sub_right]
  ring

/-- The derivative of the slab height. -/
theorem deriv_slabHeight (K : Knot) (c : R3) (u : ℝ) (v : R3) (t : ℝ) :
    deriv (slabHeight K c u v) t = inner ℝ v (deriv K.curve t) := by
  have h : slabHeight K c u v
      = fun r : ℝ => inner ℝ v (K.curve r) - (inner ℝ v c + u) := rfl
  rw [h, deriv_sub_const, deriv_inner_curve_const]

/-- The derivative of the `(σ 2)`-coordinate of the knot is the derivative of the flat height. -/
theorem deriv_coord_eq_deriv_flatHeight (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (t : ℝ) :
    deriv (fun r : ℝ => (K.curve r) (σ 2)) t = deriv (flatHeight K c σ u) t := by
  have h : (fun r : ℝ => (K.curve r) (σ 2))
      = fun r : ℝ => flatHeight K c σ u r + (c (σ 2) + u) := by
    funext r; rw [flatHeight_apply]; ring
  rw [h, deriv_add_const]

/-- The derivative of the flat height is the `(σ 2)`-coordinate of the velocity. -/
theorem deriv_flatHeight (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (t : ℝ) :
    deriv (flatHeight K c σ u) t = (deriv K.curve t) (σ 2) := by
  have h : flatHeight K c σ u
      = fun r : ℝ => inner ℝ (Work.BoxShrink.shiftVσ σ 1) (K.curve r) - (c (σ 2) + u) := by
    funext r; rw [flatHeight_apply, inner_shiftVσ_one]
  rw [h, deriv_sub_const, deriv_inner_curve_const, inner_shiftVσ_one]

/-- The flat height is unchanged by the period shift. -/
theorem flatHeight_periodic (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Function.Periodic (flatHeight K c σ u) (2 * Real.pi) := by
  intro t
  rw [flatHeight_apply, flatHeight_apply, K.periodic]

theorem slabHeight_periodic (K : Knot) (c : R3) (u : ℝ) (v : R3) :
    Function.Periodic (slabHeight K c u v) (2 * Real.pi) := by
  intro t
  rw [slabHeight_apply, slabHeight_apply, K.periodic]

/-- `shiftVσ σ 1` is a unit vector. -/
theorem norm_shiftVσ_one (σ : Equiv.Perm (Fin 3)) :
    ‖Work.BoxShrink.shiftVσ σ 1‖ = 1 := by
  have h : inner ℝ (Work.BoxShrink.shiftVσ σ 1) (Work.BoxShrink.shiftVσ σ 1) = 1 := by
    rw [real_inner_comm, inner_shiftVσ_one, Work.BoxShrink.shiftVσ_apply]; simp
  have h2 := real_inner_self_eq_norm_sq (Work.BoxShrink.shiftVσ σ 1)
  rw [h] at h2
  nlinarith [norm_nonneg (Work.BoxShrink.shiftVσ σ 1)]

/-- The general norm of `shiftVσ σ d`. -/
theorem norm_shiftVσ (σ : Equiv.Perm (Fin 3)) (d : ℝ) :
    ‖Work.BoxShrink.shiftVσ σ d‖ = |d| := by
  have h : inner ℝ (Work.BoxShrink.shiftVσ σ d) (Work.BoxShrink.shiftVσ σ d) = d ^ 2 := by
    rw [PiLp.inner_apply]
    simp [Work.BoxShrink.shiftVσ_apply]
  have h2 := real_inner_self_eq_norm_sq (Work.BoxShrink.shiftVσ σ d)
  rw [h] at h2
  nlinarith [norm_nonneg (Work.BoxShrink.shiftVσ σ d), abs_nonneg d, sq_abs d]

/-- The unit coordinate vector in the direction `σ i`. -/
def unitCoord (σ : Equiv.Perm (Fin 3)) (i : Fin 3) : R3 :=
  WithLp.toLp 2 (fun m : Fin 3 => if m = σ i then 1 else 0)

theorem inner_unitCoord (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (x : R3) :
    inner ℝ (unitCoord σ i) x = x (σ i) := by
  rw [PiLp.inner_apply]
  simp [unitCoord]

theorem norm_unitCoord (σ : Equiv.Perm (Fin 3)) (i : Fin 3) : ‖unitCoord σ i‖ = 1 := by
  have h : inner ℝ (unitCoord σ i) (unitCoord σ i) = 1 := by
    rw [inner_unitCoord, unitCoord]
    simp
  have h2 := real_inner_self_eq_norm_sq (unitCoord σ i)
  rw [h] at h2
  nlinarith [norm_nonneg (unitCoord σ i)]

/-- `shiftVσ σ 0` is orthogonal to the flat direction. -/
theorem inner_shiftVσ_zero_shiftVσ_one (σ : Equiv.Perm (Fin 3)) :
    inner ℝ (Work.BoxShrink.shiftVσ σ 0) (Work.BoxShrink.shiftVσ σ 1) = 0 := by
  rw [real_inner_comm, inner_shiftVσ_one, Work.BoxShrink.shiftVσ_apply]
  have h : σ 0 ≠ σ 2 := by
    intro hc
    exact absurd (σ.injective hc) (by decide)
  simp [h]

/-- The orthogonal velocity, unfolded. -/
theorem vertVel_eq (K : Knot) (e : R3) (t : ℝ) :
    vertVel K e t = deriv K.curve t - inner ℝ e (deriv K.curve t) • e := by
  rw [vertVel, perpProj]

/-- The orthogonal velocity is orthogonal to `e`. -/
theorem inner_vertVel_eq_zero (K : Knot) {e : R3} (he : ‖e‖ = 1) (t : ℝ) :
    inner ℝ (vertVel K e t) e = 0 :=
  inner_perpProj_eq_zero e (deriv K.curve t) he

/-- **Period reduction.**  Every parameter has a representative in one period with the same point
and the same velocity. -/
theorem exists_period_reduce (K : Knot) (t : ℝ) :
    ∃ t' ∈ Set.Icc 0 (2 * Real.pi),
      K.curve t' = K.curve t ∧ deriv K.curve t' = deriv K.curve t := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hper : Function.Periodic (fun r : ℝ => (K.curve r, deriv K.curve r)) (2 * Real.pi) :=
    fun r => by
      simp only [Prod.mk.injEq]
      exact ⟨K.periodic r, periodic_deriv_curve K r⟩
  obtain ⟨t', ht', hval⟩ := exists_mem_Icc_eq_of_periodic (2 * Real.pi) hπ
    (fun r : ℝ => (K.curve r, deriv K.curve r)) hper t
  exact ⟨t', ht', (Prod.mk.injEq _ _ _ _).mp hval⟩

/-! ## The crossings and their flat speed -/

/-- The crossings of the cutting level with the knot inside the closed box, during one period. -/
def crossingSet (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) (s u : ℝ)
    (hcut : CutTransverse K s c σ u) : Finset ℝ :=
  (finite_flatCrossings K c σ s u hcut).toFinset

theorem mem_crossingSet {K : Knot} {c : R3} {σ : Equiv.Perm (Fin 3)} {s u : ℝ}
    {hcut : CutTransverse K s c σ u} {t : ℝ} :
    t ∈ crossingSet K c σ s u hcut ↔ t ∈ Set.Icc 0 (2 * Real.pi) ∧
      K.curve t ∈ closure (Submission.PBox s c σ) ∧ (K.curve t) (σ 2) = c (σ 2) + u := by
  rw [crossingSet, Set.Finite.mem_toFinset]
  rfl

/-- At a crossing the knot lies in the open box and the flat height has nonzero derivative. -/
theorem crossingSet_spec {K : Knot} {c : R3} {σ : Equiv.Perm (Fin 3)} {s u : ℝ}
    {hcut : CutTransverse K s c σ u} {t : ℝ} (ht : t ∈ crossingSet K c σ s u hcut) :
    K.curve t ∈ Submission.PBox s c σ ∧ deriv (flatHeight K c σ u) t ≠ 0 := by
  obtain ⟨-, h2, h3⟩ := (mem_crossingSet.mp ht)
  obtain ⟨h4, h5⟩ := hcut t h2 h3
  refine ⟨h4, fun hcon => h5 ?_⟩
  rw [deriv_coord_eq_deriv_flatHeight K c σ u t]
  exact hcon

/-- A positive lower bound for the flat speed at the crossings. -/
theorem exists_flatSpeed_pos {K : Knot} {c : R3} {σ : Equiv.Perm (Fin 3)} {s u : ℝ}
    (hcut : CutTransverse K s c σ u) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ t ∈ crossingSet K c σ s u hcut,
      lam ≤ |deriv (flatHeight K c σ u) t| := by
  rcases (crossingSet K c σ s u hcut).eq_empty_or_nonempty with hE | hN
  · exact ⟨1, one_pos, fun t ht => by rw [hE] at ht; exact absurd ht (by simp)⟩
  · obtain ⟨t₀, ht₀, hmin⟩ := Finset.exists_min_image (crossingSet K c σ s u hcut)
      (fun t => |deriv (flatHeight K c σ u) t|) hN
    exact ⟨|deriv (flatHeight K c σ u) t₀|, abs_pos.mpr (crossingSet_spec ht₀).2,
      fun t ht => hmin t ht⟩

/-- The crossing set consists of points of the closed box in the period. -/
theorem crossingSet_subset_Icc {K : Knot} {c : R3} {σ : Equiv.Perm (Fin 3)} {s u : ℝ}
    {hcut : CutTransverse K s c σ u} {t : ℝ} (ht : t ∈ crossingSet K c σ s u hcut) :
    t ∈ Set.Icc 0 (2 * Real.pi) := (mem_crossingSet.mp ht).1

/-- The crossing set lies in the closed box. -/
theorem crossingSet_mem_closure {K : Knot} {c : R3} {σ : Equiv.Perm (Fin 3)} {s u : ℝ}
    {hcut : CutTransverse K s c σ u} {t : ℝ} (ht : t ∈ crossingSet K c σ s u hcut) :
    K.curve t ∈ closure (Submission.PBox s c σ) := (mem_crossingSet.mp ht).2.1

/-! ## Avoiding the non-vertical crossings -/

/-- **Avoiding the non-vertical crossings.**  There is a vector which is not orthogonal to the
orthogonal velocity of the knot at any non-vertical crossing (a finite union of hyperplanes does not
cover the space). -/
theorem exists_avoid_vertVel (K : Knot) (e : R3) {c : R3} {σ : Equiv.Perm (Fin 3)} {s u : ℝ}
    (hcut : CutTransverse K s c σ u) :
    ∃ Ñ : R3, ∀ t ∈ crossingSet K c σ s u hcut, vertVel K e t ≠ 0 →
      inner ℝ Ñ (vertVel K e t) ≠ 0 := by
  classical
  set T := crossingSet K c σ s u hcut with hT
  set T' := T.filter (fun t => vertVel K e t ≠ 0) with hT'
  set P : ℝ → Submodule ℝ R3 :=
    fun t => LinearMap.ker ((innerSL ℝ (vertVel K e t) : R3 →ₗ[ℝ] ℝ)) with hP
  have hne : ∀ t : {t // t ∈ T'}, P t.1 ≠ ⊤ := by
    rintro ⟨t, ht⟩ htop
    have hz : vertVel K e t ≠ 0 := (Finset.mem_filter.mp ht).2
    have hmem : vertVel K e t ∈ P t := by rw [htop]; trivial
    rw [hP, LinearMap.mem_ker] at hmem
    have hval : ((innerSL ℝ (vertVel K e t) : R3 →ₗ[ℝ] ℝ)) (vertVel K e t)
        = inner ℝ (vertVel K e t) (vertVel K e t) := rfl
    rw [hval, real_inner_self_eq_norm_sq] at hmem
    exact hz (norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hmem))
  have hsub := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt (K := ℝ) (M := R3)
    (T'.attach) (fun t : {t // t ∈ T'} => P t.1) hne
    (by rw [ENat.card_eq_top_of_infinite (α := ℝ)]; exact ENat.natCast_lt_top _)
  obtain ⟨Ñ, hÑ⟩ : ∃ Ñ : R3, Ñ ∉ ⋃ i ∈ T'.attach, (P i.1 : Set R3) := by
    by_contra hcon
    push Not at hcon
    exact (Set.ssubset_univ_iff.mp hsub) (Set.eq_univ_of_forall hcon)
  refine ⟨Ñ, fun t ht hz => ?_⟩
  have hmemT' : t ∈ T' := Finset.mem_filter.mpr ⟨ht, hz⟩
  have hnotmem : Ñ ∉ P t := by
    intro hcon
    exact hÑ (Set.mem_iUnion.mpr ⟨⟨t, hmemT'⟩,
      Set.mem_iUnion.mpr ⟨Finset.mem_attach _ _, hcon⟩⟩)
  intro hzero
  apply hnotmem
  simp only [hP]
  rw [LinearMap.mem_ker]
  rw [show ((innerSL ℝ (vertVel K e t) : R3 →ₗ[ℝ] ℝ)) Ñ = inner ℝ (vertVel K e t) Ñ from rfl,
    real_inner_comm, hzero]

/-! ## Normalised orthogonal projection -/

/-- The unit direction `m = ‖n‖⁻¹ • n`. -/
def unitDir (n : R3) : R3 := (‖n‖)⁻¹ • n

/-- The normalised orthogonal projection of `e` onto `m^⊥`: the slab direction. -/
def orthDir (e m : R3) : R3 :=
  (‖e - inner ℝ e m • m‖)⁻¹ • (e - inner ℝ e m • m)

theorem unitDir_norm (n : R3) (hn : n ≠ 0) : ‖unitDir n‖ = 1 := by
  rw [unitDir, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg n),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn)]

theorem inner_unitDir (n y : R3) : inner ℝ (unitDir n) y = (‖n‖)⁻¹ * inner ℝ n y := by
  rw [unitDir, real_inner_smul_left]

/-- The normalised projection has norm `1`, is orthogonal to `m`, and its angle with the unit
vector `e` is controlled by `s = ⟪e, m⟫`. -/
theorem orthDir_spec {e m : R3} (he : ‖e‖ = 1) (hm : ‖m‖ = 1) {s : ℝ} (hs : s = inner ℝ e m)
    (hs1 : |s| ≤ 1 / 2) :
    ‖orthDir e m‖ = 1 ∧ inner ℝ (orthDir e m) m = 0 ∧
      inner ℝ e (orthDir e m) = ‖e - s • m‖ ∧
      ‖orthDir e m - e‖ ≤ Real.sqrt 2 * |s| ∧ |s| ≤ ‖orthDir e m - e‖ := by
  have hms : inner ℝ m e = s := by rw [hs, real_inner_comm]
  have hs2 : s ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs s, abs_nonneg s, hs1]
  have hnm : (1 : ℝ) - s ^ 2 = ‖e - s • m‖ ^ 2 := by
    have h1 : ⟪e, s • m⟫ = s * s := by rw [real_inner_smul_right, ← hs]
    have h2 : ‖s • m‖ ^ 2 = s ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, hm, mul_one, sq_abs]
    rw [norm_sub_sq_real, h1, h2, he]
    ring
  have hpos1 : 0 < 1 - s ^ 2 := by linarith
  have hw2 : 0 < ‖e - s • m‖ ^ 2 := by rw [← hnm]; exact hpos1
  have hwpos : 0 < ‖e - s • m‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm (fun h => by rw [h] at hw2; norm_num at hw2))
  have hw : ‖e - s • m‖ ≠ 0 := ne_of_gt hwpos
  have hwle1 : ‖e - s • m‖ ≤ 1 := by nlinarith [hnm ▸ hpos1.le, norm_nonneg (e - s • m)]
  have h1 : ‖orthDir e m‖ = 1 := by
    rw [orthDir, ← hs, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ hw]
  have hwdot : inner ℝ (e - s • m) m = 0 := by
    rw [inner_sub_left, ← hs, real_inner_smul_left, real_inner_self_eq_norm_sq, hm]
    ring
  have h2 : inner ℝ (orthDir e m) m = 0 := by
    rw [orthDir, ← hs, real_inner_smul_left, hwdot, mul_zero]
  have hed : inner ℝ e (e - s • m) = 1 - s ^ 2 := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, he, real_inner_smul_right, ← hs]
    ring
  have h4 : inner ℝ e (orthDir e m) = ‖e - s • m‖ := by
    rw [orthDir, ← hs, real_inner_smul_right, hed, hnm, sq, ← mul_assoc, inv_mul_cancel₀ hw,
      one_mul]
  have h3 : ‖orthDir e m - e‖ ^ 2 = 2 - 2 * ‖e - s • m‖ := by
    rw [norm_sub_sq_real, h1, real_inner_comm, h4, he]
    ring
  have h5 : ‖orthDir e m - e‖ ≤ Real.sqrt 2 * |s| := by
    have hle : ‖orthDir e m - e‖ ^ 2 ≤ 2 * s ^ 2 := by
      have h1' : ‖e - s • m‖ ^ 2 ≤ ‖e - s • m‖ := by
        nlinarith [hwle1, norm_nonneg (e - s • m)]
      have hs2' : s ^ 2 = 1 - ‖e - s • m‖ ^ 2 := by linarith [hnm]
      rw [h3, hs2']
      nlinarith [h1']
    calc ‖orthDir e m - e‖ = Real.sqrt (‖orthDir e m - e‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (2 * s ^ 2) := Real.sqrt_le_sqrt hle
      _ = Real.sqrt 2 * |s| := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_sq_eq_abs]
  have h6 : |s| ≤ ‖orthDir e m - e‖ := by
    have h : s = inner ℝ (e - orthDir e m) m := by
      rw [inner_sub_left, ← hs, h2, sub_zero]
    rw [h]
    calc |inner ℝ (e - orthDir e m) m| ≤ ‖e - orthDir e m‖ * ‖m‖ := abs_real_inner_le_norm _ _
      _ = ‖e - orthDir e m‖ := by rw [hm, mul_one]
      _ = ‖orthDir e m - e‖ := by rw [norm_sub_rev]
  exact ⟨h1, h2, h4, h5, h6⟩

/-! ## Misc elementary facts -/

/-- The decomposition of the derivative of the `n`-height of the knot. -/
theorem deriv_inner_eq_mul_add_vertVel (K : Knot) {e n : R3} (he : ‖e‖ = 1) (t : ℝ) :
    deriv (fun r : ℝ => inner ℝ n (K.curve r)) t
      = inner ℝ n e * inner ℝ e (deriv K.curve t) + inner ℝ n (vertVel K e t) := by
  have hdecomp : deriv K.curve t
      = (inner ℝ e (deriv K.curve t)) • e + vertVel K e t := by
    rw [vertVel, perpProj]
    abel
  have h1 : inner ℝ n (deriv K.curve t)
      = inner ℝ n e * inner ℝ e (deriv K.curve t) + inner ℝ n (vertVel K e t) := by
    conv_lhs => rw [hdecomp]
    rw [inner_add_right, real_inner_smul_right]
    ring
  rw [deriv_inner_curve_const, h1]

/-- Points of `PBox s c σ` are within `5/2 s` of the centre. -/
theorem norm_sub_le_of_mem_PBox {s : ℝ} (hs : 0 ≤ s) {c : R3} {σ : Equiv.Perm (Fin 3)}
    {y : R3} (hy : y ∈ Submission.PBox s c σ) : ‖y - c‖ ≤ 5 / 2 * s := by
  have h := Submission.PBox_subset_ball s hs c σ hy
  rw [Metric.mem_ball, dist_eq_norm] at h
  exact le_of_lt h

end

end Work.Drive.Mono
