import Mathlib
import Submission.Work.Drive.encodedShear

/-!
# The parameter directions of the box shear (`NOTES_LEAD_hodd_blockT6.md` §2.2)

This module proves `Work.Drive.shear_param_directions`: the two vectors
`hb (y 0) • e₀` and `hb (y 1) • e₁` of the target square lie in the span of the four parameter
directions of `q ↦ shear q y` at **every** parameter `q₀`.

The proof is a concrete computation, in three layers.

* `Work.Drive.spdProj4` and the two linear-algebra lemmas `spdSpanRangeApply` /
  `spdSingleSpanTop` reduce the statement to the membership of the two vectors in the *range* of the
  differential of `q ↦ shear q y`.
* `Work.Drive.spdPhiT` is the polynomial map with `spdPhiT y (ballClamp q) = shear q y`; its two
  coordinate differentials `spdPhiM0 y`, `spdPhiM1 y c` are computed by hand, and the explicit
  vectors `spdPhiU1 y c`, `spdPhiU2 y c` satisfy
  `(fderiv ℝ (spdPhiT y) c) (spdPhiU1 y c) = hb (y 0) • e₀`,
  `(fderiv ℝ (spdPhiT y) c) (spdPhiU2 y c) = hb (y 1) • e₁`.
* `Work.Drive.spdHasFDerivAt_ballClamp` computes the differential of `ballClamp` explicitly and
  `Work.Drive.spdBallClampDeriv_surjective` shows it is onto, so that the range of the differential
  of `shear · y` is the range of the differential of `spdPhiT y` at the clamped parameter; the
  chain rule finishes.
-/

namespace Work.Drive

open scoped Manifold Topology

noncomputable section

set_option linter.unusedSimpArgs false

/-! ## 1. The coordinate functionals of `𝔼⁴` -/

/-- The `j`-th coordinate functional of `EuclideanSpace ℝ (Fin 4)`. -/
def spdProj4 (j : Fin 4) : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 4 => ℝ) j

@[simp] lemma spdProj4_apply (j : Fin 4) (v : EuclideanSpace ℝ (Fin 4)) :
    spdProj4 j v = v.ofLp j :=
  PiLp.proj_apply 2 (fun _ : Fin 4 => ℝ) j v

lemma spdProj4_single (j i : Fin 4) (a : ℝ) :
    spdProj4 j (EuclideanSpace.single i a) = if j = i then a else 0 := by
  rw [spdProj4_apply, PiLp.single_apply]

/-- The standard basis vectors of `𝔼⁴` expand every vector. -/
lemma spdSingleExpansion (v : EuclideanSpace ℝ (Fin 4)) :
    v = ∑ j : Fin 4, (v j) • (EuclideanSpace.single j (1 : ℝ)) := by
  ext i
  rw [← spdProj4_apply i v,
    ← spdProj4_apply i (∑ j : Fin 4, (v j) • (EuclideanSpace.single j (1 : ℝ)))]
  rw [map_sum, Finset.sum_eq_single i]
  · simp [spdProj4_apply]
  · intro j _ hj
    simp [spdProj4_apply, hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

lemma spdSingleSpanTop :
    Submodule.span ℝ
      (Set.range (fun j : Fin 4 => (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin 4))))
      = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [spdSingleExpansion v]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- The span of the images of the standard basis under a linear map is its range. -/
lemma spdSpanRangeApply_eq_range (f : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
    Submodule.span ℝ (Set.range (fun j : Fin 4 => f (EuclideanSpace.single j (1 : ℝ))))
      = LinearMap.range (f : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) := by
  have h1 : Submodule.span ℝ (Set.range (fun j : Fin 4 => f (EuclideanSpace.single j (1 : ℝ))))
      = Submodule.map (f : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
          (Submodule.span ℝ (Set.range (fun j : Fin 4 =>
            (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin 4))))) := by
    rw [Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨_, ⟨j, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
  rw [h1, spdSingleSpanTop, Submodule.map_top, LinearMap.range_eq_map]

/-! ## 2. The differential of `ballClamp` and its surjectivity -/

/-- The differential of `ballClamp q = (2 √(1+‖q‖²))⁻¹ • q` at `q₀`. -/
def spdBallClampDeriv (q₀ : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  (2 * Real.sqrt (1 + ‖q₀‖ ^ 2))⁻¹ • (1 : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    - (2 * Real.sqrt (1 + ‖q₀‖ ^ 2) ^ 3)⁻¹ • (innerSL ℝ q₀).smulRight q₀

lemma spdBallClampDeriv_apply (q₀ v : EuclideanSpace ℝ (Fin 4)) :
    spdBallClampDeriv q₀ v = (2 * Real.sqrt (1 + ‖q₀‖ ^ 2))⁻¹ • v
      - (2 * Real.sqrt (1 + ‖q₀‖ ^ 2) ^ 3)⁻¹ • (inner ℝ q₀ v • q₀) := by
  rw [spdBallClampDeriv]
  simp only [sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    one_apply_eq_self]

lemma spdHasFDerivAt_ballClamp (q₀ : EuclideanSpace ℝ (Fin 4)) :
    HasFDerivAt ballClamp (spdBallClampDeriv q₀) q₀ := by
  set s := Real.sqrt (1 + ‖q₀‖ ^ 2) with hs_def
  have hspos : 0 < s := by rw [hs_def]; positivity
  have hs : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 4) => Real.sqrt (1 + ‖q‖ ^ 2))
      ((1 / (2 * s)) • ((2 : ℕ) • innerSL ℝ q₀)) q₀ := by
    rw [hs_def]
    simpa using (((hasFDerivAt_id q₀).norm_sq.const_add 1).sqrt (by positivity))
  have h4 : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 4) => 2 * Real.sqrt (1 + ‖q‖ ^ 2))
      ((2 : ℝ) • ((1 / (2 * s)) • ((2 : ℕ) • innerSL ℝ q₀))) q₀ := by
    simpa using hs.const_mul 2
  have h5 : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin 4) => (2 * Real.sqrt (1 + ‖q‖ ^ 2))⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-((2 * s) ^ 2)⁻¹)).comp
        ((2 : ℝ) • ((1 / (2 * s)) • ((2 : ℕ) • innerSL ℝ q₀)))) q₀ := by
    have hx : 2 * s ≠ 0 := by positivity
    exact (hasFDerivAt_inv hx).comp q₀ h4
  have h6 := h5.smul (hasFDerivAt_id q₀)
  have hugly : ((ContinuousLinearMap.toSpanSingleton ℝ (-((2 * s) ^ 2)⁻¹)).comp
        ((2 : ℝ) • ((1 / (2 * s)) • ((2 : ℕ) • innerSL ℝ q₀))))
      = ((-(2 * s ^ 3)⁻¹) • innerSL ℝ q₀) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply]
    field_simp
    ring
  refine (h6.congr_of_eventuallyEq ?_).congr_fderiv ?_
  · filter_upwards with q
    simp [ballClamp]
  · rw [hugly]
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [spdBallClampDeriv, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, ContinuousLinearMap.id_apply, one_apply_eq_self, id_eq, ← hs_def,
      mul_inv_rev, neg_apply, neg_smul, sub_eq_add_neg, mul_smul, smul_assoc]

/-- The differential of `ballClamp` is onto. -/
lemma spdBallClampDeriv_surjective (q₀ : EuclideanSpace ℝ (Fin 4)) :
    Function.Surjective (spdBallClampDeriv q₀) := by
  intro w
  refine ⟨(2 * Real.sqrt (1 + ‖q₀‖ ^ 2)) • (w + (inner ℝ q₀ w) • q₀), ?_⟩
  rw [spdBallClampDeriv_apply]
  set s := Real.sqrt (1 + ‖q₀‖ ^ 2) with hs_def
  have hs2 : s ^ 2 = 1 + ‖q₀‖ ^ 2 := by rw [hs_def, Real.sq_sqrt (by positivity)]
  have hspos : 0 < s := by rw [hs_def]; positivity
  have hx : (2 : ℝ) * s ≠ 0 := by positivity
  rw [inv_smul_smul₀ hx, real_inner_smul_right, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq]
  rw [show inner ℝ q₀ w + inner ℝ q₀ w * ‖q₀‖ ^ 2 = inner ℝ q₀ w * s ^ 2 by rw [hs2]; ring]
  rw [← mul_smul]
  rw [show (2 * s ^ 3)⁻¹ * (2 * s * (inner ℝ q₀ w * s ^ 2)) = inner ℝ q₀ w by field_simp]
  simp

/-! ## 3. The polynomial map `spdPhiT` with `spdPhiT y (ballClamp q) = shear q y` -/

/-- The first coordinate of the polynomial form of `shear · y`. -/
def spdPhiX (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) : ℝ :=
  y 0 + (c 0 * (1 - 2 * y 1) + c 2 * hb (y 1)) * hb (y 0)

/-- The polynomial form of `shear · y`, read in the *clamped* variable. -/
def spdPhiT (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 2) :=
  pt2 (spdPhiX y c) (y 1 + (c 1 * (1 - 2 * spdPhiX y c) + c 3 * hb (spdPhiX y c)) * hb (y 1))

lemma spdPhiT_ballClamp (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    spdPhiT y (ballClamp q) = shear q y := by
  simp [spdPhiT, spdPhiX, shear, shear₁, shear₂]

/-- The normalisation of the `(0,2)`-block of the differential. -/
def spdPhiS1 (y : EuclideanSpace ℝ (Fin 2)) : ℝ := (1 - 2 * y 1) ^ 2 + hb (y 1) ^ 2

/-- The normalisation of the `(1,3)`-block of the differential. -/
def spdPhiS2 (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) : ℝ :=
  (1 - 2 * spdPhiX y c) ^ 2 + hb (spdPhiX y c) ^ 2

/-- The coupling coefficient of the two blocks. -/
def spdPhiK (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) : ℝ :=
  -2 * c 1 + c 3 * (1 - 2 * spdPhiX y c)

/-- The first component of the differential of `spdPhiT`. -/
def spdPhiM0 (y : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ :=
  hb (y 0) • ((1 - 2 * y 1) • spdProj4 0 + hb (y 1) • spdProj4 2)

/-- The second component of the differential of `spdPhiT`. -/
def spdPhiM1 (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ :=
  hb (y 1) • (spdPhiK y c • spdPhiM0 y + (1 - 2 * spdPhiX y c) • spdProj4 1
    + hb (spdPhiX y c) • spdProj4 3)

/-- The `(0,2)`-block vector of the first parameter direction. -/
def spdPhiV (y : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 4) :=
  (1 - 2 * y 1) • EuclideanSpace.single 0 (1 : ℝ)
    + hb (y 1) • EuclideanSpace.single 2 (1 : ℝ)

/-- The `(1,3)`-block vector of the parameter directions. -/
def spdPhiW (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) :=
  (1 - 2 * spdPhiX y c) • EuclideanSpace.single 1 (1 : ℝ)
    + hb (spdPhiX y c) • EuclideanSpace.single 3 (1 : ℝ)

/-- The parameter direction producing `hb (y 0) • e₀`. -/
def spdPhiU1 (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) :=
  (spdPhiS1 y)⁻¹ • spdPhiV y
    - (spdPhiK y c * hb (y 0) * (spdPhiS2 y c)⁻¹) • spdPhiW y c

/-- The parameter direction producing `hb (y 1) • e₁`. -/
def spdPhiU2 (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) :=
  (spdPhiS2 y c)⁻¹ • spdPhiW y c

lemma spdOneSubTwoMulSqAddHbSqPos (t : ℝ) : 0 < (1 - 2 * t) ^ 2 + hb t ^ 2 := by
  rcases eq_or_ne (hb t) 0 with h | h
  · rw [h]
    rcases mul_eq_zero.mp h with h1 | h1
    · rw [h1]; norm_num
    · have ht : t = 1 := by linarith
      rw [ht]; norm_num
  · nlinarith [sq_nonneg (1 - 2 * t), sq_pos_of_ne_zero h, sq_nonneg (hb t)]

lemma spdPhiS1_pos (y : EuclideanSpace ℝ (Fin 2)) : 0 < spdPhiS1 y :=
  spdOneSubTwoMulSqAddHbSqPos (y 1)

lemma spdPhiS2_pos (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    0 < spdPhiS2 y c := spdOneSubTwoMulSqAddHbSqPos (spdPhiX y c)

/-! ## 4. The two coordinate differentials of `spdPhiT` -/

lemma spdHasFDerivAt_PhiX (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    HasFDerivAt (fun c : EuclideanSpace ℝ (Fin 4) => spdPhiX y c) (spdPhiM0 y) c := by
  have h0 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 c 0
  have h2 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 c 2
  have h := ((h0.mul_const (1 - 2 * y 1)).add (h2.mul_const (hb (y 1)))).mul_const (hb (y 0))
  have h' := h.const_add (y 0)
  simp only [spdPhiX, spdPhiM0] at h' ⊢
  exact h'

lemma spdHasDerivAt_hb (x : ℝ) : HasDerivAt hb (1 - 2 * x) x := by
  have h := (hasDerivAt_id x).mul ((hasDerivAt_const (x := x) 1).sub (hasDerivAt_id x))
  refine h.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with y
    simp [hb, Pi.mul_apply]
  · simp [Pi.mul_apply]
    ring

lemma spdHasFDerivAt_PhiT_zero (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    HasFDerivAt (fun c : EuclideanSpace ℝ (Fin 4) => (spdPhiT y c) 0) (spdPhiM0 y) c := by
  have h := spdHasFDerivAt_PhiX y c
  simp only [spdPhiT, pt2_zero] at h ⊢
  exact h

lemma spdHasFDerivAt_PhiT_one (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    HasFDerivAt (fun c : EuclideanSpace ℝ (Fin 4) => (spdPhiT y c) 1) (spdPhiM1 y c) c := by
  have hX := spdHasFDerivAt_PhiX y c
  have h1 : HasFDerivAt (fun c : EuclideanSpace ℝ (Fin 4) => c 1) (spdProj4 1) c :=
    (ContinuousLinearMap.hasFDerivAt (spdProj4 1)).congr_of_eventuallyEq (by
      filter_upwards with v; simp [spdProj4_apply])
  have h3 : HasFDerivAt (fun c : EuclideanSpace ℝ (Fin 4) => c 3) (spdProj4 3) c :=
    (ContinuousLinearMap.hasFDerivAt (spdProj4 3)).congr_of_eventuallyEq (by
      filter_upwards with v; simp [spdProj4_apply])
  have h1m : HasFDerivAt (fun c : EuclideanSpace ℝ (Fin 4) => 1 - 2 * spdPhiX y c)
      ((-2 : ℝ) • spdPhiM0 y) c := by
    have hh := (hX.const_mul 2).const_sub 1
    refine hh.congr_fderiv ?_
    rw [← neg_smul]
  have hhbX : HasFDerivAt (fun c : EuclideanSpace ℝ (Fin 4) => hb (spdPhiX y c))
      ((1 - 2 * spdPhiX y c) • spdPhiM0 y) c := by
    have hbd : HasFDerivAt hb (ContinuousLinearMap.toSpanSingleton ℝ (1 - 2 * spdPhiX y c))
        (spdPhiX y c) := (hasDerivAt_iff_hasFDerivAt.mp (spdHasDerivAt_hb (spdPhiX y c)))
    have hcomp := hbd.comp c hX
    have heq : (ContinuousLinearMap.toSpanSingleton ℝ (1 - 2 * spdPhiX y c)).comp (spdPhiM0 y)
        = (1 - 2 * spdPhiX y c) • spdPhiM0 y := by
      ext v; simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
    rw [heq] at hcomp
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards with v
    rfl
  have h := ((h1.mul h1m).add (h3.mul hhbX)).mul_const (hb (y 1))
  have h' := h.const_add (y 1)
  simp only [spdPhiT, pt2_one] at h' ⊢
  refine h'.congr_fderiv ?_
  ext v
  simp only [spdPhiM1, spdPhiM0, spdPhiK, add_apply, smul_apply, spdProj4_apply]
  ring

lemma spdDifferentiableAt_PhiT (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    DifferentiableAt ℝ (spdPhiT y) c := by
  rw [differentiableAt_piLp]
  intro i
  fin_cases i
  · simpa using (spdHasFDerivAt_PhiT_zero y c).differentiableAt
  · simpa using (spdHasFDerivAt_PhiT_one y c).differentiableAt

lemma spdPhi_fderiv_zero (y : EuclideanSpace ℝ (Fin 2)) (c u : EuclideanSpace ℝ (Fin 4)) :
    ((fderiv ℝ (spdPhiT y) c) u) 0 = spdPhiM0 y u := by
  have hΦ : HasFDerivAt (spdPhiT y) (fderiv ℝ (spdPhiT y) c) c :=
    (spdDifferentiableAt_PhiT y c).hasFDerivAt
  have hcomp := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (spdPhiT y c) 0).comp c hΦ
  have hcomp' : HasFDerivAt (fun c => (spdPhiT y c) 0)
      ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0) ∘L (fderiv ℝ (spdPhiT y) c)) c :=
    hcomp.congr_of_eventuallyEq (by filter_upwards with v; rfl)
  have huniq := hcomp'.unique (spdHasFDerivAt_PhiT_zero y c)
  rw [← huniq]
  simp [ContinuousLinearMap.comp_apply, PiLp.proj_apply]

lemma spdPhi_fderiv_one (y : EuclideanSpace ℝ (Fin 2)) (c u : EuclideanSpace ℝ (Fin 4)) :
    ((fderiv ℝ (spdPhiT y) c) u) 1 = spdPhiM1 y c u := by
  have hΦ : HasFDerivAt (spdPhiT y) (fderiv ℝ (spdPhiT y) c) c :=
    (spdDifferentiableAt_PhiT y c).hasFDerivAt
  have hcomp := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (spdPhiT y c) 1).comp c hΦ
  have hcomp' : HasFDerivAt (fun c => (spdPhiT y c) 1)
      ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1) ∘L (fderiv ℝ (spdPhiT y) c)) c :=
    hcomp.congr_of_eventuallyEq (by filter_upwards with v; rfl)
  have huniq := hcomp'.unique (spdHasFDerivAt_PhiT_one y c)
  rw [← huniq]
  simp [ContinuousLinearMap.comp_apply, PiLp.proj_apply]

/-! ## 5. The explicit parameter directions -/

lemma spdPhiM0_apply (y : EuclideanSpace ℝ (Fin 2)) (v : EuclideanSpace ℝ (Fin 4)) :
    spdPhiM0 y v = hb (y 0) * ((1 - 2 * y 1) * (v.ofLp 0) + hb (y 1) * (v.ofLp 2)) := by
  simp only [spdPhiM0, add_apply, smul_apply, spdProj4_apply, smul_eq_mul]

lemma spdPhiM1_apply (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4))
    (v : EuclideanSpace ℝ (Fin 4)) :
    spdPhiM1 y c v = hb (y 1) * (spdPhiK y c * (spdPhiM0 y v) + (1 - 2 * spdPhiX y c) * (v.ofLp 1)
      + hb (spdPhiX y c) * (v.ofLp 3)) := by
  simp only [spdPhiM1, add_apply, smul_apply, spdProj4_apply, smul_eq_mul]

lemma spdPhiV_zero (y : EuclideanSpace ℝ (Fin 2)) : (spdPhiV y).ofLp 0 = 1 - 2 * y 1 := by
  rw [← spdProj4_apply 0 (spdPhiV y), spdPhiV, map_add, map_smul, map_smul, spdProj4_single,
    spdProj4_single]
  simp

lemma spdPhiV_one (y : EuclideanSpace ℝ (Fin 2)) : (spdPhiV y).ofLp 1 = 0 := by
  rw [← spdProj4_apply 1 (spdPhiV y), spdPhiV, map_add, map_smul, map_smul, spdProj4_single,
    spdProj4_single]
  simp

lemma spdPhiV_two (y : EuclideanSpace ℝ (Fin 2)) : (spdPhiV y).ofLp 2 = hb (y 1) := by
  rw [← spdProj4_apply 2 (spdPhiV y), spdPhiV, map_add, map_smul, map_smul, spdProj4_single,
    spdProj4_single]
  simp

lemma spdPhiV_three (y : EuclideanSpace ℝ (Fin 2)) : (spdPhiV y).ofLp 3 = 0 := by
  rw [← spdProj4_apply 3 (spdPhiV y), spdPhiV, map_add, map_smul, map_smul, spdProj4_single,
    spdProj4_single]
  simp

lemma spdPhiW_zero (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    (spdPhiW y c).ofLp 0 = 0 := by
  rw [← spdProj4_apply 0 (spdPhiW y c), spdPhiW, map_add, map_smul, map_smul, spdProj4_single,
    spdProj4_single]
  simp

lemma spdPhiW_one (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    (spdPhiW y c).ofLp 1 = 1 - 2 * spdPhiX y c := by
  rw [← spdProj4_apply 1 (spdPhiW y c), spdPhiW, map_add, map_smul, map_smul, spdProj4_single,
    spdProj4_single]
  simp

lemma spdPhiW_two (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    (spdPhiW y c).ofLp 2 = 0 := by
  rw [← spdProj4_apply 2 (spdPhiW y c), spdPhiW, map_add, map_smul, map_smul, spdProj4_single,
    spdProj4_single]
  simp

lemma spdPhiW_three (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    (spdPhiW y c).ofLp 3 = hb (spdPhiX y c) := by
  rw [← spdProj4_apply 3 (spdPhiW y c), spdPhiW, map_add, map_smul, map_smul, spdProj4_single,
    spdProj4_single]
  simp

lemma spdPhiM0_PhiV (y : EuclideanSpace ℝ (Fin 2)) :
    spdPhiM0 y (spdPhiV y) = hb (y 0) * spdPhiS1 y := by
  rw [spdPhiM0_apply, spdPhiV_zero, spdPhiV_two, spdPhiS1]; ring

lemma spdPhiM0_PhiW (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    spdPhiM0 y (spdPhiW y c) = 0 := by
  rw [spdPhiM0_apply, spdPhiW_zero, spdPhiW_two]; ring

lemma spdPhiM1_PhiV (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    spdPhiM1 y c (spdPhiV y) = hb (y 1) * (spdPhiK y c * (hb (y 0) * spdPhiS1 y)) := by
  rw [spdPhiM1_apply, spdPhiV_one, spdPhiV_three, spdPhiM0_PhiV]; ring

lemma spdPhiM1_PhiW (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    spdPhiM1 y c (spdPhiW y c) = hb (y 1) * spdPhiS2 y c := by
  rw [spdPhiM1_apply, spdPhiW_one, spdPhiW_three, spdPhiM0_PhiW, spdPhiS2]; ring

lemma spdPhiM0_PhiU1 (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    spdPhiM0 y (spdPhiU1 y c) = hb (y 0) := by
  rw [spdPhiU1, map_sub, map_smul, map_smul, spdPhiM0_PhiV, spdPhiM0_PhiW, smul_eq_mul, smul_eq_mul,
    mul_zero, sub_zero, mul_comm (hb (y 0)), ← mul_assoc,
    inv_mul_cancel₀ (ne_of_gt (spdPhiS1_pos y)), one_mul]

lemma spdPhiM1_PhiU1 (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    spdPhiM1 y c (spdPhiU1 y c) = 0 := by
  rw [spdPhiU1, map_sub, map_smul, map_smul, spdPhiM1_PhiV, spdPhiM1_PhiW, smul_eq_mul, smul_eq_mul]
  field_simp [ne_of_gt (spdPhiS1_pos y), ne_of_gt (spdPhiS2_pos y c)]
  ring

lemma spdPhiM0_PhiU2 (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    spdPhiM0 y (spdPhiU2 y c) = 0 := by
  rw [spdPhiU2, map_smul, spdPhiM0_PhiW, smul_eq_mul, mul_zero]

lemma spdPhiM1_PhiU2 (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    spdPhiM1 y c (spdPhiU2 y c) = hb (y 1) := by
  rw [spdPhiU2, map_smul, spdPhiM1_PhiW, smul_eq_mul]
  rw [show (spdPhiS2 y c)⁻¹ * (hb (y 1) * spdPhiS2 y c) = hb (y 1) by
    rw [mul_comm (hb (y 1)), ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (spdPhiS2_pos y c)), one_mul]]

lemma spdPhi_fderiv_PhiU1 (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    (fderiv ℝ (spdPhiT y) c) (spdPhiU1 y c)
      = hb (y 0) • (EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) := by
  ext i
  fin_cases i <;>
    simp [spdPhi_fderiv_zero, spdPhi_fderiv_one, spdPhiM0_PhiU1, spdPhiM1_PhiU1, PiLp.single_apply]

lemma spdPhi_fderiv_PhiU2 (y : EuclideanSpace ℝ (Fin 2)) (c : EuclideanSpace ℝ (Fin 4)) :
    (fderiv ℝ (spdPhiT y) c) (spdPhiU2 y c)
      = hb (y 1) • (EuclideanSpace.single 1 (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) := by
  ext i
  fin_cases i <;>
    simp [spdPhi_fderiv_zero, spdPhi_fderiv_one, spdPhiM0_PhiU2, spdPhiM1_PhiU2, PiLp.single_apply]

/-! ## 6. The theorem -/

theorem shear_param_directions (q₀ : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    (Work.Drive.hb (y 0) • (EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 2)))
        ∈ Submodule.span ℝ (Set.range fun j : Fin 4 =>
            fderiv ℝ (fun q' : EuclideanSpace ℝ (Fin 4) => Work.Drive.shear q' y) q₀
              (EuclideanSpace.single j (1 : ℝ))) ∧
    (Work.Drive.hb (y 1) • (EuclideanSpace.single 1 (1 : ℝ) : EuclideanSpace ℝ (Fin 2)))
        ∈ Submodule.span ℝ (Set.range fun j : Fin 4 =>
            fderiv ℝ (fun q' : EuclideanSpace ℝ (Fin 4) => Work.Drive.shear q' y) q₀
              (EuclideanSpace.single j (1 : ℝ))) := by
  have hsurj : Function.Surjective (fderiv ℝ ballClamp q₀) := by
    rw [(spdHasFDerivAt_ballClamp q₀).fderiv]
    exact spdBallClampDeriv_surjective q₀
  have hchain : fderiv ℝ (fun q' : EuclideanSpace ℝ (Fin 4) => shear q' y) q₀
      = (fderiv ℝ (spdPhiT y) (ballClamp q₀)).comp (fderiv ℝ ballClamp q₀) := by
    have h1 : DifferentiableAt ℝ (spdPhiT y) (ballClamp q₀) :=
      spdDifferentiableAt_PhiT y (ballClamp q₀)
    have h2 : DifferentiableAt ℝ ballClamp q₀ := (spdHasFDerivAt_ballClamp q₀).differentiableAt
    have h3 := fderiv_comp (𝕜 := ℝ) q₀ h1 h2
    have hfun : (fun q' : EuclideanSpace ℝ (Fin 4) => shear q' y) = spdPhiT y ∘ ballClamp := by
      funext q
      simpa using (spdPhiT_ballClamp q y).symm
    rw [hfun, h3]
  rw [spdSpanRangeApply_eq_range]
  constructor
  · rw [LinearMap.mem_range]
    obtain ⟨z, hz⟩ := hsurj (spdPhiU1 y (ballClamp q₀))
    refine ⟨z, ?_⟩
    rw [hchain]
    change (fderiv ℝ (spdPhiT y) (ballClamp q₀)) ((fderiv ℝ ballClamp q₀) z)
      = hb (y 0) • (EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 2))
    rw [hz]
    exact spdPhi_fderiv_PhiU1 y _
  · rw [LinearMap.mem_range]
    obtain ⟨z, hz⟩ := hsurj (spdPhiU2 y (ballClamp q₀))
    refine ⟨z, ?_⟩
    rw [hchain]
    change (fderiv ℝ (spdPhiT y) (ballClamp q₀)) ((fderiv ℝ ballClamp q₀) z)
      = hb (y 1) • (EuclideanSpace.single 1 (1 : ℝ) : EuclideanSpace ℝ (Fin 2))
    rw [hz]
    exact spdPhi_fderiv_PhiU2 y _

end

end Work.Drive
