import Mathlib
import Submission.Work.Drive.LensSpaceGlue
import Submission.Work.Drive.phiCap_eq_phiConf

/-!
# The glueing map `S³ → LensSpace` is surjective

`Work.Drive.LensSpace` is the Heegaard presentation `L(2,1) = (S¹ × D²) ∪_f (D² × S¹)` of the capping
slice, and `Work.Drive.phi : S³ → LensSpace` sends a point of the unit sphere of `ℂ²` to the class of
`capPt (z₁,z₂)` if `‖z₁‖ ≤ ‖z₂‖` and to the class of `confPt (z₁,z₂)` otherwise.

This file proves that `phi` is onto.  The substance is the surjectivity of the two branch maps onto
their solid tori: given `(θ, z) ∈ S¹ × D²` we choose a square root `w` of `circleOf θ` (of norm one)
and put

* `z₂ = r / w` and `z₁ = z w / √2` with `r = √(1 - ‖z‖²/2)`,

so that `(‖z₂‖/z₂)² = w² = circleOf θ` and `√2 z₁z₂/‖z₂‖ = z`; the configuration branch is the mirror
image of this.  Since a point of `LensSpace` is the class of a point of one of the two solid tori,
this gives a preimage of every point.
-/

set_option maxHeartbeats 1000000

namespace Work.Drive

noncomputable section

open scoped Topology

/-! ## Arithmetic of the square root of a unit complex number -/

/-- Every complex number of norm one has a square root of norm one. -/
lemma exists_sq_eq_of_norm_one {ζ : ℂ} (hζ : ‖ζ‖ = 1) : ∃ w : ℂ, ‖w‖ = 1 ∧ w ^ 2 = ζ := by
  refine ⟨Complex.exp ((ζ.arg / 2 : ℝ) * Complex.I), ?_, ?_⟩
  · exact Complex.norm_exp_ofReal_mul_I (ζ.arg / 2)
  · rw [sq, ← Complex.exp_add]
    have h : (ζ.arg / 2 : ℝ) * Complex.I + (ζ.arg / 2 : ℝ) * Complex.I =
        (ζ.arg : ℂ) * Complex.I := by
      push_cast; ring
    rw [h]
    have h2 := Complex.norm_mul_exp_arg_mul_I ζ
    rw [hζ, Complex.ofReal_one, one_mul] at h2
    exact h2

/-- The square root of `circleOf θ`, as an element of the unit circle: `circleOf θ` is a unit complex
number, `exists_sq_eq_of_norm_one` provides a square root of norm one. -/
lemma exists_sq_circleOf (θ : UnitAddCircle) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ w ^ 2 = circleOf θ :=
  exists_sq_eq_of_norm_one (norm_circleOf θ)

/-! ## Arithmetic of `r = √(1 - x²/2)` for `0 ≤ x ≤ 1` -/

lemma one_sub_sq_div_two_pos {x : ℝ} (hx : x ≤ 1) (hx0 : 0 ≤ x) : 0 < 1 - x ^ 2 / 2 := by
  nlinarith

lemma one_sub_sq_div_two_nonneg {x : ℝ} (hx : x ≤ 1) (hx0 : 0 ≤ x) : 0 ≤ 1 - x ^ 2 / 2 :=
  (one_sub_sq_div_two_pos hx hx0).le

/-- `‖z‖/√2 ≤ r` for `r = √(1 - ‖z‖²/2)`, when `‖z‖ ≤ 1`. -/
lemma div_sqrt_two_le_sqrt_one_sub {x : ℝ} (hx : x ≤ 1) (hx0 : 0 ≤ x) :
    x / Real.sqrt 2 ≤ Real.sqrt (1 - x ^ 2 / 2) := by
  have h := one_sub_sq_div_two_nonneg hx hx0
  refine (sq_le_sq₀ (div_nonneg hx0 (Real.sqrt_nonneg 2)) (Real.sqrt_nonneg _)).mp ?_
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt h]
  nlinarith

/-- `(x/√2)² + r² = 1` for `r = √(1 - x²/2)`, when `0 ≤ x ≤ 1`. -/
lemma sq_div_sqrt_two_add_sq_sqrt {x : ℝ} (hx : x ≤ 1) (hx0 : 0 ≤ x) :
    (x / Real.sqrt 2) ^ 2 + (Real.sqrt (1 - x ^ 2 / 2)) ^ 2 = 1 := by
  have h := one_sub_sq_div_two_nonneg hx hx0
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt h]
  ring

/-- The vector of `ℂ² = ℝ⁴` with the two given complex coordinates. -/
def mkVec (z₁ z₂ : ℂ) : Eucl 3 := !₂[z₁.re, z₁.im, z₂.re, z₂.im]

@[simp] lemma c₁_mkVec (z₁ z₂ : ℂ) : c₁ (mkVec z₁ z₂) = z₁ := by
  simp [mkVec, c₁]

@[simp] lemma c₂_mkVec (z₁ z₂ : ℂ) : c₂ (mkVec z₁ z₂) = z₂ := by
  simp [mkVec, c₂]

/-- The vector `(z₁,z₂)` lies on the unit sphere when `‖z₁‖² + ‖z₂‖² = 1`. -/
lemma mkVec_mem_unitSphere {z₁ z₂ : ℂ} (h : ‖z₁‖ ^ 2 + ‖z₂‖ ^ 2 = 1) :
    mkVec z₁ z₂ ∈ unitSphere 3 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  have h2 : ‖mkVec z₁ z₂‖ ^ 2 = 1 := by
    rw [norm_sq_c₁_c₂]; simpa using h
  rcases sq_eq_one_iff.mp h2 with hh | hh
  · exact hh
  · nlinarith [norm_nonneg (mkVec z₁ z₂)]

/-! ## Surjectivity of the two branches -/

/-- **`capPt` is onto `S¹ × D²`.** -/
lemma capPt_surjective : Function.Surjective capPt := by
  rintro ⟨θ, z⟩
  obtain ⟨w, hw, hw2⟩ := exists_sq_circleOf θ
  have hwne : w ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hw; norm_num at hw
  have hzn : ‖(z : ℂ)‖ ≤ 1 := by
    have h := z.2
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    exact h
  set r : ℝ := Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2 / 2) with hrdef
  have hr2 : r ^ 2 = 1 - ‖(z : ℂ)‖ ^ 2 / 2 := by
    rw [hrdef, Real.sq_sqrt (one_sub_sq_div_two_nonneg hzn (norm_nonneg (z : ℂ)))]
  have hrpos : 0 < r := by
    rw [hrdef]
    exact Real.sqrt_pos.mpr (one_sub_sq_div_two_pos hzn (norm_nonneg (z : ℂ)))
  have hrneC : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hrpos)
  set z₁ : ℂ := (z : ℂ) * w / (Real.sqrt 2 : ℂ) with hz₁
  set z₂ : ℂ := ((r : ℝ) : ℂ) / w with hz₂
  have hz₂norm : ‖z₂‖ = r := by
    rw [hz₂, norm_div, hw, div_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrpos.le]
  have hz₁norm : ‖z₁‖ = ‖(z : ℂ)‖ / Real.sqrt 2 := by
    rw [hz₁, norm_div, norm_mul, hw, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2)]
  have hratio : ((‖z₂‖ : ℝ) : ℂ) / z₂ = w := by
    rw [hz₂norm, hz₂]
    field_simp
  have hsq : ‖z₁‖ ^ 2 + ‖z₂‖ ^ 2 = 1 := by
    rw [hz₁norm, hz₂norm, hr2, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hle : ‖z₁‖ ≤ ‖z₂‖ := by
    rw [hz₁norm, hz₂norm, hrdef]
    exact div_sqrt_two_le_sqrt_one_sub hzn (norm_nonneg (z : ℂ))
  refine ⟨⟨⟨mkVec z₁ z₂, mkVec_mem_unitSphere hsq⟩, ?_⟩, ?_⟩
  · show ‖c₁ (mkVec z₁ z₂)‖ ≤ ‖c₂ (mkVec z₁ z₂)‖
    rw [c₁_mkVec, c₂_mkVec]
    exact hle
  · refine Prod.ext ?_ ?_
    · show (capPt ⟨⟨mkVec z₁ z₂, mkVec_mem_unitSphere hsq⟩, _⟩).1 = θ
      rw [capPt_fst]
      apply circleOf_injective
      rw [circleOf_circOf]
      simp only [Subtype.coe_mk, c₂_mkVec]
      rw [hratio, hw2]
    · refine Subtype.ext ?_
      show ((capPt ⟨⟨mkVec z₁ z₂, mkVec_mem_unitSphere hsq⟩, _⟩).2 : ℂ) = (z : ℂ)
      rw [capPt_snd]
      simp only [Subtype.coe_mk, c₁_mkVec, c₂_mkVec]
      rw [hz₂norm, hz₁, hz₂]
      field_simp

/-- **`confPt` is onto `D² × S¹`.** -/
lemma confPt_surjective : Function.Surjective confPt := by
  rintro ⟨z, θ⟩
  obtain ⟨w, hw, hw2⟩ := exists_sq_circleOf θ
  have hwne : w ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hw; norm_num at hw
  have hzn : ‖(z : ℂ)‖ ≤ 1 := by
    have h := z.2
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    exact h
  set r : ℝ := Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2 / 2) with hrdef
  have hr2 : r ^ 2 = 1 - ‖(z : ℂ)‖ ^ 2 / 2 := by
    rw [hrdef, Real.sq_sqrt (one_sub_sq_div_two_nonneg hzn (norm_nonneg (z : ℂ)))]
  have hrpos : 0 < r := by
    rw [hrdef]
    exact Real.sqrt_pos.mpr (one_sub_sq_div_two_pos hzn (norm_nonneg (z : ℂ)))
  have hrneC : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hrpos)
  set z₁ : ℂ := ((r : ℝ) : ℂ) * w with hz₁
  set z₂ : ℂ := (z : ℂ) / ((Real.sqrt 2 : ℂ) * w) with hz₂
  have hz₁norm : ‖z₁‖ = r := by
    rw [hz₁, norm_mul, hw, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrpos.le]
  have hz₂norm : ‖z₂‖ = ‖(z : ℂ)‖ / Real.sqrt 2 := by
    rw [hz₂, norm_div, norm_mul, hw, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2)]
  have hratio : z₁ / ((‖z₁‖ : ℝ) : ℂ) = w := by
    rw [hz₁norm, hz₁]
    field_simp
  have hsq : ‖z₁‖ ^ 2 + ‖z₂‖ ^ 2 = 1 := by
    rw [hz₁norm, hz₂norm, hr2, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hle : ‖z₂‖ ≤ ‖z₁‖ := by
    rw [hz₂norm, hz₁norm, hrdef]
    exact div_sqrt_two_le_sqrt_one_sub hzn (norm_nonneg (z : ℂ))
  refine ⟨⟨⟨mkVec z₁ z₂, mkVec_mem_unitSphere hsq⟩, ?_⟩, ?_⟩
  · show ‖c₂ (mkVec z₁ z₂)‖ ≤ ‖c₁ (mkVec z₁ z₂)‖
    rw [c₁_mkVec, c₂_mkVec]
    exact hle
  · refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      show ((confPt ⟨⟨mkVec z₁ z₂, mkVec_mem_unitSphere hsq⟩, _⟩).1 : ℂ) = (z : ℂ)
      rw [confPt_fst]
      simp only [Subtype.coe_mk, c₁_mkVec, c₂_mkVec]
      rw [hz₁norm, hz₁, hz₂]
      field_simp
    · show (confPt ⟨⟨mkVec z₁ z₂, mkVec_mem_unitSphere hsq⟩, _⟩).2 = θ
      rw [confPt_snd]
      apply circleOf_injective
      rw [circleOf_circOf]
      simp only [Subtype.coe_mk, c₁_mkVec]
      rw [hratio, hw2]

/-! ## The two branches of `phi` -/

/-- `phi` on the cap hemisphere. -/
lemma phi_of_cap (v : unitSphere 3) (h : ‖c₁ v.1‖ ≤ ‖c₂ v.1‖) :
    phi v = Quotient.mk'' (Sum.inl (capPt ⟨v, h⟩)) := by
  rw [phi, dif_pos h]

/-- `phi` on the configuration hemisphere: on the common boundary the two branches agree in the
quotient, which is `phiCap_eq_phiConf`. -/
lemma phi_of_conf (v : unitSphere 3) (h : ‖c₂ v.1‖ ≤ ‖c₁ v.1‖) :
    phi v = Quotient.mk'' (Sum.inr (confPt ⟨v, h⟩)) := by
  by_cases h' : ‖c₁ v.1‖ ≤ ‖c₂ v.1‖
  · rw [phi, dif_pos h']
    have heq : ‖c₁ v.1‖ = ‖c₂ v.1‖ := le_antisymm h' h
    have hcc := phiCap_eq_phiConf v heq
    rw [phiCap, phiConf, dif_pos h', dif_pos h] at hcc
    exact hcc
  · rw [phi, dif_neg h']

/-! ## The glueing map is surjective -/

/-- **The glueing map `phi : S³ → LensSpace` is surjective.**  Each point of `LensSpace` is the class
of a point of `CapTorus` or of `ConfTorus`, and the maps `capPt` and `confPt` are surjective onto
their solid tori. -/
theorem phi_surjective : Function.Surjective phi := by
  intro q
  obtain ⟨x, hx⟩ := Quotient.exists_rep q
  rcases x with ⟨θ, z⟩ | ⟨z, θ⟩
  · obtain ⟨⟨v, h⟩, hv⟩ := capPt_surjective (θ, z)
    refine ⟨v, ?_⟩
    rw [phi_of_cap v h, hv]
    exact hx
  · obtain ⟨⟨v, h⟩, hv⟩ := confPt_surjective (z, θ)
    refine ⟨v, ?_⟩
    rw [phi_of_conf v h, hv]
    exact hx

end

end Work.Drive
