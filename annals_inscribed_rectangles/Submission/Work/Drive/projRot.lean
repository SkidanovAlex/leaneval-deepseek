import Mathlib
import Submission.Work.Drive.projCharted
import Submission.Work.Drive.contMDiffAt_projCharted_iff
import Submission.Work.Drive.confProjVecOf_data_span
import Submission.Work.Drive.confProjVecOf_fderiv_span
import Submission.Work.Drive.capConeSmooth
import Submission.Work.Drive.lensToProj_confTorus
import Submission.Work.Drive.omegaChainInterface
import Submission.Work.Drive.phi_surjective

/-!
# The rotation of `ℝP³` induced by the rotation of the capping space

The rotation `Work.Drive.rotCapping` of the capping space `Y = CappingSpace` of Hugelmeyer's fifth
auxiliary result is defined on the quotient of the configuration and cap pieces, and the capping space
carries the *transparent* smooth structure `Work.Drive.cappingCharted`, transported along the
homeomorphism `Work.Drive.cappingSpaceHomeoProj : CappingSpace ≃ₜ (0,∞) × ℝP³`.  In those coordinates
the rotation acts on the `ℝP³` factor only, by the **projectivisation of the diagonal rotation of
`ℂ² ≅ ℝ⁴`**

`D_t (z₁, z₂) = (e^{iπt} z₁, e^{-iπt} z₂)`,

i.e. multiplication of the first complex coordinate by `e^{iπt}` and of the second by its conjugate.
(The half angle is forced: the configuration boundary circle coordinate is the *doubled* direction
`(z₁/‖z₁‖)²`, so a rotation of `S³` by `e^{iπt}` in the first coordinate adds `t` — not `2t` — to it;
and the cap coordinate `(‖z₂‖/z₂)²` moves by `+t` under `z₂ ↦ e^{-iπt} z₂`.)

This file collects the *algebraic* dictionary between the two pictures:

* `Work.Drive.circ`, `Work.Drive.diagRot` and their basic computation rules
  (`c₁_diagRot`, `c₂_diagRot`, `diagRot_add`, `norm_diagRot`, `contDiff_diagRot`);
* `Work.Drive.projRot` — the induced map of `ℝP³`, its action on representatives
  (`projRot_mk`), the invariance of the projective charts (`projRot_mem_projChartSource_iff`) and the
  **chart formula** `projChartMap_projRot_of_mem` expressing its chart coordinates through the
  standard section `projSection i`;
* the compatibility with the sphere lifts `capProjVecOf`/`confProjVecOf` of the two solid tori
  (`diagRot_capProjVecOf`, `diagRot_confProjVecOf`), and the **equivariance with `lensToProj`**:
  `lensToProj (rotLens t q) = projRot t (lensToProj q)` for `t : ℝ` (`lensToProj_rotLens`).

The smoothness of the action is proved on top of these in `Submission/Work/Drive/projRotSmooth.lean`.
-/

set_option autoImplicit false

namespace Work.Drive

open scoped LinearAlgebra.Projectivization Manifold ContDiff Topology
open Set

noncomputable section

/-! ## The half-angle circle element -/

/-- `e^{iπt}`, as the point `circleOf (t/2)` of the unit circle. -/
def circ (t : ℝ) : ℂ := circleOf ((t / 2 : ℝ) : UnitAddCircle)

@[simp] lemma circ_zero : circ 0 = 1 := by
  apply Complex.ext
  · rw [circ, circleOf_coe_re]
    norm_num
  · rw [circ, circleOf_coe_im]
    norm_num

lemma norm_circ (t : ℝ) : ‖circ t‖ = 1 := norm_circleOf _

lemma circ_add (s t : ℝ) : circ (s + t) = circ s * circ t := by
  have h : ((s + t) / 2 : ℝ) = s / 2 + t / 2 := by ring
  rw [circ, circ, circ, h, AddCircle.coe_add, circleOf_add]

/-- `circ (-t)` is the conjugate of `circ t`. -/
lemma circ_neg (t : ℝ) : circ (-t) = star (circ t) := by
  apply Complex.ext
  · rw [Complex.star_def, Complex.conj_re, circ, circ, circleOf_coe_re, circleOf_coe_re,
      show 2 * Real.pi * (-t / 2) = -(2 * Real.pi * (t / 2)) by ring, Real.cos_neg]
  · rw [Complex.star_def, Complex.conj_im, circ, circ, circleOf_coe_im, circleOf_coe_im,
      show 2 * Real.pi * (-t / 2) = -(2 * Real.pi * (t / 2)) by ring, Real.sin_neg]

/-- `(circ t)^2 = circleOf t`: `circ t` is a square root of the circle element of `t`. -/
lemma circ_sq (t : ℝ) : circ t ^ 2 = circleOf ((t : ℝ) : UnitAddCircle) := by
  have h : ((t : ℝ) : UnitAddCircle) = ((t / 2 : ℝ) : UnitAddCircle)
      + ((t / 2 : ℝ) : UnitAddCircle) := by
    rw [← AddCircle.coe_add]
    congr 1
    ring
  rw [h, circleOf_add, circ, pow_two]

lemma contDiff_circ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => circ t) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : ℝ => circleOf ((s : ℝ) : UnitAddCircle)) := contDiff_circleOf_coe
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => t / 2) := by fun_prop
  have := h1.comp h2
  simpa [circ, Function.comp_def] using this

/-! ## The diagonal rotation of `ℂ² = ℝ⁴` -/

/-- **The diagonal rotation**: multiplication of the first complex coordinate of `ℂ² ≅ ℝ⁴` by
`e^{iπt}` and of the second by its conjugate. -/
def diagRot (t : ℝ) (x : Eucl 3) : Eucl 3 :=
  ofComplex (circ t * c₁ x) (star (circ t) * c₂ x)

@[simp] lemma c₁_diagRot (t : ℝ) (x : Eucl 3) : c₁ (diagRot t x) = circ t * c₁ x := by
  simp only [diagRot, c₁_ofComplex]

@[simp] lemma c₂_diagRot (t : ℝ) (x : Eucl 3) : c₂ (diagRot t x) = star (circ t) * c₂ x := by
  simp only [diagRot, c₂_ofComplex]

/-- `ofComplex` of equal complex coordinates is equal. -/
lemma ofComplex_congr {z z' w w' : ℂ} (h : z = w) (h' : z' = w') :
    ofComplex z z' = ofComplex w w' := by rw [h, h']

lemma diagRot_zero (x : Eucl 3) : diagRot 0 x = x := by
  rw [diagRot, circ_zero, one_mul, star_one, one_mul, ofComplex_c₁_c₂]

lemma diagRot_add (s t : ℝ) (x : Eucl 3) : diagRot s (diagRot t x) = diagRot (s + t) x := by
  simp only [diagRot, c₁_ofComplex, c₂_ofComplex]
  refine ofComplex_congr ?_ ?_
  · rw [← mul_assoc, circ_add]
  · rw [circ_add, star_mul]
    ring

/-- The two complex coordinates are `ℝ`-linear (they are the continuous linear maps
`confProjVecOf_c₁CLM`, `confProjVecOf_c₂CLM`). -/
lemma c₁_smul (a : ℝ) (x : Eucl 3) : c₁ (a • x) = (a : ℂ) * c₁ x := by
  rw [← confProjVecOf_c₁CLM_apply, ← confProjVecOf_c₁CLM_apply, map_smul, Complex.real_smul]

lemma c₂_smul (a : ℝ) (x : Eucl 3) : c₂ (a • x) = (a : ℂ) * c₂ x := by
  rw [← confProjVecOf_c₂CLM_apply, ← confProjVecOf_c₂CLM_apply, map_smul, Complex.real_smul]

lemma smul_ofComplex (a : ℝ) (z z' : ℂ) :
    a • ofComplex z z' = ofComplex ((a : ℂ) * z) ((a : ℂ) * z') := by
  have h1 : c₁ (a • ofComplex z z') = (a : ℂ) * z := by rw [c₁_smul, c₁_ofComplex]
  have h2 : c₂ (a • ofComplex z z') = (a : ℂ) * z' := by rw [c₂_smul, c₂_ofComplex]
  rw [show a • ofComplex z z'
      = ofComplex (c₁ (a • ofComplex z z')) (c₂ (a • ofComplex z z')) from
    (ofComplex_c₁_c₂ _).symm, h1, h2]

lemma diagRot_smul (t : ℝ) (a : ℝ) (x : Eucl 3) : diagRot t (a • x) = a • diagRot t x := by
  simp only [diagRot, c₁_ofComplex, c₂_ofComplex]
  rw [smul_ofComplex]
  refine ofComplex_congr ?_ ?_
  · rw [c₁_smul]
    ring
  · rw [c₂_smul]
    ring

lemma norm_diagRot (t : ℝ) (x : Eucl 3) : ‖diagRot t x‖ = ‖x‖ := by
  have h := norm_sq_c₁_c₂ (diagRot t x)
  rw [c₁_diagRot, c₂_diagRot, norm_mul, norm_mul, norm_circ, norm_star, norm_circ,
    one_mul, one_mul] at h
  rw [← norm_sq_c₁_c₂ x] at h
  have h2 := congrArg Real.sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h2

lemma diagRot_ne_zero (t : ℝ) {x : Eucl 3} (hx : x ≠ 0) : diagRot t x ≠ 0 := by
  intro h
  have h1 : ‖diagRot t x‖ = 0 := by rw [h, norm_zero]
  rw [norm_diagRot] at h1
  exact hx (norm_eq_zero.mp h1)

lemma contDiffAt_diagRot (t : ℝ) (x : Eucl 3) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × Eucl 3 => diagRot q.1 q.2) (t, x) := by
  set n : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞) with hn
  have hc : ContDiffAt ℝ n (fun q : ℝ × Eucl 3 => circ q.1) (t, x) :=
    contDiff_circ.contDiffAt.comp (t, x) (contDiffAt_fst (n := n))
  have hc' : ContDiffAt ℝ n (fun q : ℝ × Eucl 3 => star (circ q.1)) (t, x) := by
    have h : ContDiffAt ℝ n (fun q : ℝ × Eucl 3 => circ (-q.1)) (t, x) :=
      contDiff_circ.contDiffAt.comp (t, x) ((contDiffAt_fst (n := n)).neg)
    rwa [show (fun q : ℝ × Eucl 3 => circ (-q.1)) = fun q => star (circ q.1) from
      funext (fun q => circ_neg q.1)] at h
  have hA : ContDiffAt ℝ n (fun q : ℝ × Eucl 3 => c₁ q.2) (t, x) := by
    have h := (confProjVecOf_c₁CLM.contDiff (n := n)).contDiffAt.comp (t, x)
      (contDiffAt_snd (n := n))
    simpa [Function.comp_def] using h
  have hB : ContDiffAt ℝ n (fun q : ℝ × Eucl 3 => c₂ q.2) (t, x) := by
    have h := (confProjVecOf_c₂CLM.contDiff (n := n)).contDiffAt.comp (t, x)
      (contDiffAt_snd (n := n))
    simpa [Function.comp_def] using h
  have h1 : ContDiffAt ℝ n (fun q : ℝ × Eucl 3 => circ q.1 * c₁ q.2) (t, x) := hc.mul hA
  have h2 : ContDiffAt ℝ n (fun q : ℝ × Eucl 3 => star (circ q.1) * c₂ q.2) (t, x) := hc'.mul hB
  have h := confProjVecOf_contDiffAt_ofComplex h1 h2
  simp only [diagRot]
  exact h

lemma contDiff_diagRot :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × Eucl 3 => diagRot q.1 q.2) :=
  contDiff_iff_contDiffAt.mpr (fun q => contDiffAt_diagRot q.1 q.2)

/-! ## The induced map of `ℝP³` -/

/-- **The rotation of `ℝP³`**: the projectivisation of the diagonal rotation `diagRot t`. -/
def projRot (t : ℝ) (p : ℙ ℝ (Eucl 3)) : ℙ ℝ (Eucl 3) :=
  Projectivization.mk ℝ (diagRot t p.rep) (diagRot_ne_zero t (Projectivization.rep_nonzero p))

lemma projRot_mk (t : ℝ) (v : Eucl 3) (hv : v ≠ 0) :
    projRot t (Projectivization.mk ℝ v hv)
      = Projectivization.mk ℝ (diagRot t v) (diagRot_ne_zero t hv) := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℝ (Projectivization.rep _) v
    (Projectivization.rep_nonzero _) hv).mp (Projectivization.mk_rep _)
  have key : diagRot t (Projectivization.rep (Projectivization.mk ℝ v hv))
      = a • diagRot t v := by
    rw [← ha]
    simp only [Units.smul_def, diagRot_smul]
  exact (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).mpr ⟨a, key.symm⟩


lemma projChartMap_projRot_of_mem (t : ℝ) (i : Fin 4) (p : ℙ ℝ (Eucl 3))
    (hp : p ∈ projChartSource i) :
    projChartMap i (projRot t p)
      = projCoordFun i (diagRot t (projSection i (projChartMap i p))) := by
  conv_lhs => rw [← projChartInv_projChartMap hp]
  rw [projChartInv, projRot_mk, projChartMap_mk]

/-! ## Compatibility with the sphere lifts of the solid tori -/

lemma diagRot_capProjVecOf (t : ℝ) (w d : ℂ) :
    diagRot t (capProjVecOf w d) = capProjVecOf (circ t * w) d := by
  simp only [diagRot, capProjVecOf, c₁_ofComplex, c₂_ofComplex, div_eq_mul_inv]
  refine ofComplex_congr ?_ ?_
  · ring
  · rw [star_mul]
    ring

lemma diagRot_confProjVecOf (t : ℝ) (u d : ℂ) :
    diagRot t (confProjVecOf u d) = confProjVecOf (circ t * u) d := by
  simp only [diagRot, confProjVecOf, c₁_ofComplex, c₂_ofComplex, div_eq_mul_inv]
  refine ofComplex_congr ?_ ?_
  · ring
  · rw [star_mul]
    ring

/-! ## Equivariance with the projection of the slice

The rotation of `LensSpace` (addition of the angle to the doubled-direction coordinate) corresponds,
through the projection `lensToProj : LensSpace → ℝP³`, to the rotation `projRot` of `ℝP³`.  This is the
key computation that identifies the action of the capping space on its `ℝP³` coordinate. -/

theorem lensToProj_rotLens (t : ℝ) (q : LensSpace) :
    lensToProj (rotLens ((t : ℝ) : UnitAddCircle) q) = projRot t (lensToProj q) := by
  induction q using Quotient.inductionOn with
  | h p =>
    rcases p with ⟨θ, d⟩ | ⟨d, η⟩
    · obtain ⟨w, -, hw⟩ := exists_sq_circleOf θ
      have hcirc : (circ t * w) ^ 2 = circleOf (θ + ((t : ℝ) : UnitAddCircle)) := by
        rw [mul_pow, hw, circ_sq, circleOf_add, mul_comm]
      rw [rotLens_mk, rotLensSum_inl, lensToProj_capTorus θ d hw, projRot_mk, rotCapTorus,
        lensToProj_capTorus (θ + ((t : ℝ) : UnitAddCircle)) d (w := circ t * w) hcirc]
      exact (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
        ⟨1, by rw [one_smul, diagRot_capProjVecOf]⟩
    · obtain ⟨u, -, hu⟩ := exists_sq_circleOf η
      have hcirc : (circ t * u) ^ 2 = circleOf (η + ((t : ℝ) : UnitAddCircle)) := by
        rw [mul_pow, hu, circ_sq, circleOf_add, mul_comm]
      rw [rotLens_mk, rotLensSum_inr, lensToProj_confTorus d η hu, projRot_mk, rotConfTorus,
        lensToProj_confTorus d (η + ((t : ℝ) : UnitAddCircle)) (u := circ t * u) hcirc]
      exact (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
        ⟨1, by rw [one_smul, diagRot_confProjVecOf]⟩

/-! ## The rotation on the two pieces of the capping space

`rotCapping` is defined by descending `rotSum` (addition of the angle to the doubled direction on the
configuration piece, resp. to the `S¹`-coordinate on the cap piece) along the gluing `cappingRel`.
The two computation rules below are what lets a *presentation* of a plane given piecewise (through
`Work.Drive.contMDiffAt_confPiece_mk` / `contMDiffAt_capPiece_mk`) be rotated: the rotation only
changes the data by `circleOf η ↦ circleOf η · circleOf u` (configuration piece) and likewise on the
cap piece. -/

/-- The rotation on the configuration piece: it adds the angle to the doubled direction. -/
theorem rotCapping_mk_inl (u : UnitAddCircle) (p : ConfigPiece) :
    rotCapping u (Quotient.mk'' (Sum.inl p) : CappingSpace)
      = Quotient.mk'' (Sum.inl (rotConfig u p)) := by
  rw [rotCapping_mk, rotSum_inl]

/-- The rotation on the cap piece: it adds the angle to the cap's `S¹`-coordinate. -/
theorem rotCapping_mk_inr (u : UnitAddCircle) (p : CapPiece) :
    rotCapping u (Quotient.mk'' (Sum.inr p) : CappingSpace)
      = Quotient.mk'' (Sum.inr (rotCap u p)) := by
  rw [rotCapping_mk, rotSum_inr]

/-- The rotated configuration point, as a pair of a point of the configuration torus and a proof:
the rotation adds the angle to the doubled direction. -/
@[simp] lemma rotConfig_val (u : UnitAddCircle) (p : ConfigPiece) :
    ((rotConfig u p : ConfigPiece) : ℝ × ℂ × UnitAddCircle) = (p.1.1, p.1.2.1, p.1.2.2 + u) := rfl

end
end Work.Drive
