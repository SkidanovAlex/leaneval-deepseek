import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2Lead.twistDefs
import Submission.Work.Drive.N2Lead.starShapedRadial
import Submission.Work.Drive.N2Lead.isCertifiedAt_of_roundImage
import Submission.Work.Drive.N2Lead.isCertifiedAt_of_ambientPath
import Submission.Work.Drive.N2Lead.isLevelIsotopy_ambient_local
import Submission.Work.Drive.N2Lead.isLevelIsotopy_squash

/-!
# Tier `D2b`/`D2c`: the star-shaped certificate with **one centre per component**

`Work.Drive.N2Lead.isCertifiedAt_of_starShaped` (`N2Lead/isCertifiedAt_of_starShaped.lean`) reduces a
certificate to the star rows *about the origin* — that works only for a level with a **single**
component (a second closed curve would meet every ray).  The split/merge saddles have a certificate
level with **two** components, each star-shaped about its own centre (`o_R`, `o_L` of §5.2/§5.3 of
`N2Lead/NOTES_LEAD_coherentWindows.md`).  This file supplies the corresponding engine:

* `plCLM`/`pl` — the planar inclusion `ℂ → ℝ³`;
* `radFlat o r s` — the *flattening radial map* with centre `o` and radius `r`: at `s = 0` the
  identity, at `s = 1` the map `w ↦ o + (r / ‖proj2 (w - o)‖) • pl (proj2 (w - o))`, whose image is
  the round circle of radius `r` about `o` *in the plane* `z = o 2` (the planar projection alone is
  not enough: the value has to be planar for `isCertifiedAt_of_roundImage`);
* `isCertifiedAt_of_ambientPath_local` — the image-local variant of the proved
  `isCertifiedAt_of_ambientPath` (Tier `D2d.2`), needed because the per-component maps below are only
  injective/immersive *near the picture*;
* `isCertifiedAt_of_starShaped_components` — the engine.

The proof of the engine: separate the components by a bump-localised translation `F₁` (so that the
flattening images of different components land in disjoint balls), then apply the bump-localised
flattening radial map `F₂` component by component.  The star rows are consumed at the *original*
centres `o i`, because the translation cancels in `proj2 (· - (o i + T i))`.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Function

noncomputable section

/-! ## The planar inclusion -/

/-- The planar inclusion `z ↦ (z.re, z.im, 0)` as a continuous linear map. -/
noncomputable def plCLM : ℂ →L[ℝ] E3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 ![z.re, z.im, (0 : ℝ)]
      map_add' := fun a b => by ext i <;> fin_cases i <;> simp
      map_smul' := fun c a => by ext i <;> fin_cases i <;> simp }

/-- The planar inclusion `z ↦ (z.re, z.im, 0)`. -/
noncomputable def pl (z : ℂ) : E3 := plCLM z

@[simp] lemma plCLM_apply (z : ℂ) : plCLM z = pl z := rfl
@[simp] lemma pl_apply_zero (z : ℂ) : (pl z) 0 = z.re := rfl
@[simp] lemma pl_apply_one (z : ℂ) : (pl z) 1 = z.im := rfl
@[simp] lemma pl_apply_two (z : ℂ) : (pl z) 2 = 0 := rfl

lemma proj2_pl (z : ℂ) : proj2 (pl z) = z := by
  apply Complex.ext <;> simp [proj2]

/-- The vertical part `(0, 0, w 2)` of a vector. -/
noncomputable def zpart (w : E3) : E3 := w - pl (proj2 w)

@[simp] lemma zpart_apply_zero (w : E3) : (zpart w) 0 = 0 := by
  show (w - pl (proj2 w)) 0 = 0
  rw [PiLp.sub_apply, pl_apply_zero, proj2]
  simp

@[simp] lemma zpart_apply_one (w : E3) : (zpart w) 1 = 0 := by
  show (w - pl (proj2 w)) 1 = 0
  rw [PiLp.sub_apply, pl_apply_one, proj2]
  simp

@[simp] lemma zpart_apply_two (w : E3) : (zpart w) 2 = w 2 := by
  show (w - pl (proj2 w)) 2 = w 2
  rw [PiLp.sub_apply, pl_apply_two]
  simp

lemma pl_proj2_add_zpart (w : E3) : pl (proj2 w) + zpart w = w := by
  show pl (proj2 w) + (w - pl (proj2 w)) = w
  abel

lemma zpart_pl (z : ℂ) : zpart (pl z) = 0 := by
  show pl z - pl (proj2 (pl z)) = 0
  rw [proj2_pl, sub_self]

/-! ## The flattening radial map -/

/-- **The flattening radial map** with centre `o` and radius `r`: at time `s` it moves `w` towards
the point `o + (r / ‖proj2 (w - o)‖) • pl (proj2 (w - o))` of the round circle of radius `r` about
`o` inside the plane `z = o 2`.  At `s = 0` it is the identity. -/
noncomputable def radFlat (o : E3) (r s : ℝ) (v : E3) : E3 :=
  o + ((1 - Real.smoothTransition s) + Real.smoothTransition s * (r / ‖proj2 (v - o)‖))
        • pl (proj2 (v - o))
      + (1 - Real.smoothTransition s) • zpart (v - o)

@[simp] lemma radFlat_zero (o : E3) (r : ℝ) (v : E3) : radFlat o r 0 v = v := by
  have h0 : Real.smoothTransition (0 : ℝ) = 0 := Real.smoothTransition.zero_of_nonpos le_rfl
  rw [radFlat, h0]
  simp only [sub_zero, zero_mul, add_zero, one_smul]
  rw [show o + pl (proj2 (v - o)) + zpart (v - o)
        = o + (pl (proj2 (v - o)) + zpart (v - o)) by abel,
      pl_proj2_add_zpart]
  abel

@[simp] lemma radFlat_one (o : E3) (r : ℝ) (v : E3) :
    radFlat o r 1 v = o + (r / ‖proj2 (v - o)‖) • pl (proj2 (v - o)) := by
  have h1 : Real.smoothTransition (1 : ℝ) = 1 := Real.smoothTransition.one_of_one_le le_rfl
  rw [radFlat, h1]
  simp

/-! ## Smoothness of the flattening radial map -/

/-- The planar inclusion is smooth. -/
lemma contDiff_pl : ContDiff ℝ tpC (pl : ℂ → E3) := plCLM.contDiff

/-- The vertical part is smooth. -/
lemma contDiff_zpart : ContDiff ℝ tpC (zpart : E3 → E3) := by
  have h : (zpart : E3 → E3) = fun w : E3 => w - pl (proj2 w) := rfl
  rw [h]
  exact contDiff_id.sub (contDiff_pl.comp proj2CLM.contDiff)

/-- The auxiliary form of the flattening radial map, in the variable `u = v - o`. -/
noncomputable def radFlatAux (o : E3) (r s : ℝ) (u : E3) : E3 :=
  o + ((1 - Real.smoothTransition s) + Real.smoothTransition s * (r / ‖proj2 u‖))
        • pl (proj2 u)
      + (1 - Real.smoothTransition s) • zpart u

lemma radFlat_eq_aux (o : E3) (r s : ℝ) (v : E3) :
    radFlat o r s v = radFlatAux o r s (v - o) := rfl

/-- **Joint smoothness of the flattening radial map** off the singular set. -/
lemma contDiffAt_uncurry_radFlatAux (o : E3) (r : ℝ) {s : ℝ} {u : E3}
    (hu : proj2 u ≠ 0) :
    ContDiffAt ℝ tpC (Function.uncurry (radFlatAux o r)) (s, u) := by
  have hσ : ContDiffAt ℝ tpC (fun p : ℝ × E3 => Real.smoothTransition p.1) (s, u) :=
    Real.smoothTransition.contDiff.contDiffAt.comp (s, u) contDiffAt_fst
  have hproj : ContDiffAt ℝ tpC (fun p : ℝ × E3 => proj2 p.2) (s, u) :=
    proj2CLM.contDiff.contDiffAt.comp (s, u) contDiffAt_snd
  have hpn : ContDiffAt ℝ tpC (fun p : ℝ × E3 => ‖proj2 p.2‖) (s, u) := hproj.norm ℂ hu
  have hinv : ContDiffAt ℝ tpC (fun p : ℝ × E3 => (‖proj2 p.2‖)⁻¹) (s, u) :=
    hpn.inv (norm_ne_zero_iff.mpr hu)
  have hpl : ContDiffAt ℝ tpC (fun p : ℝ × E3 => pl (proj2 p.2)) (s, u) :=
    contDiff_pl.contDiffAt.comp (s, u) hproj
  have hzp : ContDiffAt ℝ tpC (fun p : ℝ × E3 => zpart p.2) (s, u) :=
    contDiff_zpart.contDiffAt.comp (s, u) contDiffAt_snd
  have hcoef : ContDiffAt ℝ tpC (fun p : ℝ × E3 =>
      (1 - Real.smoothTransition p.1) + Real.smoothTransition p.1 * (r * (‖proj2 p.2‖)⁻¹))
      (s, u) :=
    (contDiffAt_const.sub hσ).add (hσ.mul (contDiffAt_const.mul hinv))
  have hmain : ContDiffAt ℝ tpC (fun p : ℝ × E3 =>
      o + ((1 - Real.smoothTransition p.1)
          + Real.smoothTransition p.1 * (r * (‖proj2 p.2‖)⁻¹)) • pl (proj2 p.2)
        + (1 - Real.smoothTransition p.1) • zpart p.2) (s, u) :=
    (contDiffAt_const.add (hcoef.smul hpl)).add ((contDiffAt_const.sub hσ).smul hzp)
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards with p
  rw [Function.uncurry_apply_pair, radFlatAux, div_eq_mul_inv]

/-! ## Coordinates of the flattening radial map -/

@[simp] lemma proj2_zero : proj2 (0 : E3) = 0 := by
  apply Complex.ext <;> simp [proj2]

lemma proj2_neg (x : E3) : proj2 (-x) = -proj2 x := by
  apply Complex.ext <;> simp [proj2]

lemma proj2_sub (x y : E3) : proj2 (x - y) = proj2 x - proj2 y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, proj2_add, proj2_neg]

lemma proj2_zpart (w : E3) : proj2 (zpart w) = 0 := by
  apply Complex.ext <;> simp [proj2, zpart_apply_zero, zpart_apply_one]

/-- The planar projection of `radFlat o r s a - o`. -/
lemma proj2_radFlat_sub (o : E3) (r s : ℝ) (a : E3) :
    proj2 (radFlat o r s a - o) = radCoeff r s (a - o) • proj2 (a - o) := by
  have h : radFlat o r s a - o
      = ((1 - Real.smoothTransition s)
          + Real.smoothTransition s * (r / ‖proj2 (a - o)‖)) • pl (proj2 (a - o))
        + (1 - Real.smoothTransition s) • zpart (a - o) := by
    rw [radFlat]; abel
  rw [h]
  simp only [proj2_add, proj2_smul, proj2_pl, proj2_zpart, smul_zero, add_zero, radCoeff]

/-- The third coordinate of `radFlat o r s a - o`. -/
lemma radFlat_sub_apply_two (o : E3) (r s : ℝ) (a : E3) :
    (radFlat o r s a - o) 2 = (1 - Real.smoothTransition s) * ((a - o) 2) := by
  have h : radFlat o r s a - o
      = ((1 - Real.smoothTransition s)
          + Real.smoothTransition s * (r / ‖proj2 (a - o)‖)) • pl (proj2 (a - o))
        + (1 - Real.smoothTransition s) • zpart (a - o) := by
    rw [radFlat]; abel
  rw [h]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, pl_apply_two, mul_zero, zero_add,
    zpart_apply_two]

/-- **The flattening radial map is injective on a star-shaped set.** -/
theorem radFlat_injOn {o : E3} {r s : ℝ} (hr : 0 < r) {K : Set E3}
    (hne : ∀ v ∈ K, proj2 (v - o) ≠ 0)
    (hray : ∀ a ∈ K, ∀ b ∈ K,
      (∃ t : ℝ, 0 < t ∧ proj2 (a - o) = t • proj2 (b - o)) → a = b) :
    Set.InjOn (radFlat o r s) K := by
  intro a ha b hb hab
  have hpa : proj2 (a - o) ≠ 0 := hne a ha
  have hpb : proj2 (b - o) ≠ 0 := hne b hb
  have hca : 0 < radCoeff r s (a - o) := radCoeff_pos hr s hpa
  have hcb : 0 < radCoeff r s (b - o) := radCoeff_pos hr s hpb
  have hproj : radCoeff r s (a - o) • proj2 (a - o)
      = radCoeff r s (b - o) • proj2 (b - o) := by
    have h := congrArg (fun x : E3 => proj2 (x - o)) hab
    rw [proj2_radFlat_sub, proj2_radFlat_sub] at h
    exact h
  refine hray a ha b hb ⟨radCoeff r s (b - o) / radCoeff r s (a - o), div_pos hcb hca, ?_⟩
  have h := congrArg (fun z : ℂ => (radCoeff r s (a - o))⁻¹ • z) hproj
  rw [smul_smul, smul_smul, inv_mul_cancel₀ hca.ne', one_smul] at h
  simpa [div_eq_inv_mul] using h

/-- The slice of the flattening radial map is smooth off the singular set. -/
lemma contDiffAt_radFlat (o : E3) (r s : ℝ) {v : E3} (hv : proj2 (v - o) ≠ 0) :
    ContDiffAt ℝ tpC (radFlat o r s) v := by
  have h := contDiffAt_uncurry_radFlatAux (o := o) (r := r) (s := s) (u := v - o) hv
  have hcomp := h.comp v (contDiffAt_const.prodMk (contDiffAt_id.sub contDiffAt_const))
  convert hcomp using 1
  ext w
  simp [Function.uncurry_apply_pair, radFlat_eq_aux]

/-! ## The derivative of the flattening radial map along a line -/

/-- **The derivative of the flattening radial map along a line.**  With `p = proj2 u` and
`q = proj2 w`, the derivative of `τ ↦ radFlatAux o r s (u + τ • w)` at `τ = 0` is
`(1 - σ s) • w + σ s • ((r / ‖p‖) • pl q - (r ⟪p, q⟫ / ‖p‖³) • pl p)`, where `σ` is
`Real.smoothTransition`. -/
theorem hasDerivAt_radFlatAux {o : E3} {r s : ℝ} {u w : E3} (hp : proj2 u ≠ 0) :
    HasDerivAt (fun τ : ℝ => radFlatAux o r s (u + τ • w))
      ((1 - Real.smoothTransition s) • w
        + Real.smoothTransition s •
          ((r / ‖proj2 u‖) • pl (proj2 w)
            - (r * inner ℝ (proj2 u) (proj2 w) / ‖proj2 u‖ ^ 3) • pl (proj2 u))) 0 := by
  have hnorm0 : 0 < ‖proj2 u‖ := norm_pos_iff.mpr hp
  -- the line and its projection
  have hline : HasDerivAt (fun τ : ℝ => u + τ • w) w 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const w).const_add u
  have hproj' : HasDerivAt (fun τ : ℝ => proj2 u + τ • proj2 w) (proj2 w) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (proj2 w)).const_add (proj2 u)
  have hproj : HasDerivAt (fun τ : ℝ => proj2 (u + τ • w)) (proj2 w) 0 :=
    hproj'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun τ => by simp [proj2_add, proj2_smul]))
  have hplline' : HasDerivAt (fun τ : ℝ => pl (proj2 u) + τ • pl (proj2 w)) (pl (proj2 w)) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (pl (proj2 w))).const_add (pl (proj2 u))
  have hplline : HasDerivAt (fun τ : ℝ => pl (proj2 (u + τ • w))) (pl (proj2 w)) 0 :=
    hplline'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun τ => by
        show pl (proj2 (u + τ • w)) = pl (proj2 u) + τ • pl (proj2 w)
        rw [proj2_add, proj2_smul]
        change plCLM (proj2 u + τ • proj2 w) = plCLM (proj2 u) + τ • plCLM (proj2 w)
        rw [map_add, map_smul]))
  -- the squared norm of the projection
  have hsq : HasDerivAt (fun τ : ℝ => ‖proj2 (u + τ • w)‖ ^ 2)
      (2 * inner ℝ (proj2 u) (proj2 w)) 0 := by
    simpa using hproj.norm_sq
  have hnorm : HasDerivAt (fun τ : ℝ => ‖proj2 (u + τ • w)‖)
      (inner ℝ (proj2 u) (proj2 w) / ‖proj2 u‖) 0 := by
    have hx : ‖proj2 u‖ ^ 2 ≠ 0 := pow_ne_zero 2 hnorm0.ne'
    have h1 := hsq.sqrt (by simpa using hx)
    simp only [zero_smul, add_zero] at h1
    rw [Real.sqrt_sq hnorm0.le] at h1
    have h3 : HasDerivAt (fun τ : ℝ => ‖proj2 (u + τ • w)‖)
        ((2 * inner ℝ (proj2 u) (proj2 w)) / (2 * ‖proj2 u‖)) 0 := by
      refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => ?_))
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    convert h3 using 1
    field_simp
  -- the inverse norm and the coefficient
  have hinv : HasDerivAt (fun τ : ℝ => (‖proj2 (u + τ • w)‖)⁻¹)
      (-(inner ℝ (proj2 u) (proj2 w) / ‖proj2 u‖) / ‖proj2 u‖ ^ 2) 0 := by
    have h := hnorm.inv (by
      show ‖proj2 (u + 0 • w)‖ ≠ 0
      simp only [zero_smul, add_zero]
      exact hnorm0.ne')
    simp only [zero_smul, add_zero] at h
    convert h using 1 <;> try rfl
  have hA : r * (-(inner ℝ (proj2 u) (proj2 w) / ‖proj2 u‖) / ‖proj2 u‖ ^ 2)
      = -(r * inner ℝ (proj2 u) (proj2 w) / ‖proj2 u‖ ^ 3) := by
    field_simp
  have hcoef : HasDerivAt (fun τ : ℝ => r / ‖proj2 (u + τ • w)‖)
      (-(r * inner ℝ (proj2 u) (proj2 w) / ‖proj2 u‖ ^ 3)) 0 := by
    have h := (hinv.const_mul r).congr_deriv hA
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun τ => ?_))
    simp only [div_eq_mul_inv]
  -- the radial term
  have hrad : HasDerivAt
      (fun τ : ℝ => (r / ‖proj2 (u + τ • w)‖) • pl (proj2 (u + τ • w)))
      ((r / ‖proj2 u‖) • pl (proj2 w)
        + (-(r * inner ℝ (proj2 u) (proj2 w) / ‖proj2 u‖ ^ 3)) • pl (proj2 u)) 0 := by
    have h := hcoef.smul hplline
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun τ => rfl))).congr_deriv ?_
    simp only [zero_smul, add_zero]
  -- the sum, with the constant `o`
  have hwhole : HasDerivAt
      (fun τ : ℝ => o + ((1 - Real.smoothTransition s) • (u + τ • w)
          + Real.smoothTransition s
              • ((r / ‖proj2 (u + τ • w)‖) • pl (proj2 (u + τ • w)))))
      ((1 - Real.smoothTransition s) • w
        + Real.smoothTransition s •
          ((r / ‖proj2 u‖) • pl (proj2 w)
            + (-(r * inner ℝ (proj2 u) (proj2 w) / ‖proj2 u‖ ^ 3)) • pl (proj2 u))) 0 := by
    have h := ((hline.const_smul (1 - Real.smoothTransition s)).add
      (hrad.const_smul (Real.smoothTransition s))).const_add o
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun τ => rfl))).congr_deriv ?_
    simp only [zero_smul, add_zero]
  have hfun : (fun τ : ℝ => radFlatAux o r s (u + τ • w))
      = fun τ : ℝ => o + ((1 - Real.smoothTransition s) • (u + τ • w)
          + Real.smoothTransition s
              • ((r / ‖proj2 (u + τ • w)‖) • pl (proj2 (u + τ • w)))) := by
    funext τ
    simp only [radFlatAux]
    rw [add_smul]
    have hcoe : (Real.smoothTransition s * (r / ‖proj2 (u + τ • w)‖))
        • pl (proj2 (u + τ • w))
        = Real.smoothTransition s
            • ((r / ‖proj2 (u + τ • w)‖) • pl (proj2 (u + τ • w))) := mul_smul _ _ _
    rw [hcoe]
    have hz : (1 - Real.smoothTransition s) • zpart (u + τ • w)
        = (1 - Real.smoothTransition s) • ((u + τ • w) - pl (proj2 (u + τ • w))) := rfl
    rw [hz]
    module
  rw [hfun]
  refine hwhole.congr_deriv ?_
  simp only [neg_smul, sub_eq_add_neg]

/-- **The derivative of the flattening radial map along a line**, in the variable `v` and with
`u = v - o`. -/
theorem hasDerivAt_radFlat {o : E3} {r s : ℝ} {v w : E3} (hp : proj2 (v - o) ≠ 0) :
    HasDerivAt (fun τ : ℝ => radFlat o r s (v + τ • w))
      ((1 - Real.smoothTransition s) • w
        + Real.smoothTransition s •
          ((r / ‖proj2 (v - o)‖) • pl (proj2 w)
            - (r * inner ℝ (proj2 (v - o)) (proj2 w) / ‖proj2 (v - o)‖ ^ 3)
                • pl (proj2 (v - o)))) 0 := by
  have h := hasDerivAt_radFlatAux (o := o) (r := r) (s := s) (u := v - o) (w := w) hp
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun τ => ?_))
  show radFlat o r s (v + τ • w) = radFlatAux o r s (v - o + τ • w)
  rw [radFlat_eq_aux]
  congr 1
  abel

/-! ## The kernel of the flattening radial map

The kernel characterisation `fderiv (radFlat o r s) v w = 0 → w = 0 ∨ (1 ≤ s ∧ proj2 w ∈ ℝ (proj2 (v - o)))`
is the imm row of the image-local ambient path built on `radFlat`; it is deferred to the file that
consumes it (the D2 certificate now goes through `isCertifiedAt_of_starRegions`). -/


end

end Work.Drive.N2Lead
