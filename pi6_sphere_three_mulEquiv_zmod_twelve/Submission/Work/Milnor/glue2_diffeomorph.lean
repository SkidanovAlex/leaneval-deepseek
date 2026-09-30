import Mathlib
import Submission.Work.Milnor.Construction

set_option synthInstance.maxHeartbeats 400000

/-!
# The second gluing map `glue₂ k` is a diffeomorphism of the annulus

Milnor's construction glues the two copies of `D⁴ × S³` along the twist
`f(x, y) = (x, x^k y x⁻¹)`.  In the formalisation the twist appears as the self-map

`glue₂ k p = (p.1, clutch (-k) (unitDir p.1, p.2))`

of the ambient space `ℝ⁴ × S³ ≅ ℝ⁴ × ℍ`, which restricts to a self-map of the annulus
`{1/2 < ‖p.1‖ < 3/4} × S³`.

This file proves that this restriction is a diffeomorphism of the annulus; the inverse is

`glue₂Inv k p = (p.1, invTwist k (unitDir p.1, p.2)) = (p.1, u ^ k * p.2 * u)`,
where `u = unitDir p.1`.

The mathematical content is:
* `p ↦ unitDir p.1` is smooth on the annulus: on `{x ≠ 0}` the map `x ↦ x / ‖x‖` is smooth, and
  being `S³`-valued it is smooth as a map to the sphere (`ContMDiff.codRestrict_sphere`);
* the twist `(u, y) ↦ u^{-k} y u^{-1}` is smooth on `S³ × S³` (`clutch_smooth`), as is its
  inverse `(u, y) ↦ u^{k} y u` (`contMDiff_invTwist`);
* the two twists are mutually inverse (`invTwist_clutch`, `clutch_invTwist`),
  which makes `glue₂ k` bijective with inverse `glue₂Inv k`.
-/

open scoped Manifold ContDiff Topology
open Metric (sphere)
open Submission.Milnor
open TopologicalSpace Set

namespace Work.Milnor

noncomputable section

/-! ### Smoothness of the direction map -/

/-- The direction of a vector `x : ℝ⁴`, viewed in the quaternions: the value of `unitDir x`
(for `x ≠ 0`).  It is the normalisation map `x ↦ x / ‖x‖` (transported along the linear
isometry `ℍ ≃ ℝ⁴`). -/
def dirVal (x : EuclideanSpace ℝ (Fin 4)) : Quaternion ℝ :=
  (‖x‖ : ℝ)⁻¹ • Quaternion.linearIsometryEquivTuple.symm x

/-- The value of `unitDir x` in `ℍ`, for nonzero `x`. -/
lemma unitDir_coe (x : EuclideanSpace ℝ (Fin 4)) (hx : x ≠ 0) :
    ((unitDir x : QS3) : Quaternion ℝ) = dirVal x := by
  rw [unitDir, dif_neg hx, dirVal, Algebra.smul_def]
  exact (Algebra.commutes ((‖x‖ : ℝ)⁻¹) (Quaternion.linearIsometryEquivTuple.symm x)).symm

/-- A point of the annulus has nonzero first coordinate. -/
lemma annulus_ne (p : MSpace) (hp : p ∈ (annulus : Set MSpace)) : p.1 ≠ 0 := by
  intro h0
  have h := hp.1
  rw [h0, norm_zero] at h
  linarith

/-- The normalisation map `x ↦ x / ‖x‖` (as a quaternion valued map) is smooth away from `0`. -/
lemma dirVal_contMDiffOn : ContMDiffOn (𝓡 4) 𝓘(ℝ, Quaternion ℝ) ∞ dirVal
    {x : EuclideanSpace ℝ (Fin 4) | x ≠ 0} := by
  rw [contMDiffOn_iff_contDiffOn]
  have hB : ContDiffOn ℝ ∞
      (fun x : EuclideanSpace ℝ (Fin 4) => Quaternion.linearIsometryEquivTuple.symm x)
      {x | x ≠ 0} :=
    (LinearIsometryEquiv.contDiff Quaternion.linearIsometryEquivTuple.symm).contDiffOn
  have hA : ContDiffOn ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 4) => (‖x‖ : ℝ)⁻¹) {x | x ≠ 0} := by
    have hn : ContDiffOn ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖) {x | x ≠ 0} :=
      ContDiffOn.norm ℝ contDiff_id.contDiffOn (fun x hx => hx)
    exact hn.inv (fun x hx => norm_ne_zero_iff.mpr hx)
  exact ContDiffOn.smul (𝕜' := ℝ) (F := Quaternion ℝ) hA hB

/-- `p ↦ unitDir p.1` is smooth on the annulus, as a map into the sphere `S³`. -/
lemma unitDir_contMDiffOn : ContMDiffOn ((𝓡 4).prod (𝓡 3)) (𝓡 3) ∞
    (fun p : MSpace => unitDir p.1) (annulus : Set MSpace) := by
  have hdirOn : ContMDiffOn ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun p : MSpace => dirVal p.1) (annulus : Set MSpace) := by
    have hfst : ContMDiffOn ((𝓡 4).prod (𝓡 3)) (𝓡 4) ∞
        (Prod.fst : MSpace → EuclideanSpace ℝ (Fin 4)) (annulus : Set MSpace) :=
      contMDiff_fst.contMDiffOn
    exact (dirVal_contMDiffOn.comp hfst (fun p hp => annulus_ne p hp)).congr (fun _ _ => rfl)
  have hcoe : ContMDiffOn ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun p : MSpace => ((unitDir p.1 : QS3) : Quaternion ℝ)) (annulus : Set MSpace) :=
    hdirOn.congr (fun p hp => unitDir_coe p.1 (annulus_ne p hp))
  have hglob : ContMDiff ((𝓡 4).prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun p : ↥(annulus : Opens MSpace) =>
        ((unitDir (p : MSpace).1 : QS3) : Quaternion ℝ)) := by
    intro p
    exact (contMDiffAt_subtype_iff (U := (annulus : Opens MSpace))
      (f := fun q : MSpace => ((unitDir q.1 : QS3) : Quaternion ℝ)) (x := p)).mpr
      (hcoe.contMDiffAt ((annulus : Opens MSpace).2.mem_nhds p.2))
  have hmem : ∀ p : ↥(annulus : Opens MSpace),
      ((unitDir (p : MSpace).1 : QS3) : Quaternion ℝ) ∈ sphere (0 : Quaternion ℝ) 1 :=
    fun p => (unitDir (p : MSpace).1).2
  have hsphere : ContMDiff ((𝓡 4).prod (𝓡 3)) (𝓡 3) ∞
      (fun p : ↥(annulus : Opens MSpace) => unitDir (p : MSpace).1) :=
    (ContMDiff.codRestrict_sphere hglob hmem).congr (fun p => Subtype.ext rfl)
  intro p hp
  exact ((contMDiffAt_subtype_iff (U := (annulus : Opens MSpace))
    (f := fun q : MSpace => unitDir q.1) (x := ⟨p, hp⟩)).mp (hsphere ⟨p, hp⟩)).contMDiffWithinAt

/-! ### The two glueing maps -/

/-- The quaternion valued inverse twist `(x, y) ↦ x ^ k * y * x`, the inverse of
`(x, y) ↦ x ^ (-k) * y * x⁻¹`. -/
def invTwistVal (k : ℤ) (x y : QS3) : Quaternion ℝ := (x : Quaternion ℝ) ^ k * (y : Quaternion ℝ) * (x : Quaternion ℝ)

/-- The norm of the inverse twist is one. -/
lemma norm_invTwistVal (k : ℤ) (x y : QS3) : ‖invTwistVal k x y‖ = 1 := by
  rw [invTwistVal, norm_mul, norm_mul, norm_zpow, Submission.Milnor.norm_coe,
    Submission.Milnor.norm_coe]
  simp

/-- The inverse twist `(x, y) ↦ (x, x ^ k * y * x)`, as a map `S³ × S³ → S³`. -/
def invTwist (k : ℤ) (p : QS3 × QS3) : QS3 :=
  ⟨invTwistVal k p.1 p.2, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact norm_invTwistVal k p.1 p.2⟩

lemma contMDiff_invTwist_val (k : ℤ) :
    ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞
      (fun p : QS3 × QS3 => invTwistVal k p.1 p.2) := by
  have h : ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, Quaternion ℝ) ∞
      ((fun p : QS3 × QS3 => (p.1 : Quaternion ℝ) ^ k) *
        (fun p : QS3 × QS3 => (p.2 : Quaternion ℝ)) *
        (fun p : QS3 × QS3 => (p.1 : Quaternion ℝ))) :=
    ((Work.Quaternion.contMDiff_coe_zpow k).mul
      (contMDiff_coe_sphere.comp contMDiff_snd)).mul (contMDiff_coe_sphere.comp contMDiff_fst)
  exact h.congr (fun p => by simp only [invTwistVal, Pi.mul_apply])

lemma contMDiff_invTwist (k : ℤ) :
    ContMDiff ((𝓡 3).prod (𝓡 3)) (𝓡 3) ∞ (fun p : QS3 × QS3 => invTwist k p) := by
  have hcl : ContMDiff ((𝓡 3).prod (𝓡 3)) (𝓡 3) ∞
      (Set.codRestrict (fun p : QS3 × QS3 => invTwistVal k p.1 p.2) (sphere (0 : Quaternion ℝ) 1)
        (fun p => by
          rw [Metric.mem_sphere, dist_zero_right]
          exact norm_invTwistVal k p.1 p.2)) :=
    ContMDiff.codRestrict_sphere (contMDiff_invTwist_val k) _
  convert hcl using 1
  funext p
  exact Subtype.ext rfl

/-- `invTwist k` is a left inverse of the twist `clutch (-k)`. -/
lemma invTwist_clutch (k : ℤ) (x y : QS3) : invTwist k (x, clutch (-k) (x, y)) = y := by
  refine Subtype.ext ?_
  have hx : (x : Quaternion ℝ) ≠ 0 := Work.Quaternion.coe_ne_zero x
  have h1 : (x : Quaternion ℝ) ^ k * (x : Quaternion ℝ) ^ (-k) = 1 := by
    rw [← zpow_add₀ hx, add_neg_cancel, zpow_zero]
  simp only [invTwist, clutch, invTwistVal, clutchVal, Subtype.coe_mk]
  rw [mul_assoc ((x : Quaternion ℝ) ^ (-k)) (y : Quaternion ℝ) ((x : Quaternion ℝ)⁻¹),
    ← mul_assoc ((x : Quaternion ℝ) ^ k) ((x : Quaternion ℝ) ^ (-k))
      ((y : Quaternion ℝ) * (x : Quaternion ℝ)⁻¹), h1, one_mul, mul_assoc,
    inv_mul_cancel₀ hx, mul_one]

/-- `invTwist k` is a right inverse of the twist `clutch (-k)`. -/
lemma clutch_invTwist (k : ℤ) (x y : QS3) : clutch (-k) (x, invTwist k (x, y)) = y := by
  refine Subtype.ext ?_
  have hx : (x : Quaternion ℝ) ≠ 0 := Work.Quaternion.coe_ne_zero x
  have h1 : (x : Quaternion ℝ) ^ (-k) * (x : Quaternion ℝ) ^ k = 1 := by
    rw [← zpow_add₀ hx, neg_add_cancel, zpow_zero]
  simp only [invTwist, clutch, invTwistVal, clutchVal, Subtype.coe_mk]
  rw [mul_assoc ((x : Quaternion ℝ) ^ k) (y : Quaternion ℝ) (x : Quaternion ℝ),
    ← mul_assoc ((x : Quaternion ℝ) ^ (-k)) ((x : Quaternion ℝ) ^ k)
      ((y : Quaternion ℝ) * (x : Quaternion ℝ)), h1, one_mul, mul_assoc,
    mul_inv_cancel₀ hx, mul_one]

/-- The inverse of the twist: `(x, y) ↦ (x, u ^ k * y * u)` with `u = unitDir x`. -/
def glue₂Inv (k : ℤ) (p : MSpace) : MSpace :=
  (p.1, invTwist k (unitDir p.1, p.2))

/-- `glue₂ k` maps the annulus into itself (its first coordinate is unchanged). -/
lemma glue₂_mapsTo_annulus (k : ℤ) :
    MapsTo (glue₂ k) (annulus : Set MSpace) (annulus : Set MSpace) := by
  intro p hp
  simp only [Submission.Milnor.annulus, Submission.Milnor.glue₂] at hp ⊢
  exact hp

/-- `glue₂Inv k` maps the annulus into itself (its first coordinate is unchanged). -/
lemma glue₂Inv_mapsTo_annulus (k : ℤ) :
    MapsTo (glue₂Inv k) (annulus : Set MSpace) (annulus : Set MSpace) := by
  intro p hp
  simp only [Submission.Milnor.annulus, glue₂Inv] at hp ⊢
  exact hp

/-- `glue₂ k` is smooth on the annulus. -/
lemma glue₂_contMDiffOn (k : ℤ) :
    ContMDiffOn ((𝓡 4).prod (𝓡 3)) ((𝓡 4).prod (𝓡 3)) ∞ (glue₂ k) (annulus : Set MSpace) := by
  rw [contMDiffOn_prod_iff]
  constructor
  · have hfst : ContMDiffOn ((𝓡 4).prod (𝓡 3)) (𝓡 4) ∞
        (Prod.fst : MSpace → EuclideanSpace ℝ (Fin 4)) (annulus : Set MSpace) :=
      contMDiff_fst.contMDiffOn
    exact hfst.congr (fun _ _ => rfl)
  · have hpair : ContMDiffOn ((𝓡 4).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
        (fun p : MSpace => (unitDir p.1, p.2)) (annulus : Set MSpace) :=
      unitDir_contMDiffOn.prodMk (contMDiff_snd (I := 𝓡 4) (J := 𝓡 3)).contMDiffOn
    exact ((Work.Quaternion.clutch_smooth (-k)).comp_contMDiffOn hpair).congr (fun _ _ => rfl)

/-- `glue₂Inv k` is smooth on the annulus. -/
lemma glue₂Inv_contMDiffOn (k : ℤ) :
    ContMDiffOn ((𝓡 4).prod (𝓡 3)) ((𝓡 4).prod (𝓡 3)) ∞ (glue₂Inv k) (annulus : Set MSpace) := by
  rw [contMDiffOn_prod_iff]
  constructor
  · have hfst : ContMDiffOn ((𝓡 4).prod (𝓡 3)) (𝓡 4) ∞
        (Prod.fst : MSpace → EuclideanSpace ℝ (Fin 4)) (annulus : Set MSpace) :=
      contMDiff_fst.contMDiffOn
    exact hfst.congr (fun _ _ => rfl)
  · have hpair : ContMDiffOn ((𝓡 4).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
        (fun p : MSpace => (unitDir p.1, p.2)) (annulus : Set MSpace) :=
      unitDir_contMDiffOn.prodMk (contMDiff_snd (I := 𝓡 4) (J := 𝓡 3)).contMDiffOn
    exact ((contMDiff_invTwist k).comp_contMDiffOn hpair).congr (fun _ _ => rfl)

/-! ### The two maps are mutually inverse -/

/-- `glue₂Inv k` is a left inverse of `glue₂ k`. -/
lemma glue₂Inv_glue₂ (k : ℤ) (p : MSpace) : glue₂Inv k (glue₂ k p) = p := by
  rw [glue₂Inv, glue₂]
  exact Prod.ext rfl (invTwist_clutch k (unitDir p.1) p.2)

/-- `glue₂Inv k` is a right inverse of `glue₂ k`. -/
lemma glue₂_glue₂Inv (k : ℤ) (p : MSpace) : glue₂ k (glue₂Inv k p) = p := by
  rw [glue₂Inv, glue₂]
  exact Prod.ext rfl (clutch_invTwist k (unitDir p.1) p.2)

/-! ### The diffeomorphism -/

open scoped Manifold ContDiff Topology in
open Submission.Milnor in
open TopologicalSpace in
theorem glue2_diffeomorph (k : ℤ) :
    ∃ e : ↥(annulus : Opens MSpace) ≃ₘ⟮(𝓡 4).prod (𝓡 3), (𝓡 4).prod (𝓡 3)⟯
        ↥(annulus : Opens MSpace),
      ∀ p : ↥(annulus : Opens MSpace), (e p : MSpace) = glue₂ k (p : MSpace) := by
  let F : ↥(annulus : Opens MSpace) → ↥(annulus : Opens MSpace) :=
    fun p => ⟨glue₂ k (p : MSpace), glue₂_mapsTo_annulus k p.2⟩
  let G : ↥(annulus : Opens MSpace) → ↥(annulus : Opens MSpace) :=
    fun p => ⟨glue₂Inv k (p : MSpace), glue₂Inv_mapsTo_annulus k p.2⟩
  have hFG : Function.LeftInverse G F := fun p => Subtype.ext (glue₂Inv_glue₂ k (p : MSpace))
  have hGF : Function.RightInverse G F := fun p => Subtype.ext (glue₂_glue₂Inv k (p : MSpace))
  let e : ↥(annulus : Opens MSpace) ≃ ↥(annulus : Opens MSpace) := ⟨F, G, hFG, hGF⟩
  have hF : ContMDiff ((𝓡 4).prod (𝓡 3)) ((𝓡 4).prod (𝓡 3)) ∞ (⇑e) := by
    refine (ContMDiff.subtypeVal_comp_iff (annulus : Opens MSpace) F).mp ?_
    intro p
    exact (contMDiffAt_subtype_iff (U := (annulus : Opens MSpace))
      (f := glue₂ k) (x := p)).mpr
      ((glue₂_contMDiffOn k).contMDiffAt ((annulus : Opens MSpace).2.mem_nhds p.2))
  have hG : ContMDiff ((𝓡 4).prod (𝓡 3)) ((𝓡 4).prod (𝓡 3)) ∞ (⇑e.symm) := by
    refine (ContMDiff.subtypeVal_comp_iff (annulus : Opens MSpace) G).mp ?_
    intro p
    exact (contMDiffAt_subtype_iff (U := (annulus : Opens MSpace))
      (f := glue₂Inv k) (x := p)).mpr
      ((glue₂Inv_contMDiffOn k).contMDiffAt ((annulus : Opens MSpace).2.mem_nhds p.2))
  exact ⟨⟨e, hF, hG⟩, fun p => rfl⟩

end

end Work.Milnor
