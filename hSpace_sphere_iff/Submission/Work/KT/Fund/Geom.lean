import Mathlib
import Submission.Work.KT.Defs

/-!
# `Work.KT.Fund.Geom` — `S²` as two discs glued along `S¹`

`S2 = Sph (EuclideanSpace ℝ (Fin 3))` is the union of its closed upper and lower hemispheres,
meeting along the equator `S¹`.  Each hemisphere is homeomorphic to the closed unit disc of `ℂ`
via the first two coordinates; the boundary circle of the disc is the equator.

This is the geometric input for Bott periodicity: it identifies `C(X × S², ℂ)` with the fibre
product of two copies of `C(X × Ball ℂ, ℂ)` over `C(X × Sph ℂ, ℂ)`, so that classes in
`K₀(C(X × S²))` become "clutching data" on `X × S¹`.
-/

namespace Work.KT
namespace Fund

noncomputable section

/-- The point of `ℝ³ = ℂ × ℝ` with complex coordinate `z` and third coordinate `t`. -/
def mk3 (z : ℂ) (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![z.re, z.im, t]

@[simp] lemma mk3_apply_zero (z : ℂ) (t : ℝ) : mk3 z t 0 = z.re := rfl
@[simp] lemma mk3_apply_one (z : ℂ) (t : ℝ) : mk3 z t 1 = z.im := rfl
@[simp] lemma mk3_apply_two (z : ℂ) (t : ℝ) : mk3 z t 2 = t := rfl

/-- The squared ℓ²-norm of `(z, t) ∈ ℂ × ℝ`. -/
lemma norm_mk3_sq (z : ℂ) (t : ℝ) : ‖mk3 z t‖ ^ 2 = ‖z‖ ^ 2 + t ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [mk3_apply_zero, mk3_apply_one, mk3_apply_two, Real.norm_eq_abs, sq_abs]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

lemma continuous_mk3 : Continuous (fun p : ℂ × ℝ => mk3 p.1 p.2) := by
  unfold mk3
  fun_prop

/-- Parametrisation of the closed upper hemisphere `S²₊` by the unit disc of `ℂ`. -/
def upPt (v : ℂ) : EuclideanSpace ℝ (Fin 3) := mk3 v (Real.sqrt (1 - ‖v‖ ^ 2))

/-- Parametrisation of the closed lower hemisphere `S²₋` by the unit disc of `ℂ`. -/
def dnPt (v : ℂ) : EuclideanSpace ℝ (Fin 3) := mk3 v (-(Real.sqrt (1 - ‖v‖ ^ 2)))

lemma continuous_upPt : Continuous upPt := by
  have h : Continuous (fun v : ℂ => 1 - ‖v‖ ^ 2) :=
    continuous_const.sub (continuous_norm.pow 2)
  have h2 : Continuous (fun v : ℂ => Real.sqrt (1 - ‖v‖ ^ 2)) := Real.continuous_sqrt.comp h
  exact continuous_mk3.comp (continuous_id.prodMk h2)

lemma continuous_dnPt : Continuous dnPt := by
  have h : Continuous (fun v : ℂ => 1 - ‖v‖ ^ 2) :=
    continuous_const.sub (continuous_norm.pow 2)
  have h2 : Continuous (fun v : ℂ => Real.sqrt (1 - ‖v‖ ^ 2)) := Real.continuous_sqrt.comp h
  exact continuous_mk3.comp (continuous_id.prodMk h2.neg)

lemma sq_le_one_of_le_one {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ^ 2 ≤ 1 := by
  nlinarith [sq_nonneg (x - 1)]

lemma norm_upPt (v : ℂ) (hv : ‖v‖ ≤ 1) : ‖upPt v‖ = 1 := by
  have h : 0 ≤ 1 - ‖v‖ ^ 2 := by
    have := sq_le_one_of_le_one (norm_nonneg v) hv
    linarith
  have hs : (Real.sqrt (1 - ‖v‖ ^ 2)) ^ 2 = 1 - ‖v‖ ^ 2 := Real.sq_sqrt h
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one]
  simp only [upPt]
  rw [norm_mk3_sq, hs]
  ring

lemma norm_dnPt (v : ℂ) (hv : ‖v‖ ≤ 1) : ‖dnPt v‖ = 1 := by
  have h : 0 ≤ 1 - ‖v‖ ^ 2 := by
    have := sq_le_one_of_le_one (norm_nonneg v) hv
    linarith
  have hs : (-(Real.sqrt (1 - ‖v‖ ^ 2))) ^ 2 = 1 - ‖v‖ ^ 2 := by
    rw [neg_sq, Real.sq_sqrt h]
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one]
  simp only [dnPt]
  rw [norm_mk3_sq, hs]
  ring

lemma ball_norm_le_one (v : Ball ℂ) : ‖(v : ℂ)‖ ≤ 1 := mem_closedBall_zero_iff.mp v.2

/-- The upper hemisphere parametrisation, as a map to `S²`. -/
def up (v : Ball ℂ) : S2 := ⟨upPt v, by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  exact norm_upPt v (ball_norm_le_one v)⟩

/-- The lower hemisphere parametrisation, as a map to `S²`. -/
def dn (v : Ball ℂ) : S2 := ⟨dnPt v, by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  exact norm_dnPt v (ball_norm_le_one v)⟩

lemma continuous_up : Continuous (up : Ball ℂ → S2) :=
  Continuous.subtype_mk (continuous_upPt.comp continuous_subtype_val) _

lemma continuous_dn : Continuous (dn : Ball ℂ → S2) :=
  Continuous.subtype_mk (continuous_dnPt.comp continuous_subtype_val) _

/-- The two parametrisations agree on the boundary circle: the equator of `S²`. -/
lemma up_eq_dn_of_norm_eq_one (v : Ball ℂ) (hv : ‖(v : ℂ)‖ = 1) : up v = dn v := by
  have h2 : (1 : ℝ) - ‖(v : ℂ)‖ ^ 2 = 0 := by rw [hv]; ring
  apply Subtype.ext
  simp only [up, dn, upPt, dnPt, mk3, h2, Real.sqrt_zero, neg_zero]

lemma up_eq_dn_of_bdry (v : Ball ℂ) (hv : v ∈ bdry ℂ) : up v = dn v :=
  up_eq_dn_of_norm_eq_one v hv

/-- The equator of `S²`: the points with vanishing third coordinate. -/
def equator : Set S2 := {x | (x : EuclideanSpace ℝ (Fin 3)) 2 = 0}

lemma up_mem_equator_iff (v : Ball ℂ) : up v ∈ equator ↔ ‖(v : ℂ)‖ = 1 := by
  constructor
  · intro h
    have h2 : Real.sqrt (1 - ‖(v : ℂ)‖ ^ 2) = 0 := h
    have h3 : 1 - ‖(v : ℂ)‖ ^ 2 = 0 := by
      have := Real.sq_sqrt (show 0 ≤ 1 - ‖(v : ℂ)‖ ^ 2 by
        have := sq_le_one_of_le_one (norm_nonneg (v : ℂ)) (ball_norm_le_one v)
        linarith)
      rw [h2] at this; simpa using this.symm
    nlinarith [norm_nonneg (v : ℂ)]
  · intro hv
    have h2 : (1 : ℝ) - ‖(v : ℂ)‖ ^ 2 = 0 := by rw [hv]; ring
    show (up v : EuclideanSpace ℝ (Fin 3)) 2 = 0
    simp only [up, upPt, mk3, h2, Real.sqrt_zero]
    rfl

section Pullback

/-- The upper hemisphere parametrisation as a continuous map. -/
def upCm : C(Ball ℂ, S2) := ⟨up, continuous_up⟩

/-- The lower hemisphere parametrisation as a continuous map. -/
def dnCm : C(Ball ℂ, S2) := ⟨dn, continuous_dn⟩

lemma norm_coe_sph (v : Sph ℂ) : ‖(v : ℂ)‖ = 1 := by
  have h := Metric.mem_sphere.mp v.2
  rwa [dist_eq_norm, sub_zero] at h

/-- The boundary circle of the disc, as a map `S¹ → D`. -/
def sphIncl : C(Sph ℂ, Ball ℂ) where
  toFun v := ⟨(v : ℂ), by rw [mem_closedBall_zero_iff, norm_coe_sph v]⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val
    (fun v => by rw [mem_closedBall_zero_iff, norm_coe_sph v])

/-- Restriction of functions on `X × S²` to the upper hemisphere, viewed as a disc. -/
def pullUp (X : Type) [TopologicalSpace X] : C(X × S2, ℂ) →+* C(X × Ball ℂ, ℂ) :=
  (pullAlg (⟨fun p : X × Ball ℂ => (p.1, up p.2),
      Continuous.prodMk continuous_fst (continuous_up.comp continuous_snd)⟩ :
      C(X × Ball ℂ, X × S2))).toRingHom

/-- Restriction of functions on `X × S²` to the lower hemisphere, viewed as a disc. -/
def pullDn (X : Type) [TopologicalSpace X] : C(X × S2, ℂ) →+* C(X × Ball ℂ, ℂ) :=
  (pullAlg (⟨fun p : X × Ball ℂ => (p.1, dn p.2),
      Continuous.prodMk continuous_fst (continuous_dn.comp continuous_snd)⟩ :
      C(X × Ball ℂ, X × S2))).toRingHom

/-- Restriction of functions on the disc to its boundary circle. -/
def bdryRestrict (X : Type) [TopologicalSpace X] : C(X × Ball ℂ, ℂ) →+* C(X × Sph ℂ, ℂ) :=
  (pullAlg (⟨fun p : X × Sph ℂ => (p.1, sphIncl p.2),
      Continuous.prodMk continuous_fst (sphIncl.continuous.comp continuous_snd)⟩ :
      C(X × Sph ℂ, X × Ball ℂ))).toRingHom

@[simp] lemma pullUp_apply (X : Type) [TopologicalSpace X] (g : C(X × S2, ℂ))
    (p : X × Ball ℂ) : pullUp X g p = g (p.1, up p.2) := rfl

@[simp] lemma pullDn_apply (X : Type) [TopologicalSpace X] (g : C(X × S2, ℂ))
    (p : X × Ball ℂ) : pullDn X g p = g (p.1, dn p.2) := rfl

@[simp] lemma bdryRestrict_apply (X : Type) [TopologicalSpace X] (g : C(X × Ball ℂ, ℂ))
    (p : X × Sph ℂ) : bdryRestrict X g p = g (p.1, sphIncl p.2) := rfl

/-- The two restrictions of a function on `X × S²` agree on the equator. -/
lemma bdryRestrict_pullUp_eq_pullDn (X : Type) [TopologicalSpace X] (g : C(X × S2, ℂ)) :
    bdryRestrict X (pullUp X g) = bdryRestrict X (pullDn X g) := by
  ext p
  simp only [bdryRestrict_apply, pullUp_apply, pullDn_apply]
  exact congrArg g (Prod.ext rfl (up_eq_dn_of_norm_eq_one (sphIncl p.2) (norm_coe_sph p.2)))

end Pullback

end

end Fund
end Work.KT
