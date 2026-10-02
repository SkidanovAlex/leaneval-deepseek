import Mathlib
import Submission.Work.Milnor.VBundleDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Milnor

open scoped Manifold ContDiff Topology
open Submission.Milnor

/-!
# Smoothness of the clutching map `vMap k` of the bundle `ξ`

The two charts of the total space `MSpace8 = ℝ⁴ × ℍ` of the rank-`4` bundle `ξ` over `S⁴` are
glued along `{x ≠ 0} × ℍ` by `(x, y) ↦ (x/‖x‖², û^{-k} y û⁻¹)`, where `û = x/‖x‖`
(`Submission.Milnor.vMap`), with inverse `(x, y) ↦ (x/‖x‖², û^{k} y û)`
(`Submission.Milnor.vMapInv`).  This file proves that both maps are smooth on the gluing
region.

The point is that both maps are built out of
* the inversion `invBase x = x/‖x‖²` (`Submission.Milnor.contMDiffOn_invBase`), and
* the twist `(x, y) ↦ q^a * y * q^b` with `q = dirVal x = x/‖x‖` (`Work.Milnor.dirVal`),

and all of these are smooth away from `x = 0`.  The direction `dirVal x` is a *unit* quaternion,
so its inverse is its conjugate `star (dirVal x)`, which is smooth; this avoids needing
smoothness of inversion on all of `ℍ`.
-/

/-! ### The direction `dirVal` -/

/-- The direction `x/‖x‖` has norm one away from the origin. -/
private lemma norm_dirVal {x : EuclideanSpace ℝ (Fin 4)} (hx : x ≠ 0) : ‖dirVal x‖ = 1 := by
  rw [← unitDir_coe x hx]
  exact Submission.Milnor.norm_coe (unitDir x)

/-- The direction `x/‖x‖` is nonzero away from the origin. -/
private lemma dirVal_ne_zero {x : EuclideanSpace ℝ (Fin 4)} (hx : x ≠ 0) : dirVal x ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [norm_dirVal hx]; exact one_ne_zero)

/-- On the unit sphere, inversion is conjugation. -/
private lemma dirVal_inv_eq_star {x : EuclideanSpace ℝ (Fin 4)} (hx : x ≠ 0) :
    (dirVal x)⁻¹ = star (dirVal x) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self]
  simp [norm_dirVal hx]

/-- `p ↦ dirVal p.1` is smooth on the gluing region. -/
private lemma contDiffOn_dirVal_fst :
    ContDiffOn ℝ ∞ (fun p : MSpace8 => dirVal p.1) {p : MSpace8 | p.1 ≠ 0} :=
  (contMDiffOn_iff_contDiffOn.mp dirVal_contMDiffOn).comp contDiff_fst.contDiffOn
    (fun _ hp => hp)

/-- `p ↦ (dirVal p.1)^a` is smooth on the gluing region, for every integer `a`. -/
private lemma contDiffOn_dirVal_zpow (a : ℤ) :
    ContDiffOn ℝ ∞ (fun p : MSpace8 => (dirVal p.1) ^ a) {p : MSpace8 | p.1 ≠ 0} := by
  have hdir := contDiffOn_dirVal_fst
  have hinv : ContDiffOn ℝ ∞ (fun p : MSpace8 => (dirVal p.1)⁻¹) {p : MSpace8 | p.1 ≠ 0} := by
    refine ((contMDiff_iff_contDiff.mp Work.Quaternion.contMDiff_star).comp_contDiffOn hdir).congr ?_
    intro p hp
    exact dirVal_inv_eq_star hp
  induction a using Int.induction_on with
  | zero => simpa using contDiffOn_const (s := {p : MSpace8 | p.1 ≠ 0}) (c := (1 : Quaternion ℝ))
  | succ n ih =>
      refine (ih.mul hdir).congr (fun p hp => ?_)
      exact zpow_add_one₀ (dirVal_ne_zero hp) _
  | pred n ih =>
      refine (ih.mul hinv).congr (fun p hp => ?_)
      exact zpow_sub_one₀ (dirVal_ne_zero hp) _

/-- The twist `p ↦ (dirVal p.1)^a * p.2 * (dirVal p.1)^b` is smooth on the gluing region. -/
private lemma contDiffOn_dirVal_twist (a b : ℤ) :
    ContDiffOn ℝ ∞
      (fun p : MSpace8 => (dirVal p.1) ^ a * p.2 * (dirVal p.1) ^ b)
      {p : MSpace8 | p.1 ≠ 0} :=
  ((contDiffOn_dirVal_zpow a).mul contDiff_snd.contDiffOn).mul (contDiffOn_dirVal_zpow b)

/-- `vMap k` and its inverse `vMapInv k` are smooth on the gluing region `{x ≠ 0} × ℍ`. -/
theorem vMap_smooth (k : ℤ) :
    ContMDiffOn 𝓘(ℝ, Submission.Milnor.MSpace8) 𝓘(ℝ, Submission.Milnor.MSpace8) ∞
        (Submission.Milnor.vMap k) {p : Submission.Milnor.MSpace8 | p.1 ≠ 0} ∧
      ContMDiffOn 𝓘(ℝ, Submission.Milnor.MSpace8) 𝓘(ℝ, Submission.Milnor.MSpace8) ∞
        (Submission.Milnor.vMapInv k) {p : Submission.Milnor.MSpace8 | p.1 ≠ 0} := by
  constructor
  · rw [contMDiffOn_iff_contDiffOn]
    have hfst : ContDiffOn ℝ ∞ (fun p : MSpace8 => invBase p.1) {p : MSpace8 | p.1 ≠ 0} :=
      (contMDiffOn_iff_contDiffOn.mp contMDiffOn_invBase).comp contDiff_fst.contDiffOn
        (fun _ hp => hp)
    have hsnd : ContDiffOn ℝ ∞ (fun p : MSpace8 => vTwist (-k) (dirVal p.1) p.2)
        {p : MSpace8 | p.1 ≠ 0} :=
      (contDiffOn_dirVal_twist (-k) (-1)).congr (fun p _ => by simp only [vTwist, zpow_neg_one])
    exact (hfst.prodMk hsnd).congr (fun p hp => by
      simp only [vMap, unitDir_coe p.1 hp])
  · rw [contMDiffOn_iff_contDiffOn]
    have hfst : ContDiffOn ℝ ∞ (fun p : MSpace8 => invBase p.1) {p : MSpace8 | p.1 ≠ 0} :=
      (contMDiffOn_iff_contDiffOn.mp contMDiffOn_invBase).comp contDiff_fst.contDiffOn
        (fun _ hp => hp)
    have hsnd : ContDiffOn ℝ ∞ (fun p : MSpace8 => vTwistInv (-k) (dirVal p.1) p.2)
        {p : MSpace8 | p.1 ≠ 0} :=
      (contDiffOn_dirVal_twist k 1).congr (fun p _ => by
        simp only [vTwistInv, neg_neg, zpow_one])
    exact (hfst.prodMk hsnd).congr (fun p hp => by
      simp only [vMapInv, unitDir_coe p.1 hp])

end Work.Milnor
