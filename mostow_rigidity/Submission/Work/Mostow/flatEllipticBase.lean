import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.stabFlatDefs
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.stabFlatActionCanon
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.hptOf_hdist
import Submission.Work.Mostow.horoSpec
import Submission.Work.Mostow.stabParabOrEllip
import Submission.Work.Mostow.horoActTrivId
import Submission.Work.Mostow.cegDefs
import Submission.Work.Mostow.zassenhausNilpotent
import Submission.Work.Mostow.nilp_torsionGen_finite
import Submission.Work.Mostow.finite_nearStab

/-!
# The flat action of an elliptic isometry fixing a boundary point

For `γ : PO n 1` fixing `ξ ∈ Sph n` and preserving the horospheres at `ξ` (i.e. with vanishing
Busemann cocycle at `ξ`), the action of `γ` on the horospheres at `ξ` is by an affine isometry
of the flat space `ξ^⊥`; its linear part is `fPart ξ γ` and its translation part `fShift ξ γ`.

This file collects the basic facts about `fPart`/`fShift` that the elliptic-gap argument needs:

* `fData` — for an **elliptic** `γ` fixing `ξ` (one with a fixed point `p`), the action on the
  horospheres at `ξ` is by `y ↦ fPart ξ γ y + fShift ξ γ`, with `fShift ξ γ ⊥ ξ` and `fPart ξ γ`
  orthogonal on `ξ^⊥`;
* `hdist_fPart` — the corresponding displacement formula
  `hdist u (γ • u) = arccosh (1 + (lev ξ u * ‖fPart ξ γ (yc ξ u) + fShift ξ γ - yc ξ u‖)²/2)`;
* `fShift_add_fPart_fix` — the translation part is read off from a fixed point `p`:
  `fPart ξ γ (yc ξ p) + fShift ξ γ = yc ξ p`;
* `eq_one_of_fPart_eq_id` — if `fPart ξ γ` acts trivially on `ξ^⊥`, then `γ = 1`;
* `fPart_eq_of_flatData` — any affine pair `(A, v)` satisfying the flat-action formula at `ξ`
  agrees, on `ξ^⊥`, with `(fPart ξ γ, fShift ξ γ)`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-- The linear part of the flat action of `γ` at `ξ`: `fPart ξ γ = flatLin ξ (Λ γ)`. -/
def fPart (ξ : E n) (γ : PO n 1) : E n →ₗ[ℝ] E n := flatLin ξ (LambdaMat γ)

/-- The translation part of the flat action of `γ` at `ξ`: `fShift ξ γ = flatTrans ξ (Λ γ)`. -/
def fShift (ξ : E n) (γ : PO n 1) : E n := flatTrans ξ (LambdaMat γ)

@[simp] lemma fPart_apply (ξ : E n) (γ : PO n 1) (y : E n) :
    fPart ξ γ y = flatLin ξ (LambdaMat γ) y := rfl

@[simp] lemma fShift_eq_flatTrans (ξ : E n) (γ : PO n 1) :
    fShift ξ γ = flatTrans ξ (LambdaMat γ) := rfl

/-- The normalised flat coordinate of a point is orthogonal to `ξ`. -/
lemma inner_yc_Sph {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) : inner ℝ (yc ξ u) ξ = 0 := by
  have h1 : inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have h : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
    rw [h, one_pow]
  simp only [yc, wc, real_inner_smul_left, inner_sub_left, h1, mul_one, sub_self, mul_zero]

/-- **The flat action data of an elliptic element fixing `ξ`.**  If `γ` fixes `ξ` and has a
fixed point in `ℍⁿ`, then it preserves the horospheres at `ξ` and acts on them by the affine
isometry `y ↦ fPart ξ γ y + fShift ξ γ` of `ξ^⊥`. -/
theorem fData (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) {ξ : E n} (hξ : ξ ∈ Sph n) {γ : PO n 1}
    (hb : bd γ ξ = ξ) (hell : ∃ p : E n, γ • p = p) :
    inner ℝ (fShift ξ γ) ξ = 0 ∧
      (∀ y : E n, inner ℝ y ξ = 0 → inner ℝ (fPart ξ γ y) ξ = 0) ∧
      (∀ y : E n, inner ℝ y ξ = 0 → ‖fPart ξ γ y‖ = ‖y‖) ∧
      (∀ (y : E n) (D : ℝ), inner ℝ y ξ = 0 → 0 < D →
        lev ξ (γ • hptOf ξ y D) = D ∧ yc ξ (γ • hptOf ξ y D) = fPart ξ γ y + fShift ξ γ) := by
  have hbc : busemann ξ (γ • (0 : E n)) = 0 := by
    have h1 := bCocy_eq_zero_of_fixed hI γ ξ hξ hb hell.choose hell.choose_spec
    simpa [bCocy, hb] using h1
  exact stabFlatActionCanon n hA hI ξ hξ γ hb hbc

/-- **The flat displacement formula.**  For an elliptic `γ` fixing `ξ` and any point `u` of `ℍⁿ`,
the displacement of `u` under `γ` is the flat displacement at the level and flat coordinate of
`u`. -/
theorem hdist_fPart (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) {ξ : E n} (hξ : ξ ∈ Sph n) {γ : PO n 1}
    (hb : bd γ ξ = ξ) (hell : ∃ p : E n, γ • p = p) (u : E n) :
    hdist u (γ • u) =
      Real.arcosh (1 + (lev ξ u * ‖fPart ξ γ (yc ξ u) + fShift ξ γ - yc ξ u‖) ^ 2 / 2) := by
  obtain ⟨hv, hperp, hnorm, hform⟩ := fData hA hI hξ hb hell
  have hy : inner ℝ (yc ξ u) ξ = 0 := inner_yc_Sph hξ u
  have hD : 0 < lev ξ u := lev_pos ξ hξ u
  obtain ⟨hl, hyc⟩ := hform (yc ξ u) (lev ξ u) hy hD
  have hu : hptOf ξ (yc ξ u) (lev ξ u) = u := hptOf_yc_lev hξ u
  have hsum : inner ℝ (fPart ξ γ (yc ξ u) + fShift ξ γ) ξ = 0 := by
    rw [inner_add_left, hperp (yc ξ u) hy, hv, add_zero]
  have hlv : lev ξ (hptOf ξ (yc ξ u) (lev ξ u)) = lev ξ u :=
    (hptOf_level ξ hξ (lev ξ u) hD (yc ξ u) hy).1
  have hyc' : yc ξ (hptOf ξ (yc ξ u) (lev ξ u)) = yc ξ u :=
    (hptOf_level ξ hξ (lev ξ u) hD (yc ξ u) hy).2
  have hhu : γ • u = hptOf ξ (fPart ξ γ (yc ξ u) + fShift ξ γ) (lev ξ u) := by
    rw [← hu, ← hptOf_yc ξ hξ (lev ξ u) hD (γ • hptOf ξ (yc ξ u) (lev ξ u)) hl, hyc, hlv, hyc']
  calc hdist u (γ • u)
      = hdist (hptOf ξ (yc ξ u) (lev ξ u))
              (hptOf ξ (fPart ξ γ (yc ξ u) + fShift ξ γ) (lev ξ u)) := by rw [hu, hhu]
    _ = Real.arcosh (1 + (lev ξ u * ‖yc ξ u - (fPart ξ γ (yc ξ u) + fShift ξ γ)‖) ^ 2 / 2) :=
          hptOf_hdist ξ hξ (lev ξ u) hD (yc ξ u)
            (fPart ξ γ (yc ξ u) + fShift ξ γ) hy hsum
    _ = Real.arcosh (1 + (lev ξ u * ‖fPart ξ γ (yc ξ u) + fShift ξ γ - yc ξ u‖) ^ 2 / 2) := by
          rw [norm_sub_rev]

/-- A fixed point of an elliptic `γ` fixing `ξ` gives the affine centre of the flat action:
`fPart ξ γ (yc ξ p) + fShift ξ γ = yc ξ p`. -/
theorem fPart_add_fShift_fix (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) {ξ : E n} (hξ : ξ ∈ Sph n) {γ : PO n 1}
    (hb : bd γ ξ = ξ) (hell : ∃ p : E n, γ • p = p) {p : E n} (hp : γ • p = p) :
    fPart ξ γ (yc ξ p) + fShift ξ γ = yc ξ p := by
  obtain ⟨-, -, -, hform⟩ := fData hA hI hξ hb hell
  have hy : inner ℝ (yc ξ p) ξ = 0 := inner_yc_Sph hξ p
  have hD : 0 < lev ξ p := lev_pos ξ hξ p
  have h := (hform (yc ξ p) (lev ξ p) hy hD).2
  rw [hptOf_yc_lev hξ p, hp] at h
  exact h.symm

/-- If `γ` fixes `ξ` and is elliptic, then the level function at `ξ` is `γ`-invariant. -/
theorem lev_smul_of_elliptic (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) {ξ : E n} (hξ : ξ ∈ Sph n) {γ : PO n 1}
    (hb : bd γ ξ = ξ) (hell : ∃ p : E n, γ • p = p) :
    ∀ u : E n, lev ξ (γ • u) = lev ξ u := by
  have hbc : bCocy γ ξ = 0 :=
    bCocy_eq_zero_of_fixed hI γ ξ hξ hb hell.choose hell.choose_spec
  have hlev0 : lev ξ (γ • (0 : E n)) = 1 := by
    rw [lev_eq_exp hξ (γ • (0 : E n)),
      show busemann ξ (γ • (0 : E n)) = bCocy γ ξ from by rw [bCocy, hb], hbc, Real.exp_zero]
  intro u
  rw [lev_smul_self (HypIsoData.ofProp hI) (POBasic.ofProp hA) ξ hξ γ u hb, hlev0, mul_one]

/-- If the flat linear part of an elliptic `γ` fixing `ξ` is the identity on `ξ^⊥`, then
`γ = 1`. -/
theorem eq_one_of_fPart_eq_id (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) {ξ : E n} (hξ : ξ ∈ Sph n) {γ : PO n 1}
    (hb : bd γ ξ = ξ) (hell : ∃ p : E n, γ • p = p)
    (h : ∀ y : E n, inner ℝ y ξ = 0 → fPart ξ γ y = y) : γ = 1 := by
  obtain ⟨hv, -, -, hform⟩ := fData hA hI hξ hb hell
  have hlev := lev_smul_of_elliptic hA hI hξ hb hell
  obtain ⟨p, hp⟩ := hell
  have hy0 : fShift ξ γ = 0 := by
    have h1 := fPart_add_fShift_fix hA hI hξ hb ⟨p, hp⟩ hp
    rw [h (yc ξ p) (inner_yc_Sph hξ p)] at h1
    exact add_left_cancel (a := yc ξ p) (h1.trans (add_zero (yc ξ p)).symm)
  have htriv : ∀ u : E n, lev ξ u = 1 → γ • u = u := by
    intro u hu
    have hy : inner ℝ (yc ξ u) ξ = 0 := inner_yc_Sph hξ u
    have hD : 0 < lev ξ u := lev_pos ξ hξ u
    have hu' : hptOf ξ (yc ξ u) (lev ξ u) = u := hptOf_yc_lev hξ u
    have h1 : yc ξ (γ • hptOf ξ (yc ξ u) (lev ξ u)) = yc ξ u := by
      rw [(hform (yc ξ u) (lev ξ u) hy hD).2, h (yc ξ u) hy, hy0, add_zero]
    have h2 : lev ξ (γ • hptOf ξ (yc ξ u) (lev ξ u)) = lev ξ u := by
      rw [(hform (yc ξ u) (lev ξ u) hy hD).1]
    calc γ • u = γ • hptOf ξ (yc ξ u) (lev ξ u) := by rw [hu']
      _ = hptOf ξ (yc ξ (γ • hptOf ξ (yc ξ u) (lev ξ u)))
            (lev ξ (γ • hptOf ξ (yc ξ u) (lev ξ u))) := (hptOf_yc_lev hξ _).symm
      _ = hptOf ξ (yc ξ u) (lev ξ u) := by rw [h1, h2]
      _ = u := hu'
  exact horoActTrivId hA γ ξ hξ 1 one_pos hb hlev htriv

/-- Any affine pair `(A, v)` realising the flat action of an elliptic `γ` fixing `ξ` agrees with
`(fPart ξ γ, fShift ξ γ)` on `ξ^⊥`. -/
theorem fPart_eq_of_flatData (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) {ξ : E n} (hξ : ξ ∈ Sph n) {γ : PO n 1}
    (hb : bd γ ξ = ξ) (hell : ∃ p : E n, γ • p = p)
    {A : E n →ₗ[ℝ] E n} {v : E n}
    (hform : ∀ (y : E n) (D : ℝ), inner ℝ y ξ = 0 → 0 < D →
      lev ξ (γ • hptOf ξ y D) = D ∧ yc ξ (γ • hptOf ξ y D) = A y + v) :
    (∀ y : E n, inner ℝ y ξ = 0 → A y = fPart ξ γ y) ∧ v = fShift ξ γ := by
  obtain ⟨-, -, -, hform'⟩ := fData hA hI hξ hb hell
  have hzero : v = fShift ξ γ := by
    have h1 := (hform 0 1 (by simp) one_pos).2
    have h2 := (hform' 0 1 (by simp) one_pos).2
    rw [map_zero, zero_add] at h1 h2
    exact h1.symm.trans h2
  refine ⟨fun y hy => ?_, hzero⟩
  have h1 := (hform y 1 hy one_pos).2
  have h2 := (hform' y 1 hy one_pos).2
  rw [hzero] at h1
  exact add_right_cancel (h1.symm.trans h2)

end

end Work.Mostow
