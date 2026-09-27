import Mathlib
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.LambdaMat_theta_eq_exp_smul
import Submission.Work.Mostow.stabFlatDefs
import Submission.Work.Mostow.stabFlatActionCanon
import Submission.Work.Mostow.flatActBasic
import Submission.Work.Mostow.geomFiniteDefs

/-!
# The flat linear part of the horospherical action is a homomorphism

For `ξ ∈ Sph n`, an element `g : PO n 1` with `bd g ξ = ξ` and vanishing Busemann cocycle
`bCocy g ξ = 0` preserves every horosphere of `ξ`, and acts on the flat coordinate `yc ξ ·` of
each of them by the *canonical* affine isometry `y ↦ flatLin ξ (Λg) y + flatTrans ξ (Λg)`
(`Work.Mostow.stabFlatActionCanon`).

The present file extracts the two group-theoretic consequences of that fact on the level-one
horosphere, where the flat action is `flatAct`:

* the linear parts multiply: `flatLin ξ (Λ(γδ)) y = flatLin ξ (Λγ) (flatLin ξ (Λδ) y)`;
* the linear part of the inverse is a left inverse: `flatLin ξ (Λ γ⁻¹) (flatLin ξ (Λγ) y) = y`.

Both are proved by comparing the two affine expressions for `flatAct ξ (·) y` furnished by
`stabFlatActionCanon` with the composition law `flatAct_comp`; evaluating at `y = 0` pins down
the translation parts and hence the linear parts.
-/

namespace Work.Mostow.cuspHoro

open Submission.Mostow LeanEval.Geometry.MostowRigidity

variable {n : ℕ}

/-- For `g` fixing `ξ` with vanishing cocycle, the flat action `flatAct` is the canonical affine
map `y ↦ flatLin ξ (Λg) y + flatTrans ξ (Λg)`, and its translation part is tangent to `ξ^⊥`. -/
private lemma flatAct_eq_flatLin_add (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (ξ : Submission.Mostow.E n)
    (hξ : ξ ∈ Submission.Mostow.Sph n) (g : LeanEval.Geometry.MostowRigidity.PO n 1)
    (hg : Submission.Mostow.bd g ξ = ξ) (hb : Work.Mostow.bCocy g ξ = 0) :
    inner ℝ (Work.Mostow.flatTrans ξ (Work.Mostow.LambdaMat g)) ξ = 0 ∧
      ∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 →
        Work.Mostow.flatAct ξ g y
          = Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat g) y
            + Work.Mostow.flatTrans ξ (Work.Mostow.LambdaMat g) := by
  have hbus : Submission.Mostow.busemann ξ (g • (0 : Submission.Mostow.E n)) = 0 := by
    simpa [Work.Mostow.bCocy, hg] using hb
  have hc := Work.Mostow.stabFlatActionCanon n hA hI ξ hξ g hg hbus
  refine ⟨hc.1, fun y hy => ?_⟩
  have h1 := hc.2.2.2 y 1 hy one_pos
  show Work.Mostow.yc ξ (g • Work.Mostow.horoPt ξ y) = _
  rw [Work.Mostow.horoPt_eq_hptOf]
  exact h1.2

/-- If `g` fixes `ξ` and `bCocy g ξ = 0` then `g` preserves the horosphere level at `0`. -/
private lemma lev_one_of_bCocy_eq_zero (ξ : Submission.Mostow.E n)
    (hξ : ξ ∈ Submission.Mostow.Sph n) (g : LeanEval.Geometry.MostowRigidity.PO n 1)
    (hg : Submission.Mostow.bd g ξ = ξ) (hb : Work.Mostow.bCocy g ξ = 0) :
    Work.Mostow.lev ξ (g • (0 : Submission.Mostow.E n)) = 1 := by
  have hbus : Submission.Mostow.busemann ξ (g • (0 : Submission.Mostow.E n)) = 0 := by
    simpa [Work.Mostow.bCocy, hg] using hb
  rw [Work.Mostow.lev_eq_exp hξ, hbus, Real.exp_zero]

/-- The flat linear parts multiply on `ξ^⊥`. -/
private lemma flatLin_mul_of_bCocy_eq_zero (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (ξ : Submission.Mostow.E n)
    (hξ : ξ ∈ Submission.Mostow.Sph n) {γ δ : LeanEval.Geometry.MostowRigidity.PO n 1}
    (hγ : Submission.Mostow.bd γ ξ = ξ) (hδ : Submission.Mostow.bd δ ξ = ξ)
    (hbγ : Work.Mostow.bCocy γ ξ = 0) (hbδ : Work.Mostow.bCocy δ ξ = 0)
    {y : Submission.Mostow.E n} (hy : inner ℝ y ξ = 0) :
    Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (γ * δ)) y
      = Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat γ)
          (Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat δ) y) := by
  have hAb : Work.Mostow.POBasic n := Work.Mostow.POBasic.ofProp hA
  have hIb : Work.Mostow.HypIsoData n := Work.Mostow.HypIsoData.ofProp hI
  have hγδ : Submission.Mostow.bd (γ * δ) ξ = ξ := by
    rw [hAb.bd_mul γ δ ξ hξ, hδ, hγ]
  have hbγδ : Work.Mostow.bCocy (γ * δ) ξ = 0 := by
    rw [Work.Mostow.bCocy_mul hA hI γ δ ξ hξ, hbδ, hδ, hbγ, zero_add]
  have h1 := flatAct_eq_flatLin_add hA hI ξ hξ γ hγ hbγ
  have h2 := flatAct_eq_flatLin_add hA hI ξ hξ δ hδ hbδ
  have h3 := flatAct_eq_flatLin_add hA hI ξ hξ (γ * δ) hγδ hbγδ
  have hleγ := lev_one_of_bCocy_eq_zero ξ hξ γ hγ hbγ
  have hleδ := lev_one_of_bCocy_eq_zero ξ hξ δ hδ hbδ
  have hkey : ∀ y' : Submission.Mostow.E n, inner ℝ y' ξ = 0 →
      Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (γ * δ)) y'
          + Work.Mostow.flatTrans ξ (Work.Mostow.LambdaMat (γ * δ))
        = Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat γ)
            (Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat δ) y'
              + Work.Mostow.flatTrans ξ (Work.Mostow.LambdaMat δ))
          + Work.Mostow.flatTrans ξ (Work.Mostow.LambdaMat γ) := by
    intro y' hy'
    calc Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (γ * δ)) y'
          + Work.Mostow.flatTrans ξ (Work.Mostow.LambdaMat (γ * δ))
        = Work.Mostow.flatAct ξ (γ * δ) y' := (h3.2 y' hy').symm
      _ = Work.Mostow.flatAct ξ γ (Work.Mostow.flatAct ξ δ y') :=
            Work.Mostow.flatAct_comp hξ hAb hIb hγ hδ hleγ hleδ hy'
      _ = Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat γ) (Work.Mostow.flatAct ξ δ y')
            + Work.Mostow.flatTrans ξ (Work.Mostow.LambdaMat γ) :=
            h1.2 _ (Work.Mostow.flatAct_mem hξ δ y')
      _ = Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat γ)
            (Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat δ) y'
              + Work.Mostow.flatTrans ξ (Work.Mostow.LambdaMat δ))
          + Work.Mostow.flatTrans ξ (Work.Mostow.LambdaMat γ) := by rw [h2.2 y' hy']
  have h0 : Work.Mostow.flatTrans ξ (Work.Mostow.LambdaMat (γ * δ))
      = Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat γ)
          (Work.Mostow.flatTrans ξ (Work.Mostow.LambdaMat δ))
        + Work.Mostow.flatTrans ξ (Work.Mostow.LambdaMat γ) := by
    have h := hkey 0 (by simp)
    simpa only [map_zero, zero_add] using h
  have hmain := hkey y hy
  rw [h0, map_add, add_assoc] at hmain
  exact add_right_cancel hmain

/-- The flat linear part of `γ⁻¹` is a left inverse on `ξ^⊥`. -/
private lemma flatLin_inv_of_bCocy_eq_zero (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (ξ : Submission.Mostow.E n)
    (hξ : ξ ∈ Submission.Mostow.Sph n) {γ : LeanEval.Geometry.MostowRigidity.PO n 1}
    (hγ : Submission.Mostow.bd γ ξ = ξ) (hbγ : Work.Mostow.bCocy γ ξ = 0)
    {y : Submission.Mostow.E n} (hy : inner ℝ y ξ = 0) :
    Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat γ⁻¹) (Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat γ) y)
      = y := by
  have hAb : Work.Mostow.POBasic n := Work.Mostow.POBasic.ofProp hA
  have hIb : Work.Mostow.HypIsoData n := Work.Mostow.HypIsoData.ofProp hI
  have hγi : Submission.Mostow.bd γ⁻¹ ξ = ξ := Work.Mostow.bd_inv_of hξ hAb hγ
  have hbγi : Work.Mostow.bCocy γ⁻¹ ξ = 0 := by
    have h := Work.Mostow.bCocy_mul hA hI γ⁻¹ γ ξ hξ
    rw [inv_mul_cancel, Work.Mostow.bCocy_one hA hI ξ hξ, hγ, hbγ, zero_add] at h
    exact h.symm
  have h1 := flatAct_eq_flatLin_add hA hI ξ hξ γ hγ hbγ
  have h2 := flatAct_eq_flatLin_add hA hI ξ hξ γ⁻¹ hγi hbγi
  have hleγ := lev_one_of_bCocy_eq_zero ξ hξ γ hγ hbγ
  have hleγi := lev_one_of_bCocy_eq_zero ξ hξ γ⁻¹ hγi hbγi
  have hkey : ∀ y' : Submission.Mostow.E n, inner ℝ y' ξ = 0 →
      y' = Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat γ⁻¹)
            (Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat γ) y'
              + Work.Mostow.flatTrans ξ (Work.Mostow.LambdaMat γ))
          + Work.Mostow.flatTrans ξ (Work.Mostow.LambdaMat γ⁻¹) := by
    intro y' hy'
    have hcomp := Work.Mostow.flatAct_comp hξ hAb hIb hγi hγ hleγi hleγ hy'
    rw [inv_mul_cancel, Work.Mostow.flatAct_one hξ hAb hy'] at hcomp
    rw [h1.2 y' hy'] at hcomp
    rw [h2.2 _ (by rw [← h1.2 y' hy']; exact Work.Mostow.flatAct_mem hξ γ y')] at hcomp
    exact hcomp
  have h0 : Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat γ⁻¹)
        (Work.Mostow.flatTrans ξ (Work.Mostow.LambdaMat γ))
      + Work.Mostow.flatTrans ξ (Work.Mostow.LambdaMat γ⁻¹) = 0 := by
    have h := hkey 0 (by simp)
    simpa only [map_add, map_zero, zero_add, add_zero] using h.symm
  have hfin := hkey y hy
  rw [map_add, add_assoc, h0, add_zero] at hfin
  exact hfin.symm

theorem flatLinMulLambdaMat (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (ξ : Submission.Mostow.E n)
    (hξ : ξ ∈ Submission.Mostow.Sph n) :
    (∀ (γ δ : LeanEval.Geometry.MostowRigidity.PO n 1),
      Submission.Mostow.bd γ ξ = ξ → Submission.Mostow.bd δ ξ = ξ →
      Work.Mostow.bCocy γ ξ = 0 → Work.Mostow.bCocy δ ξ = 0 →
      ∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 →
        Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat (γ * δ)) y
          = Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat γ)
              (Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat δ) y)) ∧
    (∀ (γ : LeanEval.Geometry.MostowRigidity.PO n 1),
      Submission.Mostow.bd γ ξ = ξ → Work.Mostow.bCocy γ ξ = 0 → ∀ y : Submission.Mostow.E n,
        inner ℝ y ξ = 0 →
          Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat γ⁻¹)
            (Work.Mostow.flatLin ξ (Work.Mostow.LambdaMat γ) y) = y) := by
  refine ⟨fun γ δ hγ hδ hbγ hbδ y hy => ?_,
    fun γ hγ hbγ y hy => ?_⟩
  · exact flatLin_mul_of_bCocy_eq_zero hA hI ξ hξ hγ hδ hbγ hbδ hy
  · exact flatLin_inv_of_bCocy_eq_zero hA hI ξ hξ hγ hbγ hy

end Work.Mostow.cuspHoro
