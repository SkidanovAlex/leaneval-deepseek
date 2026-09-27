import Mathlib
import Submission.Work.Mostow.cuspHoroDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.horSpec
import Submission.Work.Mostow.hptOfLevelYc
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.hptOf_level

/-!
# The flat action of the cusp stabiliser on the level-`1` horosphere

For a boundary point `ξ ∈ Sph n` and an isometry `γ` of `ℍⁿ` fixing `ξ` and preserving the
horospherical levels `lev ξ`, the map

`flatAct ξ γ y = yc ξ (γ • horoPt ξ y)`   (`horoPt ξ y = hptOf ξ y 1`)

describes the induced action on the level-`1` horosphere, identified with `ξ^⊥` through the
normalised flat coordinate `yc ξ`.  Using the (sorry-free) `horSpec` at level `D = 1`, this
induced action is seen to be a *surjective Euclidean isometry* of `ξ^⊥` with a genuine action
law, and the hyperbolic displacement of `γ` at the base point is

`hdist 0 (γ • 0) = arccosh (1 + ‖flatAct ξ γ 0‖² / 2)`.

These are the elementary facts on which the uniform gap for parabolic flat displacements rests.
-/

namespace Work.Mostow.cuspHoro

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

set_option maxHeartbeats 1000000

variable {n : ℕ}

lemma horoPt_eq_hptOf (ξ y : E n) : horoPt ξ y = hptOf ξ y 1 := by
  rw [horoPt, hptOf]
  simp only [mul_one, one_pow, one_mul]
  rw [show ‖y‖ ^ 2 / 2 = (1 + ‖y‖ ^ 2) / 2 - 1 / 2 by ring, one_smul]

lemma horoPt_zero (ξ : E n) : horoPt ξ (0 : E n) = (0 : E n) := by
  rw [horoPt]; norm_num

lemma lev_zero (ξ : E n) : lev ξ (0 : E n) = 1 := by simp [lev, tpart]

lemma yc_zero (ξ : E n) : yc ξ (0 : E n) = 0 := by simp [yc, wc, lev_zero]

/-- Level preservation is inherited from the vanishing of the Busemann cocycle. -/
lemma busemann_smul_stab (hI : HypIsometryProp n) {Γ : Subgroup (PO n 1)} {ξ : E n}
    (hξ : ξ ∈ Sph n)
    (hstab : ∀ γ : Γ, bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (γ : Γ) (hγ : bd (γ : PO n 1) ξ = ξ) (u : E n) :
    busemann ξ ((γ : PO n 1) • u) = busemann ξ u := by
  have hbus := hI.2.2.2.2.2.2.2.2.2.2.2.2 (γ : PO n 1) ξ u hξ
  have h0 : busemann (bd (γ : PO n 1) ξ) ((γ : PO n 1) • (0 : E n)) = 0 := by
    simpa only [bCocy] using hstab γ hγ
  rw [hγ] at hbus h0
  rw [h0, add_zero] at hbus
  exact hbus

lemma lev_smul_of_stab (hI : HypIsometryProp n) {Γ : Subgroup (PO n 1)} {ξ : E n}
    (hξ : ξ ∈ Sph n)
    (hstab : ∀ γ : Γ, bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (γ : Γ) (hγ : bd (γ : PO n 1) ξ = ξ) (u : E n) :
    lev ξ ((γ : PO n 1) • u) = lev ξ u := by
  rw [lev_eq_exp hξ ((γ : PO n 1) • u), lev_eq_exp hξ u]
  exact congrArg Real.exp (busemann_smul_stab hI hξ hstab γ hγ u)

lemma lev_horoPt_of (ξ : E n) (hξ : ξ ∈ Sph n) {γ : PO n 1}
    (hlev : ∀ u : E n, lev ξ (γ • u) = lev ξ u) {y : E n} (hy : inner ℝ y ξ = 0) :
    lev ξ (γ • horoPt ξ y) = 1 := by
  rw [hlev, horoPt_eq_hptOf]
  exact (hptOf_level ξ hξ 1 one_pos y hy).1

/-- The induced action of `γ` on the level-`1` horosphere, as provided by `horSpec`. -/
lemma flatAct_eq_rho_of (hn : 1 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) (ξ : E n)
    (hξ : ξ ∈ Sph n) {γ : PO n 1} (hg : bd γ ξ = ξ)
    (hlev : ∀ u : E n, lev ξ (γ • u) = lev ξ u) :
    ∃ ρ : E n → E n,
      (∀ y : E n, inner ℝ y ξ = 0 → flatAct ξ γ y = ρ y) ∧
      (∀ y y' : E n, inner ℝ y ξ = 0 → inner ℝ y' ξ = 0 → ‖ρ y - ρ y'‖ = ‖y - y'‖) ∧
      (∀ y : E n, inner ℝ y ξ = 0 → ∃ y₀ : E n, inner ℝ y₀ ξ = 0 ∧ ρ y₀ = y) := by
  obtain ⟨-, -, -, ρ, hρ1, hρ2, hρ3⟩ := horSpec n hn hA hI ξ hξ 1 one_pos γ hg hlev
  refine ⟨ρ, ?_, hρ2, hρ3⟩
  intro y hy
  show yc ξ (γ • horoPt ξ y) = ρ y
  rw [horoPt_eq_hptOf, ← (hρ1 y hy).2]
  exact (hptOf_level ξ hξ 1 one_pos (ρ y) (hρ1 y hy).1).2

lemma flatAct_orth_of (ξ : E n) (hξ : ξ ∈ Sph n) (γ : PO n 1) (y : E n) :
    inner ℝ (flatAct ξ γ y) ξ = 0 := yc_inner_orth hξ

/-- The induced action of a level-preserving element fixing `ξ` is an isometry of `ξ^⊥`. -/
lemma flatAct_isom_of (hn : 1 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) (ξ : E n)
    (hξ : ξ ∈ Sph n) {γ : PO n 1} (hg : bd γ ξ = ξ)
    (hlev : ∀ u : E n, lev ξ (γ • u) = lev ξ u) {y y' : E n}
    (hy : inner ℝ y ξ = 0) (hy' : inner ℝ y' ξ = 0) :
    ‖flatAct ξ γ y - flatAct ξ γ y'‖ = ‖y - y'‖ := by
  obtain ⟨ρ, hρ, hiso, -⟩ := flatAct_eq_rho_of hn hA hI ξ hξ hg hlev
  rw [hρ y hy, hρ y' hy']
  exact hiso y y' hy hy'

/-- The induced action is surjective onto `ξ^⊥`. -/
lemma flatAct_surj_of (hn : 1 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) (ξ : E n)
    (hξ : ξ ∈ Sph n) {γ : PO n 1} (hg : bd γ ξ = ξ)
    (hlev : ∀ u : E n, lev ξ (γ • u) = lev ξ u) {y : E n} (hy : inner ℝ y ξ = 0) :
    ∃ y₀ : E n, inner ℝ y₀ ξ = 0 ∧ flatAct ξ γ y₀ = y := by
  obtain ⟨ρ, hρ, -, hsurj⟩ := flatAct_eq_rho_of hn hA hI ξ hξ hg hlev
  obtain ⟨y₀, hy₀, hρy₀⟩ := hsurj y hy
  exact ⟨y₀, hy₀, by rw [hρ y₀ hy₀, hρy₀]⟩

lemma flatAct_one_of (hA : POActionProp n) (ξ : E n) (hξ : ξ ∈ Sph n) {y : E n}
    (hy : inner ℝ y ξ = 0) : flatAct ξ (1 : PO n 1) y = y := by
  have hA' := POBasic.ofProp hA
  show yc ξ ((1 : PO n 1) • horoPt ξ y) = y
  rw [hA'.one_smul, horoPt_eq_hptOf]
  exact (hptOf_level ξ hξ 1 one_pos y hy).2

/-- The action law for the induced flat action. -/
lemma flatAct_mul_of (hn : 1 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) (ξ : E n)
    (hξ : ξ ∈ Sph n) {γ δ : PO n 1} (hg : bd γ ξ = ξ) (hd : bd δ ξ = ξ)
    (hlevγ : ∀ u : E n, lev ξ (γ • u) = lev ξ u)
    (hlevδ : ∀ u : E n, lev ξ (δ • u) = lev ξ u) {y : E n} (hy : inner ℝ y ξ = 0) :
    flatAct ξ (γ * δ) y = flatAct ξ γ (flatAct ξ δ y) := by
  have hA' := POBasic.ofProp hA
  have h1 : lev ξ (δ • horoPt ξ y) = 1 := lev_horoPt_of ξ hξ hlevδ hy
  have h2 : horoPt ξ (flatAct ξ δ y) = δ • horoPt ξ y := by
    rw [horoPt_eq_hptOf]
    exact hptOf_yc ξ hξ 1 one_pos _ h1
  show yc ξ ((γ * δ) • horoPt ξ y) = yc ξ (γ • horoPt ξ (flatAct ξ δ y))
  rw [h2, hA'.mul_smul]

lemma bd_inv_of (hA : POActionProp n) {ξ : E n} (hξ : ξ ∈ Sph n) {γ : PO n 1}
    (hg : bd γ ξ = ξ) : bd γ⁻¹ ξ = ξ := by
  have hA' := POBasic.ofProp hA
  have h : bd γ⁻¹ (bd γ ξ) = ξ := by
    have h1 := hA'.bd_mul γ⁻¹ γ ξ hξ
    rw [inv_mul_cancel, hA'.bd_one ξ hξ] at h1
    exact h1.symm
  rwa [hg] at h

lemma lev_smul_inv (hA : POActionProp n) {ξ : E n} {γ : PO n 1}
    (hlevγ : ∀ u : E n, lev ξ (γ • u) = lev ξ u) (u : E n) :
    lev ξ (γ⁻¹ • u) = lev ξ u := by
  have hA' := POBasic.ofProp hA
  have h := hA'.mul_smul γ γ⁻¹ u
  rw [mul_inv_cancel, hA'.one_smul] at h
  rw [← hlevγ (γ⁻¹ • u), ← h]

lemma flatAct_inv_comp (hn : 1 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) (ξ : E n)
    (hξ : ξ ∈ Sph n) {γ : PO n 1} (hg : bd γ ξ = ξ)
    (hlevγ : ∀ u : E n, lev ξ (γ • u) = lev ξ u) {y : E n} (hy : inner ℝ y ξ = 0) :
    flatAct ξ γ⁻¹ (flatAct ξ γ y) = y := by
  have hcomp : ∀ z : E n, inner ℝ z ξ = 0 →
      flatAct ξ (γ⁻¹ * γ) z = flatAct ξ γ⁻¹ (flatAct ξ γ z) :=
    fun z hz => flatAct_mul_of hn hA hI ξ hξ (bd_inv_of hA hξ hg) hg
      (lev_smul_inv hA hlevγ) hlevγ hz
  rw [← hcomp y hy]
  rw [inv_mul_cancel]
  exact flatAct_one_of hA ξ hξ hy

lemma flatAct_comp_inv (hn : 1 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) (ξ : E n)
    (hξ : ξ ∈ Sph n) {γ : PO n 1} (hg : bd γ ξ = ξ)
    (hlevγ : ∀ u : E n, lev ξ (γ • u) = lev ξ u) {y : E n} (hy : inner ℝ y ξ = 0) :
    flatAct ξ γ (flatAct ξ γ⁻¹ y) = y := by
  have hcomp : ∀ z : E n, inner ℝ z ξ = 0 →
      flatAct ξ (γ * γ⁻¹) z = flatAct ξ γ (flatAct ξ γ⁻¹ z) :=
    fun z hz => flatAct_mul_of hn hA hI ξ hξ hg (bd_inv_of hA hξ hg) hlevγ
      (lev_smul_inv hA hlevγ) hz
  rw [← hcomp y hy]
  rw [mul_inv_cancel]
  exact flatAct_one_of hA ξ hξ hy

lemma cosh_hdist_zero_flatAct (ξ : E n) (hξ : ξ ∈ Sph n) (γ : PO n 1)
    (hlev : ∀ u : E n, lev ξ (γ • u) = lev ξ u) :
    Real.cosh (hdist (0 : E n) (γ • (0 : E n))) = 1 + ‖flatAct ξ γ (0 : E n)‖ ^ 2 / 2 := by
  have hlev0 : lev ξ (γ • (0 : E n)) = 1 := by rw [hlev, lev_zero]
  have h := levYcFormula hξ (0 : E n) (γ • (0 : E n))
  simp only [hlev0, lev_zero, yc_zero, div_one, Real.log_one, Real.cosh_zero] at h
  have hflat : yc ξ (γ • (0 : E n)) = flatAct ξ γ (0 : E n) := by
    show yc ξ (γ • (0 : E n)) = yc ξ (γ • horoPt ξ (0 : E n))
    rw [horoPt_zero]
  rw [hflat] at h
  have h2 : (1 : ℝ) + 1 * 1 / 2 * ‖(0 : E n) - flatAct ξ γ (0 : E n)‖ ^ 2
      = 1 + ‖flatAct ξ γ (0 : E n)‖ ^ 2 / 2 := by
    rw [zero_sub, norm_neg]; ring
  rw [← h2]
  exact h

/-- The hyperbolic displacement of `γ` at the base point in terms of the flat action. -/
lemma hdist_zero_flatAct (ξ : E n) (hξ : ξ ∈ Sph n) (γ : PO n 1)
    (hlev : ∀ u : E n, lev ξ (γ • u) = lev ξ u) :
    hdist (0 : E n) (γ • (0 : E n)) = Real.arcosh (1 + ‖flatAct ξ γ (0 : E n)‖ ^ 2 / 2) := by
  have hge : (1 : ℝ) ≤ 1 + ‖flatAct ξ γ (0 : E n)‖ ^ 2 / 2 := by
    have := norm_nonneg (flatAct ξ γ (0 : E n))
    nlinarith [sq_nonneg ‖flatAct ξ γ (0 : E n)‖]
  have h1 : Real.cosh (hdist (0 : E n) (γ • (0 : E n)))
      = Real.cosh (Real.arcosh (1 + ‖flatAct ξ γ (0 : E n)‖ ^ 2 / 2)) := by
    rw [cosh_hdist_zero_flatAct ξ hξ γ hlev, Real.cosh_arcosh hge]
  have h2 := congrArg Real.arcosh h1
  rw [Real.arcosh_cosh (hdist_nonneg _ _), Real.arcosh_cosh (Real.arcosh_nonneg hge)] at h2
  exact h2

end Work.Mostow.cuspHoro
