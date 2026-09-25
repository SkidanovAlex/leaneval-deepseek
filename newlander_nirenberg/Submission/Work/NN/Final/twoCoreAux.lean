/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The `(0,2)`-Poincaré operator on nested polydiscs (`twoCore`): auxiliary construction

This file contains the construction behind `Work.NN.Final.twoCore`
(`Submission/Work/NN/Final/twoCore.lean`): the flat `(0,2)`-solver on the nested polydiscs
`pd n ρ 2 ⊂ pd n ρ 4` with the full `C^{k,α}` gain.  See the docstrings below for the two steps
(one Bochner–Martinelli step, and the transferred loss-free `uS2`-solver).
-/
import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.CR.Flat.Holder.holderNorm_smul
import Submission.Work.CR.Flat.Holder.holderNorm_sum_le
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comp_diagAffine
import Submission.Work.CR.Flat.Polydisc.dbarCoord_add
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmPot_dbarCoord
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
import Submission.Work.NN.Core.bmRow
import Submission.Work.NN.Core.bmRow_holder
import Submission.Work.NN.Core.exists_contDiff_bump_of_isCompact_subset
import Submission.Work.NN.Final.bmDefect_eq_local
import Submission.Work.NN.Final.twoRec
import Submission.Work.NN.Final.uS2_solves
import Submission.Work.NN.Final.uS2_estimate
import Submission.Work.NN.Final.uS2_smooth
import Submission.Work.NN.Final.uS2_contDiff
import Submission.Work.NN.Final.uS2_holderNorm_uniform
import Submission.Work.NN.Final.holderNorm_comp_linear
import Submission.Work.NN.Final.bmPot_linear
import Submission.Work.NN.Final.bmPot_bmH_dbarCoord_eq
import Submission.Work.NN.Final.bmPot_bmH_dbarCoord_eq_local
import Submission.Work.NN.Final.bmPot_bmH_holderNorm_le
import Submission.Work.NN.Final.uS2_rescale_holderNorm_le

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set MeasureTheory
open Work.CR.Flat Work.CR.Flat.Cauchy

namespace Work.NN.Final

variable {n : ℕ}

/-! ## Elementary `∂̄`-calculus -/

/-- `∂̄_j` of a constant multiple of a differentiable function. -/
lemma dbarCoord_const_mul {j : Fin n} (c : ℂ) (V : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hV : DifferentiableAt ℝ V z) :
    dbarCoord j (fun w => c * V w) z = c * dbarCoord j V z := by
  rw [Work.CR.Flat.Polydisc.dbarCoord_mul j (fun _ => c) V z (differentiableAt_const c) hV]
  simp [dbarCoord]

/-- Chain rule for the diagonal linear map `diagLin a` (`z ↦ (i ↦ a i * z i)`). -/
lemma dbarCoord_comp_diagLin {a : Fin n → ℝ} (j : Fin n) {U : (Fin n → ℂ) → ℂ}
    {z : Fin n → ℂ} (hU : DifferentiableAt ℝ U (Work.CR.Flat.Polydisc.diagLin a z)) :
    dbarCoord j (fun z' => U (Work.CR.Flat.Polydisc.diagLin a z')) z
      = (a j : ℂ) * dbarCoord j U (Work.CR.Flat.Polydisc.diagLin a z) := by
  have hU' : DifferentiableAt ℝ U (fun i => (0 : Fin n → ℂ) i + (a i : ℂ) * z i) := by
    simpa only [Pi.zero_apply, zero_add, Work.CR.Flat.Polydisc.diagLin_apply] using hU
  have h := Work.CR.Flat.Polydisc.dbarCoord_comp_diagAffine (a := a) (b := 0) (j := j)
    (U := U) (z := z) hU'
  have h1 : (fun z' : Fin n → ℂ => U (Work.CR.Flat.Polydisc.diagLin a z'))
      = fun z' => U (fun i => (0 : Fin n → ℂ) i + (a i : ℂ) * z' i) := by
    funext z'; congr 1; funext i; simp [Work.CR.Flat.Polydisc.diagLin_apply]
  have h2 : Work.CR.Flat.Polydisc.diagLin a z
      = fun i => (0 : Fin n → ℂ) i + (a i : ℂ) * z i := by
    funext i; simp [Work.CR.Flat.Polydisc.diagLin_apply]
  rw [h1, h2]
  exact h

/-! ## The scaled radii and the two diagonal maps -/

/-- The radii of the polydisc on which the transferred solver is applied: `(8/3) ρ`. -/
def sgm (ρ : Fin n → ℝ) : Fin n → ℝ := fun i => (8/3) * ρ i

lemma sgm_pos {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (i : Fin n) : 0 < sgm ρ i := by
  have := hρ i; rw [sgm]; linarith

lemma sgm_ne_zero {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (i : Fin n) : sgm ρ i ≠ 0 :=
  ne_of_gt (sgm_pos hρ i)

/-- The diagonal scaling `z ↦ (i ↦ sgm ρ i * z i)`. -/
def smap (ρ : Fin n → ℝ) : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
  Work.CR.Flat.Polydisc.diagLin (sgm ρ)

/-- The inverse diagonal scaling `z ↦ (i ↦ (sgm ρ i)⁻¹ * z i)`. -/
def sInv (ρ : Fin n → ℝ) : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
  Work.CR.Flat.Polydisc.diagLin (fun i => (sgm ρ i)⁻¹)

@[simp] lemma smap_apply (ρ : Fin n → ℝ) (z : Fin n → ℂ) (i : Fin n) :
    smap ρ z i = (sgm ρ i : ℂ) * z i := by
  rw [smap, Work.CR.Flat.Polydisc.diagLin_apply]

@[simp] lemma sInv_apply (ρ : Fin n → ℝ) (z : Fin n → ℂ) (i : Fin n) :
    sInv ρ z i = (((sgm ρ i)⁻¹ : ℝ) : ℂ) * z i := by
  rw [sInv, Work.CR.Flat.Polydisc.diagLin_apply]

lemma smap_sInv {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (z : Fin n → ℂ) :
    smap ρ (sInv ρ z) = z := by
  funext i
  rw [smap_apply, sInv_apply]
  have h' : (sgm ρ i : ℂ) * (((sgm ρ i)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (sgm_ne_zero hρ i), Complex.ofReal_one]
  rw [← mul_assoc, h', one_mul]

lemma sInv_smap {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (z : Fin n → ℂ) :
    sInv ρ (smap ρ z) = z := by
  funext i
  rw [sInv_apply, smap_apply]
  have h' : (((sgm ρ i)⁻¹ : ℝ) : ℂ) * (sgm ρ i : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (sgm_ne_zero hρ i), Complex.ofReal_one]
  rw [← mul_assoc, h', one_mul]

lemma contDiff_smap (ρ : Fin n → ℝ) (m : ℕ∞) : ContDiff ℝ m (smap ρ) := (smap ρ).contDiff

lemma contDiff_sInv (ρ : Fin n → ℝ) (m : ℕ∞) : ContDiff ℝ m (sInv ρ) := (sInv ρ).contDiff

/-- Chain rule for the inverse scaling. -/
lemma dbarCoord_comp_sInv {ρ : Fin n → ℝ} (i : Fin n) {U : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hU : DifferentiableAt ℝ U (sInv ρ z)) :
    dbarCoord i (fun z' => U (sInv ρ z')) z
      = (((sgm ρ i)⁻¹ : ℝ) : ℂ) * dbarCoord i U (sInv ρ z) :=
  dbarCoord_comp_diagLin (a := fun i : Fin n => (sgm ρ i)⁻¹) (j := i) (U := U) (z := z) hU

/-- Chain rule for the scaling. -/
lemma dbarCoord_comp_smap {ρ : Fin n → ℝ} (i : Fin n) {U : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hU : DifferentiableAt ℝ U (smap ρ z)) :
    dbarCoord i (fun z' => U (smap ρ z')) z
      = ((sgm ρ i : ℝ) : ℂ) * dbarCoord i U (smap ρ z) :=
  dbarCoord_comp_diagLin (a := sgm ρ) (j := i) (U := U) (z := z) hU

/-- The scaling sends the polydisc of radii `c * sgm ρ` onto the polydisc of constant radius `c`. -/
lemma smap_preimage_polydisc {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (c : ℝ) :
    smap ρ ⁻¹' polydisc 0 (fun i => c * sgm ρ i) = polydisc 0 (fun _ => c) := by
  ext w
  rw [Set.mem_preimage, mem_polydisc, mem_polydisc]
  simp only [Pi.zero_apply, sub_zero, smap_apply, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (le_of_lt (sgm_pos hρ _))]
  constructor
  · intro h i
    have h1 : sgm ρ i * ‖w i‖ < sgm ρ i * c := by
      have := h i
      rwa [mul_comm c (sgm ρ i)] at this
    exact lt_of_mul_lt_mul_left h1 (le_of_lt (sgm_pos hρ i))
  · intro h i
    rw [← mul_comm (sgm ρ i) c]
    exact mul_lt_mul_of_pos_left (h i) (sgm_pos hρ i)

lemma smap_mapsTo {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    MapsTo (smap ρ) (polydisc 0 (fun _ => (1 : ℝ))) (polydisc 0 (sgm ρ)) := by
  intro w hw
  have h := smap_preimage_polydisc hρ 1
  simp only [one_mul] at h
  rw [← h] at hw
  rwa [Set.mem_preimage] at hw

/-- Membership of `pd n ρ 2` after applying the inverse scaling: exactly `solveSet`. -/
lemma sInv_mem_solveSet_iff {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (z : Fin n → ℂ) :
    sInv ρ z ∈ solveSet ↔ z ∈ pd n ρ 2 := by
  have h3 : ∀ i : Fin n, sgm ρ i * (3 / 4) = 2 * ρ i := fun i => by rw [sgm]; ring
  rw [mem_solveSet, mem_pd]
  simp only [eqRad, sInv_apply, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (le_of_lt (inv_pos.mpr (sgm_pos hρ _)))]
  constructor
  · intro h i
    have hi := h i
    have h4 : sgm ρ i * ((sgm ρ i)⁻¹ * ‖z i‖) = ‖z i‖ := by
      rw [← mul_assoc, mul_inv_cancel₀ (sgm_ne_zero hρ i), one_mul]
    rw [← h4, ← h3 i]
    exact mul_lt_mul_of_pos_left hi (sgm_pos hρ i)
  · intro h i
    have hkey : (sgm ρ i)⁻¹ * (2 * ρ i) = 3 / 4 := by
      rw [← h3 i, ← mul_assoc, inv_mul_cancel₀ (sgm_ne_zero hρ i), one_mul]
    rw [← hkey]
    exact mul_lt_mul_of_pos_left (h i) (inv_pos.mpr (sgm_pos hρ i))

lemma sInv_mapsTo_solveSet {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    MapsTo (sInv ρ) (pd n ρ 2) solveSet :=
  fun z hz => (sInv_mem_solveSet_iff hρ z).mpr hz

lemma sInv_preimage_solveSet {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    sInv ρ ⁻¹' solveSet = pd n ρ 2 := by
  ext z
  rw [Set.mem_preimage]
  exact sInv_mem_solveSet_iff hρ z

/-! ## The rescaled datum and the transferred solver -/

/-- The `(0,2)`-datum rescaled so that the polydisc of radii `sgm ρ` becomes the unit polydisc. -/
def gmap (ρ : Fin n → ℝ) (ζ : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    Fin n → Fin n → (Fin n → ℂ) → ℂ :=
  fun j l w => (sgm ρ j : ℂ) * (sgm ρ l : ℂ) * ζ j l (smap ρ w)

@[simp] lemma gmap_apply (ρ : Fin n → ℝ) (ζ : Fin n → Fin n → (Fin n → ℂ) → ℂ)
    (j l : Fin n) (w : Fin n → ℂ) :
    gmap ρ ζ j l w = (sgm ρ j : ℂ) * (sgm ρ l : ℂ) * ζ j l (smap ρ w) := rfl

/-- The transferred `(0,2)`-solver: it solves `∂̄_j ψ_l - ∂̄_l ψ_j = ζ_{jl}` on `pd n ρ 2` for
data `ζ` which are `∂̄`-closed on `polydisc 0 (sgm ρ) = pd n ρ (8/3)`. -/
def tfin (ρ : Fin n → ℝ) (ζ : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    Fin n → (Fin n → ℂ) → ℂ :=
  fun l z => (((sgm ρ l)⁻¹ : ℝ) : ℂ) * uS2 (gmap ρ ζ) l (sInv ρ z)

@[simp] lemma tfin_apply (ρ : Fin n → ℝ) (ζ : Fin n → Fin n → (Fin n → ℂ) → ℂ)
    (l : Fin n) (z : Fin n → ℂ) :
    tfin ρ ζ l z = (((sgm ρ l)⁻¹ : ℝ) : ℂ) * uS2 (gmap ρ ζ) l (sInv ρ z) := rfl

/-- Unfolding of `tfin` at the level of functions. -/
lemma tfin_apply' (ρ : Fin n → ℝ) (ζ : Fin n → Fin n → (Fin n → ℂ) → ℂ) (l : Fin n) :
    tfin ρ ζ l
      = fun z => (((sgm ρ l)⁻¹ : ℝ) : ℂ) * uS2 (gmap ρ ζ) l (sInv ρ z) := rfl

lemma dbarCoord_gmap {ρ : Fin n → ℝ} {ζ : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hζ : ∀ i l, ContDiff ℝ 1 (ζ i l)) (i l m : Fin n) (w : Fin n → ℂ) :
    dbarCoord i (gmap ρ ζ l m) w
      = (sgm ρ l : ℂ) * (sgm ρ m : ℂ) * ((sgm ρ i : ℝ) : ℂ)
          * dbarCoord i (ζ l m) (smap ρ w) := by
  have hd : DifferentiableAt ℝ (ζ l m) (smap ρ w) :=
    ((hζ l m).differentiable one_ne_zero).differentiableAt
  have hinner : DifferentiableAt ℝ (smap ρ) w := (smap ρ).differentiableAt
  have hVd : DifferentiableAt ℝ (fun w' => ζ l m (smap ρ w')) w := hd.comp w hinner
  have hchain : dbarCoord i (fun w' => ζ l m (smap ρ w')) w
      = ((sgm ρ i : ℝ) : ℂ) * dbarCoord i (ζ l m) (smap ρ w) :=
    dbarCoord_comp_smap i hd
  have hV2 : DifferentiableAt ℝ (fun w' => (sgm ρ m : ℂ) * ζ l m (smap ρ w')) w :=
    hVd.const_mul _
  have h1 : dbarCoord i (fun w' => (sgm ρ l : ℂ) * ((sgm ρ m : ℂ) * ζ l m (smap ρ w'))) w
      = (sgm ρ l : ℂ) * dbarCoord i (fun w' => (sgm ρ m : ℂ) * ζ l m (smap ρ w')) w :=
    dbarCoord_const_mul (j := i) _ _ w hV2
  have h2 : dbarCoord i (fun w' => (sgm ρ m : ℂ) * ζ l m (smap ρ w')) w
      = (sgm ρ m : ℂ) * dbarCoord i (fun w' => ζ l m (smap ρ w')) w :=
    dbarCoord_const_mul (j := i) _ _ w hVd
  rw [show gmap ρ ζ l m
        = fun w' => (sgm ρ l : ℂ) * ((sgm ρ m : ℂ) * ζ l m (smap ρ w')) from by
      funext w'; rw [gmap_apply]; ring,
    h1, h2, hchain]
  ring

/-- Closedness transfers to the rescaled datum on the unit polydisc. -/
lemma gmap_closed {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {ζ : Fin n → Fin n → (Fin n → ℂ) → ℂ} (hζ : ∀ i l, ContDiff ℝ 1 (ζ i l))
    (hcl : ∀ i l m z, z ∈ polydisc 0 (sgm ρ) →
      dbarCoord i (ζ l m) z - dbarCoord l (ζ i m) z + dbarCoord m (ζ i l) z = 0) :
    ∀ i l m w, w ∈ polydisc 0 (fun _ => (1 : ℝ)) →
      dbarCoord i (gmap ρ ζ l m) w - dbarCoord l (gmap ρ ζ i m) w
        + dbarCoord m (gmap ρ ζ i l) w = 0 := by
  intro i l m w hw
  have hw' : smap ρ w ∈ polydisc 0 (sgm ρ) := smap_mapsTo hρ hw
  rw [dbarCoord_gmap hζ i l m w, dbarCoord_gmap hζ l i m w, dbarCoord_gmap hζ m i l w]
  have hc := hcl i l m (smap ρ w) hw'
  have key : (sgm ρ i : ℂ) * (sgm ρ l : ℂ) * (sgm ρ m : ℂ)
      * (dbarCoord i (ζ l m) (smap ρ w) - dbarCoord l (ζ i m) (smap ρ w)
          + dbarCoord m (ζ i l) (smap ρ w)) = 0 := by
    rw [hc, mul_zero]
  have h1 : (sgm ρ l : ℂ) * (sgm ρ m : ℂ) * (sgm ρ i : ℂ) * dbarCoord i (ζ l m) (smap ρ w)
      = (sgm ρ i : ℂ) * (sgm ρ l : ℂ) * (sgm ρ m : ℂ) * dbarCoord i (ζ l m) (smap ρ w) := by
    ring
  have h2 : (sgm ρ i : ℂ) * (sgm ρ m : ℂ) * (sgm ρ l : ℂ) * dbarCoord l (ζ i m) (smap ρ w)
      = (sgm ρ i : ℂ) * (sgm ρ l : ℂ) * (sgm ρ m : ℂ) * dbarCoord l (ζ i m) (smap ρ w) := by
    ring
  rw [h1, h2]
  linear_combination key

lemma gmap_antisymm {ρ : Fin n → ℝ} {ζ : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hζ : ∀ i l z, ζ i l z = - ζ l i z) (i l : Fin n) (w : Fin n → ℂ) :
    gmap ρ ζ i l w = - gmap ρ ζ l i w := by
  rw [gmap_apply, gmap_apply, hζ l i (smap ρ w)]
  ring

/-- The rescaled datum of a `C^m` family is `C^m`. -/
lemma contDiff_gmap {ρ : Fin n → ℝ} {ζ : Fin n → Fin n → (Fin n → ℂ) → ℂ} {m : ℕ∞}
    (hζ : ∀ i l, ContDiff ℝ m (ζ i l)) (i l : Fin n) :
    ContDiff ℝ m (gmap ρ ζ i l) := by
  have h1 : ContDiff ℝ m (fun w => ζ i l (smap ρ w)) := (hζ i l).comp (contDiff_smap ρ m)
  exact contDiff_const.mul h1

/-- The components of `uS2` applied to a rescaled `C^m` datum are `C^m`. -/
lemma contDiff_uS2_gmap {ρ : Fin n → ℝ} {ζ : Fin n → Fin n → (Fin n → ℂ) → ℂ} {m : ℕ}
    (hζ : ∀ i l, ContDiff ℝ m (ζ i l)) (i : Fin n) :
    ContDiff ℝ m (uS2 (gmap ρ ζ) i) :=
  uS2_contDiff m (fun i l => contDiff_gmap hζ i l) i

/-- **The transferred solver solves the `(0,2)`-equation on `pd n ρ 2`**. -/
lemma tfin_solves {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {ζ : Fin n → Fin n → (Fin n → ℂ) → ℂ} (hζ : ∀ i l, ContDiff ℝ 1 (ζ i l))
    (hanti : ∀ i l z, ζ i l z = - ζ l i z)
    (hcl : ∀ i l m z, z ∈ polydisc 0 (sgm ρ) →
      dbarCoord i (ζ l m) z - dbarCoord l (ζ i m) z + dbarCoord m (ζ i l) z = 0) :
    ∀ j l z, z ∈ pd n ρ 2 →
      dbarCoord j (tfin ρ ζ l) z - dbarCoord l (tfin ρ ζ j) z = ζ j l z := by
  intro j l z hz
  have hψ : ∀ i, ContDiff ℝ 1 (uS2 (gmap ρ ζ) i) := fun i => contDiff_uS2_gmap hζ i
  have hdiff : ∀ i, DifferentiableAt ℝ (uS2 (gmap ρ ζ) i) (sInv ρ z) :=
    fun i => ((hψ i).differentiable (by simp)).differentiableAt
  have hcomp : ∀ i, DifferentiableAt ℝ (fun z' => uS2 (gmap ρ ζ) i (sInv ρ z')) z :=
    fun i => (hdiff i).comp z (sInv ρ).differentiableAt
  have hchain : ∀ b i : Fin n,
      dbarCoord i (tfin ρ ζ b) z
        = (((sgm ρ b)⁻¹ : ℝ) : ℂ) * (((sgm ρ i)⁻¹ : ℝ) : ℂ)
            * dbarCoord i (uS2 (gmap ρ ζ) b) (sInv ρ z) := by
    intro b i
    have hfun : tfin ρ ζ b
        = fun w => (((sgm ρ b)⁻¹ : ℝ) : ℂ)
            * (fun z' => uS2 (gmap ρ ζ) b (sInv ρ z')) w := rfl
    rw [hfun, dbarCoord_const_mul (j := i) _ _ z (hcomp b)]
    rw [dbarCoord_comp_sInv i (hdiff b)]
    ring
  have key := uS2_solves (η := gmap ρ ζ) (fun i l => contDiff_gmap hζ i l)
    (gmap_antisymm hanti) (gmap_closed hρ hζ hcl) j l (sInv ρ z) (sInv_mapsTo_solveSet hρ hz)
  rw [gmap_apply, smap_sInv hρ] at key
  have hcl_ : (((sgm ρ l)⁻¹ : ℝ) : ℂ) * (sgm ρ l : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (sgm_ne_zero hρ l), Complex.ofReal_one]
  have hcj : (((sgm ρ j)⁻¹ : ℝ) : ℂ) * (sgm ρ j : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (sgm_ne_zero hρ j), Complex.ofReal_one]
  have halg : (((sgm ρ l)⁻¹ : ℝ) : ℂ) * (((sgm ρ j)⁻¹ : ℝ) : ℂ)
      * ((sgm ρ j : ℂ) * (sgm ρ l : ℂ)) = 1 := by
    calc (((sgm ρ l)⁻¹ : ℝ) : ℂ) * (((sgm ρ j)⁻¹ : ℝ) : ℂ)
          * ((sgm ρ j : ℂ) * (sgm ρ l : ℂ))
        = ((((sgm ρ l)⁻¹ : ℝ) : ℂ) * (sgm ρ l : ℂ))
            * ((((sgm ρ j)⁻¹ : ℝ) : ℂ) * (sgm ρ j : ℂ)) := by ring
      _ = 1 * 1 := by rw [hcl_, hcj]
      _ = 1 := one_mul 1
  rw [hchain l j, hchain j l]
  rw [show (((sgm ρ l)⁻¹ : ℝ) : ℂ) * (((sgm ρ j)⁻¹ : ℝ) : ℂ)
          * dbarCoord j (uS2 (gmap ρ ζ) l) (sInv ρ z)
        - (((sgm ρ j)⁻¹ : ℝ) : ℂ) * (((sgm ρ l)⁻¹ : ℝ) : ℂ)
          * dbarCoord l (uS2 (gmap ρ ζ) j) (sInv ρ z)
      = (((sgm ρ l)⁻¹ : ℝ) : ℂ) * (((sgm ρ j)⁻¹ : ℝ) : ℂ)
          * (dbarCoord j (uS2 (gmap ρ ζ) l) (sInv ρ z)
              - dbarCoord l (uS2 (gmap ρ ζ) j) (sInv ρ z)) from by ring, key]
  rw [show (((sgm ρ l)⁻¹ : ℝ) : ℂ) * (((sgm ρ j)⁻¹ : ℝ) : ℂ)
          * ((sgm ρ j : ℂ) * (sgm ρ l : ℂ) * ζ j l z)
      = ((((sgm ρ l)⁻¹ : ℝ) : ℂ) * (((sgm ρ j)⁻¹ : ℝ) : ℂ)
          * ((sgm ρ j : ℂ) * (sgm ρ l : ℂ))) * ζ j l z from by ring, halg, one_mul]

/-- The transferred solver is additive in the datum. -/
lemma tfin_add {ρ : Fin n → ℝ} (ζ ζ' : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    tfin ρ (ζ + ζ') = tfin ρ ζ + tfin ρ ζ' := by
  funext l z
  have hg : gmap ρ (ζ + ζ') = gmap ρ ζ + gmap ρ ζ' := by
    funext i l' w
    simp only [gmap_apply, Pi.add_apply]
    ring
  rw [tfin_apply', hg, uS2_add]
  simp only [Pi.add_apply, tfin_apply]
  ring

/-- The transferred solver is `ℝ`-homogeneous in the datum. -/
lemma tfin_smul {ρ : Fin n → ℝ} (c : ℝ) (ζ : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    tfin ρ (c • ζ) = c • tfin ρ ζ := by
  funext l z
  have hg : gmap ρ (c • ζ) = c • gmap ρ ζ := by
    funext i l' w
    simp only [gmap_apply, Pi.smul_apply]
    rw [Complex.real_smul, Complex.real_smul]
    ring
  rw [tfin_apply', hg, uS2_smul]
  simp only [Pi.smul_apply, tfin_apply]
  rw [Complex.real_smul, Complex.real_smul]
  ring

/-- **The transferred solver is bounded at every order**, with the datum norm taken on the
polydisc of radii `sgm ρ` and the solution norm on `pd n ρ 2`.  (This is
`Work.NN.Final.uS2_rescale_holderNorm_le` transferred to the notation of this file.) -/
lemma tfin_bound {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ζ : Fin n → Fin n → (Fin n → ℂ) → ℂ,
      (∀ i l, ContDiff ℝ k (ζ i l)) →
      ∀ j : Fin n,
        holderNorm k α (tfin ρ ζ j) (pd n ρ 2)
          ≤ ENNReal.ofReal C *
              ∑ i : Fin n, ∑ l : Fin n,
                holderNorm k α (ζ i l) (polydisc 0 (sgm ρ)) := by
  obtain ⟨C, hC0, hC⟩ := uS2_rescale_holderNorm_le (n := n) hα0 hα1 k (fun i => sgm_ne_zero hρ i)
  refine ⟨C, hC0, fun ζ hζ j => ?_⟩
  have hreg : polydisc 0 (fun i => (3 / 4 : ℝ) * sgm ρ i) = pd n ρ 2 := by
    congr 1
    funext i
    rw [sgm]; ring
  rw [hreg] at hC
  exact hC ζ hζ j

/-- The transferred solver is smooth on smooth data. -/
lemma tfin_smooth {ρ : Fin n → ℝ} {ζ : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hζ : ∀ i l, ContDiff ℝ (⊤ : ℕ∞) (ζ i l)) (j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (tfin ρ ζ j) := by
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (uS2 (gmap ρ ζ) j) :=
    uS2_smooth (gmap ρ ζ) (fun i l => contDiff_gmap hζ i l) j
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z => uS2 (gmap ρ ζ) j (sInv ρ z)) :=
    hψ.comp (contDiff_sInv ρ _)
  exact contDiff_const.mul h1


/-! ## The cut-off -/

/-- A smooth cut-off which is `1` on `pd n ρ (8/3)` and whose topological support lies in
`pd n ρ 3`. -/
lemma exists_cutoff {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    ∃ (χ : (Fin n → ℂ) → ℂ) (V : Set (Fin n → ℂ)), ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ pd n ρ 3 ∧ IsOpen V ∧
      (∀ z, z ∈ pd n ρ (8/3 : ℝ) → z ∈ V) ∧ (∀ y ∈ V, χ y = 1) := by
  have hKc : IsCompact (Set.univ.pi fun i => Metric.closedBall (0 : ℂ) ((17/6) * ρ i)) :=
    isCompact_univ_pi fun i => isCompact_closedBall 0 _
  have hKU : Set.univ.pi (fun i => Metric.closedBall (0 : ℂ) ((17/6) * ρ i)) ⊆ pd n ρ 3 := by
    intro z hz
    rw [mem_pd]
    intro i
    have h1 : ‖z i‖ ≤ (17/6) * ρ i := by
      have h2 := hz i
      rw [Metric.mem_closedBall, dist_eq_norm] at h2
      simpa using h2
    have h3 : (17/6 : ℝ) * ρ i < 3 * ρ i := by linarith [hρ i]
    linarith
  obtain ⟨χ, V, hχ, hcs, htsupp, hVo, hKV, hχ1⟩ :=
    Work.NN.Core.exists_contDiff_bump_of_isCompact_subset (n := n) hKc (isOpen_pd ρ 3) hKU
  refine ⟨χ, V, hχ, hcs, htsupp, hVo, fun z hz => hKV ?_, hχ1⟩
  intro i _
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have h2 : ‖z i‖ < (8/3) * ρ i := by
    have h3 := hz i
    rw [Pi.zero_apply, sub_zero] at h3
    exact h3
  have h1 : (8/3 : ℝ) * ρ i ≤ (17/6) * ρ i := by linarith [hρ i]
  exact le_trans (le_of_lt h2) h1

/-- The support of `∂̄_a χ` is contained in the (topological) support of `χ`. -/
lemma tsupport_dbarCoord_subset {χ : (Fin n → ℂ) → ℂ} (a : Fin n) :
    tsupport (fun z => dbarCoord a χ z) ⊆ tsupport χ := by
  refine closure_minimal ?_ (isClosed_tsupport χ)
  intro y hy
  by_contra h
  have h0 : χ =ᶠ[nhds y] (0 : (Fin n → ℂ) → ℂ) := by
    filter_upwards [(isClosed_tsupport χ).compl_mem_nhds h] with w hw
    exact Function.notMem_support.mp fun hw' => hw (by rw [tsupport]; exact subset_closure hw')
  have hy0 : fderiv ℝ χ y = 0 := by
    have := h0.fderiv_eq (𝕜 := ℝ)
    simpa using this
  exact (Function.mem_support.mp hy) (by simp [dbarCoord, hy0])

/-- The `∂̄`-derivative of a smooth function is smooth. -/
lemma contDiff_dbarCoord_of {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (a : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w => dbarCoord a χ w) := by
  rw [Work.CR.Flat.Polydisc.dbarCoord_eq_comp]
  exact (Work.CR.Flat.Polydisc.dbarCoordPhi a).contDiff.comp (hχ.fderiv_right (by simp))

/-- Products of a compactly supported smooth function with a function that is only `C^m` on an
open set containing the support are globally `C^m`. -/
lemma contDiff_mul_of_contDiffOn_tsupp {m : ℕ} {O : Set (Fin n → ℂ)} (hO : IsOpen O)
    {η f : (Fin n → ℂ) → ℂ} (hη : ContDiff ℝ ∞ η) (hηt : tsupport η ⊆ O)
    (hf : ContDiffOn ℝ m f O) : ContDiff ℝ m (fun z => η z * f z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport η
  · exact ((hη.of_le (by simp)).contDiffAt).mul (hf.contDiffAt (hO.mem_nhds (hηt hz)))
  · have h0 : η =ᶠ[nhds z] 0 := by
      filter_upwards [(isClosed_tsupport η).compl_mem_nhds hz] with y hy
      exact Function.notMem_support.mp fun hy' => hy (by rw [tsupport]; exact subset_closure hy')
    have hev : (fun y => η y * f y) =ᶠ[nhds z] (fun _ => 0) := by
      filter_upwards [h0] with y hy
      simp [hy]
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev

/-- The products `∂̄_a χ · η` are globally `C^m` when `η` is `C^m` on `pd n ρ 4` and the support of
`χ` lies in `pd n ρ 4`. -/
lemma contDiff_dbarCoord_mul {ρ : Fin n → ℝ} {χ η : (Fin n → ℂ) → ℂ} {m : ℕ}
    (hχ : ContDiff ℝ ∞ χ) (hχt : tsupport χ ⊆ pd n ρ 4)
    (hη : ContDiffOn ℝ m η (pd n ρ 4)) (a : Fin n) :
    ContDiff ℝ m (fun w => dbarCoord a χ w * η w) := by
  have h1 : ContDiff ℝ ∞ (fun w => dbarCoord a χ w) :=
    (contDiff_dbarCoord_of hχ a).of_le (by simp)
  exact contDiff_mul_of_contDiffOn_tsupp (isOpen_pd ρ 4) h1
    ((tsupport_dbarCoord_subset a).trans hχt) hη

/-! ## The error term of one Bochner–Martinelli step -/

/-- The error term `E = γ⁻¹ bmPot (bmH χ η)` of one Bochner–Martinelli step. -/
def Edat (χ : (Fin n → ℂ) → ℂ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    Fin n → Fin n → (Fin n → ℂ) → ℂ :=
  fun j l z => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
    Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) z

@[simp] lemma Edat_apply (χ : (Fin n → ℂ) → ℂ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ)
    (j l : Fin n) (z : Fin n → ℂ) :
    Edat χ η j l z = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
      Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) z := rfl


/-- The topological support of `∂̄_a χ` is compact when that of `χ` is. -/
lemma hasCompactSupport_dbarCoord {χ : (Fin n → ℂ) → ℂ} (hcs : HasCompactSupport χ)
    (a : Fin n) : HasCompactSupport (fun w => dbarCoord a χ w) := by
  have h : IsCompact (tsupport (fun w => dbarCoord a χ w)) :=
    hcs.isCompact.of_isClosed_subset (isClosed_tsupport _) (tsupport_dbarCoord_subset a)
  exact h

/-- The explicit form of `bmH`. -/
lemma bmH_eq_sum (χ : (Fin n → ℂ) → ℂ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ)
    (j l i : Fin n) (w : Fin n → ℂ) :
    Work.NN.Core.bmH χ η j l i w
      = dbarCoord i χ w * η j l w + dbarCoord j χ w * η l i w
        - dbarCoord l χ w * η j i w := rfl

lemma bmH_antisymm {χ : (Fin n → ℂ) → ℂ} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hanti : ∀ i l z, η i l z = - η l i z) (j l i : Fin n) (w : Fin n → ℂ) :
    Work.NN.Core.bmH χ η j l i w = - Work.NN.Core.bmH χ η l j i w := by
  rw [bmH_eq_sum, bmH_eq_sum, hanti l j w]
  ring

lemma bmH_continuous {χ : (Fin n → ℂ) → ℂ} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ 1 χ) (hηc : ∀ i l, Continuous (η i l)) (j l i : Fin n) :
    Continuous (fun w => Work.NN.Core.bmH χ η j l i w) := by
  rw [show (fun w => Work.NN.Core.bmH χ η j l i w)
      = fun w => dbarCoord i χ w * η j l w + dbarCoord j χ w * η l i w
          - dbarCoord l χ w * η j i w from by funext w; rw [bmH_eq_sum]]
  exact (((continuous_dbarCoord hχ i).mul (hηc j l)).add
    ((continuous_dbarCoord hχ j).mul (hηc l i))).sub
    ((continuous_dbarCoord hχ l).mul (hηc j i))

lemma bmH_hasCompactSupport {χ : (Fin n → ℂ) → ℂ} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hcs : HasCompactSupport χ) (j l i : Fin n) :
    HasCompactSupport (fun w => Work.NN.Core.bmH χ η j l i w) := by
  rw [show (fun w => Work.NN.Core.bmH χ η j l i w)
      = fun w => dbarCoord i χ w * η j l w + dbarCoord j χ w * η l i w
          - dbarCoord l χ w * η j i w from by funext w; rw [bmH_eq_sum]]
  exact (((hasCompactSupport_dbarCoord hcs i).mul_right).add
    ((hasCompactSupport_dbarCoord hcs j).mul_right)).sub
    ((hasCompactSupport_dbarCoord hcs l).mul_right)

/-- `bmH χ η j l i z = 0` at points where `χ ≡ 1` in a neighbourhood. -/
lemma bmH_eq_zero_of_eventuallyEq_one {χ : (Fin n → ℂ) → ℂ}
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hz : χ =ᶠ[nhds z] 1) (j l i : Fin n) :
    Work.NN.Core.bmH χ η j l i z = 0 := by
  have hf : fderiv ℝ χ z = 0 := by
    have h := hz.fderiv_eq (𝕜 := ℝ)
    simpa using h
  have h0 : ∀ a : Fin n, dbarCoord a χ z = 0 := by
    intro a; simp [dbarCoord, hf]
  rw [bmH_eq_sum, h0 i, h0 j, h0 l]
  ring

/-- The components of `bmH χ η` are `C^m` when `η` is `C^m` on `pd n ρ 4`. -/
lemma contDiff_bmH {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ} {m : ℕ} (hχ : ContDiff ℝ ∞ χ)
    (htsupp : tsupport χ ⊆ pd n ρ 4)
    (hη : ∀ i l, ContDiffOn ℝ m (η i l) (pd n ρ 4)) (j l i : Fin n) :
    ContDiff ℝ m (fun w => Work.NN.Core.bmH χ η j l i w) := by
  rw [show (fun w => Work.NN.Core.bmH χ η j l i w)
      = fun w => dbarCoord i χ w * η j l w + dbarCoord j χ w * η l i w
          - dbarCoord l χ w * η j i w from by funext w; rw [bmH_eq_sum]]
  exact (((contDiff_dbarCoord_mul hχ htsupp (hη j l) i).add
    (contDiff_dbarCoord_mul hχ htsupp (hη l i) j)).sub
    (contDiff_dbarCoord_mul hχ htsupp (hη j i) l))

/-- The Bochner–Martinelli potential of `bmH χ η` is `C^m` when `η` is `C^m` on `pd n ρ 4`. -/
lemma contDiff_bmPot_bmH (hn : 0 < n) {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ} {m : ℕ} (hχ : ContDiff ℝ ∞ χ)
    (hcs : HasCompactSupport χ) (htsupp : tsupport χ ⊆ pd n ρ 4)
    (hη : ∀ i l, ContDiffOn ℝ m (η i l) (pd n ρ 4)) (j l : Fin n) :
    ContDiff ℝ m (fun z => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) z) := by
  have hdat : ∀ i, ContDiff ℝ m (fun w => Work.NN.Core.bmH χ η j l i w) :=
    fun i => contDiff_bmH hχ htsupp hη j l i
  have hcs' : ∀ i, HasCompactSupport (fun w => Work.NN.Core.bmH χ η j l i w) :=
    fun i => bmH_hasCompactSupport hcs j l i
  have hbm : ContDiff ℝ m (Work.CR.Flat.Cauchy.bmPotential (fun i => Work.NN.Core.bmH χ η j l i)) :=
    Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport hn hdat hcs'
  have heq : (fun z => Work.CR.Flat.Cauchy.bmPotential (fun i => Work.NN.Core.bmH χ η j l i) z)
      = fun z => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) z :=
    funext fun z => Work.CR.Flat.Cauchy.bmPotential_eq_bmPot _ z
  rw [← heq]
  exact hbm

/-- `E` is `C^m` when `η` is `C^m` on `pd n ρ 4`. -/
lemma Edat_contDiff (hn : 0 < n) {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ} {m : ℕ} (hχ : ContDiff ℝ ∞ χ)
    (hcs : HasCompactSupport χ) (htsupp : tsupport χ ⊆ pd n ρ 4)
    (hη : ∀ i l, ContDiffOn ℝ m (η i l) (pd n ρ 4)) (j l : Fin n) :
    ContDiff ℝ m (Edat χ η j l) := by
  have h1 := contDiff_bmPot_bmH hn hχ hcs htsupp hη j l
  rw [show Edat χ η j l = fun z => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
      Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) z from rfl]
  exact contDiff_const.mul h1

/-- `E` is smooth when `η` is smooth on `pd n ρ 4`. -/
lemma Edat_smooth (hn : 0 < n) {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ ∞ χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ pd n ρ 4)
    (hη : ∀ i l, ContDiffOn ℝ (⊤ : ℕ∞) (η i l) (pd n ρ 4)) (j l : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (Edat χ η j l) := by
  rw [contDiff_infty]
  intro m
  exact Edat_contDiff hn hχ hcs htsupp (fun i l => (hη i l).of_le (by simp)) j l

/-- The bound for `E` (`bmPot_bmH_holderNorm_le`, transferred to the notation of this file). -/
lemma Edat_bound (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (htsupp : tsupport χ ⊆ pd n ρ 3) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
      (∀ i l, ContDiffOn ℝ (k + 1) (η i l) (pd n ρ 4)) → ∀ j l : Fin n,
        holderNorm (k + 1) α (Edat χ η j l) (pd n ρ (8/3 : ℝ))
          ≤ ENNReal.ofReal C * ∑ r : Fin n, ∑ s : Fin n,
              holderNorm k α (η r s) (pd n ρ 4) := by
  obtain ⟨C, hC0, hC⟩ := Work.NN.Final.bmPot_bmH_holderNorm_le (n := n) hn hα0 hα1 hρ
    (fun m => hχ.of_le (by simp)) htsupp k
  exact ⟨C, hC0, fun η hη j l => hC η hη j l⟩

lemma contDiff_bmH_zero {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hχ4 : tsupport χ ⊆ pd n ρ 4) (hη : ∀ i l, ContinuousOn (η i l) (pd n ρ 4))
    (j l i : Fin n) : Continuous (fun w => Work.NN.Core.bmH χ η j l i w) := by
  have h0 : ∀ a b : Fin n, ContDiffOn ℝ 0 (η a b) (pd n ρ 4) :=
    fun a b => by simpa using hη a b
  have h1 : ContDiff ℝ 0 (fun w => dbarCoord i χ w * η j l w) :=
    contDiff_dbarCoord_mul hχ hχ4 (h0 j l) i
  have h2 : ContDiff ℝ 0 (fun w => dbarCoord j χ w * η l i w) :=
    contDiff_dbarCoord_mul hχ hχ4 (h0 l i) j
  have h3 : ContDiff ℝ 0 (fun w => dbarCoord l χ w * η j i w) :=
    contDiff_dbarCoord_mul hχ hχ4 (h0 j i) l
  rw [show (fun w => Work.NN.Core.bmH χ η j l i w)
      = fun w => dbarCoord i χ w * η j l w + dbarCoord j χ w * η l i w
          - dbarCoord l χ w * η j i w from by funext w; rw [bmH_eq_sum]]
  exact contDiff_zero.mp ((h1.add h2).sub h3)

/-- Additivity of `bmPot` in the family. -/
lemma bmPot_add {n : ℕ} (hn : 0 < n) {f g : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, Continuous (f j)) (hg : ∀ j, Continuous (g j))
    (hfs : ∀ j, HasCompactSupport (f j)) (hgs : ∀ j, HasCompactSupport (g j)) :
    (fun z => Work.CR.Flat.Cauchy.bmPot (fun j => fun y => f j y + g j y) z)
      = (fun z => Work.CR.Flat.Cauchy.bmPot f z) + fun z => Work.CR.Flat.Cauchy.bmPot g z := by
  funext z
  have h := bmPot_linear (n := n) hn (1 : ℂ) (1 : ℂ) hf hg hfs hgs z
  have h1 : (fun j => fun y => (1 : ℂ) * f j y + (1 : ℂ) * g j y)
      = (fun j => fun y => f j y + g j y) := by
    funext j y; ring
  rw [h1] at h
  simpa using h

/-- `ℝ`-homogeneity of `bmPot` in the family. -/
lemma bmPot_real_smul {n : ℕ} (hn : 0 < n) (c : ℝ) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, Continuous (f j)) (hfs : ∀ j, HasCompactSupport (f j)) :
    (fun z => Work.CR.Flat.Cauchy.bmPot (fun j => fun y => (c : ℂ) * f j y) z)
      = c • (fun z => Work.CR.Flat.Cauchy.bmPot f z) := by
  funext z
  have h := bmPot_linear (n := n) hn ((c : ℂ)) (0 : ℂ) hf hf hfs hfs z
  have h1 : (fun j => fun y => (c : ℂ) * f j y + (0 : ℂ) * f j y)
      = (fun j => fun y => (c : ℂ) * f j y) := by
    funext j y; ring
  rw [h1] at h
  simp only [zero_mul, add_zero, Pi.smul_apply, Complex.real_smul] at h ⊢
  exact h

/-- `E` is antisymmetric when `η` is. -/
lemma Edat_antisymm (hn : 0 < n) {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ ∞ χ) (hcs : HasCompactSupport χ)
    (hχ4 : tsupport χ ⊆ pd n ρ 4)
    (hηc : ∀ i l, ContinuousOn (η i l) (pd n ρ 4)) (hanti : ∀ i l z, η i l z = - η l i z)
    (j l : Fin n) (z : Fin n → ℂ) :
    Edat χ η j l z = - Edat χ η l j z := by
  have hlin := bmPot_linear (n := n) hn (-1) 0 (f := fun i => fun w => Work.NN.Core.bmH χ η l j i w)
    (g := fun i => fun w => Work.NN.Core.bmH χ η l j i w)
    (fun i => contDiff_bmH_zero hχ hχ4 hηc l j i) (fun i => contDiff_bmH_zero hχ hχ4 hηc l j i)
    (fun i => bmH_hasCompactSupport hcs l j i) (fun i => bmH_hasCompactSupport hcs l j i)
  have hfun : (fun i => fun w => Work.NN.Core.bmH χ η j l i w)
      = fun i => fun w => (-1 : ℂ) * Work.NN.Core.bmH χ η l j i w
          + 0 * Work.NN.Core.bmH χ η l j i w := by
    funext i w
    rw [bmH_antisymm hanti j l i w]
    ring
  rw [Edat_apply, Edat_apply, hfun]
  rw [hlin z]
  simp only [zero_mul, add_zero]
  ring

/-- `E` is `∂̄`-closed at the points where `χ` is identically `1` in a neighbourhood. -/
lemma Edat_closed (hn : 0 < n) {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcs : HasCompactSupport χ) (htsupp : tsupport χ ⊆ pd n ρ 4)
    (hη : ∀ i l, ContDiff ℝ 1 (η i l))
    (hcl : ∀ j l m z, z ∈ pd n ρ 4 →
      dbarCoord j (η l m) z - dbarCoord l (η j m) z + dbarCoord m (η j l) z = 0)
    (j l m : Fin n) {z : Fin n → ℂ} (hz : χ =ᶠ[nhds z] 1) :
    dbarCoord j (Edat χ η l m) z - dbarCoord l (Edat χ η j m) z
      + dbarCoord m (Edat χ η j l) z = 0 := by
  have h2 : ContDiff ℝ 2 χ := (hχ.of_le (by simp))
  have hmain := Work.NN.Final.bmPot_bmH_dbarCoord_eq (n := n) hn h2 hcs (isOpen_pd ρ 4) htsupp hη
    (fun j l m z hz' => hcl j l m z hz') j l m z
  have hzero : Work.NN.Core.bmH χ η j l m z = 0 := bmH_eq_zero_of_eventuallyEq_one hz j l m
  rw [hzero, mul_zero] at hmain
  have hd : ∀ a b : Fin n,
      DifferentiableAt ℝ (fun w => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η a b i) w) z :=
    fun a b => ((contDiff_bmPot_bmH hn hχ hcs htsupp (fun i l => (hη i l).contDiffOn) a b).differentiable
      one_ne_zero).differentiableAt
  rw [show Edat χ η l m = fun w => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
        Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η l m i) w from rfl,
      show Edat χ η j m = fun w => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
        Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j m i) w from rfl,
      show Edat χ η j l = fun w => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
        Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) w from rfl]
  rw [dbarCoord_const_mul (j := j) _ _ z (hd l m), dbarCoord_const_mul (j := l) _ _ z (hd j m),
    dbarCoord_const_mul (j := m) _ _ z (hd j l)]
  linear_combination ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹) * hmain


/-- `bmH χ η` is additive in `η`. -/
lemma bmH_add (χ : (Fin n → ℂ) → ℂ) (η η' : Fin n → Fin n → (Fin n → ℂ) → ℂ)
    (j l i : Fin n) (w : Fin n → ℂ) :
    Work.NN.Core.bmH χ (η + η') j l i w
      = Work.NN.Core.bmH χ η j l i w + Work.NN.Core.bmH χ η' j l i w := by
  rw [bmH_eq_sum, bmH_eq_sum, bmH_eq_sum]
  simp only [Pi.add_apply]
  ring

/-- `bmH χ η` is `ℝ`-homogeneous in `η`. -/
lemma bmH_smul (χ : (Fin n → ℂ) → ℂ) (c : ℝ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ)
    (j l i : Fin n) (w : Fin n → ℂ) :
    Work.NN.Core.bmH χ (c • η) j l i w = c • Work.NN.Core.bmH χ η j l i w := by
  rw [bmH_eq_sum, bmH_eq_sum]
  simp only [Pi.smul_apply, Complex.real_smul]
  ring

/-- Additivity of `bmPot (bmH χ ·)` in the datum. -/
lemma bmPot_bmH_add (hn : 0 < n) {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcs : HasCompactSupport χ) (hχ4 : tsupport χ ⊆ pd n ρ 4)
    {η η' : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ j l, ContinuousOn (η j l) (pd n ρ 4))
    (hη' : ∀ j l, ContinuousOn (η' j l) (pd n ρ 4)) (i l : Fin n) :
    (fun z => Work.CR.Flat.Cauchy.bmPot (fun m => Work.NN.Core.bmH χ (η + η') i l m) z)
      = (fun z => Work.CR.Flat.Cauchy.bmPot (fun m => Work.NN.Core.bmH χ η i l m) z)
        + (fun z => Work.CR.Flat.Cauchy.bmPot (fun m => Work.NN.Core.bmH χ η' i l m) z) := by
  have hc : ∀ (θ : Fin n → Fin n → (Fin n → ℂ) → ℂ), (∀ j l, ContinuousOn (θ j l) (pd n ρ 4)) →
      ∀ m, Continuous (fun w => Work.NN.Core.bmH χ θ i l m w) :=
    fun θ hθ m => contDiff_bmH_zero hχ hχ4 hθ i l m
  have hs : ∀ (θ : Fin n → Fin n → (Fin n → ℂ) → ℂ), ∀ m,
      HasCompactSupport (fun w => Work.NN.Core.bmH χ θ i l m w) :=
    fun θ m => bmH_hasCompactSupport hcs i l m
  have hL : (fun z => Work.CR.Flat.Cauchy.bmPot (fun m => Work.NN.Core.bmH χ (η + η') i l m) z)
      = fun z => Work.CR.Flat.Cauchy.bmPot (fun m => fun y =>
          Work.NN.Core.bmH χ η i l m y + Work.NN.Core.bmH χ η' i l m y) z := by
    funext z
    congr 1
    funext m w
    exact bmH_add χ η η' i l m w
  rw [hL]
  exact bmPot_add hn (hc η hη) (hc η' hη') (hs η) (hs η')

/-- `ℝ`-homogeneity of `bmPot (bmH χ ·)` in the datum. -/
lemma bmPot_bmH_smul (hn : 0 < n) {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcs : HasCompactSupport χ) (hχ4 : tsupport χ ⊆ pd n ρ 4)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ j l, ContinuousOn (η j l) (pd n ρ 4)) (c : ℝ) (i l : Fin n) :
    (fun z => Work.CR.Flat.Cauchy.bmPot (fun m => Work.NN.Core.bmH χ (c • η) i l m) z)
      = c • (fun z => Work.CR.Flat.Cauchy.bmPot (fun m => Work.NN.Core.bmH χ η i l m) z) := by
  have hc : ∀ m, Continuous (fun w => Work.NN.Core.bmH χ η i l m w) :=
    fun m => contDiff_bmH_zero hχ hχ4 hη i l m
  have hs : ∀ m, HasCompactSupport (fun w => Work.NN.Core.bmH χ η i l m w) :=
    fun m => bmH_hasCompactSupport hcs i l m
  have hL : (fun z => Work.CR.Flat.Cauchy.bmPot (fun m => Work.NN.Core.bmH χ (c • η) i l m) z)
      = fun z => Work.CR.Flat.Cauchy.bmPot (fun m => fun y =>
          (c : ℂ) * Work.NN.Core.bmH χ η i l m y) z := by
    funext z
    congr 1
    funext m w
    rw [bmH_smul χ c η i l m w, Complex.real_smul]
  rw [hL]
  exact bmPot_real_smul hn c hc hs

/-- `E` is additive in the datum. -/
lemma Edat_add (hn : 0 < n) {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcs : HasCompactSupport χ) (hχ4 : tsupport χ ⊆ pd n ρ 4)
    {η η' : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ j l, ContinuousOn (η j l) (pd n ρ 4))
    (hη' : ∀ j l, ContinuousOn (η' j l) (pd n ρ 4)) :
    Edat χ (η + η') = Edat χ η + Edat χ η' := by
  funext j l z
  have h := congrFun (bmPot_bmH_add hn hχ hcs hχ4 hη hη' j l) z
  simp only [Edat_apply, Pi.add_apply, h]
  ring

/-- `E` is `ℝ`-homogeneous in the datum. -/
lemma Edat_smul (hn : 0 < n) {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcs : HasCompactSupport χ) (hχ4 : tsupport χ ⊆ pd n ρ 4)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ j l, ContinuousOn (η j l) (pd n ρ 4)) (c : ℝ) :
    Edat χ (c • η) = c • Edat χ η := by
  funext j l z
  have h := congrFun (bmPot_bmH_smul hn hχ hcs hχ4 hη c j l) z
  simp only [Edat_apply, Pi.smul_apply, h, Complex.real_smul]
  ring


/-- Additivity of `bmPot (bmH χ ·)` in the datum (continuity form). -/
lemma bmPot_bmH_add' (hn : 0 < n) {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcs : HasCompactSupport χ) (hχ4 : tsupport χ ⊆ pd n ρ 4)
    {η η' : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ j l, ContinuousOn (η j l) (pd n ρ 4))
    (hη' : ∀ j l, ContinuousOn (η' j l) (pd n ρ 4)) (i l : Fin n) :
    (fun z => Work.CR.Flat.Cauchy.bmPot (fun m => Work.NN.Core.bmH χ (η + η') i l m) z)
      = (fun z => Work.CR.Flat.Cauchy.bmPot (fun m => Work.NN.Core.bmH χ η i l m) z)
        + (fun z => Work.CR.Flat.Cauchy.bmPot (fun m => Work.NN.Core.bmH χ η' i l m) z) :=
  bmPot_bmH_add hn hχ hcs hχ4 hη hη' i l

/-! ## The solution operator -/

/-- Data which are continuous on `pd n ρ 4`. -/
def contPd (n : ℕ) (ρ : Fin n → ℝ) : Submodule ℝ (Fin n → Fin n → (Fin n → ℂ) → ℂ) where
  carrier := {η | ∀ j l, ContinuousOn (η j l) (pd n ρ 4)}
  zero_mem' := fun j l => continuousOn_const
  add_mem' := fun hf hg j l => (hf j l).add (hg j l)
  smul_mem' := fun c f hf j l => (hf j l).const_smul c

/-- The product of a smooth function supported in `pd n ρ 4` with a function continuous there is
globally continuous. -/
lemma continuous_mul_of_contOn {ρ : Fin n → ℝ} {χ η : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hχ4 : tsupport χ ⊆ pd n ρ 4) (hη : ContinuousOn η (pd n ρ 4)) :
    Continuous (fun w => χ w * η w) :=
  contDiff_zero.mp (contDiff_mul_of_contDiffOn_tsupp (isOpen_pd ρ 4) hχ hχ4 (by simpa using hη))

/-- Additivity of the Bochner–Martinelli part in the datum. -/
lemma bmRow_add (hn : 0 < n) {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcs : HasCompactSupport χ) (hχ4 : tsupport χ ⊆ pd n ρ 4)
    {η η' : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ j l, ContinuousOn (η j l) (pd n ρ 4))
    (hη' : ∀ j l, ContinuousOn (η' j l) (pd n ρ 4)) :
    Work.NN.Core.bmRow (fun a b w => χ w * (η + η') a b w)
      = Work.NN.Core.bmRow (fun a b w => χ w * η a b w)
        + Work.NN.Core.bmRow (fun a b w => χ w * η' a b w) := by
  funext i z
  have hfam : (fun l => fun w => χ w * (η i l w + η' i l w))
      = fun l => fun w => χ w * η i l w + χ w * η' i l w := by
    funext l w
    ring
  have hpot := congrFun (bmPot_add hn
    (f := fun l => fun w => χ w * η i l w) (g := fun l => fun w => χ w * η' i l w)
    (fun l => continuous_mul_of_contOn hχ hχ4 (hη i l))
    (fun l => continuous_mul_of_contOn hχ hχ4 (hη' i l))
    (fun l => hcs.mul_right) (fun l => hcs.mul_right)) z
  simp only [Work.NN.Core.bmRow_apply, Pi.add_apply]
  rw [hfam, hpot]
  simp only [Pi.add_apply]
  ring

/-- `ℝ`-homogeneity of the Bochner–Martinelli part in the datum. -/
lemma bmRow_smul (hn : 0 < n) {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcs : HasCompactSupport χ) (hχ4 : tsupport χ ⊆ pd n ρ 4)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ j l, ContinuousOn (η j l) (pd n ρ 4)) (c : ℝ) :
    Work.NN.Core.bmRow (fun a b w => χ w * (c • η) a b w)
      = c • Work.NN.Core.bmRow (fun a b w => χ w * η a b w) := by
  funext i z
  have hfam : (fun l => fun w => χ w * (c • η i l w))
      = fun l => fun w => (c : ℂ) * (χ w * η i l w) := by
    funext l w
    rw [Complex.real_smul]
    ring
  have hpot := congrFun (bmPot_real_smul hn c
    (f := fun l => fun w => χ w * η i l w)
    (fun l => continuous_mul_of_contOn hχ hχ4 (hη i l))
    (fun l => hcs.mul_right)) z
  simp only [Work.NN.Core.bmRow_apply, Pi.smul_apply]
  rw [hfam, hpot]
  simp only [Pi.smul_apply, Complex.real_smul]
  ring

/-- The `(0,2)`-solution operator on data continuous on `pd n ρ 4`. -/
noncomputable def T2lin (hn : 0 < n) {ρ : Fin n → ℝ} (χ : (Fin n → ℂ) → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hcs : HasCompactSupport χ) (hχ4 : tsupport χ ⊆ pd n ρ 4) :
    contPd n ρ →ₗ[ℝ] (Fin n → (Fin n → ℂ) → ℂ) where
  toFun := fun η => Work.NN.Core.bmRow (fun a b w => χ w * η.1 a b w) + tfin ρ (Edat χ η.1)
  map_add' := by
    intro η η'
    have h1 : (η + η').1 = η.1 + η'.1 := rfl
    rw [h1, bmRow_add hn hχ hcs hχ4 η.2 η'.2, Edat_add hn hχ hcs hχ4 η.2 η'.2, tfin_add]
    abel
  map_smul' := by
    intro c η
    have h1 : (c • η).1 = c • η.1 := rfl
    rw [h1, bmRow_smul hn hχ hcs hχ4 η.2 c, Edat_smul hn hχ hcs hχ4 η.2 c, tfin_smul]
    rw [smul_add]
    abel

/-- The `(0,2)`-solution operator, extended linearly to all data. -/
noncomputable def T2 (hn : 0 < n) {ρ : Fin n → ℝ} (χ : (Fin n → ℂ) → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hcs : HasCompactSupport χ) (hχ4 : tsupport χ ⊆ pd n ρ 4) :
    (Fin n → Fin n → (Fin n → ℂ) → ℂ) →ₗ[ℝ] (Fin n → (Fin n → ℂ) → ℂ) :=
  Classical.choose (LinearMap.exists_extend (T2lin hn χ hχ hcs hχ4))

lemma T2_apply (hn : 0 < n) {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ} {hχ : ContDiff ℝ ∞ χ}
    {hcs : HasCompactSupport χ} {hχ4 : tsupport χ ⊆ pd n ρ 4}
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ} (hη : η ∈ contPd n ρ) :
    T2 hn χ hχ hcs hχ4 η = T2lin hn χ hχ hcs hχ4 ⟨η, hη⟩ := by
  have h := Classical.choose_spec (LinearMap.exists_extend (T2lin hn χ hχ hcs hχ4))
  exact congrFun (congrArg DFunLike.coe h) ⟨η, hη⟩


/-! ## Differentiability and smoothness helpers -/

/-- The Bochner–Martinelli potential of `C¹` compactly supported data is differentiable. -/
lemma differentiableAt_bmPot (hn : 0 < n) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ 1 (f j)) (hfs : ∀ j, HasCompactSupport (f j)) (z : Fin n → ℂ) :
    DifferentiableAt ℝ (fun y => Work.CR.Flat.Cauchy.bmPot f y) z := by
  have hc : ContDiff ℝ 1 (Work.CR.Flat.Cauchy.bmPotential f) :=
    Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport hn hf hfs
  have hfun : (fun y => Work.CR.Flat.Cauchy.bmPot f y)
      = fun y => Work.CR.Flat.Cauchy.bmPotential f y :=
    funext fun y => (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot f y).symm
  rw [hfun]
  exact (hc.differentiable one_ne_zero).differentiableAt

/-- The Bochner–Martinelli potential of `C^m` compactly supported data is `C^m`. -/
lemma contDiff_bmPot {m : ℕ} (hn : 0 < n) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ m (f j)) (hfs : ∀ j, HasCompactSupport (f j)) :
    ContDiff ℝ m (fun y => Work.CR.Flat.Cauchy.bmPot f y) := by
  have hc := Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport hn hf hfs
  have hfun : (fun y => Work.CR.Flat.Cauchy.bmPot f y)
      = fun y => Work.CR.Flat.Cauchy.bmPotential f y :=
    funext fun y => (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot f y).symm
  rwa [hfun]

/-- `bmRow` of `C^m` compactly supported data is `C^m`. -/
lemma contDiff_bmRow {m : ℕ} (hn : 0 < n) {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ m (η i l)) (hcs : ∀ i l, HasCompactSupport (η i l)) (i : Fin n) :
    ContDiff ℝ m (Work.NN.Core.bmRow η i) := by
  rw [show Work.NN.Core.bmRow η i = fun z => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹) *
      Work.CR.Flat.Cauchy.bmPot (fun l => η i l) z from rfl]
  exact contDiff_const.mul (contDiff_bmPot hn (fun l => hη i l) (fun l => hcs i l))

/-- `bmRow` of `C¹` compactly supported data is differentiable. -/
lemma differentiableAt_bmRow (hn : 0 < n) {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ 1 (η i l)) (hcs : ∀ i l, HasCompactSupport (η i l))
    (i : Fin n) (z : Fin n → ℂ) : DifferentiableAt ℝ (Work.NN.Core.bmRow η i) z := by
  rw [show Work.NN.Core.bmRow η i = fun z => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹) *
      Work.CR.Flat.Cauchy.bmPot (fun l => η i l) z from rfl]
  exact (differentiableAt_const _).mul
    (differentiableAt_bmPot hn (fun l => hη i l) (fun l => hcs i l) z)

/-- Additivity of `∂̄_j` for sums of functions. -/
lemma dbarCoord_add_pi (j : Fin n) {f g : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbarCoord j (f + g) z = dbarCoord j f z + dbarCoord j g z := by
  rw [show (f + g) = fun w => f w + g w from rfl]
  exact Work.CR.Flat.Polydisc.dbarCoord_add j f g z hf hg

/-! ## The error term `E` is `∂̄`-closed on the inner polydisc -/

/-- `E = γ⁻¹ bmPot (bmH χ η)` is `∂̄`-closed on `polydisc 0 (sgm ρ) = pd n ρ (8/3)` when `η` is
`C¹` and closed on `pd n ρ 4`.  Every term vanishes because `bmH χ η` vanishes at the points where
`χ ≡ 1` in a neighbourhood, which is the form of the local `(0,3)`-identity
`Work.NN.Final.bmPot_bmH_dbarCoord_eq_local`. -/
lemma Edat_closed_ball (hn : 0 < n) {ρ : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ} {V : Set (Fin n → ℂ)}
    (hχ : ContDiff ℝ ∞ χ) (hcs : HasCompactSupport χ) (htsupp : tsupport χ ⊆ pd n ρ 4)
    (hVo : IsOpen V) (hVmem : ∀ z, z ∈ pd n ρ (8/3 : ℝ) → z ∈ V)
    (hχ1 : ∀ y ∈ V, χ y = 1)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiffOn ℝ 1 (η i l) (pd n ρ 4))
    (hcl : ∀ j l m z, z ∈ pd n ρ 4 →
      dbarCoord j (η l m) z - dbarCoord l (η j m) z + dbarCoord m (η j l) z = 0) :
    ∀ i m m' z', z' ∈ polydisc 0 (sgm ρ) →
      dbarCoord i (Edat χ η m m') z' - dbarCoord m (Edat χ η i m') z'
        + dbarCoord m' (Edat χ η i m) z' = 0 := by
  intro i m m' z' hz'
  have hz8 : z' ∈ pd n ρ (8/3 : ℝ) := hz'
  have hzne : χ =ᶠ[nhds z'] 1 := by
    filter_upwards [hVo.mem_nhds (hVmem z' hz8)] with y hy
    exact hχ1 y hy
  have hH0 : Work.NN.Core.bmH χ η i m m' z' = 0 :=
    bmH_eq_zero_of_eventuallyEq_one hzne i m m'
  have hd : ∀ a b : Fin n, DifferentiableAt ℝ
      (fun z => Work.CR.Flat.Cauchy.bmPot (fun l => Work.NN.Core.bmH χ η a b l) z) z' :=
    fun a b => ((contDiff_bmPot_bmH hn hχ hcs htsupp hη a b).differentiable one_ne_zero).differentiableAt
  have h1 : dbarCoord i (Edat χ η m m') z'
      = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * dbarCoord i
          (fun z => Work.CR.Flat.Cauchy.bmPot (fun l => Work.NN.Core.bmH χ η m m' l) z) z' :=
    dbarCoord_const_mul (j := i) ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
      (fun z => Work.CR.Flat.Cauchy.bmPot (fun l => Work.NN.Core.bmH χ η m m' l) z) z' (hd m m')
  have h2 : dbarCoord m (Edat χ η i m') z'
      = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * dbarCoord m
          (fun z => Work.CR.Flat.Cauchy.bmPot (fun l => Work.NN.Core.bmH χ η i m' l) z) z' :=
    dbarCoord_const_mul (j := m) ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
      (fun z => Work.CR.Flat.Cauchy.bmPot (fun l => Work.NN.Core.bmH χ η i m' l) z) z' (hd i m')
  have h3 : dbarCoord m' (Edat χ η i m) z'
      = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * dbarCoord m'
          (fun z => Work.CR.Flat.Cauchy.bmPot (fun l => Work.NN.Core.bmH χ η i m l) z) z' :=
    dbarCoord_const_mul (j := m') ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
      (fun z => Work.CR.Flat.Cauchy.bmPot (fun l => Work.NN.Core.bmH χ η i m l) z) z' (hd i m)
  have hthree := Work.NN.Final.bmPot_bmH_dbarCoord_eq_local (n := n) hn (hχ.of_le (by simp)) hcs
      (isOpen_pd ρ 4) htsupp hη hcl i m m' z'
  have key : dbarCoord i (fun z => Work.CR.Flat.Cauchy.bmPot
        (fun l => Work.NN.Core.bmH χ η m m' l) z) z'
      - dbarCoord m (fun z => Work.CR.Flat.Cauchy.bmPot
        (fun l => Work.NN.Core.bmH χ η i m' l) z) z'
      + dbarCoord m' (fun z => Work.CR.Flat.Cauchy.bmPot
        (fun l => Work.NN.Core.bmH χ η i m l) z) z' = 0 := by
    rw [hthree, hH0, mul_zero]
  rw [h1, h2, h3]
  linear_combination ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹) * key

/-- The transferred solver is `C^m` on globally `C^m` data. -/
lemma contDiff_tfin {ρ : Fin n → ℝ} {ζ : Fin n → Fin n → (Fin n → ℂ) → ℂ} {m : ℕ}
    (hζ : ∀ i l, ContDiff ℝ m (ζ i l)) (j : Fin n) : ContDiff ℝ m (tfin ρ ζ j) := by
  have h1 : ContDiff ℝ m (uS2 (gmap ρ ζ) j) := contDiff_uS2_gmap hζ j
  have h2 : ContDiff ℝ m (fun z => uS2 (gmap ρ ζ) j (sInv ρ z)) :=
    h1.comp (contDiff_sInv ρ (m : ℕ∞))
  exact contDiff_const.mul h2

/-- **The `(0,2)`-defect identity of one Bochner–Martinelli step** with the datum assumed `C¹` only
on the polydisc `pd n ρ 4` (rather than globally).  The datum is globalised by a smooth bump which
is `1` on a neighbourhood of `pd n ρ 2 ∪ tsupport χ` and is supported in `pd n ρ 4`. -/
lemma bmDefect_eq_contOn {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hn : 0 < n)
    {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ ∞ χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ pd n ρ 4)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiffOn ℝ 1 (η i l) (pd n ρ 4))
    (hcl : ∀ j l m z, z ∈ pd n ρ 4 →
      dbarCoord j (η l m) z - dbarCoord l (η j m) z + dbarCoord m (η j l) z = 0) :
    ∀ j l z, z ∈ pd n ρ 2 →
      dbarCoord j (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) l) z
        - dbarCoord l (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) z
      = η j l z + Work.NN.Core.bmDefect χ η j l z := by
  have hK'c : IsCompact (tsupport χ ∪ Set.univ.pi
      fun i => Metric.closedBall (0 : ℂ) ((3 : ℝ) * ρ i)) :=
    hcs.isCompact.union (isCompact_univ_pi fun i => isCompact_closedBall 0 _)
  have hK'4 : (tsupport χ ∪ Set.univ.pi fun i => Metric.closedBall (0 : ℂ) ((3 : ℝ) * ρ i))
      ⊆ pd n ρ 4 := by
    intro z hz
    rcases hz with hz | hz
    · exact htsupp hz
    · rw [mem_pd]
      intro i
      have h2 : ‖z i‖ ≤ 3 * ρ i := by simpa using hz i
      have h3 : (3 : ℝ) * ρ i < 4 * ρ i := by linarith [hρ i]
      linarith
  have h2K' : pd n ρ 2 ⊆ tsupport χ ∪ Set.univ.pi
      fun i => Metric.closedBall (0 : ℂ) ((3 : ℝ) * ρ i) := by
    intro z hz
    refine Or.inr (Set.mem_univ_pi.mpr fun i => ?_)
    have h1 : ‖z i‖ < 2 * ρ i := by simpa using hz i
    have h3 : (2 : ℝ) * ρ i ≤ 3 * ρ i := by linarith [hρ i]
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact le_trans (le_of_lt h1) h3
  obtain ⟨χ₂, W, hχ₂, _hcs₂, htsupp₂, hWo, hKW, hχ₂1⟩ :=
    Work.NN.Core.exists_contDiff_bump_of_isCompact_subset hK'c (isOpen_pd ρ 4) hK'4
  have hWK : tsupport χ ⊆ W := fun z hz => hKW (Or.inl hz)
  have hW2 : ∀ z, z ∈ pd n ρ 2 → z ∈ W := fun z hz => hKW (h2K' hz)
  have hUopen : IsOpen (W ∩ pd n ρ 4) := hWo.inter (isOpen_pd ρ 4)
  have hχU : ∀ z, χ z ≠ 0 → z ∈ W ∩ pd n ρ 4 := fun z hz =>
    ⟨hWK (subset_tsupport χ (Function.mem_support.mpr hz)),
      htsupp (subset_tsupport χ (Function.mem_support.mpr hz))⟩
  set η₂ : Fin n → Fin n → (Fin n → ℂ) → ℂ := fun i l w => χ₂ w * η i l w with hη₂def
  have hη₂diff : ∀ i l, ContDiff ℝ 1 (η₂ i l) := fun i l =>
    contDiff_mul_of_contDiffOn_tsupp (isOpen_pd ρ 4) hχ₂ htsupp₂ (hη i l)
  have hη₂closed : ∀ j l m z, z ∈ W ∩ pd n ρ 4 →
      dbarCoord j (η₂ l m) z - dbarCoord l (η₂ j m) z + dbarCoord m (η₂ j l) z = 0 := by
    intro j l m z hz
    have hder : ∀ a b : Fin n,
        fderiv ℝ (fun w => χ₂ w * η a b w) z = fderiv ℝ (η a b) z := by
      intro a b
      have h1 : (fun w => χ₂ w * η a b w) =ᶠ[nhds z] η a b := by
        filter_upwards [hWo.mem_nhds hz.1] with w hw
        rw [hχ₂1 w hw, one_mul]
      exact h1.fderiv_eq
    have e1 : dbarCoord j (η₂ l m) z = dbarCoord j (η l m) z := by
      simp only [hη₂def, dbarCoord, hder l m]
    have e2 : dbarCoord l (η₂ j m) z = dbarCoord l (η j m) z := by
      simp only [hη₂def, dbarCoord, hder j m]
    have e3 : dbarCoord m (η₂ j l) z = dbarCoord m (η j l) z := by
      simp only [hη₂def, dbarCoord, hder j l]
    rw [e1, e2, e3]
    exact hcl j l m z hz.2
  obtain ⟨R, hRpos, hR⟩ := hcs.isCompact.isBounded.exists_pos_norm_le
  have hgl := Work.NN.Final.bmDefect_eq_local (n := n) hn (R := R + 1) (by linarith)
    (U := W ∩ pd n ρ 4) hUopen χ (hχ.of_le (by simp))
    (fun z hz => by
      by_contra hc
      have hmem : z ∈ tsupport χ := subset_tsupport χ (Function.mem_support.mpr hc)
      linarith [hR z hmem])
    hχU η₂ hη₂diff hη₂closed
  have hprod : ∀ i l' : Fin n, (fun w => χ w * η₂ i l' w) = fun w => χ w * η i l' w := by
    intro i l'
    funext w
    by_cases hc : χ w = 0
    · rw [hc, zero_mul, zero_mul]
    · have hmem : w ∈ tsupport χ := subset_tsupport χ (Function.mem_support.mpr hc)
      simp only [hη₂def]
      rw [hχ₂1 w (hWK hmem), one_mul]
  have hH : ∀ i l' m' w, Work.NN.Core.bmH χ η₂ i l' m' w = Work.NN.Core.bmH χ η i l' m' w := by
    intro i l' m' w
    by_cases hw : w ∈ tsupport χ
    · simp only [Work.NN.Core.bmH, hη₂def]
      rw [hχ₂1 w (hWK hw)]
      ring
    · have h0 : χ =ᶠ[nhds w] 0 := by
        filter_upwards [(isClosed_tsupport χ).compl_mem_nhds hw] with y hy
        exact Function.notMem_support.mp fun hy' => hy (subset_tsupport χ hy')
      have hfd : fderiv ℝ χ w = 0 := by
        have h := h0.fderiv_eq (𝕜 := ℝ)
        simpa using h
      have hdb : ∀ a : Fin n, dbarCoord a χ w = 0 := fun a => by simp [dbarCoord, hfd]
      simp only [Work.NN.Core.bmH, hdb m', hdb i, hdb l']
      ring
  have hrow : ∀ i : Fin n, Work.NN.Core.bmRow (fun a b w => χ w * η₂ a b w) i
      = Work.NN.Core.bmRow (fun a b w => χ w * η a b w) i := by
    intro i
    have hfg : (fun a b w => χ w * η₂ a b w) = fun a b w => χ w * η a b w := by
      funext a b w
      exact congrFun (hprod a b) w
    rw [hfg]
  intro j l z hz
  have hχ₂z : χ₂ z = 1 := hχ₂1 z (hW2 z hz)
  have hzj : η₂ j l z = η j l z := by simp only [hη₂def]; rw [hχ₂z, one_mul]
  have hdefz : Work.NN.Core.bmDefect χ η₂ j l z = Work.NN.Core.bmDefect χ η j l z := by
    rw [Work.NN.Core.bmDefect_apply, Work.NN.Core.bmDefect_apply]
    have hF : (fun m' => Work.NN.Core.bmH χ η₂ j l m') = fun m' => Work.NN.Core.bmH χ η j l m' := by
      funext m' w
      exact hH j l m' w
    rw [hzj, hF]
  have hj := hgl j l z
  rw [hrow j, hrow l] at hj
  rw [hj, hzj, hdefz]

/-- The sum of a constant over the double index `Fin n × Fin n` is bounded by
`((n+1)^2)` times the constant. -/
lemma sum_sum_const_fin_le (n : ℕ) (x : ℝ≥0∞) :
    (∑ _i : Fin n, ∑ _l : Fin n, x)
      ≤ ENNReal.ofReal (((n : ℝ) + 1) * ((n : ℝ) + 1)) * x := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcast : ((n : ℝ≥0∞) * (n : ℝ≥0∞)) = ENNReal.ofReal ((n : ℝ) * (n : ℝ)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  calc ((n : ℝ≥0∞) * ((n : ℝ≥0∞) * x))
      = ((n : ℝ≥0∞) * (n : ℝ≥0∞)) * x := by rw [mul_assoc]
    _ = ENNReal.ofReal ((n : ℝ) * (n : ℝ)) * x := by rw [hcast]
    _ ≤ ENNReal.ofReal (((n : ℝ) + 1) * ((n : ℝ) + 1)) * x :=
        mul_le_mul_of_nonneg_right
          (ENNReal.ofReal_le_ofReal (by
            have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
            nlinarith))
          (zero_le : (0 : ℝ≥0∞) ≤ x)

/-! ## The main result -/

set_option maxHeartbeats 1000000 in
/-- **The flat `(0,2)`-Poincaré operator on nested polydiscs, with the full `C^{k,α}` gain.** -/
theorem twoCoreAux {n : ℕ} {α : ℝ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hα0 : 0 < α)
    (hα1 : α < 1) :
    ∃ (T2 : (Fin n → Fin n → (Fin n → ℂ) → ℂ) →ₗ[ℝ] (Fin n → (Fin n → ℂ) → ℂ))
      (C2 : ℕ → ℝ), (∀ k, 0 < C2 k) ∧
      (∀ η, (∀ j l, ContDiffOn ℝ (1 : ℕ∞) (η j l) (pd n ρ 4)) →
        (∀ j l z, η j l z = - η l j z) → Clos2 n ρ 4 η →
        ∀ j l z, z ∈ pd n ρ 2 →
          dbarCoord j (T2 η l) z - dbarCoord l (T2 η j) z = η j l z) ∧
      (∀ (k : ℕ) (η), (∀ j l, ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) (η j l) (pd n ρ 4)) →
        (∀ j l z, η j l z = - η l j z) → Clos2 n ρ 4 η → ∀ j,
          holderNorm (k + 1) α (T2 η j) (pd n ρ 2)
            ≤ ENNReal.ofReal (C2 k) * ∑ j, ∑ l, holderNorm k α (η j l) (pd n ρ 4)) ∧
      (∀ η, (∀ j l, ContDiffOn ℝ (⊤ : ℕ∞) (η j l) (pd n ρ 4)) →
        (∀ j l z, η j l z = - η l j z) → Clos2 n ρ 4 η →
        ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (T2 η j) (pd n ρ 2)) := by
  rcases lt_or_ge n 2 with hn2 | hn2
  · refine ⟨0, fun _ => 1, fun k => one_pos, ?_, ?_, ?_⟩
    · intro η hη hanti hcl j l z hz
      have hjl : j = l := Fin.ext (by omega)
      subst hjl
      have h0 : η j j z = 0 := by
        have h := hanti j j z
        linear_combination (1 / 2 : ℂ) * h
      rw [h0, sub_self]
    · intro k η hη hanti hcl j
      simp
    · intro η hη hanti hcl j
      exact contDiffOn_const
  · have hn0 : 0 < n := by omega
    obtain ⟨χ, V, hχ, hcs, htsupp3, hVo, hVmem, hχ1⟩ := exists_cutoff (n := n) hρ
    have htsupp4 : tsupport χ ⊆ pd n ρ 4 := htsupp3.trans (pd_mono hρ (by norm_num))
    have hη2 : ∀ z, z ∈ pd n ρ 2 → χ z = 1 := fun z hz =>
      hχ1 z (hVmem z (pd_mono hρ (by norm_num) hz))
    have hconst : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
          (∀ j l, ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) (η j l) (pd n ρ 4)) → ∀ j : Fin n,
            holderNorm (k + 1) α
                ((Work.NN.Core.bmRow (fun a b w => χ w * η a b w)
                  + tfin ρ (Edat χ η)) j) (pd n ρ 2)
              ≤ ENNReal.ofReal C * ∑ j : Fin n, ∑ l : Fin n,
                  holderNorm k α (η j l) (pd n ρ 4) := by
      intro k
      obtain ⟨Cb, hCb0, hCb⟩ := Work.NN.Core.bmRow_holder (n := n) hn0 hα0 hα1
        (c := 0) (r := fun i => 6 * ρ i) (fun i => by linarith [hρ i]) k
      obtain ⟨Cc, hCc0, hCc⟩ :=
        Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport (n := n) (Ω := pd n ρ 4)
          (isOpen_pd ρ 4).uniqueDiffOn hα0.le hα1.le (k := k) (hχ.of_le (by simp)) hcs
      obtain ⟨CE, hCE0, hCE⟩ := Edat_bound (n := n) hn0 hα0 hα1 hρ hχ htsupp3 k
      obtain ⟨Ct, hCt0, hCt⟩ := tfin_bound (ρ := ρ) hα0 hα1 hρ (k + 1)
      refine ⟨Cb * Cc + Ct * (((n : ℝ) + 1) * ((n : ℝ) + 1) * CE) + 1, by positivity, ?_⟩
      intro η hη j
      have hηk : ∀ i l, ContDiffOn ℝ ((k : ℕ) : ℕ∞) (η i l) (pd n ρ 4) :=
        fun i l => (hη i l).of_le (by simp)
      have hηk1 : ∀ i l, ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) (η i l) (pd n ρ 4) :=
        fun i l => (hη i l).of_le (by simp)
      have hη1 : ∀ i l, ContDiff ℝ (k + 1) (fun w => χ w * η i l w) := fun i l =>
        contDiff_mul_of_contDiffOn_tsupp (isOpen_pd ρ 4) hχ htsupp4 (hηk1 i l)
      have hvan : ∀ z : Fin n → ℂ, (∃ i : Fin n, 3 * ρ i ≤ ‖z i‖) → χ z = 0 := by
        intro z hz
        obtain ⟨i, hi⟩ := hz
        by_contra hc
        have hmem : z ∈ tsupport χ := subset_tsupport χ (Function.mem_support.mpr hc)
        have hz3 : z ∈ pd n ρ 3 := htsupp3 hmem
        rw [mem_pd] at hz3
        linarith [hz3 i, hi]
      -- ### the Bochner–Martinelli part
      have hB : holderNorm (k + 1) α
            (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) (pd n ρ 2)
          ≤ ENNReal.ofReal (Cb * Cc)
              * (∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4)) := by
        have hvan' : ∀ a b z, (∃ i : Fin n, 6 * ρ i / 2 ≤ ‖z i - (0 : Fin n → ℂ) i‖) →
            χ z * η a b z = 0 := by
          intro a b z hz
          obtain ⟨i, hi⟩ := hz
          simp only [Pi.zero_apply, sub_zero] at hi
          rw [show (6 : ℝ) * ρ i / 2 = 3 * ρ i from by ring] at hi
          rw [hvan z ⟨i, hi⟩, zero_mul]
        have hCb' := hCb (fun a b w => χ w * η a b w) hη1 hvan' j
        have hset : polydisc (0 : Fin n → ℂ) (fun i => 6 * ρ i / 2) = pd n ρ 3 := by
          simp only [pd]
          congr 1
          funext i
          ring
        rw [hset] at hCb'
        have hsum : (∑ l : Fin n, ∑ m : Fin n,
              holderNorm k α ((fun a b w => χ w * η a b w) l m) Set.univ)
            ≤ ENNReal.ofReal Cc
                * (∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4)) := by
          simp only [Finset.mul_sum]
          refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun m _ => ?_
          refine le_trans (holderNorm_univ_le_holderNorm_polydisc_of_vanishing (c := 0)
            (r := fun i => 3 * ρ i) (r' := fun i => 4 * ρ i) (fun i => by linarith [hρ i])
            hα0.le (fun z hz => ?_)) ?_
          · obtain ⟨i, hi⟩ := hz
            simp only [Pi.zero_apply, sub_zero] at hi
            rw [hvan z ⟨i, hi⟩, zero_mul]
          · exact hCc (η l m) (hηk l m)
        calc holderNorm (k + 1) α (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j)
              (pd n ρ 2)
            ≤ holderNorm (k + 1) α (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j)
                (pd n ρ 3) :=
              holderNorm_mono_set (isOpen_pd ρ 3) (isOpen_pd ρ 2) (pd_mono hρ (by norm_num))
                (k + 1) α _
          _ ≤ ENNReal.ofReal Cb * (∑ l : Fin n, ∑ m : Fin n,
                holderNorm k α ((fun a b w => χ w * η a b w) l m) Set.univ) := hCb'
          _ ≤ ENNReal.ofReal Cb * (ENNReal.ofReal Cc
                * (∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4))) :=
              mul_le_mul_of_nonneg_left hsum zero_le
          _ = ENNReal.ofReal (Cb * Cc)
                * (∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4)) := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul hCb0.le]
      -- ### the transferred-solver part
      have hT : holderNorm (k + 1) α (tfin ρ (Edat χ η) j) (pd n ρ 2)
          ≤ ENNReal.ofReal (Ct * (((n : ℝ) + 1) * ((n : ℝ) + 1) * CE))
              * (∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4)) := by
        have hEd : ∀ i l, ContDiff ℝ (k + 1) (Edat χ η i l) := fun i l =>
          Edat_contDiff hn0 hχ hcs htsupp4 hηk1 i l
        have hCt' := hCt (Edat χ η) hEd j
        have hterm : ∀ i l : Fin n,
            holderNorm (k + 1) α (Edat χ η i l) (polydisc 0 (sgm ρ))
              ≤ ENNReal.ofReal CE
                * (∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4)) :=
          fun i l => hCE η hη i l
        have hsum : (∑ i : Fin n, ∑ l : Fin n,
              holderNorm (k + 1) α (Edat χ η i l) (polydisc 0 (sgm ρ)))
            ≤ ENNReal.ofReal (((n : ℝ) + 1) * ((n : ℝ) + 1) * CE)
                * (∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4)) := by
          calc (∑ i : Fin n, ∑ l : Fin n,
                holderNorm (k + 1) α (Edat χ η i l) (polydisc 0 (sgm ρ)))
              ≤ ∑ _i : Fin n, ∑ _l : Fin n, (ENNReal.ofReal CE
                  * (∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4))) :=
                Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => hterm i l
            _ ≤ ENNReal.ofReal (((n : ℝ) + 1) * ((n : ℝ) + 1))
                  * (ENNReal.ofReal CE
                      * (∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4))) :=
                sum_sum_const_fin_le n _
            _ = ENNReal.ofReal (((n : ℝ) + 1) * ((n : ℝ) + 1) * CE)
                  * (∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4)) := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        calc holderNorm (k + 1) α (tfin ρ (Edat χ η) j) (pd n ρ 2)
            ≤ ENNReal.ofReal Ct * (∑ i : Fin n, ∑ l : Fin n,
                holderNorm (k + 1) α (Edat χ η i l) (polydisc 0 (sgm ρ))) := hCt'
          _ ≤ ENNReal.ofReal Ct * (ENNReal.ofReal (((n : ℝ) + 1) * ((n : ℝ) + 1) * CE)
                * (∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4))) :=
              mul_le_mul_of_nonneg_left hsum zero_le
          _ = ENNReal.ofReal (Ct * (((n : ℝ) + 1) * ((n : ℝ) + 1) * CE))
                * (∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4)) := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul hCt0.le]
      -- ### the two parts together
      have hsplit : holderNorm (k + 1) α
            ((Work.NN.Core.bmRow (fun a b w => χ w * η a b w)
              + tfin ρ (Edat χ η)) j) (pd n ρ 2)
          ≤ holderNorm (k + 1) α (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j)
              (pd n ρ 2)
            + holderNorm (k + 1) α (tfin ρ (Edat χ η) j) (pd n ρ 2) := by
        rw [Pi.add_apply]
        refine Work.CR.Flat.Holder.holderNorm_add_le (k := k + 1) ?_ ?_ (isOpen_pd ρ 2).uniqueDiffOn
        · exact (contDiff_bmRow hn0 hη1 (fun i l => hcs.mul_right) j).contDiffOn
        · exact (contDiff_tfin (ρ := ρ) (ζ := Edat χ η) (m := k + 1)
            (fun i l => Edat_contDiff hn0 hχ hcs htsupp4 hηk1 i l) j).contDiffOn
      calc holderNorm (k + 1) α
            ((Work.NN.Core.bmRow (fun a b w => χ w * η a b w)
              + tfin ρ (Edat χ η)) j) (pd n ρ 2)
          ≤ holderNorm (k + 1) α (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) (pd n ρ 2)
            + holderNorm (k + 1) α (tfin ρ (Edat χ η) j) (pd n ρ 2) := hsplit
        _ ≤ ENNReal.ofReal (Cb * Cc)
              * (∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4))
            + ENNReal.ofReal (Ct * (((n : ℝ) + 1) * ((n : ℝ) + 1) * CE))
              * (∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4)) :=
              add_le_add hB hT
        _ = ENNReal.ofReal (Cb * Cc + Ct * (((n : ℝ) + 1) * ((n : ℝ) + 1) * CE))
              * (∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4)) := by
              rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ ENNReal.ofReal (Cb * Cc + Ct * (((n : ℝ) + 1) * ((n : ℝ) + 1) * CE) + 1)
              * (∑ r : Fin n, ∑ s : Fin n, holderNorm k α (η r s) (pd n ρ 4)) :=
              mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith)) zero_le
    refine ⟨T2 hn0 χ hχ hcs htsupp4, fun k => Classical.choose (hconst k),
      fun k => (Classical.choose_spec (hconst k)).1, ?_, ?_, ?_⟩
    · -- the `∂̄`-equation
      intro η hη hanti hcl j l z hz
      have hηc : η ∈ contPd n ρ := fun i l => (hη i l).continuousOn
      rw [T2_apply hn0 hηc]
      have hEq : T2lin hn0 χ hχ hcs htsupp4 ⟨η, hηc⟩
          = Work.NN.Core.bmRow (fun a b w => χ w * η a b w) + tfin ρ (Edat χ η) := rfl
      rw [hEq]
      have hη1 : ∀ i l, ContDiffOn ℝ 1 (η i l) (pd n ρ 4) := fun i l => (hη i l).of_le (by simp)
      have hcl' : ∀ j l m z, z ∈ pd n ρ 4 →
          dbarCoord j (η l m) z - dbarCoord l (η j m) z + dbarCoord m (η j l) z = 0 :=
        fun j l m z hz' => hcl j l m z hz'
      -- the Bochner–Martinelli part
      have hb := bmDefect_eq_contOn hρ hn0 hχ hcs htsupp4 hη1 hcl' j l z hz
      have hbdef : Edat χ η j l z
          = (χ z - 1) * η j l z - Work.NN.Core.bmDefect χ η j l z := by
        rw [show Edat χ η j l z = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹
            * Work.CR.Flat.Cauchy.bmPot (fun m => Work.NN.Core.bmH χ η j l m) z from rfl,
          Work.NN.Core.bmDefect_apply]
        ring
      have hb1 : dbarCoord j (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) l) z
            - dbarCoord l (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) z
          = η j l z - Edat χ η j l z := by
        rw [hb, hbdef, hχ1 z (hVmem z (pd_mono hρ (by norm_num) hz))]
        ring
      -- the transferred-solver part
      have hEd : ∀ i m, ContDiff ℝ 1 (Edat χ η i m) := fun i m =>
        Edat_contDiff hn0 hχ hcs htsupp4 hη1 i m
      have hEda : ∀ i m z', Edat χ η i m z' = - Edat χ η m i z' := fun i m z' =>
        Edat_antisymm hn0 hχ hcs htsupp4 (fun a b => (hη a b).continuousOn) hanti i m z'
      have hEdc : ∀ i m m' z', z' ∈ polydisc 0 (sgm ρ) →
          dbarCoord i (Edat χ η m m') z' - dbarCoord m (Edat χ η i m') z'
            + dbarCoord m' (Edat χ η i m) z' = 0 := fun i m m' z' hz' =>
        Edat_closed_ball hn0 hχ hcs htsupp4 hVo hVmem hχ1 hη1 hcl' i m m' z' hz'
      have ht := tfin_solves (ρ := ρ) hρ hEd hEda hEdc j l z hz
      -- split `∂̄` over the sum
      have hBd : ∀ i : Fin n, DifferentiableAt ℝ
          (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) i) z := fun i =>
        differentiableAt_bmRow hn0 (fun a b => contDiff_mul_of_contDiffOn_tsupp (isOpen_pd ρ 4)
          hχ htsupp4 (hη1 a b)) (fun a b => hcs.mul_right) i z
      have hTd : ∀ i : Fin n, DifferentiableAt ℝ (tfin ρ (Edat χ η) i) z := fun i =>
        ((contDiff_tfin (ρ := ρ) (ζ := Edat χ η) (m := 1) hEd i).differentiable one_ne_zero).differentiableAt
      have eFl : (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) + tfin ρ (Edat χ η)) l
          = Work.NN.Core.bmRow (fun a b w => χ w * η a b w) l + tfin ρ (Edat χ η) l :=
        Pi.add_apply _ _ l
      have eFj : (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) + tfin ρ (Edat χ η)) j
          = Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j + tfin ρ (Edat χ η) j :=
        Pi.add_apply _ _ j
      rw [eFl, eFj, dbarCoord_add_pi j (hBd l) (hTd l), dbarCoord_add_pi l (hBd j) (hTd j)]
      linear_combination hb1 + ht
    · -- the `C^{k,α}` gain
      intro k η hη hanti hcl j
      have hηc : η ∈ contPd n ρ := fun i l => (hη i l).continuousOn
      rw [T2_apply hn0 hηc]
      have hEq : T2lin hn0 χ hχ hcs htsupp4 ⟨η, hηc⟩
          = Work.NN.Core.bmRow (fun a b w => χ w * η a b w) + tfin ρ (Edat χ η) := rfl
      rw [hEq]
      exact (Classical.choose_spec (hconst k)).2 η hη j
    · -- smoothness
      intro η hη hanti hcl j
      have hηc : η ∈ contPd n ρ := fun i l => (hη i l).continuousOn
      rw [T2_apply hn0 hηc]
      have hEq : T2lin hn0 χ hχ hcs htsupp4 ⟨η, hηc⟩
          = Work.NN.Core.bmRow (fun a b w => χ w * η a b w) + tfin ρ (Edat χ η) := rfl
      rw [hEq, Pi.add_apply]
      have hsm : ∀ i l, ContDiff ℝ (⊤ : ℕ∞) (fun w => χ w * η i l w) := by
        intro i l
        rw [contDiff_infty]
        intro m
        exact contDiff_mul_of_contDiffOn_tsupp (isOpen_pd ρ 4) hχ htsupp4
          ((hη i l).of_le (by simp))
      have hbm : ContDiff ℝ (⊤ : ℕ∞) (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) := by
        rw [contDiff_infty]
        intro m
        exact contDiff_bmRow hn0 (fun i l => (hsm i l).of_le (by simp))
          (fun i l => hcs.mul_right) j
      have htf : ContDiff ℝ (⊤ : ℕ∞) (tfin ρ (Edat χ η) j) :=
        tfin_smooth (fun i l => Edat_smooth hn0 hχ hcs htsupp4 hη i l) j
      exact (hbm.add htf).contDiffOn
end Work.NN.Final
end
