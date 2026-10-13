/-
# Almost-everywhere strong measurability of the four `H¹` pairing integrands

The `ℋ¹` pairing `H1IP α` is a sum of four weighted `L²` pairings whose integrands are
the products of two *blocks* (see `H1IPAddDefs`):

* `Xeta a · Xeta b`         (the `D_z⁰`-block),
* `XetaDz a · XetaDz b`     (the `D_z¹`-block),
* `XgamDth α a · XgamDth α b` (the `D_θ`-block),
* `Xw a · Xw b`             (the plain `w²`-block).

Each block is the product of a `z`-derivative (`Dth` etc.) of a `SmoothNbhd` profile with
an explicit weight, and is therefore *jointly continuous on the open quadrant*
`QdOp = (0,∞) × (0,π/2)`; moreover, for every fixed `z ∈ Iz`, its `θ`-slice is continuous
on the open interval `(0,π/2)`.  Since the open quadrant / open interval differ from the
closed domain `Iz × Iθ` by a null set, all these blocks are almost everywhere strongly
measurable, both for the product measure `(dz)|_{Iz} ⊗ (dθ)|_{Iθ}` and for every one
dimensional slice measure `(dθ)|_{Iθ}`.

This file proves those a.e. strong measurability statements for the four pairings above.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.H1IPAddDefs
import Submission.Work.Coercivity.Eztheta1_eq_HkSq_one
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The weights of the four blocks -/

/-- The radial–angular weight `w(z)/sin(2θ)^{η/2}` multiplying the two `η`-blocks. -/
private def Weta (z θ : ℝ) : ℝ := Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2)

/-- The plain radial weight `w(z)` multiplying the third block. -/
def Ww (z : ℝ) (_θ : ℝ) : ℝ := Spaces.w z

/-- The angular weight `Wt α = w(z) · sin(2θ)^{-γ/2}` multiplying the `D_θ`-block. -/
def Wgam (α : ℝ) (z θ : ℝ) : ℝ := Spaces.Wt α z θ

/-! ## The open quadrant lies in the neighbourhood on which `SmoothNbhd` is stated -/

lemma QdOp_subset_nbhU : QdOp ⊆ Spaces.nbhU :=
  Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num))
    (Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos]))

/-- `sin (2θ) > 0` for `θ ∈ (0,π/2)`. -/
private lemma sin_two_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

/-! ## Continuity on the open quadrant -/

/-- `θ ↦ sin(2θ)^c` is continuous on the open quadrant. -/
lemma contOn_Qd_sinpow (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) QdOp :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_of_mem hp.2)))

/-- The radial weight `w(z) = (1+z)²/z²` is continuous on the open quadrant. -/
lemma contOn_Qd_w : ContinuousOn (fun p : ℝ × ℝ => Spaces.w p.1) QdOp := by
  simp only [Spaces.w]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt hp.1)

/-- The weight `Weta` is continuous on the open quadrant. -/
lemma contOn_Qd_Weta : ContinuousOn (fun p : ℝ × ℝ => Weta p.1 p.2) QdOp := by
  simp only [Weta]
  exact contOn_Qd_w.div (contOn_Qd_sinpow (Spaces.eta / 2))
    (fun _p hp => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem hp.2) _))

/-- The weight `Ww` is continuous on the open quadrant. -/
lemma contOn_Qd_Ww : ContinuousOn (fun p : ℝ × ℝ => Ww p.1 p.2) QdOp := by
  simpa only [Ww] using contOn_Qd_w

/-- The weight `Wgam α = Wt α` is continuous on the open quadrant. -/
lemma contOn_Qd_Wgam (α : ℝ) : ContinuousOn (fun p : ℝ × ℝ => Wgam α p.1 p.2) QdOp := by
  simp only [Wgam, Spaces.Wt, Spaces.wTheta]
  exact contOn_Qd_w.mul (contOn_Qd_sinpow (-(Spaces.gam α / 2)))

/-- A `SmoothNbhd` profile is continuous on the open quadrant. -/
lemma contOn_Qd_uncurry {f : ℝ → ℝ → ℝ} (hf : Spaces.SmoothNbhd f) :
    ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) QdOp :=
  hf.continuousOn.mono QdOp_subset_nbhU

/-- The product of a `SmoothNbhd` profile with a weight continuous on the open quadrant
is continuous on the open quadrant. -/
lemma contOn_Qd_mul_weight {f W : ℝ → ℝ → ℝ} (hf : Spaces.SmoothNbhd f)
    (hW : ContinuousOn (fun p : ℝ × ℝ => W p.1 p.2) QdOp) :
    ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2 * W p.1 p.2) QdOp :=
  (contOn_Qd_uncurry hf).mul hW

lemma contOn_Qd_Xeta {f : ℝ → ℝ → ℝ} (hf : Spaces.SmoothNbhd f) :
    ContinuousOn (fun p : ℝ × ℝ => Xeta f p.1 p.2) QdOp := by
  simpa only [Xeta, Weta] using contOn_Qd_mul_weight hf contOn_Qd_Weta

lemma contOn_Qd_XetaDz {f : ℝ → ℝ → ℝ} (hf : Spaces.SmoothNbhd f) :
    ContinuousOn (fun p : ℝ × ℝ => XetaDz f p.1 p.2) QdOp := by
  simpa only [XetaDz, Weta] using
    contOn_Qd_mul_weight (Spaces.SmoothNbhd.Dz hf) contOn_Qd_Weta

lemma contOn_Qd_XgamDth (α : ℝ) {f : ℝ → ℝ → ℝ} (hf : Spaces.SmoothNbhd f) :
    ContinuousOn (fun p : ℝ × ℝ => XgamDth α f p.1 p.2) QdOp := by
  simpa only [XgamDth, Wgam] using
    contOn_Qd_mul_weight (Spaces.SmoothNbhd.Dth hf) (contOn_Qd_Wgam α)

lemma contOn_Qd_Xw {f : ℝ → ℝ → ℝ} (hf : Spaces.SmoothNbhd f) :
    ContinuousOn (fun p : ℝ × ℝ => Xw f p.1 p.2) QdOp := by
  simpa only [Xw, Ww] using contOn_Qd_mul_weight hf contOn_Qd_Ww

/-! ## Continuity of the slices on the open interval `(0,π/2)` -/

/-- For `z ∈ Iz`, the `θ`-slice of a `SmoothNbhd` profile is continuous on `(0,π/2)`. -/
lemma contOn_slice_smoothNbhd {f : ℝ → ℝ → ℝ} (hf : Spaces.SmoothNbhd f) {z : ℝ}
    (hz : z ∈ Spaces.Iz) :
    ContinuousOn (fun θ => f z θ) (Set.Ioo 0 (π / 2)) := by
  have hz' : (-1 : ℝ) < z := by
    rw [Spaces.Iz, Set.mem_Ici] at hz; linarith
  have hcont : ContinuousOn (Function.uncurry f) Spaces.nbhU := hf.continuousOn
  have hiota : ContinuousOn (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (π / 2)) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hmap : MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (π / 2)) Spaces.nbhU := by
    intro θ hθ
    rw [Spaces.nbhU, Set.mem_prod]
    exact ⟨by rw [Set.mem_Ioi]; exact hz',
      by rw [Set.mem_Ioo]; exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
  simpa only [Function.uncurry] using hcont.comp' hiota hmap

/-- The `θ`-slice of `Weta z · ` is continuous on `(0,π/2)`. -/
lemma contOn_slice_Weta (z : ℝ) :
    ContinuousOn (fun θ => Weta z θ) (Set.Ioo 0 (π / 2)) := by
  simp only [Weta]
  exact continuousOn_const.div
    (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_of_mem hθ))))
    (fun θ hθ => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem hθ) _))

/-- The `θ`-slice of `Ww z · ` is continuous on `(0,π/2)`. -/
lemma contOn_slice_Ww (z : ℝ) :
    ContinuousOn (fun θ => Ww z θ) (Set.Ioo 0 (π / 2)) := by
  simpa only [Ww] using (continuousOn_const : ContinuousOn (fun _ : ℝ => Spaces.w z)
    (Set.Ioo 0 (π / 2)))

/-- The `θ`-slice of `Wgam α z · ` is continuous on `(0,π/2)`. -/
lemma contOn_slice_Wgam (α z : ℝ) :
    ContinuousOn (fun θ => Wgam α z θ) (Set.Ioo 0 (π / 2)) := by
  simp only [Wgam, Spaces.Wt, Spaces.wTheta]
  exact continuousOn_const.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_of_mem hθ))))

/-- The product of the `θ`-slice of a `SmoothNbhd` profile with a weight slice continuous
on `(0,π/2)` is continuous on `(0,π/2)`. -/
lemma contOn_slice_mul_weight {f W : ℝ → ℝ → ℝ} (hf : Spaces.SmoothNbhd f) {z : ℝ}
    (hz : z ∈ Spaces.Iz) (hW : ContinuousOn (fun θ => W z θ) (Set.Ioo 0 (π / 2))) :
    ContinuousOn (fun θ => f z θ * W z θ) (Set.Ioo 0 (π / 2)) :=
  (contOn_slice_smoothNbhd hf hz).mul hW

lemma contOn_slice_Xeta {f : ℝ → ℝ → ℝ} (hf : Spaces.SmoothNbhd f) {z : ℝ}
    (hz : z ∈ Spaces.Iz) :
    ContinuousOn (fun θ => Xeta f z θ) (Set.Ioo 0 (π / 2)) := by
  simpa only [Xeta, Weta] using contOn_slice_mul_weight hf hz (contOn_slice_Weta z)

lemma contOn_slice_XetaDz {f : ℝ → ℝ → ℝ} (hf : Spaces.SmoothNbhd f) {z : ℝ}
    (hz : z ∈ Spaces.Iz) :
    ContinuousOn (fun θ => XetaDz f z θ) (Set.Ioo 0 (π / 2)) := by
  simpa only [XetaDz, Weta] using
    contOn_slice_mul_weight (Spaces.SmoothNbhd.Dz hf) hz (contOn_slice_Weta z)

lemma contOn_slice_XgamDth (α : ℝ) {f : ℝ → ℝ → ℝ} (hf : Spaces.SmoothNbhd f) {z : ℝ}
    (hz : z ∈ Spaces.Iz) :
    ContinuousOn (fun θ => XgamDth α f z θ) (Set.Ioo 0 (π / 2)) := by
  simpa only [XgamDth, Wgam] using
    contOn_slice_mul_weight (Spaces.SmoothNbhd.Dth hf) hz (contOn_slice_Wgam α z)

lemma contOn_slice_Xw {f : ℝ → ℝ → ℝ} (hf : Spaces.SmoothNbhd f) {z : ℝ}
    (hz : z ∈ Spaces.Iz) :
    ContinuousOn (fun θ => Xw f z θ) (Set.Ioo 0 (π / 2)) := by
  simpa only [Xw, Ww] using contOn_slice_mul_weight hf hz (contOn_slice_Ww z)

/-! ## The open interval `(0,π/2)` is co-null in `Iθ` -/

lemma restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Spaces.Iθ := by
  apply Measure.restrict_congr_set
  rw [Spaces.Iθ]
  exact MeasureTheory.Ioo_ae_eq_Icc

/-! ## From continuity to a.e. strong measurability -/

/-- A generic pair of blocks satisfying the two continuity conditions is a.e. strongly
measurable, jointly and on every slice. -/
lemma aesm_pair_of_contOn {f g : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) QdOp)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) QdOp)
    (hfs : ∀ z ∈ Spaces.Iz, ContinuousOn (fun θ => f z θ) (Set.Ioo 0 (π / 2)))
    (hgs : ∀ z ∈ Spaces.Iz, ContinuousOn (fun θ => g z θ) (Set.Ioo 0 (π / 2))) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2 * g p.1 p.2)
        ((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ))
      ∧ ∀ z ∈ Spaces.Iz, MeasureTheory.AEStronglyMeasurable (fun θ => f z θ * g z θ)
          (MeasureTheory.volume.restrict Spaces.Iθ) := by
  refine ⟨Spaces.aesm_of_continuousOn_Qd _ (hf.mul hg), ?_⟩
  intro z hz
  rw [← restrict_Ioo_eq_restrict_Iθ]
  exact ((hfs z hz).mul (hgs z hz)).aestronglyMeasurable measurableSet_Ioo

end Work.Coercivity

namespace Work.Coercivity

theorem aesm_blocks (α : ℝ) (a b : ℝ → ℝ → ℝ) (hsa : Spaces.SmoothNbhd a)
    (hsb : Spaces.SmoothNbhd b) :
    (MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Xeta a p.1 p.2 * Xeta b p.1 p.2)
        ((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ))
      ∧ ∀ z ∈ Spaces.Iz, MeasureTheory.AEStronglyMeasurable (fun θ => Xeta a z θ * Xeta b z θ)
          (MeasureTheory.volume.restrict Spaces.Iθ))
    ∧ (MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => XetaDz a p.1 p.2 * XetaDz b p.1 p.2)
        ((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ))
      ∧ ∀ z ∈ Spaces.Iz, MeasureTheory.AEStronglyMeasurable (fun θ => XetaDz a z θ * XetaDz b z θ)
          (MeasureTheory.volume.restrict Spaces.Iθ))
    ∧ (MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => XgamDth α a p.1 p.2 * XgamDth α b p.1 p.2)
        ((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ))
      ∧ ∀ z ∈ Spaces.Iz, MeasureTheory.AEStronglyMeasurable (fun θ => XgamDth α a z θ * XgamDth α b z θ)
          (MeasureTheory.volume.restrict Spaces.Iθ))
    ∧ (MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Xw a p.1 p.2 * Xw b p.1 p.2)
        ((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ))
      ∧ ∀ z ∈ Spaces.Iz, MeasureTheory.AEStronglyMeasurable (fun θ => Xw a z θ * Xw b z θ)
          (MeasureTheory.volume.restrict Spaces.Iθ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact aesm_pair_of_contOn (contOn_Qd_Xeta hsa) (contOn_Qd_Xeta hsb)
      (fun _ hz => contOn_slice_Xeta hsa hz) (fun _ hz => contOn_slice_Xeta hsb hz)
  · exact aesm_pair_of_contOn (contOn_Qd_XetaDz hsa) (contOn_Qd_XetaDz hsb)
      (fun _ hz => contOn_slice_XetaDz hsa hz) (fun _ hz => contOn_slice_XetaDz hsb hz)
  · exact aesm_pair_of_contOn (contOn_Qd_XgamDth α hsa) (contOn_Qd_XgamDth α hsb)
      (fun _ hz => contOn_slice_XgamDth α hsa hz) (fun _ hz => contOn_slice_XgamDth α hsb hz)
  · exact aesm_pair_of_contOn (contOn_Qd_Xw hsa) (contOn_Qd_Xw hsb)
      (fun _ hz => contOn_slice_Xw hsa hz) (fun _ hz => contOn_slice_Xw hsb hz)

end Work.Coercivity
