import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs

/-!
# The box sphere is a round sphere

`Work.Topology.SphereSlicing.BoxSphere s c σ` is the boundary of Pardon's box `Submission.PBox s
c σ`, i.e. the level set `{y | Submission.boxNorm c σ y = s}` of the box norm.  For `s > 0` it is
a polyhedral 2-sphere, and here we produce an **explicit** homeomorphism

`BoxSphere s c σ ≃ₜ Metric.sphere 0 1`

given by radial projection `y ↦ ‖y - c‖⁻¹ • (y - c)` from the centre of the box onto the unit
sphere, whose inverse is the inverse of radial projection followed by the rescaling which brings
the radial ray back to the box:

`w ↦ c + (s / boxNorm c σ (c + w)) • w`.

Both directions are continuous (the denominators never vanish on the respective domains), the two
formulas are mutually inverse by the two structural properties of the box norm — that it vanishes
only at the centre and that it is homogeneous along rays through the centre — and the second
formula *is* the first formula of the statement, up to `a / b = a * b⁻¹`.

This is the "item 1" of the assignment: it makes `BoxSphere s c σ` a `Metric.sphere 0 1`, hence
(elsewhere) an `Work.InnermostDisk.IsEmbeddedSphere`.
-/

namespace Work.Topology.SphereSlicing

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- The box norm is continuous. -/
private theorem boxNorm_continuous_aux (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Continuous fun y : R3 => Submission.boxNorm c σ y := by
  unfold Submission.boxNorm
  fun_prop

/-- The box norm is homogeneous along rays through the centre `c`: scaling about `c` by `t`
scales the norm by `|t|`. -/
private theorem boxNorm_homogeneous_aux (c : R3) (σ : Equiv.Perm (Fin 3)) (t : ℝ) (y : R3) :
    Submission.boxNorm c σ (c + t • (y - c)) = |t| * Submission.boxNorm c σ y := by
  have h : ∀ i : Fin 3, |(c + t • (y - c)) (σ i) - c (σ i)| / Submission.boxSide i
      = |t| * (|y (σ i) - c (σ i)| / Submission.boxSide i) := by
    intro i
    rw [show (c + t • (y - c)) (σ i) - c (σ i) = t * (y (σ i) - c (σ i)) by simp]
    rw [abs_mul]
    ring
  rw [Submission.boxNorm, Submission.boxNorm, h 0, h 1, h 2]
  simp only [mul_max_of_nonneg _ _ (abs_nonneg t)]

/-- `max (max a b) d = 0` for nonnegative `a, b, d`. -/
private theorem max_max_eq_zero {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    max (max a b) d = 0 ↔ a = 0 ∧ b = 0 ∧ d = 0 := by
  constructor
  · intro h
    refine ⟨le_antisymm ?_ ha, le_antisymm ?_ hb, le_antisymm ?_ hd⟩
    · exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_of_eq h))
    · exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_of_eq h))
    · exact le_trans (le_max_right _ _) (le_of_eq h)
  · rintro ⟨rfl, rfl, rfl⟩
    simp

/-- **The box norm vanishes only at the centre.** -/
private theorem boxNorm_eq_zero_iff (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) :
    Submission.boxNorm c σ y = 0 ↔ y = c := by
  rw [Submission.boxNorm,
    max_max_eq_zero (div_nonneg (abs_nonneg _) (le_of_lt (Submission.boxSide_pos 0)))
      (div_nonneg (abs_nonneg _) (le_of_lt (Submission.boxSide_pos 1)))
      (div_nonneg (abs_nonneg _) (le_of_lt (Submission.boxSide_pos 2)))]
  constructor
  · rintro ⟨h0, h1, h2⟩
    have key : ∀ i : Fin 3, y (σ i) = c (σ i) := by
      intro i
      have hi : |y (σ i) - c (σ i)| / Submission.boxSide i = 0 := by
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
      have hz : |y (σ i) - c (σ i)| = 0 := by
        rcases div_eq_zero_iff.mp hi with h' | h'
        · exact h'
        · exact absurd h' (ne_of_gt (Submission.boxSide_pos i))
      exact sub_eq_zero.mp (abs_eq_zero.mp hz)
    ext j
    simpa using key (σ.symm j)
  · rintro rfl
    refine ⟨by simp, by simp, by simp⟩

theorem homeomorph_BoxSphere {s : ℝ} (hs : 0 < s) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) :
    ∃ Φ : {y : LeanEval.KnotTheory.PardonDistortion.R3 // Submission.boxNorm c σ y = s} ≃ₜ
        Metric.sphere (0 : LeanEval.KnotTheory.PardonDistortion.R3) 1,
      (∀ y, (Φ y : LeanEval.KnotTheory.PardonDistortion.R3)
        = (‖(y : LeanEval.KnotTheory.PardonDistortion.R3) - c‖)⁻¹ •
            ((y : LeanEval.KnotTheory.PardonDistortion.R3) - c)) ∧
      (∀ w, ((Φ.symm w : {y : LeanEval.KnotTheory.PardonDistortion.R3 //
                Submission.boxNorm c σ y = s}) : LeanEval.KnotTheory.PardonDistortion.R3)
        = c + (s / Submission.boxNorm c σ (c + (w : LeanEval.KnotTheory.PardonDistortion.R3))) •
            (w : LeanEval.KnotTheory.PardonDistortion.R3)) := by
  -- the box sphere avoids the centre
  have hBoxNe : ∀ y : BoxSphere s c σ, (y : R3) ≠ c := by
    intro y hy
    have h1 : Submission.boxNorm c σ (y : R3) = s := y.2
    have h2 : Submission.boxNorm c σ (y : R3) = 0 := by
      rw [hy]; exact (boxNorm_eq_zero_iff c σ c).mpr rfl
    rw [h2] at h1; linarith
  -- normalising a point of the box sphere lands on the unit sphere
  have hSphMem : ∀ y : BoxSphere s c σ,
      ‖(y : R3) - c‖⁻¹ • ((y : R3) - c) ∈ Metric.sphere (0 : R3) 1 := by
    intro y
    have hne : (y : R3) - c ≠ 0 := sub_ne_zero.mpr (hBoxNe y)
    have hpos : 0 < ‖(y : R3) - c‖ := norm_pos_iff.mpr hne
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hpos]
    exact inv_mul_cancel₀ (ne_of_gt hpos)
  -- the box norm does not vanish on the unit sphere translated to the centre
  have hNzero : ∀ w : Metric.sphere (0 : R3) 1,
      Submission.boxNorm c σ (c + (w : R3)) ≠ 0 := by
    intro w h
    have hcw : c + (w : R3) = c := (boxNorm_eq_zero_iff c σ (c + (w : R3))).mp h
    have hw0 : (w : R3) = 0 := by
      have := congrArg (fun z : R3 => z - c) hcw
      simpa using this
    have hw1 : ‖(w : R3)‖ = 1 := by
      have h := w.2; rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    rw [hw0] at hw1; simp at hw1
  -- rescaled inverse radial projection lands on the box sphere
  have hBoxMem : ∀ w : Metric.sphere (0 : R3) 1,
      c + (s * (Submission.boxNorm c σ (c + (w : R3)))⁻¹) • (w : R3) ∈ BoxSphere s c σ := by
    intro w
    have hNpos : 0 < Submission.boxNorm c σ (c + (w : R3)) :=
      lt_of_le_of_ne (Submission.boxNorm_nonneg c σ _) (Ne.symm (hNzero w))
    show Submission.boxNorm c σ
      (c + (s * (Submission.boxNorm c σ (c + (w : R3)))⁻¹) • (w : R3)) = s
    have hhom := boxNorm_homogeneous_aux c σ (s * (Submission.boxNorm c σ (c + (w : R3)))⁻¹)
      (c + (w : R3))
    rw [show (c + (w : R3)) - c = (w : R3) by abel] at hhom
    rw [hhom, abs_of_nonneg (mul_nonneg (le_of_lt hs) (le_of_lt (inv_pos.mpr hNpos))),
      mul_assoc, inv_mul_cancel₀ (ne_of_gt hNpos), mul_one]
  -- the two maps
  let φ : BoxSphere s c σ → Metric.sphere (0 : R3) 1 :=
    fun y => ⟨‖(y : R3) - c‖⁻¹ • ((y : R3) - c), hSphMem y⟩
  let ψ : Metric.sphere (0 : R3) 1 → BoxSphere s c σ :=
    fun w => ⟨c + (s * (Submission.boxNorm c σ (c + (w : R3)))⁻¹) • (w : R3), hBoxMem w⟩
  have hcontφ : Continuous φ := by
    have hnorm : Continuous fun y : BoxSphere s c σ => ‖(y : R3) - c‖ :=
      (continuous_subtype_val.sub continuous_const).norm
    have hne : ∀ y : BoxSphere s c σ, ‖(y : R3) - c‖ ≠ 0 :=
      fun y => ne_of_gt (norm_pos_iff.mpr (sub_ne_zero.mpr (hBoxNe y)))
    exact ((hnorm.fun_inv₀ hne).smul (continuous_subtype_val.sub continuous_const)).subtype_mk
      hSphMem
  have hcontψ : Continuous ψ := by
    have hNcont : Continuous fun w : Metric.sphere (0 : R3) 1 =>
        Submission.boxNorm c σ (c + (w : R3)) :=
      (boxNorm_continuous_aux c σ).comp (continuous_const.add continuous_subtype_val)
    exact (continuous_const.add
      ((continuous_const.mul (hNcont.fun_inv₀ hNzero)).smul continuous_subtype_val)).subtype_mk
      hBoxMem
  -- the two maps are mutually inverse
  have hleft : ∀ y : BoxSphere s c σ, ψ (φ y) = y := by
    intro y
    apply Subtype.ext
    have hpos : 0 < ‖(y : R3) - c‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (hBoxNe y))
    have hφy : (φ y : R3) = ‖(y : R3) - c‖⁻¹ • ((y : R3) - c) := rfl
    have hNcφ : Submission.boxNorm c σ (c + (φ y : R3)) = s * ‖(y : R3) - c‖⁻¹ := by
      have h := boxNorm_homogeneous_aux c σ (‖(y : R3) - c‖⁻¹) (y : R3)
      rw [← hφy] at h
      rw [h, abs_of_pos (inv_pos.mpr hpos), y.2, mul_comm]
    show c + (s * (Submission.boxNorm c σ (c + (φ y : R3)))⁻¹) • (φ y : R3) = (y : R3)
    rw [hNcφ]
    rw [show s * (s * ‖(y : R3) - c‖⁻¹)⁻¹ = ‖(y : R3) - c‖ by
      rw [mul_inv_rev, inv_inv, mul_comm (‖(y : R3) - c‖) s⁻¹, ← mul_assoc,
        mul_inv_cancel₀ (ne_of_gt hs), one_mul]]
    rw [hφy, smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
    abel
  have hright : ∀ w : Metric.sphere (0 : R3) 1, φ (ψ w) = w := by
    intro w
    apply Subtype.ext
    have hNpos : 0 < Submission.boxNorm c σ (c + (w : R3)) :=
      lt_of_le_of_ne (Submission.boxNorm_nonneg c σ _) (Ne.symm (hNzero w))
    have hpsi : (ψ w : R3) - c
        = (s * (Submission.boxNorm c σ (c + (w : R3)))⁻¹) • (w : R3) := by
      show c + (s * (Submission.boxNorm c σ (c + (w : R3)))⁻¹) • (w : R3) - c = _
      abel
    have ht : 0 < s * (Submission.boxNorm c σ (c + (w : R3)))⁻¹ :=
      mul_pos hs (inv_pos.mpr hNpos)
    have hwm : ‖(w : R3)‖ = 1 := by
      have h := w.2; rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    show ‖(ψ w : R3) - c‖⁻¹ • ((ψ w : R3) - c) = (w : R3)
    rw [hpsi, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hwm, mul_one,
      inv_smul_smul₀ (ne_of_gt ht)]
  refine ⟨Homeomorph.mk { toFun := φ, invFun := ψ, left_inv := hleft, right_inv := hright }
    hcontφ hcontψ, ?_, ?_⟩
  · intro y; rfl
  · intro w
    show c + (s * (Submission.boxNorm c σ (c + (w : R3)))⁻¹) • (w : R3)
      = c + (s / Submission.boxNorm c σ (c + (w : R3))) • (w : R3)
    rw [div_eq_mul_inv]

end

end Work.Topology.SphereSlicing
