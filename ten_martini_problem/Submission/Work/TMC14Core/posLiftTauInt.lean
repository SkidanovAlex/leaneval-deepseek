import Mathlib
import Submission.Work.TMComp.RotBasics.Defs
import Submission.Work.TMC13.Basic

/-!
# Integer translation number for a positive lift whose matrix has a real eigenvector

`IsPosLift M G` says that `G` presents the *positive* projective lift of the invertible
matrix `M`: for every `t`, `smul M (vc t) = ‖smul M (vc t)‖ • vc (G t)`, so that `vc (G t)`
is the direction of `M` applied to the direction `t`, positively normalised.

If `M` has a nonzero real eigenvector then the projective action of `M` fixes the
corresponding *direction* of the circle.  Consequently the lift `G` sends that point `s`
of the circle to itself modulo the period `1` of the half-turn parametrisation:
`vc (G s) = ± vc s`, hence `G s = s + m` for an integer `m`.  A `CircleDeg1Lift` with
`G s = s + m` has translation number `m` (`CircleDeg1Lift.translationNumber_of_eq_add_int`),
so the translation number of `G` is an integer.

The main theorem `posLiftTauInt` is the statement requested by the C14 (`P_GapBound`)
subproject; the lemmas `vcDirExists` and `tauInt_of_vc_scalar` are its reusable
ingredients.
-/

noncomputable section

namespace Work.TMC14Core

open Work.TMComp.RotBasics

/-! ## Circle points in a prescribed direction -/

/-- The complex number whose two coordinates are those of `v : Fin 2 → ℝ`. -/
def toC (v : Fin 2 → ℝ) : ℂ := ⟨v 0, v 1⟩

lemma toC_injective : Function.Injective toC := by
  intro v u h
  funext i
  fin_cases i
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h

@[simp] lemma toC_zero : toC (0 : Fin 2 → ℝ) = 0 := by
  refine Complex.ext ?_ ?_ <;> simp [toC]

lemma toC_ne_zero {v : Fin 2 → ℝ} (hv : v ≠ 0) : toC v ≠ 0 :=
  fun h => hv (toC_injective (by rw [h, toC_zero]))

lemma toC_mulVec (M : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    toC (M.mulVec v) = smul M (toC v) := by
  refine Complex.ext ?_ ?_ <;> simp [toC, smul, Matrix.mulVec]

lemma toC_const_smul (c : ℝ) (v : Fin 2 → ℝ) : toC (c • v) = c • toC v := by
  refine Complex.ext ?_ ?_ <;> simp [toC, Pi.smul_apply, smul_eq_mul]

/-- A half turn: `vc 1 = -1`. -/
lemma vc_one : vc 1 = -1 := by
  refine Complex.ext ?_ ?_ <;> simp [vc, Real.cos_pi, Real.sin_pi]

/-- Shifting the argument by one half turn negates the circle point. -/
lemma vc_add_one (s : ℝ) : vc (s + 1) = -vc s := by
  rw [vc_add, vc_one, mul_neg, mul_one]

/-- Every nonzero complex number is a positive multiple of a circle point `vc s`. -/
theorem vcDirExists (w : ℂ) (hw : w ≠ 0) :
    ∃ (s r : ℝ), 0 < r ∧ w = r • vc s := by
  refine ⟨w.arg / Real.pi, ‖w‖, norm_pos_iff.mpr hw, ?_⟩
  have harg : Real.pi * (w.arg / Real.pi) = w.arg := by
    rw [mul_div_cancel₀ _ Real.pi_ne_zero]
  have hvc : vc (w.arg / Real.pi) = Complex.exp ((w.arg : ℂ) * Complex.I) := by
    rw [Complex.exp_ofReal_mul_I]
    refine Complex.ext ?_ ?_ <;>
      simp [vc, harg, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  rw [hvc, Complex.real_smul]
  exact (Complex.norm_mul_exp_arg_mul_I w).symm

/-! ## A matrix with nonzero determinant never kills a circle point -/

lemma smul_vc_ne_zero {A : Matrix (Fin 2) (Fin 2) ℝ} (hdet : A.det ≠ 0) (t : ℝ) :
    smul A (vc t) ≠ 0 := by
  intro hz
  have e1 : A 0 0 * (vc t).re + A 0 1 * (vc t).im = 0 := by
    have h := congrArg Complex.re hz; simpa [smul] using h
  have e2 : A 1 0 * (vc t).re + A 1 1 * (vc t).im = 0 := by
    have h := congrArg Complex.im hz; simpa [smul] using h
  have hdetval : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := Matrix.det_fin_two A
  have hc0 : (vc t).re = 0 := by
    have h0 : A.det * (vc t).re = 0 := by
      rw [hdetval]; linear_combination A 1 1 * e1 - A 0 1 * e2
    exact (mul_eq_zero.mp h0).resolve_left hdet
  have hs0 : (vc t).im = 0 := by
    have h0 : A.det * (vc t).im = 0 := by
      rw [hdetval]; linear_combination A 0 0 * e2 - A 1 0 * e1
    exact (mul_eq_zero.mp h0).resolve_left hdet
  exact vc_ne_zero t (Complex.ext hc0 hs0)

/-! ## Integer translation numbers from a fixed circle point -/

/-- If the lift `G` sends `s` to a point whose `vc`-value is a nonzero real multiple of
`vc s`, then the translation number of `G` is an integer. -/
theorem tauInt_of_vc_scalar {G : CircleDeg1Lift} {s : ℝ}
    (h : ∃ c : ℝ, c ≠ 0 ∧ vc (G s) = c • vc s) :
    ∃ k : ℤ, G.translationNumber = (k : ℝ) := by
  obtain ⟨c, _hc, hvc⟩ := h
  have hcabs : |c| = 1 := by
    have h1 : ‖vc (G s)‖ = ‖c • vc s‖ := by rw [hvc]
    rw [vc_norm, norm_smul_real, vc_norm, mul_one] at h1
    exact h1.symm
  have hcpm : c = 1 ∨ c = -1 := by
    have h2 : c ^ 2 = 1 := by rw [← sq_abs, hcabs]; norm_num
    exact eq_or_eq_neg_of_sq_eq_sq c 1 (by rw [h2]; norm_num)
  rcases hcpm with h1 | h1
  · have hvceq : vc (G s) = vc s := by rw [hvc, h1]; simp
    obtain ⟨m, hm⟩ := vc_eq_iff hvceq
    refine ⟨2 * m, ?_⟩
    have hGs : G s = s + ((2 * m : ℤ) : ℝ) := by
      rw [hm]; push_cast; ring
    rw [CircleDeg1Lift.translationNumber_of_eq_add_int (f := G) hGs]
  · have hvceq : vc (G s) = vc (s + 1) := by rw [hvc, h1, vc_add_one]; simp
    obtain ⟨m, hm⟩ := vc_eq_iff hvceq
    refine ⟨2 * m + 1, ?_⟩
    have hGs : G s = s + ((2 * m + 1 : ℤ) : ℝ) := by
      rw [hm]; push_cast; ring
    rw [CircleDeg1Lift.translationNumber_of_eq_add_int (f := G) hGs]

/-! ## The requested theorem -/

theorem posLiftTauInt {M : Matrix (Fin 2) (Fin 2) ℝ} {G : CircleDeg1Lift}
    (hG : Work.TMComp.RotBasics.IsPosLift M ⇑G) (hdet : M.det ≠ 0)
    (hlam : ∃ (l : ℝ) (v : Fin 2 → ℝ), v ≠ 0 ∧ M.mulVec v = l • v) :
    ∃ k : ℤ, G.translationNumber = (k : ℝ) := by
  obtain ⟨l, v, hv, hMv⟩ := hlam
  -- the eigenvector, read in `ℂ`
  have hw : toC v ≠ 0 := toC_ne_zero hv
  have hsmulv : smul M (toC v) = l • toC v := by
    have h := congrArg toC hMv
    rw [toC_mulVec, toC_const_smul] at h
    exact h
  -- a circle point lying in the direction of the eigenvector
  obtain ⟨s, r, hr, hrw⟩ := vcDirExists (toC v) hw
  -- `M` preserves that direction
  have hsl : smul M (vc s) = l • vc s := by
    have hkey : r • smul M (vc s) = r • (l • vc s) := by
      calc r • smul M (vc s)
          = smul M (r • vc s) := (smul_smul_real M r (vc s)).symm
        _ = smul M (toC v) := by rw [hrw]
        _ = l • toC v := hsmulv
        _ = l • (r • vc s) := by rw [hrw]
        _ = r • (l • vc s) := smul_comm l r (vc s)
    exact smul_right_injective ℂ (ne_of_gt hr) hkey
  have hne : smul M (vc s) ≠ 0 := smul_vc_ne_zero hdet s
  have hlne : l ≠ 0 := fun hl => hne (by rw [hsl, hl, zero_smul])
  -- hence `G s` presents the same circle point as `s`
  have hGfixed : ∃ c : ℝ, c ≠ 0 ∧ vc (G s) = c • vc s := by
    have hs : l • vc s = ‖l • vc s‖ • vc (G s) := by
      have h := hG s
      rwa [hsl] at h
    set n : ℝ := ‖l • vc s‖ with hn
    have hlnz : l • vc s ≠ 0 := hsl ▸ hne
    have hnne : n ≠ 0 := by rw [hn, norm_ne_zero_iff]; exact hlnz
    have hsn : l • vc s = n • vc (G s) := by rw [hn]; exact hs
    refine ⟨n⁻¹ * l, mul_ne_zero (inv_ne_zero hnne) hlne, ?_⟩
    have hkey : n • vc (G s) = n • ((n⁻¹ * l) • vc s) := by
      rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ hnne, one_mul]
      exact hsn.symm
    exact smul_right_injective ℂ hnne hkey
  exact tauInt_of_vc_scalar hGfixed

end Work.TMC14Core
