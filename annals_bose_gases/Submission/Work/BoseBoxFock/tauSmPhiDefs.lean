import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.TauProf
import Submission.Work.SmallBoxBogolubovKinetic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.tauSmPhi` — the kinetic symbol of the honest model at the **explicit** profile

`Defs.tauSm` is built from `tauProf = tauProf`, whose only usable
properties are the six of `exists_tauProf`; the *pointwise envelope* of those six properties is
`tauEnvWorst`, and it is an admissible profile, so every statement about `tauSm` must survive
replacing the profile by `tauEnvWorst`.  The kinetic row does **not**: the envelope reading fails
by `~1 %` (two independent review refutations plus the adversarial scan
`ScratchL5/adv2.py`; see `FINDING_L5_numerics.md` §2bis).  The repair is to use the *explicit*
profile `tauPhi = (·₊)² ⋆ K` (`TauProf.lean`), whose six properties are proved there and whose
transition values (`tauPhi 1.5 ≈ 0.0067` vs the envelope's `0.25`) are what the row needs.

This module only fixes the *name* of the repaired symbol and its elementary API:

* `tauSmPhi eT s d ℓ k` — `tauSm` with `tauProf ↦ tauPhi`;
* `tauSmPhi_eq_twoScale` — its two-scale unfolding;
* `tauSmPhi_eq_of_norm_eq` — it is radial;
* `sq_mul_tauPhi_le_fsKinCoeff` — the scaled pointwise bound `c²·tauPhi(r/c) ≤ [r−c]₊²`;
* `tauSmPhi_le_fsKinCoeff` — the same for the two-scale symbol.

After the (lead-owned) one-line change `Defs.tauProf := tauPhi`, `tauSmPhi` and `Defs.tauSm`
coincide definitionally; the name exists so that the row can be stated and proved before that
change is applied.
-/

noncomputable section

open scoped Real

namespace Work.BoseBoxFock

/-- The kinetic symbol of the honest model at the **explicit** profile `tauPhi` (the repaired
`Defs.tauSm`).  `tauSmPhi eT s d ℓ k = (1−eT)·c₁²·tauPhi(‖k‖/c₁) + eT·c₂²·tauPhi(‖k‖/c₂)` with
`c₁ = (2sℓ)⁻¹`, `c₂ = (2dsℓ)⁻¹`. -/
def tauSmPhi (eT s d ℓ : ℝ) (k : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (1 - eT) * ((2 * s * ℓ)⁻¹) ^ 2 * tauPhi (‖k‖ / (2 * s * ℓ)⁻¹)
    + eT * ((2 * d * s * ℓ)⁻¹) ^ 2 * tauPhi (‖k‖ / (2 * d * s * ℓ)⁻¹)

/-- The defining two-scale unfolding of `tauSmPhi`. -/
lemma tauSmPhi_eq_twoScale (eT s d ℓ : ℝ) (k : EuclideanSpace ℝ (Fin 3)) :
    tauSmPhi eT s d ℓ k
      = (1 - eT) * ((2 * s * ℓ)⁻¹) ^ 2 * tauPhi (‖k‖ / (2 * s * ℓ)⁻¹)
        + eT * ((2 * d * s * ℓ)⁻¹) ^ 2 * tauPhi (‖k‖ / (2 * d * s * ℓ)⁻¹) := rfl

/-- The symbol only depends on `‖k‖`. -/
lemma tauSmPhi_eq_of_norm_eq (eT s d ℓ : ℝ) {k k' : EuclideanSpace ℝ (Fin 3)}
    (h : ‖k‖ = ‖k'‖) : tauSmPhi eT s d ℓ k = tauSmPhi eT s d ℓ k' := by
  rw [tauSmPhi, tauSmPhi, h]

/-- **The scaled pointwise bound**: `c²·tauPhi(r/c) ≤ [r−c]₊²` for `c > 0` (`tauPhi_le`). -/
lemma sq_mul_tauPhi_le_fsKinCoeff {c r : ℝ} (hc : 0 < c) :
    c ^ 2 * tauPhi (r / c) ≤ Submission.BoseGases.fsKinCoeff c r := by
  rcases le_or_gt r c with hle | hlt
  · have hr : r / c ≤ 1 := (div_le_one hc).mpr hle
    have hz : tauPhi (r / c) = 0 := tauPhi_zero_of_le_one (r / c) hr
    have h0 : (0 : ℝ) ≤ Submission.BoseGases.fsKinCoeff c r := by
      rw [Submission.BoseGases.fsKinCoeff]; exact sq_nonneg _
    rw [hz, mul_zero]; exact h0
  · have h0 : (0 : ℝ) ≤ r / c - 1 := by
      have : (1 : ℝ) ≤ r / c := (le_div_iff₀ hc).mpr (by linarith)
      linarith
    have h1 : tauPhi (r / c) ≤ (r / c - 1) ^ 2 := by
      have hh := tauPhi_le (r / c)
      rwa [max_eq_right h0] at hh
    have h2 : c ^ 2 * (r / c - 1) ^ 2 = (r - c) ^ 2 := by field_simp
    have h3 : Submission.BoseGases.fsKinCoeff c r = (r - c) ^ 2 := by
      rw [Submission.BoseGases.fsKinCoeff, max_eq_left (by linarith : (0 : ℝ) ≤ r - c)]
    rw [h3]
    calc c ^ 2 * tauPhi (r / c) ≤ c ^ 2 * (r / c - 1) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
      _ = (r - c) ^ 2 := h2

/-- **The trivial majorant by the kinetic form**: `c²·tauPhi(r/c) ≤ r²` for `c > 0`, `r ≥ 0`
(`tauPhi_le` gives `≤ (max 0 (r−c))² ≤ r²`).  This is the bound that makes the windowed kinetic row
follow from the *kinetic form* of the state whenever the `neuWord` credit dominates. -/
lemma sq_mul_tauPhi_le_sq {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    c ^ 2 * tauPhi (r / c) ≤ r ^ 2 := by
  have h1 : tauPhi (r / c) ≤ (max 0 (r / c - 1)) ^ 2 := tauPhi_le (r / c)
  have h2 : c ^ 2 * (max 0 (r / c - 1)) ^ 2 ≤ r ^ 2 := by
    rcases le_or_gt (r - c) 0 with h | h
    · have hz : max 0 (r / c - 1) = 0 := by
        apply max_eq_left
        have hrc : r / c ≤ 1 := by rw [div_le_one hc]; linarith
        linarith
      rw [hz]; simpa using sq_nonneg r
    · have hpos : (0 : ℝ) ≤ r / c - 1 := by
        have : (1 : ℝ) ≤ r / c := (le_div_iff₀ hc).mpr (by linarith)
        linarith
      have heq : c ^ 2 * (r / c - 1) ^ 2 = (r - c) ^ 2 := by field_simp
      rw [max_eq_right hpos, heq]
      nlinarith [sq_nonneg (r - c), hr]
  exact le_trans (mul_le_mul_of_nonneg_left h1 (sq_nonneg c)) h2

/-- `tauSmPhi ≤ fsKinCoeff`: the smoothed two-scale symbol is below FS's sharp one at the same two
scales. -/
lemma tauSmPhi_le_fsKinCoeff {eT s d ℓ : ℝ} (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1)
    (hs : 0 < s) (hd : 0 < d) (hℓ : 0 < ℓ) (k : EuclideanSpace ℝ (Fin 3)) :
    tauSmPhi eT s d ℓ k
      ≤ (1 - eT) * Submission.BoseGases.fsKinCoeff ((2 * s * ℓ)⁻¹) ‖k‖
        + eT * Submission.BoseGases.fsKinCoeff ((2 * d * s * ℓ)⁻¹) ‖k‖ := by
  have h1 : ((2 * s * ℓ)⁻¹ : ℝ) ^ 2 * tauPhi (‖k‖ / (2 * s * ℓ)⁻¹)
      ≤ Submission.BoseGases.fsKinCoeff ((2 * s * ℓ)⁻¹) ‖k‖ :=
    sq_mul_tauPhi_le_fsKinCoeff (by positivity)
  have h0 : ((2 * d * s * ℓ)⁻¹ : ℝ) ^ 2 * tauPhi (‖k‖ / (2 * d * s * ℓ)⁻¹)
      ≤ Submission.BoseGases.fsKinCoeff ((2 * d * s * ℓ)⁻¹) ‖k‖ :=
    sq_mul_tauPhi_le_fsKinCoeff (by positivity)
  have h1' := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 - eT)
  have h0' := mul_le_mul_of_nonneg_left h0 heT0
  rw [tauSmPhi]
  linarith [h1', h0']

end Work.BoseBoxFock
