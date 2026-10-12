import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.ShiftDefs
import Submission.Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt
import Submission.Work.OneBodyKin.kinFT_sub_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.Kin.Expand` — the bilinear expansion of `bsW`

For `F ≥ 0` the map `h ↦ bsW F h = ∫_p F‖p‖·‖bsPsi h p‖²` is the quadratic form of the spectral
symbol `F(√−Δ)`.  This module supplies its bilinear companion

`bsWBilin F a b = ∫_p F‖p‖·Re⟨bsPsi a p, bsPsi b p⟩`

together with the facts the bridge of `Submission/Work/BoseFixR/KINETIC_HALF_DESIGN.md` §2 needs:

* the exact expansion `bsW F (a+b) = bsW F a + 2·bsWBilin F a b + bsW F b`: the sliding state
  splits as `χ_B(u)(ψ−m_u) = χ_{d,u}ξ + (M−m_u)·χ_B(u)`, and the corrections are the cross
  (`Cform`) and the mass (`Dform`) terms;
* the Cauchy–Schwarz bound `|bsWBilin F a b| ≤ √(bsW F a)·√(bsW F b)`
  (so that `|Cform| ≤ 2√(Dform)·√(family form)` and `Dform ≤ C_win·gapBare`).
-/

noncomputable section

open MeasureTheory
open scoped Topology Real ENNReal

namespace Work.BoseFixR

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open Work.BSKinetic.Decomp

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## 1. Additivity of `bsPsi` -/

/-- **`bsPsi` is additive on smooth compactly supported states.** -/
lemma bsPsi_add {a b : ℝ³ → ℝ} (had : ContDiff ℝ (⊤ : ENat) a) (hac : HasCompactSupport a)
    (hbd : ContDiff ℝ (⊤ : ENat) b) (hbc : HasCompactSupport b) (p : ℝ³) :
    bsPsi (fun z => a z + b z) p = bsPsi a p + bsPsi b p := by
  have h1 : Integrable (fun z : ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (a z : ℂ)) :=
    integrable_phase_mul had hac p
  have h2 : Integrable (fun z : ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (b z : ℂ)) :=
    integrable_phase_mul hbd hbc p
  rw [bsPsi, bsPsi, bsPsi, kinFT, kinFT, kinFT]
  have hpt : ∀ z : ℝ³,
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (((a z + b z : ℝ) : ℂ))
        = Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((a z : ℝ) : ℂ)
          + Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((b z : ℝ) : ℂ) := by
    intro z; push_cast; ring
  rw [show (∫ z : ℝ³, Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (((a z + b z : ℝ) : ℂ)))
      = ∫ z : ℝ³, (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((a z : ℝ) : ℂ)
          + Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * ((b z : ℝ) : ℂ)) from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_add h1 h2]

/-! ## 2. The bilinear companion of `bsW` -/

/-- **The bilinear form of the spectral symbol** `F(√−Δ)` applied to a pair of one-body states:
`bsWBilin F a b = ∫_p F‖p‖·Re(bsPsi a p · conj (bsPsi b p))`.

`bsWBilin F a a = bsW F a` and, for `0 ≤ F`, `|bsWBilin F a b| ≤ √(bsW F a)·√(bsW F b)`. -/
def bsWBilin (F : ℝ → ℝ) (a b : ℝ³ → ℝ) : ℝ :=
  ∫ p : ℝ³, F ‖p‖ * (bsPsi a p * star (bsPsi b p)).re

/-- `bsWBilin F a a = bsW F a`. -/
lemma bsWBilin_self (F : ℝ → ℝ) (a : ℝ³ → ℝ) :
    bsWBilin F a a = bsW F a := by
  rw [bsWBilin, bsW]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  change F ‖p‖ * (bsPsi a p * star (bsPsi a p)).re = F ‖p‖ * ‖bsPsi a p‖ ^ 2
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- **Symmetry** of the bilinear form. -/
lemma bsWBilin_comm (F : ℝ → ℝ) (a b : ℝ³ → ℝ) :
    bsWBilin F a b = bsWBilin F b a := by
  rw [bsWBilin, bsWBilin]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  change F ‖p‖ * (bsPsi a p * star (bsPsi b p)).re
    = F ‖p‖ * (bsPsi b p * star (bsPsi a p)).re
  congr 1
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-! ## 3. The exact expansion -/

/-- **The pointwise expansion of the squared norm**:
`‖x+y‖² = ‖x‖² + 2·Re(x·conj y) + ‖y‖²`. -/
lemma normSq_add_pointwise (x y : ℂ) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * (x * star y).re + ‖y‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.star_def, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

/-- **The exact bilinear expansion of `bsW` on a sum.**

`bsW F (a+b) = bsW F a + 2·bsWBilin F a b + bsW F b`: the pointwise identity
`‖x+y‖² = ‖x‖² + 2Re(x·conj y) + ‖y‖²` in `p`-space, integrated against `F‖p‖`. -/
theorem bsW_add {F : ℝ → ℝ} {a b : ℝ³ → ℝ}
    (had : ContDiff ℝ (⊤ : ENat) a) (hac : HasCompactSupport a)
    (hbd : ContDiff ℝ (⊤ : ENat) b) (hbc : HasCompactSupport b)
    (hia : Integrable (fun p : ℝ³ => F ‖p‖ * ‖bsPsi a p‖ ^ 2))
    (hib : Integrable (fun p : ℝ³ => F ‖p‖ * ‖bsPsi b p‖ ^ 2))
    (hii : Integrable (fun p : ℝ³ =>
      F ‖p‖ * (bsPsi a p * star (bsPsi b p)).re)) :
    bsW F (fun z => a z + b z)
      = bsW F a + 2 * bsWBilin F a b + bsW F b := by
  have hpt : ∀ p : ℝ³, F ‖p‖ * ‖bsPsi (fun z => a z + b z) p‖ ^ 2
      = F ‖p‖ * ‖bsPsi a p‖ ^ 2 + 2 * (F ‖p‖ * (bsPsi a p * star (bsPsi b p)).re)
        + F ‖p‖ * ‖bsPsi b p‖ ^ 2 := by
    intro p
    rw [bsPsi_add had hac hbd hbc p, normSq_add_pointwise]
    ring
  have hcongr : (∫ p : ℝ³, F ‖p‖ * ‖bsPsi (fun z => a z + b z) p‖ ^ 2)
      = ∫ p : ℝ³, (F ‖p‖ * ‖bsPsi a p‖ ^ 2
          + 2 * (F ‖p‖ * (bsPsi a p * star (bsPsi b p)).re) + F ‖p‖ * ‖bsPsi b p‖ ^ 2) :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hsplit : (∫ p : ℝ³, (F ‖p‖ * ‖bsPsi a p‖ ^ 2
        + 2 * (F ‖p‖ * (bsPsi a p * star (bsPsi b p)).re) + F ‖p‖ * ‖bsPsi b p‖ ^ 2))
      = (∫ p : ℝ³, F ‖p‖ * ‖bsPsi a p‖ ^ 2)
        + 2 * (∫ p : ℝ³, F ‖p‖ * (bsPsi a p * star (bsPsi b p)).re)
        + ∫ p : ℝ³, F ‖p‖ * ‖bsPsi b p‖ ^ 2 := by
    have h1 : Integrable (fun p : ℝ³ => F ‖p‖ * ‖bsPsi a p‖ ^ 2
        + 2 * (F ‖p‖ * (bsPsi a p * star (bsPsi b p)).re)) := hia.add (hii.const_mul 2)
    rw [show (∫ p : ℝ³, (F ‖p‖ * ‖bsPsi a p‖ ^ 2
          + 2 * (F ‖p‖ * (bsPsi a p * star (bsPsi b p)).re) + F ‖p‖ * ‖bsPsi b p‖ ^ 2))
        = ∫ p : ℝ³, (fun q : ℝ³ => F ‖q‖ * ‖bsPsi a q‖ ^ 2
              + 2 * (F ‖q‖ * (bsPsi a q * star (bsPsi b q)).re)) p
            + (fun q : ℝ³ => F ‖q‖ * ‖bsPsi b q‖ ^ 2) p from rfl]
    rw [integral_add h1 hib]
    congr 1
    rw [show (∫ p : ℝ³, (fun q : ℝ³ => F ‖q‖ * ‖bsPsi a q‖ ^ 2
              + 2 * (F ‖q‖ * (bsPsi a q * star (bsPsi b q)).re)) p)
        = ∫ p : ℝ³, (fun q : ℝ³ => F ‖q‖ * ‖bsPsi a q‖ ^ 2) p
            + (fun q : ℝ³ => 2 * (F ‖q‖ * (bsPsi a q * star (bsPsi b q)).re)) p from rfl]
    rw [integral_add hia (hii.const_mul 2), integral_const_mul]
  rw [bsW, bsW, bsW, bsWBilin, hcongr, hsplit]

/-! ## 4. Cauchy–Schwarz for the bilinear form -/

/-- **Cauchy–Schwarz for `bsWBilin`**: for `F ≥ 0`,
`|bsWBilin F a b| ≤ √(bsW F a)·√(bsW F b)`. -/
theorem bsWBilin_abs_le {F : ℝ → ℝ} (hF : ∀ r, 0 ≤ F r) {a b : ℝ³ → ℝ}
    (hia : Integrable (fun p : ℝ³ => F ‖p‖ * ‖bsPsi a p‖ ^ 2))
    (hib : Integrable (fun p : ℝ³ => F ‖p‖ * ‖bsPsi b p‖ ^ 2))
    (hii : Integrable (fun p : ℝ³ =>
      F ‖p‖ * (bsPsi a p * star (bsPsi b p)).re))
    (hmea : AEStronglyMeasurable (fun p : ℝ³ => Real.sqrt (F ‖p‖) * ‖bsPsi a p‖)
      (volume : Measure ℝ³))
    (hmeb : AEStronglyMeasurable (fun p : ℝ³ => Real.sqrt (F ‖p‖) * ‖bsPsi b p‖)
      (volume : Measure ℝ³)) :
    |bsWBilin F a b| ≤ Real.sqrt (bsW F a) * Real.sqrt (bsW F b) := by
  have hpt_le : ∀ p : ℝ³, (bsPsi a p * star (bsPsi b p)).re ≤ ‖bsPsi a p‖ * ‖bsPsi b p‖ := by
    intro p
    calc (bsPsi a p * star (bsPsi b p)).re ≤ |(bsPsi a p * star (bsPsi b p)).re| := le_abs_self _
      _ ≤ ‖bsPsi a p * star (bsPsi b p)‖ := Complex.abs_re_le_norm _
      _ = ‖bsPsi a p‖ * ‖bsPsi b p‖ := by
          rw [Complex.norm_mul, Complex.star_def, Complex.norm_conj]
  have hpt_ge : ∀ p : ℝ³, -(‖bsPsi a p‖ * ‖bsPsi b p‖) ≤ (bsPsi a p * star (bsPsi b p)).re := by
    intro p
    have h := Complex.abs_re_le_norm (bsPsi a p * star (bsPsi b p))
    rw [Complex.norm_mul, Complex.star_def, Complex.norm_conj] at h
    exact (abs_le.mp h).1
  have hbound : ∀ p : ℝ³,
      |F ‖p‖ * (bsPsi a p * star (bsPsi b p)).re| ≤ F ‖p‖ * (‖bsPsi a p‖ * ‖bsPsi b p‖) := by
    intro p
    rw [abs_mul, abs_of_nonneg (hF ‖p‖)]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hpt_ge p, hpt_le p⟩) (hF ‖p‖)
  have hmemA : MemLp (fun p : ℝ³ => Real.sqrt (F ‖p‖) * ‖bsPsi a p‖) 2 (volume : Measure ℝ³) := by
    refine (memLp_two_iff_integrable_sq hmea).mpr ?_
    refine hia.congr (Filter.Eventually.of_forall fun p => ?_)
    change F ‖p‖ * ‖bsPsi a p‖ ^ 2 = (Real.sqrt (F ‖p‖) * ‖bsPsi a p‖) ^ 2
    rw [mul_pow, Real.sq_sqrt (hF ‖p‖)]
  have hmemB : MemLp (fun p : ℝ³ => Real.sqrt (F ‖p‖) * ‖bsPsi b p‖) 2 (volume : Measure ℝ³) := by
    refine (memLp_two_iff_integrable_sq hmeb).mpr ?_
    refine hib.congr (Filter.Eventually.of_forall fun p => ?_)
    change F ‖p‖ * ‖bsPsi b p‖ ^ 2 = (Real.sqrt (F ‖p‖) * ‖bsPsi b p‖) ^ 2
    rw [mul_pow, Real.sq_sqrt (hF ‖p‖)]
  have hprod : (fun p : ℝ³ => (Real.sqrt (F ‖p‖) * ‖bsPsi a p‖) * (Real.sqrt (F ‖p‖) * ‖bsPsi b p‖))
      = fun p : ℝ³ => F ‖p‖ * (‖bsPsi a p‖ * ‖bsPsi b p‖) := by
    funext p
    have h1 : Real.sqrt (F ‖p‖) * Real.sqrt (F ‖p‖) = F ‖p‖ := by
      rw [← sq, Real.sq_sqrt (hF ‖p‖)]
    calc (Real.sqrt (F ‖p‖) * ‖bsPsi a p‖) * (Real.sqrt (F ‖p‖) * ‖bsPsi b p‖)
        = (Real.sqrt (F ‖p‖) * Real.sqrt (F ‖p‖)) * (‖bsPsi a p‖ * ‖bsPsi b p‖) := by ring
      _ = F ‖p‖ * (‖bsPsi a p‖ * ‖bsPsi b p‖) := by rw [h1]
  have hnm : Integrable (fun p : ℝ³ => F ‖p‖ * (‖bsPsi a p‖ * ‖bsPsi b p‖)) :=
    (hmemA.integrable_mul hmemB).congr (Filter.Eventually.of_forall fun p => (hprod ▸ rfl))
  have hmain : |bsWBilin F a b| ≤ ∫ p : ℝ³, F ‖p‖ * (‖bsPsi a p‖ * ‖bsPsi b p‖) := by
    rw [bsWBilin]
    refine le_trans ?_ (MeasureTheory.integral_mono hii.abs hnm hbound)
    simpa [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm
        (fun p : ℝ³ => F ‖p‖ * (bsPsi a p * star (bsPsi b p)).re)
  have hcs := Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt hmemA hmemB
  have hvalA : (∫ p : ℝ³, (Real.sqrt (F ‖p‖) * ‖bsPsi a p‖) ^ 2)
      = ∫ p : ℝ³, F ‖p‖ * ‖bsPsi a p‖ ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun p => by
      change (Real.sqrt (F ‖p‖) * ‖bsPsi a p‖) ^ 2 = F ‖p‖ * ‖bsPsi a p‖ ^ 2
      rw [mul_pow, Real.sq_sqrt (hF ‖p‖)])
  have hvalB : (∫ p : ℝ³, (Real.sqrt (F ‖p‖) * ‖bsPsi b p‖) ^ 2)
      = ∫ p : ℝ³, F ‖p‖ * ‖bsPsi b p‖ ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun p => by
      change (Real.sqrt (F ‖p‖) * ‖bsPsi b p‖) ^ 2 = F ‖p‖ * ‖bsPsi b p‖ ^ 2
      rw [mul_pow, Real.sq_sqrt (hF ‖p‖)])
  rw [hvalA, hvalB] at hcs
  rw [← hprod] at hmain
  rw [bsW, bsW]
  refine hmain.trans (le_trans (le_of_eq ?_) hcs)
  rw [abs_of_nonneg (MeasureTheory.integral_nonneg fun p =>
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)))]

end Work.BoseFixR
