import Mathlib
import Submission.Work.Drive.chordUnitDirDefs

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-! ## Elementary facts used below

The unit chord direction `chordUnitDir γ p = chordC γ p / ‖chordC γ p‖` is the quotient of the
complexified chord by its (Euclidean) length.  We record here that the complexified chord `chordC` is
the image of the difference of the two curve points under the complexification `toC`
(`Work.Drive.chordC_eq_toC`), and that the class `arg z / π` in `ℝ/ℤ` corresponds under `circleOf` to
the *square* of the unit vector `z / ‖z‖` (`Work.Drive.circleOf_arg_div_pi`), which is the "halving"
property of the church direction. -/

/-- The complexified chord is the complexification of the chord of the two curve points. -/
lemma chordC_eq_toC (γ : Circle → ℝ × ℝ) (p : ℝ × ℝ) :
    chordC γ p = toC (γ (Circle.exp p.1) - γ (Circle.exp p.2)) := by
  rw [chordC, toC]
  apply Complex.ext <;> simp

/-- `circleOf` of a real class is the exponential of `2πi t`. -/
lemma circleOf_coe_eq_exp (t : ℝ) :
    circleOf ((t : ℝ) : UnitAddCircle) = Complex.exp (((2 * Real.pi * t) : ℝ) * Complex.I) := by
  apply Complex.ext
  · rw [circleOf_coe_re, Complex.exp_ofReal_mul_I_re]
  · rw [circleOf_coe_im, Complex.exp_ofReal_mul_I_im]

/-- The unit vector `z / ‖z‖` is `exp (i arg z)` (a local form of
`Work.Drive.div_norm_eq_exp_arg`, proved directly from `Complex.norm_mul_exp_arg_mul_I`). -/
lemma div_norm_eq_exp_arg' (z : ℂ) (hz : z ≠ 0) :
    z / ((‖z‖ : ℝ) : ℂ) = Complex.exp (((z.arg : ℝ) : ℂ) * Complex.I) := by
  have hne : (((‖z‖ : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr hz
  rw [div_eq_iff hne, mul_comm]
  exact (Complex.norm_mul_exp_arg_mul_I z).symm

/-- **The class `arg z / π` of a non-zero complex number, read in the circle, is the square of its
unit vector.**  This is the "halving" identity: `circleOf` of the doubled direction `arg / π` is the
square of the undoubled unit direction `z / ‖z‖`. -/
lemma circleOf_arg_div_pi (z : ℂ) (hz : z ≠ 0) :
    circleOf ((Complex.arg z / Real.pi : ℝ) : UnitAddCircle)
      = (z / ((‖z‖ : ℝ) : ℂ)) ^ 2 := by
  rw [circleOf_coe_eq_exp]
  have harg : ((2 * Real.pi * (Complex.arg z / Real.pi)) : ℝ) = 2 * Complex.arg z := by
    field_simp
  rw [harg]
  have h2 : Complex.exp (((2 * Complex.arg z : ℝ) : ℂ) * Complex.I)
      = (Complex.exp (((Complex.arg z : ℝ) : ℂ) * Complex.I)) ^ 2 := by
    rw [show (((2 * Complex.arg z : ℝ)) : ℂ) * Complex.I
        = ((2 : ℕ) : ℂ) * (((Complex.arg z : ℝ) : ℂ) * Complex.I) by push_cast; ring]
    rw [Complex.exp_nat_mul]
  rw [h2, div_norm_eq_exp_arg' z hz]

open Manifold in
open scoped Manifold ContDiff in
/-- **The undoubled chord direction is smooth off the diagonal and halves `dirC`.**  With
`Work.Drive.chordUnitDir γ p = chordC γ p / ‖chordC γ p‖`, where `Work.Drive.chordC γ p` is the chord
`γ (Circle.exp p.1) - γ (Circle.exp p.2) ∈ ℝ²` read as a **complex** number (so that `‖·‖` is the
Euclidean norm — `ℝ × ℝ` carries the sup norm in Mathlib, and the identity below is *false* for the
sup norm), the unit complex number in the direction of the chord is `C^∞` off the diagonal, its square
is `Work.Drive.circleOf (dirC (γ x - γ y))` — i.e. `chordUnitDir γ p` is a *halving* of the doubled
chord direction `dirC` — and it has unit norm.

This is the data that `Work.Drive.contMDiffAt_cappingSpace_configPiece` and
`Work.Drive.lensToProj_confTorus` need in order to make the strip chart a smooth map into
`CappingSpace` (`Submission/Work/Drive/CAPPING_ANALYSIS.md` §2): `Work.Drive.lensToProj_confTorus`
gives `lensToProj ⟦inr (d, η)⟧ = mk ℝ (confProjVecOf u d) ⋯` for any `u` with `u ^ 2 = circleOf η`, and
the present statement supplies the smooth `u := chordUnitDir γ p` for `η := dirC (γ x - γ y)`.

Route: `Work.Drive.chordC γ` is smooth on `ℝ × ℝ` (difference of `γ ∘ Circle.exp` in the two
variables, read in `ℂ`) and non-vanishing on `{p | Circle.exp p.1 ≠ Circle.exp p.2}` by injectivity of
`γ` (from `hγ.isEmbedding.injective`); its complex norm is smooth and positive there, so the quotient
`chordUnitDir γ` is `C^∞` and of norm `1`; the halving identity is `dirCz`-arithmetic: for `v ≠ 0`,
`circleOf (dirC v) = Complex.exp (2 * π * (arg v / π) * I) = Complex.exp (2 * arg v * I) = (v / ‖v‖) ^ 2`
(using `Work.Drive.circleOf_coe_re`/`_im`, or the existing identity `div_norm_eq_exp_arg` of
`Submission/Work/Drive/winding_eq_crossing_sum.lean`). -/
theorem contDiffOn_chordUnitDir (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.chordUnitDir γ)
        {p : ℝ × ℝ | Circle.exp p.1 ≠ Circle.exp p.2} ∧
      (∀ p : ℝ × ℝ, Circle.exp p.1 ≠ Circle.exp p.2 →
        Work.Drive.circleOf (Submission.Collision.dirC (γ (Circle.exp p.1) - γ (Circle.exp p.2)))
          = (Work.Drive.chordUnitDir γ p) ^ 2) ∧
      (∀ p : ℝ × ℝ, Circle.exp p.1 ≠ Circle.exp p.2 → ‖Work.Drive.chordUnitDir γ p‖ = 1) := by
  -- injectivity of `γ` and smoothness of the complexified chord
  have hγinj : Function.Injective γ := hγ.isEmbedding.injective
  have hbase : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => γ (Circle.exp t)) :=
    (hγ.contMDiff.comp contMDiff_circleExp).contDiff
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => γ (Circle.exp p.1)) :=
    hbase.comp contDiff_fst
  have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => γ (Circle.exp p.2)) :=
    hbase.comp contDiff_snd
  have hchordC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => chordC γ p) :=
    (Complex.equivRealProdCLM.symm.contDiff).comp (hA.sub hB)
  -- the chord does not vanish off the diagonal
  have hCne : ∀ p : ℝ × ℝ, Circle.exp p.1 ≠ Circle.exp p.2 → chordC γ p ≠ 0 := by
    intro p hp h
    have h' : toC (γ (Circle.exp p.1) - γ (Circle.exp p.2)) = 0 := by
      rw [← chordC_eq_toC]; exact h
    exact hp (hγinj (sub_eq_zero.mp (toC_eq_zero_iff.mp h')))
  -- smoothness of the squared Euclidean norm `Complex.normSq (chordC γ p)` of the chord
  have hre : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => (chordC γ p).re) :=
    Complex.reCLM.contDiff.comp hchordC
  have him : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => (chordC γ p).im) :=
    Complex.imCLM.contDiff.comp hchordC
  have hQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Complex.normSq (chordC γ p)) := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (chordC γ p).re ^ 2 + (chordC γ p).im ^ 2) :=
      (hre.pow 2).add (him.pow 2)
    convert h using 1
    ext p
    rw [Complex.normSq_apply]
    ring
  -- the smoothness clause: divide the chord by its (positive, smooth) length
  have hkey1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chordUnitDir γ)
      {p : ℝ × ℝ | Circle.exp p.1 ≠ Circle.exp p.2} := by
    set U : Set (ℝ × ℝ) := {p : ℝ × ℝ | Circle.exp p.1 ≠ Circle.exp p.2} with hU
    have hQne : ∀ p ∈ U, Complex.normSq (chordC γ p) ≠ 0 := by
      intro p hp h
      exact hCne p hp ((Complex.normSq_eq_zero).mp h)
    have hsqrt : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => Real.sqrt (Complex.normSq (chordC γ p))) U :=
      hQ.contDiffOn.sqrt hQne
    have hnormOn : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => ((‖chordC γ p‖ : ℝ) : ℂ)) U :=
      ((Complex.ofRealCLM.contDiff).comp_contDiffOn hsqrt).congr (fun p hp => rfl)
    have hinv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => ((((‖chordC γ p‖ : ℝ)) : ℂ))⁻¹) U :=
      hnormOn.inv (fun p hp h =>
        norm_ne_zero_iff.mpr (hCne p hp) (Complex.ofReal_eq_zero.mp h))
    have hdiv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => chordC γ p * ((((‖chordC γ p‖ : ℝ)) : ℂ))⁻¹) U :=
      hchordC.contDiffOn.mul hinv
    exact hdiv.congr (fun p hp => by rw [chordUnitDir, div_eq_mul_inv])
  refine ⟨hkey1, ?_, ?_⟩
  · -- the halving identity
    intro p hp
    have hne := hCne p hp
    rw [chordUnitDir]
    exact circleOf_arg_div_pi (chordC γ p) hne
  · -- unit norm
    intro p hp
    have hne := hCne p hp
    rw [chordUnitDir, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr hne)]

end Work.Drive
