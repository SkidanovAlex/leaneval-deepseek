import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.boxWaveIntegralScaled
import Submission.Work.BoseBoxFock.L1Tails.latDoubleSum_re
import Submission.Work.BoseBoxFock.L1Tails.latPoly_star_mul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.boxLatPoly_normSq` — Parseval for the lattice trigonometric polynomial

The lattice plane waves `x ↦ e^{i⟪κ_n,x⟫}`, `κ_n = kappaL ℓ n = ℓ⁻¹ • vec n = (2π/ℓ) n`, are
**orthogonal on the box `boxL ℓ = [-ℓ/2,ℓ/2]³`** of volume `ℓ³`:

`∫_{boxL ℓ} e^{i⟪κ_k,x⟫} dx = ℓ³ δ_{k,0}`  (`Work.BoseBoxFock.L1Tails.boxWaveIntegralScaled`).

Hence the modulus square of the trigonometric polynomial
`latPoly ℓ S c x = ∑ n ∈ S, c n · e^{i⟪κ_n,x⟫}` has the Parseval integral

`∫_{boxL ℓ} ‖latPoly ℓ S c x‖² dx = ℓ³ ∑ n ∈ S, ‖c n‖²`.

This is the `(P2)` input of the `L¹`-weight tail chapter (`sources/boseDCF/bose_L1tails.md`, T3/T4):
it is what turns the *dual* trial function `ψ = φ_ℓ · latPoly ℓ S c` of the Coulomb-duality argument
into `Σ_{n∈S} ‖c n‖²` at one power of `ℓ³`.

## The proof, in three steps

* `boxWaveIntegralScaled` — the orthogonality `∫_{boxL ℓ} latWave (kappaL ℓ k) = ℓ³ δ_{k,0}`
  (via the scaling `x = ℓ y` to the unit cell and the factorised unit-cell integral).
* `latPoly_star_mul` — the pointwise expansion
  `conj (latPoly x) · latPoly x = ∑ n ∈ S, ∑ m ∈ S, conj (c n) · c m · latWave (kappaL ℓ (m−n)) x`.
* `latDoubleSum_re` — the Kronecker collapse of the resulting double sum to `ℓ³ ∑ ‖c n‖²`.

The assembly itself uses `conj z · z = ↑‖z‖²` (`Complex.conj_mul'`), the pull-out of the real part of
a complex set integral (`Work.BoseB4.setIntegral_re`, with `boxL ℓ` compact), and linearity of the
integral over the finite double sum (`MeasureTheory.integral_finsetSum`).
-/

namespace Work.BoseBoxFock.L1Tails

open MeasureTheory
open scoped Pointwise

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem boxLatPoly_normSq {ℓ : ℝ} (hℓ : 0 < ℓ) (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℂ) :
    ∫ x in Work.BoseK15.corpusBox.boxL ℓ, ‖Work.BoseBoxFock.L1Tails.latPoly ℓ S c x‖ ^ 2
      = ℓ ^ 3 * ∑ n ∈ S, ‖c n‖ ^ 2 := by
  -- `conj P · P` is continuous, hence integrable on the compact box.
  have hcont : Continuous (fun x : E3 =>
      (starRingEnd ℂ) (Work.BoseBoxFock.L1Tails.latPoly ℓ S c x)
        * Work.BoseBoxFock.L1Tails.latPoly ℓ S c x) := by
    have hP : Continuous (Work.BoseBoxFock.L1Tails.latPoly ℓ S c) :=
      (Work.BoseBoxFock.L1Tails.latPoly_contDiff ℓ S c).continuous
    exact (continuous_star.comp hP).mul hP
  have hFint : IntegrableOn (fun x : E3 =>
      (starRingEnd ℂ) (Work.BoseBoxFock.L1Tails.latPoly ℓ S c x)
        * Work.BoseBoxFock.L1Tails.latPoly ℓ S c x) (Work.BoseK15.corpusBox.boxL ℓ) :=
    hcont.continuousOn.integrableOn_compact (Work.BoseK15.corpusBox.boxL_compact ℓ)
  -- **Step 1.** `‖P x‖² = (conj P x · P x).re` and the real part comes out of the integral.
  have hstep1 : (∫ x in Work.BoseK15.corpusBox.boxL ℓ,
        ‖Work.BoseBoxFock.L1Tails.latPoly ℓ S c x‖ ^ 2)
      = (∫ x in Work.BoseK15.corpusBox.boxL ℓ,
          (starRingEnd ℂ) (Work.BoseBoxFock.L1Tails.latPoly ℓ S c x)
            * Work.BoseBoxFock.L1Tails.latPoly ℓ S c x).re := by
    rw [show (∫ x in Work.BoseK15.corpusBox.boxL ℓ, ‖Work.BoseBoxFock.L1Tails.latPoly ℓ S c x‖ ^ 2)
        = ∫ x in Work.BoseK15.corpusBox.boxL ℓ,
            ((starRingEnd ℂ) (Work.BoseBoxFock.L1Tails.latPoly ℓ S c x)
              * Work.BoseBoxFock.L1Tails.latPoly ℓ S c x).re from
      setIntegral_congr_fun (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)
        (fun x _ => by
          rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq])]
    exact Work.BoseB4.setIntegral_re (Work.BoseK15.corpusBox.boxL_measurableSet ℓ) _ hFint
  -- **Step 2.** Expansion into the difference momenta, then term-by-term integration.
  have hstep2 : (∫ x in Work.BoseK15.corpusBox.boxL ℓ,
        (starRingEnd ℂ) (Work.BoseBoxFock.L1Tails.latPoly ℓ S c x)
          * Work.BoseBoxFock.L1Tails.latPoly ℓ S c x)
      = ∑ n ∈ S, ∑ m ∈ S, (starRingEnd ℂ) (c n) * c m
          * (if m - n = 0 then ((ℓ ^ 3 : ℝ) : ℂ) else 0) := by
    rw [show (∫ x in Work.BoseK15.corpusBox.boxL ℓ,
          (starRingEnd ℂ) (Work.BoseBoxFock.L1Tails.latPoly ℓ S c x)
            * Work.BoseBoxFock.L1Tails.latPoly ℓ S c x)
        = ∫ x in Work.BoseK15.corpusBox.boxL ℓ,
            ∑ n ∈ S, ∑ m ∈ S, (starRingEnd ℂ) (c n) * c m
              * Work.BoseBoxFock.L1Tails.latWave (Work.BoseBoxFock.kappaL ℓ (m - n)) x from
      setIntegral_congr_fun (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)
        (fun x _ => latPoly_star_mul S c x)]
    have hAint : ∀ n m : Fin 3 → ℤ, Integrable (fun x : E3 =>
        (starRingEnd ℂ) (c n) * c m
          * Work.BoseBoxFock.L1Tails.latWave (Work.BoseBoxFock.kappaL ℓ (m - n)) x)
        (volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)) := by
      intro n m
      exact (((Work.BoseBoxFock.L1Tails.latWave_contDiff
          (Work.BoseBoxFock.kappaL ℓ (m - n))).continuous.const_mul
        ((starRingEnd ℂ) (c n) * c m)).continuousOn).integrableOn_compact
          (Work.BoseK15.corpusBox.boxL_compact ℓ)
    rw [MeasureTheory.integral_finsetSum S (fun n _ =>
      MeasureTheory.integrable_finsetSum S (fun m _ => hAint n m))]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [MeasureTheory.integral_finsetSum S (fun m _ => hAint n m)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MeasureTheory.integral_const_mul, boxWaveIntegralScaled hℓ (m - n)]
  -- **Step 3.** `m - n = 0 ↔ m = n`, then the Kronecker collapse.
  have hstep3 : (∑ n ∈ S, ∑ m ∈ S, (starRingEnd ℂ) (c n) * c m
        * (if m - n = 0 then ((ℓ ^ 3 : ℝ) : ℂ) else 0)).re = ℓ ^ 3 * ∑ n ∈ S, ‖c n‖ ^ 2 := by
    rw [← latDoubleSum_re ℓ S c]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hmn : m - n = 0
    · rw [if_pos hmn, if_pos (sub_eq_zero.mp hmn)]
    · rw [if_neg hmn, if_neg (fun hc => hmn (sub_eq_zero.mpr hc))]
  rw [hstep1, hstep2, hstep3]

end Work.BoseBoxFock.L1Tails
