import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.tauGapDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false

namespace Work.BoseBoxFock

open scoped BigOperators
open MeasureTheory

/-!
# `Work.BoseBoxFock.row_of_deficit` — the lattice kinetic row from the deficit inequality

With `k_n = kmomInt ℓ n = ℓ⁻¹ • vec n = (2π/ℓ)n`, `τ_c(r) = c²·tauPhi (r/c)` (the *smoothed*
kinetic symbol of `TauProf.lean`), `tauRho c r = (r - 3c/2)² + c₀c²` its quadratic tail,
`tauPsi c = tauRho c - τ_c` the convexity defect (`≥ 0`) and `tauTheta c r = (c - r)₊²`, the two
pointwise identities

* `τ_c(r) = r² - 3cr + (9/4+c₀)c² - tauPsi c r`   (`tauRho_sub_tauPsi` + `tauRho_eq`),
* `fsKinCoeff c r = [r-c]₊² = (r-c)² - tauTheta c r`

turn the *row* `Σ_n ℓ⁻³ τ_c(‖k_n‖)G(k_n) ≤ (2π)⁻³∫[‖p‖-c]₊²G(p)` into a statement about the
first-moment deficit and the low-frequency mass.  Combined with the two (assumed) lattice/continuum
moment identities `L(1) = C(1)`, `L(‖·‖²) = C(‖·‖²)`, the row is *equivalent* to

    c·(3L(‖·‖) - 2C(‖·‖)) + L(tauPsi) - C(tauTheta) ≥ (5/4 + c₀)·c²·L(1),

which is exactly the hypothesis `hdef` of the theorem.  So the whole content of this file is the
(linear) bookkeeping: splitting the two absolutely convergent lattice series and the two
Bochner integrals into their four pieces and substituting the two moment identities.

The summability/integrability hypotheses are precisely the ones that make those splits legal
(`tsum_add`, `tsum_sub`, `tsum_mul_left`, `integral_add`, `integral_sub`, `integral_const_mul`).
-/

theorem row_of_deficit {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    (G : EuclideanSpace ℝ (Fin 3) → ℝ) (hG : ∀ p, 0 ≤ G p)
    (hS0 : (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * G (Work.BoseBoxFock.kmomInt ℓ n))
        = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), G p)
    (hS2 : (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2
          * G (Work.BoseBoxFock.kmomInt ℓ n))
        = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 * G p)
    (hs0 : Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * G (Work.BoseBoxFock.kmomInt ℓ n)))
    (hs1 : Summable (fun n : Fin 3 → ℤ =>
      (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ * G (Work.BoseBoxFock.kmomInt ℓ n)))
    (hs2 : Summable (fun n : Fin 3 → ℤ =>
      (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2 * G (Work.BoseBoxFock.kmomInt ℓ n)))
    (hsψ : Summable (fun n : Fin 3 → ℤ =>
      (ℓ ^ 3)⁻¹ * Work.BoseBoxFock.tauPsi c ‖Work.BoseBoxFock.kmomInt ℓ n‖
        * G (Work.BoseBoxFock.kmomInt ℓ n)))
    (hi0 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => G p))
    (hi1 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ * G p))
    (hi2 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 * G p))
    (hiθ : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => Work.BoseBoxFock.tauTheta c ‖p‖ * G p))
    (hdef : c * (3 * (∑' n : Fin 3 → ℤ,
              (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ * G (Work.BoseBoxFock.kmomInt ℓ n))
            - 2 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ * G p))
          + (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * Work.BoseBoxFock.tauPsi c ‖Work.BoseBoxFock.kmomInt ℓ n‖
              * G (Work.BoseBoxFock.kmomInt ℓ n))
          - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
              Work.BoseBoxFock.tauTheta c ‖p‖ * G p
        ≥ (5 / 4 + Work.BoseBoxFock.tauC0phi) * c ^ 2
            * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), G p)) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (c ^ 2 * Work.BoseBoxFock.tauPhi (‖Work.BoseBoxFock.kmomInt ℓ n‖ / c))
        * G (Work.BoseBoxFock.kmomInt ℓ n))
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * G p := by
  -- the pointwise identity for the smoothed kinetic symbol
  have hpt : ∀ r : ℝ, c ^ 2 * tauPhi (r / c)
      = r ^ 2 - 3 * c * r + (9 / 4 + tauC0phi) * c ^ 2 - tauPsi c r := by
    intro r
    rw [tauRho_sub_tauPsi, tauRho_eq]
    ring
  -- the four lattice densities
  set f0 : (Fin 3 → ℤ) → ℝ := fun n => (ℓ ^ 3)⁻¹ * G (kmomInt ℓ n) with hf0
  set f1 : (Fin 3 → ℤ) → ℝ := fun n => (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ * G (kmomInt ℓ n) with hf1
  set f2 : (Fin 3 → ℤ) → ℝ := fun n => (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ 2 * G (kmomInt ℓ n) with hf2
  set fψ : (Fin 3 → ℤ) → ℝ := fun n => (ℓ ^ 3)⁻¹ * tauPsi c ‖kmomInt ℓ n‖ * G (kmomInt ℓ n)
    with hfψ
  have hs0' : Summable f0 := by rw [hf0]; exact hs0
  have hs1' : Summable f1 := by rw [hf1]; exact hs1
  have hs2' : Summable f2 := by rw [hf2]; exact hs2
  have hsψ' : Summable fψ := by rw [hfψ]; exact hsψ
  -- the two moment identities
  have hS0' : (∑' n, f0 n) = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), G p := by
    simpa only [hf0] using hS0
  have hS2' : (∑' n, f2 n)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 * G p := by
    simpa only [hf2] using hS2
  -- and the deficit hypothesis
  have hdef' : c * (3 * (∑' n, f1 n)
        - 2 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ * G p))
      + (∑' n, fψ n)
      - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), tauTheta c ‖p‖ * G p
      ≥ (5 / 4 + tauC0phi) * c ^ 2
        * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), G p) := by
    simpa only [hf1, hfψ] using hdef
  -- the lattice side: the smoothed row splits into the three moments and the defect
  have hpt2 : ∀ n : Fin 3 → ℤ,
      (ℓ ^ 3)⁻¹ * (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c)) * G (kmomInt ℓ n)
        = f2 n - 3 * c * f1 n + ((9 / 4 + tauC0phi) * c ^ 2) * f0 n - fψ n := by
    intro n
    simp only [hf0, hf1, hf2, hfψ]
    rw [hpt (‖kmomInt ℓ n‖)]
    ring
  have hLHS : (∑' n : Fin 3 → ℤ,
        (ℓ ^ 3)⁻¹ * (c ^ 2 * tauPhi (‖kmomInt ℓ n‖ / c)) * G (kmomInt ℓ n))
      = (∑' n, f2 n) - 3 * c * (∑' n, f1 n)
        + ((9 / 4 + tauC0phi) * c ^ 2) * (∑' n, f0 n) - (∑' n, fψ n) := by
    rw [tsum_congr hpt2]
    rw [Summable.tsum_sub
          ((hs2'.sub (hs1'.mul_left (3 * c))).add (hs0'.mul_left ((9 / 4 + tauC0phi) * c ^ 2)))
          hsψ',
        Summable.tsum_add (hs2'.sub (hs1'.mul_left (3 * c)))
          (hs0'.mul_left ((9 / 4 + tauC0phi) * c ^ 2)),
        Summable.tsum_sub hs2' (hs1'.mul_left (3 * c)),
        hs1'.tsum_mul_left (3 * c), hs0'.tsum_mul_left ((9 / 4 + tauC0phi) * c ^ 2)]
  -- the pointwise splitting of the sharp kinetic coefficient
  have hfs : ∀ r : ℝ, Submission.BoseGases.fsKinCoeff c r = (r - c) ^ 2 - tauTheta c r := by
    intro r
    rw [Submission.BoseGases.fsKinCoeff, tauTheta]
    rcases le_or_gt r c with h | h
    · rw [max_eq_right (by linarith : r - c ≤ 0), max_eq_right (by linarith : (0 : ℝ) ≤ c - r)]
      ring
    · rw [max_eq_left (by linarith : (0 : ℝ) ≤ r - c), max_eq_left (by linarith : c - r ≤ 0)]
      ring
  have hptI : ∀ p : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.fsKinCoeff c ‖p‖ * G p
        = ((‖p‖ ^ 2 * G p - (2 * c) * (‖p‖ * G p)) + c ^ 2 * G p)
          - tauTheta c ‖p‖ * G p := by
    intro p
    rw [hfs ‖p‖]
    ring
  -- the continuum side
  have hINT : (∫ p : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.fsKinCoeff c ‖p‖ * G p)
      = (∫ p, ‖p‖ ^ 2 * G p) - 2 * c * (∫ p, ‖p‖ * G p)
        + c ^ 2 * (∫ p, G p) - (∫ p, tauTheta c ‖p‖ * G p) := by
    have h1 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        ‖p‖ ^ 2 * G p - (2 * c) * (‖p‖ * G p)) := hi2.sub (hi1.const_mul (2 * c))
    have h2 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => c ^ 2 * G p) :=
      hi0.const_mul (c ^ 2)
    have h3 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        (‖p‖ ^ 2 * G p - (2 * c) * (‖p‖ * G p)) + c ^ 2 * G p) := h1.add h2
    rw [integral_congr_ae (Filter.Eventually.of_forall hptI)]
    rw [integral_sub (f := fun p : EuclideanSpace ℝ (Fin 3) =>
          (‖p‖ ^ 2 * G p - (2 * c) * (‖p‖ * G p)) + c ^ 2 * G p)
        (g := fun p : EuclideanSpace ℝ (Fin 3) => tauTheta c ‖p‖ * G p) h3 hiθ]
    rw [integral_add (f := fun p : EuclideanSpace ℝ (Fin 3) =>
          ‖p‖ ^ 2 * G p - (2 * c) * (‖p‖ * G p))
        (g := fun p : EuclideanSpace ℝ (Fin 3) => c ^ 2 * G p) h1 h2]
    rw [integral_sub (f := fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 * G p)
        (g := fun p : EuclideanSpace ℝ (Fin 3) => (2 * c) * (‖p‖ * G p)) hi2
        (hi1.const_mul (2 * c))]
    rw [integral_const_mul, integral_const_mul]
  -- assembly: the row is exactly the deficit inequality
  rw [hLHS, hS0', hS2', hINT]
  linarith [hdef']

end Work.BoseBoxFock
