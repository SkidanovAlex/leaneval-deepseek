import ChallengeDeps
import Submission.NewtonCoulomb
import Submission.Work.SmallBoxBogolubovLayer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-260 part 6 — the D1 main-term atom: the `½(1+C(R/s)²)·g0w0Mass`
coefficient bound in the real-space Newtonian form

The `−½(1+…)g0w0Mass(N̂+1)N̂/s³` leading term of
`lm_appbogolubov_refined_target` (FS eq:refinedaprioribog) has as its mass
coefficient, in the corpus's real-space Newtonian form (Session-228/229
dictionary: `¼(2π)⁻³∫Ŵ₁²/p² = ¼∬W₁W₁/(4π|x−y|)`, the 4π-normalised Newtonian
double energy):

    coeff(W₁) := ½ · (1/(8π)) · ∬_xy W₁(x)W₁(y) / ‖x−y‖

with `W₁ := wScaled s (g0 v h)` (the χ-renormalised kernel `g₀/(χ⋆χ(·/s))`).
`NewtonCoulomb.i2_integral_xspace_fs` is the corpus eq:I2-integral leaf:
`|(1/(8π))∬W₁W₁K − g0w0Mass| ≤ δ(2+δ)·g0w0Mass`, `δ := 2C(R/s)²`, from the
χ-Taylor (`ConvChiBound.conv3chi_second_order_bound` supplies the `hT`
hypothesis).  This module packages the coefficient:

  * `g0w0Mass_nonneg` — `0 ≤ g0w0Mass v h`
    (`ScatGChosen.chosen_gomega_integral_bounds` + the `g0`-def);
  * **`mainMassCoeff_le`** — `coeff(W₁) ≤ ½(1+δ(2+δ))·g0w0Mass`
    (exact from `i2_integral_xspace_fs`);
  * **`mainMassCoeff_le_coarse`** — `coeff(W₁) ≤ ½(1+6C(R/s)²)·g0w0Mass`
    (`δ ≤ 1` via `hcond`), the corpus form of FS's `½(1+C(R/(dℓ))²)ĝω(0)`
    with `ℓ := s`.

Multiplying by the count factor `(N̂+1)N̂/s³` (the b-mode commutator
normalisation) gives the leading term of the target; the `(1+C·c0·(av))`
second factor is the `|p| > 2c`-lattice correction of the next module
(`boxModeCoeff ≤ (s²/(π²‖k‖²))·(1+4c·s/(π‖k‖))`-type, feeding the
log/`c0³` bracket).  The per-mode Fock2Mode instantiation at the box-mode
`𝒜(k)` coefficients attaches afterwards per SmallBoxDesignNote part 5.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
namespace Submission
open _root_.BoseGases
namespace BoseGases
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- the `g₀ω₀`-mass is nonnegative. -/
lemma g0w0Mass_nonneg {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    0 ≤ g0w0Mass (v := v) h := by
  have hb := chosen_gomega_integral_bounds (v := v) (R := R) hR hv_nonneg hvrad hv_supp h
  -- hb.1 : 0 ≤ ∫ x, (v x * (1 - choose h x)) * choose h x
  dsimp [g0w0Mass, g0]
  simpa using hb.1

/-- **the main-term mass coefficient bound** (FS lm:appbogolubov's leading
term in the real-space Newtonian form, eq:I2-integral): the
`½·(1/(8π))`-scaled Newtonian double energy of the χ-renormalised
`W₁ := wScaled s (g0 v h)` kernel is at most
`½·(1 + (2C(R/s)²)(2+2C(R/s)²))·g0w0Mass` — assemble from
`i2_integral_xspace_fs` (the eq:I2-integral leaf, an absolute-value bound
around `g0w0Mass`).  With `δ := 2C(R/s)² ≤ 1` this is `≤
½(1+6C(R/s)²)·g0w0Mass`, i.e. the corpus form of FS's
`½(1+C(R/(dℓ))²)ĝω(0)` at `ℓ := s`; multiplying by `(N̂+1)N̂/s³` gives the
main term of `lm_appbogolubov_refined_target`. -/
lemma mainMassCoeff_le {v : ℝ³ → ℝ} {R s r₁ C : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |conv3 chi chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hreg : R / s ≤ r₁) (hcond : C * (R / s) ^ 2 ≤ 1 / 2) :
    (1 / 2) * (1 / (8 * π)) *
        (∫ x : ℝ³, ∫ y : ℝ³,
          wScaled s (g0 v h) x * wScaled s (g0 v h) y * (‖x - y‖ : ℝ)⁻¹)
      ≤ (1 / 2) * (1 + (2 * C * (R / s) ^ 2) * (2 + 2 * C * (R / s) ^ 2))
          * g0w0Mass (v := v) h := by
  have hI := i2_integral_xspace_fs (v := v) (R := R) (ℓ := s) (r₁ := r₁) (C := C)
    hR hv_nonneg hvrad hv_supp h hC hr₁ hT hs hreg hcond
  have hnonneg : 0 ≤ g0w0Mass (v := v) h := g0w0Mass_nonneg hR hv_nonneg hvrad hv_supp h
  have hA : (1 / (8 * π)) *
        (∫ x : ℝ³, ∫ y : ℝ³,
          wScaled s (g0 v h) x * wScaled s (g0 v h) y * (‖x - y‖ : ℝ)⁻¹)
      ≤ (1 + (2 * C * (R / s) ^ 2) * (2 + 2 * C * (R / s) ^ 2)) * g0w0Mass (v := v) h := by
    have hmp := abs_le.mp hI
    have hYdef : g0w0Mass (v := v) h =
        (∫ x : ℝ³, g0 v h x * Classical.choose h x) := rfl
    have hlin : (1 / (8 * π)) *
          (∫ x : ℝ³, ∫ y : ℝ³,
            wScaled s (g0 v h) x * wScaled s (g0 v h) y * (‖x - y‖ : ℝ)⁻¹)
          ≤ g0w0Mass (v := v) h +
              (2 * C * (R / s) ^ 2) * (2 + 2 * C * (R / s) ^ 2) * g0w0Mass (v := v) h := by
          rw [hYdef]
          nlinarith [hmp.2]
    calc
      (1 / (8 * π)) *
          (∫ x : ℝ³, ∫ y : ℝ³,
            wScaled s (g0 v h) x * wScaled s (g0 v h) y * (‖x - y‖ : ℝ)⁻¹)
          ≤ g0w0Mass (v := v) h +
              (2 * C * (R / s) ^ 2) * (2 + 2 * C * (R / s) ^ 2) * g0w0Mass (v := v) h := hlin
      _ = (1 + (2 * C * (R / s) ^ 2) * (2 + 2 * C * (R / s) ^ 2)) * g0w0Mass (v := v) h := by ring
  calc
    (1 / 2) * (1 / (8 * π)) *
        (∫ x : ℝ³, ∫ y : ℝ³,
          wScaled s (g0 v h) x * wScaled s (g0 v h) y * (‖x - y‖ : ℝ)⁻¹)
        = (1 / 2) * ((1 / (8 * π)) *
            (∫ x : ℝ³, ∫ y : ℝ³,
              wScaled s (g0 v h) x * wScaled s (g0 v h) y * (‖x - y‖ : ℝ)⁻¹)) := by ring
    _ ≤ (1 / 2) * ((1 + (2 * C * (R / s) ^ 2) * (2 + 2 * C * (R / s) ^ 2))
            * g0w0Mass (v := v) h) := by
          exact mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ (1 / 2 : ℝ))
    _ = (1 / 2) * (1 + (2 * C * (R / s) ^ 2) * (2 + 2 * C * (R / s) ^ 2))
          * g0w0Mass (v := v) h := by ring


/-- **coarsened main-term coefficient** (the target-bracket form): with
`δ := 2C(R/s)² ≤ 1` (`hcond`), the coefficient of the leading negative term
is at most `½·(1 + 6·C·(R/s)²)·g0w0Mass` — the corpus form of FS's
`½(1+C(R/(dℓ))²)ĝω(0)` (absorbing the `(2+2C(R/s)²)` into the universal
`6C`). -/
lemma mainMassCoeff_le_coarse {v : ℝ³ → ℝ} {R s r₁ C : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : ℝ³, ‖x‖ ≤ r₁ → |conv3 chi chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hreg : R / s ≤ r₁) (hcond : C * (R / s) ^ 2 ≤ 1 / 2) :
    (1 / 2) * (1 / (8 * π)) *
        (∫ x : ℝ³, ∫ y : ℝ³,
          wScaled s (g0 v h) x * wScaled s (g0 v h) y * (‖x - y‖ : ℝ)⁻¹)
      ≤ (1 / 2) * (1 + 6 * C * (R / s) ^ 2) * g0w0Mass (v := v) h := by
  have hE := mainMassCoeff_le (v := v) (R := R) (s := s) (r₁ := r₁) (C := C)
    hR hs hv_nonneg hvrad hv_supp h hC hr₁ hT hreg hcond
  have hnonneg : 0 ≤ g0w0Mass (v := v) h := g0w0Mass_nonneg hR hv_nonneg hvrad hv_supp h
  have hDle : (2 * C * (R / s) ^ 2) * (2 + 2 * C * (R / s) ^ 2)
      ≤ 6 * C * (R / s) ^ 2 := by
    let δ : ℝ := 2 * C * (R / s) ^ 2
    have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
    have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith
    have hδsq : δ ^ 2 ≤ δ := by
      calc
        δ ^ 2 = δ * δ := by ring
        _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hδ1 hδ0
        _ = δ := by ring
    dsimp [δ] at hδsq
    nlinarith
  have hcoef : (1 / 2) * (1 + (2 * C * (R / s) ^ 2) * (2 + 2 * C * (R / s) ^ 2))
      ≤ (1 / 2) * (1 + 6 * C * (R / s) ^ 2) := by
    exact mul_le_mul_of_nonneg_left (by nlinarith [hDle]) (by positivity : 0 ≤ (1 / 2 : ℝ))
  calc
    (1 / 2) * (1 / (8 * π)) *
        (∫ x : ℝ³, ∫ y : ℝ³,
          wScaled s (g0 v h) x * wScaled s (g0 v h) y * (‖x - y‖ : ℝ)⁻¹)
        ≤ (1 / 2) * (1 + (2 * C * (R / s) ^ 2) * (2 + 2 * C * (R / s) ^ 2))
            * g0w0Mass (v := v) h := hE
    _ ≤ (1 / 2) * (1 + 6 * C * (R / s) ^ 2) * g0w0Mass (v := v) h := by
          exact mul_le_mul_of_nonneg_right hcoef hnonneg

end BoseGases
end Submission

