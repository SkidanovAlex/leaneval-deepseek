import Mathlib
import Submission.Commons.Combinatorics.Transference.poly_lemma_abstract
import Submission.Commons.Combinatorics.Transference.avg_H_cubeSum_le

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- **Green–Tao Lemma 6.6 (the polynomial lemma)**, monomial case, over `ZMod p`: the
pairing of `f` with a product of `K` dual functions of functions majorised by `ν` is
bounded by `‖f‖_{U^d}` times a constant. -/
theorem poly_lemma {p : ℕ} [Fact p.Prime] {d K : ℕ} (hd : 1 ≤ d) (f : ZMod p → ℝ)
    (F : Fin K → ZMod p → ℝ) {ν τ : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x) (hτ : ∀ x, 0 ≤ τ x)
    (hF : ∀ (j : Fin K) (x : ZMod p), |F j x| ≤ ν x) {Cm : ℝ}
    (hcorr : ∀ h : Fin d → ZMod p,
      (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p,
          ∏ ω : Fin d → Bool, ν (y + ∑ i, (if ω i then h i else 0))
        ≤ ∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
            τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))))
    (hmom : (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, τ y ^ K ≤ Cm) :
    |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, f x * ∏ j : Fin K, davg d (F j) x|
      ≤ Unorm d f * (1 + ((2 ^ d * 2 ^ d : ℕ) : ℝ) ^ K * Cm) :=
  poly_lemma_abstract (G := ZMod p) d hd f F
    (fun ω hω => avg_H_cubeSum_le hd F hν hτ hF hcorr hmom ω hω)

end Commons.Combinatorics.Transference
