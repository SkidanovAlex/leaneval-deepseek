import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.FarSepDefs
import Submission.Work.FIArea4.Vflip.Vfd.FarSepApply
import Submission.Work.FIArea4.Vflip.Vfd.separation_ineq_nearCut
import Submission.Work.FIArea4.Vflip.Vfd.coprimeSetup
import Submission.Work.FIArea4.Vflip.Vfd.coprime_pairR_oddPart_m
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.PairSumCommon

/-!
# Auxiliary objects for the far part of the flipped-moduli bound

This module collects the objects shared between the proof of `Vflip_far_bound` and its
delegated sub-lemmas:

* `cR c R = ⌈R/c⌉`, the reduced dyadic box parameter of the `c`-group (the reduced moduli
  `ρ = r/c` of a box point satisfy `ρ ≤ 2⌈R/c⌉`);
* the coefficient arrays `farU m c α u t` and `farV m c α u t` in which the exponential sum
  `farExpSum` of a `(m,c,Q)`-piece is repackaged as a coprime pair sum of modulus `m q'`.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `⌈R/c⌉`: the reduced box parameter of the `c`-group. -/
def cR (c R : ℕ) : ℕ := (R + c - 1) / c

lemma cR_pos {c R : ℕ} (hc : 1 ≤ c) (hR : 1 ≤ R) : 1 ≤ cR c R := by
  rw [cR, Nat.le_div_iff_mul_le hc]
  omega

lemma le_mul_cR {c R : ℕ} (hc : 1 ≤ c) : R ≤ c * cR c R := by
  rw [cR]
  have h := Nat.div_add_mod (R + c - 1) c
  have h2 : (R + c - 1) % c ≤ c - 1 := by
    have := Nat.mod_lt (R + c - 1) hc; omega
  omega

lemma div_le_cR {c R : ℕ} (hc : 1 ≤ c) : R / c ≤ cR c R := by
  rw [cR]
  exact Nat.div_le_div_right (by omega : R ≤ R + c - 1)

/-- The coefficient array of the `c`-group whose coprime pair sum of modulus `m q'` reproduces
the exponential sum `farExpSum` of the piece.  All the factors beyond `α (c ρ) s` have modulus
one (or vanish), so `p14L2` of this array is at most that of `redA c α`. -/
def farU (m c : ℕ) (α : ℕ → ℕ → ℂ) (u t : ℝ) : ℕ → ℕ → ℂ :=
  fun ρ s => α (c * ρ) s * ((jacobiSym (s : ℤ) ρ : ℤ) : ℂ) * Work.FIArea4.jw m ρ *
    Complex.exp (2 * Real.pi * Complex.I * (u * ((s : ℝ) / (((c * ρ : ℕ) : ℝ))))) *
    ((((ρ : ℕ) : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)))

/-- The companion array of `farU`: its complex conjugate carries the conjugate factors. -/
def farV (m c : ℕ) (α : ℕ → ℕ → ℂ) (u t : ℝ) : ℕ → ℕ → ℂ :=
  fun ρ s => α (c * ρ) s * ((jacobiSym (s : ℤ) ρ : ℤ) : ℂ) * Work.FIArea4.jw m ρ *
    Complex.exp (2 * Real.pi * Complex.I * (u * ((s : ℝ) / (((c * ρ : ℕ) : ℝ))))) *
    ((((ρ : ℕ) : ℝ) : ℂ) ^ (-(Complex.I * (t : ℂ))))

/-- **The Fourier–Mellin separation applied to one `(m,c,Q₁,Q₂)`-piece**: if `M` bounds the
exponential sums `farExpSum` of the piece, then the piece itself is bounded by
`(log (2 + b/a) + 1)² · M`. -/
theorem farInner_bound_sep :
    ∃ C : ℝ, 0 < C ∧ ∀ {D R S m c Q1 Q2 : ℕ} {a b M : ℝ} {α : ℕ → ℕ → ℂ},
      (ha : 0 < a) → (hab : a ≤ b) → (hD : 0 < D) →
      (hM : ∀ u t : ℝ, ‖farExpSum D R S a b α m c Q1 Q2 u t‖ ≤ M) →
      ‖farInner D R S a b α m c Q1 Q2‖ ≤ C * (Real.log (2 + b / a) + 1) ^ 2 * M := by
  obtain ⟨C₀, hC₀, hsep⟩ := separation_ineq_nearCut
  exact ⟨C₀, hC₀, fun ha hab hD hM => far_sep_apply_of_sep hC₀ hsep ha hab hD hM⟩

end

end Work.FIArea4.Vflip.Vfd
