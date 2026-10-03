import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.FarSepDefs

/-!
# The separation inequality applied to a `(m,c,Q₁,Q₂)`-piece of the far sum

The far sum is split into the pieces `farInner D R S a b α m c Q₁ Q₂` (the intervals of the
flipped modulus `q'`); this module shows that the Fourier–Mellin separation inequality `hsep`
(Friedlander–Iwaniec (12.13)–(12.14), proved in `separation_ineq_nearCut`) bounds each piece by
`(log (2 + b/a) + 1)²` times a bound for the exponential sums `farExpSum`.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The terms of the exponential sum of a piece, in the form used by the subtype sum. -/
private def expTerm (D : ℕ) (α : ℕ → ℕ → ℂ) (m c : ℕ) (u t : ℝ) (i : FarIx) : ℂ :=
  farCoef m c α i * Complex.exp (2 * Real.pi * Complex.I * (u * xOrig c i)) *
    (((ySep c D i : ℝ)) : ℂ) ^ (Complex.I * (t : ℂ))

/-- **The separation inequality applied to one piece of the far sum.**  If `M` bounds the
exponential sums `Σ_i c_i e(u x_i) y_i^{it}` of the index set of the `(m,c,Q₁,Q₂)`-piece, then the
piece is bounded by `(log (2 + b/a) + 1)² · M`. -/
theorem far_sep_apply_of_sep {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hsep : ∀ (a b : ℝ), 0 < a → a ≤ b →
      ∀ (ι : Type) [Fintype ι] (x y : ι → ℝ) (cc : ι → ℂ) (M : ℝ),
      (∀ i, 0 < y i) →
      (∀ u t : ℝ, ‖∑ i, cc i * Complex.exp (2 * Real.pi * Complex.I * (u * x i)) *
            (y i : ℂ) ^ (Complex.I * t)‖ ≤ M) →
      ‖∑ i, cc i * ((Work.FIArea4.Vflip.bump (|x i| * y i)
            * Work.FIArea4.Vflip.nearCut a b (x i) : ℝ) : ℂ)‖
        ≤ C₀ * (Real.log (2 + b / a) + 1) ^ 2 * M)
    {D R S m c Q1 Q2 : ℕ} {a b M : ℝ} {α : ℕ → ℕ → ℂ}
    (ha : 0 < a) (hab : a ≤ b) (hD : 0 < D)
    (hM : ∀ u t : ℝ, ‖farExpSum D R S a b α m c Q1 Q2 u t‖ ≤ M) :
    ‖farInner D R S a b α m c Q1 Q2‖ ≤ C₀ * (Real.log (2 + b / a) + 1) ^ 2 * M := by
  have hy : ∀ i : ↥(farSet D R S a b m c Q1 Q2), 0 < ySep c D i.val := by
    intro i
    obtain ⟨hc, h1, h2⟩ := farCond_pos (farCond_of_mem_farSet i.2)
    have hq : 0 < i.val.1.1 := by have := (mem_farSet.mp i.2).1; omega
    exact ySep_pos hc hD i.val h1 h2 hq
  have hM' : ∀ u t : ℝ,
      ‖∑ i : ↥(farSet D R S a b m c Q1 Q2), expTerm D α m c u t i.val‖ ≤ M := by
    intro u t
    have hcongr : (∑ i : ↥(farSet D R S a b m c Q1 Q2), expTerm D α m c u t i.val)
        = farExpSum D R S a b α m c Q1 Q2 u t := by
      rw [farExpSum, ← Finset.sum_attach (farSet D R S a b m c Q1 Q2)
        (fun i => farCoef m c α i * Complex.exp (2 * Real.pi * Complex.I * (u * xOrig c i)) *
          (((ySep c D i : ℝ)) : ℂ) ^ (Complex.I * (t : ℂ))), Finset.univ_eq_attach]
      rfl
    rw [hcongr]
    exact hM u t
  have hkey := hsep a b ha hab (↥(farSet D R S a b m c Q1 Q2))
    (fun z => xOrig c z.val) (fun z => ySep c D z.val) (fun z => farCoef m c α z.val) M hy hM'
  have hsum : farInner D R S a b α m c Q1 Q2
      = ∑ z : ↥(farSet D R S a b m c Q1 Q2),
          farCoef m c α z.val *
            (((Work.FIArea4.Vflip.bump (|xOrig c z.val| * ySep c D z.val)
              * Work.FIArea4.Vflip.nearCut a b (xOrig c z.val) : ℝ)) : ℂ) := by
    rw [farInner, ← Finset.sum_attach (farSet D R S a b m c Q1 Q2)
      (fun i => farCoef m c α i * farWeight D a b c i), Finset.univ_eq_attach]
    exact Finset.sum_congr rfl (fun z _ => by rw [farWeight])
  rw [hsum]
  exact hkey

end

end Work.FIArea4.Vflip.Vfd
