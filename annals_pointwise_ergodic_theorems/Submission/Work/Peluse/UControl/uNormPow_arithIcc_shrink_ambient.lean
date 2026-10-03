import Mathlib
import Submission.Work.Peluse.Concat.arithIcc_shrink_ge_two
import Submission.Work.Peluse.Pairing.boxSumPow_neg_directions
import Submission.Work.Peluse.Ulower.boxSumPow_neg

/-!
# Shrinking both the direction set and the ambient box of the uniformity-norm power

For `s ≥ 2` there is a constant `C > 0` with

`C * uNormPow s (arithIcc κ L') (symIcc N') g ≤ uNormPow s (arithIcc κ L) (symIcc N) g`

whenever `κ ≠ 0`, `1 ≤ L ≤ L'`, `N ≤ N'`, `g` is supported in `[-N,N]` and `‖g‖ ≤ 1`.

This is the "monotone in the data" form of the direction-length inequality of Peluse's box norms
(`Work.Peluse.Concat.arithIcc_shrink_ge_two_signed`), combined with the fact that, in this
formalisation of Peluse's Definition 2.1, the ambient set `S` enters the box norm only through the
normalising factor `|S|⁻¹` (the sum over `x` is a `tsum` over all of `ℤ`); enlarging the ambient set
therefore *decreases* the norm (`Work.Peluse.PETTwo.boxNormPow_mono_set`, reproved here as
`boxNormPow_mono_symIcc` for the symmetric boxes `symIcc ·`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-- The box sum is `|S|⁻¹` times a factor which does not depend on the ambient set `S`: the sums
over `x` and over the shift tuples are `S`-free. -/
lemma boxSumPow_eq_inv_card_mul_common {t : ℕ} (Q : Fin t → Finset ℤ) (f : ℤ → ℂ) :
    ∃ A : ℂ, ∀ S : Finset ℤ, boxSumPow t Q S f = ((S.card : ℂ))⁻¹ * A := by
  refine ⟨(∏ i : Fin t, (((Q i).card : ℂ))⁻¹) * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) *
      ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i}, ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑' x : ℤ, ∏ ω : Fin t → Bool,
          (star^[weight ω]) (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)), ?_⟩
  intro S
  simp only [boxSumPow, prodCubeSum_eq]
  ring

/-- Enlarging the ambient set `symIcc N` to `symIcc N'` (`N ≤ N'`) can only decrease the box-norm
power. -/
lemma boxNormPow_mono_symIcc {t : ℕ} {Q : Fin t → Finset ℤ} {N N' : ℕ} (hNN' : N ≤ N')
    (f : ℤ → ℂ) :
    boxNormPow t Q (symIcc N') f ≤ boxNormPow t Q (symIcc N) f := by
  obtain ⟨A, hA⟩ := boxSumPow_eq_inv_card_mul_common Q f
  have hsub : symIcc N ⊆ symIcc N' := by
    intro x hx
    simp only [symIcc, Finset.mem_Icc] at hx ⊢
    obtain ⟨h1, h2⟩ := hx
    have hNZ : (N : ℤ) ≤ (N' : ℤ) := by exact_mod_cast hNN'
    constructor <;> omega
  have hne : (symIcc N).Nonempty := ⟨0, by simp [symIcc]⟩
  have hcard : ((symIcc N).card : ℝ) ≤ ((symIcc N').card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hpos : (0 : ℝ) < ((symIcc N).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hpos' : (0 : ℝ) < ((symIcc N').card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (hne.mono hsub)
  have hinv : (((symIcc N').card : ℝ))⁻¹ ≤ (((symIcc N).card : ℝ))⁻¹ := by
    rw [inv_le_inv₀ hpos' hpos]
    exact hcard
  rw [boxNormPow, boxNormPow, hA (symIcc N'), hA (symIcc N), norm_mul, norm_mul, norm_inv,
    norm_inv, Complex.norm_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right hinv (norm_nonneg A)

end

end Work.Peluse.UControl
