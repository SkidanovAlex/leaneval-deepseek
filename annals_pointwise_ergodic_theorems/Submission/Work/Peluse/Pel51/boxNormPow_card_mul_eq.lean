import Mathlib
import Submission.Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow

/-!
# The normalised box-sum `|S| · ‖f‖^{2^t}_{□^t_Q(S)}` is independent of the support box `S`

The support set `S` enters `prodCubeSum t Q S g` only through the normalising factor
`(|S| : ℂ)⁻¹`; the cube sum over `x` itself is `S`-free (see `Work.Peluse.prodCubeSum_eq`).
Multiplying by `|S|` therefore removes the dependence on `S` completely:

`|S| * ‖f‖^{2^t}_{□^t_Q(S)} = |S'| * ‖f‖^{2^t}_{□^t_Q(S')}`

whenever `S` and `S'` are nonempty.  This is the exact scaling used to enlarge the ambient window
of Peluse's Lemma 5.1 for free.
-/

namespace Work.Peluse.Pel51

/-- **The identity `|S| · boxNormPow t Q S f = |S'| · boxNormPow t Q S' f`.**

Both sides equal the norm of the `S`-free part of the cube sum:  after unfolding
`boxSumPow`/`prodCubeSum`, `boxSumPow t Q T f` is `|T|⁻¹` times an expression not mentioning `T`,
so multiplying by `|T|` (legal since `T` is nonempty) gives the same complex number for `T = S`
and `T = S'`; taking moduli gives the claim. -/
theorem boxNormPow_card_mul_eq {t : ℕ} (Q : Fin t → Finset ℤ) {S S' : Finset ℤ}
    (hS : S.Nonempty) (hS' : S'.Nonempty) (f : ℤ → ℂ) :
    (S.card : ℝ) * Work.Peluse.boxNormPow t Q S f
      = (S'.card : ℝ) * Work.Peluse.boxNormPow t Q S' f := by
  -- `|T| · boxSumPow t Q T f` as a complex number does not depend on `T` (for `T` nonempty).
  have hkey : ∀ T : Finset ℤ, T.Nonempty →
      (T.card : ℂ) * Work.Peluse.boxSumPow t Q T f =
        (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) *
          (∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
            ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
            ∑' x : ℤ, ∏ ω : Fin t → Bool,
              (star^[Work.Peluse.weight ω])
                (f (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))) := by
    intro T hT
    have hTc : (T.card : ℂ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hT
    simp only [Work.Peluse.boxSumPow, Work.Peluse.prodCubeSum]
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hTc, one_mul]
  have hcomplex : (S.card : ℂ) * Work.Peluse.boxSumPow t Q S f =
      (S'.card : ℂ) * Work.Peluse.boxSumPow t Q S' f := by
    rw [hkey S hS, hkey S' hS']
  have hnorm := congrArg (fun z : ℂ => ‖z‖) hcomplex
  simpa only [norm_mul, Complex.norm_natCast, Work.Peluse.boxNormPow] using hnorm

end Work.Peluse.Pel51
