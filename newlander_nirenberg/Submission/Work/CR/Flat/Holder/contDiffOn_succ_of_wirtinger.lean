import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Holder.holderNorm_le_wirtinger_coord

namespace Work.CR.Flat.Holder

/-- **Smoothness upgrade from the Wirtinger derivatives.**

If `h : ℂⁿ → ℂ` is differentiable on an open `Ω`, is `C^m` there, and each of its Wirtinger
derivatives `∂_j h = dCoord j h` and `∂̄_j h = dbarCoord j h` is again `C^m` on `Ω`, then `h`
is `C^{m+1}` on `Ω`.

Proof: `fderivWithin ℝ h Ω` agrees on `Ω` with
`fun z => ∑ j, (PhiN j (dCoord j h z) + PsiN j (dbarCoord j h z))` (the pointwise identity
`fderiv_eq_sum_PhiN_PsiN` of `Submission/Work/CR/Flat/Holder/holderNorm_le_wirtinger_coord.lean`
combined with `fderivWithin_of_isOpen`), and that function is `C^m` as a sum of compositions of
the continuous linear maps `PhiN j`, `PsiN j` with the `C^m` functions `dCoord j h`, `dbarCoord j h`.
So `fderivWithin ℝ h Ω` is `C^m`, and `contDiffOn_succ_iff_fderivWithin` (or
`contDiffOn_succ_of_fderivWithin` plus `contDiffOn_congr` using `fderivWithin_of_isOpen`)
finishes. -/
theorem contDiffOn_succ_of_wirtinger {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    {h : (Fin n → ℂ) → ℂ} {m : ℕ} (hdiff : DifferentiableOn ℝ h Ω)
    (hm : ContDiffOn ℝ ((m : ℕ) : ℕ∞) h Ω)
    (h1 : ∀ j, ContDiffOn ℝ ((m : ℕ) : ℕ∞) (fun z => Work.CR.Flat.dCoord j h z) Ω)
    (h2 : ∀ j, ContDiffOn ℝ ((m : ℕ) : ℕ∞) (fun z => Work.CR.Flat.dbarCoord j h z) Ω) :
    ContDiffOn ℝ (((m + 1 : ℕ)) : ℕ∞) h Ω := by
  -- `(m : WithTop ℕ∞)` is never `⊤`, so the analytic hypothesis is vacuous.
  have hntop : (((m : ℕ) : ℕ∞) : WithTop ℕ∞) ≠ ⊤ := WithTop.coe_ne_top
  -- The Wirtinger reconstruction of the differential is `C^m`.
  have hF : ContDiffOn ℝ ((m : ℕ) : ℕ∞)
      (fun z => ∑ j : Fin n,
        (PhiN j (Work.CR.Flat.dCoord j h z) + PsiN j (Work.CR.Flat.dbarCoord j h z))) Ω := by
    refine ContDiffOn.sum (fun j _ => ?_)
    exact (((PhiN j).contDiff.comp_contDiffOn (h1 j)).add
      ((PsiN j).contDiff.comp_contDiffOn (h2 j)))
  refine contDiffOn_succ_of_fderivWithin hdiff (fun hn => absurd hn hntop) ?_
  -- On the open set `Ω`, `fderivWithin` agrees with the reconstruction.
  refine hF.congr (fun z hz => ?_)
  rw [fderivWithin_of_isOpen hΩ hz, fderiv_eq_sum_PhiN_PsiN]

end Work.CR.Flat.Holder
