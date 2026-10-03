/-
# `Submission.Work.FIArea7.UniAssembled6` — the assembled ω-form of the uniform (paper's `W`) cut

Assembles the two pair-level identities of the uniform §17 chain into the box-level ones:

* `WUniExpanded6_eq_WUniOmega6` — the (17.1) reflected sum equals its ω-form `WUniOmega6`
  (`Work.FIArea7.WUniOmega6Inner_pair_eq`, the uniform analogue of `WBOmega6_pair_eq`,
  instantiated at the support of `IsBetaCoeff6`);
* `WUni6_eq_WUniOmega6` — hence the paper's sharp `W` is the ω-form, the left-hand side of (17.10).

The degenerate pairs `|Δ| = 0` contribute `0` on both sides (`logFac6 = log(…/0) = 0`), so the
hypotheses of the pair lemma (which need `0 < |Δ|` to turn `4be ∣ |Δ|` into a bound on `b`) are
only invoked on the non-degenerate pairs.
-/
import Mathlib
import Submission.Work.FIArea7.UniExpanded6
import Submission.Work.FIArea7.WUniOmega6Inner_pair_eq
import Submission.Work.FIArea7.coprime_gnorm_of_dvd_absDelta
import Submission.Work.FIArea7.WUniOmega6_eq_WUniOmega6Pull6

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The (17.9) ω-form of the (17.1) reflected sum of the uniform cut.**  For every coefficient of
(4.13)+(5.13)+(5.7) and every `1 ≤ X`, the reflected Möbius-expanded sum `WUniExpanded6` equals the
ω-form `WUniOmega6` — the left-hand side of (17.10). -/
theorem WUniExpanded6_eq_WUniOmega6 {Pa : Work.FITop.Params} {X : ℕ} {φ : ℝ}
    {z0 : GaussianInt} {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β)
    (hX : 1 ≤ X) :
    WUniExpanded6 Pa X β = WUniOmega6 Pa X β := by
  rw [WUniExpanded6, WUniOmega6]
  congr 1
  refine Finset.sum_congr rfl fun z1 _ => ?_
  refine Finset.sum_congr rfl fun z2 _ => ?_
  by_cases hg : Work.FIPlan.GaussCoprime z1 z2
  · rw [if_pos hg, if_pos hg]
    by_cases hb1 : β z1 = 0
    · have hzero : WUniOmega6Inner X z1 z2 β = 0 := by
        rw [WUniOmega6Inner]
        refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun e _ => ?_
        simp [Work.FIArea7.betaPrime, hb1]
      rw [hzero, hb1]
      simp
    · by_cases hb2 : β z2 = 0
      · have hzero : WUniOmega6Inner X z1 z2 β = 0 := by
          rw [WUniOmega6Inner]
          refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun e _ => ?_
          simp [Work.FIArea7.betaPrime, hb2]
        rw [hzero, hb2]
        simp
      · by_cases hM0 : Work.FIPlan.absDelta z1 z2 = 0
        · -- degenerate pair: the logarithmic factor vanishes
          have hL : Work.FITop4.logFac6 z1 z2 = 0 := by
            rw [Work.FITop4.logFac6, hM0]; simp
          have hz1 : WUniOmega6Inner X z1 z2 β = 0 := by
            rw [WUniOmega6Inner]
            refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun e _ => ?_
            simp [hL]
          have hz2 : WUniInner X (fun d => Work.FIArea7.ratioSym z1 z2 d)
              (Work.FITop4.logFac6 z1 z2) 0 = 0 := by
            rw [WUniInner]
            refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun e _ => ?_
            simp [hL]
          rw [hM0, hz2, hz1]
          simp
        · have hbox1 : Work.FITop3.InPolarBox Pa φ z1 :=
            Work.FITop4.IsBetaCoeff6.support hβ hb1
          have hbox2 : Work.FITop3.InPolarBox Pa φ z2 :=
            Work.FITop4.IsBetaCoeff6.support hβ hb2
          have hsqf1 : Squarefree (Work.FIPlan.gnorm z1) :=
            Work.FITop4.IsBetaCoeff6.squarefree_gnorm hβ hb1
          have hsqf2 : Squarefree (Work.FIPlan.gnorm z2) :=
            Work.FITop4.IsBetaCoeff6.squarefree_gnorm hβ hb2
          obtain ⟨h8r, h8i⟩ :=
            modEq_of_sameClass8 (Work.FITop4.IsBetaCoeff6.sameClass hβ hb1 hb2)
          have hmain := WUniOmega6Inner_pair_eq X z1 z2 β hbox1.1 hbox2.1 hsqf1 hsqf2 hg
            h8r h8i hX (fun b e _ h4be _ => ?_)
          · simpa only [Work.FITop4.ratioSym] using hmain
          · have h4be0 : 4 * b * e ≠ 0 := by
              intro h0
              rw [h0] at h4be
              exact hM0 (Nat.eq_zero_of_zero_dvd h4be)
            exact Work.FIArea7.coprime_gnorm_of_dvd_absDelta (Nat.pos_of_ne_zero h4be0)
              hbox1.1 hbox2.1 hsqf1 hsqf2 hg h4be
  · rw [if_neg hg, if_neg hg]

/-- **The uniform (paper's `W`) cut in ω-form**: `WUni6 = WUniOmega6`, the left-hand side of
(17.10). -/
theorem WUni6_eq_WUniOmega6 (Pa : Work.FITop.Params) (X : ℕ) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (hX : 1 ≤ X) :
    WUni6 Pa X β = WUniOmega6 Pa X β := by
  rw [WUni6_eq_WUniExpanded6, WUniExpanded6_eq_WUniOmega6 hβ hX]

/-- **The uniform cut with the `(b,e)`-sums pulled outside the pair sums** — the form on which
(16.11)/(17.10) is applied. -/
theorem WUni6_eq_WUniOmega6Pull6 (Pa : Work.FITop.Params) (X : ℕ) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (hX : 1 ≤ X) :
    WUni6 Pa X β = WUniOmega6Pull6 Pa X β := by
  rw [WUni6_eq_WUniOmega6 Pa X φ z0 β hβ hX,
    WUniOmega6_eq_WUniOmega6Pull6 Pa X φ z0 β hβ hX]

end

end Work.FIArea7
