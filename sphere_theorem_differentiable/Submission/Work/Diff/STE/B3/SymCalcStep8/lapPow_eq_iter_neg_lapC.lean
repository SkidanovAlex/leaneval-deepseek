import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep6.lapPow_one_eq_neg_lapC
import Submission.Work.Diff.STE.B3.SymCalcStep6.lapPow_algebra
import Submission.Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Λ^j = (-Δ)^j` on the flat torus: the iterated form

`Work.Diff.STE.B3.SymCalcStep5.lapPow j` is the flat Laplacian power `Λ^j`, defined as the Fourier
multiplier with symbol `flatLam m ^ j`, and `Work.Diff.STE.B3.SymCalc.lapC = Σᵢ ∂ᵢ∂ᵢ` is the
second-order operator `Δ`.  The case `j = 1` of the dictionary between the two notations,
`Λ = -Δ`, is `Work.Diff.STE.B3.SymCalcStep6.lapPow_one_eq_neg_lapC`; this file records the general
form

  `Λ^j w = ((-Δ))^j w`   (the `j`-fold iterate of the operator `-Δ` applied to `w`)

for smooth `1`-periodic `w`.  The proof is an induction on `j`:

* `j = 0`: `Λ^0` is the multiplier with symbol `1`, i.e. the identity; this is Fourier inversion
  `seriesFun (fourierCoeff w) = w` for smooth `1`-periodic `w`;
* `j → j + 1`: `Λ^{j+1} = Λ^1 ∘ Λ^j`
  (`Work.Diff.STE.B3.SymCalcStep6.lapPow_algebra`), and `Λ^1 = -Δ`
  (`Work.Diff.STE.B3.SymCalcStep6.lapPow_one_eq_neg_lapC`, applicable to `Λ^j w` because `Λ^j w`
  is again smooth — `Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox` — and `1`-periodic).
-/

namespace Work.Diff.STE.B3.SymCalcStep8

theorem lapPow_eq_iter_neg_lapC {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ℕ) (w : (ι → ℝ) → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwp : Work.Diff.STE.Periodic1 w) :
    ∀ x : ι → ℝ, Work.Diff.STE.B3.SymCalcStep5.lapPow j w x
      = ((fun w : (ι → ℝ) → ℂ => fun x : ι → ℝ =>
          - Work.Diff.STE.B3.SymCalc.lapC w x)^[j] w) x := by
  have key : ∀ j : ℕ, Work.Diff.STE.B3.SymCalcStep5.lapPow j w
      = (fun u : (ι → ℝ) → ℂ => fun x : ι → ℝ =>
          - Work.Diff.STE.B3.SymCalc.lapC u x)^[j] w := by
    intro j
    induction j with
    | zero =>
      -- `Λ^0` is the identity multiplier: Fourier inversion
      funext x
      rw [Function.iterate_zero_apply]
      rw [Work.Diff.STE.B3.SymCalcStep6.lapPow_eq_seriesFun]
      simp only [pow_zero, Complex.ofReal_one, one_mul]
      exact Work.Diff.STE.flat.seriesFun_fourierCoeff w hw hwp x
    | succ j ih =>
      -- `Λ^{j+1} = Λ^1 ∘ Λ^j = (-Δ) ∘ Λ^j`, and by induction `Λ^j = (-Δ)^j`
      have hsm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalcStep5.lapPow j w) :=
        (Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox j 0).2.2.1 w hw hwp
      have hper : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalcStep5.lapPow j w) :=
        (Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox j 0).2.2.2 w
      have h1 : Work.Diff.STE.B3.SymCalcStep5.lapPow 1
            (Work.Diff.STE.B3.SymCalcStep5.lapPow j w)
          = fun x : ι → ℝ =>
              - Work.Diff.STE.B3.SymCalc.lapC
                  (Work.Diff.STE.B3.SymCalcStep5.lapPow j w) x :=
        funext fun x => Work.Diff.STE.B3.SymCalcStep6.lapPow_one_eq_neg_lapC
          (Work.Diff.STE.B3.SymCalcStep5.lapPow j w) hsm hper x
      have h2 : Work.Diff.STE.B3.SymCalcStep5.lapPow (Nat.succ j) w
          = Work.Diff.STE.B3.SymCalcStep5.lapPow 1
              (Work.Diff.STE.B3.SymCalcStep5.lapPow j w) := by
        rw [Work.Diff.STE.B3.SymCalcStep6.lapPow_algebra.1 1 j w hw hwp, Nat.add_comm 1 j]
      rw [h2, h1, ih, Function.iterate_succ_apply']
  intro x
  rw [key j]

end Work.Diff.STE.B3.SymCalcStep8
