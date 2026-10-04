import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep1.flat_multiplier_commutator
import Submission.Work.Diff.STE.B3.SymCalcStep1.conj_cut_aux
import Submission.Work.Diff.STE.B3.flat_diag_pairing_le
import Submission.Work.Diff.STE.B3.SymCalcStep1.firstOrder_comm_trunc_le
import Submission.Work.Diff.STE.flat.fourierCoeff_seriesFun
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.eq_zero_of_fourierCoeff_eq_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep7

/-! ## The two Fourier-coefficient identities of the flat multiplier commutator

These are the "read the multiplier on the functions" dictionary: the Fourier coefficients of
`M_β ∘ S_ε` and of `S_ε ∘ M_β` are obtained from those of `β` and `h` by the coefficient-family
operations `conv` and `trunc` (the `trunc` being the multiplier `ρ ∘ (ε ·)`).

Both proofs are the absolutely convergent product rule `Work.Diff.STE.fourierCoeff_mul_seriesFun`
(Fourier inversion `seriesFun ∘ fourierCoeff = id` for the smooth `1`-periodic factor,
`Work.Diff.STE.flat.seriesFun_fourierCoeff`), plus `conv_comm` to put the two factors in the
order used by `flat_multiplier_commutator`. -/

/-- **Fourier coefficients of `M_β ∘ S_ε`**: multiplying a `1`-periodic function by the smooth
multiplier `β` commutes with taking Fourier coefficients, and the cutoff `S_ε = flatCut ρ ε` acts
on the coefficient family by `trunc ρ ε`. -/
lemma fourierCoeff_mul_flatCut {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    (β h : (ι → ℝ) → ℂ) (hβ : Continuous β)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhp : Work.Diff.STE.Periodic1 h) (k : ι → ℤ) :
    Work.Diff.STE.fourierCoeff
        (fun x : ι → ℝ => β x * Work.Diff.STE.B3.SymCalc.flatCut ρ ε h x) k
      = Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff β)
          (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff h)) k := by
  have hβint : MeasureTheory.Integrable β
      (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous_cplx hβ
  have htrunc_sum : Summable (fun l : ι → ℤ =>
      ‖Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff h) l‖) :=
    Work.Diff.STE.B3.SymCalcStep1.summable_trunc_one ρ hρ ε
      (Work.Diff.STE.B3.summable_norm_fourierCoeff h hh hhp)
  have hkey := Work.Diff.STE.fourierCoeff_mul_seriesFun β
    (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff h)) k hβint htrunc_sum
  rw [Work.Diff.STE.B3.SymCalcStep1.conv_comm
    (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff h))
    (Work.Diff.STE.fourierCoeff β) k] at hkey
  simpa only [Work.Diff.STE.B3.SymCalc.flatCut] using hkey

/-- **Fourier coefficients of `S_ε ∘ M_β`**: first multiply the two `1`-periodic functions
(`conv` on the Fourier side), then apply the cutoff (`trunc ρ ε`). -/
lemma fourierCoeff_flatCut_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    (β h : (ι → ℝ) → ℂ) (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβp : Work.Diff.STE.Periodic1 β)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhp : Work.Diff.STE.Periodic1 h) (k : ι → ℤ) :
    Work.Diff.STE.fourierCoeff
        (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y : ι → ℝ => β y * h y)) k
      = Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff β)
          (Work.Diff.STE.fourierCoeff h)) k := by
  have hbh_sm : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => β y * h y) := hβ.mul hh
  have hbh_per : Work.Diff.STE.Periodic1 (fun y : ι → ℝ => β y * h y) :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hβp hhp
  have hβint : MeasureTheory.Integrable β
      (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous_cplx hβ.continuous
  have hh_sum : Summable (fun l : ι → ℤ => ‖Work.Diff.STE.fourierCoeff h l‖) :=
    Work.Diff.STE.B3.summable_norm_fourierCoeff h hh hhp
  rw [Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_flatCut ρ hρ ε hbh_sm hbh_per k]
  change (ρ (ε • (fun i => (k i : ℝ))) : ℂ)
        * Work.Diff.STE.fourierCoeff (fun y : ι → ℝ => β y * h y) k
      = (ρ (ε • (fun i => (k i : ℝ))) : ℂ)
        * Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff β) (Work.Diff.STE.fourierCoeff h) k
  have hkey := Work.Diff.STE.fourierCoeff_mul_seriesFun β (Work.Diff.STE.fourierCoeff h) k
    hβint hh_sum
  rw [Work.Diff.STE.B3.SymCalcStep1.conv_comm (Work.Diff.STE.fourierCoeff h)
    (Work.Diff.STE.fourierCoeff β) k] at hkey
  rw [show (fun x : ι → ℝ => β x * Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff h) x)
      = (fun y : ι → ℝ => β y * h y) from funext fun x => by
        rw [Work.Diff.STE.flat.seriesFun_fourierCoeff h hh hhp x]] at hkey
  rw [hkey]

/-- **The flat multiplier commutator in function form, `ε`-uniformly of order `−1`.** This is `Work.Diff.STE.B3.SymCalcStep1.flat_multiplier_commutator` (stated on Fourier coefficient families, with `conv` and `trunc`) read on the *functions*: for a fixed smooth `1`-periodic multiplier `β`, the commutator of `M_β` with the Friedrichs cutoff `S_ε = flatCut ρ ε` gains one derivative, uniformly in `ε ∈ (0,1]`. Route (no new Fourier analysis): `fourierCoeff (fun x => β x * flatCut ρ ε h x) = conv (fourierCoeff β) (trunc ρ ε (fourierCoeff h))` and `fourierCoeff (flatCut ρ ε (fun y => β y * h y)) = trunc ρ ε (conv (fourierCoeff β) (fourierCoeff h))`; `Work.Diff.STE.flat.fourierCoeff_sub_of_continuous` turns the difference of coefficient families into the coefficients of the difference, and `flat_multiplier_commutator` bounds it with the moment hypothesis `Work.Diff.STE.B3.summable_wt_pow_mul_norm_fourierCoeff`. -/
theorem flat_multiplier_gain {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρ0 : ρ 0 = 1)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (β : (ι → ℝ) → ℂ) (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (hβp : Work.Diff.STE.Periodic1 β)
    (t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ h : (ι → ℝ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) h → Work.Diff.STE.Periodic1 h →
      Work.Diff.STE.CSq (t + 1) (Work.Diff.STE.fourierCoeff (fun x => β x *
            Work.Diff.STE.B3.SymCalc.flatCut ρ ε h x
          - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y => β y * h y) x))
        ≤ C * Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff h) := by
  classical
  -- The coefficient-family certificate, with `a = fourierCoeff β` (rapidly decaying by
  -- `summable_wt_pow_mul_norm_fourierCoeff`).
  obtain ⟨C, hC0, hC⟩ :=
    Work.Diff.STE.B3.SymCalcStep1.flat_multiplier_commutator ρ hρ hdiam hρ0 L hL hρlip
      (Work.Diff.STE.fourierCoeff β)
      (fun N => Work.Diff.STE.B3.summable_wt_pow_mul_norm_fourierCoeff N β hβ hβp) t
  refine ⟨C, hC0, ?_⟩
  intro ε hε hε1 h hh hhp
  -- The Fourier transform of the commutator is the commutator of the Fourier transforms.
  have hcoef : Work.Diff.STE.fourierCoeff (fun x : ι → ℝ => β x *
        Work.Diff.STE.B3.SymCalc.flatCut ρ ε h x
      - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y : ι → ℝ => β y * h y) x)
      = fun k : ι → ℤ => Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff β)
            (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff h)) k
          - Work.Diff.STE.trunc ρ ε (Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff β)
              (Work.Diff.STE.fourierCoeff h)) k := by
    have hFh_sm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h) :=
      Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε hh hhp
    have hFbh_sm : ContDiff ℝ (⊤ : ℕ∞)
        (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y : ι → ℝ => β y * h y)) :=
      Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρ ε (hβ.mul hh)
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hβp hhp)
    funext k
    rw [Work.Diff.STE.flat.fourierCoeff_sub_of_continuous
      (fun x : ι → ℝ => β x * Work.Diff.STE.B3.SymCalc.flatCut ρ ε h x)
      (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y : ι → ℝ => β y * h y))
      (hβ.continuous.mul hFh_sm.continuous) hFbh_sm.continuous k]
    rw [fourierCoeff_mul_flatCut ρ hρ ε β h hβ.continuous hh hhp k]
    rw [fourierCoeff_flatCut_mul ρ hρ ε β h hβ hβp hh hhp k]
  rw [hcoef]
  exact hC ε hε hε1 (Work.Diff.STE.fourierCoeff h)
    (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff h hh hhp t)

end Work.Diff.STE.B3.SymCalcStep7
