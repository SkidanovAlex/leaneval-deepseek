/-
# The lift: the cumulative IW multiplier as a finite sum of modulated height-`0` operators

This file reproduces the two ingredients of `LowModApproxBoundedH/mdlPartVar.lean` that the
assembly `sliceGBoundAux.lean` needs,

* `Tle_eq_sum_modulation` — the pointwise lift
  `Tle ρ l φ f x = ∑_{α ∈ (ℚ/ℤ)_{≤l}} conj (e (x α)) · Tle ρ 0 φ (M_α f) x`, and
* `variationalNorm_Tle_le_sum` — its `V^r` form,

together with the three elementary facts their proofs use
(`fourier_conj_mul_sub`, `TleKer_zero_eq_cw`, `TleKer_eq_char_mul_cw`,
`variationalNorm_unit_mul_le`).

They are *reproduced* here (in the separate namespace `…LowModApproxBoundedH.Lift`, so that no
name is shared with `mdlPartVar.lean`) because `mdlPartVar.lean` currently sits downstream of a
module with a duplicated declaration (`Work.KMTPlan.A6.MdlPartLowHighGain` clashes with
`Work.KMTAreas.A7.ModelApproxAux` on the name `lmaxR_nonneg`), so importing it is not possible
while that clash is present.  The statements and proofs are those of `mdlPartVar.lean`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlTleKer
import Submission.Work.KMTAreas.A7.lacDilTriVar
import Submission.Work.KMTAreas.A7.varShiftDiffPrep

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6.LowModApproxBoundedH.Lift

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.Analysis.IonescuWainger

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- The character identity behind the lift:
`conj (fourier x α) * fourier (x - j) α = conj (fourier j α)`. -/
theorem fourier_conj_mul_sub (α : Circ) (x j : ℤ) :
    (starRingEnd ℂ) (fourier (T := 1) x α) * fourier (T := 1) (x - j) α
      = (starRingEnd ℂ) (fourier (T := 1) j α) := by
  rw [← fourier_neg (T := 1) (n := x) (x := α), ← fourier_neg (T := 1) (n := j) (x := α)]
  rw [← fourier_add (T := 1) (m := -x) (n := x - j) (x := α)]
  ring_nf

/-- The height-`0` kernel is `cw φ`. -/
theorem TleKer_zero_eq_cw (ρ : ℝ) {φ : ℝ → ℂ} (hφ : Integrable φ) (j : ℤ) :
    Work.KMTPlan.A6.TleKer ρ 0 φ j = Work.KMTAreas.A7.cw φ j := by
  rw [Work.KMTPlan.A6.TleKer_eq_arChar_cw ρ 0 hφ j]
  have h1 : Work.KMTPlan.A6.TleArChar ρ 0 j = 1 := by
    rw [Work.KMTPlan.A6.TleArChar]
    have h0 : Work.Analysis.IonescuWainger.iwArithFreqs ρ 0
        = ({(0 : Circ)} : Finset Circ) := Work.KMTAreas.A7.iwArithFreqs_zero ρ
    rw [h0, Finset.sum_singleton]
    simp
  rw [h1, one_mul]

/-- The height-`l` kernel is the character-weighted height-`0` kernel. -/
theorem TleKer_eq_char_mul_cw (ρ : ℝ) (l : ℕ) {φ : ℝ → ℂ} (hφ : Integrable φ) (j : ℤ) :
    Work.KMTPlan.A6.TleKer ρ l φ j
      = (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
            (starRingEnd ℂ) (fourier (T := 1) j α)) * Work.KMTAreas.A7.cw φ j := by
  rw [Work.KMTPlan.A6.TleKer_eq_arChar_cw ρ l hφ j, Work.KMTPlan.A6.TleArChar]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  exact fourier_neg (n := j) (x := α)

/-- **The lift.**  For an integrable symbol `φ`, the cumulative Ionescu–Wainger multiplier at
arithmetic height `≤ l` is the finite sum over the arithmetic frequencies
`α ∈ (ℚ/ℤ)_{≤ l}` of the modulation `M_{-α}` of the *height-`0`* operator applied to `M_α f`. -/
theorem Tle_eq_sum_modulation (ρ : ℝ) (l : ℕ) {φ : ℝ → ℂ} (hφ : Integrable φ) (f : ℤ → ℂ)
    (Cf : ℝ) (hbdd : ∀ y : ℤ, ‖f y‖ ≤ Cf)
    (hcw : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw φ j‖) (x : ℤ) :
    Work.KMTAreas.A7.Tle ρ l φ f x
      = ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
          (starRingEnd ℂ) (fourier (T := 1) x α)
            * Work.KMTAreas.A7.Tle ρ 0 φ (fun y : ℤ => fourier (T := 1) y α * f y) x := by
  classical
  set A : Finset Circ := Work.Analysis.IonescuWainger.iwArithFreqs ρ l with hA
  have hK0 : ∀ j : ℤ, Work.KMTPlan.A6.TleKer ρ 0 φ j = Work.KMTAreas.A7.cw φ j :=
    fun j => TleKer_zero_eq_cw ρ hφ j
  have hKl : ∀ j : ℤ, Work.KMTPlan.A6.TleKer ρ l φ j
      = (∑ α ∈ A, (starRingEnd ℂ) (fourier (T := 1) j α)) * Work.KMTAreas.A7.cw φ j :=
    fun j => TleKer_eq_char_mul_cw ρ l hφ j
  -- the individual summands are summable
  have hsumm : ∀ α : Circ,
      Summable fun j : ℤ => (starRingEnd ℂ) (fourier (T := 1) j α)
        * (Work.KMTAreas.A7.cw φ j * f (x - j)) := by
    intro α
    refine Summable.of_norm_bounded (hcw.mul_right Cf) fun j => ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖(starRingEnd ℂ) (fourier (T := 1) j α)‖ = 1 := by
      rw [RCLike.norm_conj, fourier_apply]
      exact Circle.norm_coe _
    rw [h1, one_mul]
    exact mul_le_mul_of_nonneg_left (hbdd (x - j)) (norm_nonneg _)
  -- left-hand side as a sum over the arithmetic frequencies
  have hL : Work.KMTAreas.A7.Tle ρ l φ f x
      = ∑ α ∈ A, ∑' j : ℤ, (starRingEnd ℂ) (fourier (T := 1) j α)
          * (Work.KMTAreas.A7.cw φ j * f (x - j)) := by
    rw [Work.KMTPlan.A6.Tle_eq_convOp_TleKer ρ l φ f]
    show (∑' j : ℤ, Work.KMTPlan.A6.TleKer ρ l φ j * f (x - j)) = _
    have hstep : ∀ j : ℤ, Work.KMTPlan.A6.TleKer ρ l φ j * f (x - j)
        = ∑ α ∈ A, (starRingEnd ℂ) (fourier (T := 1) j α)
            * (Work.KMTAreas.A7.cw φ j * f (x - j)) := by
      intro j
      rw [hKl j, mul_assoc, Finset.sum_mul]
    rw [tsum_congr hstep]
    exact Summable.tsum_finsetSum (s := A) fun α _ => hsumm α
  -- each arithmetic frequency gives the modulated height-`0` operator
  have hR : ∀ α : Circ, (starRingEnd ℂ) (fourier (T := 1) x α)
        * Work.KMTAreas.A7.Tle ρ 0 φ (fun y : ℤ => fourier (T := 1) y α * f y) x
      = ∑' j : ℤ, (starRingEnd ℂ) (fourier (T := 1) j α)
          * (Work.KMTAreas.A7.cw φ j * f (x - j)) := by
    intro α
    rw [Work.KMTPlan.A6.Tle_eq_convOp_TleKer ρ 0 φ (fun y : ℤ => fourier (T := 1) y α * f y)]
    show (starRingEnd ℂ) (fourier (T := 1) x α)
        * (∑' j : ℤ, Work.KMTPlan.A6.TleKer ρ 0 φ j
            * (fourier (T := 1) (x - j) α * f (x - j)))
      = ∑' j : ℤ, (starRingEnd ℂ) (fourier (T := 1) j α)
          * (Work.KMTAreas.A7.cw φ j * f (x - j))
    rw [show (starRingEnd ℂ) (fourier (T := 1) x α)
          * (∑' j : ℤ, Work.KMTPlan.A6.TleKer ρ 0 φ j
              * (fourier (T := 1) (x - j) α * f (x - j)))
        = ∑' j : ℤ, (starRingEnd ℂ) (fourier (T := 1) x α)
              * (Work.KMTPlan.A6.TleKer ρ 0 φ j
                  * (fourier (T := 1) (x - j) α * f (x - j))) from
        (tsum_mul_left).symm]
    refine tsum_congr fun j => ?_
    rw [hK0 j]
    rw [show (starRingEnd ℂ) (fourier (T := 1) x α)
          * (Work.KMTAreas.A7.cw φ j * (fourier (T := 1) (x - j) α * f (x - j)))
        = ((starRingEnd ℂ) (fourier (T := 1) x α) * fourier (T := 1) (x - j) α)
            * (Work.KMTAreas.A7.cw φ j * f (x - j)) from by ring]
    rw [fourier_conj_mul_sub α x j]
  rw [hL]
  exact Finset.sum_congr rfl fun α _ => (hR α).symm

/-- Scaling a sequence family by a *unit modulus* scalar does not increase its variational norm. -/
theorem variationalNorm_unit_mul_le (r : NNReal) (hr : 1 ≤ r) (c : ℂ) (hc : ‖c‖ = 1)
    (w : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => c * w n)
      ≤ PointwiseErgodicTheorems.variationalNorm r w := by
  have hfam : (fun n : ℕ => c * w n) = c • w := rfl
  rw [hfam, Submission.PointwiseErgodicTheorems.variationalNorm_smul hr c w]
  have h1 : ‖c‖ₑ = 1 := by rw [← ofReal_norm, hc, ENNReal.ofReal_one]
  rw [h1, one_mul]

/-- **The level-`l` variational bound from the level-`0` one.**  For a family of integrable symbols
`ψ` with summable `cw`-coefficients and a bounded input `F`, the `r`-variation of the clipped
level-`l` family is dominated by the sum, over the arithmetic frequencies `α` of height `≤ l`, of
the `r`-variations of the (clipped) *level-`0`* families applied to the modulated inputs
`y ↦ fourier y α · F y`. -/
theorem variationalNorm_Tle_le_sum (ρ : ℝ) (l : ℕ) {ψ : ℕ → ℝ → ℂ}
    (hψ : ∀ n, Integrable (ψ n))
    (hcw : ∀ n, Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw (ψ n) j‖)
    (F : ℤ → ℂ) (Cf : ℝ) (hbdd : ∀ y : ℤ, ‖F y‖ ≤ Cf)
    (c : ℕ → Prop) [DecidablePred c] (r : NNReal) (hr : 1 ≤ r) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if c n then Work.KMTAreas.A7.Tle ρ l (ψ n) F x else 0)
      ≤ ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
          PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if c n then
              Work.KMTAreas.A7.Tle ρ 0 (ψ n) (fun y : ℤ => fourier (T := 1) y α * F y) x
              else 0) := by
  classical
  set A := Work.Analysis.IonescuWainger.iwArithFreqs ρ l with hA
  have hfun : (fun n : ℕ => if c n then Work.KMTAreas.A7.Tle ρ l (ψ n) F x else 0)
      = fun n : ℕ => ∑ α ∈ A, (starRingEnd ℂ) (fourier (T := 1) x α)
          * (if c n then Work.KMTAreas.A7.Tle ρ 0 (ψ n)
              (fun y : ℤ => fourier (T := 1) y α * F y) x else 0) := by
    funext n
    by_cases h : c n
    · rw [if_pos h, Tle_eq_sum_modulation ρ l (hψ n) F Cf hbdd (hcw n) x]
      exact Finset.sum_congr rfl fun α _ => by rw [if_pos h]
    · rw [if_neg h]
      exact (Finset.sum_eq_zero fun α _ => by rw [if_neg h, mul_zero]).symm
  rw [hfun]
  refine (Work.KMTAreas.A7.variationalNorm_finset_sum_le hr A (fun α n =>
      (starRingEnd ℂ) (fourier (T := 1) x α)
      * (if c n then Work.KMTAreas.A7.Tle ρ 0 (ψ n)
          (fun y : ℤ => fourier (T := 1) y α * F y) x else 0))).trans ?_
  refine Finset.sum_le_sum fun α _ => ?_
  refine variationalNorm_unit_mul_le r hr _ ?_ _
  rw [RCLike.norm_conj, fourier_apply]
  exact Circle.norm_coe _

end

end Work.KMTPlan.A6.LowModApproxBoundedH.Lift
