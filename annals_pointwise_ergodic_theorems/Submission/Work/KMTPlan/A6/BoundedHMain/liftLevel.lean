/-
# The level-`l` low-pass lacunary walk from the level-`0` one (bounded input)

At a *bounded* arithmetic height `l ≤ B` the level-`l` Ionescu--Wainger projection at a monotone
family of windows is a **finite** sum of modulated level-`0` projections:

  `Π_{≤l,≤-M} = Tle ρ l (η_{≤-M}) = ∑_{α ∈ (ℚ/ℤ)_{≤l}} conj (χ α ·) · Tle ρ 0 (η_{≤-M}) (χ α · ·)`

(`Work.KMTPlan.A6.LowModApproxBoundedH.Tle_eq_sum_modulation`, valid for *bounded* inputs).  Since
modulations do not change the variational norm
(`Work.KMTPlan.A6.LowModApproxBoundedH.variationalNorm_unit_mul_le`) and the number of arithmetic
frequencies is bounded by `|(ℚ/ℤ)_{≤B}|` (a constant at bounded height), the level-`l` packet
estimate reduces to the *unconditional* level-`0` estimate
`Work.KMTPlan.A6.BoundedHMain.lowpassSubfamilyVar`.  This gives the `f`-side and `g`-side linear packet
estimate of the concrete `§5` columns at bounded height **without** `AreaA1` and **without** the
workspace's canonical crux `A7HiRep.chainPartSqFun` (which the general, unbounded-height route
needs).

The boundedness of the input is used only to *justify the identity*; the estimate for arbitrary
`f ∈ ℓ^2` follows from it by the standard density/Fatou argument, using the `ℓ^2`-boundedness of
the IW projections (`Work.KMTPlan.A6.eLpNorm_iwConv_two_le_of_symbol_bound`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlTleKer
import Submission.Work.KMTAreas.A7.residueLp_fiberOp_le_of_projection
import Submission.Work.KMTAreas.A7LoLin.lepingle

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6.BoundedHMain

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7
open Work.Analysis.IonescuWainger

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## The elementary facts of the level-`0`/level-`l` interface -/

/-- The character identity `conj (χ_x α) * χ_{x-j} α = conj (χ_j α)`. -/
theorem fourier_conj_mul_sub' (α : Circ) (x j : ℤ) :
    (starRingEnd ℂ) (fourier (T := 1) x α) * fourier (T := 1) (x - j) α
      = (starRingEnd ℂ) (fourier (T := 1) j α) := by
  rw [← fourier_neg (T := 1) (n := x) (x := α), ← fourier_neg (T := 1) (n := j) (x := α)]
  rw [← fourier_add (T := 1) (m := -x) (n := x - j) (x := α)]
  ring_nf

/-- Multiplying a sequence family by a *unit modulus* scalar does not increase its variational
norm. -/
theorem variationalNorm_unit_mul_le' (r : NNReal) (hr : 1 ≤ r) (c : ℂ) (hc : ‖c‖ = 1)
    (w : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => c * w n)
      ≤ PointwiseErgodicTheorems.variationalNorm r w := by
  have hfam : (fun n : ℕ => c * w n) = c • w := rfl
  rw [hfam, Submission.PointwiseErgodicTheorems.variationalNorm_smul hr c w]
  have h1 : ‖c‖ₑ = 1 := by rw [← ofReal_norm, hc, ENNReal.ofReal_one]
  rw [h1, one_mul]

/-- The height-`0` kernel is `cw φ`. -/
theorem TleKer_zero_eq_cw' (ρ : ℝ) {φ : ℝ → ℂ} (hφ : Integrable φ) (j : ℤ) :
    Work.KMTPlan.A6.TleKer ρ 0 φ j = Work.KMTAreas.A7.cw φ j := by
  rw [Work.KMTPlan.A6.TleKer_eq_arChar_cw ρ 0 hφ j]
  have h1 : Work.KMTPlan.A6.TleArChar ρ 0 j = 1 := by
    rw [Work.KMTPlan.A6.TleArChar]
    have h0 : iwArithFreqs ρ 0 = ({(0 : Circ)} : Finset Circ) := iwArithFreqs_zero ρ
    rw [h0, Finset.sum_singleton]
    simp
  rw [h1, one_mul]

/-- The height-`l` kernel is the character-weighted height-`0` kernel. -/
theorem TleKer_eq_char_mul_cw' (ρ : ℝ) (l : ℕ) {φ : ℝ → ℂ} (hφ : Integrable φ) (j : ℤ) :
    Work.KMTPlan.A6.TleKer ρ l φ j
      = (∑ α ∈ iwArithFreqs ρ l, (starRingEnd ℂ) (fourier (T := 1) j α))
          * Work.KMTAreas.A7.cw φ j := by
  rw [Work.KMTPlan.A6.TleKer_eq_arChar_cw ρ l hφ j, Work.KMTPlan.A6.TleArChar]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  exact fourier_neg (n := j) (x := α)

/-- **The lift.**  For an integrable symbol `φ` with summable `cw`-coefficients and a *bounded*
input `f`, the cumulative Ionescu--Wainger multiplier at arithmetic height `≤ l` is the finite sum,
over the arithmetic frequencies `α ∈ (ℚ/ℤ)_{≤l}`, of the modulation `χ_{-α}` of the *height-`0`*
operator applied to `χ_α f`. -/
theorem Tle_eq_sum_modulation' (ρ : ℝ) (l : ℕ) {φ : ℝ → ℂ} (hφ : Integrable φ) (f : ℤ → ℂ)
    (Cf : ℝ) (hbdd : ∀ y : ℤ, ‖f y‖ ≤ Cf)
    (hcw : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw φ j‖) (x : ℤ) :
    Work.KMTAreas.A7.Tle ρ l φ f x
      = ∑ α ∈ iwArithFreqs ρ l,
          (starRingEnd ℂ) (fourier (T := 1) x α)
            * Work.KMTAreas.A7.Tle ρ 0 φ (fun y : ℤ => fourier (T := 1) y α * f y) x := by
  classical
  set A : Finset Circ := iwArithFreqs ρ l with hA
  have hK0 : ∀ j : ℤ, Work.KMTPlan.A6.TleKer ρ 0 φ j = Work.KMTAreas.A7.cw φ j :=
    fun j => TleKer_zero_eq_cw' ρ hφ j
  have hKl : ∀ j : ℤ, Work.KMTPlan.A6.TleKer ρ l φ j
      = (∑ α ∈ A, (starRingEnd ℂ) (fourier (T := 1) j α)) * Work.KMTAreas.A7.cw φ j :=
    fun j => TleKer_eq_char_mul_cw' ρ l hφ j
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
    rw [fourier_conj_mul_sub' α x j]
  rw [hL]
  exact Finset.sum_congr rfl fun α _ => (hR α).symm

/-- `etaCut kmtEta k` is integrable (it is compactly supported and continuous). -/
theorem integrable_etaCut_kmtEta (k : ℤ) :
    Integrable (etaCut Work.KMTContract.kmtEta k : ℝ → ℂ) :=
  (Work.KMTAreas.A7.contDiff_etaCut k).continuous.integrable_of_hasCompactSupport
    (Work.KMTAreas.A7.hasCompactSupport_etaCut k)

end

end Work.KMTPlan.A6.BoundedHMain
