import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auPhiDisc
import Submission.Work.Resample.auWiRow
import Submission.Work.Resample.auLTwoMulAddLe
import Submission.Work.Resample.auMLe
import Submission.Work.Fx.norm_tdiv_sub_div_lt

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-! ## Helpers -/

/-- `2^p · fxC p z` recovers the Gaussian integer `z`. -/
theorem auTwoPow_mul_fxC (p : ℕ) (z : ℤ × ℤ) :
    (((2 : ℝ) ^ p : ℝ) : ℂ) * HvdH.fxC p z = (z.1 : ℂ) + (z.2 : ℂ) * Complex.I := by
  have h : (((2 : ℝ) ^ p : ℝ) : ℂ) = (2 : ℂ) ^ p := by push_cast; ring
  rw [h, HvdH.fxC, mul_div_cancel₀]
  exact pow_ne_zero _ (by norm_num)

/-- A point of the fixed-point disc has fixed-point value of modulus at most `1`. -/
theorem auFxCNormLeOne {p : ℕ} {z : ℤ × ℤ} (h : HvdH.inDisc p z) : ‖HvdH.fxC p z‖ ≤ 1 := by
  have h1 : ‖((z.1 : ℂ) + (z.2 : ℂ) * Complex.I)‖ ≤ (2 : ℝ) ^ p := normCplxOfInDisc p z h
  rw [HvdH.fxC, norm_div, norm_pow, Complex.norm_ofNat, div_le_one (by positivity)]
  exact h1

/-- The norm of a real complex number is its absolute value. -/
theorem auNorm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  nlinarith [norm_nonneg (r : ℂ), abs_nonneg r, sq_abs r]

/-- Arithmetic bound on the window length: `2·auL p α + 3 < p²` for `p ≥ 100`, `α² < p`. -/
theorem auL_two_mul_add_three_lt (p α : ℕ) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p) :
    2 * auL p α + 3 < p ^ 2 := by
  have hL : auL p α ≤ 4 * p + 1 := (auMLe p α hα hαp).2
  have h1 : 2 * auL p α + 3 ≤ 8 * p + 5 := by omega
  have h8 : 8 * p + 5 < p ^ 2 := by nlinarith [hp]
  omega

/-- The per-index weight accuracy bound, from the `∀ N : ℕ` form. -/
theorem auWt_perIndex (p α s t : ℕ)
    (hwt : ∀ (N : ℕ), |(auWt p α t (N : ℤ) : ℝ) - (2 : ℝ) ^ p * (1 / (2 * (α : ℝ))) *
      Real.exp (-(Real.pi * (N : ℝ) / ((α : ℝ) ^ 2 * (t : ℝ) ^ 2)))| ≤ 2) (k i : ℕ) :
    |(auWt p α t (auNsq p α s t k i) : ℝ) - (2 : ℝ) ^ p * auWi p α s t k i| ≤ 2 := by
  have hZ : (((auNsq p α s t k i).toNat : ℕ) : ℤ) = auNsq p α s t k i :=
    Int.toNat_of_nonneg (auNsq_nonneg p α s t k i)
  have hcast : (((auNsq p α s t k i).toNat : ℕ) : ℝ) = (auNsq p α s t k i : ℝ) := by
    rw [← Int.cast_natCast, hZ]
  have h := hwt ((auNsq p α s t k i).toNat)
  rw [hcast, hZ] at h
  rw [auWi]
  convert h using 1
  ring

theorem auFinal (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) (htp : t < 2 ^ p) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p) (hAnorm : ∀ (u : Fin s → ℂ), ‖(HvdH.resA s t α).mulVec u‖ ≤ 3 / 4 * ‖u‖) (hwt : ∀ (N : ℕ), |(auWt p α t (N : ℤ) : ℝ) - (2 : ℝ) ^ p * (1 / (2 * (α : ℝ))) * Real.exp (-(Real.pi * (N : ℝ) / ((α : ℝ) ^ 2 * (t : ℝ) ^ 2)))| ≤ 2) (htail : ∀ (u : Fin s → ℂ), ‖u‖ ≤ 1 → ∀ k : Fin t, ‖(∑ i ∈ Finset.range (auL p α), ((auWi p α s t (k : ℕ) i : ℝ) : ℂ) * u ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩) - (HvdH.resA s t α).mulVec u k‖ ≤ (2 : ℝ) ^ (-(p : ℤ))) : (∀ (w : Fin s → ℤ × ℤ), (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin t, HvdH.inDisc p (auPhi p α s t w k)) ∧ (∀ (w : Fin s → ℤ × ℤ), (∀ j, HvdH.inDisc p (w j)) → ∀ k : Fin t, ‖HvdH.fxC p (auPhi p α s t w k) - (HvdH.resA s t α).mulVec (fun j => HvdH.fxC p (w j)) k‖ * (2 : ℝ) ^ p < (p : ℝ) ^ 2) := by
  have _ := hAnorm
  have _ := hcop
  have _ := htp
  have hwt' : ∀ (k i : ℕ), |(auWt p α t (auNsq p α s t k i) : ℝ) -
      (2 : ℝ) ^ p * auWi p α s t k i| ≤ 2 := fun k i => auWt_perIndex p α s t hwt k i
  have hrow : ∀ k : Fin t, ∑ i ∈ Finset.range (auL p α), auWi p α s t (k : ℕ) i ≤ 3 / 4 :=
    fun k => auWiRow p α s t hs hα hαp hst k
  constructor
  · intro w hw k
    exact auPhiDisc p α s t hs hst hα hp hαp hwt' hrow w hw k
  · intro w hw k
    -- ### resolve the `if` in `auPhi`
    have hsumA : (∑ i ∈ Finset.range (auL p α),
          auWt p α t (auNsq p α s t (k : ℕ) i) *
            (if h : auJ p α s t (k : ℕ) i < s then w ⟨auJ p α s t (k : ℕ) i, h⟩ else 0).1)
        = ∑ i ∈ Finset.range (auL p α),
          auWt p α t (auNsq p α s t (k : ℕ) i) *
            (w ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩).1 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [dif_pos (auJ_lt p α s t (k : ℕ) i hs)]
    have hsumB : (∑ i ∈ Finset.range (auL p α),
          auWt p α t (auNsq p α s t (k : ℕ) i) *
            (if h : auJ p α s t (k : ℕ) i < s then w ⟨auJ p α s t (k : ℕ) i, h⟩ else 0).2)
        = ∑ i ∈ Finset.range (auL p α),
          auWt p α t (auNsq p α s t (k : ℕ) i) *
            (w ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩).2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [dif_pos (auJ_lt p α s t (k : ℕ) i hs)]
    set A : ℤ := ∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t (k : ℕ) i) *
          (w ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩).1 with hA
    set B : ℤ := ∑ i ∈ Finset.range (auL p α), auWt p α t (auNsq p α s t (k : ℕ) i) *
          (w ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩).2 with hB
    have hphi : auPhi p α s t w k = (Int.tdiv A ((2 : ℤ) ^ p), Int.tdiv B ((2 : ℤ) ^ p)) := by
      simp only [auPhi]
      rw [hsumA, hsumB, hA, hB]
    -- ### the vector of exact values
    set z : Fin s → ℂ := fun j => HvdH.fxC p (w j) with hz
    have hzj : ∀ j, ‖z j‖ ≤ 1 := fun j => auFxCNormLeOne (hw j)
    have hz1 : ‖z‖ ≤ 1 :=
      (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr hzj
    -- ### the two sums
    set Sw : ℂ := ∑ i ∈ Finset.range (auL p α),
        ((auWi p α s t (k : ℕ) i : ℝ) : ℂ) *
          z ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩ with hSw
    set S : ℂ := ∑ i ∈ Finset.range (auL p α),
        (auWt p α t (auNsq p α s t (k : ℕ) i) : ℂ) *
          z ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩ with hS
    have htailk : ‖Sw - (HvdH.resA s t α).mulVec z k‖ ≤ (2 : ℝ) ^ (-(p : ℤ)) := by
      rw [hSw]; exact htail z hz1 k
    -- ### `X = 2^p · fxC (auPhi …)`
    set X : ℂ := ((Int.tdiv A ((2 : ℤ) ^ p) : ℤ) : ℂ)
        + ((Int.tdiv B ((2 : ℤ) ^ p) : ℤ) : ℂ) * Complex.I with hX
    have hXfx : (((2 : ℝ) ^ p : ℝ) : ℂ) * HvdH.fxC p (auPhi p α s t w k) = X := by
      rw [hphi, hX]
      exact auTwoPow_mul_fxC p _
    -- ### `(A, B)` is `2^p · S`
    have hAfact : (A : ℂ) + (B : ℂ) * Complex.I = (((2 : ℝ) ^ p : ℝ) : ℂ) * S := by
      rw [hA, hB, hS]
      push_cast
      rw [Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hzval : (2 : ℂ) ^ p * z ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩
          = ((w ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩).1 : ℂ)
            + ((w ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩).2 : ℂ) * Complex.I := by
        have h2p : (((2 : ℝ) ^ p : ℝ) : ℂ) = (2 : ℂ) ^ p := by push_cast; ring
        rw [hz, ← h2p]
        exact auTwoPow_mul_fxC p _
      calc (auWt p α t (auNsq p α s t (k : ℕ) i) : ℂ)
              * ((w ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩).1 : ℂ)
            + (auWt p α t (auNsq p α s t (k : ℕ) i) : ℂ)
              * ((w ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩).2 : ℂ) * Complex.I
          = (auWt p α t (auNsq p α s t (k : ℕ) i) : ℂ)
              * (((w ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩).1 : ℂ)
                + ((w ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩).2 : ℂ)
                  * Complex.I) := by ring
        _ = (auWt p α t (auNsq p α s t (k : ℕ) i) : ℂ)
              * ((2 : ℂ) ^ p * z ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩) := by
              rw [hzval]
        _ = (2 : ℂ) ^ p * ((auWt p α t (auNsq p α s t (k : ℕ) i) : ℂ)
              * z ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩) := by ring
    have h2p_ne : (((2 : ℝ) ^ p : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]; positivity
    have hfrac : (((A : ℝ) : ℂ) + ((B : ℝ) : ℂ) * Complex.I) / (((2 : ℝ) ^ p : ℝ) : ℂ) = S := by
      rw [div_eq_iff h2p_ne]
      have hbridge : ((A : ℝ) : ℂ) + ((B : ℝ) : ℂ) * Complex.I = (A : ℂ) + (B : ℂ) * Complex.I := by
        push_cast; ring
      rw [hbridge, hAfact]
      ring
    -- ### Step A: the `tdiv` rounding
    have hSA : ‖X - S‖ ≤ 2 := by
      rw [hX, ← hfrac]
      have h := Work.Fx.norm_tdiv_sub_div_lt (A := A) (B := B) (b := 2 ^ p) (by positivity)
      have h2 : Real.sqrt 2 ≤ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      have h' : ‖((Int.tdiv A ((2 : ℤ) ^ p) : ℤ) : ℂ) + ((Int.tdiv B ((2 : ℤ) ^ p) : ℤ) : ℂ)
            * Complex.I
          - (((A : ℝ) : ℂ) + ((B : ℝ) : ℂ) * Complex.I) / (((2 : ℝ) ^ p : ℝ) : ℂ)‖
          < Real.sqrt 2 := by
        convert h using 2 <;> push_cast <;> ring
      linarith
    -- ### Step B: replacing the computed weights by the ideal ones
    have hdiff : S - (((2 : ℝ) ^ p : ℝ) : ℂ) * Sw
        = ∑ i ∈ Finset.range (auL p α),
            (((auWt p α t (auNsq p α s t (k : ℕ) i) : ℝ) : ℂ)
              - (((2 : ℝ) ^ p : ℝ) : ℂ) * ((auWi p α s t (k : ℕ) i : ℝ) : ℂ))
              * z ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩ := by
      rw [hS, hSw, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      push_cast
      ring
    have hSB : ‖S - (((2 : ℝ) ^ p : ℝ) : ℂ) * Sw‖ ≤ 2 * (auL p α : ℝ) := by
      rw [hdiff]
      have hterm : ∀ i ∈ Finset.range (auL p α),
          ‖(((auWt p α t (auNsq p α s t (k : ℕ) i) : ℝ) : ℂ)
              - (((2 : ℝ) ^ p : ℝ) : ℂ) * ((auWi p α s t (k : ℕ) i : ℝ) : ℂ))
              * z ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩‖ ≤ 2 := by
        intro i _
        rw [norm_mul]
        have h1 : ‖(((auWt p α t (auNsq p α s t (k : ℕ) i) : ℝ) : ℂ)
              - (((2 : ℝ) ^ p : ℝ) : ℂ) * ((auWi p α s t (k : ℕ) i : ℝ) : ℂ))‖
            = |(auWt p α t (auNsq p α s t (k : ℕ) i) : ℝ)
                - (2 : ℝ) ^ p * auWi p α s t (k : ℕ) i| := by
          rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, auNorm_ofReal]
        rw [h1]
        have h2 := hwt' (k : ℕ) i
        have h3 := hzj ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩
        nlinarith [h2, h3,
          norm_nonneg (z ⟨auJ p α s t (k : ℕ) i, auJ_lt p α s t (k : ℕ) i hs⟩)]
      calc ‖∑ i ∈ Finset.range (auL p α), _‖
            ≤ ∑ i ∈ Finset.range (auL p α), ‖_‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range (auL p α), (2 : ℝ) := Finset.sum_le_sum hterm
        _ = 2 * (auL p α : ℝ) := by
            rw [Finset.sum_const, Finset.card_range]
            simp only [nsmul_eq_mul]
            push_cast
            ring
    -- ### Step C: the discarded tail
    have hT : ‖-((((2 : ℝ) ^ p : ℝ) : ℂ) * ((HvdH.resA s t α).mulVec z k - Sw))‖ ≤ 1 := by
      rw [norm_neg, norm_mul, auNorm_ofReal, abs_of_nonneg (by positivity)]
      have h2 : ‖(HvdH.resA s t α).mulVec z k - Sw‖ ≤ (2 : ℝ) ^ (-(p : ℤ)) := by
        rw [norm_sub_rev]; exact htailk
      calc (2 : ℝ) ^ p * ‖(HvdH.resA s t α).mulVec z k - Sw‖
            ≤ (2 : ℝ) ^ p * (2 : ℝ) ^ (-(p : ℤ)) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 1 := by
            rw [zpow_neg, zpow_natCast, mul_inv_cancel₀ (by positivity)]
    -- ### Assembly
    have hid : X - (((2 : ℝ) ^ p : ℝ) : ℂ) * ((HvdH.resA s t α).mulVec z k)
        = (X - S) + (S - (((2 : ℝ) ^ p : ℝ) : ℂ) * Sw)
          + (-((((2 : ℝ) ^ p : ℝ) : ℂ) * ((HvdH.resA s t α).mulVec z k - Sw))) := by ring
    have hfinal : ‖X - (((2 : ℝ) ^ p : ℝ) : ℂ) * ((HvdH.resA s t α).mulVec z k)‖
        ≤ 2 * (auL p α : ℝ) + 3 := by
      rw [hid]
      have h1 := norm_add_le ((X - S) + (S - (((2 : ℝ) ^ p : ℝ) : ℂ) * Sw))
        (-((((2 : ℝ) ^ p : ℝ) : ℂ) * ((HvdH.resA s t α).mulVec z k - Sw)))
      have h2 := norm_add_le (X - S) (S - (((2 : ℝ) ^ p : ℝ) : ℂ) * Sw)
      linarith [h1, h2, hSA, hSB, hT]
    have hgoal : ‖HvdH.fxC p (auPhi p α s t w k) - (HvdH.resA s t α).mulVec z k‖ * (2 : ℝ) ^ p
        = ‖X - (((2 : ℝ) ^ p : ℝ) : ℂ) * ((HvdH.resA s t α).mulVec z k)‖ := by
      have h1 : ‖HvdH.fxC p (auPhi p α s t w k) - (HvdH.resA s t α).mulVec z k‖ * (2 : ℝ) ^ p
          = ‖(((2 : ℝ) ^ p : ℝ) : ℂ)
              * (HvdH.fxC p (auPhi p α s t w k) - (HvdH.resA s t α).mulVec z k)‖ := by
        rw [norm_mul, auNorm_ofReal, abs_of_nonneg (by positivity), mul_comm]
      rw [h1, mul_sub, hXfx]
    have hL : 2 * (auL p α : ℝ) + 3 < (p : ℝ) ^ 2 := by
      have := auL_two_mul_add_three_lt p α hα hp hαp
      exact_mod_cast this
    rw [hgoal]
    linarith [hfinal, hL]

end Work.Resample
