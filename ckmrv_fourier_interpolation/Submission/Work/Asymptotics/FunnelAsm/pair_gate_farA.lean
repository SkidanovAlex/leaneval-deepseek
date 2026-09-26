/-
# The far-region pair gate

This file proves `Work.Asymptotics.pair_gate_far`: for every `τ` with `Im τ ≥ 2` the two
leading cusp coefficients `G_{1,0}`, `G_{1,1}` of the dimension-`24` kernel do not vanish
simultaneously.

## Structure of the argument

* **Strip reduction** (`Submission/Work/Asymptotics/PGFar/Reduction`).  Write `τ = w + n` with
  `n = ⌊Re τ + 1/2⌋ ∈ ℤ` and `w = τ - n` in the fundamental strip `Strip w`
  (`|Re w| ≤ 1/2`, `Im w = Im τ ≥ 2`).  Both components of the pair are *affine* along the
  `T`-orbits: `G_{1,1}(τ) = (i/3456)(F24 w - 2πinA24 w)` and
  `G_{1,0}(τ) = G_{1,0} w + n·(G_{1,0}(w+1) - G_{1,0} w)`.  Hence, if both components vanish,
  the vanishing of the second gives `n = F24 w/(2πiA24 w)`, and substituting into the first
  `G_{1,0} τ = G_{1,0} w + F24 w·(G_{1,0}(w+1)-G_{1,0}w)/(2πiA24 w)`.

* **The strip estimate** (`strip_core` below).  On the strip `‖nomeQ w‖ ≤ e^{-4π} ≤ 1/280000`
  is tiny and the four quantitative inputs of `StripBounds` give a contradiction.
-/
import Mathlib
import Submission.Work.Asymptotics.PGFar.Defs
import Submission.Work.Asymptotics.PGFar.Reduction
import Submission.Work.Asymptotics.FunnelAsm.EisensteinQExpA
import Submission.Work.Asymptotics.ThetaQExp
import Submission.Work.Asymptotics.FunnelAsm.StripBoundsProofsA
import Submission.Work.Asymptotics.LfunQExp
import Submission.Work.Asymptotics.CuspL_eq
import Submission.Work.Asymptotics.LogLambdaData_L_eq_Lfun
import Submission.Work.Residues.XiSlashS
import Submission.Work.Kernels.KernelFacts.psi2_T2
import Submission.Work.Asymptotics.FunnelAsm.G10BoundsA

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup

noncomputable section

/-- The four quantitative strip estimates on which the far-region pair gate rests. -/
structure StripBounds (ℓ : Work.Kernels.LogLambdaData) : Prop where
  hF24 : ∀ w : UpperHalfPlane, Strip w →
    ‖F24 w - (3456 * nomeQ w
        + (3908736 + 2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * 725760) * (nomeQ w) ^ 2)‖
      ≤ 1000000000 * (1 + ‖(w : ℂ)‖) * ‖nomeQ w‖ ^ 3
  hA24 : ∀ w : UpperHalfPlane, Strip w →
    ‖A24 w + 725760 * (nomeQ w) ^ 2‖ ≤ 1000000000 * ‖nomeQ w‖ ^ 3
  hG10 : ∀ w : UpperHalfPlane, Strip w →
    ‖Gcusp ℓ 24 1 0 w‖ ≤ 5 * (1 + ‖(w : ℂ)‖) * ‖nomeQ w‖
  hDG10 : ∀ w : UpperHalfPlane, Strip w →
    ‖Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ w) - Gcusp ℓ 24 1 0 w + Complex.I * nomeQ w‖
      ≤ 100000 * ‖nomeQ w‖ ^ 2

/-- The numeric core of the far-region pair gate: on the fundamental strip the two affine
components cannot vanish simultaneously. -/
theorem strip_core (ℓ : Work.Kernels.LogLambdaData) (B : StripBounds ℓ) (n : ℤ)
    (w : UpperHalfPlane) (hw : Strip w)
    (hF24eq : F24 w = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * A24 w)) :
    Gcusp ℓ 24 1 0 w + (n : ℂ) * (Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ w) - Gcusp ℓ 24 1 0 w) ≠ 0 := by
  intro hz
  obtain ⟨hQ1, hRQ1, h1R⟩ := strip_facts w hw
  set Q := ‖nomeQ w‖ with hQdef
  set R := ‖(w : ℂ)‖ with hRdef
  have hQpos : 0 < Q := by rw [hQdef]; exact norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hQ2 : Q ^ 2 ≤ (1 / 280000) * Q := by
    have h2 : Q ^ 2 = Q * Q := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_right hQ1 hQpos.le
  have hRQ2 : R * Q ^ 2 ≤ (3 / 280000) * Q := by
    have h2 : R * Q ^ 2 = (R * Q) * Q := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_right hRQ1 hQpos.le
  have h1RQ3 : (1 + R) * Q ^ 3 ≤ (4 / 280000) * Q ^ 2 := by
    have h2 : (1 + R) * Q ^ 3 = ((1 + R) * Q) * Q ^ 2 := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1R (by positivity)
  -- ## the F24 truncation and its error
  have herr : ‖F24 w - (3456 * nomeQ w
      + (3908736 + 2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * 725760) * (nomeQ w) ^ 2)‖
      ≤ 1000000000 * (4 / 280000) * Q ^ 2 := by
    have h := B.hF24 w hw
    rw [← hRdef, ← hQdef] at h
    refine le_trans h ?_
    calc (1000000000 : ℝ) * (1 + R) * Q ^ 3
        = 1000000000 * ((1 + R) * Q ^ 3) := by ring
      _ ≤ 1000000000 * ((4 / 280000) * Q ^ 2) :=
          mul_le_mul_of_nonneg_left h1RQ3 (by norm_num)
      _ = 1000000000 * (4 / 280000) * Q ^ 2 := by ring
  -- ## lower bound for the truncation
  have hpb : ‖(3908736 + 2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * 725760) * (nomeQ w) ^ 2‖
      ≤ (3908736 + 2 * Real.pi * 725760 * R) * Q ^ 2 := by
    rw [norm_mul, norm_pow, hQdef]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h1 : ‖(3908736 : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * 725760‖
        ≤ 3908736 + ‖2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * 725760‖ := by
      have h := norm_add_le (3908736 : ℂ) (2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * 725760)
      simpa using h
    have h2 : ‖2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * 725760‖ = 2 * Real.pi * 725760 * R := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul, hRdef]
      simp only [Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, mul_one]
      ring
    linarith [h1, h2]
  have hT : ‖(3456 : ℂ) * nomeQ w
      + (3908736 + 2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * 725760) * (nomeQ w) ^ 2‖
      ≥ 3456 * Q - (3908736 + 2 * Real.pi * 725760 * R) * Q ^ 2 := by
    have h1 : ‖(3456 : ℂ) * nomeQ w‖ = 3456 * Q := by
      rw [norm_mul, Complex.norm_ofNat, hQdef]
    have hsub := norm_sub_le ((3456 : ℂ) * nomeQ w
        + (3908736 + 2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * 725760) * (nomeQ w) ^ 2)
      ((3908736 + 2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * 725760) * (nomeQ w) ^ 2)
    rw [add_sub_cancel_right, h1] at hsub
    linarith [hsub, hpb]
  have hmixed : (3908736 + 2 * Real.pi * 725760 * R) * Q ^ 2 ≤ 80 * Q := by
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    nlinarith [hQ2, hRQ2, hpi, Real.pi_pos, hQpos]
  have hF24low : (3370 : ℝ) * Q ≤ ‖F24 w‖ := by
    set poly := (3456 : ℂ) * nomeQ w
      + (3908736 + 2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * 725760) * (nomeQ w) ^ 2 with hpdef
    have h1 : ‖poly‖ ≥ 3456 * Q - (3908736 + 2 * Real.pi * 725760 * R) * Q ^ 2 := hT
    have h2 : ‖F24 w‖ ≥ ‖poly‖ - ‖F24 w - poly‖ := by
      have h := norm_sub_le (F24 w) (F24 w - poly)
      have he : F24 w - (F24 w - poly) = poly := by ring
      rw [he] at h
      linarith [h]
    have herr' : ‖F24 w - poly‖ ≤ 1000000000 * (4 / 280000) * Q ^ 2 := herr
    have herr2 : ‖F24 w - poly‖ ≤ (1000000000 * (4 / 280000)) * ((1 / 280000) * Q) :=
      le_trans herr' (mul_le_mul_of_nonneg_left hQ2 (by norm_num))
    have hpoly : (3376 : ℝ) * Q ≤ ‖poly‖ := by linarith [h1, hmixed]
    linarith [hpoly, h2, herr2]
  -- ## upper bound for `A24`
  have hA24up : ‖A24 w‖ ≤ 729332 * Q ^ 2 := by
    have h := B.hA24 w hw
    rw [← hQdef] at h
    have h1 : ‖A24 w‖ ≤ ‖A24 w + 725760 * (nomeQ w) ^ 2‖ + 725760 * Q ^ 2 := by
      have hsub := norm_sub_le (A24 w + 725760 * (nomeQ w) ^ 2) (725760 * (nomeQ w) ^ 2)
      rw [add_sub_cancel_right, norm_mul, Complex.norm_ofNat, norm_pow, ← hQdef] at hsub
      linarith [hsub]
    have h3 : (1000000000 : ℝ) * Q ^ 3 ≤ (1000000000 / 280000) * Q ^ 2 := by
      have h2 : Q ^ 3 = Q * Q ^ 2 := by ring
      have h4 : Q * Q ^ 2 ≤ (1 / 280000) * Q ^ 2 :=
        mul_le_mul_of_nonneg_right hQ1 (by positivity)
      nlinarith [h4]
    nlinarith [h1, h, h3, norm_nonneg (A24 w)]
  -- ## lower bound for `‖(n : ℂ)‖`
  have hnormF : ‖F24 w‖ = ‖(n : ℂ)‖ * (2 * Real.pi * ‖A24 w‖) := by
    rw [hF24eq, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hn : (57 / 100000 : ℝ) ≤ ‖(n : ℂ)‖ * Q := by
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    have h1 : ‖(n : ℂ)‖ * (2 * Real.pi * ‖A24 w‖) ≤ ‖(n : ℂ)‖ * (2 * 4 * (729332 * Q ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      nlinarith [hA24up, hpi, Real.pi_pos]
    rw [hnormF] at hF24low
    have h2 : (3370 : ℝ) * Q ≤ ‖(n : ℂ)‖ * (2 * 4 * (729332 * Q ^ 2)) := le_trans hF24low h1
    have h3 : (3370 : ℝ) ≤ ‖(n : ℂ)‖ * (2 * 4 * (729332 : ℝ)) * Q := by
      have h2' : ‖(n : ℂ)‖ * (2 * 4 * (729332 * Q ^ 2))
          = ‖(n : ℂ)‖ * (2 * 4 * (729332 : ℝ)) * Q ^ 2 := by ring
      rw [h2'] at h2
      have := h2
      nlinarith [this, hQpos]
    nlinarith [h3]
  -- ## lower bound for the `T`-difference
  have hDlow : (16 / 25 : ℝ) * Q
      ≤ ‖Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ w) - Gcusp ℓ 24 1 0 w‖ := by
    set D := Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ w) - Gcusp ℓ 24 1 0 w with hDdef
    have h := B.hDG10 w hw
    rw [← hQdef] at h
    have h1 : Q ≤ ‖D‖ + 100000 * Q ^ 2 := by
      have h2 : ‖Complex.I * nomeQ w‖ ≤ ‖D + Complex.I * nomeQ w‖ + ‖D‖ := by
        have h3 := norm_sub_le (D + Complex.I * nomeQ w) D
        rw [add_sub_cancel_left] at h3
        linarith [h3]
      have h4 : ‖Complex.I * nomeQ w‖ = Q := by
        rw [norm_mul, Complex.norm_I, one_mul]
      rw [h4] at h2
      linarith [h2, h]
    have h5 : 100000 * Q ^ 2 ≤ (100000 / 280000) * Q := by nlinarith [hQ2]
    have h6 : (16 / 25 : ℝ) * Q ≤ Q - 100000 * Q ^ 2 := by nlinarith [h5]
    linarith [h1, h6]
  -- ## upper bound for `G_{1,0} w`
  have hGup : ‖Gcusp ℓ 24 1 0 w‖ ≤ 20 / 280000 := by
    have h := B.hG10 w hw
    rw [← hRdef, ← hQdef] at h
    nlinarith [h, h1R, norm_nonneg (Gcusp ℓ 24 1 0 w)]
  -- ## the contradiction
  have hfin : (29 / 100000 : ℝ) ≤ ‖Gcusp ℓ 24 1 0 w
      + (n : ℂ) * (Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ w) - Gcusp ℓ 24 1 0 w)‖ := by
    have hmul : ‖(n : ℂ) * (Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ w) - Gcusp ℓ 24 1 0 w)‖
        = ‖(n : ℂ)‖ * ‖Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ w) - Gcusp ℓ 24 1 0 w‖ := norm_mul _ _
    have h2 : (3648 / 10000000 : ℝ) ≤ ‖(n : ℂ) * (Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ w)
        - Gcusp ℓ 24 1 0 w)‖ := by
      rw [hmul]
      have h3 : (57 / 100000 / Q) * ((16 / 25) * Q)
          ≤ ‖(n : ℂ)‖ * ‖Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ w) - Gcusp ℓ 24 1 0 w‖ := by
        have hb : (57 / 100000 / Q : ℝ) ≤ ‖(n : ℂ)‖ := by
          rw [div_le_iff₀ hQpos]
          exact hn
        exact mul_le_mul hb hDlow (mul_nonneg (by norm_num) hQpos.le) (norm_nonneg _)
      have h4 : (57 / 100000 / Q) * ((16 / 25) * Q) = 3648 / 10000000 := by
        field_simp
        norm_num
      linarith [h3, h4.le]
    have h5 : ‖Gcusp ℓ 24 1 0 w
        + (n : ℂ) * (Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ w) - Gcusp ℓ 24 1 0 w)‖
        ≥ ‖(n : ℂ) * (Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ w) - Gcusp ℓ 24 1 0 w)‖
          - ‖Gcusp ℓ 24 1 0 w‖ := by
      have h6 := norm_sub_le ((n : ℂ) * (Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ w) - Gcusp ℓ 24 1 0 w)
        + Gcusp ℓ 24 1 0 w) (Gcusp ℓ 24 1 0 w)
      rw [add_sub_cancel_right] at h6
      have h7 : ‖Gcusp ℓ 24 1 0 w
          + (n : ℂ) * (Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ w) - Gcusp ℓ 24 1 0 w)‖
          = ‖(n : ℂ) * (Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ w) - Gcusp ℓ 24 1 0 w)
            + Gcusp ℓ 24 1 0 w‖ := by rw [add_comm]
      rw [h7]
      linarith [h6]
    linarith [h2, h5, hGup]
  rw [hz, norm_zero] at hfin
  norm_num at hfin

end


open UpperHalfPlane

/-- Every point `τ` with `Im τ ≥ 2` is an integer translate of a point of the fundamental
strip `Strip`. -/
lemma exists_strip_decomposition (τ : UpperHalfPlane) (h : 2 ≤ τ.im) :
    ∃ (n : ℤ) (w : UpperHalfPlane), Strip w ∧ (n : ℝ) +ᵥ w = τ := by
  refine ⟨⌊τ.re + 1 / 2⌋, (-((⌊τ.re + 1 / 2⌋ : ℤ) : ℝ)) +ᵥ τ, ⟨?_, ?_⟩, ?_⟩
  · -- `|w.re| ≤ 1/2`
    have hco : (((-((⌊τ.re + 1 / 2⌋ : ℤ) : ℝ)) +ᵥ τ : UpperHalfPlane) : ℂ)
        = -((⌊τ.re + 1 / 2⌋ : ℤ) : ℂ) + (τ : ℂ) := by
      rw [UpperHalfPlane.coe_vadd]; push_cast; ring
    have hre : ((-((⌊τ.re + 1 / 2⌋ : ℤ) : ℝ)) +ᵥ τ).re
        = τ.re - ((⌊τ.re + 1 / 2⌋ : ℤ) : ℝ) := by
      rw [← UpperHalfPlane.coe_re, hco]
      simp only [Complex.add_re, Complex.neg_re, UpperHalfPlane.coe_re]
      norm_num
      ring
    rw [hre, abs_le]
    have h1 : ((⌊τ.re + 1 / 2⌋ : ℤ) : ℝ) ≤ τ.re + 1 / 2 := Int.floor_le _
    have h2 : τ.re + 1 / 2 < ((⌊τ.re + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    constructor <;> linarith
  · -- `2 ≤ w.im`
    have hco : (((-((⌊τ.re + 1 / 2⌋ : ℤ) : ℝ)) +ᵥ τ : UpperHalfPlane) : ℂ)
        = -((⌊τ.re + 1 / 2⌋ : ℤ) : ℂ) + (τ : ℂ) := by
      rw [UpperHalfPlane.coe_vadd]; push_cast; ring
    have him : ((-((⌊τ.re + 1 / 2⌋ : ℤ) : ℝ)) +ᵥ τ).im = τ.im := by
      rw [← UpperHalfPlane.coe_im, hco]
      simp
    rw [him]; exact h
  · -- `(n : ℝ) +ᵥ w = τ`
    rw [← add_vadd, add_neg_cancel, zero_vadd]

/-- **The far-region pair gate, conditional on the four strip estimates.** -/
theorem pair_gate_far_of_bounds (ℓ : Work.Kernels.LogLambdaData) (B : StripBounds ℓ)
    (τ : UpperHalfPlane) (h : 2 ≤ τ.im) :
    (Work.Asymptotics.Gcusp ℓ 24 1 0 τ, Work.Asymptotics.Gcusp ℓ 24 1 1 τ) ≠ (0, 0) := by
  intro hzero
  have h10 : Gcusp ℓ 24 1 0 τ = 0 := by simpa using congrArg Prod.fst hzero
  have h11 : Gcusp ℓ 24 1 1 τ = 0 := by simpa using congrArg Prod.snd hzero
  obtain ⟨n, w, hwstrip, hnw⟩ := exists_strip_decomposition τ h
  have hG11w : Gcusp ℓ 24 1 1 w = (Complex.I / 3456) * F24 w := by
    show Gcusp24 ℓ 1 1 w = (Complex.I / 3456) * F24 w
    rw [Gcusp24_one_one]
  have hF24eq : F24 w = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * A24 w) := by
    have hlaw := Gcusp11_vadd_int ℓ n w
    rw [hnw, h11] at hlaw
    -- `0 = G_{1,1} w - (i/3456)(2πin)A24 w`
    have h2 : Gcusp ℓ 24 1 1 w
        = (Complex.I / 3456) * (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * A24 w :=
      sub_eq_zero.mp hlaw.symm
    rw [hG11w] at h2
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have h3 : (Complex.I / 3456) * F24 w
        = (Complex.I / 3456) * ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * A24 w)) := by
      rw [h2]; ring
    have h4 : (Complex.I / 3456) ≠ 0 := by
      simp [hI]
    exact mul_left_cancel₀ h4 h3
  have h10w := Gcusp10_vadd_int ℓ n w
  rw [hnw, h10] at h10w
  exact strip_core ℓ B n w hwstrip hF24eq h10w.symm


/-- **The far-region pair gate**, conditional on the two remaining strip estimates on the first
component `G_{1,0}`.  The other two inputs of `StripBounds` are the proved second-order
`q`-expansions of `A24` and `F24`. -/
theorem pair_gate_far_of_strip (ℓ : Work.Kernels.LogLambdaData)
    (hG10 : ∀ w : UpperHalfPlane, Strip w →
      ‖Gcusp ℓ 24 1 0 w‖ ≤ 5 * (1 + ‖(w : ℂ)‖) * ‖nomeQ w‖)
    (hDG10 : ∀ w : UpperHalfPlane, Strip w →
      ‖Gcusp ℓ 24 1 0 ((1 : ℝ) +ᵥ w) - Gcusp ℓ 24 1 0 w + Complex.I * nomeQ w‖
        ≤ 100000 * ‖nomeQ w‖ ^ 2)
    (τ : UpperHalfPlane) (h : 2 ≤ τ.im) :
    (Work.Asymptotics.Gcusp ℓ 24 1 0 τ, Work.Asymptotics.Gcusp ℓ 24 1 1 τ) ≠ (0, 0) :=
  pair_gate_far_of_bounds ℓ
    { hF24 := fun w hw => PGF24StripBound w hw
      hA24 := fun w hw => PGA24StripBound w hw
      hG10 := hG10
      hDG10 := hDG10 } τ h

/-- **The far-region pair gate.** -/
theorem pair_gate_far (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) (h : 2 ≤ τ.im) :
    (Work.Asymptotics.Gcusp ℓ 24 1 0 τ, Work.Asymptotics.Gcusp ℓ 24 1 1 τ) ≠ (0, 0) :=
  pair_gate_far_of_strip ℓ (fun w hw => PGGcusp10StripBound ℓ w hw)
    (fun w hw => PGGcusp10DeltaBound ℓ w hw) τ h

end Work.Asymptotics
