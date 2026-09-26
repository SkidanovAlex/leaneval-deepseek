import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.Rigidity.SlashSTdefTendstoZeroInP
import Submission.Work.CKFinal.Xi24_Delta_bound
import Submission.Work.CKFinal.LineDecay.Ncusp24_delta_funnel_zfree

namespace Work.CKFinal.LineDecay

open UpperHalfPlane MeasureTheory
open scoped Topology Manifold

noncomputable section

/-! ## Auxiliary facts about `Ξ₂₄` -/

/-- `Ξ₂₄` is invariant under translation of its second variable by `1`. -/
lemma Xi24_vadd_one (τ z : ℍ) :
    Work.Asymptotics.Xi24 τ ((1 : ℝ) +ᵥ z) = Work.Asymptotics.Xi24 τ z := by
  simp only [Work.Asymptotics.Xi24, Work.Kernels.KernelFacts.fk_vadd_one,
    Work.Kernels.KernelFacts.jInvariantFun_vadd_one, Work.Kernels.E2Fun_vadd_one]

/-- `Ξ₂₄` is invariant under integer translations of its second variable. -/
lemma Xi24_vadd_int (τ z : ℍ) (k : ℤ) :
    Work.Asymptotics.Xi24 τ ((k : ℝ) +ᵥ z) = Work.Asymptotics.Xi24 τ z :=
  Work.Rigidity.vadd_int_of_vadd_one (fun w => Xi24_vadd_one τ w) k z

/-- On the funnel, `Ξ₂₄` is bounded by a power of `‖τ‖` times `‖q(z)‖` (CKMRV (4.40) for
`K₊^{(24)}`, the `z`-cusp estimate with no `τ`-decay). -/
lemma Xi24_funnel_qz :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ z : ℍ,
      τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → (1 : ℝ) / 3 ≤ z.im →
        ‖Work.Asymptotics.Xi24 τ z‖ ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * ‖Work.Kernels.qParamFun z‖ := by
  obtain ⟨Cσ, hCσ, hσ1, hσ2, hσ3, hσ4⟩ := Work.Asymptotics.ZAtomsThird.cusp_forms
  obtain ⟨cΔ, hcΔ, hΔl⟩ := Work.Asymptotics.delta_lower_third
  obtain ⟨CD, hCD, hΔu⟩ := Work.Asymptotics.delta_upper_third
  obtain ⟨B4, hB4, hE4⟩ := Work.Asymptotics.E4_bounded_third
  obtain ⟨Cq2, hCq2, hE2sq⟩ := Work.Asymptotics.E2sq_sub_one_third
  obtain ⟨Cq4, hCq4, hE4m1⟩ := Work.Asymptotics.E4_sub_one_third
  obtain ⟨Cj, hCj, hjzσ⟩ := Work.Asymptotics.jz_sigma_third
  obtain ⟨C, A, hC, hA, h⟩ := Work.Asymptotics.Xi24_bound_funnel Cσ Cσ Cq2 Cq4 Cj cΔ CD B4
    hCσ hCσ hCq2 hCq4 hCj hcΔ hCD hB4 (fun z hz => hσ1 z hz) (fun z hz => hσ4 z hz)
    hE2sq hE4m1 hjzσ hE4 hΔl hΔu
  exact ⟨C, A, hC, hA, fun τ z hD hτ hz => h τ z ⟨hD, hτ⟩ hz⟩

/-! ## The assembly: the two cusp estimates imply the slashed-kernel bound -/

/-- Auxiliary form of the main theorem: the `Δ(τ)`-cleared cusp estimates for `Ξ₂₄` and `Ncusp`
(CKMRV Lemma 4.11 (4.42) for `d = 24`, in the form needed here) imply the bound for the slashed
kernels. -/
theorem slash_qtau_twentyfour_of (ℓ : Work.Kernels.LogLambdaData)
    (hXi : ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ z : ℍ,
      τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → (1 : ℝ) / 3 ≤ z.im →
      ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Xi24 τ z‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ A *
            Real.exp (-(Real.pi * (4 * τ.im + z.im))))
    (hNc : ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ z : ℍ,
      τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → (1 : ℝ) / 3 ≤ z.im →
      ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Ncusp ℓ 24 τ z‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A *
            Real.exp (-(Real.pi * (4 * τ.im + z.im)))) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ (τ z : ℍ),
      τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → (1 : ℝ) / 3 ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
      (‖(z : ℂ) ^ ((24 : ℤ) / 2 - 2) * Work.Kernels.KPlus 24 τ (ModularGroup.S • z)‖
          ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * ‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))
              / ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖)
      ∧ (‖(z : ℂ) ^ ((24 : ℤ) / 2 - 2) * Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • z)‖
          ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * ‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))
              / ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) := by
  obtain ⟨C1, A1, hC1, hA1, hb1⟩ := hXi
  obtain ⟨C2, A2, hC2, hA2, hb2⟩ := hNc
  obtain ⟨Cq, Aq, hCq, hAq, hbq⟩ := Xi24_funnel_qz
  obtain ⟨cΔ, hcΔ, hΔl⟩ := Work.Asymptotics.delta_lower_third
  have hΔl' : ∀ w : ℍ, (1 : ℝ) / 3 ≤ w.im → cΔ * ‖Work.Kernels.qParamFun w‖ ≤
      ‖Work.Kernels.DeltaFun w‖ := fun w hw => hΔl w hw
  -- constants of the two core estimates
  set CX : ℝ := C1 * 2 ^ A1 / cΔ + Cq + 1 with hCX
  set AX : ℝ := max (2 * A1) Aq + 1 with hAX
  set CN : ℝ := C2 / cΔ + 1 with hCN
  set AN : ℝ := A2 + 1 with hAN
  have hCXpos : 0 < CX := by rw [hCX]; positivity
  have hAXnn : 0 ≤ AX := by rw [hAX]; positivity
  have hCNpos : 0 < CN := by rw [hCN]; positivity
  have hANnn : 0 ≤ AN := by rw [hAN]; linarith
  have hCX2 : C1 * 2 ^ A1 / cΔ ≤ CX := by
    rw [hCX, show C1 * 2 ^ A1 / cΔ + Cq + 1 = C1 * 2 ^ A1 / cΔ + (Cq + 1) by ring]
    exact le_add_of_nonneg_right (by positivity)
  have hCXCq : Cq ≤ CX := by
    rw [hCX, show C1 * 2 ^ A1 / cΔ + Cq + 1 = Cq + (C1 * 2 ^ A1 / cΔ + 1) by ring]
    exact le_add_of_nonneg_right (by positivity)
  have hCNC2 : C2 / cΔ ≤ CN := by
    rw [hCN]; exact le_add_of_nonneg_right (by norm_num)
  have hANA2 : A2 ≤ AN := by rw [hAN]; linarith
  have hAXAq : Aq ≤ AX := by rw [hAX]; have := le_max_right (2 * A1) Aq; linarith
  have hAX2A1 : 2 * A1 ≤ AX := by rw [hAX]; have := le_max_left (2 * A1) Aq; linarith
  -- core estimate for `Ξ₂₄`
  have coreXi : ∀ τ z : ℍ, τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → (1 : ℝ) / 3 ≤ z.im →
      ‖Work.Asymptotics.Xi24 τ z‖ ≤
        CX * (1 + ‖(τ : ℂ)‖) ^ AX * (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))) := by
    intro τ z hD hτ2 hz
    have hτ3 : (1 : ℝ) / 3 ≤ τ.im := by linarith
    have hqτ : ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) :=
      Work.Asymptotics.norm_qParamFun τ
    have hX1 : (0 : ℝ) < 1 + ‖(τ : ℂ)‖ := by positivity
    have hsz1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by have := norm_nonneg (τ : ℂ); linarith
    have hsz0 : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by linarith
    have hP0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im)) := by positivity
    by_cases hcase : 2 * τ.im ≤ z.im
    · have hb := hbq τ z hD hτ2 hz
      have hqz : ‖Work.Kernels.qParamFun z‖ = Real.exp (-(2 * Real.pi * z.im)) :=
        Work.Asymptotics.norm_qParamFun z
      have he : Real.exp (-(2 * Real.pi * z.im)) ≤
          ‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im)) := by
        rw [hqτ, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_pos]
      have h2 : Cq * (1 + ‖(τ : ℂ)‖) ^ Aq ≤ CX * (1 + ‖(τ : ℂ)‖) ^ AX := by
        have hpow : (1 + ‖(τ : ℂ)‖) ^ Aq ≤ (1 + ‖(τ : ℂ)‖) ^ AX :=
          Real.rpow_le_rpow_of_exponent_le hsz1 hAXAq
        calc Cq * (1 + ‖(τ : ℂ)‖) ^ Aq ≤ CX * (1 + ‖(τ : ℂ)‖) ^ Aq :=
              mul_le_mul_of_nonneg_right hCXCq (Real.rpow_nonneg hsz0 Aq)
          _ ≤ CX * (1 + ‖(τ : ℂ)‖) ^ AX := mul_le_mul_of_nonneg_left hpow hCXpos.le
      calc ‖Work.Asymptotics.Xi24 τ z‖
          ≤ Cq * (1 + ‖(τ : ℂ)‖) ^ Aq * ‖Work.Kernels.qParamFun z‖ := hb
        _ = Cq * (1 + ‖(τ : ℂ)‖) ^ Aq * Real.exp (-(2 * Real.pi * z.im)) := by rw [hqz]
        _ ≤ Cq * (1 + ‖(τ : ℂ)‖) ^ Aq *
              (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))) :=
            mul_le_mul_of_nonneg_left he (by positivity)
        _ ≤ CX * (1 + ‖(τ : ℂ)‖) ^ AX *
              (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))) :=
            mul_le_mul_of_nonneg_right h2 hP0
    · push Not at hcase
      have hcase' : z.im ≤ 2 * τ.im := le_of_lt hcase
      set n : ℤ := ⌊z.re⌋ with hn
      set w : ℍ := (-(n : ℝ)) +ᵥ z with hw
      have hwre : w.re = z.re - (n : ℝ) := by rw [hw, UpperHalfPlane.vadd_re]; ring
      have hwim : w.im = z.im := by rw [hw, UpperHalfPlane.vadd_im]
      have hfl : (n : ℝ) ≤ z.re := by rw [hn]; exact Int.floor_le z.re
      have hfr : z.re < (n : ℝ) + 1 := by rw [hn]; exact Int.lt_floor_add_one z.re
      have hre0 : 0 ≤ w.re := by rw [hwre]; linarith
      have hre1 : w.re < 1 := by rw [hwre]; linarith
      have hper : Work.Asymptotics.Xi24 τ w = Work.Asymptotics.Xi24 τ z := by
        rw [hw, show (-(n : ℝ)) = (((-n : ℤ)) : ℝ) by push_cast; ring]
        exact Xi24_vadd_int τ z (-n)
      have hw13 : (1 : ℝ) / 3 ≤ w.im := by rw [hwim]; exact hz
      have hb := hb1 τ w hD hτ2 hw13
      have hwnorm : ‖(w : ℂ)‖ ≤ 1 + z.im := by
        have h1 := Complex.norm_le_abs_re_add_abs_im (w : ℂ)
        rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hwre, hwim] at h1
        have h2 : |z.re - (n : ℝ)| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith
        have h3 : |z.im| = z.im := abs_of_pos z.im_pos
        linarith
      have hτn : τ.im ≤ ‖(τ : ℂ)‖ := by
        have h := Complex.abs_im_le_norm (τ : ℂ)
        rw [UpperHalfPlane.coe_im, abs_of_pos τ.im_pos] at h
        exact h
      have hbig : (1 + ‖(w : ℂ)‖) ^ A1 ≤ 2 ^ A1 * (1 + ‖(τ : ℂ)‖) ^ A1 := by
        have h2 : 1 + ‖(w : ℂ)‖ ≤ 2 * (1 + ‖(τ : ℂ)‖) := by nlinarith
        calc (1 + ‖(w : ℂ)‖) ^ A1 ≤ (2 * (1 + ‖(τ : ℂ)‖)) ^ A1 :=
              Real.rpow_le_rpow (by positivity) h2 hA1
          _ = 2 ^ A1 * (1 + ‖(τ : ℂ)‖) ^ A1 := Real.mul_rpow (by norm_num) (by positivity)
      have hexp : Real.exp (-(Real.pi * (4 * τ.im + w.im))) ≤
          ‖Work.Kernels.qParamFun τ‖ ^ 2 * Real.exp (-(Real.pi * z.im)) := by
        have hE : Real.exp (-(Real.pi * (4 * τ.im + w.im))) =
            Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(2 * Real.pi * τ.im)) *
              Real.exp (-(Real.pi * z.im)) := by
          rw [hwim, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [hE, hqτ, sq]
      have hpowa : (1 + ‖(τ : ℂ)‖) ^ A1 * (1 + ‖(τ : ℂ)‖) ^ A1
          = (1 + ‖(τ : ℂ)‖) ^ (2 * A1) := by
        rw [← Real.rpow_add hX1]
        congr 1
        ring
      have hprod : C1 * (1 + ‖(τ : ℂ)‖) ^ A1 * (1 + ‖(w : ℂ)‖) ^ A1 *
            Real.exp (-(Real.pi * (4 * τ.im + w.im)))
          ≤ C1 * 2 ^ A1 * (1 + ‖(τ : ℂ)‖) ^ (2 * A1) *
              (‖Work.Kernels.qParamFun τ‖ ^ 2 * Real.exp (-(Real.pi * z.im))) := by
        have hE0 : (0 : ℝ) ≤ Real.exp (-(Real.pi * (4 * τ.im + w.im))) := (Real.exp_pos _).le
        have h2n : (0 : ℝ) ≤ 2 ^ A1 * (1 + ‖(τ : ℂ)‖) ^ A1 := by positivity
        have hstep : (1 + ‖(w : ℂ)‖) ^ A1 * Real.exp (-(Real.pi * (4 * τ.im + w.im)))
            ≤ (2 ^ A1 * (1 + ‖(τ : ℂ)‖) ^ A1) *
                (‖Work.Kernels.qParamFun τ‖ ^ 2 * Real.exp (-(Real.pi * z.im))) :=
          mul_le_mul hbig hexp hE0 h2n
        have hC10 : (0 : ℝ) ≤ C1 * (1 + ‖(τ : ℂ)‖) ^ A1 := by positivity
        have hp := mul_le_mul_of_nonneg_left hstep hC10
        calc C1 * (1 + ‖(τ : ℂ)‖) ^ A1 * (1 + ‖(w : ℂ)‖) ^ A1 *
              Real.exp (-(Real.pi * (4 * τ.im + w.im)))
            = (C1 * (1 + ‖(τ : ℂ)‖) ^ A1) *
                ((1 + ‖(w : ℂ)‖) ^ A1 * Real.exp (-(Real.pi * (4 * τ.im + w.im)))) := by ring
          _ ≤ (C1 * (1 + ‖(τ : ℂ)‖) ^ A1) *
                ((2 ^ A1 * (1 + ‖(τ : ℂ)‖) ^ A1) *
                  (‖Work.Kernels.qParamFun τ‖ ^ 2 * Real.exp (-(Real.pi * z.im)))) := hp
          _ = C1 * 2 ^ A1 * ((1 + ‖(τ : ℂ)‖) ^ A1 * (1 + ‖(τ : ℂ)‖) ^ A1) *
                (‖Work.Kernels.qParamFun τ‖ ^ 2 * Real.exp (-(Real.pi * z.im))) := by ring
          _ = C1 * 2 ^ A1 * (1 + ‖(τ : ℂ)‖) ^ (2 * A1) *
                (‖Work.Kernels.qParamFun τ‖ ^ 2 * Real.exp (-(Real.pi * z.im))) := by
              rw [hpowa]
      have hΔΞ : ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Xi24 τ w‖
          ≤ C1 * 2 ^ A1 * (1 + ‖(τ : ℂ)‖) ^ (2 * A1) *
              (‖Work.Kernels.qParamFun τ‖ ^ 2 * Real.exp (-(Real.pi * z.im))) :=
        le_trans hb hprod
      have hqpos : 0 < ‖Work.Kernels.qParamFun τ‖ := by rw [hqτ]; exact Real.exp_pos _
      have hΔlτ : cΔ * ‖Work.Kernels.qParamFun τ‖ ≤ ‖Work.Kernels.DeltaFun τ‖ := hΔl' τ hτ3
      have hden0 : 0 < cΔ * ‖Work.Kernels.qParamFun τ‖ := mul_pos hcΔ hqpos
      have hres : ‖Work.Asymptotics.Xi24 τ z‖ ≤
          (C1 * 2 ^ A1 / cΔ) * (1 + ‖(τ : ℂ)‖) ^ (2 * A1) *
            (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))) := by
        have hΔΞ' : ‖Work.Asymptotics.Xi24 τ z‖ * ‖Work.Kernels.DeltaFun τ‖
            ≤ C1 * 2 ^ A1 * (1 + ‖(τ : ℂ)‖) ^ (2 * A1) *
                (‖Work.Kernels.qParamFun τ‖ ^ 2 * Real.exp (-(Real.pi * z.im))) := by
          have h := hΔΞ
          rw [mul_comm (Work.Kernels.DeltaFun τ)] at h
          rw [← norm_mul, ← hper]
          exact h
        have hb2' : ‖Work.Asymptotics.Xi24 τ z‖
            ≤ (C1 * 2 ^ A1 * (1 + ‖(τ : ℂ)‖) ^ (2 * A1) *
                (‖Work.Kernels.qParamFun τ‖ ^ 2 * Real.exp (-(Real.pi * z.im)))) /
                (cΔ * ‖Work.Kernels.qParamFun τ‖) := by
          rw [le_div_iff₀ hden0]
          have hre : ‖Work.Asymptotics.Xi24 τ z‖ * (cΔ * ‖Work.Kernels.qParamFun τ‖)
              ≤ ‖Work.Asymptotics.Xi24 τ z‖ * ‖Work.Kernels.DeltaFun τ‖ :=
            mul_le_mul_of_nonneg_left hΔlτ (norm_nonneg _)
          exact le_trans hre hΔΞ'
        refine le_trans hb2' ?_
        have hsplit : (C1 * 2 ^ A1 * (1 + ‖(τ : ℂ)‖) ^ (2 * A1) *
              (‖Work.Kernels.qParamFun τ‖ ^ 2 * Real.exp (-(Real.pi * z.im)))) /
              (cΔ * ‖Work.Kernels.qParamFun τ‖)
            = (C1 * 2 ^ A1 / cΔ) * (1 + ‖(τ : ℂ)‖) ^ (2 * A1) *
              (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))) := by
          field_simp <;> ring
        rw [hsplit]
      refine le_trans hres ?_
      have hpow : (1 + ‖(τ : ℂ)‖) ^ (2 * A1) ≤ (1 + ‖(τ : ℂ)‖) ^ AX :=
        Real.rpow_le_rpow_of_exponent_le hsz1 hAX2A1
      have hstep1 : (C1 * 2 ^ A1 / cΔ) * (1 + ‖(τ : ℂ)‖) ^ (2 * A1) *
            (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im)))
          ≤ CX * (1 + ‖(τ : ℂ)‖) ^ (2 * A1) *
            (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCX2 (Real.rpow_nonneg hsz0 (2 * A1))) hP0
      exact le_trans hstep1 (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hCXpos.le) hP0)
  -- core estimate for `Ncusp`
  have coreNc : ∀ τ z : ℍ, τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → (1 : ℝ) / 3 ≤ z.im →
      ‖Work.Asymptotics.Ncusp ℓ 24 τ z‖ ≤
        CN * (1 + ‖(τ : ℂ)‖) ^ AN * (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))) := by
    intro τ z hD hτ2 hz
    have hτ3 : (1 : ℝ) / 3 ≤ τ.im := by linarith
    have hb := hb2 τ z hD hτ2 hz
    have hqτ : ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) :=
      Work.Asymptotics.norm_qParamFun τ
    have hqpos : 0 < ‖Work.Kernels.qParamFun τ‖ := by rw [hqτ]; exact Real.exp_pos _
    have hsz1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by have := norm_nonneg (τ : ℂ); linarith
    have hsz0 : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by linarith
    have hΔlτ : cΔ * ‖Work.Kernels.qParamFun τ‖ ≤ ‖Work.Kernels.DeltaFun τ‖ := hΔl' τ hτ3
    have hden0 : 0 < cΔ * ‖Work.Kernels.qParamFun τ‖ := mul_pos hcΔ hqpos
    have hexp : Real.exp (-(Real.pi * (4 * τ.im + z.im))) =
        ‖Work.Kernels.qParamFun τ‖ ^ 2 * Real.exp (-(Real.pi * z.im)) := by
      have harg : -(Real.pi * (4 * τ.im + z.im))
          = -(2 * Real.pi * τ.im) + -(2 * Real.pi * τ.im) + -(Real.pi * z.im) := by ring
      rw [hqτ, sq, harg, Real.exp_add, Real.exp_add]
    have hP0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im)) := by positivity
    have h1 : ‖Work.Asymptotics.Ncusp ℓ 24 τ z‖
        = ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Ncusp ℓ 24 τ z‖ /
            ‖Work.Kernels.DeltaFun τ‖ := by
      rw [norm_mul]
      exact (mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr
        (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ))).symm
    have h2 : (C2 * (1 + ‖(τ : ℂ)‖) ^ A2 *
            (‖Work.Kernels.qParamFun τ‖ ^ 2 * Real.exp (-(Real.pi * z.im)))) /
            (cΔ * ‖Work.Kernels.qParamFun τ‖)
        = (C2 / cΔ) * (1 + ‖(τ : ℂ)‖) ^ A2 *
            (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))) := by
      field_simp <;> ring
    rw [h1]
    calc ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Ncusp ℓ 24 τ z‖ / ‖Work.Kernels.DeltaFun τ‖
        ≤ (C2 * (1 + ‖(τ : ℂ)‖) ^ A2 * Real.exp (-(Real.pi * (4 * τ.im + z.im)))) /
            ‖Work.Kernels.DeltaFun τ‖ := div_le_div_of_nonneg_right hb (norm_nonneg _)
      _ = (C2 * (1 + ‖(τ : ℂ)‖) ^ A2 *
            (‖Work.Kernels.qParamFun τ‖ ^ 2 * Real.exp (-(Real.pi * z.im)))) /
            ‖Work.Kernels.DeltaFun τ‖ := by rw [hexp]
      _ ≤ (C2 * (1 + ‖(τ : ℂ)‖) ^ A2 *
            (‖Work.Kernels.qParamFun τ‖ ^ 2 * Real.exp (-(Real.pi * z.im)))) /
            (cΔ * ‖Work.Kernels.qParamFun τ‖) :=
          div_le_div_of_nonneg_left (by positivity) hden0 hΔlτ
      _ = (C2 / cΔ) * (1 + ‖(τ : ℂ)‖) ^ A2 *
            (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))) := h2
      _ ≤ CN * (1 + ‖(τ : ℂ)‖) ^ AN *
            (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))) := by
          have hpow : (1 + ‖(τ : ℂ)‖) ^ A2 ≤ (1 + ‖(τ : ℂ)‖) ^ AN :=
            Real.rpow_le_rpow_of_exponent_le hsz1 hANA2
          have h1' : (C2 / cΔ) * (1 + ‖(τ : ℂ)‖) ^ A2 ≤ CN * (1 + ‖(τ : ℂ)‖) ^ AN :=
            calc (C2 / cΔ) * (1 + ‖(τ : ℂ)‖) ^ A2 ≤ CN * (1 + ‖(τ : ℂ)‖) ^ A2 :=
                  mul_le_mul_of_nonneg_right hCNC2 (Real.rpow_nonneg hsz0 A2)
              _ ≤ CN * (1 + ‖(τ : ℂ)‖) ^ AN := mul_le_mul_of_nonneg_left hpow hCNpos.le
          exact mul_le_mul_of_nonneg_right h1' hP0
  -- the final constants
  set cK : ℂ := (36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I with hcK
  set C : ℝ := max (CX / ‖cK‖) CN + 1 with hCdef
  set A : ℝ := max AX AN + 1 with hAdef
  have hcKne : cK ≠ 0 := by
    rw [hcK]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) Complex.I_ne_zero
    · simp [Work.Kernels.c1728]
    · exact zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
  have hCpos : 0 < C := by
    rw [hCdef]
    have h1 : (0 : ℝ) ≤ CX / ‖cK‖ := div_nonneg hCXpos.le (norm_nonneg _)
    have h2 : (0 : ℝ) ≤ max (CX / ‖cK‖) CN := le_max_of_le_left h1
    linarith
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    have h1 : (0 : ℝ) ≤ max AX AN := le_max_of_le_left hAXnn
    linarith
  have hCXle : CX / ‖cK‖ ≤ C := by
    rw [hCdef]
    have h1 : CX / ‖cK‖ ≤ max (CX / ‖cK‖) CN := le_max_left _ _
    linarith
  have hCNle : CN ≤ C := by
    rw [hCdef]
    have h1 : CN ≤ max (CX / ‖cK‖) CN := le_max_right _ _
    linarith
  have hAXA : AX ≤ A := by rw [hAdef]; have := le_max_left AX AN; linarith
  have hANA : AN ≤ A := by rw [hAdef]; have := le_max_right AX AN; linarith
  refine ⟨C, A, hCpos, hAnn, ?_⟩
  intro τ z hD hτ2 hz hne
  have hJ : Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z ≠ 0 := sub_ne_zero.mpr hne
  have hDz : Work.Kernels.DeltaFun z *
      (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ≠ 0 :=
    mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) hJ
  have hQ0 : (0 : ℝ) ≤ ‖Work.Kernels.DeltaFun z *
      (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := norm_nonneg _
  have hsz1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by have := norm_nonneg (τ : ℂ); linarith
  have hzpow : (z : ℂ) ^ ((24 : ℤ) / 2 - 2) = (z : ℂ) ^ 10 := by
    rw [show ((24 : ℤ) / 2 - 2) = (10 : ℤ) by norm_num, zpow_ofNat]
  constructor
  · -- the `K₊` half
    have hXi := coreXi τ z hD hτ2 hz
    have hkey := Work.Asymptotics.Xi24_eq τ z hne
    have hdiv : (z : ℂ) ^ 10 * Work.Kernels.KPlus 24 τ (ModularGroup.S • z)
        = Work.Asymptotics.Xi24 τ z /
            (cK * (Work.Kernels.DeltaFun z *
              (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))) := by
      rw [eq_div_iff (mul_ne_zero hcKne hDz), mul_comm]
      exact hkey
    have hQpos : 0 < ‖Work.Kernels.DeltaFun z *
        (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
      norm_pos_iff.mpr hDz
    rw [hzpow, hdiv, norm_div, norm_mul]
    have h1 : ‖Work.Asymptotics.Xi24 τ z‖ / (‖cK‖ *
          ‖Work.Kernels.DeltaFun z *
            (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖)
        ≤ (CX * (1 + ‖(τ : ℂ)‖) ^ AX *
            (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im)))) /
          (‖cK‖ * ‖Work.Kernels.DeltaFun z *
            (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) :=
      div_le_div_of_nonneg_right hXi (le_of_lt (mul_pos (norm_pos_iff.mpr hcKne) hQpos))
    refine le_trans h1 ?_
    have hfac : (CX * (1 + ‖(τ : ℂ)‖) ^ AX *
            (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im)))) /
          (‖cK‖ * ‖Work.Kernels.DeltaFun z *
            (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖)
        = (CX / ‖cK‖) * ((1 + ‖(τ : ℂ)‖) ^ AX *
            (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))) /
            ‖Work.Kernels.DeltaFun z *
              (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) := by
      field_simp <;> ring
    rw [hfac]
    have h5 : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ AX *
        (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))) /
          ‖Work.Kernels.DeltaFun z *
            (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by positivity
    refine le_trans (mul_le_mul_of_nonneg_right hCXle h5) ?_
    have h6 : (1 + ‖(τ : ℂ)‖) ^ AX *
          (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))) /
          ‖Work.Kernels.DeltaFun z *
            (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
        ≤ (1 + ‖(τ : ℂ)‖) ^ A *
          (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))) /
          ‖Work.Kernels.DeltaFun z *
            (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
      refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hsz1 hAXA) (by positivity)
    exact le_trans (mul_le_mul_of_nonneg_left h6 hCpos.le) (le_of_eq (by ring))
  · -- the `K₋` half
    have hNc := coreNc τ z hD hτ2 hz
    have hkey := Work.Asymptotics.Ncusp_ident ℓ 24 (Or.inr rfl) τ z hne
    have he : (-(2 - ((24 : ℕ) : ℤ) / 2)) = (10 : ℤ) := by norm_num
    have hdiv : (z : ℂ) ^ 10 * Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • z)
        = Work.Asymptotics.Ncusp ℓ 24 τ z /
            (Work.Kernels.DeltaFun z *
              (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) := by
      have h1 : (z : ℂ) ^ (-(2 - ((24 : ℕ) : ℤ) / 2)) *
            Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • z)
          = Work.Asymptotics.Ncusp ℓ 24 τ z /
              (Work.Kernels.DeltaFun z *
                (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) := by
        rw [hkey, mul_div_cancel_left₀ _ hDz]
      rw [he] at h1
      exact h1
    rw [hzpow, hdiv, norm_div]
    have h1 : ‖Work.Asymptotics.Ncusp ℓ 24 τ z‖ /
          ‖Work.Kernels.DeltaFun z *
            (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
        ≤ (CN * (1 + ‖(τ : ℂ)‖) ^ AN *
            (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im)))) /
          ‖Work.Kernels.DeltaFun z *
            (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
      div_le_div_of_nonneg_right hNc hQ0
    refine le_trans h1 ?_
    have hfac : (CN * (1 + ‖(τ : ℂ)‖) ^ AN *
            (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im)))) /
          ‖Work.Kernels.DeltaFun z *
            (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
        = CN * ((1 + ‖(τ : ℂ)‖) ^ AN *
            (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))) /
            ‖Work.Kernels.DeltaFun z *
              (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) := by
      ring
    rw [hfac]
    have h5 : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ AN *
        (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))) /
          ‖Work.Kernels.DeltaFun z *
            (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by positivity
    refine le_trans (mul_le_mul_of_nonneg_right hCNle h5) ?_
    have h6 : (1 + ‖(τ : ℂ)‖) ^ AN *
          (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))) /
          ‖Work.Kernels.DeltaFun z *
            (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
        ≤ (1 + ‖(τ : ℂ)‖) ^ A *
          (‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))) /
          ‖Work.Kernels.DeltaFun z *
            (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
      refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hsz1 hANA) (by positivity)
    exact le_trans (mul_le_mul_of_nonneg_left h6 hCpos.le) (le_of_eq (by ring))

theorem slash_qtau_twentyfour (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ (τ z : UpperHalfPlane),
      τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → (1 : ℝ) / 3 ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
      (‖(z : ℂ) ^ ((24 : ℤ) / 2 - 2) * Work.Kernels.KPlus 24 τ (ModularGroup.S • z)‖
          ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * ‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))
              / ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖)
      ∧ (‖(z : ℂ) ^ ((24 : ℤ) / 2 - 2) * Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • z)‖
          ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * ‖Work.Kernels.qParamFun τ‖ * Real.exp (-(Real.pi * z.im))
              / ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) := by
  refine slash_qtau_twentyfour_of ℓ ?_ (Ncusp24_delta_funnel_zfree ℓ)
  obtain ⟨C, A, hC, hA, h⟩ := Work.CKFinal.Xi24_Delta_bound
  exact ⟨C, A, hC, hA, fun τ z _ hτ2 hz => h τ z (by linarith) hz⟩

end

end Work.CKFinal.LineDecay
