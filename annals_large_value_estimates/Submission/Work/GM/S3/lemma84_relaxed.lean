import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.Statements
import Submission.Work.GM.S3.Rl4Aux
import Submission.Work.GM.S3.fourier_decay_explicit
import Submission.Work.GM.S3.RtildeSq_one_lower
import Submission.Work.GM.S3.bddAbove_range_RtildeSq
import Submission.Work.GM.S3.gSq_continuous
import Submission.Work.GM.S3.integral_gSq_le
import Submission.Work.GM.S3.lemma84_clashfree
import Submission.Work.GM.S3.RtildeSq_one_lower_geT
import Submission.Work.GM.S3.Rsq_shifted_fourier_decay
import Submission.Work.GM.S3.RtildeSq_fourier_trivial

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators FourierTransform
open Submission.GM (Rfun energy Separated)


section ShiftIdentity

/-- If a bump at one is nonzero then its argument lies in `[1/C, C]`. -/
private theorem bumpAtOne_zero_of_notMem {ψ : ℝ → ℝ} {C : ℝ} (h : IsBumpAtOne ψ C) {x : ℝ}
    (hx : x ∉ Set.Icc (1 / C) C) : ψ x = 0 :=
  by_contra fun hne => hx (h.2.2.1 x hne)

/-- If a bump at zero is nonzero then its argument lies in `[-C, C]`. -/
private theorem bumpAtZero_zero_of_notMem {ψ : ℝ → ℝ} {C : ℝ} (h : IsBumpAtZero ψ C) {x : ℝ}
    (hx : x ∉ Set.Icc (-C) C) : ψ x = 0 := by
  refine by_contra fun hne => hx ?_
  have hx' := h.2.2.1 x hne
  rw [abs_le] at hx'
  exact ⟨hx'.1, hx'.2⟩

/-- The Fourier character `𝓮(-ξu)` as a complex number. -/
private noncomputable def chr (ξ : ℝ) (u : ℝ) : ℂ := (Real.fourierChar (-(ξ * u)) : ℂ)

private theorem chr_add (ξ z w : ℝ) : chr ξ (z + w) = chr ξ z * chr ξ w := by
  unfold chr
  rw [show -(ξ * (z + w)) = -(ξ * z) + -(ξ * w) by ring, AddChar.map_add_eq_mul, Circle.coe_mul]

/-- `∫ x, f (a - x) = ∫ x, f x` (translation and reflection invariance of Lebesgue measure). -/
private theorem integral_comp_sub_left_eq_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (a : ℝ) : ∫ x, f (a - x) = ∫ x, f x := by
  have h1 : (fun x : ℝ => f (a - x)) = (fun x : ℝ => (fun y : ℝ => f (-y)) (x - a)) := by
    funext x; rw [show a - x = -(x - a) by ring]
  rw [h1, MeasureTheory.integral_sub_right_eq_self (fun y : ℝ => f (-y)) a,
    MeasureTheory.integral_neg_eq_self f volume]

private theorem normSq_Rfun_sub_continuous (ψ₂ : ℝ → ℝ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀)
    (h₂ : IsBumpAtOne ψ₂ C₀) (W : Finset ℝ) :
    Continuous (fun p : ℝ × ℝ => ψ₂ (p.1 - p.2) * ‖Submission.GM.Rfun W (p.1 - p.2)‖ ^ 2) :=
  (gSq_continuous ψ₂ C₀ hC₀ h₂ W).comp (by fun_prop)

/-- **Fubini + shift identity for `𝓕 (ψ₁ · RtildeSq)`.**  With `B_s = N·B`, `k(w) = B_s ψ₃(B_s w)`
and `g(v) = ψ₂(v)‖R(v)‖²` (so that `RtildeSq u = ∫ w, k w · g (u - w)`), the double integral
defining `𝓕 (ψ₁ · RtildeSq) ξ` factorises as `∫ w, 𝐞(-ξw)·k(w)·𝓕(ψ₁(· + w)·g) ξ`. -/
private theorem fourier_shift_identity
    (ψ₁ ψ₂ ψ₃ : ℝ → ℝ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀)
    (h₁ : IsBumpAtOne ψ₁ C₀) (h₂ : IsBumpAtOne ψ₂ C₀) (h₃ : IsBumpAtZero ψ₃ C₀)
    (W : Finset ℝ) (N : ℕ) (B ξ : ℝ) (hB : 0 < B) :
    FourierTransform.fourier (fun u => ((ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ)) ξ
      = ∫ w, chr ξ w * ((((N : ℝ) * B) * ψ₃ (((N : ℝ) * B) * w) : ℝ) : ℂ) *
          FourierTransform.fourier
            (fun u' => ((ψ₁ (u' + w) * ψ₂ u' * ‖Submission.GM.Rfun W u'‖ ^ 2 : ℝ) : ℂ)) ξ := by
  set Bs : ℝ := (N : ℝ) * B with hBsdef
  set G : ℝ → ℝ → ℂ := fun u w => chr ξ u * ((ψ₁ u : ℝ) : ℂ) * (((Bs * ψ₃ (Bs * w) : ℝ)) : ℂ) *
      ((ψ₂ (u - w) * ‖Submission.GM.Rfun W (u - w)‖ ^ 2 : ℝ) : ℂ) with hG
  -- `RtildeSq` is a convolution
  have hRt : ∀ u : ℝ, RtildeSq W N B ψ₃ ψ₂ u
      = ∫ u', Bs * ψ₃ (Bs * (u - u')) * (ψ₂ u' * ‖Submission.GM.Rfun W u'‖ ^ 2) := by
    intro u
    rw [RtildeSq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u' => ?_)
    simp only [hBsdef]
    ring
  -- complex form of the convolution identity
  have hRtC : ∀ u : ℝ, ((RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ)
      = ∫ u', ((Bs * ψ₃ (Bs * (u - u')) * (ψ₂ u' * ‖Submission.GM.Rfun W u'‖ ^ 2) : ℝ) : ℂ) := by
    intro u
    rw [hRt u]
    exact (integral_ofReal (μ := volume) (𝕜 := ℂ)
      (f := fun u' : ℝ => Bs * ψ₃ (Bs * (u - u')) *
        (ψ₂ u' * ‖Submission.GM.Rfun W u'‖ ^ 2))).symm
  -- the double integrand is continuous with compact support
  have hGcont : Continuous (Function.uncurry G) := by
    rw [hG]
    have hch : Continuous fun p : ℝ × ℝ => chr ξ p.1 :=
      (continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp ((continuous_const.mul continuous_id).neg))).comp
          continuous_fst
    have ha : Continuous fun p : ℝ × ℝ => ((ψ₁ p.1 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (h₁.1.continuous.comp continuous_fst)
    have hb : Continuous fun p : ℝ × ℝ => (((Bs * ψ₃ (Bs * p.2) : ℝ)) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((continuous_const.mul (h₃.1.continuous.comp (by fun_prop))).comp continuous_snd)
    have hd : Continuous fun p : ℝ × ℝ =>
        ((ψ₂ (p.1 - p.2) * ‖Submission.GM.Rfun W (p.1 - p.2)‖ ^ 2 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (normSq_Rfun_sub_continuous ψ₂ C₀ hC₀ h₂ W)
    exact ((hch.mul ha).mul hb).mul hd
  have hGcs : HasCompactSupport (Function.uncurry G) := by
    refine HasCompactSupport.intro
      (K := Set.Icc (1 / C₀ : ℝ) C₀ ×ˢ Set.Icc (1 / C₀ - C₀ : ℝ) (C₀ - 1 / C₀))
      (isCompact_Icc.prod isCompact_Icc) ?_
    rintro ⟨u, w⟩ hp
    rw [hG]
    simp only [Function.uncurry]
    by_cases hu : u ∈ Set.Icc (1 / C₀ : ℝ) C₀
    · have hw : w ∉ Set.Icc (1 / C₀ - C₀ : ℝ) (C₀ - 1 / C₀) := by
        intro hw
        exact hp (by simp only [Set.mem_prod]; exact ⟨hu, hw⟩)
      have hsub : u - w ∉ Set.Icc (1 / C₀ : ℝ) C₀ := by
        intro hs
        rw [Set.mem_Icc] at hs hw
        apply hw
        constructor <;> linarith [hu.1, hu.2, hs.1, hs.2]
      rw [bumpAtOne_zero_of_notMem h₂ hsub]
      simp
    · rw [bumpAtOne_zero_of_notMem h₁ hu]
      simp
  have hGint : Integrable (Function.uncurry G) (volume.prod volume) :=
    hGcont.integrable_of_hasCompactSupport hGcs
  -- Step A : the Fourier transform is the double integral of `G`
  have hstepA : FourierTransform.fourier (fun u => ((ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ)) ξ
      = ∫ u, ∫ w, G u w := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [show inner ℝ u ξ = ξ * u from by simp]
    rw [Circle.smul_def, smul_eq_mul]
    rw [show ((ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ)
          = (ψ₁ u : ℂ) * ((RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ) by push_cast; ring]
    rw [hRtC u]
    -- substitute `u' = u - w` in the inner integral
    have hsub : (∫ u', ((Bs * ψ₃ (Bs * (u - u')) *
            (ψ₂ u' * ‖Submission.GM.Rfun W u'‖ ^ 2) : ℝ) : ℂ))
        = ∫ w, ((Bs * ψ₃ (Bs * w) *
            (ψ₂ (u - w) * ‖Submission.GM.Rfun W (u - w)‖ ^ 2) : ℝ) : ℂ) := by
      rw [← integral_comp_sub_left_eq_self
        (fun x : ℝ => ((Bs * ψ₃ (Bs * x) *
          (ψ₂ (u - x) * ‖Submission.GM.Rfun W (u - x)‖ ^ 2) : ℝ) : ℂ)) u]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only []
      rw [show u - (u - x) = x by ring]
    rw [hsub]
    -- pull the constants inside and identify with `∫ w, G u w`
    have hinner : (∫ w, ((Bs * ψ₃ (Bs * w) *
          (ψ₂ (u - w) * ‖Submission.GM.Rfun W (u - w)‖ ^ 2) : ℝ) : ℂ))
        = ∫ w, (((Bs * ψ₃ (Bs * w) : ℝ)) : ℂ) *
            ((ψ₂ (u - w) * ‖Submission.GM.Rfun W (u - w)‖ ^ 2 : ℝ) : ℂ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      push_cast
      ring
    rw [hinner, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [hG, chr]
    ring
  -- Step B : Fubini
  have hstepB : (∫ u, ∫ w, G u w) = ∫ w, ∫ u, G u w :=
    integral_integral_swap hGint
  -- Step C : factor out the kernel and identify the Fourier transform
  have hstepC : ∀ w : ℝ, (∫ u, G u w)
      = chr ξ w * (((Bs * ψ₃ (Bs * w) : ℝ)) : ℂ) *
          FourierTransform.fourier
            (fun v => ((ψ₁ (v + w) * ψ₂ v * ‖Submission.GM.Rfun W v‖ ^ 2 : ℝ) : ℂ)) ξ := by
    intro w
    -- pull the constant kernel factor out
    have h1 : (∫ u, G u w)
        = (((Bs * ψ₃ (Bs * w) : ℝ)) : ℂ) *
            ∫ u, chr ξ u * ((ψ₁ u : ℝ) : ℂ) *
              ((ψ₂ (u - w) * ‖Submission.GM.Rfun W (u - w)‖ ^ 2 : ℝ) : ℂ) := by
      rw [← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only [hG]
      ring
    -- shift `u = v + w` and split the character
    have h2 : (∫ u, chr ξ u * ((ψ₁ u : ℝ) : ℂ) *
              ((ψ₂ (u - w) * ‖Submission.GM.Rfun W (u - w)‖ ^ 2 : ℝ) : ℂ))
        = ∫ v, chr ξ v * chr ξ w * ((ψ₁ (v + w) : ℝ) : ℂ) *
              ((ψ₂ v * ‖Submission.GM.Rfun W v‖ ^ 2 : ℝ) : ℂ) := by
      rw [← MeasureTheory.integral_add_right_eq_self
        (fun u : ℝ => chr ξ u * ((ψ₁ u : ℝ) : ℂ) *
          ((ψ₂ (u - w) * ‖Submission.GM.Rfun W (u - w)‖ ^ 2 : ℝ) : ℂ)) w]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      simp only []
      rw [show v + w - w = v by ring, chr_add]
    -- pull out `chr ξ w`
    have h3 : (∫ v, chr ξ v * chr ξ w * ((ψ₁ (v + w) : ℝ) : ℂ) *
              ((ψ₂ v * ‖Submission.GM.Rfun W v‖ ^ 2 : ℝ) : ℂ))
        = chr ξ w * ∫ v, chr ξ v *
              ((ψ₁ (v + w) * ψ₂ v * ‖Submission.GM.Rfun W v‖ ^ 2 : ℝ) : ℂ) := by
      rw [← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      push_cast
      ring
    -- identify the Fourier transform
    have h4 : (∫ v, chr ξ v * ((ψ₁ (v + w) * ψ₂ v * ‖Submission.GM.Rfun W v‖ ^ 2 : ℝ) : ℂ))
        = FourierTransform.fourier
            (fun v => ((ψ₁ (v + w) * ψ₂ v * ‖Submission.GM.Rfun W v‖ ^ 2 : ℝ) : ℂ)) ξ := by
      rw [Real.fourier_eq]
      refine (integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)).symm
      simp only [chr, show inner ℝ v ξ = ξ * v from by simp]
      rw [Circle.smul_def, smul_eq_mul]
    rw [h1, h2, h3, h4]
    ring
  rw [hstepA, hstepB]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only []
  exact hstepC w

end ShiftIdentity

/-- Elementary arithmetic: `a * s ≤ a * b * c * s` for `a, s ≥ 0` and `b, c ≥ 1`. -/
private lemma mul_le_mul_of_one_le_one_le {a b c s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hb : 1 ≤ b) (hc : 1 ≤ c) : a * s ≤ a * b * c * s := by
  have hbc : 1 ≤ b * c := by nlinarith [hb, hc]
  have h1 : a * 1 ≤ a * (b * c) := by nlinarith [ha, hbc]
  have h2 : a * 1 * s ≤ a * (b * c) * s := by nlinarith [h1, hs]
  calc a * s = a * 1 * s := by ring
    _ ≤ a * (b * c) * s := h2
    _ = a * b * c * s := by ring

/-- The arithmetic of the "far" branch: with `Dj, Wc, Cc ≥ 0`, `cR > 0`, `T ≥ 1`, `|ξ| > 0`,
`Tη ≥ 1` and `cR * Wc ≤ sF`,
`Dj · Wc · (1+T)^j / |ξ|^j · Cc ≤ (Cc·Dj·2^j/cR) · Tη · (T/|ξ|)^j · sF`. -/
private lemma arith_far {Dj Wc T ξ Tη sF Cc cR : ℝ} {j : ℕ}
    (hDj : 0 ≤ Dj) (hWc : 0 ≤ Wc) (hCc : 0 ≤ Cc) (hcR : 0 < cR) (hT : 1 ≤ T)
    (hξ : 0 < |ξ|) (hTη : 1 ≤ Tη) (hsup : cR * Wc ≤ sF) :
    Dj * Wc * (1 + T) ^ j / |ξ| ^ j * Cc
      ≤ (Cc * Dj * 2 ^ j / cR) * Tη * (T / |ξ|) ^ j * sF := by
  have hξj : (0 : ℝ) < |ξ| ^ j := pow_pos hξ j
  have hsFnn : 0 ≤ sF := le_trans (mul_nonneg hcR.le hWc) hsup
  have hpt : (1 + T) ^ j ≤ 2 ^ j * T ^ j := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) j
  have hstep1 : Dj * Wc * (1 + T) ^ j / |ξ| ^ j * Cc
      ≤ (Cc * Dj * 2 ^ j) * (T ^ j / |ξ| ^ j) * Wc := by
    have hA : Dj * Wc * (1 + T) ^ j / |ξ| ^ j * Cc
        ≤ Dj * Wc * (2 ^ j * T ^ j) / |ξ| ^ j * Cc := by
      refine mul_le_mul_of_nonneg_right ?_ hCc
      refine div_le_div_of_nonneg_right ?_ hξj.le
      exact mul_le_mul_of_nonneg_left hpt (mul_nonneg hDj hWc)
    refine hA.trans (le_of_eq ?_)
    field_simp
  have hstep2 : (Cc * Dj * 2 ^ j) * (T ^ j / |ξ| ^ j) * Wc
      ≤ (Cc * Dj * 2 ^ j) * (T ^ j / |ξ| ^ j) * (sF / cR) := by
    have hsup' : Wc * cR ≤ sF := by linarith [hsup]
    refine mul_le_mul_of_nonneg_left ((le_div_iff₀ hcR).mpr hsup') ?_
    positivity
  have hstep3 : (Cc * Dj * 2 ^ j) * (T ^ j / |ξ| ^ j) * (sF / cR)
      ≤ (Cc * Dj * 2 ^ j / cR) * Tη * (T ^ j / |ξ| ^ j) * sF := by
    have hcoef : 0 ≤ (Cc * Dj * 2 ^ j / cR) * (T ^ j / |ξ| ^ j) * sF := by positivity
    calc (Cc * Dj * 2 ^ j) * (T ^ j / |ξ| ^ j) * (sF / cR)
        = (Cc * Dj * 2 ^ j / cR) * (T ^ j / |ξ| ^ j) * sF := by ring
      _ = ((Cc * Dj * 2 ^ j / cR) * (T ^ j / |ξ| ^ j) * sF) * 1 := by ring
      _ ≤ ((Cc * Dj * 2 ^ j / cR) * (T ^ j / |ξ| ^ j) * sF) * Tη :=
          mul_le_mul_of_nonneg_left hTη hcoef
      _ = (Cc * Dj * 2 ^ j / cR) * Tη * (T ^ j / |ξ| ^ j) * sF := by ring
  calc Dj * Wc * (1 + T) ^ j / |ξ| ^ j * Cc
      ≤ (Cc * Dj * 2 ^ j) * (T ^ j / |ξ| ^ j) * Wc := hstep1
    _ ≤ (Cc * Dj * 2 ^ j) * (T ^ j / |ξ| ^ j) * (sF / cR) := hstep2
    _ ≤ (Cc * Dj * 2 ^ j / cR) * Tη * (T ^ j / |ξ| ^ j) * sF := hstep3
    _ = (Cc * Dj * 2 ^ j / cR) * Tη * (T / |ξ|) ^ j * sF := by rw [div_pow]

/-- **GM 8.4 with the cap on the smoothing frequency removed** (the paper's `B ⪅ T`).

Identical to `Work.GM.S3.Lemma84Statement` except that the hypothesis `(N : ℝ) * B ≤ M N` is
deleted (only `1 ≤ (N : ℝ) * B` is kept).  This is needed by the dyadic box of GM 7.2: the box scale
`M` is allowed up to `(M N)^{1+δ}/N`, so the *matched* smoothing frequency `N B` (the one that makes
the window comparison of GM 7.1 work, `B ≈ M/(M N)^η`) may exceed `T = M N` for the upper part of the
dyadic range.  The paper's GM 8.4 is stated for `T^ε ≤ B ⪅ T`, i.e. `B ≤ T^{1+δ}`.

For every `ε > 0`, every `C₀ ≥ 1`, every bumps `ψ₁, ψ₂` supported on `x ≍ 1` with
`ψ₁ 1 = ψ₂ 1 = 1` and `ψ₃` supported on `|x| ⪅ 1` with `ψ₃ 0 = 1` (`IsBumpAtOne`, `IsBumpAtZero`;
smooth, non-negative, bounded derivatives), there is `c : ℕ → ℝ → ℝ` such that for every `N ≥ 1`,
every `W ⊆ [0, M N]` that is `(M N)^ε`-separated, every `B` with `1 ≤ N B`, every `j`, `η > 0` and
`ξ ≠ 0`:

`‖𝓕 (ψ₁ · RtildeSq W N B ψ₃ ψ₂) ξ‖ ≤ c j η · (M N)^η · (M N/|ξ|)^j · sup_u (ψ₁ u · RtildeSq W N B ψ₃ ψ₂ u)`.

Proof: as in `Work.GM.S3.lemma84` (`f = ψ₁ f₁`, `f₁ = (B_s ψ₃(B_s ·)) * g`, `B_s = N B`,
`g = ψ₂‖R‖²`, so `f̂ = ψ̂₁ * (ψ̂₃(·/B_s) ĝ)`), with one extra step: for `T < |ξ| < B_s` use the
Fourier decay of `ĝ` at rate `T`, namely `‖ĝ(ξ)‖ ⪯ |W|² min(1, (T/|ξ|)^j)` (from
`‖R(u)‖² = Σ_q r(q) e^{iq log |u|}` with `|q| ≤ M N`, `Σ_q r(q) = |W|²`, and `j` integrations by
parts).  The comparison with `sup f` uses `f(1) ⪰ |W|² min(1, B_s/T)` (`Rfun_lower_near_one`); for
`B_s ≥ T` that minimum is `1`. -/
theorem lemma84_relaxed :
    ∀ ε : ℝ, 0 < ε → ∀ C₀ : ℝ, 1 ≤ C₀ →
    ∀ (ψ₁ ψ₂ ψ₃ : ℝ → ℝ), Work.GM.S3.IsBumpAtOne ψ₁ C₀ →
      Work.GM.S3.IsBumpAtOne ψ₂ C₀ → Work.GM.S3.IsBumpAtZero ψ₃ C₀ →
    ∃ c : ℕ → ℝ → ℝ,
      ∀ N : ℕ, 1 ≤ N → ∀ W : Finset ℝ,
        (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
        Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
      ∀ B : ℝ, 1 ≤ (N : ℝ) * B →
      ∀ (j : ℕ) (η : ℝ), 0 < η → ∀ ξ : ℝ, ξ ≠ 0 →
        ‖FourierTransform.fourier
            (fun u => ((ψ₁ u * Work.GM.S3.RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ)) ξ‖ ≤
          c j η * (Submission.LargeValues.M N) ^ η *
            (Submission.LargeValues.M N / |ξ|) ^ j *
            sSup (Set.range (fun u => ψ₁ u * Work.GM.S3.RtildeSq W N B ψ₃ ψ₂ u)) := by
  intro ε hε C₀ hC₀ ψ₁ ψ₂ ψ₃ h₁ h₂ h₃
  obtain ⟨c84, hc84⟩ := lemma84_clashfree ε hε C₀ hC₀ ψ₁ ψ₂ ψ₃ h₁ h₂ h₃
  obtain ⟨Ctriv, hCtrivpos, hCtriv⟩ := RtildeSq_fourier_trivial ψ₁ ψ₂ ψ₃ C₀ hC₀ h₁ h₂ h₃
  obtain ⟨K, hKnn, hK⟩ := Rsq_shifted_fourier_decay ψ₁ ψ₂ C₀ hC₀ h₁ h₂
  obtain ⟨cR, hcRpos, hcR⟩ := RtildeSq_one_lower_geT ψ₂ ψ₃ C₀ hC₀ h₂ h₃
  obtain ⟨c₃, hc₃nn, hc₃⟩ := h₃.2.2.2.2 0
  simp only [iteratedDeriv_zero] at hc₃
  have hC₀nn : (0 : ℝ) ≤ C₀ := le_trans zero_le_one hC₀
  refine ⟨fun j η => max (max Ctriv (c84 j η)) ((2 * C₀ * c₃) * K j * 2 ^ j / cR), ?_⟩
  intro N hN W hW hSep B hB j η hη ξ hξ
  set T : ℝ := Submission.LargeValues.M N with hTdef
  have hT1 : 1 ≤ T := by rw [hTdef]; exact Submission.LargeValues.M_ge_one hN
  set Bs : ℝ := (N : ℝ) * B with hBsdef
  have hBs1 : 1 ≤ Bs := hB
  have hBspos : 0 < Bs := lt_of_lt_of_le one_pos hBs1
  have hBpos : 0 < B := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    nlinarith [hBspos, hBsdef]
  have hWabs : ∀ t ∈ W, |t| ≤ T := by
    intro t ht
    have h := hW t ht
    rw [Set.mem_Icc] at h
    rw [hTdef, abs_le]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  set fR : ℝ → ℝ := fun u => ψ₁ u * RtildeSq W N B ψ₃ ψ₂ u with hfRdef
  set sF : ℝ := sSup (Set.range fR) with hsFdef
  have hRnn : ∀ u, 0 ≤ RtildeSq W N B ψ₃ ψ₂ u :=
    fun u => RtildeSq_nonneg W N B ψ₃ ψ₂ u h₃.2.1 h₂.2.1 hBpos.le
  have hfRnn : ∀ u, 0 ≤ fR u := fun u => by
    rw [hfRdef]; exact mul_nonneg (h₁.2.1 u) (hRnn u)
  have hbdd : BddAbove (Set.range fR) := by
    rw [hfRdef]
    exact bddAbove_range_RtildeSq ψ₁ ψ₂ ψ₃ C₀ h₁ h₂ h₃ W N B hBspos.le
  have hsup1 : fR 1 ≤ sF := by rw [hsFdef]; exact le_csSup hbdd (Set.mem_range_self 1)
  have hsupnn : 0 ≤ sF := le_trans (hfRnn 1) hsup1
  have hfRone : fR 1 = RtildeSq W N B ψ₃ ψ₂ 1 := by
    rw [hfRdef]; simp only [h₁.2.2.2.1, one_mul]
  have hXnn : 0 ≤ max (max Ctriv (c84 j η)) ((2 * C₀ * c₃) * K j * 2 ^ j / cR) :=
    le_trans hCtrivpos.le (le_trans (le_max_left _ _) (le_max_left _ _))
  change ‖FourierTransform.fourier
      (fun u => ((ψ₁ u * Work.GM.S3.RtildeSq W N B ψ₃ ψ₂ u : ℝ) : ℂ)) ξ‖ ≤
    max (max Ctriv (c84 j η)) ((2 * C₀ * c₃) * K j * 2 ^ j / cR) * T ^ η *
      (T / |ξ|) ^ j * sF
  by_cases hξle : |ξ| ≤ T
  · -- Case `|ξ| ≤ T`: the trivial bound.
    have h := hCtriv W N B ξ hBpos.le
    have hTη : 1 ≤ T ^ η := Real.one_le_rpow hT1 hη.le
    have hr : 1 ≤ (T / |ξ|) ^ j := by
      apply one_le_pow₀
      rw [one_le_div (abs_pos.mpr hξ)]
      exact hξle
    have h1 : Ctriv * sF ≤ max (max Ctriv (c84 j η)) ((2 * C₀ * c₃) * K j * 2 ^ j / cR) * sF := by
      refine mul_le_mul_of_nonneg_right ?_ hsupnn
      exact le_trans (le_max_left _ _) (le_max_left _ _)
    exact h.trans (h1.trans (mul_le_mul_of_one_le_one_le hXnn hsupnn hTη hr))
  · have hξgt : T < |ξ| := lt_of_not_ge hξle
    by_cases hBT : Bs ≤ T
    · -- Case `B_s ≤ T`: the original GM 8.4 (`Work.GM.S3.lemma84`).
      have h := hc84 N hN W hW hSep B hB hBT j η hη ξ hξ
      have hle : c84 j η ≤ max (max Ctriv (c84 j η)) ((2 * C₀ * c₃) * K j * 2 ^ j / cR) :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      have hTη : 0 ≤ T ^ η := Real.rpow_nonneg (le_trans zero_le_one hT1) η
      have hr : 0 ≤ (T / |ξ|) ^ j := by positivity
      refine h.trans ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hTη) hr) hsupnn
    · -- Case `T < B_s`: the new `T`-rate decay.
      set Cc : ℝ := 2 * C₀ * c₃ with hCcdef
      have hCcnn : 0 ≤ Cc := by rw [hCcdef]; positivity
      have hc₃1 : 1 ≤ c₃ := by
        have h := hc₃ 0
        rw [h₃.2.2.2.1] at h
        simpa using h
      have hCcpos : 0 < Cc := by
        rw [hCcdef]
        nlinarith [hC₀, hc₃1]
      have hBsT : T < Bs := lt_of_not_ge hBT
      have hlow : cR * (W.card : ℝ) ^ 2 ≤ sF := by
        have h := hcR W N T B hT1 hWabs hB hBsT.le
        rw [← hfRone] at h
        exact le_trans h hsup1
      have hid := fourier_shift_identity ψ₁ ψ₂ ψ₃ C₀ hC₀ h₁ h₂ h₃ W N B ξ hBpos
      rw [← hBsdef] at hid
      -- the smoothing kernel is integrable
      have hkint : Integrable (fun w : ℝ => |Bs * ψ₃ (Bs * w)|) volume := by
        have hcont : Continuous (fun w : ℝ => Bs * ψ₃ (Bs * w)) :=
          continuous_const.mul (h₃.1.continuous.comp (by fun_prop))
        refine hcont.abs.integrable_of_hasCompactSupport ?_
        refine HasCompactSupport.intro (K := Set.Icc (-(C₀ / Bs)) (C₀ / Bs)) isCompact_Icc ?_
        intro w hw
        have hmem : Bs * w ∉ Set.Icc (-C₀) C₀ := by
          intro hmem
          rw [Set.mem_Icc] at hmem
          rw [Set.mem_Icc, not_and_or] at hw
          rcases hw with h1 | h2
          · have h3 := mul_lt_mul_of_pos_left (by linarith : w < -(C₀ / Bs)) hBspos
            rw [mul_neg, mul_div_cancel₀ C₀ (ne_of_gt hBspos)] at h3
            linarith [hmem.1]
          · have h3 := mul_lt_mul_of_pos_left (by linarith : C₀ / Bs < w) hBspos
            rw [mul_div_cancel₀ C₀ (ne_of_gt hBspos)] at h3
            linarith [hmem.2]
        rw [bumpAtZero_zero_of_notMem h₃ hmem, mul_zero, abs_zero]
      have hk_le : ∫ w, |Bs * ψ₃ (Bs * w)| ≤ Cc := by
        have hind : Integrable (fun w : ℝ =>
            (Set.Icc (-(C₀ / Bs)) (C₀ / Bs)).indicator (fun _ => Bs * c₃) w) volume := by
          rw [integrable_indicator_iff measurableSet_Icc]
          exact integrableOn_const (C := Bs * c₃)
            (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
            (by rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top)
        have hcmp : ∫ w, |Bs * ψ₃ (Bs * w)| ≤
            ∫ w, (Set.Icc (-(C₀ / Bs)) (C₀ / Bs)).indicator (fun _ => Bs * c₃) w := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => abs_nonneg _) hind ?_
          refine Filter.Eventually.of_forall fun w => ?_
          by_cases hw : w ∈ Set.Icc (-(C₀ / Bs)) (C₀ / Bs)
          · rw [Set.indicator_of_mem hw]
            simp only []
            rw [abs_mul, abs_of_pos hBspos]
            exact mul_le_mul_of_nonneg_left (hc₃ (Bs * w)) hBspos.le
          · rw [Set.indicator_of_notMem hw]
            simp only []
            have hmem : Bs * w ∉ Set.Icc (-C₀) C₀ := by
              intro hmem
              rw [Set.mem_Icc] at hmem
              rw [Set.mem_Icc, not_and_or] at hw
              rcases hw with h1 | h2
              · have h3 := mul_lt_mul_of_pos_left (by linarith : w < -(C₀ / Bs)) hBspos
                rw [mul_neg, mul_div_cancel₀ C₀ (ne_of_gt hBspos)] at h3
                linarith [hmem.1]
              · have h3 := mul_lt_mul_of_pos_left (by linarith : C₀ / Bs < w) hBspos
                rw [mul_div_cancel₀ C₀ (ne_of_gt hBspos)] at h3
                linarith [hmem.2]
            rw [bumpAtZero_zero_of_notMem h₃ hmem]
            simp
        have hval : ∫ w, (Set.Icc (-(C₀ / Bs)) (C₀ / Bs)).indicator (fun _ => Bs * c₃) w
            = Cc := by
          have hC0Bs : (0 : ℝ) ≤ C₀ / Bs := div_nonneg hC₀nn hBspos.le
          rw [MeasureTheory.integral_indicator_const (Bs * c₃) measurableSet_Icc, smul_eq_mul,
            Real.volume_real_Icc_of_le (by linarith)]
          rw [hCcdef]
          field_simp
          ring
        exact hcmp.trans (le_of_eq hval)
      have hCjnn : 0 ≤ K j * (W.card : ℝ) ^ 2 * (1 + T) ^ j / |ξ| ^ j := by
        have h1 : (0 : ℝ) < 1 + T := by linarith
        have h2 : (0 : ℝ) < |ξ| ^ j := pow_pos (abs_pos.mpr hξ) j
        refine div_nonneg (mul_nonneg (mul_nonneg (hKnn j) (sq_nonneg _)) ?_) h2.le
        exact le_of_lt (pow_pos h1 j)
      have hInt : Integrable (fun w : ℝ =>
          |Bs * ψ₃ (Bs * w)| * (K j * (W.card : ℝ) ^ 2 * (1 + T) ^ j / |ξ| ^ j)) volume :=
        hkint.mul_const _
      have hge1 : ∀ w : ℝ,
          ‖(Real.fourierChar (-(ξ * w)) : ℂ) * (((Bs * ψ₃ (Bs * w) : ℝ)) : ℂ) *
              FourierTransform.fourier (fun u' => ((ψ₁ (u' + w) * ψ₂ u' *
                ‖Submission.GM.Rfun W u'‖ ^ 2 : ℝ) : ℂ)) ξ‖
            ≤ |Bs * ψ₃ (Bs * w)| * (K j * (W.card : ℝ) ^ 2 * (1 + T) ^ j / |ξ| ^ j) := by
        intro w
        have h := hK W T w hT1 hWabs j ξ hξgt
        rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real]
        exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
      have hstep : ‖∫ w, (Real.fourierChar (-(ξ * w)) : ℂ) * (((Bs * ψ₃ (Bs * w) : ℝ)) : ℂ) *
                FourierTransform.fourier (fun u' => ((ψ₁ (u' + w) * ψ₂ u' *
                  ‖Submission.GM.Rfun W u'‖ ^ 2 : ℝ) : ℂ)) ξ‖
          ≤ K j * (W.card : ℝ) ^ 2 * (1 + T) ^ j / |ξ| ^ j * Cc := by
        calc ‖∫ w, (Real.fourierChar (-(ξ * w)) : ℂ) * (((Bs * ψ₃ (Bs * w) : ℝ)) : ℂ) *
                FourierTransform.fourier (fun u' => ((ψ₁ (u' + w) * ψ₂ u' *
                  ‖Submission.GM.Rfun W u'‖ ^ 2 : ℝ) : ℂ)) ξ‖
            ≤ ∫ w, ‖(Real.fourierChar (-(ξ * w)) : ℂ) * (((Bs * ψ₃ (Bs * w) : ℝ)) : ℂ) *
                FourierTransform.fourier (fun u' => ((ψ₁ (u' + w) * ψ₂ u' *
                  ‖Submission.GM.Rfun W u'‖ ^ 2 : ℝ) : ℂ)) ξ‖ :=
              MeasureTheory.norm_integral_le_integral_norm _
          _ ≤ ∫ w, |Bs * ψ₃ (Bs * w)| *
                (K j * (W.card : ℝ) ^ 2 * (1 + T) ^ j / |ξ| ^ j) :=
              integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => norm_nonneg _) hInt
                (Filter.Eventually.of_forall hge1)
          _ = (K j * (W.card : ℝ) ^ 2 * (1 + T) ^ j / |ξ| ^ j) * ∫ w, |Bs * ψ₃ (Bs * w)| := by
              rw [MeasureTheory.integral_mul_const]
              ring
          _ ≤ (K j * (W.card : ℝ) ^ 2 * (1 + T) ^ j / |ξ| ^ j) * Cc :=
              mul_le_mul_of_nonneg_left hk_le hCjnn
      rw [hid]
      have hnew : K j * (W.card : ℝ) ^ 2 * (1 + T) ^ j / |ξ| ^ j * Cc
          ≤ (Cc * K j * 2 ^ j / cR) * T ^ η * (T / |ξ|) ^ j * sF :=
        arith_far (hKnn j) (by positivity) hCcnn hcRpos hT1 (abs_pos.mpr hξ)
          (Real.one_le_rpow hT1 hη.le) hlow
      have hle : Cc * K j * 2 ^ j / cR
          ≤ max (max Ctriv (c84 j η)) (Cc * K j * 2 ^ j / cR) := le_max_right _ _
      have hTη0 : 0 ≤ T ^ η := Real.rpow_nonneg (le_trans zero_le_one hT1) η
      have hr0 : 0 ≤ (T / |ξ|) ^ j := by positivity
      exact hstep.trans (hnew.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hTη0) hr0) hsupnn))

/-- `Work.GM.S3.Lemma84RelaxedStatement` (the interface of `Submission/Work/GM/S3/Statements.lean`),
re-exported for the consumers of this module. -/
theorem lemma84_relaxed_statement : Work.GM.S3.Lemma84RelaxedStatement := lemma84_relaxed


end Work.GM.S3
