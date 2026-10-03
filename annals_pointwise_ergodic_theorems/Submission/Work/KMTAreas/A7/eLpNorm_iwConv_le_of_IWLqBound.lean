import Mathlib
import Submission.Work.KMTAreas.A7.bump_Tm_bounded
import Submission.Work.KMTAreas.schwartz_decay_bound
import Submission.Port.Aesm

namespace Work.KMTAreas.A7

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Decay of the coefficients `cw Φ j` of a Schwartz function

`cw m j = ∫_ℝ m(θ) e(-jθ) dθ` is the continuous Fourier transform of `m` at the integer frequency
`j` (`Work.KMTAreas.A7.cw_eq_fourierTransform`), so for a Schwartz function `Φ` it decays like
`j^{-2}`: the Schwartz space is stable under the Fourier transform, and any Schwartz function is
bounded by a multiple of `(1 + |t|)^{-2}` (`Work.KMTAreas.schwartz_decay_bound`). -/

/-- **Quadratic decay of the coefficients of a Schwartz function.** -/
theorem cw_schwartz_decay (Φ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℤ,
      ‖Work.KMTAreas.A7.cw (Φ : ℝ → ℂ) j‖ ≤ C / (1 + |(j : ℝ)|) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := Work.KMTAreas.schwartz_decay_bound (FourierTransform.fourier Φ)
  refine ⟨C + 1, by linarith, fun j => ?_⟩
  have h := hC (j : ℝ)
  rw [SchwartzMap.fourier_coe] at h
  rw [Work.KMTAreas.A7.cw_eq_fourierTransform]
  exact h.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))

/-! ## The `ℓ¹` (indeed `j^{-2}`) decay of the IW kernel of a periodised Schwartz symbol

The arithmetic-character identity `Work.KMTPlan.A6.IwKernelArithChar` writes the Fourier
coefficient of the IW symbol `iwSymbolSet A (periodize Φ)` as the arithmetic character
`∑_{α ∈ A} e(-jα)`, of modulus at most `#A`, times `cw Φ j`. -/

/-- **Quadratic decay of the Ionescu–Wainger kernel of a periodised Schwartz symbol.** -/
theorem iwSymbolSet_periodize_schwartz_kernel_decay (A : Finset Work.Analysis.IonescuWainger.Circle)
    (Φ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℤ,
      ‖Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet A
          (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ))) j‖
        ≤ C / (1 + |(j : ℝ)|) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := cw_schwartz_decay Φ
  refine ⟨max 1 ((A.card : ℝ) * C), lt_max_of_lt_left one_pos, fun j => ?_⟩
  rw [Work.KMTPlan.A6.IwKernelArithChar A Φ.integrable j]
  have hchar : ‖∑ α ∈ A, fourier (T := 1) (-j) α‖ ≤ (A.card : ℝ) := by
    calc ‖∑ α ∈ A, fourier (T := 1) (-j) α‖
        ≤ ∑ α ∈ A, ‖fourier (T := 1) (-j) α‖ := norm_sum_le _ _
      _ = ∑ _α ∈ A, (1 : ℝ) := by
          refine Finset.sum_congr rfl (fun α _ => ?_)
          rw [fourier_apply]
          exact _root_.Circle.norm_coe _
      _ = (A.card : ℝ) := by simp
  have hden : (0 : ℝ) < (1 + |(j : ℝ)|) ^ 2 := by positivity
  calc ‖(∑ α ∈ A, fourier (T := 1) (-j) α) * Work.KMTAreas.A7.cw (Φ : ℝ → ℂ) j‖
      = ‖∑ α ∈ A, fourier (T := 1) (-j) α‖ * ‖Work.KMTAreas.A7.cw (Φ : ℝ → ℂ) j‖ :=
        norm_mul _ _
    _ ≤ (A.card : ℝ) * (C / (1 + |(j : ℝ)|) ^ 2) :=
        mul_le_mul hchar (hC j) (norm_nonneg _) (by positivity)
    _ = ((A.card : ℝ) * C) / (1 + |(j : ℝ)|) ^ 2 := by
        rw [mul_div_assoc]
    _ ≤ max 1 ((A.card : ℝ) * C) / (1 + |(j : ℝ)|) ^ 2 :=
        div_le_div_of_nonneg_right (le_max_right _ _) (le_of_lt hden)

/-! ## The convolution against the truncations `truncZ K f` -/

/-- **The IW convolution of a truncation is the partial sum of the kernel over `Icc (n-K) (n+K)`.**
`truncZ K f` vanishes off `[-K,K]`, so the summand `iwKernel … j • f (n-j)` of the defining series
is killed as soon as `|n - j| > K`, i.e. as soon as `j ∉ Icc (n-K) (n+K)`. -/
theorem iwConv_truncZ_eq_sumIcc {A : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ} (K : ℕ) (f : ℤ → ℂ) (n : ℤ) :
    Work.Analysis.IWMultiplier.iwConv A Φ (Work.KMTContract.truncZ K f) n
      = ∑ j ∈ Finset.Icc (n - (K : ℤ)) (n + (K : ℤ)),
          Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j
            * f (n - j) := by
  have hiff : ∀ j : ℤ,
      |n - j| ≤ (K : ℤ) ↔ j ∈ Finset.Icc (n - (K : ℤ)) (n + (K : ℤ)) := by
    intro j
    rw [Finset.mem_Icc, abs_le]
    omega
  rw [Work.Analysis.IWMultiplier.iwConv_apply]
  have hzero : ∀ b : ℤ, b ∉ Finset.Icc (n - (K : ℤ)) (n + (K : ℤ)) →
      Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) b
        • Work.KMTContract.truncZ K f (n - b) = 0 := by
    intro b hb
    rw [Work.KMTContract.truncZ_of_gt (K := K) (f := f) (x := n - b) ?_, smul_zero]
    by_contra h
    exact hb ((hiff b).mp (le_of_not_gt h))
  rw [tsum_eq_sum (s := Finset.Icc (n - (K : ℤ)) (n + (K : ℤ))) hzero]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  rw [Work.KMTContract.truncZ_of_le (K := K) (f := f) (x := n - b) ((hiff b).mpr hb),
    smul_eq_mul]

/-- **Pointwise convergence of the IW convolution along the truncations `truncZ K f`.**  If the IW
kernel decays like `j^{-2}` and `f ∈ ℓ^p(ℤ)` with `1 < p`, then for every `n` the truncated
convolutions converge to the convolution of `f`: the kernel is in `ℓ¹`, `f` is bounded
(`Work.KMTContract.bound_of_memLp_count`), so `j ↦ kernel j * f (n-j)` is absolutely summable and
the truncations are its partial sums over the expanding intervals `{j : |n-j| ≤ K}`
(`Work.KMTContract.tendsto_sum_Icc_atTop`). -/
theorem iwConv_tendsto_truncZ
    {A : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hdecay : ∃ Cd : ℝ, 0 < Cd ∧ ∀ j : ℤ,
      ‖Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j‖ ≤ Cd / (1 + |(j : ℝ)|) ^ 2)
    {p : ENNReal} (hp : 1 < p) {f : ℤ → ℂ}
    (hf : MeasureTheory.MemLp f p MeasureTheory.Measure.count) (n : ℤ) :
    Filter.Tendsto (fun K : ℕ =>
        Work.Analysis.IWMultiplier.iwConv A Φ (Work.KMTContract.truncZ K f) n)
      Filter.atTop (nhds (Work.Analysis.IWMultiplier.iwConv A Φ f n)) := by
  obtain ⟨Cd, _hCd, hdec⟩ := hdecay
  have hk : Summable (fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j‖) :=
    Work.KMTContract.kernel_l1_of_decay hdec
  obtain ⟨M, hM⟩ := Work.KMTContract.bound_of_memLp_count hp hf
  have hg : Summable (fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j * f (n - j)) := by
    refine Summable.of_norm_bounded (hk.mul_left (M : ℝ)) (fun j => ?_)
    rw [norm_mul]
    calc ‖Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j‖
            * ‖f (n - j)‖
        ≤ ‖Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j‖
            * (M : ℝ) := mul_le_mul_of_nonneg_left (hM (n - j)) (norm_nonneg _)
      _ = (M : ℝ) * ‖Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j‖ := mul_comm _ _
  have hsum := Work.KMTContract.tendsto_sum_Icc_atTop hg n
  have h1 : (fun K : ℕ =>
        Work.Analysis.IWMultiplier.iwConv A Φ (Work.KMTContract.truncZ K f) n)
      = fun K : ℕ => ∑ j ∈ Finset.Icc (n - (K : ℤ)) (n + (K : ℤ)),
          Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j
            * f (n - j) :=
    funext fun K => iwConv_truncZ_eq_sumIcc K f n
  rw [h1, Work.Analysis.IWMultiplier.iwConv_apply]
  simpa only [smul_eq_mul] using hsum

/-! ## The target: extension of the `ℓ^q` bound from finitely supported to all sequences -/

/-- **Extension of the `IWLqBound` for `iwConv` from finitely supported inputs to all of `ℓ^r`.**
`IWLqBound` is only tested on finitely supported sequences; here the bound is extended to *every*
`g : ℤ → ℂ`.  When `eLpNorm g = ⊤` the right-hand side is `⊤`, since `0 < C`; otherwise `g ∈ ℓ^r`,
hence bounded, and the argument of
`Work.KMTAreas.A7.eLpNorm_iwConv_le_of_IWLqBoundScalar_of_bounded` applies: the truncations
`truncZ K g` are finitely supported and converge pointwise (because the kernel is in `ℓ¹`, here a
consequence of the `j^{-2}` decay of the kernel of a periodised Schwartz symbol), so Fatou gives
the bound in the limit. -/
theorem eLpNorm_iwConv_le_of_IWLqBound (A : Finset Work.Analysis.IonescuWainger.Circle)
    (Φ : SchwartzMap ℝ ℂ) {r : ℝ} (hr : 1 < r) {C : NNReal} (hC : 0 < C)
    (hb : Work.Analysis.IWMultiplier.IWLqBound A
      (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ)) (ENNReal.ofReal r) C) :
    ∀ g : ℤ → ℂ, MeasureTheory.eLpNorm
        (Work.Analysis.IWMultiplier.iwConv A (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ)) g)
        (ENNReal.ofReal r) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C : ℝ) * MeasureTheory.eLpNorm g (ENNReal.ofReal r) MeasureTheory.Measure.count := by
  intro g
  obtain ⟨Cd, hCd, hdec⟩ := iwSymbolSet_periodize_schwartz_kernel_decay A Φ
  by_cases htop : MeasureTheory.eLpNorm g (ENNReal.ofReal r)
      (MeasureTheory.Measure.count : Measure ℤ) = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (by exact_mod_cast hC))]
    exact le_top
  · have hflt : MeasureTheory.eLpNorm g (ENNReal.ofReal r)
        (MeasureTheory.Measure.count : Measure ℤ) < ⊤ :=
      lt_top_iff_ne_top.mpr htop
    have hfmem : MeasureTheory.MemLp g (ENNReal.ofReal r)
        (MeasureTheory.Measure.count : Measure ℤ) :=
      (MeasureTheory.memLp_iff.mpr (hflt))
    have hq1 : 1 < ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (lt_trans zero_lt_one hr)]
      exact hr
    have hle : ∀ K : ℕ,
        MeasureTheory.eLpNorm (Work.Analysis.IWMultiplier.iwConv A
            (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ))
            (Work.KMTContract.truncZ K g))
            (ENNReal.ofReal r) (MeasureTheory.Measure.count : Measure ℤ)
          ≤ ENNReal.ofReal (C : ℝ)
            * MeasureTheory.eLpNorm g (ENNReal.ofReal r)
                (MeasureTheory.Measure.count : Measure ℤ) := by
      intro K
      refine (hb ℂ (Work.KMTContract.truncZ K g)
        (finite_support_of_finSupp (Work.KMTContract.finsupp_truncZ K g))).trans ?_
      have hpt : ∀ x : ℤ, ‖Work.KMTContract.truncZ K g x‖ ≤ ‖g x‖ := by
        intro x
        by_cases hx : |x| ≤ (K : ℤ)
        · rw [Work.KMTContract.truncZ_of_le hx]
        · rw [Work.KMTContract.truncZ_of_gt (not_le.mp hx), norm_zero]
          positivity
      exact mul_le_mul_right (MeasureTheory.eLpNorm_mono (hf := by pw_aesm) hpt) _
    have hlim : ∀ x : ℤ, Filter.Tendsto (fun K : ℕ =>
          Work.Analysis.IWMultiplier.iwConv A
            (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ))
            (Work.KMTContract.truncZ K g) x)
        Filter.atTop (nhds (Work.Analysis.IWMultiplier.iwConv A
          (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ)) g x)) :=
      fun x => iwConv_tendsto_truncZ ⟨Cd, hCd, hdec⟩ hq1 hfmem x
    refine (Commons.Analysis.Hilbert.eLpNorm_le_liminf_of_tendsto
      (p := r) (by linarith) hlim).trans ?_
    have hconst : Filter.liminf (fun _ : ℕ => ENNReal.ofReal (C : ℝ)
        * MeasureTheory.eLpNorm g (ENNReal.ofReal r) (MeasureTheory.Measure.count : Measure ℤ))
        Filter.atTop
        = ENNReal.ofReal (C : ℝ)
          * MeasureTheory.eLpNorm g (ENNReal.ofReal r)
              (MeasureTheory.Measure.count : Measure ℤ) :=
      Filter.liminf_const _
    have hmono := Filter.liminf_le_liminf (f := Filter.atTop)
      (v := fun K : ℕ => MeasureTheory.eLpNorm (Work.Analysis.IWMultiplier.iwConv A
        (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ))
        (Work.KMTContract.truncZ K g))
        (ENNReal.ofReal r) (MeasureTheory.Measure.count : Measure ℤ))
      (u := fun _ : ℕ => ENNReal.ofReal (C : ℝ)
        * MeasureTheory.eLpNorm g (ENNReal.ofReal r)
            (MeasureTheory.Measure.count : Measure ℤ))
      (Filter.eventually_atTop.mpr ⟨0, fun K _ => hle K⟩)
    rw [hconst] at hmono
    exact hmono

end

end Work.KMTAreas.A7
