import Mathlib
import Submission.Work.KMTAreas.A7G.singleHeightMaxLowpass
import Submission.Port.Aesm

set_option autoImplicit false

namespace Work.KMTAreas.A7G

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **`kmtProj` at an integer level is an `iwConv` with the `Decim.bump` symbol.** -/
theorem kmtProj_eq_iwConv_bump (ρ : ℝ) (l₁ : ℕ) (L : ℕ) (f : ℤ → ℂ) :
    Work.KMTContract.kmtProj ρ l₁ (-(L : ℤ)) f
      = Work.Analysis.IWMultiplier.iwConv (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
          (Work.KMTPlan.A6.Decim.bump L) f := rfl

/-- **The KMSZ decimation factorisation with a free period `Q` and an arbitrary height `l₁`.**
This is `Work.KMTPlan.A6.iwConv_comp_of_symbol` fed with the circle-geometry identity
`Work.KMTAreas.A7Hi.iwSymbolSet_torsFinset_mul_bump`: whenever the arithmetic frequencies
`(ℚ/ℤ)_{≤l₁}` of height `l₁` are `Q`-torsion and the coarse level `C₀` is coarser than the
`Q`-lattice (`3Q < 2^{C₀}`), the projection at the fine level `-L` (`L ≥ C₀ + 1`) is the
period-`Q` decimating convolution of the projection at the coarse level `-C₀`. -/
theorem decimFactBdd (ρ : ℝ) (l₁ C₀ : ℕ) (Q : ℕ) (hQ : 1 ≤ Q)
    (hAT : Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁
      ⊆ Work.KMTPlan.A6.Decim.torsFinset Q)
    (hnarrow : 3 * Q < 2 ^ C₀) (L : ℕ) (hL : C₀ + 1 ≤ L)
    (f : ℤ → ℂ) {B : ℝ} (hf : ∀ m : ℤ, ‖f m‖ ≤ B) :
    Work.KMTContract.kmtProj ρ l₁ (-(L : ℤ)) f
      = Work.Analysis.IWMultiplier.iwConv (Work.KMTPlan.A6.Decim.torsFinset Q)
          (Work.KMTPlan.A6.Decim.bump L)
          (Work.KMTContract.kmtProj ρ l₁ (-(C₀ : ℤ)) f) := by
  have hC₀ : 1 ≤ C₀ := by
    by_contra h
    have h0 : C₀ = 0 := by omega
    subst h0
    simp only [pow_zero] at hnarrow
    omega
  have hsym : Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTPlan.A6.Decim.torsFinset Q)
        (Work.KMTPlan.A6.Decim.bump L)
      * Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
          (Work.KMTPlan.A6.Decim.bump C₀)
      = Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
          (Work.KMTPlan.A6.Decim.bump L) :=
    Work.KMTAreas.A7Hi.iwSymbolSet_torsFinset_mul_bump Q C₀ L hQ hC₀ hnarrow hL
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁) hAT
  have hcomp := Work.KMTPlan.A6.iwConv_comp_of_symbol
    (A := Work.KMTPlan.A6.Decim.torsFinset Q)
    (D := Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
    (Φ := Work.KMTPlan.A6.Decim.bump L) (Ψ := Work.KMTPlan.A6.Decim.bump C₀)
    hsym
    (Work.KMTAreas.A7Hi.summable_iwKernel_iwSymbolSet_bump _ L)
    (Work.KMTAreas.A7Hi.hasSum_fourierSeries_iwSymbolSet_bump _ L
      (Work.KMTAreas.A7Hi.summable_iwKernel_iwSymbolSet_bump _ L))
    (Work.KMTAreas.A7Hi.memLp_two_iwSymbolSet_bump _ C₀ hC₀)
    (Work.KMTAreas.A7Hi.summable_iwKernel_iwSymbolSet_bump _ C₀)
    hf
  show Work.Analysis.IWMultiplier.iwConv (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
      (Work.KMTPlan.A6.Decim.bump L) f
    = Work.Analysis.IWMultiplier.iwConv (Work.KMTPlan.A6.Decim.torsFinset Q)
        (Work.KMTPlan.A6.Decim.bump L)
        (Work.Analysis.IWMultiplier.iwConv (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
          (Work.KMTPlan.A6.Decim.bump C₀) f)
  exact hcomp.symm

/-- **The decimated kernel at a multiple of the period is the dilate of the KMT profile.**
This is the pointwise form of "the `Q`-torsion periodisation of the level-`L` bump is the
real-scale dilation of the KMT profile `kmtPhiSch = 𝓕 η` by the factor `σ = 2^L/Q`":
`decimatedKernel Q Φ_L (Q t) = Q · 2^{-L} · kmtPhiSch (2^{-L} · Q · t)`. -/
theorem decimKernel_mul_Q (Q L : ℕ) (hQ : 1 ≤ Q) (hL : 1 ≤ L) (t : ℤ) :
    Work.BourgainPlan.Thm52.decimatedKernel Q
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))) ((Q : ℤ) * t)
      = (Q : ℂ) * (((2 : ℝ) ^ (-(L : ℤ)) : ℝ) : ℂ)
          * (Work.KMTAreas.A7Hi.kmtPhiSch (((2 : ℝ) ^ (-(L : ℤ))) * ((Q : ℝ) * (t : ℝ))) : ℂ) := by
  have hφ : MeasureTheory.Integrable
      (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))) := by
    rw [← Work.KMTAreas.A7.etaCutSchwartz_coe (-(L : ℤ))]
    exact SchwartzMap.integrable _
  have h1 : Work.BourgainPlan.Thm52.decimatedKernel Q
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))) ((Q : ℤ) * t)
      = (∑ α ∈ Work.KMTPlan.A6.Decim.torsFinset Q,
          fourier (T := 1) (-((Q : ℤ) * t)) α)
        * Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
            (-(L : ℤ))) ((Q : ℤ) * t) := by
    rw [← Work.KMTAreas.A7Hi.iwKernel_torsFinset_bump_eq_decimatedKernel Q L hQ hL ((Q : ℤ) * t)]
    exact Work.KMTPlan.A6.IwKernelArithChar (Work.KMTPlan.A6.Decim.torsFinset Q) hφ ((Q : ℤ) * t)
  have hsum : (∑ α ∈ Work.KMTPlan.A6.Decim.torsFinset Q,
      fourier (T := 1) (-((Q : ℤ) * t)) α) = (Q : ℂ) := by
    have h2 : (∑ a ∈ Finset.range Q, fourier (T := 1) (-((Q : ℤ) * t))
        (Work.KMTPlan.A6.Decim.circPt Q (a : ℤ))) = (Q : ℂ) := by
      rw [show (∑ a ∈ Finset.range Q, fourier (T := 1) (-((Q : ℤ) * t))
          (Work.KMTPlan.A6.Decim.circPt Q (a : ℤ)))
        = ∑ a ∈ Finset.range Q, fourier (T := 1) (-((Q : ℤ) * t))
            ((((a : ℝ) / (Q : ℝ)) : ℝ) : Work.Analysis.IonescuWainger.Circle) from rfl]
      rw [Work.KMTAreas.A7Hi.sum_range_fourier_div Q (-((Q : ℤ) * t))]
      rw [if_pos]
      exact ⟨-t, by ring⟩
    rw [show Work.KMTPlan.A6.Decim.torsFinset Q
        = (Finset.range Q).image (fun a : ℕ => Work.KMTPlan.A6.Decim.circPt Q (a : ℤ)) from rfl,
      Finset.sum_image]
    exact h2
    intro a ha b hb hab
    simp only at hab
    exact_mod_cast (Work.KMTPlan.A6.DecimComp.injOn_arcPt hQ ha hb hab)
  rw [h1, hsum, Work.KMTAreas.A7G.cw_etaCut_eq_dilateG, Work.KMTAreas.A7Hi.kmtPhiSch_coe]
  push_cast
  ring

/-- **The torsion-periodised bump applied to any function is `Q` times the decimated dilation
family.**  The sum-level form of `decimKernel_mul_Q`: at the point `y`,

`Σ_j decimatedKernel Q Φ_{m₀+m} (y-j) · g j = Q · Σ_j (1/σ) kmtPhiSch (Q j / σ) g (y - Q j)`,
`σ = 2^{m₀+m} = lpfScale m₀ m`, which is `Q` times `decimDilFam m₀ kmtPhiSch Q g m y`. -/
theorem iwConv_torsFinset_eq_smul_decimDilFam (Q m₀ m : ℕ) (hQ : 1 ≤ Q) (hL : 1 ≤ m₀ + m)
    (g : ℤ → ℂ) (y : ℤ) :
    Work.Analysis.IWMultiplier.iwConv (Work.KMTPlan.A6.Decim.torsFinset Q)
        (Work.KMTPlan.A6.Decim.bump (m₀ + m)) g y
      = (Q : ℂ) * Work.A7Hi2.decimDilFam m₀ Work.KMTAreas.A7Hi.kmtPhiSch Q g m y := by
  rw [Work.Analysis.IWMultiplier.iwConv_apply]
  have hcoe : ∀ j : ℤ, Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTPlan.A6.Decim.torsFinset Q)
        (Work.KMTPlan.A6.Decim.bump (m₀ + m))) j
      = Work.BourgainPlan.Thm52.decimatedKernel Q
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-((m₀ + m : ℕ) : ℤ))) j :=
    fun j => Work.KMTAreas.A7Hi.iwKernel_torsFinset_bump_eq_decimatedKernel Q (m₀ + m) hQ hL j
  rw [tsum_congr (fun j => by rw [hcoe j, smul_eq_mul])]
  have hre : (∑' j : ℤ, Work.BourgainPlan.Thm52.decimatedKernel Q
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-((m₀ + m : ℕ) : ℤ))) j
        * g (y - j))
      = ∑' j : ℤ, Work.BourgainPlan.Thm52.decimatedKernel Q
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-((m₀ + m : ℕ) : ℤ))) (y - j)
        * g j := by
    have h := Equiv.tsum_eq (Equiv.subLeft y)
      (fun i : ℤ => Work.BourgainPlan.Thm52.decimatedKernel Q
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-((m₀ + m : ℕ) : ℤ))) i
        * g (y - i))
    simpa [Equiv.subLeft_apply, sub_sub_cancel] using h.symm
  rw [hre]
  have hinj : Function.Injective (fun t : ℤ => y - (Q : ℤ) * t) := by
    intro s t hst
    have h : (Q : ℤ) * s = (Q : ℤ) * t := by linarith
    exact mul_left_cancel₀ (by exact_mod_cast (show Q ≠ 0 by omega)) h
  have hsupp : Function.support (fun j : ℤ => Work.BourgainPlan.Thm52.decimatedKernel Q
      (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-((m₀ + m : ℕ) : ℤ))) (y - j)
      * g j) ⊆ Set.range (fun t : ℤ => y - (Q : ℤ) * t) := by
    intro j hj
    rw [Function.mem_support] at hj
    have hj0 : Work.BourgainPlan.Thm52.decimatedKernel Q
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-((m₀ + m : ℕ) : ℤ))) (y - j)
        ≠ 0 := fun h => hj (by rw [h, zero_mul])
    have hdvd : (Q : ℤ) ∣ (y - j) := by
      by_contra hh
      rw [Work.BourgainPlan.Thm52.decimatedKernel, if_neg hh, mul_zero] at hj0
      exact hj0 rfl
    obtain ⟨c, hc⟩ := hdvd
    exact ⟨c, by linarith⟩
  rw [← Function.Injective.tsum_eq hinj hsupp]
  simp only [sub_sub_cancel]
  have hterm : ∀ t : ℤ, Work.BourgainPlan.Thm52.decimatedKernel Q
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-((m₀ + m : ℕ) : ℤ)))
        ((Q : ℤ) * t) * g (y - (Q : ℤ) * t)
      = (Q : ℂ) * ((1 / ((Work.KMTAreas.A7Hi.lpfScale m₀ m : ℕ) : ℝ))
          * ((Work.KMTAreas.A7Hi.kmtPhiSch ((((Q : ℤ) * t : ℤ) : ℝ)
              / ((Work.KMTAreas.A7Hi.lpfScale m₀ m : ℕ) : ℝ)) : ℂ)
            * g (y - (Q : ℤ) * t))) := by
    intro t
    rw [decimKernel_mul_Q Q (m₀ + m) hQ hL t]
    have hs : (((2 : ℝ) ^ (-(((m₀ + m : ℕ)) : ℤ)) : ℝ) : ℂ)
        = 1 / (((Work.KMTAreas.A7Hi.lpfScale m₀ m : ℕ) : ℝ) : ℂ) := by
      have hreal : (2 : ℝ) ^ (-(((m₀ + m : ℕ)) : ℤ))
          = 1 / ((Work.KMTAreas.A7Hi.lpfScale m₀ m : ℕ) : ℝ) := by
        rw [Work.KMTAreas.A7Hi.lpfScale_cast, zpow_neg, zpow_natCast, one_div]
      rw [hreal, Complex.ofReal_div, Complex.ofReal_one]
    have ha : (2 : ℝ) ^ (-(((m₀ + m : ℕ)) : ℤ)) * ((Q : ℝ) * (t : ℝ))
        = (((Q : ℤ) * t : ℤ) : ℝ) / ((Work.KMTAreas.A7Hi.lpfScale m₀ m : ℕ) : ℝ) := by
      rw [Work.KMTAreas.A7Hi.lpfScale_cast, zpow_neg, zpow_natCast, div_eq_inv_mul]
      push_cast
      ring
    rw [hs, ha]
    ring
  have hkey : (∑' t : ℤ, Work.BourgainPlan.Thm52.decimatedKernel Q
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-((m₀ + m : ℕ) : ℤ)))
        ((Q : ℤ) * t) * g (y - (Q : ℤ) * t))
      = (Q : ℂ) * (∑' t : ℤ, (1 / ((Work.KMTAreas.A7Hi.lpfScale m₀ m : ℕ) : ℝ))
          * ((Work.KMTAreas.A7Hi.kmtPhiSch ((((Q : ℤ) * t : ℤ) : ℝ)
              / ((Work.KMTAreas.A7Hi.lpfScale m₀ m : ℕ) : ℝ)) : ℂ)
            * g (y - (Q : ℤ) * t))) := by
    rw [tsum_congr hterm, tsum_mul_left]
  rw [hkey]
  rw [Work.A7Hi2.decimDilFam]
  congr 1
  refine tsum_congr (fun t => ?_)
  push_cast
  ring

/-- **A bounded function convolved with an IW kernel of a dyadic bump is bounded.** -/
theorem bdd_iwConv_bump (A : Finset Work.Analysis.IonescuWainger.Circle) (L : ℕ) {f : ℤ → ℂ}
    {B : ℝ} (hf : ∀ m : ℤ, ‖f m‖ ≤ B) :
    ∃ B' : ℝ, ∀ y : ℤ,
      ‖Work.Analysis.IWMultiplier.iwConv A (Work.KMTPlan.A6.Decim.bump L) f y‖ ≤ B' := by
  have hκ : Summable (fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump L)) j‖) :=
    Work.KMTAreas.A7Hi.summable_iwKernel_iwSymbolSet_bump A L
  refine ⟨(∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump L)) j‖) * max B 0,
    fun y => ?_⟩
  have hsum : Summable (fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump L)) j
      • f (y - j)‖) := by
    have h := Work.KMTPlan.A6.summable_ker_mul_bounded (κ := fun j : ℤ =>
      Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.KMTPlan.A6.Decim.bump L)) j) hκ hf y
    simpa only [smul_eq_mul] using h.norm
  have hsum2 : Summable (fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump L)) j‖
      * ‖f (y - j)‖) := by
    have h := Work.KMTPlan.A6.summable_ker_mul_bounded (κ := fun j : ℤ =>
      Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.KMTPlan.A6.Decim.bump L)) j) hκ hf y
    simpa only [smul_eq_mul, norm_mul] using h.norm
  rw [Work.Analysis.IWMultiplier.iwConv_apply]
  calc ‖∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump L)) j
          • f (y - j)‖
      ≤ ∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump L)) j
          • f (y - j)‖ := norm_tsum_le_tsum_norm hsum
    _ = ∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump L)) j‖
          * ‖f (y - j)‖ := by
        refine tsum_congr fun j => ?_
        rw [norm_smul]
    _ ≤ ∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump L)) j‖
          * max B 0 :=
        Summable.tsum_le_tsum
          (fun j => mul_le_mul_of_nonneg_left ((hf (y - j)).trans (le_max_left B 0)) (norm_nonneg _))
          hsum2 (hκ.mul_right (max B 0))
    _ = (∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet A (Work.KMTPlan.A6.Decim.bump L)) j‖)
          * max B 0 := tsum_mul_right

/-- **Linearity of the IW convolution in its input, for bounded inputs.** -/
theorem iwConv_sub_of_bdd {A : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ} {f g : ℤ → ℂ} {B C : ℝ}
    (hκ : Summable (fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j‖))
    (hf : ∀ m : ℤ, ‖f m‖ ≤ B) (hg : ∀ m : ℤ, ‖g m‖ ≤ C) (y : ℤ) :
    Work.Analysis.IWMultiplier.iwConv A Φ (f - g) y
      = Work.Analysis.IWMultiplier.iwConv A Φ f y
        - Work.Analysis.IWMultiplier.iwConv A Φ g y := by
  have hs1 : Summable (fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j • f (y - j)) := by
    simpa only [smul_eq_mul] using
      Work.KMTPlan.A6.summable_ker_mul_bounded (κ := fun j : ℤ =>
        Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j)
        hκ hf y
  have hs2 : Summable (fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j • g (y - j)) := by
    simpa only [smul_eq_mul] using
      Work.KMTPlan.A6.summable_ker_mul_bounded (κ := fun j : ℤ =>
        Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j)
        hκ hg y
  rw [Work.Analysis.IWMultiplier.iwConv_apply, Work.Analysis.IWMultiplier.iwConv_apply,
    Work.Analysis.IWMultiplier.iwConv_apply]
  rw [← Summable.tsum_sub hs1 hs2]
  refine tsum_congr fun j => ?_
  rw [Pi.sub_apply, smul_sub]

/-! ## `ℓᵖ`-membership in the counting measure -/

private lemma enorm_rpow_eq_ofReal' (z : ℂ) (q : ℝ) (hq : 0 ≤ q) :
    ‖z‖ₑ ^ q = ENNReal.ofReal (‖z‖ ^ q) := by
  rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq, coe_nnnorm]
  exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg z) hq

private theorem summable_of_eLpNorm_lt_top' {q : ENNReal} (hq0 : q ≠ 0) (hqt : q < ⊤)
    {u : ℤ → ℂ} (hu : MeasureTheory.eLpNorm u q MeasureTheory.Measure.count < ⊤) :
    Summable (fun n : ℤ => ‖u n‖ ^ q.toReal) := by
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 (ne_of_lt hqt)
  have hT : (∑' n : ℤ, ‖u n‖ₑ ^ q.toReal) < ⊤ := by
    have h1 : (∫⁻ n : ℤ, ‖u n‖ₑ ^ q.toReal ∂MeasureTheory.Measure.count) < ⊤ :=
      (MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (hf := by pw_aesm) hq0 (ne_of_lt hqt)).mp hu
    rwa [MeasureTheory.lintegral_count] at h1
  have h3 : (∑' n : ℤ, ENNReal.ofReal (‖u n‖ ^ q.toReal)) < ⊤ :=
    (tsum_congr (fun n => (enorm_rpow_eq_ofReal' (u n) q.toReal hqr.le).symm)).trans_lt hT
  have h4 : (∑' n : ℤ, ((Real.toNNReal (‖u n‖ ^ q.toReal) : ℝ≥0) : ℝ≥0∞)) < ⊤ := by
    simpa only [ENNReal.ofReal] using h3
  have h5 : Summable (fun n : ℤ => Real.toNNReal (‖u n‖ ^ q.toReal)) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp h4.ne
  have h6 : Summable (fun n : ℤ => (((Real.toNNReal (‖u n‖ ^ q.toReal)) : ℝ≥0) : ℝ)) :=
    NNReal.summable_coe.mpr h5
  have h7 : (fun n : ℤ => (((Real.toNNReal (‖u n‖ ^ q.toReal)) : ℝ≥0) : ℝ))
      = fun n : ℤ => ‖u n‖ ^ q.toReal := by
    funext n
    exact Real.coe_toNNReal _ (by positivity)
  rwa [h7] at h6

private theorem summable_norm_pow_of_eLpNorm_lt_top {p : ℝ} (hp : 0 < p) {f : ℤ → ℂ}
    (h : MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count < ⊤) :
    Summable (fun n : ℤ => ‖f n‖ ^ p) := by
  have h' := summable_of_eLpNorm_lt_top' (u := f) (q := ENNReal.ofReal p)
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_lt_top h
  simpa only [ENNReal.toReal_ofReal hp.le] using h'

theorem tailVarBound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r) (p : ℝ) (hp : 1 < p) :
    Work.KMTAreas.A7G.TailHyp ρ r p := by
  obtain ⟨Cρ, hCρ, C1, _hC1, hC1b⟩ := Work.KMTAreas.A7.kmtProj_lp_bound_uniform ρ hρ hρ1 p hp
  obtain ⟨C2, _hC2, hC2b⟩ := Work.A7Hi2.decimDilVarUnif Work.KMTAreas.A7Hi2.dilVarRealScale_prop
    Work.KMTAreas.A7Hi.kmtPhiSch r hr p hp
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hp0' : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hpt' : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  refine ⟨Cρ, hCρ, C2 * (2 * C1), by positivity, ?_⟩
  intro l m₀ C₀ hgood hnarrow hm0C0 f
  by_cases hftop : MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count = ⊤
  · rw [hftop, ENNReal.mul_top
      (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : (0 : ℝ) < C2 * (2 * C1)))]
    exact le_top
  · have hfle : MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count < ⊤ :=
      lt_top_iff_ne_top.mpr hftop
    obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ m : ℤ, ‖f m‖ ≤ B :=
      Work.A7Hi2.exists_norm_bound_of_summable_rpow hp0 (summable_norm_pow_of_eLpNorm_lt_top hp0 hfle)
    let Q : ℕ := Work.Analysis.IonescuWainger.iwQl ρ l
    have hQ : 1 ≤ Q := by
      dsimp only [Q]
      exact Work.Analysis.IonescuWainger.iwQl_pos
    have hQpos : (0 : ℝ) < (Q : ℝ) := by
      have h1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
      linarith
    have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQpos
    have hC0ge2 : 2 ≤ C₀ := by
      have h2 : 3 * 1 ≤ 3 * Q := Nat.mul_le_mul_left 3 hQ
      have h3 : 3 < 2 ^ C₀ := lt_of_le_of_lt (by simpa using h2) hnarrow
      by_contra hcon
      have h0 : C₀ ≤ 1 := by omega
      have h4 : 2 ^ C₀ ≤ 2 := by
        calc 2 ^ C₀ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h0
          _ = 2 := by norm_num
      omega
    -- the coarse good-major-arcs hypotheses
    have hgoodC : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(C₀ : ℤ)) :=
      Work.KMTAreas.A7G.goodMajorArcs_mono_scale (k' := -(C₀ : ℤ)) (k := -(m₀ : ℤ))
        (by omega) hgood
    have hgoodC' : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ (l - 1) (-(C₀ : ℤ)) := by
      have h := hgoodC
      rw [Work.Analysis.IonescuWainger.GoodMajorArcs] at h ⊢
      simp only [Int.cast_neg, Int.cast_natCast] at h ⊢
      have hC0r : Cρ * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ (C₀ : ℝ) := by linarith
      have hle : (2 : ℝ) ^ (ρ * ((l - 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have h1 : ((l - 1 : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast Nat.pred_le l
        nlinarith [hρ]
      have h2 : Cρ * (2 : ℝ) ^ (ρ * ((l - 1 : ℕ) : ℝ)) ≤ (C₀ : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_left hle hCρ.le) hC0r
      linarith
    -- the auxiliary curve and the decimation facts
    let G : ℤ → ℂ := fun j => Work.KMTContract.kmtProj ρ l (-(C₀ : ℤ)) f j
        - Work.KMTContract.kmtProj ρ (l - 1) (-(C₀ : ℤ)) f j
    have hAT1 : Work.Analysis.IonescuWainger.iwArithFreqs ρ l ⊆
        Work.KMTPlan.A6.Decim.torsFinset Q := by
      intro α hα
      show α ∈ Work.KMTPlan.A6.Decim.torsFinset (Work.Analysis.IonescuWainger.iwQl ρ l)
      exact Work.KMTPlan.A6.DecimComp.mem_torsFinset_of_mem_iwArithFreqs hα
    have hAT2 : Work.Analysis.IonescuWainger.iwArithFreqs ρ (l - 1) ⊆
        Work.KMTPlan.A6.Decim.torsFinset Q := fun α hα =>
      hAT1 (Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 (Nat.pred_le l) hα)
    have hfact1 : ∀ n : ℕ, Work.KMTContract.kmtProj ρ l (-(((m₀ + C₀ + 1 + n : ℕ)) : ℤ)) f
        = Work.Analysis.IWMultiplier.iwConv (Work.KMTPlan.A6.Decim.torsFinset Q)
            (Work.KMTPlan.A6.Decim.bump (m₀ + C₀ + 1 + n))
            (Work.KMTContract.kmtProj ρ l (-(C₀ : ℤ)) f) :=
      fun n => decimFactBdd ρ l C₀ Q hQ hAT1 hnarrow (m₀ + C₀ + 1 + n) (by omega) f hB
    have hfact2 : ∀ n : ℕ, Work.KMTContract.kmtProj ρ (l - 1) (-(((m₀ + C₀ + 1 + n : ℕ)) : ℤ)) f
        = Work.Analysis.IWMultiplier.iwConv (Work.KMTPlan.A6.Decim.torsFinset Q)
            (Work.KMTPlan.A6.Decim.bump (m₀ + C₀ + 1 + n))
            (Work.KMTContract.kmtProj ρ (l - 1) (-(C₀ : ℤ)) f) :=
      fun n => decimFactBdd ρ (l - 1) C₀ Q hQ hAT2 hnarrow (m₀ + C₀ + 1 + n) (by omega) f hB
    obtain ⟨B1, hB1⟩ : ∃ B1 : ℝ, ∀ y : ℤ,
        ‖Work.Analysis.IWMultiplier.iwConv (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
          (Work.KMTPlan.A6.Decim.bump C₀) f y‖ ≤ B1 :=
      bdd_iwConv_bump (Work.Analysis.IonescuWainger.iwArithFreqs ρ l) C₀ hB
    obtain ⟨B2, hB2⟩ : ∃ B2 : ℝ, ∀ y : ℤ,
        ‖Work.Analysis.IWMultiplier.iwConv (Work.Analysis.IonescuWainger.iwArithFreqs ρ (l - 1))
          (Work.KMTPlan.A6.Decim.bump C₀) f y‖ ≤ B2 :=
      bdd_iwConv_bump (Work.Analysis.IonescuWainger.iwArithFreqs ρ (l - 1)) C₀ hB
    have hGbdd : ∀ y : ℤ, ‖G y‖ ≤ B1 + B2 := by
      intro y
      have h1 : ‖Work.KMTContract.kmtProj ρ l (-(C₀ : ℤ)) f y‖ ≤ B1 := hB1 y
      have h2 : ‖Work.KMTContract.kmtProj ρ (l - 1) (-(C₀ : ℤ)) f y‖ ≤ B2 := hB2 y
      dsimp only [G]
      exact le_trans (norm_sub_le _ _) (add_le_add h1 h2)
    -- the pointwise walk identity
    have hwalk : ∀ n : ℕ, (fun x : ℤ => Work.KMTAreas.A7Hi.lpf ρ l m₀ (C₀ + 1 + n) f x
          - Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (C₀ + 1 + n) f x)
        = fun x : ℤ => (Q : ℂ) * Work.A7Hi2.decimDilFam (m₀ + C₀ + 1)
            Work.KMTAreas.A7Hi.kmtPhiSch Q G n x := by
      intro n
      funext x
      have h1 : Work.KMTAreas.A7Hi.lpf ρ l m₀ (C₀ + 1 + n) f x
          = Work.KMTContract.kmtProj ρ l (-(((m₀ + C₀ + 1 + n : ℕ)) : ℤ)) f x := by
        simp only [Work.KMTAreas.A7Hi.lpf]
        congr 1
        push_cast
        ring
      have h2 : Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (C₀ + 1 + n) f x
          = Work.KMTContract.kmtProj ρ (l - 1) (-(((m₀ + C₀ + 1 + n : ℕ)) : ℤ)) f x := by
        simp only [Work.KMTAreas.A7Hi.lpf]
        congr 1
        push_cast
        ring
      rw [h1, h2, hfact1 n, hfact2 n]
      have hlin : Work.Analysis.IWMultiplier.iwConv (Work.KMTPlan.A6.Decim.torsFinset Q)
            (Work.KMTPlan.A6.Decim.bump (m₀ + C₀ + 1 + n))
            (Work.KMTContract.kmtProj ρ l (-(C₀ : ℤ)) f
              - Work.KMTContract.kmtProj ρ (l - 1) (-(C₀ : ℤ)) f) x
          = Work.Analysis.IWMultiplier.iwConv (Work.KMTPlan.A6.Decim.torsFinset Q)
              (Work.KMTPlan.A6.Decim.bump (m₀ + C₀ + 1 + n))
              (Work.KMTContract.kmtProj ρ l (-(C₀ : ℤ)) f) x
            - Work.Analysis.IWMultiplier.iwConv (Work.KMTPlan.A6.Decim.torsFinset Q)
              (Work.KMTPlan.A6.Decim.bump (m₀ + C₀ + 1 + n))
              (Work.KMTContract.kmtProj ρ (l - 1) (-(C₀ : ℤ)) f) x :=
        iwConv_sub_of_bdd (A := Work.KMTPlan.A6.Decim.torsFinset Q)
          (Φ := Work.KMTPlan.A6.Decim.bump (m₀ + C₀ + 1 + n))
          (f := Work.KMTContract.kmtProj ρ l (-(C₀ : ℤ)) f)
          (g := Work.KMTContract.kmtProj ρ (l - 1) (-(C₀ : ℤ)) f)
          (B := B1) (C := B2)
          (Work.KMTAreas.A7Hi.summable_iwKernel_iwSymbolSet_bump _ _) hB1 hB2 x
      rw [← hlin]
      exact iwConv_torsFinset_eq_smul_decimDilFam Q (m₀ + C₀ + 1) n hQ (by omega) G x
    -- the variational norm of the walk
    have hV : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ (C₀ + 1 + n) f x
            - Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (C₀ + 1 + n) f x)
        = ENNReal.ofReal (Q : ℝ) * PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.A7Hi2.decimDilFam (m₀ + C₀ + 1)
              Work.KMTAreas.A7Hi.kmtPhiSch Q G n x) := by
      intro x
      have hfam : (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ (C₀ + 1 + n) f x
            - Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (C₀ + 1 + n) f x)
          = (Q : ℂ) • (fun n : ℕ => Work.A7Hi2.decimDilFam (m₀ + C₀ + 1)
              Work.KMTAreas.A7Hi.kmtPhiSch Q G n x) := by
        funext n
        rw [Pi.smul_apply, smul_eq_mul]
        exact congrFun (hwalk n) x
      rw [hfam, Submission.PointwiseErgodicTheorems.variationalNorm_smul hr1,
        ← ofReal_norm (Q : ℂ), Complex.norm_natCast]
    have hstep : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ (C₀ + 1 + n) f x
            - Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (C₀ + 1 + n) f x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        = ENNReal.ofReal (Q : ℝ) * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.A7Hi2.decimDilFam (m₀ + C₀ + 1)
                Work.KMTAreas.A7Hi.kmtPhiSch Q G n x))
            (ENNReal.ofReal p) MeasureTheory.Measure.count := by
      rw [show (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l m₀ (C₀ + 1 + n) f x
              - Work.KMTAreas.A7Hi.lpf ρ (l - 1) m₀ (C₀ + 1 + n) f x))
          = (fun x : ℤ => ENNReal.ofReal (Q : ℝ) * PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.A7Hi2.decimDilFam (m₀ + C₀ + 1)
                Work.KMTAreas.A7Hi.kmtPhiSch Q G n x)) from funext hV]
      exact Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (c := ENNReal.ofReal (Q : ℝ))
        ENNReal.ofReal_ne_top hp0' hpt'
    have hQle : Q ≤ Work.KMTAreas.A7Hi.lpfScale (m₀ + C₀ + 1) 0 := by
      show Q ≤ 2 ^ (m₀ + C₀ + 1 + 0)
      have h2 : 2 ^ C₀ ≤ 2 ^ (m₀ + C₀ + 1 + 0) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hle1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.A7Hi2.decimDilFam (m₀ + C₀ + 1)
            Work.KMTAreas.A7Hi.kmtPhiSch Q G n x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C2 / (Q : ℝ)) * MeasureTheory.eLpNorm G (ENNReal.ofReal p)
            MeasureTheory.Measure.count :=
      hC2b Q hQ (m₀ + C₀ + 1) hQle G
    have hGle : MeasureTheory.eLpNorm G (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (2 * C1) * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
      have h1 := hC1b l (-(C₀ : ℤ)) hgoodC f
      have h2 := hC1b (l - 1) (-(C₀ : ℤ)) hgoodC' f
      have hp1le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (le_of_lt hp)
      have hsub := MeasureTheory.eLpNorm_sub_le (μ := MeasureTheory.Measure.count)
        (f := Work.KMTContract.kmtProj ρ l (-(C₀ : ℤ)) f)
        (g := Work.KMTContract.kmtProj ρ (l - 1) (-(C₀ : ℤ)) f)
        hp1le
      calc MeasureTheory.eLpNorm G (ENNReal.ofReal p) MeasureTheory.Measure.count
          = MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ l (-(C₀ : ℤ)) f
              - Work.KMTContract.kmtProj ρ (l - 1) (-(C₀ : ℤ)) f)
              (ENNReal.ofReal p) MeasureTheory.Measure.count := rfl
        _ ≤ MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ l (-(C₀ : ℤ)) f)
              (ENNReal.ofReal p) MeasureTheory.Measure.count
            + MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ (l - 1) (-(C₀ : ℤ)) f)
              (ENNReal.ofReal p) MeasureTheory.Measure.count := hsub
        _ ≤ ENNReal.ofReal C1 * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
              MeasureTheory.Measure.count
            + ENNReal.ofReal C1 * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
              MeasureTheory.Measure.count := add_le_add h1 h2
        _ = ENNReal.ofReal (2 * C1) * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
              MeasureTheory.Measure.count := by
            rw [← add_mul, ← ENNReal.ofReal_add (by linarith) (by linarith),
              show C1 + C1 = 2 * C1 by ring]
    have hstep2 : ENNReal.ofReal (Q : ℝ) * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.A7Hi2.decimDilFam (m₀ + C₀ + 1)
              Work.KMTAreas.A7Hi.kmtPhiSch Q G n x))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Q : ℝ) * (ENNReal.ofReal (C2 / (Q : ℝ)) *
            MeasureTheory.eLpNorm G (ENNReal.ofReal p) MeasureTheory.Measure.count) :=
      mul_le_mul_of_nonneg_left hle1 bot_le
    have hstep3 : ENNReal.ofReal (Q : ℝ) * (ENNReal.ofReal (C2 / (Q : ℝ)) *
          MeasureTheory.eLpNorm G (ENNReal.ofReal p) MeasureTheory.Measure.count)
        ≤ ENNReal.ofReal (Q : ℝ) * (ENNReal.ofReal (C2 / (Q : ℝ)) *
            (ENNReal.ofReal (2 * C1) * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
              MeasureTheory.Measure.count)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGle bot_le) bot_le
    have hstep4 : ENNReal.ofReal (Q : ℝ) * (ENNReal.ofReal (C2 / (Q : ℝ)) *
          (ENNReal.ofReal (2 * C1) * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count))
        = ENNReal.ofReal (C2 * (2 * C1)) * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
      have hAB : ENNReal.ofReal (Q : ℝ) * ENNReal.ofReal (C2 / (Q : ℝ))
          = ENNReal.ofReal C2 := by
        rw [← ENNReal.ofReal_mul hQpos.le]
        congr 1
        field_simp
      have hC : ENNReal.ofReal C2 * ENNReal.ofReal (2 * C1)
          = ENNReal.ofReal (C2 * (2 * C1)) := by
        rw [← ENNReal.ofReal_mul (p := C2) (q := 2 * C1) (by linarith : (0 : ℝ) ≤ C2)]
      rw [show ENNReal.ofReal (Q : ℝ) * (ENNReal.ofReal (C2 / (Q : ℝ)) *
            (ENNReal.ofReal (2 * C1) * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
              MeasureTheory.Measure.count))
          = (ENNReal.ofReal (Q : ℝ) * ENNReal.ofReal (C2 / (Q : ℝ))
              * ENNReal.ofReal (2 * C1)) * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
              MeasureTheory.Measure.count from by ring,
        hAB, hC]
    exact (le_of_eq hstep).trans (hstep2.trans (hstep3.trans (le_of_eq hstep4)))

end

end Work.KMTAreas.A7G
