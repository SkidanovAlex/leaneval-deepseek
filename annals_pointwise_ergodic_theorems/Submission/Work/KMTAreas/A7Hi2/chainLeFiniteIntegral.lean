import Mathlib
import Submission.Work.KMTAreas.A7Hi.lpfChainPartDefs
import Submission.Work.KMTPlan.A6.continuous_periodize_of_hasCompactSupport
import Submission.Work.KMTAreas.A7Hi2.iwKernel_alphaDecomp
import Submission.Work.KMTAreas.A7.cw_tsum_sq_le
import Submission.Work.KMTAreas.A7.cwEtaCutDiffTsumLe
import Submission.Work.A7MixedG.chainPart_interchange
import Submission.Port.Aesm

namespace Work.KMTAreas.A7Hi2

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- `star (fourier (n - m) α) = star (fourier n α) * fourier m α`. -/
lemma star_fourier_sub' (α : Work.Analysis.IonescuWainger.Circle) (n m : ℤ) :
    star ((fourier (n - m)) α) = star ((fourier n) α) * (fourier m) α := by
  have h1 : (fourier (n - m)) α = (fourier n) α * (fourier (-m)) α := by
    rw [show n - m = n + (-m) by ring, fourier_add]
  have h2 : (fourier (-m)) α = star ((fourier m) α) := fourier_neg
  rw [h1, h2, star_mul, star_star]
  ring

/-- `star (fourier x α) * fourier x α = 1`. -/
lemma star_fourier_mul_self (α : Work.Analysis.IonescuWainger.Circle) (x : ℤ) :
    star ((fourier x) α) * (fourier x) α = 1 := by
  rw [← star_fourier_sub' α x x, sub_self, fourier_zero, star_one]

/-- `star (fourier x α) * fourier (x - j) α = star (fourier j α)`. -/
lemma star_fourier_mul_fourier_sub (α : Work.Analysis.IonescuWainger.Circle) (x j : ℤ) :
    star ((fourier x) α) * (fourier (x - j)) α = star ((fourier j) α) := by
  have h1 : (fourier (x - j)) α = (fourier x) α * (fourier (-j)) α := by
    rw [show x - j = x + (-j) by ring, fourier_add]
  have h2 : (fourier (-j)) α = star ((fourier j) α) := fourier_neg
  rw [h1, h2, ← mul_assoc, star_fourier_mul_self α x, one_mul]

/-- **The kernel of a singleton IW projection with the KMT cutoff** is the dilated fixed profile
`φ = 𝓕η`, modulated by the character `j ↦ star (fourier j α)`. -/
theorem iwKernel_singleton_etaCut (α : Work.Analysis.IonescuWainger.Circle) (k : ℤ) (j : ℤ) :
    Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet {α}
          (Work.Analysis.IonescuWainger.periodize
            (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j
      = star ((fourier j) α)
        * ((2 : ℂ) ^ k * Work.KMTAreas.A7Hi.kmtPhiSch ((2 : ℝ) ^ k * (j : ℝ))) := by
  have hcont : Continuous (Work.Analysis.IonescuWainger.periodize
      (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k)) :=
    Work.KMTPlan.A6.continuous_periodize_of_hasCompactSupport _
      (Work.KMTAreas.A7.contDiff_etaCut k).continuous (Work.KMTAreas.A7.hasCompactSupport_etaCut k)
  have hdec := Work.KMTAreas.A7Hi2.iwKernel_alphaDecomp (A := {α})
    (Work.Analysis.IonescuWainger.periodize
      (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k)) hcont j
  rw [Finset.sum_singleton] at hdec
  rw [hdec]
  have hint : MeasureTheory.Integrable
      (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) MeasureTheory.volume :=
    (Work.KMTAreas.A7.contDiff_etaCut k).continuous.integrable_of_hasCompactSupport
      (Work.KMTAreas.A7.hasCompactSupport_etaCut k)
  have hcw : Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k)) j
      = Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) j :=
    Work.KMTAreas.A7.periodize_fourierCoeff_eq_cw hint j
  rw [hcw, Work.KMTAreas.A7.cwEtaCutDiff_dilate k j, Work.KMTAreas.A7Hi.kmtPhiSch_coe]

/-- **A singleton IW projection of the cutoff is a modulated dilation family.** -/
theorem iwConv_singleton_lpf (ρ : ℝ) (l₁ m₀ : ℕ)
    (α : Work.Analysis.IonescuWainger.Circle) (f : ℤ → ℂ) (m : ℕ) (x : ℤ) :
    Work.Analysis.IWMultiplier.iwConv {α}
        (Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
            (-((m₀ : ℤ) + (m : ℤ))))) f x
      = star ((fourier x) α)
        * Work.KMTAreas.A7Hi.dilFam Work.KMTAreas.A7Hi.kmtPhiSch
            (Work.KMTAreas.A7Hi.lpfScale m₀)
            (Work.KMTAreas.A7Hi.charMul α f) m x := by
  have h1 : ((m₀ + m : ℕ) : ℤ) = (m₀ : ℤ) + (m : ℤ) := by push_cast; ring
  have hscalar : (2 : ℂ) ^ (-((m₀ : ℤ) + (m : ℤ)))
      = ((1 / ((Work.KMTAreas.A7Hi.lpfScale m₀ m : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [← h1, zpow_neg, zpow_natCast]
    push_cast [Work.KMTAreas.A7Hi.lpfScale_cast]
    ring
  rw [Work.Analysis.IWMultiplier.iwConv_apply, Work.KMTAreas.A7Hi.dilFam, ← tsum_mul_left]
  refine tsum_congr (fun j => ?_)
  simp only [smul_eq_mul, Work.KMTAreas.A7Hi.charMul_apply]
  rw [iwKernel_singleton_etaCut α (-((m₀ : ℤ) + (m : ℤ))) j]
  have hargj : (2 : ℝ) ^ (-((m₀ : ℤ) + (m : ℤ))) * (j : ℝ)
      = (j : ℝ) / ((Work.KMTAreas.A7Hi.lpfScale m₀ m : ℕ) : ℝ) := by
    rw [← h1, zpow_neg, zpow_natCast]
    push_cast [Work.KMTAreas.A7Hi.lpfScale_cast]
    ring
  rw [hscalar, hargj]
  rw [show star ((fourier x) α)
        * (1 / ((Work.KMTAreas.A7Hi.lpfScale m₀ m : ℕ) : ℝ)
            * Work.KMTAreas.A7Hi.kmtPhiSch
                ((j : ℝ) / ((Work.KMTAreas.A7Hi.lpfScale m₀ m : ℕ) : ℝ))
            * ((fourier (x - j)) α * f (x - j)))
      = (star ((fourier x) α) * (fourier (x - j)) α)
        * (1 / ((Work.KMTAreas.A7Hi.lpfScale m₀ m : ℕ) : ℝ)
            * Work.KMTAreas.A7Hi.kmtPhiSch
                ((j : ℝ) / ((Work.KMTAreas.A7Hi.lpfScale m₀ m : ℕ) : ℝ))
            * f (x - j)) from by push_cast; ring]
  rw [star_fourier_mul_fourier_sub α x j]
  push_cast
  ring


/-! ## The linearity of `iwConv` in the frequency set -/

/-- **`iwConv` is additive over a finite union of frequencies, in the direction we need.**
For a single symbol `Φ` split over its translates, the convolution with the comb symbol
`∑_{α∈A} Φ(· - α)` is the sum of the convolutions with the singletons `Φ(· - α)`, provided each
of the finitely many families is summable (which is what fails for arbitrary `f`). -/
theorem iwConv_eq_sum_singleton_of_summable
    (A : Finset Work.Analysis.IonescuWainger.Circle)
    (Φ : Work.Analysis.IonescuWainger.Circle → ℂ) (f : ℤ → ℂ) (x : ℤ)
    (hInt : ∀ α ∈ A, MeasureTheory.Integrable
      (Work.Analysis.IonescuWainger.iwSymbolSet {α} Φ)
      Work.Analysis.IonescuWainger.circleMeasure)
    (hSumm : ∀ α ∈ A, Summable (fun j : ℤ =>
      Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet {α} Φ) j * f (x - j))) :
    Work.Analysis.IWMultiplier.iwConv A Φ f x
      = ∑ α ∈ A, Work.Analysis.IWMultiplier.iwConv {α} Φ f x := by
  have hcoe : ∀ j : ℤ, Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j
      = ∑ α ∈ A, Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet {α} Φ) j := by
    intro j
    have h1 : Work.Analysis.IonescuWainger.iwSymbolSet A Φ
        = ∑ α ∈ A, Work.Analysis.IonescuWainger.iwSymbolSet {α} Φ := by
      funext ξ
      simp only [Work.Analysis.IonescuWainger.iwSymbolSet, Finset.sum_apply]
      exact Finset.sum_congr rfl (fun α _ => by simp)
    rw [Work.Analysis.IWMultiplier.iwKernel, h1,
      congrFun (fourierCoeff.sum A
        (fun α => Work.Analysis.IonescuWainger.iwSymbolSet {α} Φ) hInt) j,
      Finset.sum_apply]
    rfl
  rw [Work.Analysis.IWMultiplier.iwConv_apply]
  rw [show (fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet A Φ) j • f (x - j))
      = fun j : ℤ => ∑ α ∈ A, Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet {α} Φ) j • f (x - j) from by
    funext j
    rw [hcoe j, Finset.sum_smul]]
  rw [Summable.tsum_finsetSum (f := fun α j =>
    Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet {α} Φ) j • f (x - j)) ?_]
  · refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Work.Analysis.IWMultiplier.iwConv_apply]
  · intro α hα
    simpa only [smul_eq_mul] using hSumm α hα

/-! ## The kernel of a singleton projection is in `ℓ¹`, so its convolution with `f ∈ ℓᵖ` is summable -/

/-- An `ℓᵖ` function on `ℤ` is bounded. -/
theorem norm_le_of_summable_norm_rpow {q : ℝ} (hq : 0 < q) {f : ℤ → ℂ}
    (hf : Summable (fun n : ℤ => ‖f n‖ ^ q)) :
    ∀ n : ℤ, ‖f n‖ ≤ (∑' n : ℤ, ‖f n‖ ^ q) ^ (1 / q) := by
  intro n
  have h1 : ‖f n‖ ^ q ≤ ∑' m : ℤ, ‖f m‖ ^ q := by
    have h2 := hf.sum_le_tsum ({n} : Finset ℤ) (fun m _ => by positivity)
    simpa using h2
  calc ‖f n‖ = (‖f n‖ ^ q) ^ (1 / q) := by
        rw [← Real.rpow_mul (norm_nonneg _), mul_one_div, div_self (ne_of_gt hq), Real.rpow_one]
    _ ≤ (∑' m : ℤ, ‖f m‖ ^ q) ^ (1 / q) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)

/-- **The convolution of the singleton cutoff kernel with an `ℓᵖ` function is summable**: the
kernel is a unimodular multiple of the dilate of the Schwartz profile `φ = 𝓕η`, hence in `ℓ¹`,
while `f ∈ ℓᵖ` is bounded. -/
theorem summable_iwKernel_singleton_mul (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤)
    (α : Work.Analysis.IonescuWainger.Circle) (L : ℕ) (f : ℤ → ℂ) (x : ℤ)
    (hf : Summable (fun n : ℤ => ‖f n‖ ^ p.toReal)) :
    Summable (fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet {α}
        (Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))))) j
      * f (x - j)) := by
  have hp0 : (0 : ℝ) < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one hp)) (ne_of_lt hptop)
  have hbase : Summable (Work.KMTAreas.A7.bumpKern Work.KMTAreas.A7Hi.kmtPhiSch
      (fun _ => 2 ^ L) 0) :=
    Work.KMTAreas.A7.bumpKern_summable Work.KMTAreas.A7Hi.kmtPhiSch (fun _ => 2 ^ L)
      (fun _ => Nat.one_le_two_pow) 0
  have hpoint : ∀ j : ℤ, Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet {α}
          (Work.Analysis.IonescuWainger.periodize
            (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))))) j
      = star ((fourier j) α) * Work.KMTAreas.A7.bumpKern Work.KMTAreas.A7Hi.kmtPhiSch
          (fun _ => 2 ^ L) 0 j := by
    intro j
    rw [iwKernel_singleton_etaCut α (-(L : ℤ)) j, Work.KMTAreas.A7.bumpKern]
    have hzc : (2 : ℂ) ^ (-(L : ℤ)) = (1 : ℂ) / (((2 ^ L : ℕ) : ℝ) : ℂ) := by
      rw [show (2 : ℂ) ^ (-(L : ℤ)) = (((2 : ℝ) ^ (-(L : ℤ)) : ℝ) : ℂ) from
        (Complex.ofReal_zpow 2 (-(L : ℤ))).symm]
      push_cast
      rw [zpow_neg, zpow_natCast, one_div]
    have harg : (2 : ℝ) ^ (-(L : ℤ)) * (j : ℝ) = (j : ℝ) / (((2 ^ L : ℕ) : ℝ)) := by
      push_cast
      rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
      ring
    rw [hzc, harg]
  have hker : Summable fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet {α}
        (Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))))) j := by
    rw [show (fun j : ℤ => Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet {α}
            (Work.Analysis.IonescuWainger.periodize
              (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(L : ℤ))))) j)
        = fun j : ℤ => star ((fourier j) α) * Work.KMTAreas.A7.bumpKern
            Work.KMTAreas.A7Hi.kmtPhiSch (fun _ => 2 ^ L) 0 j from funext hpoint]
    refine Summable.of_norm_bounded (f := fun j : ℤ => star ((fourier j) α)
        * Work.KMTAreas.A7.bumpKern Work.KMTAreas.A7Hi.kmtPhiSch (fun _ => 2 ^ L) 0 j)
      (g := fun j : ℤ => ‖Work.KMTAreas.A7.bumpKern Work.KMTAreas.A7Hi.kmtPhiSch
        (fun _ => 2 ^ L) 0 j‖) hbase.norm (fun j => ?_)
    rw [norm_mul, norm_star, Work.KMTAreas.A7Hi.norm_fourier_int, one_mul]
  refine Work.KMTAreas.A7.summable_mul_bounded _ hker f
    ((∑' n : ℤ, ‖f n‖ ^ p.toReal) ^ (1 / p.toReal)) ?_ x
  exact norm_le_of_summable_norm_rpow hp0 hf

/-! ## The pointwise variational bound for the low-pass family -/

/-- **The chain part of the low-pass family is dominated by the sum over the arithmetic
frequencies of the variational norms of the modulated dilation families.**  This is the
`α`-decomposition of the Ionescu--Wainger comb, where every `α`-term is a *pure* dilation family
to which the arithmetic-free lacunary variational estimate `Work.KMTAreas.A7Hi.DilVar` applies. -/
theorem chainPart_le_sum_variationalNorm (ρ : ℝ) (l₁ m₀ : ℕ) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (f : ℤ → ℂ)
    (hf : Summable (fun n : ℤ => ‖f n‖ ^ p.toReal)) :
    ∀ x : ℤ, Work.KMTAreas.A7Hi.chainPart r (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)
      ≤ ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
          PointwiseErgodicTheorems.variationalNorm r
            (fun m : ℕ => Work.KMTAreas.A7Hi.dilFam Work.KMTAreas.A7Hi.kmtPhiSch
              (Work.KMTAreas.A7Hi.lpfScale m₀) (Work.KMTAreas.A7Hi.charMul α f) m x) := by
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  intro x
  have hperint : MeasureTheory.Integrable
      (Work.Analysis.IonescuWainger.periodize
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + (0 : ℤ)))))
      Work.Analysis.IonescuWainger.circleMeasure := by
    refine (Work.KMTPlan.A6.continuous_periodize_of_hasCompactSupport _
      (Work.KMTAreas.A7.contDiff_etaCut _).continuous
      (Work.KMTAreas.A7.hasCompactSupport_etaCut _)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfam : ∀ m : ℕ, Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x
      = ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
          Work.Analysis.IWMultiplier.iwConv {α}
            (Work.Analysis.IonescuWainger.periodize
              (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
                (-((m₀ : ℤ) + (m : ℤ))))) f x := by
    intro m
    have hperintm : MeasureTheory.Integrable
        (Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
            (-((m₀ : ℤ) + (m : ℤ))))) Work.Analysis.IonescuWainger.circleMeasure := by
      refine (Work.KMTPlan.A6.continuous_periodize_of_hasCompactSupport _
        (Work.KMTAreas.A7.contDiff_etaCut _).continuous
        (Work.KMTAreas.A7.hasCompactSupport_etaCut _)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    refine iwConv_eq_sum_singleton_of_summable _ _ f x ?_ ?_
    · intro α _
      have hmp : MeasurePreserving (fun ξ : Work.Analysis.IonescuWainger.Circle => ξ + (-α))
          Work.Analysis.IonescuWainger.circleMeasure
          Work.Analysis.IonescuWainger.circleMeasure :=
        measurePreserving_add_right _ (-α)
      have h1 : MeasureTheory.Integrable
          (fun ξ : Work.Analysis.IonescuWainger.Circle =>
            Work.Analysis.IonescuWainger.periodize
              (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
                (-((m₀ : ℤ) + (m : ℤ)))) (ξ + (-α)))
          Work.Analysis.IonescuWainger.circleMeasure :=
        (hmp.integrable_comp hperintm.1).mpr hperintm
      have hfuneq : Work.Analysis.IonescuWainger.iwSymbolSet {α}
            (Work.Analysis.IonescuWainger.periodize
              (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
                (-((m₀ : ℤ) + (m : ℤ)))))
          = fun ξ : Work.Analysis.IonescuWainger.Circle =>
              Work.Analysis.IonescuWainger.periodize
                (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
                  (-((m₀ : ℤ) + (m : ℤ)))) (ξ + (-α)) := by
        funext ξ
        simp only [Work.Analysis.IonescuWainger.iwSymbolSet_apply, Finset.sum_singleton,
          sub_eq_add_neg]
      rw [hfuneq]
      exact h1
    · intro α _
      have h1 : (-((m₀ : ℤ) + (m : ℤ))) = -(((m₀ + m : ℕ) : ℤ)) := by push_cast; ring
      rw [h1]
      exact summable_iwKernel_singleton_mul p hp hptop α (m₀ + m) f x hf
  rw [show (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)
      = fun m : ℕ => ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
          Work.Analysis.IWMultiplier.iwConv {α}
            (Work.Analysis.IonescuWainger.periodize
              (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
                (-((m₀ : ℤ) + (m : ℤ))))) f x from funext hfam]
  refine (Work.A7MixedG.chainPart_le_variationalNorm r _).trans ?_
  refine (Work.KMTAreas.A7.variationalNorm_finset_sum_le hr1
    (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁) (fun α m =>
      Work.Analysis.IWMultiplier.iwConv {α}
        (Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
            (-((m₀ : ℤ) + (m : ℤ))))) f x)).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [show (fun m : ℕ => Work.Analysis.IWMultiplier.iwConv {α}
        (Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
            (-((m₀ : ℤ) + (m : ℤ))))) f x)
      = star ((fourier x) α) • (fun m : ℕ => Work.KMTAreas.A7Hi.dilFam
          Work.KMTAreas.A7Hi.kmtPhiSch (Work.KMTAreas.A7Hi.lpfScale m₀)
          (Work.KMTAreas.A7Hi.charMul α f) m x) from by
    funext m
    rw [Pi.smul_apply, smul_eq_mul]
    exact iwConv_singleton_lpf ρ l₁ m₀ α f m x]
  rw [Submission.PointwiseErgodicTheorems.variationalNorm_smul hr1]
  have hnn : ‖(fourier x) α‖₊ = 1 := by
    rw [← NNReal.coe_inj, coe_nnnorm, NNReal.coe_one]
    exact Work.KMTAreas.A7Hi.norm_fourier_int α x
  have hnorm : ‖star ((fourier x) α)‖ₑ = 1 := by
    rw [enorm_eq_nnnorm, nnnorm_star, hnn]
    norm_num
  rw [hnorm, one_mul]

/-! ## `‖z‖ₑ ^ q = ofReal (‖z‖ ^ q)` and the two finiteness conversions -/

/-- The extended norm of a complex number to a real power is the `ofReal` of the power of its
norm. -/
lemma enorm_rpow_eq_ofReal (z : ℂ) (q : ℝ) (hq : 0 ≤ q) :
    ‖z‖ₑ ^ q = ENNReal.ofReal (‖z‖ ^ q) := by
  rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq, coe_nnnorm]
  exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg z) hq

/-- A function in `ℓᵖ(ℤ)` (`1 < p < ∞`) has finite `ℓᵖ` seminorm. -/
theorem eLpNorm_ne_top_of_summable (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤)
    (f : ℤ → ℂ) (hf : Summable (fun n : ℤ => ‖f n‖ ^ p.toReal)) :
    MeasureTheory.eLpNorm f p MeasureTheory.Measure.count ≠ ⊤ := by
  have hp0 : (0 : ℝ) < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one hp)) (ne_of_lt hptop)
  have hq : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  rw [← lt_top_iff_ne_top]
  rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (hf := by pw_aesm) hq (ne_of_lt hptop)]
  rw [lintegral_count,
    show (fun n : ℤ => ‖f n‖ₑ ^ p.toReal)
      = fun n : ℤ => ENNReal.ofReal (‖f n‖ ^ p.toReal) from
      funext (fun n => enorm_rpow_eq_ofReal (f n) p.toReal hp0.le),
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hf]
  exact ENNReal.ofReal_lt_top

/-- **The layer-cake integrand of `Work.KMTAreas.A7Hi2.chainLeFiniteIntegral` is finite** as soon
as the `ℓᵖ` seminorm of the `ℝ≥0∞`-valued function is finite. -/
theorem lintegral_ofReal_toReal_rpow_ne_top (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤)
    (g : ℤ → ENNReal) (hg : MeasureTheory.eLpNorm g p MeasureTheory.Measure.count ≠ ⊤) :
    MeasureTheory.lintegral MeasureTheory.Measure.count
      (fun x : ℤ => ENNReal.ofReal ((g x).toReal ^ p.toReal)) ≠ ⊤ := by
  have hp0 : (0 : ℝ) < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one hp)) (ne_of_lt hptop)
  have hq : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have h1 : (∫⁻ x : ℤ, g x ^ p.toReal ∂MeasureTheory.Measure.count) < ⊤ :=
    (MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (hf := by pw_aesm) hq
      (ne_of_lt hptop)).mp (lt_top_iff_ne_top.mpr hg)
  refine ne_of_lt (lt_of_le_of_lt (MeasureTheory.lintegral_mono fun x => ?_) h1)
  by_cases hx : g x = ⊤
  · rw [hx, ENNReal.toReal_top]
    simp [Real.zero_rpow (ne_of_gt hp0)]
  · have h2 : g x ^ p.toReal = ENNReal.ofReal ((g x).toReal ^ p.toReal) := by
      nth_rewrite 1 [← ENNReal.ofReal_toReal hx]
      rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp0.le]
    rw [h2]

/-! ## The `ℓᵖ` bound for the chain part of the low-pass family -/

/-- **The `α`-decomposition of the low-pass family, together with the arithmetic-free lacunary
variational estimate `Work.KMTAreas.A7Hi.DilVar`, bounds the chain part in `ℓᵖ`.** -/
theorem eLpNorm_chainPart_le (ρ : ℝ) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (l₁ m₀ : ℕ) (f : ℤ → ℂ)
    (hf : Summable (fun n : ℤ => ‖f n‖ ^ p.toReal)) :
    ∃ C : ℝ, 0 < C ∧
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  have hp0 : (0 : ℝ) < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one hp)) (ne_of_lt hptop)
  have hp1 : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.ofReal_lt_ofReal_iff hp0, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal (ne_of_lt hptop)]
    exact hp
  obtain ⟨C, hCpos, hC⟩ :=
    Work.KMTAreas.A7Hi.DilVar p.toReal hp1 r hr Work.KMTAreas.A7Hi.kmtPhiSch
  refine ⟨(1 + ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)) * C, by positivity, ?_⟩
  have hpt := chainPart_le_sum_variationalNorm ρ l₁ m₀ r hr p hp hptop f hf
  have h1 : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)) p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
          ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
            PointwiseErgodicTheorems.variationalNorm r
              (fun m : ℕ => Work.KMTAreas.A7Hi.dilFam Work.KMTAreas.A7Hi.kmtPhiSch
                (Work.KMTAreas.A7Hi.lpfScale m₀) (Work.KMTAreas.A7Hi.charMul α f) m x))
        p MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by simpa only [enorm_eq_self] using hpt x)
  have h2 : MeasureTheory.eLpNorm (fun x : ℤ =>
          ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
            PointwiseErgodicTheorems.variationalNorm r
              (fun m : ℕ => Work.KMTAreas.A7Hi.dilFam Work.KMTAreas.A7Hi.kmtPhiSch
                (Work.KMTAreas.A7Hi.lpfScale m₀) (Work.KMTAreas.A7Hi.charMul α f) m x))
        p MeasureTheory.Measure.count
      ≤ ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
          MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun m : ℕ => Work.KMTAreas.A7Hi.dilFam Work.KMTAreas.A7Hi.kmtPhiSch
                (Work.KMTAreas.A7Hi.lpfScale m₀) (Work.KMTAreas.A7Hi.charMul α f) m x))
            p MeasureTheory.Measure.count :=
    Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal (le_of_lt hp)
      (fun α _ => (measurable_of_countable _).aemeasurable)
  have h3 : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
      MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r
            (fun m : ℕ => Work.KMTAreas.A7Hi.dilFam Work.KMTAreas.A7Hi.kmtPhiSch
              (Work.KMTAreas.A7Hi.lpfScale m₀) (Work.KMTAreas.A7Hi.charMul α f) m x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    intro α _
    have hD := hC (Work.KMTAreas.A7Hi.lpfScale m₀)
      (fun m => Work.KMTAreas.A7Hi.lpfScale_pos m₀ m)
      (fun m => Work.KMTAreas.A7Hi.lpfScale_lacunary m₀ m)
      (Work.KMTAreas.A7Hi.charMul α f)
    rw [show p = ENNReal.ofReal p.toReal from (ENNReal.ofReal_toReal (ne_of_lt hptop)).symm]
    refine hD.trans (le_of_eq ?_)
    congr 1
    refine MeasureTheory.eLpNorm_congr_norm_ae (hf := by pw_aesm) (hg := by pw_aesm) (Filter.Eventually.of_forall fun y => ?_)
    exact Work.KMTAreas.A7Hi.norm_charMul α f y
  have hsum : (∑ _α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
        ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
      = ENNReal.ofReal (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ) * C)
        * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine (h1.trans (h2.trans (Finset.sum_le_sum h3))).trans ?_
  rw [hsum]
  have hcard : (0 : ℝ) ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ) :=
    Nat.cast_nonneg _
  have hle : ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ) * C
      ≤ (1 + ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)) * C :=
    mul_le_mul_of_nonneg_right (by linarith) hCpos.le
  exact mul_le_mul (ENNReal.ofReal_le_ofReal hle) le_rfl bot_le bot_le

theorem chainLeFiniteIntegral (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (Cρ₀ : ℝ) :
    ∀ (l₁ m₀ : ℕ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ₀ l₁ (-(m₀ : ℤ)) →
    ∀ f : ℤ → ℂ, Summable (fun n : ℤ => ‖f n‖ ^ p.toReal) →
      (MeasureTheory.lintegral MeasureTheory.Measure.count (fun x : ℤ => ENNReal.ofReal
        ((Work.KMTAreas.A7Hi.chainPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)).toReal ^ p.toReal)) ≠ ⊤) := by
  intro l₁ m₀ _hgood f hf
  obtain ⟨C, _hCpos, hC⟩ := eLpNorm_chainPart_le ρ r hr p hp hptop l₁ m₀ f hf
  have hfin : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)) p MeasureTheory.Measure.count
      < ⊤ :=
    lt_of_le_of_lt hC (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.mpr (eLpNorm_ne_top_of_summable p hp hptop f hf)))
  exact lintegral_ofReal_toReal_rpow_ne_top p hp hptop _ hfin.ne

end Work.KMTAreas.A7Hi2
