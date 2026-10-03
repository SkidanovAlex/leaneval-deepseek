import Mathlib
import Submission.Work.KMTPlan.A6.ssuModelGain
import Submission.Work.KMTPlan.A6.Tm_l2_bdd
import Submission.Work.KMTAreas.A7.periodize_mStarF_one
import Submission.Work.KMTAreas.A7.arithSymb_eq_of_spike

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.KMTAreas.A7


/-! ## The plateau of the two §6 windows

`mStarF u = η_{≤-2u}` equals `1` on the arc of radius `2^{-2u-1}` and vanishes off the arc of
radius `2^{-2u}`; hence its periodisation is `1` wherever the periodisation of a bump supported in
the *narrower* arc `ℝ_{≤-3u}` does not vanish.  The same holds for `mStargF d u = η_{≤-2du}` with
the arc `ℝ_{≤-3du}`.  These are the two "window contains the bump" facts that make the exact-height
bands of `Tm ρ l φ` lie inside the plateau of the window. -/

lemma two_zpow_neg_three_le (u : ℕ) (hu : 1 ≤ u) :
    (2 : ℝ) ^ (-(3 * (u : ℤ))) ≤ (2 : ℝ) ^ (-(2 * (u : ℤ)) - 1) := by
  refine zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ?_
  have huZ : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu
  omega

lemma two_zpow_neg_three_mul_le (d u : ℕ) (hd : 1 ≤ d) (hu : 1 ≤ u) :
    (2 : ℝ) ^ (-(3 * (d : ℤ) * (u : ℤ))) ≤ (2 : ℝ) ^ (-((d : ℤ) * 2 * (u : ℤ)) - 1) := by
  refine zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ?_
  have hdZ : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have huZ : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu
  have hdu : (1 : ℤ) ≤ (d : ℤ) * (u : ℤ) := by nlinarith
  nlinarith

lemma two_zpow_neg_three_mul_le_eighth (d u : ℕ) (hd : 1 ≤ d) (hu : 1 ≤ u) :
    (2 : ℝ) ^ (-(3 * (d : ℤ) * (u : ℤ))) ≤ 1 / 8 := by
  have hdZ : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have huZ : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu
  have hdu : (1 : ℤ) ≤ (d : ℤ) * (u : ℤ) := by nlinarith
  calc (2 : ℝ) ^ (-(3 * (d : ℤ) * (u : ℤ))) ≤ (2 : ℝ) ^ (-3 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by nlinarith)
    _ = 1 / 8 := by norm_num

/-- **The plateau of `mStarF u`.**  If `φ` is supported in `ℝ_{≤-3u}` and `u ≥ 1`, then
`periodize (mStarF u)` is `1` wherever `periodize φ` does not vanish. -/
lemma periodize_mul_mStarF_one (u : ℕ) (hu : 1 ≤ u) (φ : ℝ → ℂ)
    (hφ : ∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (u : ℤ)))) :
    ∀ ξ : Circle, periodize φ ξ * periodize (mStarF u) ξ = periodize φ ξ := by
  intro ξ
  by_cases h : periodize φ ξ = 0
  · rw [h, zero_mul]
  · have h1 : periodize (mStarF u) ξ = 1 :=
      (periodize_mStarF_one u hu).2 φ ξ h
        (fun x hx => le_trans (hφ x hx) (two_zpow_neg_three_le u hu))
    rw [h1, mul_one]

/-- **The plateau of `mStargF d u`.**  If `ψ` is supported in `ℝ_{≤-3du}` and `d, u ≥ 1`, then
`periodize (mStargF d u)` is `1` wherever `periodize ψ` does not vanish. -/
lemma periodize_mul_mStargF_one (d u : ℕ) (hd : 1 ≤ d) (hu : 1 ≤ u) (ψ : ℝ → ℂ)
    (hψ : ∀ ξ : ℝ, ψ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (d : ℤ) * (u : ℤ)))) :
    ∀ ξ : Circle, periodize ψ ξ * periodize (mStargF d u) ξ = periodize ψ ξ := by
  intro ξ
  by_cases h : periodize ψ ξ = 0
  · rw [h, zero_mul]
  · have hone : periodize (mStargF d u) ξ = 1 := by
      obtain ⟨θ₀, hθ₀, hle⟩ :=
        arithSymbSpike_exists_coe_abs_le_of_periodize_ne_zero (φ := ψ)
          (δ := (2 : ℝ) ^ (-(3 * (d : ℤ) * (u : ℤ)))) hψ h
      have h18 : (2 : ℝ) ^ (-(3 * (d : ℤ) * (u : ℤ))) ≤ 1 / 8 :=
        two_zpow_neg_three_mul_le_eighth d u hd hu
      have hle18 : |θ₀| ≤ 1 / 8 := le_trans hle h18
      obtain ⟨hlo, hhi⟩ := abs_le.mp hle18
      have hlift : lift ξ = θ₀ := by
        rw [← hθ₀]
        exact lift_coe_of_mem θ₀ (by linarith) (by linarith)
      refine arithSymbSpike_periodize_mStargF_eq_one hd hu ?_
      rw [hlift]
      exact le_trans hle (two_zpow_neg_three_mul_le d u hd hu)
    rw [hone, mul_one]

/-! ## Composition of IW multipliers with product symbol -/

/-- **The composition of two `L^∞` Fourier multipliers is the multiplier of the product symbol.**
This is the `multiplierOf` form of `multiplier_comp`. -/
lemma multiplierOf_comp_mul {f g h : Circle → ℂ} (hf : MemLp f ⊤ circleMeasure)
    (hg : MemLp g ⊤ circleMeasure) (hh : MemLp h ⊤ circleMeasure) (hfg : f * g = h) :
    (multiplierOf f hf).comp (multiplierOf g hg) = multiplierOf h hh := by
  have key : hf.toLp f • hg.toLp g = hh.toLp h := by
    refine Lp.ext ?_
    have e1 : (hf.toLp f • hg.toLp g : Lp ℂ ⊤ circleMeasure) =ᵐ[circleMeasure]
        (⇑(hf.toLp f) • ⇑(hg.toLp g) : Circle → ℂ) := Lp.coeFn_lpSMul _ _
    have e2 : ⇑(hf.toLp f) =ᵐ[circleMeasure] f := MemLp.coeFn_toLp hf
    have e3 : ⇑(hg.toLp g) =ᵐ[circleMeasure] g := MemLp.coeFn_toLp hg
    have e4 : ⇑(hh.toLp h) =ᵐ[circleMeasure] f * g :=
      (MemLp.coeFn_toLp hh).trans
        (Filter.Eventually.of_forall (fun x => (congrFun hfg x).symm))
    filter_upwards [e1, e2, e3, e4] with x hx1 hx2 hx3 hx4
    simp only [smul_eq_mul, Pi.mul_apply, hx1, hx2, hx3, hx4]
  apply ContinuousLinearMap.ext
  intro F
  show multiplier (hf.toLp f) (multiplier (hg.toLp g) F) = multiplier (hh.toLp h) F
  rw [multiplier_comp, key]

/-- **The convolution form of the IW multiplier on `ℓ²`.**  For `f ∈ ℓ²(ℤ)` the convolution
`iwConv A Φ f` is the `L²` Fourier multiplier `iwOpSet A Φ` (equivalently `multiplierOf`) applied
to the `ℓ²` element `toL2Z f`. -/
lemma iwConv_eq_multiplierOf (A : Finset Circle) (Φ : Circle → ℂ)
    (hΦ : MemLp Φ ⊤ circleMeasure) {f : ℤ → ℂ} (hf : MemLp f 2 Measure.count) :
    iwConv A Φ f
      = ⇑(multiplierOf (iwSymbolSet A Φ) (memLp_iwSymbolSet A hΦ) (toL2Z hf)) := by
  have h := iwConvEqIwOpSetMemlp (memLp_iwSymbolSet A hΦ) (toL2Z hf)
  rw [toL2Z_coe] at h
  exact h

/-- **The IW multiplier maps `ℓ²` to `ℓ²`.**  For a bounded symbol `Φ` and `f ∈ ℓ²(ℤ)`, the
convolution `iwConv A Φ f` is in `ℓ²(ℤ)` with respect to the counting measure. -/
lemma memLp_iwConv_count (A : Finset Circle) {Φ : Circle → ℂ} (hΦ : MemLp Φ ⊤ circleMeasure)
    {f : ℤ → ℂ} (hf : MemLp f 2 Measure.count) :
    MemLp (iwConv A Φ f) 2 Measure.count := by
  rw [iwConv_eq_multiplierOf A Φ hΦ hf]
  have hmem : Memℓp (⇑(multiplierOf (iwSymbolSet A Φ) (memLp_iwSymbolSet A hΦ)
      (toL2Z hf))) 2 :=
    (multiplierOf (iwSymbolSet A Φ) (memLp_iwSymbolSet A hΦ) (toL2Z hf)).property
  refine MeasureTheory.memLp_iff.mpr ?_
  rw [eLpNorm_two_count_eq_ofReal_lpNorm _ hmem]
  exact ENNReal.ofReal_lt_top

/-! ## The exact collapse of a band piece of `Tm` -/

/-- **The collapse of a single band of `Tm`.**  Let `m` be a window whose periodisation is `1` on
the support of `periodize φ`, supported (as a symbol) in the arc `ℝ_{≤W}` at which the exact-height
frequency set `diffFreqs ρ l` is non-aliasing, and let `φ` be supported in the same arc.  Then for
`α ∈ diffFreqs ρ l` the `α`-band of `Tm ρ l φ f` for the window `m` is *exactly* the single-frequency
Ionescu--Wainger multiplier `iwConv {α} (periodize φ) f`:

`bandPiece m α (Tm ρ l φ f) = iwConv {α} (periodize φ) f`.

The proof is the symbol identity `iwSymbolSet {α} (periodize m) · iwSymbolSet A Φ = iwSymbolSet {α} Φ`
(the off-diagonal frequencies are killed by non-aliasing and the window is `1` on the band), which
is turned into an operator identity by `multiplierOf_comp_mul`. -/
theorem bandPiece_Tm_eq_iwConv (ρ : ℝ) (l : ℕ) (W : ℤ) (m : ℝ → ℂ) (φ : ℝ → ℂ) (f : ℤ → ℂ)
    (hm : Integrable m)
    (hmLp : MemLp (periodize m) ⊤ circleMeasure)
    (hmsupp : SupportedInArc W (periodize m))
    (hφLp : MemLp (periodize φ) ⊤ circleMeasure)
    (hφsupp : SupportedInArc W (periodize φ))
    (hplateau : ∀ ξ : Circle, periodize φ ξ * periodize m ξ = periodize φ ξ)
    (hNA : NonAliasing W (diffFreqs ρ l))
    (hf : MemLp f 2 Measure.count) (α : Circle) (hα : α ∈ diffFreqs ρ l) :
    bandPiece m α (Tm ρ l φ f) = iwConv {α} (periodize φ) f := by
  have hA : MemLp (iwSymbolSet (diffFreqs ρ l) (periodize φ)) ⊤ circleMeasure :=
    memLp_iwSymbolSet _ hφLp
  have hPM : MemLp (iwSymbolSet {α} (periodize m)) ⊤ circleMeasure := by
    have h := memLp_iwSymbolSet ({α} : Finset Circle) hmLp
    simpa only [iwSymbolSet, Finset.sum_singleton] using h
  have hαΦ : MemLp (iwSymbolSet {α} (periodize φ)) ⊤ circleMeasure :=
    memLp_iwSymbolSet _ hφLp
  have hsym : iwSymbolSet {α} (periodize m) * iwSymbolSet (diffFreqs ρ l) (periodize φ)
      = iwSymbolSet {α} (periodize φ) := by
    have hstep := mae_iwSymbolSet_mul_diffFreqs W (A := diffFreqs ρ l)
      (D := ({α} : Finset Circle)) (Φ := periodize φ) (Ψ := periodize m)
      (by intro β hβ; rw [Finset.mem_singleton] at hβ; subst hβ; exact hα) hNA hφsupp hmsupp
    have hpm : periodize φ * periodize m = periodize φ := funext (fun ξ => hplateau ξ)
    rw [hpm] at hstep
    exact (mul_comm _ _).trans hstep
  have hcomp : (multiplierOf (iwSymbolSet {α} (periodize m)) hPM).comp
        (multiplierOf (iwSymbolSet (diffFreqs ρ l) (periodize φ)) hA)
      = multiplierOf (iwSymbolSet {α} (periodize φ)) hαΦ :=
    multiplierOf_comp_mul hPM hA hαΦ hsym
  calc bandPiece m α (Tm ρ l φ f)
      = iwConv {α} (periodize m) (iwConv (diffFreqs ρ l) (periodize φ) f) := by
        rw [bandPiece_eq_iwConv m hm α (Tm ρ l φ f)]
        rfl
    _ = iwConv {α} (periodize m)
          (⇑(multiplierOf (iwSymbolSet (diffFreqs ρ l) (periodize φ)) hA (toL2Z hf))) := by
        rw [iwConv_eq_multiplierOf (diffFreqs ρ l) (periodize φ) hφLp hf]
    _ = ⇑(multiplierOf (iwSymbolSet {α} (periodize m)) hPM
            (multiplierOf (iwSymbolSet (diffFreqs ρ l) (periodize φ)) hA (toL2Z hf))) :=
        iwConvEqIwOpSetMemlp hPM _
    _ = ⇑(multiplierOf (iwSymbolSet {α} (periodize φ)) hαΦ (toL2Z hf)) := by
        show ⇑((multiplierOf (iwSymbolSet {α} (periodize m)) hPM).comp
            (multiplierOf (iwSymbolSet (diffFreqs ρ l) (periodize φ)) hA) (toL2Z hf)) = _
        rw [hcomp]
    _ = iwConv {α} (periodize φ) f :=
        (iwConv_eq_multiplierOf {α} (periodize φ) hφLp hf).symm

theorem ssuCollapse (ρ : ℝ) (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (l₁ l₂ u : ℕ)
    (φ ψ : ℝ → ℂ) (f g : ℤ → ℂ)
    (hΦ : MemLp (periodize φ) ⊤ circleMeasure)
    (hΨ : MemLp (periodize ψ) ⊤ circleMeasure)
    (hφ : ∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (u : ℤ))))
    (hψ : ∀ ξ : ℝ, ψ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ))))
    (hu : 1 ≤ u)
    (hNA₁ : NonAliasing (-(2 * (u : ℤ))) (Work.KMTAreas.A7.diffFreqs ρ l₁))
    (hNA₂ : NonAliasing (-(2 * ((P.natDegree : ℤ) * (u : ℤ)))) (Work.KMTAreas.A7.diffFreqs ρ l₂))
    (hf : MemLp f 2 Measure.count) (hg : MemLp g 2 Measure.count) :
    ∀ x : ℤ,
      Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂ (Work.KMTAreas.A7.mStarF u)
          (Work.KMTAreas.A7.mStargF P.natDegree u)
          (Work.KMTAreas.A7.Tm ρ l₁ φ f) (Work.KMTAreas.A7.Tm ρ l₂ ψ g) x
        = ∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₁,
            ∑ β ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
              Work.KMTAreas.A7.mZ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) α β
                * iwConv {α} (periodize φ) f x * iwConv {β} (periodize ψ) g x := by
  intro x
  have hd1 : 1 ≤ P.natDegree := le_trans (by norm_num) hd
  have huZ : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu
  have hdZ : (1 : ℤ) ≤ (P.natDegree : ℤ) := by exact_mod_cast hd1
  -- the bumps sit inside the (coarser) arcs at which the windows are supported
  have hFarc : (2 : ℝ) ^ (-(3 * (u : ℤ))) ≤ (2 : ℝ) ^ (-(2 * (u : ℤ))) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hGarc : (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)))
      ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (u : ℤ))) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by
      have hdu : (0 : ℤ) ≤ (P.natDegree : ℤ) * (u : ℤ) := by positivity
      nlinarith)
  -- the non-aliasing scale of the `g`-side, in the form of `mStargF`
  have hNA₂' : NonAliasing (-((P.natDegree : ℤ) * 2 * (u : ℤ)))
      (Work.KMTAreas.A7.diffFreqs ρ l₂) := by
    have h : (-(2 * ((P.natDegree : ℤ) * (u : ℤ))) : ℤ)
        = -((P.natDegree : ℤ) * 2 * (u : ℤ)) := by ring
    rw [h] at hNA₂
    exact hNA₂
  -- the two exact collapses of the bands of `Tm`
  have keyF : ∀ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₁,
      bandPiece (mStarF u) α (Tm ρ l₁ φ f) = iwConv {α} (periodize φ) f :=
    fun α hα => bandPiece_Tm_eq_iwConv ρ l₁ (-(2 * (u : ℤ))) (mStarF u) φ f
      (kmt_integrable_mStarF u) (kmt_MemLp_periodize_mStarF u)
      (by simpa only [mStarF] using supportedInArc_periodize_etaCut (-(2 * (u : ℤ))))
      hΦ
      (supportedInArc_periodize_of_arc
        (fun xx hx => arithSymbSpike_mem_realArc (le_trans (hφ xx hx) hFarc)))
      (fun ξ => periodize_mul_mStarF_one u hu φ hφ ξ)
      hNA₁ hf α hα
  have keyG : ∀ β ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
      bandPiece (mStargF P.natDegree u) β (Tm ρ l₂ ψ g) = iwConv {β} (periodize ψ) g :=
    fun β hβ => bandPiece_Tm_eq_iwConv ρ l₂ (-((P.natDegree : ℤ) * 2 * (u : ℤ)))
      (mStargF P.natDegree u) ψ g
      (kmt_integrable_mStargF P.natDegree u) (kmt_MemLp_periodize_mStargF P.natDegree u)
      (by simpa only [mStargF] using
        supportedInArc_periodize_etaCut (-((P.natDegree : ℤ) * 2 * (u : ℤ))))
      hΨ
      (supportedInArc_periodize_of_arc
        (fun xx hx => arithSymbSpike_mem_realArc (le_trans (hψ xx hx) hGarc)))
      (fun ξ => periodize_mul_mStargF_one P.natDegree u hd1 hu ψ hψ ξ)
      hNA₂' hg β hβ
  rw [BtwistEx_eq_sum_bandPiece ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
      (Tm ρ l₁ φ f) (Tm ρ l₂ ψ g) x
      (memLp_iwConv_count (Work.KMTAreas.A7.diffFreqs ρ l₁) hΦ hf)
      (memLp_iwConv_count (Work.KMTAreas.A7.diffFreqs ρ l₂) hΨ hg)
      (summable_cw_mStarF u) (summable_cw_mStargF P.natDegree u)]
  refine Finset.sum_congr rfl (fun α hα => Finset.sum_congr rfl (fun β hβ => ?_))
  rw [keyF α hα, keyG β hβ]

end Work.KMTPlan.A6
