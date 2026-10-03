import Mathlib
import Submission.Work.KMTPlan.A6.MdlLowpassCaseHighOfDecim
import Submission.Work.KMTPlan.A6.mdlComposite_uniformSigns_le
import Submission.Work.KMTPlan.A6.varphiNtDiffSupBound
import Submission.Work.KMTPlan.A6.MdlLinVarphiNtjSupBound
import Submission.Work.KMTAreas.A7.Tm_randSymb_smallSymb
import Submission.Work.KMTAreas.A7LoLin.lepingle
import Submission.Work.KMTPlan.A6.two_pow_neg_scale_mul_Q_bound
import Submission.Work.KMTPlan.A6.two_pow_core_bound
import Submission.Port.Aesm
-- 2026-10-02: the crux-free twin of `mdlLowpassCaseHigh` used at the bottom of this file.

set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- **Narrowness of the modified bump.**  `varphiNtj N k j t` vanishes off the arc of radius
`2^{k - logN N}`: it is the product of `varphiNt N k t` (supported in `|ξ| ≤ 2^{k - logN N}`,
`varphiNt_support_le_all`) with an extra factor. -/
theorem varphiNtj_support_le (N k : ℕ) (j : ℤ) (t : ℝ) :
    ∀ ξ : ℝ, varphiNtj N k j t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by
  intro ξ hξ
  have h : Work.KMTAreas.A7.varphiNt N k t ξ ≠ 0 := by
    intro h0
    exact hξ (by rw [varphiNtj, h0, mul_zero])
  simpa only [Work.KMTAreas.A7.varphiNt] using
    Work.KMTAreas.A7.varphiNt_support_le_all k N t ξ (by
      simpa only [Work.KMTAreas.A7.varphiNt] using h)


/-- The index `n ↦ ⌊a n⌋` is monotone for a lacunary sequence with `Λ > 1` and `a n ≥ 1`.

2026-10-02: **renamed** from `monotone_floor_lacunary` — the same statement is declared under that
name in `Submission/Work/KMTPlan/A6/lowpassVarFromDecim.lean:68`, and the two cannot coexist in one
environment (the two are now imported together, because `mdlLowpassCaseHigh` below is taken from
the crux-free `MdlLowpassCaseHighOfDecim`, whose closure contains `lowpassVarFromDecim`).  Every
consumer of *this* module already has `lowpassVarFromDecim` in its closure, so the public name
remains available to them. -/
theorem monotone_floor_lacunary_slice {a : ℕ → NNReal} {Λ : NNReal} (hΛ : 1 < Λ)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) :
    Monotone fun n => Nat.floor (a n) := by
  refine monotone_nat_of_le_succ fun n => ?_
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have hne : a n ≠ 0 := ne_of_gt hpos
  have h : Λ < a (n + 1) / a n := ha n
  have h2 : a n < a (n + 1) := by
    have h3 : a (n + 1) = (a (n + 1) / a n) * a n := by
      rw [div_mul_cancel₀ _ hne]
    rw [h3]
    calc a n = 1 * a n := (one_mul _).symm
      _ < (a (n + 1) / a n) * a n := mul_lt_mul_of_pos_right (lt_trans hΛ h) hpos
  exact Nat.floor_mono (le_of_lt h2)

/-- **`mdlCore` is *upward closed* in the scale index**: `inIndexSet`, the large-scale cut
`splitCut < N` and `mainRegime` are all upward closed in `N`, and `n ↦ ⌊a n⌋` is monotone.  Hence
the core condition is a *suffix* of `ℕ`, and the target's clipped family is the full family with
an initial segment zeroed. -/
theorem mdlCore_of_le {ρ : ℝ} {C₀ : ℕ} {a : ℕ → NNReal} {l₁ l₂ k₁ k₂ m n : ℕ}
    (hfloor : Monotone fun n => Nat.floor (a n)) (hnm : n ≤ m)
    (hm : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n) : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ m := by
  obtain ⟨hin, hcut, hmain⟩ := hm
  have hN : Nat.floor (a n) ≤ Nat.floor (a m) := hfloor hnm
  have hhs : Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n))
      ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a m)) := by
    unfold Work.Analysis.EndVar.heightScale
    exact Nat.mul_le_mul_left C₀ (Work.Analysis.EndVar.logLogN_mono hN)
  have hlog : Work.Analysis.EndVar.logN (Nat.floor (a n))
      ≤ Work.Analysis.EndVar.logN (Nat.floor (a m)) := Work.Analysis.EndVar.logN_mono hN
  have hhsZ : ((Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ)
      ≤ ((Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a m)) : ℕ) : ℤ) := by
    exact_mod_cast hhs
  refine ⟨⟨le_trans hin.1 hhsZ, le_trans hin.2.1 hhsZ, le_trans hin.2.2 hhsZ⟩,
    lt_of_lt_of_le hcut hN, ?_⟩
  have htoNat : (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat
      ≤ (Work.Analysis.EndVar.logN (Nat.floor (a m))).toNat := Int.toNat_le_toNat hlog
  unfold Work.KMTAreas.A7.mainRegime at hmain ⊢
  constructor <;> omega


/-- The KMT cutoff is measurable. -/
theorem measurable_kmtEta : Measurable Work.KMTContract.kmtEta := by
  have h : Work.KMTContract.kmtEta
      = fun x : ℝ => ((Work.KMTContract.kmtBump : ℝ → ℝ) x : ℂ) := rfl
  rw [h]
  exact Complex.continuous_ofReal.measurable.comp Work.KMTContract.kmtBump.continuous.measurable

/-- The bump `varphiN N k` is measurable. -/
theorem measurable_varphiN_self (N k : ℕ) : Measurable (Work.KMTAreas.A7.varphiN N k) := by
  unfold Work.KMTAreas.A7.varphiN
  split_ifs with hk
  · exact measurable_kmtEta.comp (by fun_prop)
  · exact (measurable_kmtEta.comp (by fun_prop)).sub (measurable_kmtEta.comp (by fun_prop))

/-- The modified bump `varphiNtj N k j t` is measurable in the frequency variable. -/
theorem measurable_varphiNtj (N k : ℕ) (j : ℤ) (t : ℝ) :
    Measurable (varphiNtj N k j t) := by
  unfold varphiNtj Work.KMTAreas.A7.varphiNt Work.KMTAreas.A7.ee
  refine Measurable.mul ?_ ?_
  · refine Measurable.pow_const ?_ j
    exact Complex.continuous_ofReal.measurable.comp (by fun_prop)
  · exact (measurable_varphiN_self N k).mul (Complex.continuous_exp.measurable.comp (by fun_prop))

/-- **Narrowness of the modified bump on the core.**  If `m₀` is a core index and `n ≥ m₀`, then
the modified bump at the scale `N_n = ⌊a n⌋` vanishes off the arc `realArc (k₁ - logN N_{m₀})`,
the narrowness level that does not depend on `n`. -/
theorem varphiNtj_narrow_core {ρ : ℝ} {C₀ : ℕ} {a : ℕ → NNReal} {l₁ l₂ k₁ k₂ m₀ n : ℕ}
    (hfloor : Monotone fun n => Nat.floor (a n))
    (hm₀ : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ m₀) (hn : m₀ ≤ n) (j : ℤ) (t : ℝ) :
    ∀ ξ : ℝ, varphiNtj (Nat.floor (a n)) k₁ j t ξ ≠ 0 →
      ξ ∈ Work.Analysis.IonescuWainger.realArc
        ((k₁ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a m₀))) := by
  intro ξ hξ
  have h := varphiNtj_support_le (Nat.floor (a n)) k₁ j t ξ hξ
  have hlog : Work.Analysis.EndVar.logN (Nat.floor (a m₀))
      ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) :=
    Work.Analysis.EndVar.logN_mono (hfloor hn)
  have hExp : (k₁ : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ)
      ≤ (((k₁ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a m₀)) : ℤ) : ℝ) := by
    have hZ : (k₁ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n))
        ≤ (k₁ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a m₀)) := by omega
    calc (k₁ : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ)
        = (((k₁ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ) := by
          push_cast; ring
      _ ≤ _ := by exact_mod_cast hZ
  have hb' : |ξ| ≤ (2 : ℝ) ^ ((((k₁ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a m₀)) : ℤ) : ℝ)) :=
    h.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp)
  have hb : |ξ| ≤ (2 : ℝ) ^ ((k₁ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a m₀))) := by
    rw [← Real.rpow_intCast]
    exact hb'
  rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
  exact ⟨by linarith [(abs_le.mp hb).1], (abs_le.mp hb).2⟩

/-- **The narrow-case variational estimate for a lacunary family of narrow Ionescu--Wainger
bumps.**  If `Φ` is a family of Schwartz symbols supported in the short arc `ℝ_{≤k}`
(`2^k < 1/2`, `(l,k)` a good-major-arcs pair), and if every finite signed sum of the `Φ n`
is bounded pointwise by `M`, then the `r`-variation (`r > 2`) of the family of Ionescu--Wainger
projections `Tle ρ l (Φ n)` is bounded in `ℓ²(ℤ)` by `K ⟨l⟩ M`.

The proof is the `q = 2` case of the Ionescu--Wainger multiplier theorem
(`IWMultiplierBoundScalar_q2`) fed into the Marcinkiewicz--Zygmund transfer
`varEst_of_uniformSigns_of_measurable`: the uniform-in-signs `ℓ²` bound for the family is the
`ℓ²` bound of the single multiplier with the signed-sum symbol. -/
theorem mdlNarrowVarEst
    (ρ : ℝ) (hρ : 0 < ρ) (l : ℕ) (k : ℤ) (hk : (2 : ℝ) ^ k < 1 / 2)
    (Cρ : ℝ) (hCρ2 : 2 ≤ Cρ)
    (hNA : ∀ (l' : ℕ) (k' : ℤ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l' k' →
      Work.Analysis.IonescuWainger.NonAliasing k' (Work.Analysis.IonescuWainger.iwArithFreqs ρ l'))
    (hgood : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k)
    (Φ : ℕ → SchwartzMap ℝ ℂ)
    (hnarrow : ∀ n ξ, (Φ n : ℝ → ℂ) ξ ≠ 0 → ξ ∈ Work.Analysis.IonescuWainger.realArc k)
    (M : ℝ) (hMpos : 0 < M)
    (hsup : ∀ (U : Finset ℕ) (ω : ℕ → Bool), ∀ ξ : ℝ,
      ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * (Φ n : ℝ → ℂ) ξ‖ ≤ M)
    (r : NNReal) (hr : 2 < r) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l (Φ n : ℝ → ℂ) f x))
        2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (K * ((Work.Analysis.IWMultiplier.angleBracket l : ℝ) * M)) *
        MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  obtain ⟨K, hKpos, hK⟩ :=
    Work.KMTAreas.A7.varEst_of_uniformSigns_of_measurable 2 (by norm_num) r hr
  refine ⟨K, hKpos, fun f => ?_⟩
  have h := hK (fun n g => Work.KMTAreas.A7.Tle ρ l (Φ n : ℝ → ℂ) g) ?_
    ((Work.Analysis.IWMultiplier.angleBracket l : ℝ) * M) (by positivity) ?_ f
  · rw [show ENNReal.ofReal 2 = (2 : ENNReal) from by norm_num] at h
    exact h
  · intro n g; exact (measurable_of_countable _).aemeasurable
  · intro U ω g
    by_cases hg : ∃ B : ℝ, ∀ m : ℤ, ‖g m‖ ≤ B
    · obtain ⟨B, hB⟩ := hg
      set ΨS : SchwartzMap ℝ ℂ := ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) • (Φ n) with hΨS
      have hΨcoe : (ΨS : ℝ → ℂ)
          = fun ξ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * (Φ n : ℝ → ℂ) ξ := by
        funext ξ
        rw [hΨS, SchwartzMap.sum_apply]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        by_cases hn : ω n <;> simp [hn]
      have hident := Work.KMTAreas.A7.Tle_finsetSum_of_bounded ρ l k hk Φ hnarrow U ω hB
      have hΨnarrow : ∀ ξ : ℝ, (ΨS : ℝ → ℂ) ξ ≠ 0 →
          ξ ∈ Work.Analysis.IonescuWainger.realArc k := by
        intro ξ hξ
        rw [hΨcoe] at hξ
        by_contra hcon
        apply hξ
        refine Finset.sum_eq_zero (fun n _ => ?_)
        by_cases h : (if ω n then (1 : ℂ) else -1) = 0
        · rw [h, zero_mul]
        · have hz : (Φ n : ℝ → ℂ) ξ = 0 := by
            by_contra hne
            exact hcon (hnarrow n ξ hne)
          rw [hz, mul_zero]
      have hΨbd : ∀ ξ : ℝ, ‖(ΨS : ℝ → ℂ) ξ‖ ≤ M := by
        intro ξ; rw [hΨcoe]; exact hsup U ω ξ
      have hΨsum : ∀ x : ℝ, Summable fun j : ℤ => (ΨS : ℝ → ℂ) (x + j) := by
        intro x; exact (Work.KMTAreas.schwartz_shift_summable ΨS x).of_norm
      have hΨm : Measurable (ΨS : ℝ → ℂ) := ΨS.continuous.measurable
      let Mnn : NNReal := ⟨M, hMpos.le⟩
      have hMnnc : (Mnn : ℝ) = M := rfl
      have hIW := Work.Analysis.IWMultiplier.IWMultiplierBoundScalar_q2 (M := Mnn) hρ hCρ2
        hNA hgood hΨm hΨnarrow hΨsum hΨbd
      have hIW' : Work.Analysis.IWMultiplier.IWLqBoundScalar
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize (ΨS : ℝ → ℂ)) (ENNReal.ofReal 2)
          (Work.Analysis.IWMultiplier.angleBracket l * Mnn) := by
        rw [show ENNReal.ofReal 2 = (2 : ENNReal) from by norm_num]
        exact hIW
      have hκ : Summable fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize (ΨS : ℝ → ℂ))) j‖ :=
        Work.KMTAreas.A7.summable_iwKernel_narrow_schwartz ρ l ΨS hΨnarrow
      have hbound := Work.KMTAreas.A7.eLpNorm_iwConv_le_of_IWLqBoundScalar_of_bounded
        (q := 2) (by norm_num) hκ hIW' ⟨B, hB⟩
      have hcoec : (((Work.Analysis.IWMultiplier.angleBracket l * Mnn : NNReal)) : ℝ)
          = ((Work.Analysis.IWMultiplier.angleBracket l : ℝ) * M) := by
        rw [NNReal.coe_mul, hMnnc]
      have hfun : (fun x : ℤ => ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            Work.KMTAreas.A7.Tle ρ l (Φ n : ℝ → ℂ) g x‖ₑ ^ (2 : ℝ))
          = (fun x : ℤ => ‖Work.KMTAreas.A7.Tle ρ l
              (fun ξ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * (Φ n : ℝ → ℂ) ξ) g x‖ₑ
              ^ (2 : ℝ)) := by
        funext x; rw [congrFun hident x]
      have hmain : MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tle ρ l
            (fun ξ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * (Φ n : ℝ → ℂ) ξ) g)
            (ENNReal.ofReal 2) MeasureTheory.Measure.count
          = MeasureTheory.eLpNorm (Work.Analysis.IWMultiplier.iwConv
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
              (Work.Analysis.IonescuWainger.periodize (ΨS : ℝ → ℂ)) g)
            (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
        rw [hΨcoe]
        rfl
      calc ∫⁻ x : ℤ, ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
              Work.KMTAreas.A7.Tle ρ l (Φ n : ℝ → ℂ) g x‖ₑ ^ (2 : ℝ)
              ∂MeasureTheory.Measure.count
          = ∫⁻ x : ℤ, ‖Work.KMTAreas.A7.Tle ρ l
              (fun ξ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * (Φ n : ℝ → ℂ) ξ) g x‖ₑ
              ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
              rw [hfun]
        _ = (MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tle ρ l
              (fun ξ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * (Φ n : ℝ → ℂ) ξ) g)
              (ENNReal.ofReal 2) MeasureTheory.Measure.count) ^ (2 : ℝ) := by
              rw [Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow _ (by norm_num)]
        _ = (MeasureTheory.eLpNorm (Work.Analysis.IWMultiplier.iwConv
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
              (Work.Analysis.IonescuWainger.periodize (ΨS : ℝ → ℂ)) g)
              (ENNReal.ofReal 2) MeasureTheory.Measure.count) ^ (2 : ℝ) := by
              rw [hmain]
        _ ≤ (ENNReal.ofReal
              (((Work.Analysis.IWMultiplier.angleBracket l * Mnn : NNReal) : ℝ)) *
              MeasureTheory.eLpNorm g (ENNReal.ofReal 2) MeasureTheory.Measure.count)
              ^ (2 : ℝ) :=
              ENNReal.rpow_le_rpow hbound (by norm_num)
        _ = ENNReal.ofReal
              ((((Work.Analysis.IWMultiplier.angleBracket l * Mnn : NNReal) : ℝ)) ^ (2 : ℝ)) *
              (MeasureTheory.eLpNorm g (ENNReal.ofReal 2) MeasureTheory.Measure.count)
              ^ (2 : ℝ) := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
                ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
        _ = ENNReal.ofReal ((((Work.Analysis.IWMultiplier.angleBracket l : ℝ) * M) ^ (2 : ℝ))) *
              (MeasureTheory.eLpNorm g (ENNReal.ofReal 2) MeasureTheory.Measure.count)
              ^ (2 : ℝ) := by
              rw [hcoec]
        _ = ENNReal.ofReal ((((Work.Analysis.IWMultiplier.angleBracket l : ℝ) * M) ^ (2 : ℝ))) *
              ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
              rw [Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow g (by norm_num)]
    · have htop : (∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) = ⊤ := by
        by_contra hne
        have hne2 : (MeasureTheory.eLpNorm g (ENNReal.ofReal 2)
            MeasureTheory.Measure.count) ^ (2 : ℝ) ≠ ⊤ := by
          rwa [← Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow g (by norm_num)]
        have hlt : MeasureTheory.eLpNorm g (ENNReal.ofReal 2) MeasureTheory.Measure.count < ⊤ := by
          rw [lt_top_iff_ne_top]
          intro hcon
          exact hne2 (by rw [hcon]; simp)
        obtain ⟨C, hC⟩ :=
          Work.KMTAreas.A7.eLpNorm_finite_bounded (ENNReal.ofReal 2) (by norm_num) g hlt
        exact hg ⟨C, hC⟩
      have hM'pos : (0 : ℝ) < (Work.Analysis.IWMultiplier.angleBracket l : ℝ) * M := by
        have h1 : (1 : ℝ) ≤ (Work.Analysis.IWMultiplier.angleBracket l : ℝ) := by
          exact_mod_cast Work.Analysis.IWMultiplier.one_le_angleBracket l
        nlinarith [hMpos]
      rw [htop, ENNReal.mul_top]
      · exact le_top
      · rw [ENNReal.ofReal_ne_zero_iff]
        positivity

/-- `1 ≤ uScale ρ L`: the auxiliary scale is at least one. -/
theorem one_le_uScale (ρ : ℝ) (hρ : 0 < ρ) (L : ℕ) :
    1 ≤ Work.KMTAreas.A7.uScale ρ L := by
  rw [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount]
  have hx : ((1 : ℤ) : ℝ) ≤ ((1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
      rw [← Real.rpow_zero (2 : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by positivity)
    have h3 : ((1 : ℤ) : ℝ) = ((1 : ℕ) : ℝ) := by norm_num
    have h4 : (0 : ℝ) ≤ ((1 : ℕ) : ℝ) := by norm_num
    nlinarith [h2, h3, h4]
  have h2 : (1 : ℤ) ≤ ⌊((1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ := Int.le_floor.mpr hx
  omega

/-- `uScale ρ` is monotone in the scale parameter. -/
private theorem uScale_mono (ρ : ℝ) (hρ : 0 ≤ ρ) {L L' : ℕ} (h : L ≤ L') :
    Work.KMTAreas.A7.uScale ρ L ≤ Work.KMTAreas.A7.uScale ρ L' := by
  rw [Work.KMTAreas.A7.uScale, Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount,
    Work.Analysis.EndVar.scaleCount]
  refine Int.toNat_le_toNat (Int.floor_mono ?_)
  have hc : (L : ℝ) ≤ (L' : ℝ) := by exact_mod_cast h
  have hexp : 2 * ρ * (L : ℝ) ≤ 2 * ρ * (L' : ℝ) := by nlinarith
  have h2 : (2 : ℝ) ^ (2 * ρ * (L : ℝ)) ≤ (2 : ℝ) ^ (2 * ρ * (L' : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **The vanishing case of the linear estimate, with a uniform constant** (`k₁ ≥ 1`, or
`k₁ = 0` with `j₁ ≠ 0`): there is `K > 0`, depending only on `(ρ, C₀, R, j₁, M)` and in particular
*not* on `(a, Λ, l₁, l₂, k₁, k₂, t, f)`, such that the family of Ionescu--Wainger projections of
the exact-height shells clipped at the core satisfies the variational estimate with that constant
for every sup bound `M` of the signed sums of the modified bumps.

The proof is that of `mdlVanishingCase`; the two factors `2^{k*}·Q²` and `2^{-u}·Q²` of the
composite constant are bounded uniformly in the parameters by `two_pow_core_bound` and
`two_pow_neg_scale_mul_Q_bound`. -/
theorem mdlVanishingCaseUnif
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (C₀ : ℕ) (R : NNReal) (hR : 2 < R) (j₁ : ℤ)
    (M : ℝ) (hMnn : 1 ≤ M) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
        (hΛ : 1 < Λ) → (ha : PointwiseErgodicTheorems.Lacunary Λ a) → (ha1 : ∀ n, 1 ≤ a n) →
        (hMsup : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (ξ : ℝ),
          ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * varphiNtj (Nat.floor (a n)) k₁ j₁ t ξ‖ ≤ M) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ =>
            if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
              Work.KMTAreas.A7.Tle ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t)
                (mdlF ρ (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f) x
            else 0)) 2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal K * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨Qc, hQcpos, hQcelem⟩ := Work.Analysis.IonescuWainger.iwP_element_le hρ
  obtain ⟨Ck, hCkpos, hCk⟩ := two_pow_core_bound ρ hρ hρ1 Qc hQcpos
  obtain ⟨Cu, hCupos, hCu⟩ := two_pow_neg_scale_mul_Q_bound ρ hρ Qc hQcpos
  obtain ⟨KMZ, hKMZpos, hKMZ⟩ :=
    Work.KMTAreas.A7.varEst_of_uniformSigns_of_measurable 2 (by norm_num) R hR
  set Kc : ℝ := (1 + 2 * (4 * Ck)) * M * (2 * (1 + 2 * Cu)) with hKcdef
  have hKcpos : 0 < Kc := by
    rw [hKcdef]
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hMnn
    positivity
  refine ⟨KMZ * Kc, mul_pos hKMZpos hKcpos, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 hMsup
  set u : ℕ := Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) with hudef
  by_cases hcore : ∃ n, mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · set m₀ : ℕ := Nat.find hcore with hm₀def
    have hm₀ : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ m₀ := Nat.find_spec hcore
    have hmin : ∀ n, mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → m₀ ≤ n :=
      fun n hn => Nat.find_min' hcore hn
    have hfloor : Monotone fun n => Nat.floor (a n) := monotone_floor_lacunary hΛ ha ha1
    set Q : ℕ := Nat.ceil ((2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))) with hQdef
    have hQb : ∀ q ∈ Work.Analysis.IonescuWainger.iwP ρ l₁, q ≤ Q := by
      intro q hq
      have h := hQcelem l₁ q hq
      have h2 : (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) ≤ ((Q : ℕ) : ℝ) := by
        rw [hQdef]; exact Nat.le_ceil _
      have h3 : (q : ℝ) ≤ (Q : ℝ) := le_trans h h2
      exact_mod_cast h3
    -- the narrowness level
    set k : ℤ := (k₁ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a m₀)) with hkdef
    have hk : (2 : ℝ) ^ k < 1 / 2 := by
      obtain ⟨-, -, hmain⟩ := hm₀
      have hu1 : 1 ≤ Work.KMTAreas.A7.uScale ρ (max k₁ k₂) := one_le_uScale ρ hρ _
      have hlog : (k₁ : ℤ) + 2 * ((Work.KMTAreas.A7.uScale ρ (max k₁ k₂) : ℕ) : ℤ)
          ≤ Work.Analysis.EndVar.logN (Nat.floor (a m₀)) := by
        have htoNat : ((k₁ + 2 * Work.KMTAreas.A7.uScale ρ (max k₁ k₂) : ℕ) : ℤ)
            ≤ Work.Analysis.EndVar.logN (Nat.floor (a m₀)) := by
          have h1 : ((k₁ + 2 * Work.KMTAreas.A7.uScale ρ (max k₁ k₂) : ℕ) : ℤ)
              ≤ (((Work.Analysis.EndVar.logN (Nat.floor (a m₀))).toNat : ℕ) : ℤ) := by
            exact_mod_cast hmain.1
          rwa [Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg _)] at h1
        have hcast : ((k₁ + 2 * Work.KMTAreas.A7.uScale ρ (max k₁ k₂) : ℕ) : ℤ)
            = (k₁ : ℤ) + 2 * ((Work.KMTAreas.A7.uScale ρ (max k₁ k₂) : ℕ) : ℤ) := by
          push_cast; ring
        rwa [hcast] at htoNat
      have h2 : k ≤ (-2 : ℤ) := by
        rw [hkdef]
        have hu : (1 : ℤ) ≤ ((Work.KMTAreas.A7.uScale ρ (max k₁ k₂) : ℕ) : ℤ) := by
          exact_mod_cast hu1
        have h2u : (2 : ℤ) ≤ 2 * ((Work.KMTAreas.A7.uScale ρ (max k₁ k₂) : ℕ) : ℤ) := by
          linarith
        linarith
      calc (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (-2 : ℤ) := zpow_le_zpow_right₀ (by norm_num) h2
        _ = 1 / 4 := by norm_num
        _ < 1 / 2 := by norm_num
    -- the clipped symbol family
    set Φ' : ℕ → ℝ → ℂ := fun n ξ =>
      if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then varphiNtj (Nat.floor (a n)) k₁ j₁ t ξ else 0
      with hΦ'def
    have hΦ'm : ∀ n, Measurable (Φ' n) := by
      intro n
      by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
      · have hfun : Φ' n = varphiNtj (Nat.floor (a n)) k₁ j₁ t := by
          funext ξ; rw [hΦ'def]; simp [h]
        rw [hfun]; exact measurable_varphiNtj _ _ _ _
      · have hfun : Φ' n = 0 := by funext ξ; rw [hΦ'def]; simp [h]
        rw [hfun]; exact measurable_const
    have hΦ'supp : ∀ n ξ, Φ' n ξ ≠ 0 → ξ ∈ Work.Analysis.IonescuWainger.realArc k := by
      intro n ξ hξ
      by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
      · have hval : Φ' n ξ = varphiNtj (Nat.floor (a n)) k₁ j₁ t ξ := by
          rw [hΦ'def]; simp [h]
        have hξ' : varphiNtj (Nat.floor (a n)) k₁ j₁ t ξ ≠ 0 := by rwa [← hval]
        rw [hkdef]
        exact varphiNtj_narrow_core hfloor hm₀ (hmin n h) j₁ t ξ hξ'
      · exact absurd (by rw [hΦ'def]; simp [h]) hξ
    have hΦ'sup : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (ξ : ℝ),
        ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * Φ' n ξ‖ ≤ M := by
      intro U ω ξ
      have hterm : ∀ n, (if ω n then (1 : ℂ) else -1) * Φ' n ξ
          = (if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
              (if ω n then (1 : ℂ) else -1) * varphiNtj (Nat.floor (a n)) k₁ j₁ t ξ else 0) := by
        intro n
        by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n <;> rw [hΦ'def] <;> simp [h]
      have h1 : (∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * Φ' n ξ)
          = ∑ n ∈ U.filter (fun n => mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n),
              (if ω n then (1 : ℂ) else -1) * varphiNtj (Nat.floor (a n)) k₁ j₁ t ξ := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl (fun n _ => hterm n)
      rw [h1]
      exact hMsup _ ω ξ
    -- the composite constant
    set M' : ℝ := (1 + 2 * (2 : ℝ) ^ k * (Q : ℝ) ^ 2) * M
        * (2 * (1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * (Q : ℝ) ^ 2)) with hM'def
    have hM'pos : 0 < M' := by
      rw [hM'def]
      have h1 : (0 : ℝ) < (1 + 2 * (2 : ℝ) ^ k * (Q : ℝ) ^ 2) := by
        have hk0 : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
        nlinarith [sq_nonneg (Q : ℝ)]
      have h2 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hMnn
      have h3 : (0 : ℝ) < (2 * (1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * (Q : ℝ) ^ 2)) := by
        have hz : (0 : ℝ) < (2 : ℝ) ^ (-(u : ℤ)) := zpow_pos (by norm_num) _
        nlinarith [sq_nonneg (Q : ℝ)]
      exact mul_pos (mul_pos h1 h2) h3
    -- the composite uniform-in-signs bound
    have hcomp : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (g : ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            Work.KMTAreas.A7.Tle ρ l₁ (Φ' n) (mdlF ρ u l₁ g) x)
          2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal M' * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
      intro U ω g
      have h := mdlComposite_uniformSigns_le ρ l₁ u k hk Q hQb Φ' hΦ'm hΦ'supp
        M (le_trans zero_le_one hMnn) hΦ'sup U ω g
      simpa only [hM'def] using h
    -- the uniform bounds on the two factors of the composite constant
    have hQceil : ((Q : ℕ) : ℝ)
        ≤ 2 * (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) := by
      rw [hQdef]
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      have h2 := Nat.ceil_lt_add_one
        (show (0 : ℝ) ≤ (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) by positivity)
      linarith
    have hQ2 : ((Q : ℕ) : ℝ) ^ 2
        ≤ 4 * (2 : ℝ) ^ (2 * Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) := by
      have h3 : ((Q : ℕ) : ℝ) ^ 2
          ≤ (2 * (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hQceil 2
      have h4 : (2 * (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))) ^ 2
          = 4 * (2 : ℝ) ^ (2 * Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) := by
        rw [mul_pow]
        have hsq : ((2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))) ^ 2
            = (2 : ℝ) ^ (2 * (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))) := by
          rw [sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1
          ring
        rw [hsq]
        norm_num
        congr 1
        ring
      linarith [h3, h4]
    have hkr : (2 : ℝ) ^ k
        = (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a m₀)) : ℝ)) := by
      rw [← Real.rpow_intCast]
      congr 1
      rw [hkdef]
      push_cast
      ring
    have hkQ : (2 : ℝ) ^ k * ((Q : ℕ) : ℝ) ^ 2 ≤ 4 * Ck := by
      have hkey := hCk (Nat.floor (a m₀)) k₁ k₂ l₁ (max (max l₁ l₂) (max k₁ k₂))
        (le_trans (le_max_left l₁ l₂) (le_max_left (max l₁ l₂) (max k₁ k₂)))
        (le_trans (le_max_left k₁ k₂) (le_max_right (max l₁ l₂) (max k₁ k₂)))
        (le_trans (le_max_right k₁ k₂) (le_max_right (max l₁ l₂) (max k₁ k₂)))
        hm₀.2.1 hm₀.2.2.1
      rw [hkr]
      calc (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a m₀)) : ℝ))
              * ((Q : ℕ) : ℝ) ^ 2
          ≤ (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a m₀)) : ℝ))
              * (4 * (2 : ℝ) ^ (2 * Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))) :=
            mul_le_mul_of_nonneg_left hQ2 (by positivity)
        _ = 4 * (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a m₀)) : ℝ)
              + 2 * Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) := by
            rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            ring
        _ ≤ 4 * Ck := by linarith
    have huQ : (2 : ℝ) ^ (-(u : ℤ)) * ((Q : ℕ) : ℝ) ^ 2 ≤ Cu := by
      have h := hCu l₁ (max (max l₁ l₂) (max k₁ k₂))
        (le_trans (le_max_left l₁ l₂) (le_max_left (max l₁ l₂) (max k₁ k₂)))
      simpa only [hudef, hQdef] using h
    have hM'le : M' ≤ Kc := by
      rw [hM'def, hKcdef]
      have hA : (1 : ℝ) + 2 * (2 : ℝ) ^ k * ((Q : ℕ) : ℝ) ^ 2 ≤ 1 + 2 * (4 * Ck) := by
        linarith [hkQ]
      have hB : 2 * (1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * ((Q : ℕ) : ℝ) ^ 2) ≤ 2 * (1 + 2 * Cu) := by
        linarith [huQ]
      have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hMnn
      exact mul_le_mul (mul_le_mul hA le_rfl hM0.le (by positivity)) hB (by positivity)
        (by positivity)
    have h := hKMZ (fun n g => Work.KMTAreas.A7.Tle ρ l₁ (Φ' n) (mdlF ρ u l₁ g))
      (fun n g => (measurable_of_countable _).aemeasurable) Kc hKcpos.le ?_ f
    · -- rewrite the family
      have hpt : ∀ (x : ℤ) (n : ℕ),
          (if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
              Work.KMTAreas.A7.Tle ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t)
                (mdlF ρ u l₁ f) x else 0)
            = Work.KMTAreas.A7.Tle ρ l₁ (Φ' n) (mdlF ρ u l₁ f) x := by
        intro x n
        by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
        · simp only [h, if_true, hΦ'def]
        · rw [hΦ'def]
          simp only [h, if_false]
          exact congrFun (Work.KMTPlan.A6.Tle_zero_symbol ρ l₁ (mdlF ρ u l₁ f)).symm x
      have hfamily : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
                Work.KMTAreas.A7.Tle ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t)
                  (mdlF ρ u l₁ f) x else 0))
          = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
              (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁ (Φ' n) (mdlF ρ u l₁ f) x) := by
        funext x
        congr 1
        funext n
        exact hpt x n
      rw [hfamily]
      rw [show ENNReal.ofReal 2 = (2 : ENNReal) from by norm_num] at h
      exact h
    · -- the uniform-in-signs hypothesis
      intro U ω g
      by_cases hg : ∃ B : ℝ, ∀ m : ℤ, ‖g m‖ ≤ B
      · have hb := hcomp U ω g
        have hb0 : MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
              Work.KMTAreas.A7.Tle ρ l₁ (Φ' n) (mdlF ρ u l₁ g) x)
              (ENNReal.ofReal 2) MeasureTheory.Measure.count
            ≤ ENNReal.ofReal M' * MeasureTheory.eLpNorm g (ENNReal.ofReal 2)
                MeasureTheory.Measure.count := by
          simpa only [show ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) from by norm_num] using hb
        have hb' : MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
              Work.KMTAreas.A7.Tle ρ l₁ (Φ' n) (mdlF ρ u l₁ g) x)
              (ENNReal.ofReal 2) MeasureTheory.Measure.count
            ≤ ENNReal.ofReal Kc * MeasureTheory.eLpNorm g (ENNReal.ofReal 2)
                MeasureTheory.Measure.count := by
          refine le_trans hb0 ?_
          gcongr
        calc ∫⁻ x : ℤ, ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
              Work.KMTAreas.A7.Tle ρ l₁ (Φ' n) (mdlF ρ u l₁ g) x‖ₑ ^ (2 : ℝ)
              ∂MeasureTheory.Measure.count
            = (MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
                Work.KMTAreas.A7.Tle ρ l₁ (Φ' n) (mdlF ρ u l₁ g) x)
                (ENNReal.ofReal 2) MeasureTheory.Measure.count) ^ (2 : ℝ) := by
                rw [Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow _ (by norm_num)]
          _ ≤ (ENNReal.ofReal Kc * MeasureTheory.eLpNorm g (ENNReal.ofReal 2)
                MeasureTheory.Measure.count) ^ (2 : ℝ) :=
                ENNReal.rpow_le_rpow hb' (by norm_num)
          _ = ENNReal.ofReal (Kc ^ (2 : ℝ)) *
                (MeasureTheory.eLpNorm g (ENNReal.ofReal 2) MeasureTheory.Measure.count) ^ (2 : ℝ) := by
                rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
                  ENNReal.ofReal_rpow_of_nonneg hKcpos.le (by norm_num)]
          _ = ENNReal.ofReal (Kc ^ (2 : ℝ)) *
                ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
                rw [Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow g (by norm_num)]
      · have htop : (∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) = ⊤ := by
          by_contra hne
          have hne2 : (MeasureTheory.eLpNorm g (ENNReal.ofReal 2)
              MeasureTheory.Measure.count) ^ (2 : ℝ) ≠ ⊤ := by
            rwa [← Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow g (by norm_num)]
          have hlt : MeasureTheory.eLpNorm g (ENNReal.ofReal 2) MeasureTheory.Measure.count < ⊤ := by
            rw [lt_top_iff_ne_top]
            intro hcon
            exact hne2 (by rw [hcon]; simp)
          obtain ⟨C, hC⟩ :=
            Work.KMTAreas.A7.eLpNorm_finite_bounded (ENNReal.ofReal 2) (by norm_num) g hlt
          exact hg ⟨C, hC⟩
        rw [htop, ENNReal.mul_top]
        · exact le_top
        · rw [ENNReal.ofReal_ne_zero_iff]
          positivity
  · -- the core is empty: the family vanishes
    have hr1 : (1 : NNReal) ≤ R := le_of_lt (lt_trans (by norm_num) hR)
    have hvn0 : PointwiseErgodicTheorems.variationalNorm R (0 : ℕ → ℂ) = 0 := by
      have h := Submission.PointwiseErgodicTheorems.variationalNorm_smul (r := R) hr1
        (0 : ℂ) (0 : ℕ → ℂ)
      simpa using h
    have hfun : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
            Work.KMTAreas.A7.Tle ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t)
              (mdlF ρ u l₁ f) x else 0)) = fun _ : ℤ => 0 := by
      funext x
      have hz : (fun n : ℕ => if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
            Work.KMTAreas.A7.Tle ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t)
              (mdlF ρ u l₁ f) x else 0) = (0 : ℕ → ℂ) := by
        funext n
        rw [if_neg (fun h => hcore ⟨n, h⟩)]
        rfl
      rw [hz, hvn0]
    rw [hfun]
    simp

/-- **The vanishing case of the linear estimate** (`k₁ ≥ 1`, or `k₁ = 0` with `j₁ ≠ 0`): the
family clipped at the core satisfies the estimate with a constant depending only on
`(ρ, C₀, R, j₁, M)`, where `M` is a sup bound for the signed sums of the modified bumps. -/
theorem mdlVanishingCase
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (C₀ : ℕ) (R : NNReal) (hR : 2 < R) (j₁ : ℤ)
    (a : ℕ → NNReal) (Λ : NNReal) (hΛ : 1 < Λ)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ)
    (M : ℝ) (hMnn : 1 ≤ M)
    (hMsup : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (ξ : ℝ),
      ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * varphiNtj (Nat.floor (a n)) k₁ j₁ t ξ‖ ≤ M) :
    ∃ K : ℝ, 0 < K ∧
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ =>
          if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
            Work.KMTAreas.A7.Tle ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t)
              (mdlF ρ (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f) x
          else 0)) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal K * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  obtain ⟨K, hKpos, hK⟩ := mdlVanishingCaseUnif ρ hρ hρ1 C₀ R hR j₁ M hMnn
  exact ⟨K, hKpos, hK a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 hMsup⟩

/-- `1 ≤ lossWeight 2 ρ l₁ l₂ k₁ k₂`: the loss weight of the target statement is at least one. -/
theorem one_le_lossWeight_two {ρ : ℝ} (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    1 ≤ Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ k₁ k₂ := by
  rw [Work.KMTAreas.A7.lossWeight]
  have h0 : (0 : ℝ) ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
    rw [Work.KMTAreas.A7.lmaxR]
    have hz : (0 : ℤ) ≤ Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
      rw [Work.Analysis.EndVar.lmax]
      omega
    exact_mod_cast hz
  have h1 : (1 : ℝ) ≤ 1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by linarith
  have h2 : (1 : ℝ) ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ (2 : ℝ) :=
    Real.one_le_rpow h1 (by norm_num)
  have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ (2 : ℝ)
        * (2 : ℝ) ^ (2 * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) :=
        mul_le_mul h2 h3 (by norm_num) (le_trans zero_le_one h2)

/-- `ENNReal.ofReal` monotonicity for a real versus `ℝ≥0` constant. -/
theorem ofReal_le_coe_nnreal {K : ℝ} {Kn : NNReal} (h : K ≤ (Kn : ℝ)) :
    ENNReal.ofReal K ≤ (Kn : ENNReal) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal h

/-- Monotonicity of an `ℝ≥0`-constant factor. -/
theorem mul_le_mul_nnreal_of_le {K Kn : NNReal} (h : K ≤ Kn) (A B : ENNReal) :
    (K : ENNReal) * A * B ≤ (Kn : ENNReal) * A * B := by
  have h1 : (K : ENNReal) ≤ (Kn : ENNReal) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast h)
  exact mul_le_mul' (mul_le_mul' h1 le_rfl) le_rfl

/-- **Absorption into the loss weight.**  A bound `‖F‖ ≤ K ‖f‖` with a uniform real constant `K`
implies `‖F‖ ≤ (K' : ℝ≥0) · lossWeight 2 ρ l₁ l₂ k₁ k₂ · ‖f‖` whenever `K ≤ K'` (the loss weight
being `≥ 1`). -/
theorem ofReal_mul_le_nnreal_mul_lossWeight {K : ℝ} {Kn : NNReal} (h : K ≤ (Kn : ℝ))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) (B : ENNReal) :
    ENNReal.ofReal K * B ≤
      (Kn : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ k₁ k₂) * B := by
  have h1 : ENNReal.ofReal K ≤ (Kn : ENNReal) := ofReal_le_coe_nnreal h
  have hlw : (1 : ENNReal) ≤ ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ k₁ k₂) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_lossWeight_two hρ l₁ l₂ k₁ k₂)
  calc ENNReal.ofReal K * B ≤ (Kn : ENNReal) * B := mul_le_mul' h1 le_rfl
    _ = (Kn : ENNReal) * 1 * B := by rw [mul_one]
    _ ≤ (Kn : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ k₁ k₂) * B :=
        mul_le_mul' (mul_le_mul' le_rfl hlw) le_rfl


/-- The modulated bump `varphiNt N k t` is measurable in the frequency variable. -/
theorem measurable_varphiNt_self_local (N k : ℕ) (t : ℝ) :
    Measurable (Work.KMTAreas.A7.varphiNt N k t) := by
  show Measurable (fun ξ : ℝ =>
    Work.KMTAreas.A7.varphiN N k ξ * Work.KMTAreas.A7.ee ((N : ℝ) * t * ξ))
  exact (measurable_varphiN_self N k).mul
    (Complex.continuous_exp.measurable.comp (by fun_prop))

/-- **Narrowness of the difference `φ_{N,t} − φ_N`.**  For `m₀ ≤ n` the difference of the two
bottom-height bumps at the scale `⌊a n⌋` is supported in the arc `[-2^{−Log N_{m₀}}, 2^{−Log N_{m₀}}]`:
both terms are supported in `|ξ| ≤ 2^{−Log N_n}`, and `Log N_{m₀} ≤ Log N_n`. -/
theorem varphiNt_diff_support_local {a : ℕ → NNReal} {m₀ n : ℕ}
    (hfloor : Monotone fun n => Nat.floor (a n)) (hn : m₀ ≤ n) (t : ℝ) :
    ∀ ξ : ℝ, Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
        - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ ≠ 0 →
      ξ ∈ Work.Analysis.IonescuWainger.realArc
        (-(Work.Analysis.EndVar.logN (Nat.floor (a m₀)))) := by
  intro ξ hξ
  have hnm : Nat.floor (a m₀) ≤ Nat.floor (a n) := hfloor hn
  have hlog : Work.Analysis.EndVar.logN (Nat.floor (a m₀))
      ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := Work.Analysis.EndVar.logN_mono hnm
  have hne : Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ ≠ 0
      ∨ Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hξ (by rw [hc.1, hc.2, sub_zero])
  have hsupp : |ξ| ≤ (2 : ℝ) ^ (((0 : ℕ) : ℝ)
      - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ)) := by
    rcases hne with h | h
    · exact Work.KMTAreas.A7.varphiNt_support_le_all 0 (Nat.floor (a n)) t ξ h
    · exact Work.KMTAreas.A7.varphiN_support (Nat.floor (a n)) 0 ξ h
  have hExp : ((0 : ℕ) : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ)
      ≤ ((-(Work.Analysis.EndVar.logN (Nat.floor (a m₀))) : ℤ) : ℝ) := by
    have h1 : (Work.Analysis.EndVar.logN (Nat.floor (a m₀)) : ℝ)
        ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ) := by exact_mod_cast hlog
    push_cast
    linarith
  have hb' : |ξ| ≤ (2 : ℝ) ^ (((-(Work.Analysis.EndVar.logN (Nat.floor (a m₀)))) : ℤ) : ℝ) :=
    hsupp.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp)
  have hb : |ξ| ≤ (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN (Nat.floor (a m₀)))) := by
    rw [← Real.rpow_intCast]
    exact hb'
  rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
  exact ⟨by linarith [(abs_le.mp hb).1], (abs_le.mp hb).2⟩

theorem mdlDiffFamily_local (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ =>
            if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
              Work.KMTAreas.A7.Tle ρ l₁ (fun ξ : ℝ =>
                  Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                    - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)
                (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ
                  (max (max l₁ l₂) (max 0 k₂))) l₁ f) x
            else 0)) 2 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) *
              ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂) *
              MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  classical
  refine ⟨1, one_pos, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨Qc, hQcpos, hQcelem⟩ := Work.Analysis.IonescuWainger.iwP_element_le hρ
  obtain ⟨Ck, hCkpos, hCk⟩ := two_pow_core_bound ρ hρ hρ1 Qc hQcpos
  obtain ⟨Cu, hCupos, hCu⟩ := two_pow_neg_scale_mul_Q_bound ρ hρ Qc hQcpos
  obtain ⟨KMZ, hKMZpos, hKMZ⟩ :=
    Work.KMTAreas.A7.varEst_of_uniformSigns_of_measurable 2 (by norm_num) R hR
  -- the uniform bound `M(Λ)` for the signed sums of the difference family
  set Mof : NNReal → ℝ := fun Λ => if h : 1 < Λ then
      max 1 (Classical.choose (varphiNtDiffSupBound Λ h)) else 1 with hMofdef
  have hMof1 : ∀ Λ : NNReal, 1 ≤ Mof Λ := by
    intro Λ
    simp only [hMofdef]
    split_ifs with h
    · exact le_max_left _ _
    · exact le_rfl
  have hMofsup : ∀ (Λ : NNReal) (hΛ : 1 < Λ) (t : ℝ)
      (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
      ∀ (U : Finset ℕ) (ω : ℕ → Bool) (ξ : ℝ),
      ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
        (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
          - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)‖ ≤ Mof Λ := by
    intro Λ hΛ t ht a ha ha1 U ω ξ
    have hspec :=
      (Classical.choose_spec (varphiNtDiffSupBound Λ hΛ)).2 t ht a ha ha1 U ω ξ
    have heq : Mof Λ = max 1 (Classical.choose (varphiNtDiffSupBound Λ hΛ)) := by
      simp only [hMofdef, dif_pos hΛ]
    rw [heq]
    exact le_trans hspec (le_max_right _ _)
  -- the constant of the target
  set Kf : NNReal → NNReal := fun Λ =>
      ⟨max 1 (KMZ * ((1 + 2 * (4 * Ck)) * Mof Λ * (2 * (1 + 2 * Cu)))),
        le_trans zero_le_one (le_max_left _ _)⟩ with hKfdef
  refine ⟨Kf, ?_⟩
  intro a Λ l₁ l₂ k₂ t f hΛ ha ha1 ht
  have hKfval : (Kf Λ : ENNReal) = ENNReal.ofReal (max 1 (KMZ *
      ((1 + 2 * (4 * Ck)) * Mof Λ * (2 * (1 + 2 * Cu))))) := by
    rw [ENNReal.coe_nnreal_eq]
    congr 1
  set Q : ℕ := Nat.ceil ((2 : ℝ) ^ (Qc * 2 ^ (ρ * (l₁ : ℝ)))) with hQdef
  have hQb : ∀ q ∈ Work.Analysis.IonescuWainger.iwP ρ l₁, q ≤ Q := by
    intro q hq
    have h := hQcelem l₁ q hq
    have h2 : (2 : ℝ) ^ (Qc * 2 ^ (ρ * (l₁ : ℝ))) ≤ ((Q : ℕ) : ℝ) := by
      rw [hQdef]; exact Nat.le_ceil _
    exact_mod_cast le_trans h h2
  set u : ℕ := Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂)) with hudef
  set Kc : ℝ := (1 + 2 * (4 * Ck)) * Mof Λ * (2 * (1 + 2 * Cu)) with hKcdef
  have hKcpos : 0 < Kc := by
    rw [hKcdef]
    have h1 : (0 : ℝ) < 1 + 2 * (4 * Ck) := by linarith
    have h2 : (0 : ℝ) < 2 * (1 + 2 * Cu) := by linarith
    have h3 : (0 : ℝ) < Mof Λ := lt_of_lt_of_le zero_lt_one (hMof1 Λ)
    exact mul_pos (mul_pos h1 h3) h2
  have hgoal : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ =>
          if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
            Work.KMTAreas.A7.Tle ρ l₁ (fun ξ : ℝ =>
                Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                  - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)
              (Work.KMTPlan.A6.mdlF ρ u l₁ f) x
          else 0)) 2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (KMZ * Kc) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    by_cases hcore : ∃ n, mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
    · -- the core is nonempty: the narrowness level is the scale of the first core index
      set m₀ : ℕ := Nat.find hcore with hm₀def
      have hm₀ : mdlCore ρ C₀ a l₁ l₂ 0 k₂ m₀ := Nat.find_spec hcore
      have hmin : ∀ n, mdlCore ρ C₀ a l₁ l₂ 0 k₂ n → m₀ ≤ n :=
        fun n hn => Nat.find_min' hcore hn
      have hfloor : Monotone fun n => Nat.floor (a n) := monotone_floor_lacunary hΛ ha ha1
      set k : ℤ := - (Work.Analysis.EndVar.logN (Nat.floor (a m₀))) with hkdef
      have hk2 : k ≤ (-2 : ℤ) := by
        obtain ⟨-, -, hmain⟩ := hm₀
        have hu1 : 1 ≤ Work.KMTAreas.A7.uScale ρ (max 0 k₂) := one_le_uScale ρ hρ _
        have hlog : (2 : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a m₀)) := by
          have htoNat : ((0 + 2 * Work.KMTAreas.A7.uScale ρ (max 0 k₂) : ℕ) : ℤ)
              ≤ Work.Analysis.EndVar.logN (Nat.floor (a m₀)) := by
            have h1 : ((0 + 2 * Work.KMTAreas.A7.uScale ρ (max 0 k₂) : ℕ) : ℤ)
                ≤ (((Work.Analysis.EndVar.logN (Nat.floor (a m₀))).toNat : ℕ) : ℤ) := by
              exact_mod_cast hmain.1
            rwa [Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg _)] at h1
          have hcastL : ((0 + 2 * Work.KMTAreas.A7.uScale ρ (max 0 k₂) : ℕ) : ℤ)
              = (2 : ℤ) * ((Work.KMTAreas.A7.uScale ρ (max 0 k₂) : ℕ) : ℤ) := by
            push_cast; ring
          rw [hcastL] at htoNat
          have hu1z : (1 : ℤ) ≤ ((Work.KMTAreas.A7.uScale ρ (max 0 k₂) : ℕ) : ℤ) := by
            exact_mod_cast hu1
          linarith
        rw [hkdef]
        linarith
      have hk : (2 : ℝ) ^ k < 1 / 2 := by
        calc (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (-2 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hk2
          _ = 1 / 4 := by norm_num
          _ < 1 / 2 := by norm_num
      -- the clipped difference family
      set Φ : ℕ → ℝ → ℂ := fun n ξ =>
          if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
            Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
              - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ
          else 0 with hΦdef
      have hΦm : ∀ n, Measurable (Φ n) := by
        intro n
        by_cases h : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
        · have hfun : Φ n = fun ξ : ℝ =>
              Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ := by
            funext ξ; rw [hΦdef]; simp [h]
          rw [hfun]
          exact (measurable_varphiNt_self_local _ _ _).sub (measurable_varphiN_self _ _)
        · have hfun : Φ n = 0 := by funext ξ; rw [hΦdef]; simp [h]
          rw [hfun]; exact measurable_const
      have hΦsupp : ∀ n ξ, Φ n ξ ≠ 0 → ξ ∈ Work.Analysis.IonescuWainger.realArc k := by
        intro n ξ hξ
        have hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n := by
          by_contra h
          exact hξ (by rw [hΦdef]; simp [h])
        have hneq : Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
            - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ ≠ 0 := by
          intro h0
          exact hξ (by rw [hΦdef]; simp [hc, h0])
        rw [hkdef]
        exact varphiNt_diff_support_local hfloor (hmin n hc) t ξ hneq
      have hΦsup : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (ξ : ℝ),
          ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * Φ n ξ‖ ≤ Mof Λ := by
        intro U ω ξ
        have hterm : ∀ n, (if ω n then (1 : ℂ) else -1) * Φ n ξ
            = (if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                (if ω n then (1 : ℂ) else -1) *
                  (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                    - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ) else 0) := by
          intro n
          by_cases h : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n <;>
            rw [hΦdef] <;> simp [h]
        have h1 : (∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * Φ n ξ)
            = ∑ n ∈ U.filter (fun n => Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n),
                (if ω n then (1 : ℂ) else -1) *
                  (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                    - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ) := by
          rw [Finset.sum_filter]
          exact Finset.sum_congr rfl (fun n _ => hterm n)
        rw [h1]
        exact hMofsup Λ hΛ t ht a ha ha1 _ ω ξ
      -- the uniform bounds on the two factors of the composite constant
      have hkQ : (2 : ℝ) ^ k * ((Q : ℕ) : ℝ) ^ 2 ≤ 4 * Ck := by
        have hQ2 : ((Q : ℕ) : ℝ) ^ 2
            ≤ 4 * (2 : ℝ) ^ (2 * Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) := by
          have hQceil : ((Q : ℕ) : ℝ)
              ≤ 2 * (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) := by
            rw [hQdef]
            have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) :=
              Real.one_le_rpow (by norm_num) (by positivity)
            have h2 := Nat.ceil_lt_add_one
              (show (0 : ℝ) ≤ (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) by positivity)
            linarith
          have h3 : ((Q : ℕ) : ℝ) ^ 2
              ≤ (2 * (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hQceil 2
          have h4 : (2 * (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))) ^ 2
              = 4 * (2 : ℝ) ^ (2 * Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) := by
            rw [mul_pow]
            have hsq : ((2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))) ^ 2
                = (2 : ℝ) ^ (2 * (Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))) := by
              rw [sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
              congr 1; ring
            rw [hsq]; norm_num; congr 1; ring
          linarith [h3, h4]
        have hkr : (2 : ℝ) ^ k
            = (2 : ℝ) ^ (((0 : ℕ) : ℝ)
              - (Work.Analysis.EndVar.logN (Nat.floor (a m₀)) : ℝ)) := by
          rw [← Real.rpow_intCast]
          congr 1
          rw [hkdef]
          push_cast
          ring
        have hkey := hCk (Nat.floor (a m₀)) 0 k₂ l₁ (max (max l₁ l₂) (max 0 k₂))
          (le_trans (le_max_left l₁ l₂) (le_max_left (max l₁ l₂) (max 0 k₂)))
          (Nat.zero_le _)
          (le_trans (le_max_right 0 k₂) (le_max_right (max l₁ l₂) (max 0 k₂)))
          hm₀.2.1 hm₀.2.2.1
        rw [hkr]
        calc (2 : ℝ) ^ (((0 : ℕ) : ℝ)
                - (Work.Analysis.EndVar.logN (Nat.floor (a m₀)) : ℝ))
              * ((Q : ℕ) : ℝ) ^ 2
            ≤ (2 : ℝ) ^ (((0 : ℕ) : ℝ)
                - (Work.Analysis.EndVar.logN (Nat.floor (a m₀)) : ℝ))
              * (4 * (2 : ℝ) ^ (2 * Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))) :=
              mul_le_mul_of_nonneg_left hQ2 (by positivity)
          _ = 4 * (2 : ℝ) ^ (((0 : ℕ) : ℝ)
                - (Work.Analysis.EndVar.logN (Nat.floor (a m₀)) : ℝ)
                + 2 * Qc * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) := by
              rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
              ring
          _ ≤ 4 * Ck := by linarith [hkey]
      have huQ : (2 : ℝ) ^ (-(u : ℤ)) * ((Q : ℕ) : ℝ) ^ 2 ≤ Cu := by
        have h := hCu l₁ (max (max l₁ l₂) (max 0 k₂))
          (le_trans (le_max_left l₁ l₂) (le_max_left (max l₁ l₂) (max 0 k₂)))
        simpa only [hudef, hQdef] using h
      -- the composite constant
      set M' : ℝ := (1 + 2 * (2 : ℝ) ^ k * (Q : ℝ) ^ 2) * Mof Λ
          * (2 * (1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * (Q : ℝ) ^ 2)) with hM'def
      have hcomp : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (g : ℤ → ℂ),
          MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
              Work.KMTAreas.A7.Tle ρ l₁ (Φ n) (Work.KMTPlan.A6.mdlF ρ u l₁ g) x)
            2 MeasureTheory.Measure.count
            ≤ ENNReal.ofReal M' * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
        intro U ω g
        have h := mdlComposite_uniformSigns_le ρ l₁ u k hk Q hQb Φ hΦm hΦsupp
          (Mof Λ) (le_trans zero_le_one (hMof1 Λ)) hΦsup U ω g
        simpa only [hM'def] using h
      have hM'le : M' ≤ Kc := by
        rw [hM'def, hKcdef]
        have hA : 1 + 2 * (2 : ℝ) ^ k * ((Q : ℕ) : ℝ) ^ 2 ≤ 1 + 2 * (4 * Ck) := by
          nlinarith [hkQ]
        have hB : 2 * (1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * ((Q : ℕ) : ℝ) ^ 2)
            ≤ 2 * (1 + 2 * Cu) := by
          nlinarith [huQ]
        have hM0 : 0 < Mof Λ := lt_of_lt_of_le zero_lt_one (hMof1 Λ)
        exact mul_le_mul (mul_le_mul hA le_rfl hM0.le (by positivity)) hB
          (by positivity) (by positivity)
      have hcell := hKMZ (fun n g => Work.KMTAreas.A7.Tle ρ l₁ (Φ n)
          (Work.KMTPlan.A6.mdlF ρ u l₁ g))
        (fun n g => (measurable_of_countable _).aemeasurable) Kc hKcpos.le ?_ f
      · -- rewrite the family and conclude
        have hpt : ∀ (x : ℤ) (n : ℕ),
            (if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                Work.KMTAreas.A7.Tle ρ l₁ (fun ξ : ℝ =>
                    Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                      - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)
                  (Work.KMTPlan.A6.mdlF ρ u l₁ f) x else 0)
              = Work.KMTAreas.A7.Tle ρ l₁ (Φ n) (Work.KMTPlan.A6.mdlF ρ u l₁ f) x := by
          intro x n
          by_cases h : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
          · simp only [h, if_true, hΦdef]
          · rw [hΦdef]
            simp only [h, if_false]
            exact congrFun (Tle_zero_symbol ρ l₁ (Work.KMTPlan.A6.mdlF ρ u l₁ f)).symm x
        have hfamily : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
              (fun n : ℕ =>
                if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                  Work.KMTAreas.A7.Tle ρ l₁ (fun ξ : ℝ =>
                      Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                        - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)
                    (Work.KMTPlan.A6.mdlF ρ u l₁ f) x else 0))
            = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
                (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁ (Φ n)
                  (Work.KMTPlan.A6.mdlF ρ u l₁ f) x) := by
          funext x
          congr 1
          funext n
          exact hpt x n
        rw [hfamily]
        rw [show ENNReal.ofReal 2 = (2 : ENNReal) from by norm_num] at hcell
        exact hcell
      · -- the uniform-in-signs lintegral bound
        intro U ω g
        by_cases hg : ∃ B : ℝ, ∀ m : ℤ, ‖g m‖ ≤ B
        · have hb := hcomp U ω g
          have hb0 : MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U,
                (if ω n then (1 : ℂ) else -1) *
                  Work.KMTAreas.A7.Tle ρ l₁ (Φ n) (Work.KMTPlan.A6.mdlF ρ u l₁ g) x)
                (ENNReal.ofReal 2) MeasureTheory.Measure.count
              ≤ ENNReal.ofReal M' * MeasureTheory.eLpNorm g (ENNReal.ofReal 2)
                  MeasureTheory.Measure.count := by
            simpa only [show ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) from by norm_num] using hb
          have hb' : MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U,
                (if ω n then (1 : ℂ) else -1) *
                  Work.KMTAreas.A7.Tle ρ l₁ (Φ n) (Work.KMTPlan.A6.mdlF ρ u l₁ g) x)
                (ENNReal.ofReal 2) MeasureTheory.Measure.count
              ≤ ENNReal.ofReal Kc * MeasureTheory.eLpNorm g (ENNReal.ofReal 2)
                  MeasureTheory.Measure.count :=
            le_trans hb0 (mul_le_mul' (ENNReal.ofReal_le_ofReal hM'le) le_rfl)
          calc ∫⁻ x : ℤ, ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
                Work.KMTAreas.A7.Tle ρ l₁ (Φ n) (Work.KMTPlan.A6.mdlF ρ u l₁ g) x‖ₑ ^ (2 : ℝ)
                ∂MeasureTheory.Measure.count
              = (MeasureTheory.eLpNorm (fun x : ℤ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
                  Work.KMTAreas.A7.Tle ρ l₁ (Φ n) (Work.KMTPlan.A6.mdlF ρ u l₁ g) x)
                  (ENNReal.ofReal 2) MeasureTheory.Measure.count) ^ (2 : ℝ) := by
                  rw [Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow _
                    (by norm_num)]
            _ ≤ (ENNReal.ofReal Kc * MeasureTheory.eLpNorm g (ENNReal.ofReal 2)
                  MeasureTheory.Measure.count) ^ (2 : ℝ) :=
                  ENNReal.rpow_le_rpow hb' (by norm_num)
            _ = ENNReal.ofReal (Kc ^ (2 : ℝ)) *
                  (MeasureTheory.eLpNorm g (ENNReal.ofReal 2)
                    MeasureTheory.Measure.count) ^ (2 : ℝ) := by
                  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
                    ENNReal.ofReal_rpow_of_nonneg hKcpos.le (by norm_num)]
            _ = ENNReal.ofReal (Kc ^ (2 : ℝ)) *
                  ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
                  rw [Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow g
                    (by norm_num)]
        · -- `g` is unbounded: both sides are `⊤`
          have htop : (∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) = ⊤ := by
            by_contra hne
            have hne2 : (MeasureTheory.eLpNorm g (ENNReal.ofReal 2)
                MeasureTheory.Measure.count) ^ (2 : ℝ) ≠ ⊤ := by
              rwa [← Work.BourgainPlan.Maximal.lintegral_enorm_rpow_eq_eLpNorm_rpow g
                (by norm_num)]
            have hlt : MeasureTheory.eLpNorm g (ENNReal.ofReal 2)
                MeasureTheory.Measure.count < ⊤ := by
              rw [lt_top_iff_ne_top]
              intro hcon
              exact hne2 (by rw [hcon]; simp)
            obtain ⟨C, hC⟩ :=
              Work.KMTAreas.A7.eLpNorm_finite_bounded (ENNReal.ofReal 2) (by norm_num) g hlt
            exact hg ⟨C, hC⟩
          rw [htop, ENNReal.mul_top]
          · exact le_top
          · rw [ENNReal.ofReal_ne_zero_iff]
            positivity
    · -- the core is empty: the family vanishes identically
      have hr1 : (1 : NNReal) ≤ R := le_of_lt (lt_trans (by norm_num) hR)
      have hvn0 : PointwiseErgodicTheorems.variationalNorm R (0 : ℕ → ℂ) = 0 := by
        have h := Submission.PointwiseErgodicTheorems.variationalNorm_smul (r := R) hr1
          (0 : ℂ) (0 : ℕ → ℂ)
        simpa using h
      have hfun : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ =>
              if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                Work.KMTAreas.A7.Tle ρ l₁ (fun ξ : ℝ =>
                    Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                      - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)
                  (Work.KMTPlan.A6.mdlF ρ u l₁ f) x else 0))
          = fun _ : ℤ => 0 := by
        funext x
        have hz : (fun n : ℕ =>
              if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                Work.KMTAreas.A7.Tle ρ l₁ (fun ξ : ℝ =>
                    Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                      - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)
                  (Work.KMTPlan.A6.mdlF ρ u l₁ f) x else 0) = (0 : ℕ → ℂ) := by
          funext n
          rw [if_neg (fun h => hcore ⟨n, h⟩)]
          rfl
        rw [hz, hvn0]
      rw [hfun]
      simp
  -- the loss weight is absorbed into the constant
  have hKB_le : ENNReal.ofReal (KMZ * Kc) ≤ (Kf Λ : ENNReal) := by
    rw [hKfval, hKcdef]
    exact ENNReal.ofReal_le_ofReal (le_max_right 1 _)
  have hloss : (1 : ENNReal)
      ≤ ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_lossWeight_two hρ.le l₁ l₂ 0 k₂)
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ =>
          if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
            Work.KMTAreas.A7.Tle ρ l₁ (fun ξ : ℝ =>
                Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                  - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)
              (Work.KMTPlan.A6.mdlF ρ u l₁ f) x
          else 0)) 2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (KMZ * Kc) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
        hgoal
    _ ≤ (Kf Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
        mul_le_mul' hKB_le le_rfl
    _ ≤ (Kf Λ : ENNReal) *
          ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂) *
          MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        calc (Kf Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            = (Kf Λ : ENNReal) * 1 * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
              rw [mul_one]
          _ ≤ (Kf Λ : ENNReal) *
                ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂) *
                MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
              mul_le_mul' (mul_le_mul' le_rfl hloss) le_rfl

theorem mdlLowpassCaseZero_local (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₂ : ℕ) (f : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ =>
            if Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ 0 k₂ n then
              Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0)
                (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ
                  (max (max 0 l₂) (max 0 k₂))) 0 f) x
            else 0)) 2 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) *
              ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ 0 l₂ 0 k₂) *
              MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  classical
  refine ⟨1, by norm_num, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨Cproj, hCprojpos, hCproj⟩ := MdlFZeroTwoLe ρ hρ hρ1
  have hr1 : (1 : NNReal) ≤ R := le_of_lt (lt_trans (by norm_num) hR)
  -- the absolute constant of the unmodulated low-pass lacunary estimate, made total in `Λ`
  set LoC : NNReal → NNReal := fun Λ => if h : 1 < Λ then
    Classical.choose (Work.KMTAreas.A7LoLin.lowpass0 ρ hρ hρ1 2 (by norm_num) (by norm_num)
      R hR Λ h) else 0 with hLoCdef
  have hLoC : ∀ (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal)
      (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n) (g : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
            (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) g x))
        2 MeasureTheory.Measure.count
        ≤ (LoC Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    intro Λ hΛ a ha ha1 g
    have hspec := Classical.choose_spec (Work.KMTAreas.A7LoLin.lowpass0 ρ hρ hρ1 2 (by norm_num)
      (by norm_num) R hR Λ hΛ)
    have heq : LoC Λ = Classical.choose (Work.KMTAreas.A7LoLin.lowpass0 ρ hρ hρ1 2 (by norm_num)
        (by norm_num) R hR Λ hΛ) := by rw [hLoCdef]; simp only [dif_pos hΛ]
    rw [heq]
    exact hspec a ha ha1 g
  set CK : NNReal → NNReal := fun Λ => ⟨3 * (LoC Λ : ℝ) * Cproj + 1, by
    have h1 : (0 : ℝ) ≤ (LoC Λ : ℝ) := (LoC Λ).2
    nlinarith [hCprojpos]⟩ with hCKdef
  refine ⟨CK, ?_⟩
  intro a Λ l₂ k₂ f hΛ ha ha1
  set g : ℤ → ℂ := mdlF ρ (Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max 0 k₂))) 0 f with hg
  set E : ℕ → ℤ → ℂ := fun n x => if mdlCore ρ C₀ a 0 l₂ 0 k₂ n then
      Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) g x else 0
    with hE
  change MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
      (fun n : ℕ => E n x)) 2 MeasureTheory.Measure.count
    ≤ (CK Λ : ENNReal) *
        ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ 0 l₂ 0 k₂) *
        MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
  have hgL : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal Cproj * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    rw [hg]
    exact hCproj (Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max 0 k₂))) f
  have hCK : (CK Λ : ENNReal) = ENNReal.ofReal (3 * (LoC Λ : ℝ) * Cproj + 1) :=
    ENNReal.coe_nnreal_eq (CK Λ)
  have harith : (3 : ENNReal) * (LoC Λ : ENNReal) * ENNReal.ofReal Cproj
      = ENNReal.ofReal (3 * (LoC Λ : ℝ) * Cproj) := by
    rw [ENNReal.coe_nnreal_eq (LoC Λ),
      show (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) from (ENNReal.ofReal_ofNat 3).symm]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 3 * (LoC Λ : ℝ))]
  have hconst : (3 : ENNReal) * (LoC Λ : ENNReal) * ENNReal.ofReal Cproj
      ≤ (CK Λ : ENNReal) := by
    rw [harith, hCK]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hloss : (1 : ENNReal)
      ≤ ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ 0 l₂ 0 k₂) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal
      (Work.KMTAreas.A7Hi.one_le_lossWeight_of_nonneg 2 ρ (by norm_num) hρ.le 0 l₂ 0 k₂)
  have hfin : ∀ X : ENNReal, (CK Λ : ENNReal) * X
      ≤ (CK Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ 0 l₂ 0 k₂) * X := by
    intro X
    calc (CK Λ : ENNReal) * X = (CK Λ : ENNReal) * 1 * X := by rw [mul_one]
      _ ≤ (CK Λ : ENNReal)
            * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ 0 l₂ 0 k₂) * X :=
          mul_le_mul' (mul_le_mul' le_rfl hloss) le_rfl
  by_cases hne : ∃ n : ℕ, mdlCore ρ C₀ a 0 l₂ 0 k₂ n
  · set m₀ : ℕ := Nat.find hne with hm₀def
    have hm₀ : mdlCore ρ C₀ a 0 l₂ 0 k₂ m₀ := Nat.find_spec hne
    have hmin : ∀ n, mdlCore ρ C₀ a 0 l₂ 0 k₂ n → m₀ ≤ n := fun n hn => Nat.find_min' hne hn
    have hfloor : Monotone fun n => Nat.floor (a n) := monotone_floor_lacunary hΛ ha ha1
    have htail : ∀ n, m₀ ≤ n → mdlCore ρ C₀ a 0 l₂ 0 k₂ n :=
      fun n hn => mdlCore_of_le hfloor hn hm₀
    set E' : ℕ → ℤ → ℂ := fun k x => Work.KMTAreas.A7.Tle ρ 0
        (Work.KMTAreas.A7.varphiN (Nat.floor (a (k + m₀))) 0) g x with hE'def
    have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ => E n x)
        ≤ 3 * PointwiseErgodicTheorems.variationalNorm R (fun k : ℕ => E' k x) := by
      intro x
      have hfun : (fun n : ℕ => E n x)
          = fun n : ℕ => if n < m₀ then 0 else (fun k : ℕ => E' k x) (n - m₀) := by
        funext n
        by_cases hn : n < m₀
        · have hnc : ¬ mdlCore ρ C₀ a 0 l₂ 0 k₂ n :=
            fun hc => absurd (hmin n hc) (not_le.mpr hn)
          rw [hE]
          simp only [if_neg hnc, if_pos hn]
        · have hn' : m₀ ≤ n := le_of_not_gt hn
          rw [hE]
          simp only [if_pos (htail n hn'), if_neg hn]
          have hsub : n - m₀ + m₀ = n := Nat.sub_add_cancel hn'
          show Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) g x
            = Work.KMTAreas.A7.Tle ρ 0
                (Work.KMTAreas.A7.varphiN (Nat.floor (a (n - m₀ + m₀))) 0) g x
          rw [hsub]
      rw [hfun]
      exact Submission.PointwiseErgodicTheorems.variationalNorm_prependZeros_le hr1 m₀
        (fun k : ℕ => E' k x)
    have hstep1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => E n x)) 2 MeasureTheory.Measure.count
        ≤ 3 * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun k : ℕ => E' k x)) 2 MeasureTheory.Measure.count := by
      refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
        (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ => E n x))
        (g := fun x : ℤ => (3 : ENNReal) * PointwiseErgodicTheorems.variationalNorm R
          (fun k : ℕ => E' k x)) hpt).trans ?_
      exact MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hf := by pw_aesm)
        (f := fun x : ℤ => (3 : ENNReal) *
          PointwiseErgodicTheorems.variationalNorm R (fun k : ℕ => E' k x))
        (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R (fun k : ℕ => E' k x))
        (c := 3) (Filter.Eventually.of_forall (fun x => by
          rw [enorm_eq_self, enorm_eq_self]
          exact le_rfl)) 2
    have ha' : PointwiseErgodicTheorems.Lacunary Λ (fun n : ℕ => a (n + m₀)) := by
      intro n
      have hh := ha (n + m₀)
      simpa [Nat.add_right_comm] using hh
    have ha1' : ∀ n : ℕ, 1 ≤ (fun n : ℕ => a (n + m₀)) n := fun n => ha1 (n + m₀)
    have hstep2 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun k : ℕ => E' k x)) 2 MeasureTheory.Measure.count
        ≤ (LoC Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
      have h := hLoC Λ hΛ (fun n : ℕ => a (n + m₀)) ha' ha1' g
      simpa [hE'def] using h
    calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => E n x)) 2 MeasureTheory.Measure.count
        ≤ 3 * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun k : ℕ => E' k x)) 2 MeasureTheory.Measure.count := hstep1
      _ ≤ 3 * ((LoC Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) :=
          mul_le_mul' le_rfl hstep2
      _ ≤ 3 * ((LoC Λ : ENNReal) * (ENNReal.ofReal Cproj *
            MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hgL)
      _ = ((3 : ENNReal) * (LoC Λ : ENNReal) * ENNReal.ofReal Cproj) *
            MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by ring
      _ ≤ (CK Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
          mul_le_mul' hconst le_rfl
      _ ≤ (CK Λ : ENNReal) *
            ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ 0 l₂ 0 k₂) *
            MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := hfin _
  · have hzero : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ => E n x))
        = 0 := by
      funext x
      have hthis : (fun n : ℕ => E n x) = (0 : ℕ → ℂ) := by
        funext n
        rw [hE]
        simp only [if_neg (fun hc => hne ⟨n, hc⟩), Pi.zero_apply]
      rw [hthis]
      have hvn0 : PointwiseErgodicTheorems.variationalNorm R (0 : ℕ → ℂ) = 0 := by
        have h := Submission.PointwiseErgodicTheorems.variationalNorm_smul (r := R) hr1
          (0 : ℂ) (0 : ℕ → ℂ)
        simpa using h
      exact hvn0
    rw [hzero]
    simp


private lemma mdlOfReal_mul_right_assoc {a b : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b) (X : ℝ≥0∞) :
    ENNReal.ofReal a * (ENNReal.ofReal b * X) = ENNReal.ofReal (a * b) * X := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul ha]

/-! ## A clash-free copy of the `supPart ≤ chainPart` brick for the low-pass walk

`Work.KMTAreas.A7Hi.nestingClean` and `Work.KMTAreas.A7Hi.AnnuliOrthogonal` both declare
`Work.KMTAreas.A7Hi.circM`, so no module may import both.  The tree's `supPart_lpf_le_chainPart`
(for the low-pass walk) lives in `Work.KMTAreas.A7MixedG.chainGLCrux`, which brings the
`nestingClean` side; the chain/square-function crux
(`Submission.Work.KMTAreas.A7HiRep.chainPartSqFunLeTwo`) brings the `AnnuliOrthogonal` side.  The
four lemmas below are *verbatim copies* (renamed) of
`Work.KMTAreas.A7MixedG.{chainPart_ge_norm_sub, chainPart_ge_supPart_of_tendsto_zero,
lpf_tendsto_zero, supPart_lpf_le_chainPart}` from
`Submission/Work/KMTAreas/A7MixedG/chainGLCrux.lean`, so that this file can use the brick *without*
importing `chainGLCrux` — and hence can import the crux module. -/

/-- **The two-term chain bound**: for `2 ≤ r` the two-term chain `(n, mm)` is admissible, so
`‖a mm - a n‖ ≤ chainPart r a` (copy of `Work.KMTAreas.A7MixedG.chainPart_ge_norm_sub`). -/
theorem chainPartGeNormSub_local {r : NNReal} (hr : 2 ≤ r) (a : ℕ → ℂ) {n mm : ℕ} (hnm : n ≤ mm) :
    ENNReal.ofReal ‖a mm - a n‖ ≤ Work.KMTAreas.A7Hi.chainPart r a := by
  have hmono : Monotone (fun i : ℕ => if i = 0 then n else mm) := by
    intro i j hij
    by_cases hi : i = 0
    · subst hi
      by_cases hj : j = 0
      · simp [hj]
      · simp only [hj, ↓reduceIte]
        exact hnm
    · have hj : j ≠ 0 := by omega
      simp [hi, hj]
  have h1 : ENNReal.ofReal ‖WithLp.toLp r (fun _ : Fin 1 => a mm - a n)‖
      ≤ Work.KMTAreas.A7Hi.chainPart r a := by
    have hvec : (fun i : Fin 1 => a ((fun i : ℕ => if i = 0 then n else mm) (i + 1))
        - a ((fun i : ℕ => if i = 0 then n else mm) i))
        = (fun _ : Fin 1 => a mm - a n) := by
      funext i
      simp
    unfold Work.KMTAreas.A7Hi.chainPart
    refine le_iSup_of_le 1 (le_iSup_of_le (fun i : ℕ => if i = 0 then n else mm)
      (le_iSup_of_le hmono ?_))
    rw [hvec]
  have hy : (r : ℝ) ≠ 0 := by
    have h2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  rw [Work.KMTAreas.A7.ofReal_norm_toLp r hr 1 (fun _ : Fin 1 => a mm - a n),
    Fin.sum_univ_one, one_div, ENNReal.rpow_rpow_inv hy, ← ofReal_norm] at h1
  exact h1

/-- **`supPart ≤ chainPart` for a walk tending to `0`** (copy of
`Work.KMTAreas.A7MixedG.chainPart_ge_supPart_of_tendsto_zero`). -/
theorem chainPartGeSupPart_local {r : NNReal} (hr : 2 ≤ r) (a : ℕ → ℂ)
    (ha : Filter.Tendsto a Filter.atTop (nhds 0)) :
    Work.KMTAreas.A7Hi.supPart r a ≤ Work.KMTAreas.A7Hi.chainPart r a := by
  rw [Work.KMTAreas.A7Hi.supPart]
  refine iSup_le fun n => ?_
  by_cases htop : Work.KMTAreas.A7Hi.chainPart r a = ⊤
  · rw [htop]; exact le_top
  · have hcof : ENNReal.ofReal (Work.KMTAreas.A7Hi.chainPart r a).toReal
        = Work.KMTAreas.A7Hi.chainPart r a := ENNReal.ofReal_toReal htop
    have hle : ∀ mm : ℕ, n ≤ mm → ‖a mm - a n‖
        ≤ (Work.KMTAreas.A7Hi.chainPart r a).toReal := by
      intro mm hnm
      have h := chainPartGeNormSub_local hr a hnm
      rw [← hcof] at h
      exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h
    have htend : Filter.Tendsto (fun k : ℕ => a (k + n)) Filter.atTop (nhds 0) :=
      ha.comp (Filter.tendsto_add_atTop_nat n)
    have hcst : Filter.Tendsto (fun _ : ℕ => a n) Filter.atTop (nhds (a n)) :=
      tendsto_const_nhds
    have hone : Filter.Tendsto (fun k : ℕ => ‖a (k + n) - a n‖) Filter.atTop
        (nhds ‖a n‖) := by
      have h := (htend.sub hcst).norm
      simpa using h
    have hbdd : ∀ᶠ k : ℕ in Filter.atTop, ‖a (k + n) - a n‖ ∈ Set.Iic
        (Work.KMTAreas.A7Hi.chainPart r a).toReal :=
      Filter.Eventually.of_forall fun k => hle (k + n) (by omega)
    have hmain : ‖a n‖ ≤ (Work.KMTAreas.A7Hi.chainPart r a).toReal :=
      isClosed_Iic.mem_of_tendsto hone hbdd
    rw [← ofReal_norm, ← hcof]
    exact ENNReal.ofReal_le_ofReal hmain

/-! ## The `p = 2` low-pass variational estimate from the **repaired** (`MemLp`) chain crux

The workspace's canonical form of the chain/square-function crux carries the hypothesis
`MemLp f 2` on the input (`Work.KMTAreas.A7HiRep.chainPartSqFunLeTwo` at `p = 2`); the
`MemLp`-free form is *suspect* (`NOTES_A7HiRep_chainPartSqFunPos_SESSION.md` §S5.6–S5.7: it can
fail only if some `f` has `chainPart = ⊤` at a single point while `sqFun ∈ ℓᵖ`, and the tree's
policy is "do not add another copy of the unrepaired statement").  The assembly below therefore
consumes the *repaired* form: it is `Work.KMTPlan.A6.lowpassVarGTwo_of_chainCrux` with the chain
hypothesis restricted to `MemLp f 2`, the application of that hypothesis moved *inside* the
`Summable (‖f‖²)` branch (exactly where the tree's proof uses it), and the `¬Summable` branch
discharged by `eLpNorm f 2 = ⊤` as in the tree (`le_top`). -/

/-- `MemLp · 2` on `(ℤ, count)` from `∑ ‖g n‖² < ∞`.  A local copy of
`Work.KMTAreas.A7HiRep.memLp_two_of_summable_sq'`, kept so that this file does not have to import
`AnnuliOrthogonal`-carrying modules (that lemma's module declares `Work.KMTAreas.A7Hi.circM`, which
clashes with `Work.KMTAreas.A7Hi.nestingClean`; see the session note §4 — the clash was removed from
this file, and the copy is kept so that the chain crux module can be imported without it). -/
theorem memLp_two_of_summable_sq_local {g : ℤ → ℂ}
    (h : Summable fun n : ℤ => ‖g n‖ ^ (2 : ℝ)) :
    MeasureTheory.MemLp g 2 MeasureTheory.Measure.count := by
  refine MeasureTheory.memLp_iff.mpr ?_
  rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (hf := by pw_aesm) (by norm_num) (by norm_num),
    MeasureTheory.lintegral_count]
  simp only [ENNReal.toReal_ofNat]
  have hpt : ∀ a : ℤ, ‖g a‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖g a‖ ^ (2 : ℝ)) := by
    intro a
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
  rw [show (∑' a : ℤ, ‖g a‖ₑ ^ (2 : ℝ))
      = ∑' a : ℤ, ENNReal.ofReal (‖g a‖ ^ (2 : ℝ)) from tsum_congr fun a => hpt a,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => Real.rpow_nonneg (norm_nonneg _) _) h]
  exact ENNReal.ofReal_lt_top

set_option maxHeartbeats 6000000 in
/-- **The `(0,0)` low-frequency case, *unmodulated* half, at positive height** (the only remaining
gap of `MdlSliceLinF`).  The special case `l₁ = 0` — where the arithmetic frequency set is
`{0}`, the family is a plain lacunary *dilation* family and the estimate is the JSW/Lépingle
theorem `Work.KMTAreas.A7G.plainBumpVarG` — is proved as `mdlLowpassCaseZero` (delegated module
`Submission/Work/KMTPlan/A6/mdlLowpassCaseZero.lean`), and `mdlLowpassCase` below is the case
split on `l₁ = 0` between the two.

This is the family `n ↦ T^{l₁}_{φ_{N_n}}(Π_{l₁,≤-u}f)` of the *unmodulated* bump
`φ_N(ξ) = η(2^{Log N}ξ)` (the paper's low-frequency case `s₁ = -u`, `j₁ = 0` of `(lin-1)`, §9 of
Krause--Mirek--Tao), with `N_n = ⌊a n⌋` and the clipping at the core.

By the identification `Tle ρ l (varphiN N 0) = kmtProj ρ l (-logN N)` of
`Submission/Work/KMTAreas/A7G/lowpassAlphaTransferG.lean` and the uniform `ℓ²` bound for the
projection, this is *exactly* the workspace's standing low-pass crux
`Work.KMTPlan.A6.lacunaryProjLowpassVar2`
(`= Work.KMTAreas.A7Hi2.SupPiece + Work.KMTAreas.A7Hi2.ChainPiece`; the tree's single remaining
`sorry` is `Submission/Work/KMTAreas/A7G/chainPartLowpass.lean:867`).

The other half of the `(0,0)` case — the *difference* `φ_N(e(Nt·)-1)` — is proved in this very file
as `mdlDiffFamily_local` (copied, with a renamed declaration, from the delegated module
`Submission/Work/KMTPlan/A6/mdlDiffFamily.lean`); `MdlSliceLinF` below combines the two by the
additivity `Tle ρ l₁ (φ + ψ) = Tle ρ l₁ φ + Tle ρ l₁ ψ` for bounded input
(`Work.KMTAreas.A7LoLin.Tle_add_of_bounded`) and the triangle inequality for the variational norm.

**A trap to avoid.**  Every explicit decomposition of `Tle ρ l₁ (φ_N)` that one would try first —
the `α`-decomposition `∑_{α∈A}M_{-α}D_σM_α` over the arithmetic frequencies
`#{A} = #{iwArithFreqs ρ l₁}`, the kernel form
`Tle ρ l₁(φ_N)g(x) = ∑_j \hatφ_N(j)·#{q ∈ P_{≤l₁} : q ∣ j}·g(x-j)`, or the residue/decimation
decomposition modulo a common denominator — loses a factor `#{A} ≍ 2^{2l₁}`, which the weight
`⟨L⟩²2^{2ρL}` **cannot** absorb (`L ≥ l₁` only gives `2^{2ρL} ≥ 2^{2ρl₁}`, while `2^{2l₁}` is what
is needed for `ρ ≤ 1/2` and large `l₁`).  An `#A`-free argument is essential: the paper's is the
Shannon-sampling/adelic factorisation (`T^{l}_{φ_N}` becomes `D_σ^{ℝ} ⊗ (Ẑ-averaging)`, the
`N`-independent arithmetic factor is pulled out, and the variation is handled by the
*vector-valued* Lépingle inequality, `Work.Analysis.Variation.lepingle_variation_vector`); the
tree's alternative is the good-λ/"window sparsity" route through
`Work.KMTPlan.A6.lacunaryProjLowpassVar2_of_pieces`.  The `l₁ = 0` case, where the arithmetic comb
is absent and the family is a lacunary *dilation* family, is
`Work.KMTAreas.A7Hi.DilVar` / `Work.KMTAreas.A7G.plainBumpVarG`. -/
theorem mdlLowpassCaseHigh (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₂ : ℕ) (f : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → 1 ≤ l₁ →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ =>
            if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
              Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0)
                (mdlF ρ (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₁ f) x
            else 0)) 2 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) *
              ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂) *
              MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
  -- 2026-10-02: this was the file's only `sorry` — the `p = 2` instance of the workspace's
  -- canonical chain/square-function crux, fed to `mdlLowpassCaseHigh_of_chainPartSqFun`.  It is
  -- now taken from the **crux-free** twin `Work.KMTPlan.A6.mdlLowpassCaseHigh_of_decim`
  -- (`Submission/Work/KMTPlan/A6/MdlLowpassCaseHighOfDecim.lean`), whose statement is verbatim
  -- the one above: the `mdlCore` gate clips this family at the deep scales `splitCut ρ L`, where
  -- the Magyar–Stein–Wainger decimation gives the whole `V^R`-bound with an absolute constant
  -- (see `NOTES_A6_lowpassCaseHigh_of_decim_SESSION.md`).
  mdlLowpassCaseHigh_of_decim C₀ hC₀ R hR

/-- **The `(0,0)` low-frequency case, *unmodulated* half**: the general-height statement, obtained
from `mdlLowpassCaseHigh` (`1 ≤ l₁`) and the (copied) special case `mdlLowpassCaseZero_local`
(`l₁ = 0`) by a case split on `l₁ = 0`. -/
theorem mdlLowpassCase (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₂ : ℕ) (f : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ =>
            if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
              Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0)
                (mdlF ρ (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₁ f) x
            else 0)) 2 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) *
              ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂) *
              MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  obtain ⟨ρ₀H, hρ₀Hpos, hH⟩ := mdlLowpassCaseHigh C₀ hC₀ R hR
  obtain ⟨ρ₀Z, hρ₀Zpos, hZ⟩ := mdlLowpassCaseZero_local C₀ hC₀ R hR
  refine ⟨min ρ₀H ρ₀Z, lt_min hρ₀Hpos hρ₀Zpos, ?_⟩
  intro ρ hρ hρle
  have hρH : ρ ≤ ρ₀H := le_trans hρle (min_le_left _ _)
  have hρZ : ρ ≤ ρ₀Z := le_trans hρle (min_le_right _ _)
  obtain ⟨KH, hKH⟩ := hH ρ hρ hρH
  obtain ⟨KZ, hKZ⟩ := hZ ρ hρ hρZ
  refine ⟨fun Λ => ⟨max (KH Λ) (KZ Λ), le_trans (KH Λ).2 (le_max_left _ _)⟩, ?_⟩
  intro a Λ l₁ l₂ k₂ f hΛ ha ha1
  rcases eq_or_ne l₁ 0 with hl₁0 | hl₁ne
  · subst hl₁0
    refine (hKZ a Λ l₂ k₂ f hΛ ha ha1).trans ?_
    exact mul_le_mul_nnreal_of_le (le_max_right _ _)
      (ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ 0 l₂ 0 k₂))
      (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
  · refine (hKH a Λ l₁ l₂ k₂ f hΛ ha ha1 (Nat.one_le_iff_ne_zero.mpr hl₁ne)).trans ?_
    exact mul_le_mul_nnreal_of_le (le_max_left _ _)
      (ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂))
      (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)

set_option maxHeartbeats 4000000 in
theorem MdlSliceLinF (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R)
    (j₁ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
          t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₁ = 0 → j₁ ≠ -1) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
              (fun n : ℕ =>
                if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
                  Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ j₁ t)
                    (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ
                      (max (max l₁ l₂) (max k₁ k₂))) l₁ f) x
                else 0)) 2 MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  obtain ⟨ρU, hρUpos, hU⟩ := mdlLowpassCase C₀ hC₀ R hR
  obtain ⟨ρD, hρDpos, hD⟩ := mdlDiffFamily_local C₀ hC₀ R hR
  refine ⟨2, by norm_num, min (min ρU ρD) (1 / (2 * (C₀ : ℝ))),
    lt_min (lt_min hρUpos hρDpos) (by positivity), ?_⟩
  intro ρ hρ hρle
  have hρUle : ρ ≤ ρU := le_trans hρle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρDle : ρ ≤ ρD := le_trans hρle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hC0R : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
  have hρ1 : ρ ≤ 1 := by
    have h3 : 1 / (2 * (C₀ : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith [le_trans hρle (min_le_right (min ρU ρD) (1 / (2 * (C₀ : ℝ))))]
  obtain ⟨KU, hKU⟩ := hU ρ hρ hρUle
  obtain ⟨KD, hKD⟩ := hD ρ hρ hρDle
  let KK : NNReal → NNReal := fun Λ => ⟨max 1 ((KU Λ : ℝ) + (KD Λ : ℝ) + (if h : 1 < Λ then
      Classical.choose (mdlVanishingCaseUnif ρ hρ hρ1 C₀ R hR j₁
        (max (Classical.choose (MdlLinVarphiNtjSupBound Λ h)) 1) (le_max_right _ 1)) else 0)),
      le_trans zero_le_one (le_max_left _ _)⟩
  refine ⟨KK, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 ht hk1j
  have hKf_eq : (KK Λ : ℝ) = max 1 ((KU Λ : ℝ) + (KD Λ : ℝ)
      + (Classical.choose (mdlVanishingCaseUnif ρ hρ hρ1 C₀ R hR j₁
        (max (Classical.choose (MdlLinVarphiNtjSupBound Λ hΛ)) 1) (le_max_right _ 1)))) := by
    dsimp only [KK]
    rw [dif_pos hΛ]
    rfl
  have hKUnn : (0 : ℝ) ≤ (KU Λ : ℝ) := (KU Λ).2
  have hKDnn : (0 : ℝ) ≤ (KD Λ : ℝ) := (KD Λ).2
  have hKvan_spec := Classical.choose_spec (mdlVanishingCaseUnif ρ hρ hρ1 C₀ R hR j₁
    (max (Classical.choose (MdlLinVarphiNtjSupBound Λ hΛ)) 1) (le_max_right _ 1))
  have hKvan_le : Classical.choose (mdlVanishingCaseUnif ρ hρ hρ1 C₀ R hR j₁
      (max (Classical.choose (MdlLinVarphiNtjSupBound Λ hΛ)) 1) (le_max_right _ 1))
      ≤ (KK Λ : ℝ) := by
    rw [hKf_eq]
    exact le_trans (by linarith [hKUnn, hKDnn]) (le_max_right 1 _)
  have hKsumR : (KU Λ : ℝ) + (KD Λ : ℝ) ≤ (KK Λ : ℝ) := by
    rw [hKf_eq]
    exact le_trans (by linarith [hKvan_spec.1.le]) (le_max_right 1 _)
  have hKsumENN : (KU Λ : ENNReal) + (KD Λ : ENNReal) ≤ (KK Λ : ENNReal) := by
    rw [← ENNReal.coe_add]
    refine ENNReal.coe_le_coe.mpr ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    exact hKsumR
  have hKK1 : (1 : ℝ) ≤ (KK Λ : ℝ) := by rw [hKf_eq]; exact le_max_left _ _
  have hKKne : (KK Λ : ENNReal) ≠ 0 := by
    rw [ne_eq, ENNReal.coe_eq_zero]
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hKK1)
  have hj1cases : j₁ = -1 ∨ j₁ = 0 ∨ j₁ = 1 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hj₁
  have hspec := Classical.choose_spec (MdlLinVarphiNtjSupBound Λ hΛ)
  by_cases hk1 : k₁ = 0
  · have hj1ne : j₁ ≠ -1 := hk1j hk1
    have hj1' : j₁ = 0 ∨ j₁ = 1 := by
      rcases hj1cases with h | h | h
      · exact absurd h hj1ne
      · exact Or.inl h
      · exact Or.inr h
    rcases hj1' with hj0 | hj1one
    · -- `j₁ = 0`: the split into the unmodulated and the difference families
      subst hj0
      subst hk1
      set G : ℤ → ℂ := Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ
        (max (max l₁ l₂) (max 0 k₂))) l₁ f with hG
      set WF : ℤ → ℝ≥0∞ := fun x => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
              Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t) G x
            else 0) with hWF
      set UF : ℤ → ℝ≥0∞ := fun x => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
              Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) G x
            else 0) with hUF
      set DF : ℤ → ℝ≥0∞ := fun x => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
              Work.KMTAreas.A7.Tle ρ l₁ (fun ξ : ℝ =>
                  Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                    - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ) G x
            else 0) with hDF
      have hUe : MeasureTheory.eLpNorm UF 2 MeasureTheory.Measure.count ≤
          (KU Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂) *
            MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        simpa only [hUF, hG] using hKU a Λ l₁ l₂ k₂ f hΛ ha ha1
      have hDe : MeasureTheory.eLpNorm DF 2 MeasureTheory.Measure.count ≤
          (KD Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂) *
            MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        simpa only [hDF, hG] using hKD a Λ l₁ l₂ k₂ t f hΛ ha ha1 ht
      have hgoalWF : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) 0 0 t) G x
              else 0)) = WF := by
        rw [hWF]
        funext x
        congr 1
        funext n
        by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
        · simp only [hc, if_true]
          congr 1
          funext ξ
          simp [varphiNtj]
        · simp only [hc, if_false]
      rw [hgoalWF]
      by_cases hmem : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count
      · have hgmem : MeasureTheory.MemLp G 2 MeasureTheory.Measure.count := by
          rw [hG]
          exact memLp_mdlF ρ _ l₁ hmem
        obtain ⟨Bg, hBg⟩ := Work.KMTAreas.A7.eLpNorm_finite_bounded 2 (by norm_num) G hgmem.eLpNorm_lt_top
        have hsplitV : ∀ x : ℤ, WF x ≤ UF x + DF x := by
          intro x
          simp only [hWF, hUF, hDF]
          have hpt : (fun n : ℕ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                  Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t) G x
                else 0)
              = (fun n : ℕ => (if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                    Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) G x
                  else 0)
                + (if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                    Work.KMTAreas.A7.Tle ρ l₁ (fun ξ : ℝ =>
                        Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                          - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ) G x
                  else 0)) := by
            funext n
            by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
            · simp only [hc, if_true]
              have hsym : (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0
                    + fun ξ : ℝ => Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                        - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)
                  = Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t := by
                funext ξ
                simp only [Pi.add_apply]
                ring
              have hAdmφ : Work.KMTAreas.A7.Adm (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
                  (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) := by
                have hφ : Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 0
                    = Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 := by
                  funext ξ
                  simp [Work.KMTAreas.A7.varphiNt, Work.KMTAreas.A7.ee]
                simpa only [hφ] using
                  (Work.KMTAreas.A7.adm_of_bump
                    (Work.KMTAreas.A7.contDiff_varphiNt (Nat.floor (a n)) 0 0)
                    (Work.KMTAreas.A7.hasCompactSupport_varphiNt (Nat.floor (a n)) 0 0))
              have hAdmψ : Work.KMTAreas.A7.Adm (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
                  (fun ξ : ℝ => Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                      - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ) :=
                (Work.KMTAreas.A7.adm_of_bump
                  (Work.KMTAreas.A7.contDiff_varphiNt (Nat.floor (a n)) 0 t)
                  (Work.KMTAreas.A7.hasCompactSupport_varphiNt (Nat.floor (a n)) 0 t)).sub hAdmφ
              conv_lhs => rw [← hsym]
              rw [Work.KMTAreas.A7LoLin.Tle_add_of_bounded hAdmφ hAdmψ hBg]
              rfl
            · simp only [hc, if_false, add_zero]
          rw [hpt]
          exact Submission.PointwiseErgodicTheorems.variationalNorm_add_le
            (le_of_lt (lt_trans (by norm_num) hR)) _ _
        calc MeasureTheory.eLpNorm WF 2 MeasureTheory.Measure.count
            ≤ MeasureTheory.eLpNorm (fun x : ℤ => UF x + DF x) 2 MeasureTheory.Measure.count :=
                MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => hsplitV x)
          _ ≤ MeasureTheory.eLpNorm UF 2 MeasureTheory.Measure.count
                + MeasureTheory.eLpNorm DF 2 MeasureTheory.Measure.count :=
                MeasureTheory.eLpNorm_add_le (by norm_num)
          _ ≤ (KU Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂)
                * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              + (KD Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂)
                * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := add_le_add hUe hDe
          _ = ((KU Λ : ENNReal) + (KD Λ : ENNReal))
                * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂)
                * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
              rw [add_mul, add_mul]
          _ ≤ (KK Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂)
                * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
              gcongr
      · have htop : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count = ⊤ := by
          by_contra hne
          exact hmem (MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hne))
        rw [htop, ENNReal.mul_top]
        · exact le_top
        · exact mul_ne_zero hKKne (ENNReal.ofReal_ne_zero_iff.mpr (by
            have := one_le_lossWeight_two hρ.le l₁ l₂ 0 k₂
            linarith))
    · -- `j₁ = 1`: the vanishing case
      subst hj1one
      subst hk1
      have hsup : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (ξ : ℝ),
          ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            varphiNtj (Nat.floor (a n)) 0 1 t ξ‖
          ≤ max (Classical.choose (MdlLinVarphiNtjSupBound Λ hΛ)) 1 :=
        fun U ω ξ => le_trans (hspec.2.2 t ht a ha ha1 U ω ξ) (le_max_left _ _)
      have hmain := (Classical.choose_spec (mdlVanishingCaseUnif ρ hρ hρ1 C₀ R hR 1
        (max (Classical.choose (MdlLinVarphiNtjSupBound Λ hΛ)) 1) (le_max_right _ 1))).2
        a Λ l₁ l₂ 0 k₂ t f hΛ ha ha1 hsup
      exact hmain.trans (ofReal_mul_le_nnreal_mul_lossWeight hKvan_le hρ.le l₁ l₂ 0 k₂
        (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count))
  · -- `k₁ ≥ 1`: the vanishing case
    have hk1pos : 1 ≤ k₁ := Nat.one_le_iff_ne_zero.mpr hk1
    have hsup : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (ξ : ℝ),
        ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * varphiNtj (Nat.floor (a n)) k₁ j₁ t ξ‖
        ≤ max (Classical.choose (MdlLinVarphiNtjSupBound Λ hΛ)) 1 :=
      fun U ω ξ => le_trans (hspec.2.1 k₁ hk1pos j₁ hj₁ t ht a ha ha1 U ω ξ) (le_max_left _ _)
    have hmain := (Classical.choose_spec (mdlVanishingCaseUnif ρ hρ hρ1 C₀ R hR j₁
      (max (Classical.choose (MdlLinVarphiNtjSupBound Λ hΛ)) 1) (le_max_right _ 1))).2
      a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 hsup
    exact hmain.trans (ofReal_mul_le_nnreal_mul_lossWeight hKvan_le hρ.le l₁ l₂ k₁ k₂
      (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count))

