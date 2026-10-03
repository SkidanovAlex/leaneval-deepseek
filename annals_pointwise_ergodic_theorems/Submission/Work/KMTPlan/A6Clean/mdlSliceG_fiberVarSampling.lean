import Mathlib
import Submission.Work.KMTAreas.A7Rescue.FiberVarSamplingGRep
import Submission.Work.KMTPlan.A6Clean.fiberOpP_crude
import Submission.Work.KMTPlan.A6Clean.perShiftFibreVarG_j
import Submission.Work.KMTPlan.A6.MdlSliceLinGOne
import Submission.Work.KMTPlan.A6.LinfDefs
import Submission.Port.Aesm

namespace Work.KMTPlan.A6Clean

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Helper lemmas for the assembly -/

/-- **A square-summable sequence on `ℤ` is bounded.**  Every atom of the counting measure has
mass `1`, so `‖g x‖ₑ ≤ eLpNorm g 2`. -/
lemma exists_bound_of_memLp {g : ℤ → ℂ} (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℤ, ‖g x‖ ≤ B := by
  refine ⟨(MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count).toReal,
    ENNReal.toReal_nonneg, fun x => ?_⟩
  have hlt : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count ≠ ⊤ := hg.eLpNorm_lt_top.ne
  have hmem : ‖g x‖ₑ ≤ MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    have h1 : ‖g x‖ₑ ^ (2 : ℝ) ≤ ∫⁻ y : ℤ, ‖g y‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
      rw [MeasureTheory.lintegral_count]
      exact ENNReal.le_tsum (f := fun y : ℤ => ‖g y‖ₑ ^ (2 : ℝ)) x
    have h2 : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
        = (∫⁻ y : ℤ, ‖g y‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) ^ (1 / 2 : ℝ) := by
      rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (p := 2)
        (μ := MeasureTheory.Measure.count) (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
    rw [h2]
    calc ‖g x‖ₑ = (‖g x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
      _ ≤ _ := ENNReal.rpow_le_rpow h1 (by norm_num)
  have h4 : (‖g x‖ₑ).toReal ≤ (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count).toReal :=
    ENNReal.toReal_mono hlt hmem
  have h5 : (‖g x‖ₑ).toReal = ‖g x‖ := by
    rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]
  rwa [h5] at h4

/-- **Support of the modified `g`-side bump in the plateau of `mStargF`**: if `k₂ + 2u + 1 ≤ Log N`
then `|ξ| ≤ 2^{-d·2u-1}` wherever `varphitildeNtj P N k₂ j₂ t` does not vanish. -/
lemma rpow_varphitildeNtj_le (P : Polynomial ℤ) (hPn : 1 ≤ P.natDegree) (N k₂ U : ℕ) (j₂ : ℤ)
    (t : ℝ) (h : (k₂ : ℤ) + 2 * (U : ℤ) + 1 ≤ (Work.Analysis.EndVar.logN N).toNat) :
    (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
      ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * (2 * (U : ℤ))) - 1) := by
  rw [← Real.rpow_intCast]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hlog : ((Work.Analysis.EndVar.logN N).toNat : ℤ) = Work.Analysis.EndVar.logN N :=
    Int.toNat_of_nonneg (by simp [Work.Analysis.EndVar.logN])
  rw [hlog] at h
  have h5 : ((k₂ : ℤ) + 2 * (U : ℤ) + 1 : ℝ) ≤ (Work.Analysis.EndVar.logN N : ℝ) := by
    exact_mod_cast h
  have h4 : (k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ) ≤ -(2 * (U : ℝ)) - 1 := by
    push_cast at h5
    linarith
  have h3 : ((-((P.natDegree : ℤ) * (2 * (U : ℤ))) - 1 : ℤ) : ℝ)
      = -((P.natDegree : ℝ) * (2 * (U : ℝ))) - 1 := by push_cast; ring
  rw [h3]
  have hd0 : (0 : ℝ) ≤ (P.natDegree : ℝ) := by positivity
  have hd1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hPn
  have hmul := mul_le_mul_of_nonneg_left h4 hd0
  nlinarith [hmul, hd1]

/-! ## The functional calculus for the modified `g`-side bump (self-contained) -/

private lemma measurable_zpow_int_self (j : ℤ) : Measurable fun z : ℂ => z ^ j := by
  rcases Int.eq_nat_or_neg j with ⟨n, h | h⟩
  · subst h; simpa using (continuous_pow (M := ℂ) n).measurable
  · subst h
    simp only [zpow_neg, zpow_natCast]
    exact ((continuous_pow (M := ℂ) n).measurable).inv

private lemma measurable_varphitildeNt_self (P : Polynomial ℤ) (N k : ℕ) (t : ℝ) :
    Measurable (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t) := by
  have h : Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t
      = fun ξ : ℝ => Work.KMTAreas.A7.varphitildeN P.natDegree N k ξ
          * Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t) * ξ) := rfl
  rw [h]
  refine (Work.KMTPlan.A6.measurable_varphitildeN P.natDegree N k).mul ?_
  show Measurable fun ξ : ℝ =>
    Complex.exp (2 * Real.pi * Complex.I * ((Work.KMTAreas.A7.PevalR P ((N : ℝ) * t) * ξ : ℝ)))
  fun_prop

private lemma measurable_varphitildeNtj_self (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (t : ℝ) :
    Measurable (Work.KMTPlan.A6.varphitildeNtj P N k j t) := by
  have h : Work.KMTPlan.A6.varphitildeNtj P N k j t
      = fun ξ : ℝ => ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree
            * ξ : ℝ)) : ℂ) ^ j
          * Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ := rfl
  rw [h]
  refine ((measurable_zpow_int_self j).comp ?_).mul (measurable_varphitildeNt_self P N k t)
  exact Complex.continuous_ofReal.measurable.comp (by fun_prop)

/-- **The `bn-ident` collapse for the modified `g`-side bump**: the height-`≤ l₂` IW multiplier of
the modified bump applied to the exact-height shell `mdlG ρ P u l₂ g` is the exact-height
`Tex`-multiplier applied to `g`, in the non-singular cases `(k₂,j₂) ≠ (0,-1)`. -/
private theorem Tle_mdlG_eq_Tex_self (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (u l₂ N k₂ : ℕ) (j₂ : ℤ) (t : ℝ) (g : ℤ → ℂ)
    (hN : 1 ≤ N) (hl₂ : l₂ ≠ 0) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (hk₂ : k₂ = 0 → j₂ ≠ -1)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (hnA : Work.Analysis.IonescuWainger.NonAliasing (-((P.natDegree : ℤ) * (u : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂))
    (hsup : ∀ ξ : ℝ, Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * (2 * (u : ℤ))) - 1)) :
    Work.KMTAreas.A7.Tle ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t)
        (Work.KMTPlan.A6.mdlG ρ P u l₂ g)
      = Work.KMTAreas.A7.Tex ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t) g := by
  have hk : k₂ ≠ 0 ∨ 0 ≤ j₂ := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hk0, hjneg⟩ := hcon
    have hj2 : j₂ = -1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj₂
      rcases hj₂ with h | h | h <;> omega
    exact hk₂ hk0 hj2
  have h0A : (0 : Work.Analysis.IonescuWainger.Circle)
      ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ := by
    rw [Work.Analysis.IonescuWainger.mem_iwArithFreqs]
    exact ⟨1, Work.Analysis.IonescuWainger.one_mem_iwP ρ l₂, by simp⟩
  have hc : (2 : ℝ) ^ (-((P.natDegree : ℤ) * (u : ℤ))) ≤ 1 / 2 := by
    by_contra hcon
    rw [not_le] at hcon
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-((P.natDegree : ℤ) * (u : ℤ))) :=
      zpow_pos (by norm_num) _
    have hmem1 : (2 : ℝ) ^ (-((P.natDegree : ℤ) * (u : ℤ)))
        ∈ Work.Analysis.IonescuWainger.realArc (-((P.natDegree : ℤ) * (u : ℤ))) := by
      rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
      exact ⟨neg_le_self hpos.le, le_rfl⟩
    have hmem2 : (2 : ℝ) ^ (-((P.natDegree : ℤ) * (u : ℤ))) - 1
        ∈ Work.Analysis.IonescuWainger.realArc (-((P.natDegree : ℤ) * (u : ℤ))) := by
      rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
      constructor <;> linarith
    have hcoe : (0 : Work.Analysis.IonescuWainger.Circle)
          + (((2 : ℝ) ^ (-((P.natDegree : ℤ) * (u : ℤ))) : ℝ) :
              Work.Analysis.IonescuWainger.Circle)
        = (0 : Work.Analysis.IonescuWainger.Circle)
          + (((2 : ℝ) ^ (-((P.natDegree : ℤ) * (u : ℤ))) - 1 : ℝ) :
              Work.Analysis.IonescuWainger.Circle) := by
      rw [zero_add, zero_add, ← sub_eq_zero, ← AddCircle.coe_sub]
      have h1 : ((1 : ℝ) : Work.Analysis.IonescuWainger.Circle) = 0 := by
        rw [AddCircle.coe_eq_zero_iff]
        exact ⟨1, by simp⟩
      rw [show (2 : ℝ) ^ (-((P.natDegree : ℤ) * (u : ℤ)))
          - ((2 : ℝ) ^ (-((P.natDegree : ℤ) * (u : ℤ))) - 1) = 1 by ring, h1]
    have hres := (hnA 0 h0A 0 h0A _ hmem1 _ hmem2 hcoe).2
    linarith
  have hΦ : Work.Analysis.IonescuWainger.SupportedInArc
      (-((P.natDegree : ℤ) * (u : ℤ)) - 1)
      (Work.Analysis.IonescuWainger.periodize (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t)) := by
    refine Work.KMTPlan.A6.supportedInArc_periodize_of_arc
      (k := -((P.natDegree : ℤ) * (u : ℤ)) - 1) fun x hx => ?_
    rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
    have h1 := hsup x hx
    have h2 : (2 : ℝ) ^ (-((P.natDegree : ℤ) * (2 * (u : ℤ))) - 1)
        ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * (u : ℤ)) - 1) := by
      refine zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ?_
      have hu : (0 : ℤ) ≤ (u : ℤ) := Int.natCast_nonneg u
      have hd0 : (0 : ℤ) ≤ (P.natDegree : ℤ) := Int.natCast_nonneg _
      nlinarith
    have h3 : |x| ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * (u : ℤ)) - 1) := le_trans h1 h2
    exact ⟨neg_le_of_abs_le h3, le_of_abs_le h3⟩
  have hφmem : MeasureTheory.MemLp
      (Work.Analysis.IonescuWainger.periodize (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t)) ⊤
      Work.Analysis.IonescuWainger.circleMeasure :=
    Work.KMTPlan.A6.Linf.memLp_periodize_of_arc _ (measurable_varphitildeNtj_self P N k₂ j₂ t) _
      ((2 : ℝ) ^ (2 * P.natDegree + 1)) (zpow_nonneg (by norm_num) _) hsup
      (fun ξ => Work.KMTPlan.A6.varphitildeNtj_pointwise P (by omega) N k₂ j₂ t ξ hN hj₂ hk)
  rw [Work.KMTPlan.A6.Tle_mdlG_eq_Tm ρ hρ hρ1 P u l₂ (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t)
    hc hg hnA hφmem hΦ]
  show Work.Analysis.IWMultiplier.iwConv (Work.KMTAreas.A7.diffFreqs ρ l₂)
      (Work.Analysis.IonescuWainger.periodize (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t)) g
    = Work.Analysis.IWMultiplier.iwConv
        (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂)
        (Work.Analysis.IonescuWainger.periodize (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t)) g
  rw [Work.KMTAreas.A7.diffFreqs_eq_iwArithFreqsNew hl₂]

/-! ## The main theorem -/

theorem mdlSliceG_fiberVarSampling (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal)
    (hr : 2 < r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤), ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ C : ℝ, 0 < C ∧
        ∀ (C₀ : ℕ) (a : ℕ → NNReal) (Λ : NNReal) (hΛ : 1 < Λ)
          (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n)
          (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (j₂ : ℤ) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
          (hk₂ : k₂ = 0 → j₂ ≠ -1) (g : ℤ → ℂ),
          MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
          t ∈ Set.Icc (1 / 2 : ℝ) 1 →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              Work.KMTAreas.A7.residueLp p.toReal (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
                (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  Work.KMTAreas.A7.fiberOpP ρ P l₂
                    (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ
                      (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
                    n₀ (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) y)) x) p
              MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (C * Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm (fun x : ℤ =>
                  PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                    Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n x)) p
                  MeasureTheory.Measure.count := by
  classical
  -- the uniform kernel-mass bound of the wide bump `mStargF`
  obtain ⟨Cstar, hCstarpos, hCstar_all⟩ :=
    Work.A7.exists_cw_mStargF_tsum_le P.natDegree (by omega)
  have hCstar : ∀ U : ℕ, Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw
        (Work.KMTAreas.A7.mStargF P.natDegree U) j‖)
      ∧ (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree U) j‖) ≤ Cstar :=
    fun U => ⟨Work.KMTAreas.A7Hi.summable_cw_mStargF_fin P.natDegree U, hCstar_all U⟩
  refine ⟨0, le_rfl, 1, one_pos, ?_⟩
  intro p hp hptop ρ hρ hρ1
  -- constants depending on `ρ` (and on `p`)
  obtain ⟨Ccard, hCcardpos, hCcard⟩ := Work.KMTAreas.A7.iwArithFreqs_card_le ρ hρ hρ1
  obtain ⟨CB, hCBpos, hCB⟩ := perShiftFibreVarG_j ρ hρ hρ1 P hd p hp hptop r hr
  obtain ⟨Bfas, hBfas⟩ := Work.KMTAreas.A7Hi.farey_and_strict_of_large_L_g ρ hρ hρ1
  obtain ⟨Bna, hBna⟩ := Work.KMTAreas.A7.exists_nonAliasing_uScale ρ hρ hρ1
  set Bcase : ℕ := max Bfas Bna + 1 with hBcasedef
  set CA : ℝ := (2 : ℝ) ^ (Ccard * (2 : ℝ) ^ (ρ * (Bcase : ℝ))) * Cstar + 1 with hCAdef
  refine ⟨max (max CB CA) 1, lt_max_of_lt_left (lt_max_of_lt_left hCBpos), ?_⟩
  intro C₀ a Λ hΛ ha ha1 l₁ l₂ k₁ k₂ t j₂ hj₂ hk₂ g hg ht
  obtain ⟨Bg, hBg0, hBg⟩ := exists_bound_of_memLp hg
  -- abbreviations (and the goal rewritten in terms of them)
  set L : ℕ := Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ with hLdef
  set U : ℕ := Work.KMTAreas.A7.uScale ρ L with hUdef
  set q : ℕ := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) with hqdef
  set w : ℕ → ℤ → ℂ := Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g with hwdef
  set E : ENNReal := MeasureTheory.eLpNorm (fun x : ℤ =>
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x)) p
      MeasureTheory.Measure.count with hEdef
  have hlw0 : Work.KMTAreas.A7.lossWeight 0 ρ l₁ l₂ k₁ k₂ = 1 := by
    rw [Work.KMTAreas.A7.lossWeight]; simp
  have hBfas_lt_Bcase : Bfas < Bcase := by
    rw [hBcasedef]; exact Nat.lt_succ_of_le (le_max_left _ _)
  have hBna_le_Bcase : Bna ≤ Bcase := by
    rw [hBcasedef]; exact Nat.le_succ_of_le (le_max_right _ _)
  by_cases hsmall : l₂ = 0 ∨ L < Bcase
  · -- ===== Case A : the crude kernel-mass bound =====
    have hl₂L : l₂ ≤ L := by
      rw [hLdef, Work.KMTPlan.A6.lcL]; omega
    have hl₂B : l₂ ≤ Bcase := by
      rcases hsmall with h | h
      · omega
      · omega
    have hqpos : 0 < q := by
      rw [hqdef]; exact Work.KMTAreas.A7.arithQ_pos ρ (max l₁ l₂)
    have hcrude := fiberOpP_crude P r hr Cstar hCstarpos hCstar ρ p hp hptop l₂ U q hqpos w
    refine hcrude.trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have hcard : ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ) ≤
        (2 : ℝ) ^ (Ccard * (2 : ℝ) ^ (ρ * (Bcase : ℝ))) := by
      refine le_trans (hCcard l₂) ?_
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      refine mul_le_mul_of_nonneg_left ?_ hCcardpos.le
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have h1 : (l₂ : ℝ) ≤ (Bcase : ℝ) := by exact_mod_cast hl₂B
      nlinarith [hρ.le]
    have hstep : ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ) * Cstar + 1 ≤ CA := by
      have h2 := mul_le_mul_of_nonneg_right hcard hCstarpos.le
      rw [hCAdef]; linarith
    have h3 : CA ≤ max (max CB CA) 1 :=
      le_trans (le_max_right CB CA) (le_max_left (max CB CA) 1)
    rw [hlw0, mul_one]
    exact le_trans hstep h3
  · -- ===== Case B : the deep estimate =====
    push_neg at hsmall
    obtain ⟨hl₂ne, hBL⟩ := hsmall
    have hU1 : 1 ≤ U := by
      rw [hUdef]; exact Work.KMTAreas.A7.one_le_uScale ρ hρ.le L
    have hl₂L : l₂ ≤ L := by
      rw [hLdef, Work.KMTPlan.A6.lcL]; omega
    have hna : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (U : ℤ)))
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) :=
      hBna l₂ L hl₂L (le_trans hBna_le_Bcase hBL)
    have hBfasL : Bfas < L := lt_of_lt_of_le hBfas_lt_Bcase hBL
    have hqpos : 0 < q := by
      rw [hqdef]; exact Work.KMTAreas.A7.arithQ_pos ρ (max l₁ l₂)
    have hq1 : 1 ≤ q := hqpos
    -- the gate predicate, as an opaque local definition
    set S : ℕ → Prop := fun n => Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n with hSdef
    haveI hSdec : DecidablePred S := fun n => by rw [hSdef]; infer_instance
    have hcore_split : ∀ n, S n → Work.KMTAreas.A7.splitCut ρ L < Nat.floor (a n) := by
      intro n hn
      have hn' : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n := by rwa [hSdef] at hn
      exact ((Work.KMTPlan.A6.mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hn').2.1
    have hfarey_core : ∀ n, S n →
        8 * (2 : ℝ) ^ k₂ * (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ)
          ≤ (Nat.floor (a n) : ℝ) :=
      fun n hn => (hBfas l₁ l₂ k₁ k₂ (Nat.floor (a n)) (hcore_split n hn) hBfasL).1
    have hstrict_core : ∀ n, S n →
        (k₂ : ℤ) + 2 * (U : ℤ) + 1
          ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat := by
      intro n hn
      have h := (hBfas l₁ l₂ k₁ k₂ (Nat.floor (a n)) (hcore_split n hn) hBfasL).2
      have h2 : ((k₂ + 2 * Work.KMTAreas.A7.uScale ρ
            (max (max l₁ l₂) (max k₁ k₂)) + 1 : ℕ) : ℤ)
          ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ) := by
        exact_mod_cast h
      rw [hUdef, hLdef, Work.KMTPlan.A6.lcL]
      push_cast at h2 ⊢
      exact h2
    -- the extended scale sequence
    set K : ℕ := 2 ^ (k₂ + 2 * U + 4) * (q + 1) with hKdef
    set N' : ℕ → ℕ := fun n => if S n then Nat.floor (a n) else K with hN'def
    have hfarey' : ∀ n : ℕ, 8 * (2 : ℝ) ^ k₂ * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ)
        ≤ (N' n : ℝ) := by
      intro n
      by_cases hn : S n
      · rw [hN'def]; simp only [hn, if_true]
        have h1 := hfarey_core n hn
        have h2 : (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ)
            ≤ (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℝ) := by
          exact_mod_cast Work.KMTAreas.A7.arithQ_mono ρ hρ hρ1 (le_max_right l₁ l₂)
        refine le_trans (mul_le_mul_of_nonneg_left h2 (by positivity)) h1
      · rw [hN'def]; simp only [hn, if_false]
        have harith : (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ) ≤ (q : ℝ) := by
          rw [hqdef]
          exact_mod_cast Work.KMTAreas.A7.arithQ_mono ρ hρ hρ1 (le_max_right l₁ l₂)
        have harith0 : (0 : ℝ) ≤ (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ) := Nat.cast_nonneg _
        have hKcast : ((K : ℕ) : ℝ)
            = (2 : ℝ) ^ (k₂ + 2 * U + 4) * ((q : ℝ) + 1) := by
          rw [hKdef]; push_cast; ring
        have h9 : (2 : ℝ) ^ (k₂ + 2 * U + 4) = (2 : ℝ) ^ k₂ * (2 : ℝ) ^ (2 * U + 4) := by
          rw [show k₂ + 2 * U + 4 = k₂ + (2 * U + 4) by ring, pow_add]
        rw [hKcast, h9]
        have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ (2 * U + 4) := by
          rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num]
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        have h2k : (0 : ℝ) < (2 : ℝ) ^ k₂ := by positivity
        have hstep1 : 8 * (2 : ℝ) ^ k₂ ≤ (2 : ℝ) ^ k₂ * (2 : ℝ) ^ (2 * U + 4) := by
          calc 8 * (2 : ℝ) ^ k₂ = (2 : ℝ) ^ k₂ * 8 := by ring
            _ ≤ (2 : ℝ) ^ k₂ * (2 : ℝ) ^ (2 * U + 4) :=
                mul_le_mul_of_nonneg_left h8 h2k.le
        have hstep2 : 8 * (2 : ℝ) ^ k₂ * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ)
            ≤ ((2 : ℝ) ^ k₂ * (2 : ℝ) ^ (2 * U + 4)) * (q : ℝ) := by
          calc 8 * (2 : ℝ) ^ k₂ * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ)
              = (8 * (2 : ℝ) ^ k₂) * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ) := by ring
            _ ≤ ((2 : ℝ) ^ k₂ * (2 : ℝ) ^ (2 * U + 4))
                  * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ) :=
                mul_le_mul_of_nonneg_right hstep1 harith0
            _ ≤ ((2 : ℝ) ^ k₂ * (2 : ℝ) ^ (2 * U + 4)) * (q : ℝ) :=
                mul_le_mul_of_nonneg_left harith (by positivity)
        have hstep3 : ((2 : ℝ) ^ k₂ * (2 : ℝ) ^ (2 * U + 4)) * (q : ℝ)
            ≤ ((2 : ℝ) ^ k₂ * (2 : ℝ) ^ (2 * U + 4)) * ((q : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith [hstep2, hstep3]
    have hstrict' : ∀ n : ℕ, (k₂ : ℤ) + 2 * (U : ℤ) + 1
        ≤ (Work.Analysis.EndVar.logN (N' n)).toNat := by
      intro n
      by_cases hn : S n
      · rw [hN'def]; simp only [hn, if_true]; exact hstrict_core n hn
      · rw [hN'def]; simp only [hn, if_false]
        have hle : 2 ^ (k₂ + 2 * U + 4) ≤ max K 2 := by
          rw [hKdef]
          refine le_trans ?_ (le_max_left _ _)
          exact Nat.le_mul_of_pos_right _ (by omega)
        have hlog : k₂ + 2 * U + 4 ≤ Nat.log 2 (max K 2) :=
          Nat.le_log_of_pow_le (by norm_num : 1 < 2) hle
        have hlogK : (Work.Analysis.EndVar.logN K).toNat = Nat.log 2 (max K 2) := by
          rw [Work.Analysis.EndVar.logN, Int.toNat_natCast]
        rw [hlogK]
        omega
    -- the deep per-shift estimate
    have hdeep := hCB l₂ k₂ U j₂ hj₂ hk₂ hU1 t g Bg hBg N' S hfarey' hstrict' hna
    -- the `Tex`-carrier family of the modified bump is `w`
    have hfam_pt : ∀ n : ℕ, (if S n then Work.KMTAreas.A7.Tex ρ l₂
          (Work.KMTPlan.A6.varphitildeNtj P (N' n) k₂ j₂ t) g else 0) = w n := by
      intro n
      by_cases hn : S n
      · have hn' : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n := by rwa [hSdef] at hn
        have hNn : N' n = Nat.floor (a n) := by
          rw [hN'def]; simp only [hn, if_true]
        have hsup : ∀ ξ : ℝ, Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t ξ ≠ 0 →
            |ξ| ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * (2 * (U : ℤ))) - 1) := by
          intro ξ hξ
          exact (Work.KMTPlan.A6.varphitildeNtj_abs_le P (Nat.floor (a n)) k₂ j₂ t ξ hξ).trans
            (rpow_varphitildeNtj_le P (by omega) (Nat.floor (a n)) k₂ U j₂ t (hstrict_core n hn))
        have hnA : Work.Analysis.IonescuWainger.NonAliasing
            (-((P.natDegree : ℤ) * (U : ℤ))) (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) := by
          have h1 : (2 : ℤ) ≤ (P.natDegree : ℤ) := by exact_mod_cast hd
          have hle : -((P.natDegree : ℤ) * (U : ℤ)) ≤ -(2 * (U : ℤ)) :=
            neg_le_neg (mul_le_mul_of_nonneg_right h1 (Int.natCast_nonneg U))
          exact Work.KMTAreas.A7Hi.nonAliasing_mono_scale hle hna
        have hk : k₂ ≠ 0 ∨ 0 ≤ j₂ := by
          by_contra hcon
          push_neg at hcon
          obtain ⟨hk0, hjneg⟩ := hcon
          have hj2 : j₂ = -1 := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hj₂
            rcases hj₂ with h | h | h <;> omega
          exact hk₂ hk0 hj2
        have hkey := Tle_mdlG_eq_Tex_self ρ hρ hρ1 P hd U l₂ (Nat.floor (a n)) k₂ j₂ t g
          (Nat.le_floor (by simpa using ha1 n)) hl₂ne hj₂ hk₂ hg hnA hsup
        rw [if_pos hn, hNn, hwdef]
        simp only [Work.KMTPlan.A6.mdlSliceG, if_pos hn']
        exact hkey.symm
      · have hn' : ¬ Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n := by rwa [hSdef] at hn
        have h1 : (if S n then Work.KMTAreas.A7.Tex ρ l₂
            (Work.KMTPlan.A6.varphitildeNtj P (N' n) k₂ j₂ t) g else 0) = 0 := if_neg hn
        have h2 : w n = 0 := by
          rw [hwdef]
          simp only [Work.KMTPlan.A6.mdlSliceG, if_neg hn']
        rw [h1, h2]
    simp only [hfam_pt] at hdeep
    -- per-residue bounds and the residue average
    have hper : ∀ n₀ : ℕ, n₀ < q → MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            Work.KMTAreas.A7.fiberOpP ρ P l₂ (Work.KMTAreas.A7.mStargF P.natDegree U)
              (n₀ : ℤ) (w n) x)) (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal CB * E := by
      intro n₀ _
      have h := hdeep (P.eval (n₀ : ℤ))
      have hpo : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hptop.ne
      have hfe : ∀ (m : ℝ → ℂ) (n₁ : ℤ) (v : ℤ → ℂ), Work.KMTAreas.A7.fiberOpP ρ P l₂ m n₁ v
          = Work.KMTAreas.A7.fiberOp ρ l₂ m (P.eval n₁) v := fun _ _ _ => rfl
      simpa only [hfe, hEdef, hpo] using h
    have hres := Work.KMTAreas.A7.eLpNorm_residueLp_le (p := p.toReal)
      (ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one hp)) hptop.ne)
      (q := q) (fun x n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        Work.KMTAreas.A7.fiberOpP ρ P l₂ (Work.KMTAreas.A7.mStargF P.natDegree U)
          (n₀ : ℤ) (w n) x)) (ENNReal.ofReal CB * E) hper
    have hpo : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hptop.ne
    rw [hpo] at hres
    refine hres.trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    rw [hlw0, mul_one]
    exact le_trans (le_max_left CB CA) (le_max_left (max CB CA) 1)

end

end Work.KMTPlan.A6Clean
