/-
# `supDeepLe` (the *deep* half of the maximal Ionescu--Wainger bound) — auxiliary module

`Work.KMTAreas.A7Hi2.supDeepLe` asks for an `l₁`-free maximal bound for the *deep* range
`m₀ + n ≥ cutLevel ρ l₁` of the low-pass Ionescu--Wainger walk
`n ↦ Π_{≤l₁,≤-(m₀+n)} f`.  This module proves that statement with a *local copy* of the cut level
(`cutLevelAux`, definitionally equal to `Work.KMTAreas.A7Hi2.cutLevel`, which lives in
`supPieceClean`); the file `supDeepLe.lean` transfers the result by definitional equality.

## The argument

Write `Q := iwQl ρ l₁` for the common denominator of `(ℚ/ℤ)_{≤l₁}` and
`K := Nat.clog 2 (3Q) + 1`, so that `3Q < 2^K`.  The deep range is `m₀ + n ≥ K + 1`.  Choose the
*coarse* level

  `C₀ := max K (m₀ - 1)`.

Then

* `3Q < 2^{C₀}` (because `K ≤ C₀`) and `C₀ + 1 ≤ m₀ + n` on the deep range, so the decimation
  factorisation `Work.KMTAreas.A7G.decimFactBdd` applies at every deep level:
  `Π_{≤l₁,≤-(m₀+n)} f = iwConv (torsFinset Q) (bump (m₀+n)) (Π_{≤l₁,≤-C₀} f)`;
* the kernel of the torsion symbol is the decimated kernel, hence the level-`(m₀+n)` projection is
  `Q` times the *decimated dilation family* `decimDilFam C₀ (𝓕 kmtEta) Q g (m₀+n-C₀)` of the fixed
  coarse projection `g := Π_{≤l₁,≤-C₀} f` (`Work.KMTAreas.A7G.iwConv_torsFinset_eq_smul_decimDilFam`);
* the decimated dilation variational estimate `Work.A7Hi2.decimDilVarUnif` bounds the variational
  norm of that family by `(C/Q)‖g‖_{ℓᵖ}` with an *absolute* `C` — the factor `Q` in front cancels the
  `1/Q` exactly;
* `C₀ ≥ Cρ·2^{ρl₁}` for the constant `Cρ` of the single-scale Ionescu--Wainger bound
  (`Work.KMTAreas.A7.kmtProj_lp_bound_uniform`, whose constant is `l₁`-free), so that bound applies
  to the coarse projection `g`.

The maximal over the deep range is dominated pointwise by the first term of the variational norm,
and everything is therefore `l₁`-free. -/
import Mathlib
import Submission.Work.KMTAreas.A7G.tailVarBound
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7Hi2

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## The cut level (a local copy, definitionally equal to `Work.KMTAreas.A7Hi2.cutLevel`) -/

/-- The cut level of the deep/shallow split: the least level `L` with `3 · iwQl ρ l₁ ≤ 2^L`, plus
two (this is verbatim the definition of `Work.KMTAreas.A7Hi2.cutLevel`). -/
noncomputable def cutLevelAux (ρ : ℝ) (l₁ : ℕ) : ℕ :=
  Nat.clog 2 (3 * Work.Analysis.IonescuWainger.iwQl ρ l₁) + 2

/-- The arithmetic content of the cut level: `3 · iwQl ρ l₁ < 2 ^ (cutLevelAux ρ l₁ - 1)`. -/
lemma three_mul_iwQl_lt_two_pow (ρ : ℝ) (l₁ : ℕ) :
    3 * Work.Analysis.IonescuWainger.iwQl ρ l₁ < 2 ^ (cutLevelAux ρ l₁ - 1) := by
  have h2 : cutLevelAux ρ l₁ - 1 = Nat.clog 2 (3 * Work.Analysis.IonescuWainger.iwQl ρ l₁) + 1 := by
    simp only [cutLevelAux]
    omega
  rw [h2]
  have hpos : 0 < 3 * Work.Analysis.IonescuWainger.iwQl ρ l₁ := by
    have := Work.Analysis.IonescuWainger.iwQl_pos (ρ := ρ) (l := l₁)
    omega
  have hle : 3 * Work.Analysis.IonescuWainger.iwQl ρ l₁
      ≤ 2 ^ Nat.clog 2 (3 * Work.Analysis.IonescuWainger.iwQl ρ l₁) :=
    Nat.le_pow_clog (by norm_num) (3 * Work.Analysis.IonescuWainger.iwQl ρ l₁)
  calc 3 * Work.Analysis.IonescuWainger.iwQl ρ l₁
        ≤ 2 ^ Nat.clog 2 (3 * Work.Analysis.IonescuWainger.iwQl ρ l₁) := hle
    _ < 2 ^ (Nat.clog 2 (3 * Work.Analysis.IonescuWainger.iwQl ρ l₁) + 1) :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)

/-! ## `ℓᵖ`-membership gives boundedness -/

private theorem enorm_rpow_eq_ofReal' (z : ℂ) (q : ℝ) (hq : 0 ≤ q) :
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

/-! ## The deep-range maximal bound -/

/-- **The deep-range maximal bound, with a local copy of the cut level.**  This is
`Work.KMTAreas.A7Hi2.supDeepLe` with `cutLevelAux` in place of `cutLevel`; the two definitions are
definitionally equal. -/
theorem supDeepLe_aux (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p)
    (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ =>
          ⨆ (n : ℕ) (_ : cutLevelAux ρ l₁ ≤ m₀ + n),
            ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ)
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  have hpR : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  have hpR0 : (0 : ℝ) < p.toReal := lt_trans zero_lt_one hpR
  obtain ⟨CρS, _hCρSpos, CS, hCSpos, hS⟩ :=
    Work.KMTAreas.A7.kmtProj_lp_bound_uniform ρ hρ hρ1 p.toReal hpR
  obtain ⟨C2, hC2pos, hD⟩ := Work.A7Hi2.decimDilVarUnif
    Work.KMTAreas.A7Hi2.dilVarRealScale_prop Work.KMTAreas.A7Hi.kmtPhiSch (3 : NNReal)
    (by norm_num) p.toReal hpR
  have hpne0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpnetop : p ≠ ⊤ := ne_of_lt hptop
  have hCpos : (0 : ℝ) < C2 * CS := by positivity
  refine ⟨CρS + 1, by linarith, C2 * CS, hCpos, ?_⟩
  intro l₁ m₀ hgood f
  by_cases hftop : MeasureTheory.eLpNorm f p MeasureTheory.Measure.count = ⊤
  · rw [hftop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hCpos)]
    exact le_top
  · have hpeq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hpnetop
    rw [← hpeq]
    have hfle : MeasureTheory.eLpNorm f (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count < ⊤ := by
      rw [hpeq]; exact lt_top_iff_ne_top.mpr hftop
    obtain ⟨B, hB⟩ := Work.A7Hi2.exists_norm_bound_of_summable_rpow hpR0
      (summable_norm_pow_of_eLpNorm_lt_top hpR0 hfle)
    -- ### the arithmetic data
    set Q : ℕ := Work.Analysis.IonescuWainger.iwQl ρ l₁ with hQdef
    set K : ℕ := cutLevelAux ρ l₁ - 1 with hKdef
    set C₀ : ℕ := max K (m₀ - 1) with hC₀def
    have hQ1 : 1 ≤ Q := by rw [hQdef]; exact Work.Analysis.IonescuWainger.iwQl_pos
    have hcut2 : 2 ≤ cutLevelAux ρ l₁ := by simp [cutLevelAux]
    have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ1
    have hQne : ((Q : ℝ)) ≠ 0 := ne_of_gt hQpos
    have hKm : 3 * Q < 2 ^ K := by
      rw [hQdef, hKdef]
      exact three_mul_iwQl_lt_two_pow ρ l₁
    have hC₀geK : K ≤ C₀ := by rw [hC₀def]; exact le_max_left _ _
    have h3Q : 3 * Q < 2 ^ C₀ :=
      lt_of_lt_of_le hKm (Nat.pow_le_pow_right (by norm_num) hC₀geK)
    have hQleC₀ : Q ≤ Work.KMTAreas.A7Hi.lpfScale C₀ 0 := by
      have hpw : Work.KMTAreas.A7Hi.lpfScale C₀ 0 = 2 ^ C₀ := by
        simp only [Work.KMTAreas.A7Hi.lpfScale, Nat.add_zero]
      rw [hpw]
      have h3 : Q ≤ 3 * Q := by
        have h4 := Nat.le_mul_of_pos_right Q (by norm_num : 0 < 3)
        rwa [Nat.mul_comm] at h4
      exact le_of_lt (lt_of_le_of_lt h3 h3Q)
    -- ### the coarse level has good major arcs
    have hgoodC₀ : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρS l₁ (-(C₀ : ℤ)) := by
      rw [Work.Analysis.IonescuWainger.GoodMajorArcs] at hgood ⊢
      push_cast at hgood ⊢
      have h2ρ : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l₁ : ℝ)) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      by_cases hmK : m₀ ≤ K
      · have hC₀eq : C₀ = K := by
          rw [hC₀def]
          exact max_eq_left (by omega)
        rw [hC₀eq]
        have h1 : (CρS + 1) * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (m₀ : ℝ) := by linarith [hgood]
        have h3 : CρS * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (m₀ : ℝ) := by nlinarith [h1, h2ρ]
        have h2 : (m₀ : ℝ) ≤ (K : ℝ) := by exact_mod_cast hmK
        linarith
      · have hC₀eq : C₀ = m₀ - 1 := by
          rw [hC₀def]
          exact max_eq_right (by omega)
        have hm0pos : 1 ≤ m₀ := by omega
        rw [hC₀eq, Nat.cast_sub hm0pos]
        have h1 : (CρS + 1) * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (m₀ : ℝ) := by linarith [hgood]
        have h3 : CρS * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (m₀ : ℝ) - 1 := by nlinarith [h1, h2ρ]
        simpa using neg_le_neg h3
    -- ### the decimation identity on the deep range
    have hfine : ∀ n : ℕ, cutLevelAux ρ l₁ ≤ m₀ + n → C₀ + 1 ≤ m₀ + n := by
      intro n hn
      have hKcut : K + 1 = cutLevelAux ρ l₁ := by rw [hKdef]; omega
      have h1 : K ≤ m₀ + n - 1 := by omega
      have h2 : m₀ - 1 ≤ m₀ + n - 1 := by omega
      have h3 : C₀ ≤ m₀ + n - 1 := by
        rw [hC₀def]
        exact max_le h1 h2
      omega
    let g : ℤ → ℂ := Work.KMTContract.kmtProj ρ l₁ (-(C₀ : ℤ)) f
    have hident : ∀ n : ℕ, cutLevelAux ρ l₁ ≤ m₀ + n →
        Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f
          = fun y : ℤ => (Q : ℂ) * Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q g
              (m₀ + n - C₀) y := by
      intro n hn
      have hL : C₀ + 1 ≤ m₀ + n := hfine n hn
      have hAT : Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁
          ⊆ Work.KMTPlan.A6.Decim.torsFinset Q := by
        intro α hα
        rw [hQdef]
        exact Work.KMTPlan.A6.DecimComp.mem_torsFinset_of_mem_iwArithFreqs hα
      have h1 : Work.KMTContract.kmtProj ρ l₁ (-(((m₀ + n : ℕ)) : ℤ)) f
          = Work.Analysis.IWMultiplier.iwConv (Work.KMTPlan.A6.Decim.torsFinset Q)
              (Work.KMTPlan.A6.Decim.bump (m₀ + n)) g :=
        Work.KMTAreas.A7G.decimFactBdd ρ l₁ C₀ Q hQ1 hAT h3Q (m₀ + n) hL f hB
      have h2 : Work.Analysis.IWMultiplier.iwConv (Work.KMTPlan.A6.Decim.torsFinset Q)
            (Work.KMTPlan.A6.Decim.bump (m₀ + n)) g
          = fun y : ℤ => (Q : ℂ) * Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q g
              (m₀ + n - C₀) y := by
        funext y
        have h := Work.KMTAreas.A7G.iwConv_torsFinset_eq_smul_decimDilFam Q C₀ (m₀ + n - C₀)
          hQ1 (by omega) g y
        rwa [show C₀ + (m₀ + n - C₀) = m₀ + n from by omega] at h
      rw [Work.KMTAreas.A7Hi.lpf,
        show -((m₀ : ℤ) + (n : ℤ)) = -(((m₀ + n : ℕ)) : ℤ) from by push_cast; ring]
      rw [h1, h2]
    -- ### the pointwise domination by the (first term of the) variational norm
    have hpoint : ∀ x : ℤ,
        (⨆ (n : ℕ) (_ : cutLevelAux ρ l₁ ≤ m₀ + n),
            ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ)
        ≤ ENNReal.ofReal (Q : ℝ) *
            PointwiseErgodicTheorems.variationalNorm 3
              (fun k : ℕ => Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q g k x) := by
      intro x
      refine iSup_le fun n => iSup_le fun hn => ?_
      rw [hident n hn]
      change ‖(Q : ℂ) * Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q g
          (m₀ + n - C₀) x‖ₑ ≤ _
      have hQnorm : ‖((Q : ℂ))‖ₑ = ENNReal.ofReal (Q : ℝ) := by
        rw [← ofReal_norm, Complex.norm_natCast]
      rw [enorm_mul, hQnorm]
      refine mul_le_mul_of_nonneg_left ?_ bot_le
      refine (le_iSup (fun k : ℕ =>
        ‖Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q g k x‖ₑ)
          (m₀ + n - C₀)).trans ?_
      rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
      exact le_add_right le_rfl
    -- ### the two `ℓᵖ` inputs
    have hV : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm 3
          (fun k : ℕ => Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q g k x))
        (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C2 / Q) * MeasureTheory.eLpNorm g (ENNReal.ofReal p.toReal)
            MeasureTheory.Measure.count :=
      hD Q hQ1 C₀ hQleC₀ g
    have hg : MeasureTheory.eLpNorm g (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal CS * MeasureTheory.eLpNorm f (ENNReal.ofReal p.toReal)
            MeasureTheory.Measure.count :=
      hS l₁ (-(C₀ : ℤ)) hgoodC₀ f
    -- ### assembly
    have hpRne0 : ENNReal.ofReal p.toReal ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hpR0
    calc MeasureTheory.eLpNorm (fun x : ℤ =>
            ⨆ (n : ℕ) (_ : cutLevelAux ρ l₁ ≤ m₀ + n),
              ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x‖ₑ)
          (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal (Q : ℝ) *
            PointwiseErgodicTheorems.variationalNorm 3
              (fun k : ℕ => Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q g k x))
            (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count :=
          MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hpoint
      _ = ENNReal.ofReal (Q : ℝ) * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm 3
              (fun k : ℕ => Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q g k x))
            (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count :=
          Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal ENNReal.ofReal_ne_top hpRne0
            ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Q : ℝ) * (ENNReal.ofReal (C2 / Q) *
            MeasureTheory.eLpNorm g (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count) :=
          mul_le_mul_of_nonneg_left hV bot_le
      _ ≤ ENNReal.ofReal (Q : ℝ) * (ENNReal.ofReal (C2 / Q) *
            (ENNReal.ofReal CS * MeasureTheory.eLpNorm f (ENNReal.ofReal p.toReal)
              MeasureTheory.Measure.count)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg bot_le) bot_le
      _ = ENNReal.ofReal (C2 * CS) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count := by
          have h1 : (Q : ℝ) * (C2 / (Q : ℝ)) = C2 := by
            field_simp
          rw [← mul_assoc, ← ENNReal.ofReal_mul hQpos.le, h1,
            ← mul_assoc, ← ENNReal.ofReal_mul hC2pos.le]

end

end Work.KMTAreas.A7Hi2
