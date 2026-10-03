import Mathlib
import Submission.Work.KMTPlan.A6.lowpassSmallHeightCore
import Submission.Work.KMTAreas.A7Hi2.LowpassVarG2
import Submission.Port.Aesm

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators

set_option maxHeartbeats 1000000

/-- **The low-pass variational estimate for a bounded arithmetic height, `g`-side bump.**

Same as `Work.KMTPlan.A6.lowpassSmallHeightCore` but for the *unmodulated `g`-side* bump
`varphitildeN d N 0` (whose projection is `kmtProj ρ l (-(d * logN N))`) and for a general exponent
`p > 1`.  The reindexing base level is `M := (logN ⌊a m⌋).toNat`, and the shifted family
`k ↦ kmtProj ρ l (-(d * logN ⌊a (k+m)⌋))` is the monotone subsequence
`σ k := (d * logN ⌊a (k+m)⌋ - M).toNat` of the walk `mm ↦ lpf ρ l M mm`, which is legitimate
because `logN ⌊a m⌋ ≤ d * logN ⌊a (k+m)⌋`. -/
theorem lowpassSmallHeightShiftG (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (R : NNReal) (hR : 2 < R) (p : ℝ) (hp : 1 < p) (Λ : NNReal) (hΛ : 1 < Λ) (L₁ : ℕ) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (m l : ℕ) (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
        (ha1 : ∀ n : ℕ, 1 ≤ a n), l ≤ L₁ → ∀ (g : ℤ → ℂ),
        Summable (fun k : ℤ => ‖g k‖ ^ p) →
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l
          (-(Work.Analysis.EndVar.logN (Nat.floor (a m)))) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l
              (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (n + m))) 0) g x))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal K * MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hpE : (1 : ENNReal) < ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff hp0).mpr hp
  have hptopE : ENNReal.ofReal p < ⊤ := ENNReal.ofReal_lt_top
  -- the two proved inputs, with constants free of `l` and of the base level
  obtain ⟨CρS, hCρSpos, CS, hCSpos, hS⟩ :=
    Work.A7Hi2.eLpNorm_supPart_lpf_le_sieveMass_goodMajorArcs ρ hρ hρ1 R p hp
  obtain ⟨CD, hCDpos, hD⟩ :=
    chainPart_le_cardMul_uniform ρ R hR (ENNReal.ofReal p) hpE hptopE
  -- the finite bookkeeping over the admissible arithmetic heights
  set Ksup : ℝ := ∑ l ∈ Finset.range (L₁ + 1), Work.A7Hi2.sieveMass ρ l with hKsupdef
  set Kcard : ℝ := ∑ l ∈ Finset.range (L₁ + 1),
      ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ) with hKcarddef
  have hsieve_nonneg : ∀ l : ℕ, 0 ≤ Work.A7Hi2.sieveMass ρ l := by
    intro l
    rw [Work.A7Hi2.sieveMass]
    exact Finset.sum_nonneg fun d _ => abs_nonneg _
  have hKsieve : ∀ l : ℕ, l ≤ L₁ → Work.A7Hi2.sieveMass ρ l ≤ Ksup := by
    intro l hl
    rw [hKsupdef]
    exact Finset.single_le_sum (f := fun l => Work.A7Hi2.sieveMass ρ l)
      (fun i _ => hsieve_nonneg i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))
  have hKcardle : ∀ l : ℕ, l ≤ L₁ →
      ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ) ≤ Kcard := by
    intro l hl
    rw [hKcarddef]
    exact Finset.single_le_sum
      (f := fun l => ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ))
      (fun i _ => Nat.cast_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))
  have hKsupnn : 0 ≤ Ksup := by
    rw [hKsupdef]
    exact Finset.sum_nonneg fun i _ => hsieve_nonneg i
  have hKcardnn : 0 ≤ Kcard := by
    rw [hKcarddef]
    exact Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have hKpos : (0 : ℝ) < CS * Ksup + (1 + Kcard) * CD + 1 := by
    have h1 : 0 ≤ CS * Ksup := mul_nonneg hCSpos.le hKsupnn
    have h2 : 0 < (1 + Kcard) * CD := mul_pos (by linarith) hCDpos
    linarith
  refine ⟨max CρS 1, lt_max_of_lt_left hCρSpos, CS * Ksup + (1 + Kcard) * CD + 1,
    hKpos, ?_⟩
  intro m l a ha ha1 hl g hgsum hgood
  -- the base level `M` and the good major arcs at `-(M : ℤ)`
  have hlogNnn : (0 : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a m)) :=
    Work.Analysis.EndVar.logN_nonneg _
  set M : ℕ := (Work.Analysis.EndVar.logN (Nat.floor (a m))).toNat with hMdef
  have hMcoe : ((M : ℕ) : ℤ) = Work.Analysis.EndVar.logN (Nat.floor (a m)) := by
    rw [hMdef]
    exact Int.toNat_of_nonneg hlogNnn
  have hgoodS : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρS l (-(M : ℤ)) := by
    rw [hMcoe]
    exact Work.KMTAreas.A7Hi.goodMajorArcs_mono (le_max_left _ _) hgood
  have hamono : Monotone a := monotone_of_lacunary hΛ ha ha1
  -- the monotone reindexing `σ`
  set σ : ℕ → ℕ := fun k =>
    ((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) - (M : ℤ)).toNat with hσdef
  have hMle : ∀ k : ℕ, (M : ℤ) ≤ (d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) := by
    intro k
    have h1 : Work.Analysis.EndVar.logN (Nat.floor (a m))
        ≤ Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) :=
      Work.Analysis.EndVar.logN_mono (Nat.floor_mono (hamono (Nat.le_add_left m k)))
    have h2 : (0 : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) :=
      Work.Analysis.EndVar.logN_nonneg _
    calc (M : ℤ) = Work.Analysis.EndVar.logN (Nat.floor (a m)) := hMcoe
      _ ≤ Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) := h1
      _ = (1 : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) := (one_mul _).symm
      _ ≤ (d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hd) h2
  have hσcoe : ∀ k : ℕ, ((σ k : ℕ) : ℤ)
      = (d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) - (M : ℤ) := by
    intro k
    rw [hσdef]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr (hMle k))
  have hσmono : Monotone σ := by
    intro k k' hkk
    have h1 : Nat.floor (a (k + m)) ≤ Nat.floor (a (k' + m)) :=
      Nat.floor_mono (hamono (by omega))
    have h2 : Work.Analysis.EndVar.logN (Nat.floor (a (k + m)))
        ≤ Work.Analysis.EndVar.logN (Nat.floor (a (k' + m))) :=
      Work.Analysis.EndVar.logN_mono h1
    have h2' : (d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (k + m)))
        ≤ (d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (k' + m))) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h3 : (0 : ℤ) ≤ (d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) - (M : ℤ) :=
      sub_nonneg.mpr (hMle k)
    have h4 : (0 : ℤ) ≤ (d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (k' + m))) - (M : ℤ) :=
      sub_nonneg.mpr (hMle k')
    show (((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) - (M : ℤ)).toNat)
        ≤ (((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (k' + m))) - (M : ℤ)).toNat)
    have hx : ((((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) - (M : ℤ)).toNat : ℕ)
          : ℤ)
        = (d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) - (M : ℤ) :=
      Int.toNat_of_nonneg h3
    have hy : ((((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (k' + m))) - (M : ℤ)).toNat : ℕ)
          : ℤ)
        = (d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (k' + m))) - (M : ℤ) :=
      Int.toNat_of_nonneg h4
    have h5 : ((((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) - (M : ℤ)).toNat : ℕ)
          : ℤ)
        ≤ ((((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (k' + m))) - (M : ℤ)).toNat : ℕ)
          : ℤ) := by
      rw [hx, hy]; omega
    exact_mod_cast h5
  -- the target family is the reindexed dyadic walk, pointwise
  have hTeq : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l
          (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (n + m))) 0) g x))
      = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTContract.kmtProj ρ l
          (-((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (n + m))))) g x)) := by
    funext x
    refine congrArg (fun w : ℕ → ℂ => PointwiseErgodicTheorems.variationalNorm R w) ?_
    funext n
    rw [Work.KMTAreas.A7Hi2.Tle_varphitildeN_zero]
  have hreindex : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTContract.kmtProj ρ l
          (-((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (n + m))))) g x))
      = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l M mm g x) (σ n))) := by
    funext x
    refine congrArg (fun w : ℕ → ℂ => PointwiseErgodicTheorems.variationalNorm R w) ?_
    funext n
    have h1 : (-((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (n + m)))) : ℤ)
        = -((M : ℤ) + ((σ n : ℕ) : ℤ)) := by
      rw [hσcoe n]
      ring
    show Work.KMTContract.kmtProj ρ l
          (-((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (n + m))))) g x
        = Work.KMTAreas.A7Hi.lpf ρ l M (σ n) g x
    rw [h1]
    rfl
  have hmono : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l M mm g x) (σ n)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l M mm g x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by
      simpa only [enorm_eq_self] using
        (Work.KMTAreas.A7.variationalNorm_comp_mono_le
          (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l M mm g x) hσmono))
  by_cases hgtop : MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count = ⊤
  · rw [hgtop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hKpos)]
    exact le_top
  -- the two pieces of the dyadic walk
  have hsup : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart R
        (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l M mm g x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (CS * Work.A7Hi2.sieveMass ρ l) *
          MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count :=
    hS l M hgoodS g hgsum
  have hgsum' : Summable (fun n : ℤ => ‖g n‖ ^ (ENNReal.ofReal p).toReal) := by
    rw [ENNReal.toReal_ofReal hp0.le]
    exact hgsum
  have hchain : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart R
        (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l M mm g x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal
          ((1 + ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ)) * CD) *
          MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count :=
    hD l M g hgsum'
  have hKbig : CS * Work.A7Hi2.sieveMass ρ l
        + (1 + ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ)) * CD
      ≤ CS * Ksup + (1 + Kcard) * CD + 1 := by
    have h1 : Work.A7Hi2.sieveMass ρ l ≤ Ksup := hKsieve l hl
    have h2 : ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ) ≤ Kcard :=
      hKcardle l hl
    have h3 : CS * Work.A7Hi2.sieveMass ρ l ≤ CS * Ksup :=
      mul_le_mul_of_nonneg_left h1 hCSpos.le
    have h4 : (1 + ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ)) * CD
        ≤ (1 + Kcard) * CD :=
      mul_le_mul_of_nonneg_right (by linarith) hCDpos.le
    linarith
  have hdyad : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l M mm g x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (CS * Ksup + (1 + Kcard) * CD + 1) *
          MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    have hsplit : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l M mm g x))
        = (fun x : ℤ => Work.KMTAreas.A7Hi.supPart R
              (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l M mm g x))
          + (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart R
              (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l M mm g x)) := by
      funext x
      exact Work.KMTAreas.A7Hi.variationalNorm_eq_parts R _
    rw [hsplit]
    refine (Work.KMTAreas.A7.eLpNorm_add_le_ennreal
      (u := fun x : ℤ => Work.KMTAreas.A7Hi.supPart R
        (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l M mm g x))
      (v := fun x : ℤ => Work.KMTAreas.A7Hi.chainPart R
        (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l M mm g x))
      (q := ENNReal.ofReal p) (le_of_lt hpE) (ne_of_lt hptopE)
      (μ := MeasureTheory.Measure.count)).trans ?_
    refine (add_le_add hsup hchain).trans ?_
    have hstep : ENNReal.ofReal (CS * Work.A7Hi2.sieveMass ρ l)
          * MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count
        + ENNReal.ofReal
            ((1 + ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ)) * CD)
          * MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count
        = ENNReal.ofReal (CS * Work.A7Hi2.sieveMass ρ l
            + (1 + ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l).card : ℝ)) * CD)
          * MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count :=
      Work.KMTAreas.A7Hi.ofReal_mul_add_eq
        (mul_nonneg hCSpos.le (hsieve_nonneg l))
        (mul_nonneg (add_nonneg zero_le_one (Nat.cast_nonneg _)) hCDpos.le) _
    rw [hstep]
    exact mul_le_mul (ENNReal.ofReal_le_ofReal hKbig) le_rfl bot_le bot_le
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l
            (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (n + m))) 0) g x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l M mm g x) (σ n)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count := by rw [hTeq, hreindex]
    _ ≤ MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l M mm g x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count := hmono
    _ ≤ ENNReal.ofReal (CS * Ksup + (1 + Kcard) * CD + 1) *
          MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count := hdyad

end Work.KMTPlan.A6
