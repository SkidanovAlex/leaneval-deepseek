import Mathlib
import Submission.Work.A7Hi2.SieveAssembly
import Submission.Work.KMTAreas.A7Hi.chainPartSqFunOfBandSumSq
import Submission.Port.Aesm

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-! ## Elementary identities for the low-pass family

The two identities below (`varphiN_zero_eq_etaCut`, `Tle_varphiN_zero`) are the *only* place where
the arithmetic height `logN ⌊a ·⌋` enters: they say that the lacunary family
`n ↦ Tle ρ l₁ (varphiN ⌊a n⌋ 0)` of the estimate is literally the family of the Ionescu–Wainger
projections `n ↦ kmtProj ρ l₁ (-(logN ⌊a n⌋))`, i.e. the dyadic low-pass walk
`m ↦ lpf ρ l₁ m₀ m` reindexed by `σ n = (logN ⌊a n⌋ − m₀).toNat`. -/

/-- `varphiN N 0 = etaCut kmtEta (-(logN N))`: the unmodulated low-pass bump at scale `N` is the
continuous cutoff at level `-(logN N)`. -/
theorem varphiN_zero_eq_etaCut (N : ℕ) :
    Work.KMTAreas.A7.varphiN N 0
      = Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
          (-(Work.Analysis.EndVar.logN N)) := by
  funext ξ
  simp only [Work.KMTAreas.A7.varphiN, if_true, Work.Analysis.IonescuWainger.etaCut]
  congr 1
  rw [div_eq_mul_inv, zpow_neg, inv_inv, Real.rpow_intCast]
  ring

/-- `Tle ρ l (varphiN N 0) = kmtProj ρ l (-(logN N))`. -/
@[simp]
theorem Tle_varphiN_zero (ρ : ℝ) (l : ℕ) (N : ℕ) :
    Work.KMTAreas.A7.Tle ρ l (Work.KMTAreas.A7.varphiN N 0)
      = Work.KMTContract.kmtProj ρ l (-(Work.Analysis.EndVar.logN N)) := by
  rw [varphiN_zero_eq_etaCut]
  exact Work.KMTAreas.A7.Tle_etaCut ρ l _

/-- A `Λ`-lacunary sequence with `Λ > 1` and `a n ≥ 1` is monotone. -/
theorem monotone_of_lacunary {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) : Monotone a := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have h2 : Λ < a (n + 1) / a n := ha n
  have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
  have h3 : a n ≤ Λ * a n := by
    simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
  exact le_trans h3 h1.le

/-! ## The chain-part bound, uniform in the base scale `m₀`

`Work.KMTAreas.A7Hi2.eLpNorm_chainPart_le_cardMul` is the tree's absolute chain bound with the
base scale `m₀` moved inside the existential — but the arithmetic height `l₁` is still an *argument*
of the theorem, so its constant may a priori depend on `l₁`.  In this workspace we need *both*
uniformities at once (the target's `K` is fixed before `m`, `l₁`, `a`, `g`), and the proof of the
tree's version already exhibits the constant of the arithmetic-free lacunary variational estimate
`DilVarClean`, which depends only on `ρ`, `r` and `p`; hoisting it out of the `∀ l₁` gives the
uniform form.  The proof below is a verbatim transcription of the tree's, with the `obtain` moved
to the front. -/

theorem chainPart_le_cardMul_uniform (ρ : ℝ) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ) (f : ℤ → ℂ),
      Summable (fun n : ℤ => ‖f n‖ ^ p.toReal) →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((1 + ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)) * C)
            * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  have hp0 : (0 : ℝ) < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one hp)) (ne_of_lt hptop)
  have hp1 : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.ofReal_lt_ofReal_iff hp0, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal (ne_of_lt hptop)]
    exact hp
  obtain ⟨C, hCpos, hC⟩ :=
    Work.KMTAreas.A7Hi.DilVarClean p.toReal hp1 r hr Work.KMTAreas.A7Hi.kmtPhiSch
  refine ⟨C, hCpos, ?_⟩
  intro l₁ m₀ f hf
  have hpt := Work.KMTAreas.A7Hi2.chainPart_le_sum_variationalNorm
    ρ l₁ m₀ r hr p hp hptop f hf
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

/-! ## The target -/

/-- **The low-pass variational estimate for a *bounded* arithmetic height.**

For a fixed height bound `L₁`, and on the good major arcs at the base level, the `R`-variational
norm of the shifted lacunary Ionescu–Wainger walk `n ↦ Tle ρ l₁ (varphiN ⌊a (n + m)⌋ 0) g` is
bounded by a constant (depending on `ρ`, `R`, `Λ` and `L₁`, but **not** on `m`, `l₁ ≤ L₁`, `a` or
`g`) times `‖g‖₂`.

Route (the two bounds are *proved* and are combined here; the poisoned
`Work.KMTAreas.A7.lacunaryIWProjLowpassVar`, which imports the crux
`Work.KMTAreas.A7HiRep.chainPartSqFunPosMemLp` and is therefore axiom-tainted, is *not* used):

* write `sh k = Tle ρ l₁ (varphiN ⌊a (k + m)⌋ 0) g`, which by `Tle_varphiN_zero` is
  `kmtProj ρ l₁ (-(logN ⌊a (k + m)⌋)) g`; with `M : ℕ := (logN ⌊a m⌋).toNat` and
  `σ k := (logN ⌊a (k+m)⌋ - M).toNat` (monotone) this is the walk `k ↦ lpf ρ l₁ M (σ k) g`, a
  monotone *subsequence* of `k ↦ lpf ρ l₁ M k g`, so both `supPart` and `chainPart` of `sh` are
  dominated pointwise by those of the walk (via
  `Work.KMTAreas.A7.variationalNorm_comp_mono_le`);
* `supPart`: `Work.A7Hi2.eLpNorm_supPart_lpf_le_sieveMass_goodMajorArcs` at `p = 2`, with the
  `lpfScale` hypothesis discharged from `GoodMajorArcs`;
* `chainPart`: `chainPart_le_cardMul_uniform` above (the tree's
  `Work.KMTAreas.A7Hi2.eLpNorm_chainPart_le_cardMul`, with `l₁` moved inside so that the constant
  is uniform), constant `C (1 + #A)` with `#A = #(iwArithFreqs ρ l₁)`.

Both constants depend on `l₁` (through `sieveMass ρ l₁` respectively `#(iwArithFreqs ρ l₁)`); since
`l₁ ≤ L₁` ranges over a finite set, the target's `K` is the corresponding finite sum.  The two
pieces are the values part and the chain part of the variational norm, combined with the `ℓ²`
triangle inequality `Work.KMTAreas.A7.eLpNorm_add_le_ennreal`. -/
theorem lowpassSmallHeightCore (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (R : NNReal) (hR : 2 < R)
    (Λ : NNReal) (hΛ : 1 < Λ) (L₁ : ℕ) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (m l₁ : ℕ) (a : ℕ → NNReal) (g : ℤ → ℂ),
        l₁ ≤ L₁ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
        MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁
          (-(Work.Analysis.EndVar.logN (Nat.floor (a m)))) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁
            (Work.KMTAreas.A7.varphiN (Nat.floor (a (n + m))) 0) g x))
          2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal K * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  -- the two proved inputs, with constants free of `l₁` and `m₀`
  obtain ⟨CρS, hCρSpos, CS, hCSpos, hS⟩ :=
    Work.A7Hi2.eLpNorm_supPart_lpf_le_sieveMass_goodMajorArcs ρ hρ hρ1 R 2 (by norm_num)
  obtain ⟨CD, hCDpos, hD⟩ := chainPart_le_cardMul_uniform ρ R hR 2 (by norm_num) (by norm_num)
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
  intro m l₁ a g hl₁ ha ha1 hgmem hgood
  -- the base level and the reindexing
  have hlogNnn : (0 : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a m)) :=
    Work.Analysis.EndVar.logN_nonneg _
  set M : ℕ := (Work.Analysis.EndVar.logN (Nat.floor (a m))).toNat with hMdef
  have hMcoe : ((M : ℕ) : ℤ) = Work.Analysis.EndVar.logN (Nat.floor (a m)) := by
    rw [hMdef]
    exact Int.toNat_of_nonneg hlogNnn
  have hgoodS : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρS l₁ (-(M : ℤ)) := by
    rw [hMcoe]
    exact Work.KMTAreas.A7Hi.goodMajorArcs_mono (le_max_left _ _) hgood
  have hamono : Monotone a := monotone_of_lacunary hΛ ha ha1
  set σ : ℕ → ℕ := fun k =>
    (Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) - (M : ℤ)).toNat with hσdef
  have hMle : ∀ k : ℕ, (M : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) := by
    intro k
    rw [hMcoe]
    exact Work.Analysis.EndVar.logN_mono (Nat.floor_mono (hamono (Nat.le_add_left m k)))
  have hσcoe : ∀ k : ℕ, ((σ k : ℕ) : ℤ)
      = Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) - (M : ℤ) := by
    intro k
    rw [hσdef]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr (hMle k))
  have hσmono : Monotone σ := by
    intro k k' hkk
    have h3 : (0 : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) - (M : ℤ) :=
      sub_nonneg.mpr (hMle k)
    have h4 : (0 : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a (k' + m))) - (M : ℤ) :=
      sub_nonneg.mpr (hMle k')
    have h2 : Work.Analysis.EndVar.logN (Nat.floor (a (k + m)))
        ≤ Work.Analysis.EndVar.logN (Nat.floor (a (k' + m))) :=
      Work.Analysis.EndVar.logN_mono (Nat.floor_mono (hamono (by omega)))
    show ((Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) - (M : ℤ)).toNat)
        ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a (k' + m))) - (M : ℤ)).toNat)
    have hx : (((Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) - (M : ℤ)).toNat : ℕ) : ℤ)
        = Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) - (M : ℤ) := Int.toNat_of_nonneg h3
    have hy : (((Work.Analysis.EndVar.logN (Nat.floor (a (k' + m))) - (M : ℤ)).toNat : ℕ) : ℤ)
        = Work.Analysis.EndVar.logN (Nat.floor (a (k' + m))) - (M : ℤ) := Int.toNat_of_nonneg h4
    have h5 : (((Work.Analysis.EndVar.logN (Nat.floor (a (k + m))) - (M : ℤ)).toNat : ℕ) : ℤ)
        ≤ (((Work.Analysis.EndVar.logN (Nat.floor (a (k' + m))) - (M : ℤ)).toNat : ℕ) : ℤ) := by
      rw [hx, hy]
      omega
    exact_mod_cast h5
  -- the walk of the target is the reindexed dyadic walk, pointwise
  have hTeq : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁
          (Work.KMTAreas.A7.varphiN (Nat.floor (a (n + m))) 0) g x))
      = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTContract.kmtProj ρ l₁
          (-(Work.Analysis.EndVar.logN (Nat.floor (a (n + m))))) g x)) := by
    funext x
    congr 1
    funext n
    rw [Tle_varphiN_zero]
  have hreindex : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTContract.kmtProj ρ l₁
          (-(Work.Analysis.EndVar.logN (Nat.floor (a (n + m))))) g x))
      = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ M mm g x) (σ n))) := by
    funext x
    congr 1
    funext n
    have h1 : (-(Work.Analysis.EndVar.logN (Nat.floor (a (n + m)))) : ℤ)
        = -((M : ℤ) + ((σ n : ℕ) : ℤ)) := by
      rw [hσcoe n]
      ring
    rw [h1]
    rfl
  have hmono : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ M mm g x) (σ n)))
        2 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ M mm g x))
        2 MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by
      simpa only [enorm_eq_self] using
        (Work.KMTAreas.A7.variationalNorm_comp_mono_le
          (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ M mm g x) hσmono))
  by_cases hgtop : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = ⊤
  · rw [hgtop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hKpos)]
    exact le_top
  have hgsum : Summable (fun n : ℤ => ‖g n‖ ^ (2 : ℝ)) := by
    have h := Work.KMTAreas.A7Hi.summable_of_eLpNorm_ne_top (p := (2 : ENNReal)) (u := g)
      (by norm_num) (by norm_num) hgmem.eLpNorm_lt_top
    simpa using h
  -- the two pieces of the dyadic walk
  have h2e : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hsup : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart R
        (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ M mm g x))
        2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (CS * Work.A7Hi2.sieveMass ρ l₁) *
          MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    simpa only [h2e] using hS l₁ M hgoodS g hgsum
  have hchain : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart R
        (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ M mm g x))
        2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal
          ((1 + ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)) * CD) *
          MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
    hD l₁ M g hgsum
  have hKbig : CS * Work.A7Hi2.sieveMass ρ l₁
        + (1 + ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)) * CD
      ≤ CS * Ksup + (1 + Kcard) * CD + 1 := by
    have h1 : Work.A7Hi2.sieveMass ρ l₁ ≤ Ksup := hKsieve l₁ hl₁
    have h2 : ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ) ≤ Kcard :=
      hKcardle l₁ hl₁
    have h3 : CS * Work.A7Hi2.sieveMass ρ l₁ ≤ CS * Ksup :=
      mul_le_mul_of_nonneg_left h1 hCSpos.le
    have h4 : (1 + ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)) * CD
        ≤ (1 + Kcard) * CD :=
      mul_le_mul_of_nonneg_right (by linarith) hCDpos.le
    linarith
  have hdyad : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ M mm g x))
        2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (CS * Ksup + (1 + Kcard) * CD + 1) *
          MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    have hsplit : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ M mm g x))
        = (fun x : ℤ => Work.KMTAreas.A7Hi.supPart R
              (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ M mm g x))
          + (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart R
              (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ M mm g x)) := by
      funext x
      exact Work.KMTAreas.A7Hi.variationalNorm_eq_parts R _
    rw [hsplit]
    refine (Work.KMTAreas.A7.eLpNorm_add_le_ennreal
      (u := fun x : ℤ => Work.KMTAreas.A7Hi.supPart R
        (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ M mm g x))
      (v := fun x : ℤ => Work.KMTAreas.A7Hi.chainPart R
        (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ M mm g x))
      (q := 2) (by norm_num) (by norm_num) (μ := MeasureTheory.Measure.count)).trans ?_
    refine (add_le_add hsup hchain).trans ?_
    have hstep : ENNReal.ofReal (CS * Work.A7Hi2.sieveMass ρ l₁)
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
        + ENNReal.ofReal
            ((1 + ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)) * CD)
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
        = ENNReal.ofReal (CS * Work.A7Hi2.sieveMass ρ l₁
            + (1 + ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)) * CD)
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
      Work.KMTAreas.A7Hi.ofReal_mul_add_eq
        (mul_nonneg hCSpos.le (hsieve_nonneg l₁))
        (mul_nonneg (add_nonneg zero_le_one (Nat.cast_nonneg _)) hCDpos.le) _
    rw [hstep]
    exact mul_le_mul (ENNReal.ofReal_le_ofReal hKbig) le_rfl bot_le bot_le
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁
            (Work.KMTAreas.A7.varphiN (Nat.floor (a (n + m))) 0) g x))
        2 MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ M mm g x) (σ n)))
        2 MeasureTheory.Measure.count := by rw [hTeq, hreindex]
    _ ≤ MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun mm : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ M mm g x))
        2 MeasureTheory.Measure.count := hmono
    _ ≤ ENNReal.ofReal (CS * Ksup + (1 + Kcard) * CD + 1) *
          MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := hdyad

end

end Work.KMTPlan.A6
