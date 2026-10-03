import Mathlib
import Submission.Work.KMTAreas.A7Hi2.cutLevel
import Submission.Work.KMTAreas.A7Hi2.supDeepAux
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Elementary summability helpers (`ℓᵖ`-membership gives boundedness) -/

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

private theorem summable_norm_pow_of_eLpNorm_lt_top' {p : ℝ} (hp : 0 < p) {f : ℤ → ℂ}
    (h : MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count < ⊤) :
    Summable (fun n : ℤ => ‖f n‖ ^ p) := by
  have h' := summable_of_eLpNorm_lt_top' (u := f) (q := ENNReal.ofReal p)
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_lt_top h
  simpa only [ENNReal.toReal_ofReal hp.le] using h'

/-! ## The chain part is dominated by the variational norm -/

/-- **The chain term is dominated by the variational norm** (for every exponent, by
`variationalNorm r a = supPart r a + chainPart r a`). -/
lemma chainPart_le_variationalNorm (r : NNReal) (a : ℕ → ℂ) :
    Work.KMTAreas.A7Hi.chainPart r a ≤ PointwiseErgodicTheorems.variationalNorm r a := by
  rw [Work.KMTAreas.A7Hi.variationalNorm_eq_parts]
  exact le_add_of_nonneg_left bot_le

/-! ## Reindexing and indicator lemmas for the variational norm -/

/-- **Monotone reindexing does not increase the variational norm.**  If `ι : ℕ → ℕ` is monotone
then the sequence `D ∘ ι` is obtained from `D` by deleting entries (or repeating them), so its
`r`-variational norm is at most that of `D`. -/
lemma variationalNorm_comp_mono_le {r : NNReal} (ι : ℕ → ℕ) (hι : Monotone ι) {D : ℕ → ℂ} :
    PointwiseErgodicTheorems.variationalNorm r (fun n => D (ι n))
      ≤ PointwiseErgodicTheorems.variationalNorm r D := by
  rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add,
    Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
  refine add_le_add ?_ ?_
  · exact iSup_le fun n => le_iSup (fun m => ‖D m‖ₑ) (ι n)
  · refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
    refine le_iSup_of_le J (le_iSup_of_le (fun i => ι (N i)) (le_iSup_of_le (hι.comp hN) ?_))
    exact le_of_eq rfl

/-- **The shifted/indicative family.**  If `c - 1 ≤ C₀`, then the family
`n ↦ if c ≤ m₀ + n then z · D (m₀ + n - C₀) else 0` (the deep part of the walk, reindexed by the
shift `C₀`) has variational norm at most `3‖z‖` times that of `D`.

The point is that off the deep range (`n < c - m₀`) the index `m₀ + n - C₀` is truncated to `0`,
so the family is `z • (D ∘ ι) - z • (n ↦ if n < c - m₀ then D 0 else 0)`; the first term is
reindexing (monotone `ι`), and the second is a step. -/
lemma variationalNorm_indicator_shift_le {r : NNReal} (hr : 1 ≤ r) (z : ℂ) (c C₀ m₀ : ℕ)
    (hc : c - 1 ≤ C₀) (D : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if c ≤ m₀ + n then z * D (m₀ + n - C₀) else 0)
      ≤ 3 * ‖z‖ₑ * PointwiseErgodicTheorems.variationalNorm r D := by
  set M : ℕ := c - m₀ with hMdef
  set ι : ℕ → ℕ := fun n => m₀ + n - C₀ with hιdef
  have hιmono : Monotone ι := by
    intro a b hab
    simp only [hιdef]
    omega
  -- off the deep range the index is truncated to `0`
  have hι0 : ∀ n, n < M → ι n = 0 := by
    intro n hn
    have h1 : m₀ + n ≤ c - 1 := by rw [hMdef] at hn; omega
    have h2 : m₀ + n ≤ C₀ := le_trans h1 hc
    simp only [hιdef]
    omega
  -- the target family is the difference of the reindexed family and a step
  have hdecomp : (fun n : ℕ => if c ≤ m₀ + n then z * D (m₀ + n - C₀) else 0)
      = (z • fun n : ℕ => D (ι n)) + ((-z) • fun n : ℕ => if n < M then D 0 else 0) := by
    funext n
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    by_cases hn : n < M
    · have h1 : ¬ (c ≤ m₀ + n) := by rw [hMdef] at hn; omega
      rw [if_neg h1, if_pos hn, hι0 n hn]
      ring
    · have h1 : c ≤ m₀ + n := by rw [hMdef] at hn; omega
      rw [if_pos h1, if_neg hn]
      simp only [hιdef]
      ring
  rw [hdecomp]
  refine (Submission.PointwiseErgodicTheorems.variationalNorm_add_le hr _ _).trans ?_
  rw [Submission.PointwiseErgodicTheorems.variationalNorm_smul hr,
    Submission.PointwiseErgodicTheorems.variationalNorm_smul hr, enorm_neg]
  refine (add_le_add
      (mul_le_mul_of_nonneg_left (variationalNorm_comp_mono_le ι hιmono) bot_le)
      (mul_le_mul_of_nonneg_left
        (Submission.PointwiseErgodicTheorems.variationalNorm_step_le hr M (D 0)) bot_le)).trans ?_
  have h0 : ‖D 0‖ₑ ≤ PointwiseErgodicTheorems.variationalNorm r D :=
    Submission.PointwiseErgodicTheorems.le_variationalNorm r D 0
  have h1 : ‖z‖ₑ * (2 * ‖D 0‖ₑ)
      ≤ ‖z‖ₑ * (2 * PointwiseErgodicTheorems.variationalNorm r D) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h0 (by norm_num)) bot_le
  refine (add_le_add le_rfl h1).trans ?_
  exact le_of_eq (by ring)

/-! ## The deep-range chain bound -/

/-- **The deep-range chain bound for the Ionescu--Wainger low-pass walk, with an `l₁`-free
constant.**

For `0 < ρ ≤ 1`, `2 < r`, `1 < p < ∞` there are `Cρ > 0` and `C > 0` such that for every `l₁`,
every base level `m₀`, on the good major arcs `GoodMajorArcs ρ Cρ l₁ (-(m₀:ℤ))` and every
`f : ℤ → ℂ`, the chain part of the *deep* part of the walk
`n ↦ if cutLevel ρ l₁ ≤ m₀ + n then lpf ρ l₁ m₀ n f x else 0` is bounded by `C * ‖f‖_{ℓᵖ}` — with
**no** loss in the arithmetic height `l₁`.

Route (adapt the PROVED `Work.KMTAreas.A7Hi2.supDeepAux.supDeepLe_aux`, whose file
`Submission/Work/KMTAreas/A7Hi2/supDeepAux.lean` contains the whole arithmetic setup verbatim —
copy it into your own file):

* `Work.KMTAreas.A7G.decimFactBdd` + `Work.KMTAreas.A7G.iwConv_torsFinset_eq_smul_decimDilFam`
  give, on the deep range `cutLevel ρ l₁ ≤ m₀ + n` with `C₀ := max (cutLevel ρ l₁ - 1) (m₀ - 1)`
  and `Q := iwQl ρ l₁`, the identity
  `lpf ρ l₁ m₀ n f = fun y => (Q : ℂ) * Work.A7Hi2.decimDilFam C₀ kmtPhiSch Q g (m₀ + n - C₀) y`
  where `g := kmtProj ρ l₁ (-(C₀ : ℤ)) f` (copy the level bookkeeping: `3 * Q < 2 ^ C₀`,
  `C₀ + 1 ≤ m₀ + n`, and `lpf` agrees with `kmtProj ρ l₁` at the level `-(m₀+n)`);
* `Work.KMTAreas.A7Hi2.decimDilVarUnif` (PROVED, `l₁`-free, constant `C₂ / d`) bounds the
  *variational* norm of the family `k ↦ decimDilFam C₀ kmtPhiSch Q g k` by `(C₂ / Q) * ‖g‖_{ℓᵖ}`;
  **instantiate it at the statement's own `r`** (the witness `∃C` may depend on `r`);
  monotone reindexing (`Work.KMTAreas.A7.variationalNorm_comp_mono_le`, statement
  `V^r(u ∘ φ) ≤ V^r(u)` for `φ` monotone) transports it to `n ↦ decimDilFam C₀ kmtPhiSch Q g
  (m₀ + n - C₀)`;
* the indicator shift `‖V^r(n ↦ if c ≤ m₀+n then z * D (m₀+n-C₀) else 0)‖ ≤ 3‖z‖ * ‖V^r(D)‖` for
  `c - 1 ≤ C₀` is PROVED (as `variationalNorm_indicator_shift_le`) inside the currently
  non-compiling file `Submission/Work/KMTAreas/A7Hi2/deepVarBound.lean`; **copy that result and its
  two helpers (`variationalNorm_comp_mono_le`, and the elementary uses of
  `variationalNorm_step_le` / `le_variationalNorm`) into your own file and fix the one broken
  `rw` at its line 83** (`rw [mul_two, ← add_mul, ...]` must be replaced, since `mul_two` does not
  fire on `‖z‖ₑ * (2 * V)`; `ring` on the `ℝ≥0∞` goal, or the rewrite
  `‖z‖ₑ * (2 * V) = 2 * (‖z‖ₑ * V)` followed by arithmetic, closes it);
* then `chainPart r e ≤ variationalNorm r e` (`Work.KMTAreas.A7Hi2.chainPart_le_variationalNorm`,
  i.e. the chain part is one summand of the variational norm);
* `Work.KMTAreas.A7.kmtProj_lp_bound_uniform` (PROVED, `l₁`-free) bounds `‖g‖_{ℓᵖ} ≤ C * ‖f‖_{ℓᵖ}`
  because the level `-(C₀)` has good major arcs (it is at least as deep as `-m₀`; copy
  `supDeepAux`'s `hgoodC₀` with `CρS` replaced by `Cρ + 1`);
* the `f ∉ ℓᵖ` case is trivial (the right-hand side is `⊤`); `supDeepAux` uses the stepping stone
  `Work.A7Hi2.exists_norm_bound_of_summable_rpow`. -/
theorem deepChainLe (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
          (fun n : ℕ => if Work.KMTAreas.A7Hi2.cutLevel ρ l₁ ≤ m₀ + n
            then Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x else 0))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  have hpR : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  have hpR0 : (0 : ℝ) < p.toReal := lt_trans zero_lt_one hpR
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  obtain ⟨CρS, _hCρSpos, CS, hCSpos, hS⟩ :=
    Work.KMTAreas.A7.kmtProj_lp_bound_uniform ρ hρ hρ1 p.toReal hpR
  obtain ⟨C2, hC2pos, hD⟩ := Work.A7Hi2.decimDilVarUnif
    Work.KMTAreas.A7Hi2.dilVarRealScale_prop Work.KMTAreas.A7Hi.kmtPhiSch r hr p.toReal hpR
  have hpne0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpnetop : p ≠ ⊤ := ne_of_lt hptop
  have hCpos : (0 : ℝ) < 3 * (C2 * CS) := by positivity
  refine ⟨CρS + 1, by linarith, 3 * (C2 * CS), hCpos, ?_⟩
  intro l₁ m₀ hgood f
  by_cases hftop : MeasureTheory.eLpNorm f p MeasureTheory.Measure.count = ⊤
  · rw [hftop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hCpos)]
    exact le_top
  · have hpeq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hpnetop
    rw [← hpeq]
    have hfle : MeasureTheory.eLpNorm f (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count
        < ⊤ := by
      rw [hpeq]; exact lt_top_iff_ne_top.mpr hftop
    obtain ⟨B, hB⟩ := Work.A7Hi2.exists_norm_bound_of_summable_rpow hpR0
      (summable_norm_pow_of_eLpNorm_lt_top' hpR0 hfle)
    -- ### the arithmetic data
    set Q : ℕ := Work.Analysis.IonescuWainger.iwQl ρ l₁ with hQdef
    set cc : ℕ := Work.KMTAreas.A7Hi2.cutLevel ρ l₁ with hccdef
    set C₀ : ℕ := max (cc - 1) (m₀ - 1) with hC₀def
    have hQ1 : 1 ≤ Q := by rw [hQdef]; exact Work.Analysis.IonescuWainger.iwQl_pos
    have hcut2 : 2 ≤ cc := by
      rw [hccdef]
      exact Nat.le_add_left 2 _
    have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ1
    have hcc1 : cc - 1 ≤ C₀ := by rw [hC₀def]; exact le_max_left _ _
    have hKm : 3 * Q < 2 ^ (cc - 1) := by
      rw [hQdef, hccdef]
      exact Work.KMTAreas.A7Hi2.three_mul_iwQl_lt_two_pow ρ l₁
    have h3Q : 3 * Q < 2 ^ C₀ :=
      lt_of_lt_of_le hKm (Nat.pow_le_pow_right (by norm_num) hcc1)
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
      by_cases hmK : m₀ ≤ cc - 1
      · have hC₀eq : C₀ = cc - 1 := by
          rw [hC₀def]
          exact max_eq_left (by omega)
        rw [hC₀eq]
        have h1 : (CρS + 1) * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (m₀ : ℝ) := by linarith [hgood]
        have h3 : CρS * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (m₀ : ℝ) := by nlinarith [h1, h2ρ]
        have h2 : (m₀ : ℝ) ≤ ((cc - 1 : ℕ) : ℝ) := by exact_mod_cast hmK
        linarith
      · have hC₀eq : C₀ = m₀ - 1 := by
          rw [hC₀def]
          exact max_eq_right (by omega)
        have hm0pos : 1 ≤ m₀ := by omega
        rw [hC₀eq, Nat.cast_sub hm0pos]
        have h1 : (CρS + 1) * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (m₀ : ℝ) := by linarith [hgood]
        have h3 : CρS * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (m₀ : ℝ) - 1 := by nlinarith [h1, h2ρ]
        have h4 : -(↑m₀ - 1) ≤ -(CρS * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) := neg_le_neg h3
        simpa only [neg_mul, Nat.cast_one] using h4
    -- ### the decimation identity on the deep range
    have hfine : ∀ n : ℕ, cc ≤ m₀ + n → C₀ + 1 ≤ m₀ + n := by
      intro n hn
      have h1 : cc - 1 ≤ m₀ + n - 1 := by omega
      have h2 : m₀ - 1 ≤ m₀ + n - 1 := by omega
      have h3 : C₀ ≤ m₀ + n - 1 := by
        rw [hC₀def]
        exact max_le h1 h2
      omega
    let g : ℤ → ℂ := Work.KMTContract.kmtProj ρ l₁ (-(C₀ : ℤ)) f
    have hident : ∀ n : ℕ, cc ≤ m₀ + n →
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
    -- ### the coefficient identity `3 * ‖(Q:ℂ)‖ₑ = ofReal (3Q)`
    have hcoef : (3 : ℝ≥0∞) * ‖(Q : ℂ)‖ₑ = ENNReal.ofReal (3 * (Q : ℝ)) := by
      have h1 : ‖(Q : ℂ)‖ₑ = ENNReal.ofReal (Q : ℝ) := by
        rw [← ofReal_norm, Complex.norm_natCast]
      have h2 : (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) := by
        simpa using (ENNReal.ofReal_natCast 3).symm
      rw [h1, h2, ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 3 by norm_num)]
    -- ### the pointwise domination by `3Q` times the variational norm
    have hpc : ∀ x : ℤ,
        Work.KMTAreas.A7Hi.chainPart r
          (fun n : ℕ => if cc ≤ m₀ + n then Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x else 0)
        ≤ ENNReal.ofReal (3 * (Q : ℝ)) *
            PointwiseErgodicTheorems.variationalNorm r
              (fun k : ℕ => Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q g k x) := by
      intro x
      have hEeq : (fun n : ℕ =>
            if cc ≤ m₀ + n then Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x else 0)
          = (fun n : ℕ => if cc ≤ m₀ + n then (Q : ℂ) *
              (fun k : ℕ => Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q g k x)
                (m₀ + n - C₀) else 0) := by
        funext n
        by_cases hn : cc ≤ m₀ + n
        · simp only [if_pos hn]
          exact congrFun (hident n hn) x
        · rw [if_neg hn, if_neg hn]
      have h2 := variationalNorm_indicator_shift_le hr1 (Q : ℂ) cc C₀ m₀ hcc1
        (fun k : ℕ => Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q g k x)
      calc Work.KMTAreas.A7Hi.chainPart r
              (fun n : ℕ => if cc ≤ m₀ + n then Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x else 0)
          ≤ PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ =>
                if cc ≤ m₀ + n then Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x else 0) :=
            chainPart_le_variationalNorm r _
        _ = PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if cc ≤ m₀ + n then (Q : ℂ) *
                (fun k : ℕ => Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q g k x)
                  (m₀ + n - C₀) else 0) := by
            rw [hEeq]
        _ ≤ 3 * ‖(Q : ℂ)‖ₑ * PointwiseErgodicTheorems.variationalNorm r
              (fun k : ℕ => Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q g k x) := h2
        _ = ENNReal.ofReal (3 * (Q : ℝ)) *
              PointwiseErgodicTheorems.variationalNorm r
                (fun k : ℕ => Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q g k x) := by
            rw [hcoef]
    -- ### the two `ℓᵖ` inputs
    have hV : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
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
    calc MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
            (fun n : ℕ => if cc ≤ m₀ + n
              then Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ n f x else 0))
          (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal (3 * (Q : ℝ)) *
            PointwiseErgodicTheorems.variationalNorm r
              (fun k : ℕ => Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q g k x))
            (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count :=
          MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hpc
      _ = ENNReal.ofReal (3 * (Q : ℝ)) * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun k : ℕ => Work.A7Hi2.decimDilFam C₀ Work.KMTAreas.A7Hi.kmtPhiSch Q g k x))
            (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count :=
          Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal ENNReal.ofReal_ne_top hpRne0
            ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (3 * (Q : ℝ)) * (ENNReal.ofReal (C2 / Q) *
            MeasureTheory.eLpNorm g (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count) :=
          mul_le_mul_of_nonneg_left hV bot_le
      _ ≤ ENNReal.ofReal (3 * (Q : ℝ)) * (ENNReal.ofReal (C2 / Q) *
            (ENNReal.ofReal CS * MeasureTheory.eLpNorm f (ENNReal.ofReal p.toReal)
              MeasureTheory.Measure.count)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg bot_le) bot_le
      _ = ENNReal.ofReal (3 * (C2 * CS)) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count := by
          have h1 : (Q : ℝ) * (C2 / (Q : ℝ)) = C2 := by field_simp
          have harith : ((3 * (Q : ℝ)) * (C2 / (Q : ℝ))) * CS = 3 * (C2 * CS) := by
            rw [mul_assoc (3 : ℝ) (Q : ℝ) (C2 / (Q : ℝ)), h1]
            ring
          rw [Work.KMTAreas.A7Hi.ofReal_mul_mul_eq (mul_nonneg (by norm_num) hQpos.le)
                (div_nonneg hC2pos.le hQpos.le),
              Work.KMTAreas.A7Hi.ofReal_mul_mul_eq
                (mul_nonneg (mul_nonneg (by norm_num) hQpos.le)
                  (div_nonneg hC2pos.le hQpos.le)) hCSpos.le,
              harith]

end

end Work.KMTPlan.A6
