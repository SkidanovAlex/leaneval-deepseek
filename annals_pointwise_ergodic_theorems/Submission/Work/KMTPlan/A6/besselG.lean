import Mathlib
import Submission.Work.KMTContract.Defs
import Submission.Work.KMTPlan.A6.iwConvEqIwOpSetMemlp
import Submission.Work.KMTPlan.A6.memlpOfMemLpCount
import Submission.Work.KMTPlan.B.besselMultiplierFamily

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

/-- The frequency circle `ℝ/ℤ` of the Ionescu--Wainger analysis. -/
abbrev Circ_bG : Type := Work.Analysis.IonescuWainger.Circle

/-! ## The rescaled cutoffs `η_{≤k}` and their periodisations -/

theorem continuous_kmtEta : Continuous Work.KMTContract.kmtEta := by
  have h : Continuous fun x : ℝ => (Work.KMTContract.kmtBump x : ℝ) :=
    ContDiffBump.continuous _
  unfold Work.KMTContract.kmtEta
  exact Complex.continuous_ofReal.comp h

theorem measurable_etaCut (k : ℤ) : Measurable (etaCut Work.KMTContract.kmtEta k) :=
  (continuous_kmtEta.comp (continuous_id.div_const _)).measurable

theorem norm_etaCut_le_one (k : ℤ) (x : ℝ) :
    ‖etaCut Work.KMTContract.kmtEta k x‖ ≤ 1 := by
  rw [etaCut, Work.KMTContract.kmtEta]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Work.KMTContract.kmtEta_nonneg _)]
  exact Work.KMTContract.kmtEta_le_one _

theorem etaCut_eq_one_of_le_bG (k : ℤ) {x : ℝ} (h : |x| ≤ (2:ℝ)^(k-1)) :
    etaCut Work.KMTContract.kmtEta k x = 1 := by
  rw [etaCut]
  refine Work.KMTContract.kmtEta_one ?_
  have hpos : (0:ℝ) < (2:ℝ)^k := zpow_pos (by norm_num) k
  have hval : (2:ℝ)^(k-1) / (2:ℝ)^k = 1/2 := by
    rw [← zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0), show k - 1 - k = -1 by ring, zpow_neg_one]
    norm_num
  calc |x / (2:ℝ)^k| = |x| / (2:ℝ)^k := by rw [abs_div, abs_of_pos hpos]
    _ ≤ (2:ℝ)^(k-1) / (2:ℝ)^k := by gcongr
    _ = 1/2 := hval

theorem etaCut_eq_zero_of_le (k : ℤ) {x : ℝ} (h : (2:ℝ)^k ≤ |x|) :
    etaCut Work.KMTContract.kmtEta k x = 0 := by
  rw [etaCut]
  refine Work.KMTContract.kmtEta_zero ?_
  have hpos : (0:ℝ) < (2:ℝ)^k := zpow_pos (by norm_num) k
  calc (1:ℝ) ≤ |x| / (2:ℝ)^k := by rw [one_le_div hpos]; exact h
    _ = |x / (2:ℝ)^k| := by rw [abs_div, abs_of_pos hpos]

/-- The periodisation of the rescaled cutoff `η_{≤k}`: the symbol of `kmtProj ρ l k`. -/
def etSym (k : ℤ) : Circ_bG → ℂ :=
  periodize (etaCut Work.KMTContract.kmtEta k)

theorem memLp_etSym (k : ℤ) : MemLp (etSym k) ⊤ circleMeasure :=
  memLp_periodize (measurable_etaCut k) (R := (2:ℝ)^k) (C := 1)
    (le_of_lt (zpow_pos (by norm_num) k))
    (fun x hx => etaCut_eq_zero_of_le k (le_of_lt hx)) (fun x => norm_etaCut_le_one k x)

theorem memLp_iwSym (A : Finset Circ_bG) (k : ℤ) :
    MemLp (iwSymbolSet A (etSym k)) ⊤ circleMeasure :=
  Work.Analysis.IWMultiplier.memLp_iwSymbolSet A (memLp_etSym k)

theorem iwSymbolSet_sub_bG' (A : Finset Circ_bG) (Φ Ψ : Circ_bG → ℂ) :
    iwSymbolSet A (Φ - Ψ) = iwSymbolSet A Φ - iwSymbolSet A Ψ := by
  funext ξ
  simp only [iwSymbolSet, Pi.sub_apply]
  rw [Finset.sum_sub_distrib]

/-- The rescaled cutoff is a difference of two values in `[0,1]`. -/
theorem norm_etaCut_sub_le_one_bG (k k' : ℤ) (x : ℝ) :
    ‖etaCut Work.KMTContract.kmtEta k x - etaCut Work.KMTContract.kmtEta k' x‖ ≤ 1 := by
  rw [etaCut, etaCut, Work.KMTContract.kmtEta, Work.KMTContract.kmtEta,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor
  · have h1 := Work.KMTContract.kmtEta_nonneg (x / (2:ℝ)^k)
    have h2 := Work.KMTContract.kmtEta_le_one (x / (2:ℝ)^k')
    linarith
  · have h1 := Work.KMTContract.kmtEta_le_one (x / (2:ℝ)^k)
    have h2 := Work.KMTContract.kmtEta_nonneg (x / (2:ℝ)^k')
    linarith

/-- The periodisation of a function supported in `(-2^k, 2^k)` has at most two contributing
terms: the representative and the representative shifted by `-1`. -/
theorem etSym_eq_two_terms (k : ℤ) (hk : (2:ℝ)^k < 1/2) (x : Circ_bG) :
    etSym k x = etaCut Work.KMTContract.kmtEta k ((AddCircle.equivIco (1:ℝ) 0 x).val)
      + etaCut Work.KMTContract.kmtEta k ((AddCircle.equivIco (1:ℝ) 0 x).val - 1) := by
  have hk1 : (2:ℝ)^k < 1 := lt_trans hk (by norm_num)
  rw [etSym, periodize, tsum_eq_sum (s := ({0, -1} : Finset ℤ)) ?_]
  swap
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    obtain ⟨h0, hm1⟩ := hj
    have hy := (AddCircle.equivIco (1:ℝ) 0 x).2
    rw [Set.mem_Ico] at hy
    have h2 : (1:ℝ) ≤ |(AddCircle.equivIco (1:ℝ) 0 x).val + j| := by
      have hcase : (1:ℝ) ≤ (j:ℝ) ∨ (j:ℝ) ≤ -2 := by
        by_cases h : 0 ≤ j
        · exact Or.inl (by exact_mod_cast (show 1 ≤ j by omega))
        · push_neg at h
          exact Or.inr (by exact_mod_cast (show j ≤ -2 by omega))
      rcases hcase with h | h
      · rw [abs_of_nonneg (by linarith [hy.1])]
        linarith [hy.1]
      · rw [abs_of_neg (by linarith [hy.2])]
        linarith [hy.2]
    exact etaCut_eq_zero_of_le k (le_of_lt (lt_of_lt_of_le hk1 h2))
  rw [Finset.sum_pair (by decide : (0:ℤ) ≠ -1)]
  simp only [Int.cast_zero, Int.cast_neg, Int.cast_one, add_zero, sub_eq_add_neg]

theorem etaCut_diff_support {m m' : ℤ} (hm : m' ≤ m) {x : ℝ}
    (h : etaCut Work.KMTContract.kmtEta m x - etaCut Work.KMTContract.kmtEta m' x ≠ 0) :
    (2:ℝ)^(m'-1) < |x| ∧ |x| < (2:ℝ)^m := by
  constructor
  · by_contra hx
    rw [not_lt] at hx
    refine h ?_
    have h1 : etaCut Work.KMTContract.kmtEta m x = 1 :=
      etaCut_eq_one_of_le_bG m (hx.trans (zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)))
    have h2 : etaCut Work.KMTContract.kmtEta m' x = 1 := etaCut_eq_one_of_le_bG m' hx
    rw [h1, h2, sub_self]
  · by_contra hx
    rw [not_lt] at hx
    refine h ?_
    have h1 : etaCut Work.KMTContract.kmtEta m x = 0 := etaCut_eq_zero_of_le m hx
    have h2 : etaCut Work.KMTContract.kmtEta m' x = 0 :=
      etaCut_eq_zero_of_le m' (le_trans (zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hm) hx)
    rw [h1, h2, sub_self]

/-- The support of the periodised annulus `Φ_m − Φ_{m'}`. -/
theorem etSym_sub_support {m m' : ℤ} (hm : m' ≤ m) (hm2 : (2:ℝ)^m < 1/2) {x : Circ_bG}
    (h : etSym m x - etSym m' x ≠ 0) :
    ∃ θ : ℝ, (θ : Circ_bG) = x ∧ (2:ℝ)^(m'-1) < |θ| ∧ |θ| < (2:ℝ)^m := by
  have hm'2 : (2:ℝ)^(m') < 1/2 := lt_of_le_of_lt (zpow_le_zpow_right₀ (by norm_num) hm) hm2
  set y : ℝ := (AddCircle.equivIco (1:ℝ) 0 x).val with hydef
  have hx : etSym m x - etSym m' x
      = (etaCut Work.KMTContract.kmtEta m y - etaCut Work.KMTContract.kmtEta m' y)
        + (etaCut Work.KMTContract.kmtEta m (y - 1)
            - etaCut Work.KMTContract.kmtEta m' (y - 1)) := by
    rw [etSym_eq_two_terms m hm2 x, etSym_eq_two_terms m' hm'2 x, hydef]
    ring
  rw [hx] at h
  have key : etaCut Work.KMTContract.kmtEta m y - etaCut Work.KMTContract.kmtEta m' y ≠ 0
      ∨ etaCut Work.KMTContract.kmtEta m (y - 1)
          - etaCut Work.KMTContract.kmtEta m' (y - 1) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (by rw [hc.1, hc.2, add_zero])
  rcases key with h1 | h1
  · obtain ⟨hlo, hhi⟩ := etaCut_diff_support hm h1
    exact ⟨y, by rw [hydef, AddCircle.coe_equivIco], hlo, hhi⟩
  · obtain ⟨hlo, hhi⟩ := etaCut_diff_support hm h1
    refine ⟨y - 1, ?_, hlo, hhi⟩
    have hneg : (((-1 : ℝ)) : Circ_bG) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨-1, by simp⟩
    rw [show y - 1 = y + (-1) by ring, AddCircle.coe_add, hydef, AddCircle.coe_equivIco, hneg,
      add_zero]

/-- The periodised annulus `Φ_m − Φ_{m'}` is bounded by `1`. -/
theorem etSym_sub_norm_le {m m' : ℤ} (hm : m' ≤ m) (hm2 : (2:ℝ)^m < 1/2) (x : Circ_bG) :
    ‖etSym m x - etSym m' x‖ ≤ 1 := by
  have hm'2 : (2:ℝ)^(m') < 1/2 := lt_of_le_of_lt (zpow_le_zpow_right₀ (by norm_num) hm) hm2
  set y : ℝ := (AddCircle.equivIco (1:ℝ) 0 x).val with hydef
  have hx : etSym m x - etSym m' x
      = (etaCut Work.KMTContract.kmtEta m y - etaCut Work.KMTContract.kmtEta m' y)
        + (etaCut Work.KMTContract.kmtEta m (y - 1)
            - etaCut Work.KMTContract.kmtEta m' (y - 1)) := by
    rw [etSym_eq_two_terms m hm2 x, etSym_eq_two_terms m' hm'2 x, hydef]
    ring
  have hA : ‖etaCut Work.KMTContract.kmtEta m y - etaCut Work.KMTContract.kmtEta m' y‖ ≤ 1 :=
    norm_etaCut_sub_le_one_bG m m' y
  have hB : ‖etaCut Work.KMTContract.kmtEta m (y - 1)
      - etaCut Work.KMTContract.kmtEta m' (y - 1)‖ ≤ 1 := norm_etaCut_sub_le_one_bG m m' (y - 1)
  have hnotboth : etaCut Work.KMTContract.kmtEta m y - etaCut Work.KMTContract.kmtEta m' y = 0
      ∨ etaCut Work.KMTContract.kmtEta m (y - 1)
          - etaCut Work.KMTContract.kmtEta m' (y - 1) = 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨l1, u1⟩ := etaCut_diff_support hm hc.1
    obtain ⟨l2, u2⟩ := etaCut_diff_support hm hc.2
    have hlt : (1:ℝ) < 1 := by
      calc (1:ℝ) = |y - (y - 1)| := by norm_num
        _ ≤ |y - 0| + |0 - (y - 1)| := abs_sub_le y 0 (y - 1)
        _ = |y| + |y - 1| := by rw [sub_zero, zero_sub, abs_neg]
        _ < (2:ℝ)^m + (2:ℝ)^m := add_lt_add u1 u2
        _ < 1 := by linarith
    exact lt_irrefl _ hlt
  rw [hx]
  rcases hnotboth with h | h
  · rw [h, zero_add]; exact hB
  · rw [h, add_zero]; exact hA

/-! ## The arithmetic frequency set of exact height, and the symbol of the piece -/

/-- The arithmetic frequencies of height exactly `l₂`. -/
def pieceFreqs (ρ : ℝ) (l₂ : ℕ) : Finset Circ_bG :=
  if l₂ = 0 then iwArithFreqs ρ 0 else iwArithFreqs ρ l₂ \ iwArithFreqs ρ (l₂ - 1)

theorem pieceFreqs_subset (ρ : ℝ) (l₂ : ℕ) : pieceFreqs ρ l₂ ⊆ iwArithFreqs ρ l₂ := by
  unfold pieceFreqs
  by_cases h : l₂ = 0
  · rw [if_pos h, h]
  · rw [if_neg h]; exact Finset.sdiff_subset

theorem NonAliasing.mono_bG {K : ℤ} {A B : Finset Circ_bG} (hBA : B ⊆ A) (hA : NonAliasing K A) :
    NonAliasing K B :=
  fun α hα β hβ θ hθ θ' hθ' heq => hA α (hBA hα) β (hBA hβ) θ hθ θ' hθ' heq

/-- The pointwise symbol of the §5 piece `Gpiece (kmtPj ρ) d 0 l₂ k₂ N`. -/
def gSym (ρ : ℝ) (d : ℤ) (l₂ : ℕ) (k₂ : ℤ) (N : ℕ) : Circ_bG → ℂ :=
  iwSymbolSet (pieceFreqs ρ l₂)
    (etSym (d * (-(Work.Analysis.EndVar.logN N) + k₂))
      - etSym (d * (-(Work.Analysis.EndVar.logN N) + k₂) - d))

theorem memLp_gSym (ρ : ℝ) (d : ℤ) (l₂ : ℕ) (k₂ : ℤ) (N : ℕ) :
    MemLp (gSym ρ d l₂ k₂ N) ⊤ circleMeasure :=
  Work.Analysis.IWMultiplier.memLp_iwSymbolSet _
    ((memLp_etSym _).sub (memLp_etSym _))

/-- The support of the symbol of the `G`-piece. -/
theorem gSym_support {ρ : ℝ} {d : ℤ} (hd : 0 ≤ d) {l₂ : ℕ} {k₂ : ℤ} {N : ℕ}
    (h2 : (2:ℝ)^(d * (-(Work.Analysis.EndVar.logN N) + k₂)) < 1/2) {ξ : Circ_bG}
    (h : gSym ρ d l₂ k₂ N ξ ≠ 0) :
    ∃ α ∈ pieceFreqs ρ l₂, ∃ θ : ℝ, (θ : Circ_bG) = ξ - α ∧
      (2:ℝ)^(d * (-(Work.Analysis.EndVar.logN N) + k₂) - d - 1) < |θ| ∧
      |θ| < (2:ℝ)^(d * (-(Work.Analysis.EndVar.logN N) + k₂)) := by
  rw [gSym, iwSymbolSet_apply] at h
  obtain ⟨α, hα, hne⟩ : ∃ α ∈ pieceFreqs ρ l₂,
      (etSym (d * (-(Work.Analysis.EndVar.logN N) + k₂))
        - etSym (d * (-(Work.Analysis.EndVar.logN N) + k₂) - d)) (ξ - α) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (Finset.sum_eq_zero hc)
  obtain ⟨θ, hθ, hlo, hhi⟩ :=
    etSym_sub_support (m := d * (-(Work.Analysis.EndVar.logN N) + k₂))
      (m' := d * (-(Work.Analysis.EndVar.logN N) + k₂) - d) (by linarith) h2 hne
  exact ⟨α, hα, θ, hθ, hlo, hhi⟩

/-- The symbol of the `G`-piece is bounded by `1` at every frequency. -/
theorem gSym_norm_le {ρ : ℝ} {d : ℤ} (hd : 0 ≤ d) {l₂ : ℕ} {k₂ : ℤ} {N : ℕ}
    (h2 : (2:ℝ)^(d * (-(Work.Analysis.EndVar.logN N) + k₂)) < 1/2)
    (hNA : NonAliasing (d * (-(Work.Analysis.EndVar.logN N) + k₂) + 1) (pieceFreqs ρ l₂))
    (ξ : Circ_bG) :
    ‖gSym ρ d l₂ k₂ N ξ‖ ≤ 1 := by
  set A : ℤ := d * (-(Work.Analysis.EndVar.logN N) + k₂) with hA
  have hsub : A - d ≤ A := by omega
  by_cases hex : ∃ α ∈ pieceFreqs ρ l₂, (etSym A - etSym (A - d)) (ξ - α) ≠ 0
  · obtain ⟨α₀, hα₀, hne₀⟩ := hex
    have huniq : ∀ α ∈ pieceFreqs ρ l₂, (etSym A - etSym (A - d)) (ξ - α) ≠ 0 → α = α₀ := by
      intro α hα hne
      by_contra hne'
      obtain ⟨θ, hθ, hlo, hhi⟩ := etSym_sub_support hsub h2 hne
      obtain ⟨θ', hθ', hlo', hhi'⟩ := etSym_sub_support hsub h2 hne₀
      have hmemθ : θ ∈ realArc (A + 1) := by
        rw [realArc, Set.mem_Icc]
        have hpow : (2:ℝ)^A ≤ (2:ℝ)^(A+1) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        exact ⟨by linarith [neg_le_abs θ, hhi, hpow], by linarith [hhi, hpow, le_abs_self θ]⟩
      have hmemθ' : θ' ∈ realArc (A + 1) := by
        rw [realArc, Set.mem_Icc]
        have hpow : (2:ℝ)^A ≤ (2:ℝ)^(A+1) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        exact ⟨by linarith [neg_le_abs θ', hhi', hpow], by linarith [hhi', hpow, le_abs_self θ']⟩
      have heq : α + (θ : Circ_bG) = α₀ + (θ' : Circ_bG) := by rw [hθ, hθ']; abel
      exact hne' (hNA α hα α₀ hα₀ θ hmemθ θ' hmemθ' heq).1
    rw [gSym, iwSymbolSet_apply,
      Finset.sum_eq_single α₀ (fun α hα hne => by
        by_contra hc
        exact hne (huniq α hα hc)) (fun hnot => absurd hα₀ hnot)]
    exact etSym_sub_norm_le hsub h2 (ξ - α₀)
  · push_neg at hex
    rw [gSym, iwSymbolSet_apply, Finset.sum_eq_zero (fun α hα => hex α hα)]
    simp


/-! ## The piece as a Fourier multiplier -/

theorem multiplier_sub_bG' (m n : Lp ℂ ⊤ circleMeasure) :
    multiplier (m - n) = multiplier m - multiplier n := by
  have h := multiplier_add (m - n) n
  rw [sub_add_cancel] at h
  exact eq_sub_iff_add_eq.mpr h.symm

theorem multiplierOf_sub' {f g : Circ_bG → ℂ} (hf : MemLp f ⊤ circleMeasure)
    (hg : MemLp g ⊤ circleMeasure) (hfg : MemLp (f - g) ⊤ circleMeasure) :
    multiplierOf (f - g) hfg = multiplierOf f hf - multiplierOf g hg := by
  show multiplier (hfg.toLp (f - g)) = multiplier (hf.toLp f) - multiplier (hg.toLp g)
  have hproof : hfg = MemLp.sub hf hg := Subsingleton.elim _ _
  rw [show hfg.toLp (f - g) = (MemLp.sub hf hg).toLp (f - g) by rw [hproof],
    MemLp.toLp_sub hf hg]
  exact multiplier_sub_bG' _ _

theorem multiplierOf_congr_bG' {f g : Circ_bG → ℂ} (hf : MemLp f ⊤ circleMeasure)
    (hg : MemLp g ⊤ circleMeasure) (h : f = g) :
    multiplierOf f hf = multiplierOf g hg := by
  simp only [multiplierOf]
  rw [MemLp.toLp_congr hf hg (Filter.Eventually.of_forall (fun ξ => congrFun h ξ))]

/-- The pointwise symbol of the exact-height projection `piExact`. -/
def piSym (ρ : ℝ) (l : ℕ) (c : ℤ) : Circ_bG → ℂ :=
  iwSymbolSet (pieceFreqs ρ l) (etSym c)

theorem memLp_piSym (ρ : ℝ) (l : ℕ) (c : ℤ) : MemLp (piSym ρ l c) ⊤ circleMeasure :=
  memLp_iwSym _ _

theorem piSym_eq (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) (c : ℤ) :
    piSym ρ l c = if l = 0 then iwSymbolSet (iwArithFreqs ρ 0) (etSym c)
      else iwSymbolSet (iwArithFreqs ρ l) (etSym c)
        - iwSymbolSet (iwArithFreqs ρ (l - 1)) (etSym c) := by
  by_cases hl : l = 0
  · subst hl
    simp [piSym, pieceFreqs]
  · rw [if_neg hl, piSym, pieceFreqs, if_neg hl]
    have hsub : iwArithFreqs ρ (l - 1) ⊆ iwArithFreqs ρ l :=
      iwArithFreqs_mono hρ hρ1 (by omega)
    have h := iwSymbolSet_sdiff (iwArithFreqs ρ l) (iwArithFreqs ρ (l - 1)) hsub (etSym c)
    rw [h]
    abel

theorem piExact_eq_multiplier (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) (c : ℤ) (F : L2Z) :
    Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c (⇑F)
      = ⇑(multiplierOf (piSym ρ l c) (memLp_piSym ρ l c) F) := by
  by_cases hl : l = 0
  · subst hl
    rw [Work.Analysis.EndVar.piExact, if_pos rfl]
    simp only [Work.KMTContract.kmtPj_proj]
    have h : Work.KMTContract.kmtProj ρ 0 c (⇑F)
        = ⇑(multiplierOf (iwSymbolSet (iwArithFreqs ρ 0) (etSym c)) (memLp_iwSym _ c) F) :=
      iwConvEqIwOpSetMemlp (memLp_iwSym _ c) F
    have hclm : multiplierOf (iwSymbolSet (iwArithFreqs ρ 0) (etSym c)) (memLp_iwSym _ c)
        = multiplierOf (piSym ρ 0 c) (memLp_piSym ρ 0 c) :=
      (multiplierOf_congr_bG' (memLp_piSym ρ 0 c) (memLp_iwSym (iwArithFreqs ρ 0) c)
        (by simp [piSym, pieceFreqs])).symm
    rw [h, ← hclm]
  · rw [Work.Analysis.EndVar.piExact, if_neg hl]
    simp only [Work.KMTContract.kmtPj_proj]
    have h1 : Work.KMTContract.kmtProj ρ l c (⇑F)
        = ⇑(multiplierOf (iwSymbolSet (iwArithFreqs ρ l) (etSym c)) (memLp_iwSym _ c) F) :=
      iwConvEqIwOpSetMemlp (memLp_iwSym _ c) F
    have h2 : Work.KMTContract.kmtProj ρ (l - 1) c (⇑F)
        = ⇑(multiplierOf (iwSymbolSet (iwArithFreqs ρ (l - 1)) (etSym c)) (memLp_iwSym _ c) F) :=
      iwConvEqIwOpSetMemlp (memLp_iwSym _ c) F
    have hclm : multiplierOf (iwSymbolSet (iwArithFreqs ρ l) (etSym c)) (memLp_iwSym _ c)
        - multiplierOf (iwSymbolSet (iwArithFreqs ρ (l - 1)) (etSym c)) (memLp_iwSym _ c)
        = multiplierOf (piSym ρ l c) (memLp_piSym ρ l c) := by
      rw [← multiplierOf_sub' (memLp_iwSym (iwArithFreqs ρ l) c)
        (memLp_iwSym (iwArithFreqs ρ (l - 1)) c)
        ((memLp_iwSym (iwArithFreqs ρ l) c).sub (memLp_iwSym (iwArithFreqs ρ (l - 1)) c))]
      exact multiplierOf_congr_bG' _ _ (by rw [piSym_eq ρ hρ hρ1 l c, if_neg hl])
    rw [h1, h2, ← hclm, ContinuousLinearMap.sub_apply, lp.coeFn_sub]


theorem gSym_eq_piSym_sub (ρ : ℝ) (d : ℤ) (l₂ : ℕ) (k₂ : ℤ) (N : ℕ) :
    gSym ρ d l₂ k₂ N = piSym ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂))
      - piSym ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂) - d) := by
  rw [gSym, piSym, piSym, ← iwSymbolSet_sub_bG']

/-- The `ℓ²` element attached to a function in `ℓ²(ℤ)`. -/
noncomputable def toL2Z {g : ℤ → ℂ} (hg : MemLp g 2 Measure.count) : L2Z :=
  ⟨g, memlpOfMemLpCount (by norm_num) (by norm_num) hg⟩

@[simp] theorem toL2Z_coe {g : ℤ → ℂ} (hg : MemLp g 2 Measure.count) :
    ⇑(toL2Z hg) = g := rfl

/-- The §5 piece `Gpiece (kmtPj ρ) d 0 l₂ k₂ N` is the Fourier multiplier with symbol `gSym`. -/
theorem piece_eq_gSym (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (d : ℤ) (l₂ : ℕ) (k₂ : ℤ)
    (hk₂ : k₂ ≠ 0) (N : ℕ) (F : L2Z) :
    Work.Analysis.EndVar.Gpiece (Work.KMTContract.kmtPj ρ) d 0 l₂ k₂ N (⇑F)
      = ⇑(multiplierOf (gSym ρ d l₂ k₂ N) (memLp_gSym ρ d l₂ k₂ N) F) := by
  rw [Work.Analysis.EndVar.Gpiece_eq]
  rw [Work.Analysis.EndVar.piece_of_ne (by simpa using hk₂ :
    k₂ ≠ -((0 : ℕ) : ℤ))]
  rw [show d * (-(Work.Analysis.EndVar.logN N) + (k₂ - 1))
      = d * (-(Work.Analysis.EndVar.logN N) + k₂) - d by ring]
  rw [piExact_eq_multiplier ρ hρ hρ1 l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂)) F,
    piExact_eq_multiplier ρ hρ hρ1 l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂) - d) F]
  have hclm : multiplierOf (piSym ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂)))
        (memLp_piSym ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂)))
      - multiplierOf (piSym ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂) - d))
        (memLp_piSym ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂) - d))
      = multiplierOf (gSym ρ d l₂ k₂ N) (memLp_gSym ρ d l₂ k₂ N) := by
    rw [← multiplierOf_sub' (memLp_piSym ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂)))
      (memLp_piSym ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂) - d))
      ((memLp_piSym ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂))).sub
        (memLp_piSym ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂) - d)))]
    exact multiplierOf_congr_bG' _ _ (gSym_eq_piSym_sub ρ d l₂ k₂ N).symm
  rw [← hclm, ContinuousLinearMap.sub_apply, lp.coeFn_sub]


/-! ## Counting the scales in a dyadic window -/

theorem zpow_lt_of_lt {a b : ℤ} (h : (2:ℝ)^a < (2:ℝ)^b) : a < b := by
  by_contra hc
  push_neg at hc
  exact absurd h (not_lt.mpr (zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hc))

theorem jj_close {d : ℕ} (hd : 1 ≤ d) {j j₀ : ℤ}
    (h : (d : ℤ) * |j₀ - j| < (d : ℤ) + 1) : j = j₀ ∨ j = j₀ - 1 ∨ j = j₀ + 1 := by
  have h1 : |j₀ - j| ≤ 1 := by
    by_contra hc
    push_neg at hc
    have h2 : (2:ℤ) ≤ |j₀ - j| := by omega
    have hd0 : (0:ℤ) ≤ (d:ℤ) := by positivity
    have hle : (d:ℤ) * 2 ≤ (d:ℤ) * |j₀ - j| := mul_le_mul_of_nonneg_left h2 hd0
    have hd1 : (1:ℤ) ≤ (d:ℤ) := by exact_mod_cast hd
    omega
  have h2 := (abs_le.mp h1).1
  have h3 := (abs_le.mp h1).2
  omega

/-- A lacunary sequence meets each dyadic level `j ≥ 2` at most `⌈log_Λ 2⌉ + 2` times. -/
theorem logN_count {Λ : ℝ≥0} (hΛ : 1 < Λ) {a : ℕ → ℝ≥0}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
    (s : Finset ℕ) {j : ℤ} (hj : 2 ≤ j) :
    (s.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n)) = j)).card
      ≤ Nat.ceil (Real.logb (Λ : ℝ) 2) + 2 := by
  have hΛR : (1:ℝ) < (Λ:ℝ) := by exact_mod_cast hΛ
  have hlogΛ : 0 < Real.log (Λ:ℝ) := Real.log_pos hΛR
  set F : Finset ℕ := s.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n)) = j) with hF
  have hmul : ∀ n, (Λ:ℝ) * (a n : ℝ) ≤ (a (n+1) : ℝ) := by
    intro n
    have hpos : (0:ℝ) < (a n : ℝ) := by
      have : (0:ℝ≥0) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
      exact_mod_cast this
    have h := ha n
    have h' : (Λ:ℝ) < ((a (n+1) : ℝ)) / (a n : ℝ) := by
      have h2 := NNReal.coe_lt_coe.mpr h
      rwa [NNReal.coe_div] at h2
    exact le_of_lt ((lt_div_iff₀ hpos).mp h')
  have hgrowth : ∀ n m : ℕ, (Λ:ℝ)^m * (a n : ℝ) ≤ (a (n+m) : ℝ) := by
    intro n m
    induction m with
    | zero => simp
    | succ k ih =>
      calc (Λ:ℝ)^(k+1) * (a n : ℝ) = (Λ:ℝ) * ((Λ:ℝ)^k * (a n : ℝ)) := by ring
        _ ≤ (Λ:ℝ) * (a (n+k) : ℝ) := mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ (a ((n+k)+1) : ℝ) := hmul (n+k)
        _ = (a (n+(k+1)) : ℝ) := by rw [show n + (k+1) = (n+k)+1 by omega]
  have hwin : ∀ n ∈ F, (2:ℝ)^j.toNat ≤ (a n : ℝ) ∧ (a n : ℝ) < (2:ℝ)^(j.toNat+1) := by
    intro n hn
    have hl : Work.Analysis.EndVar.logN (Nat.floor (a n)) = j := (Finset.mem_filter.mp hn).2
    have hj0 : 0 ≤ j := by omega
    have hl'' : Nat.log 2 (max (Nat.floor (a n)) 2) = j.toNat := by
      have := hl
      simp only [Work.Analysis.EndVar.logN] at this
      omega
    have hp1 : 2 ^ j.toNat ≤ max (Nat.floor (a n)) 2 := by
      have := Nat.pow_log_le_self 2 (by omega : max (Nat.floor (a n)) 2 ≠ 0)
      rwa [hl''] at this
    have hp2 : max (Nat.floor (a n)) 2 < 2 ^ (j.toNat + 1) := by
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (max (Nat.floor (a n)) 2)
      rwa [hl''] at this
    have h2 : (2:ℕ) ≤ 2 ^ j.toNat := by
      calc (2:ℕ) = 2^1 := by norm_num
        _ ≤ 2 ^ j.toNat := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : (4:ℕ) ≤ 2 ^ j.toNat := by
      calc (4:ℕ) = 2^2 := by norm_num
        _ ≤ 2 ^ j.toNat := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : (4:ℕ) ≤ max (Nat.floor (a n)) 2 := le_trans h4 hp1
    have hmax : max (Nat.floor (a n)) 2 = Nat.floor (a n) := by
      rcases max_cases (Nat.floor (a n)) 2 with ⟨he, _⟩ | ⟨he, hle⟩
      · exact he
      · omega
    rw [hmax] at hp1 hp2
    have hfl : (a n : ℝ) < (Nat.floor (a n) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hfl2 : (Nat.floor (a n) : ℝ) ≤ (a n : ℝ) := by
      exact_mod_cast Nat.floor_le (show (0:ℝ≥0) ≤ a n by positivity)
    constructor
    · have : (2:ℝ)^j.toNat ≤ (Nat.floor (a n) : ℝ) := by exact_mod_cast hp1
      linarith
    · have : (Nat.floor (a n) + 1 : ℕ) ≤ 2^(j.toNat+1) := hp2
      have : ((Nat.floor (a n) : ℕ) : ℝ) + 1 ≤ (2:ℝ)^(j.toNat+1) := by
        push_cast
        exact_mod_cast hp2
      linarith
  have hdiam : ∀ n ∈ F, ∀ n' ∈ F, n ≤ n' → n' - n ≤ Nat.ceil (Real.logb (Λ:ℝ) 2) := by
    intro n hn n' hn' hle
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · simp [heq]
    · obtain ⟨hlo, hhi⟩ := hwin n hn
      obtain ⟨hlo', hhi'⟩ := hwin n' hn'
      have hgr := hgrowth n (n' - n)
      rw [Nat.add_sub_cancel' hle] at hgr
      have hpow : (Λ:ℝ)^(n'-n) * (2:ℝ)^j.toNat < (2:ℝ)^(j.toNat+1) := by
        calc (Λ:ℝ)^(n'-n) * (2:ℝ)^j.toNat ≤ (Λ:ℝ)^(n'-n) * (a n : ℝ) :=
              mul_le_mul_of_nonneg_left hlo (by positivity)
          _ ≤ (a n' : ℝ) := hgr
          _ < (2:ℝ)^(j.toNat+1) := hhi'
      have hpos : (0:ℝ) < (2:ℝ)^j.toNat := by positivity
      rw [show (2:ℝ)^(j.toNat+1) = 2 * (2:ℝ)^j.toNat by ring] at hpow
      have h2 : (Λ:ℝ)^(n'-n) < 2 := by
        rw [mul_comm ((Λ:ℝ)^(n'-n)) ((2:ℝ)^j.toNat),
          mul_comm (2:ℝ) ((2:ℝ)^j.toNat)] at hpow
        exact (mul_lt_mul_iff_right₀ hpos).mp hpow
      have hlog : ((n' - n : ℕ) : ℝ) * Real.log (Λ:ℝ) < Real.log 2 := by
        have h := Real.log_lt_log (by positivity) h2
        rwa [Real.log_pow] at h
      have hlt' : ((n' - n : ℕ) : ℝ) < Real.logb (Λ:ℝ) 2 := by
        rw [Real.logb, lt_div_iff₀ hlogΛ]
        exact hlog
      have hfin : ((n' - n : ℕ) : ℝ) < ((Nat.ceil (Real.logb (Λ:ℝ) 2) : ℕ) : ℝ) :=
        lt_of_lt_of_le hlt' (Nat.le_ceil _)
      exact Nat.le_of_lt (by exact_mod_cast hfin)
  rcases Finset.eq_empty_or_nonempty F with hF0 | hne
  · rw [hF0]; simp
  · set n₀ : ℕ := F.min' hne with hn₀def
    have hn₀ : n₀ ∈ F := Finset.min'_mem F hne
    have hsub : F ⊆ (Finset.range (Nat.ceil (Real.logb (Λ:ℝ) 2) + 1)).image (fun k => k + n₀) := by
      intro n hn
      have h1 : n₀ ≤ n := by
        rw [hn₀def]
        have h := (Finset.min'_eq_iff F hne (F.min' hne)).mp rfl
        exact h.2 n hn
      have h2 : n - n₀ ≤ Nat.ceil (Real.logb (Λ:ℝ) 2) := hdiam n₀ hn₀ n hn h1
      rw [Finset.mem_image]
      exact ⟨n - n₀, by rw [Finset.mem_range]; omega, by omega⟩
    calc F.card ≤ ((Finset.range (Nat.ceil (Real.logb (Λ:ℝ) 2) + 1)).image (fun k => k + n₀)).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.range (Nat.ceil (Real.logb (Λ:ℝ) 2) + 1)).card := Finset.card_image_le
      _ = Nat.ceil (Real.logb (Λ:ℝ) 2) + 1 := Finset.card_range _
      _ ≤ Nat.ceil (Real.logb (Λ:ℝ) 2) + 2 := by omega

/-- Convergence of `∑ i : {n // n ∈ s}` to `∑ n ∈ s`. -/
theorem sum_subtype_eq {M : Type*} [AddCommMonoid M] (s : Finset ℕ) (f : ℕ → M) :
    ∑ i : {n // n ∈ s}, f (i : ℕ) = ∑ n ∈ s, f n := by
  conv_rhs => rw [← Finset.sum_attach, Finset.attach_eq_univ]

/-- **The pointwise Bessel inequality for the symbols of the `G`-pieces.** -/
theorem sum_sq_gSym_le {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {Cna : ℝ} (hCna : 0 < Cna)
    (hNA : ∀ (l₁ L : ℕ) (K : ℤ), (K:ℝ) + Cna * (2:ℝ)^(ρ * (max l₁ L : ℝ)) < 0 →
      NonAliasing K (iwArithFreqs ρ l₁ ∪ iwArithFreqs ρ L))
    {d : ℕ} (hd : 1 ≤ d) {l₂ : ℕ} {k₂ : ℤ} (hk₂ : k₂ ≠ 0) {Λ : ℝ≥0} (hΛ : 1 < Λ)
    {a : ℕ → ℝ≥0} (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
    (s : Finset ℕ)
    (hsize : ∀ n ∈ s, (((d : ℤ) * (-(Work.Analysis.EndVar.logN (Nat.floor (a n))) + k₂) : ℤ) : ℝ)
      + Cna * (2:ℝ)^(ρ*(l₂:ℝ)) < -2)
    (hj2 : ∀ n ∈ s, 2 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)))
    (ξ : Circ_bG) :
    ∑ n ∈ s, ‖gSym ρ (d : ℤ) l₂ k₂ (Nat.floor (a n)) ξ‖ ^ 2
      ≤ ((3 * (Nat.ceil (Real.logb (Λ:ℝ) 2) + 2) : ℕ) : ℝ) ^ 2 := by
  set Kc : ℕ := Nat.ceil (Real.logb (Λ:ℝ) 2) + 2 with hKc
  set mm : ℕ → ℤ := fun n => (d : ℤ) * (-(Work.Analysis.EndVar.logN (Nat.floor (a n))) + k₂) with hmm
  have h2m : ∀ n ∈ s, (2:ℝ)^(mm n) < 1/2 := by
    intro n hn
    have hle : mm n ≤ -3 := by
      have hs := hsize n hn
      have hD : (0:ℝ) ≤ (2:ℝ)^(ρ*(l₂:ℝ)) := by positivity
      have hCn : (0:ℝ) ≤ Cna * (2:ℝ)^(ρ*(l₂:ℝ)) := mul_nonneg hCna.le hD
      have h2 : (mm n : ℝ) < -2 := by linarith
      have h3 : mm n < (-2 : ℤ) := by exact_mod_cast h2
      omega
    calc (2:ℝ)^(mm n) ≤ (2:ℝ)^(-3:ℤ) := zpow_le_zpow_right₀ (by norm_num) hle
      _ = 1/8 := by norm_num
      _ < 1/2 := by norm_num
  have hna : ∀ n ∈ s, NonAliasing (mm n + 1) (pieceFreqs ρ l₂) := by
    intro n hn
    have hmono : pieceFreqs ρ l₂ ⊆ iwArithFreqs ρ l₂ ∪ iwArithFreqs ρ l₂ :=
      fun x hx => Finset.mem_union_left _ (pieceFreqs_subset ρ l₂ hx)
    refine NonAliasing.mono_bG hmono ?_
    refine hNA l₂ l₂ (mm n + 1) ?_
    have hs := hsize n hn
    have hD : (0:ℝ) ≤ (2:ℝ)^(ρ*(l₂:ℝ)) := by positivity
    have hCn : (0:ℝ) ≤ Cna * (2:ℝ)^(ρ*(l₂:ℝ)) := mul_nonneg hCna.le hD
    rw [max_self]
    push_cast
    linarith
  have hnorm : ∀ n ∈ s, ‖gSym ρ (d:ℤ) l₂ k₂ (Nat.floor (a n)) ξ‖ ≤ 1 :=
    fun n hn => gSym_norm_le (d := (d:ℤ)) (by positivity) (h2m n hn) (hna n hn) ξ
  set T : Finset ℕ := s.filter (fun n => gSym ρ (d:ℤ) l₂ k₂ (Nat.floor (a n)) ξ ≠ 0) with hT
  have hsupp : ∀ n ∈ T, ∃ α ∈ pieceFreqs ρ l₂, ∃ θ : ℝ, (θ : Circ_bG) = ξ - α ∧
      (2:ℝ)^(mm n - d - 1) < |θ| ∧ |θ| < (2:ℝ)^(mm n) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_filter.mp hn
    exact gSym_support (d := (d:ℤ)) (by positivity) (h2m n hn1) hn2
  have hcount : T.card ≤ 3 * Kc := by
    rcases Finset.eq_empty_or_nonempty T with hT0 | ⟨n₀, hn₀⟩
    · rw [hT0]; simp
    · have hjj : ∀ n ∈ T, Work.Analysis.EndVar.logN (Nat.floor (a n))
          = Work.Analysis.EndVar.logN (Nat.floor (a n₀))
          ∨ Work.Analysis.EndVar.logN (Nat.floor (a n))
            = Work.Analysis.EndVar.logN (Nat.floor (a n₀)) - 1
          ∨ Work.Analysis.EndVar.logN (Nat.floor (a n))
            = Work.Analysis.EndVar.logN (Nat.floor (a n₀)) + 1 := by
        intro n hn
        obtain ⟨α, hα, θ, hθ, hlo, hhi⟩ := hsupp n hn
        obtain ⟨α', hα', θ', hθ', hlo', hhi'⟩ := hsupp n₀ hn₀
        set M : ℤ := max (mm n) (mm n₀) with hM
        have hNA' : NonAliasing (M + 1) (pieceFreqs ρ l₂) :=
          NonAliasing.mono_bG (fun x hx => Finset.mem_union_left _ (pieceFreqs_subset ρ l₂ hx))
            (hNA l₂ l₂ (M + 1) (by
              have hs := hsize n (Finset.mem_filter.mp hn).1
              have hs' := hsize n₀ (Finset.mem_filter.mp hn₀).1
              have hD : (0:ℝ) ≤ (2:ℝ)^(ρ*(l₂:ℝ)) := by positivity
              have hCn : (0:ℝ) ≤ Cna * (2:ℝ)^(ρ*(l₂:ℝ)) := mul_nonneg hCna.le hD
              have h1 : (mm n : ℝ) < -2 - Cna * (2:ℝ)^(ρ*(l₂:ℝ)) := by linarith
              have h2 : (mm n₀ : ℝ) < -2 - Cna * (2:ℝ)^(ρ*(l₂:ℝ)) := by linarith
              have h3 : (M : ℝ) < -2 - Cna * (2:ℝ)^(ρ*(l₂:ℝ)) := by
                rcases max_cases (mm n) (mm n₀) with ⟨he, _⟩ | ⟨he, _⟩
                · rw [hM, he]; exact h1
                · rw [hM, he]; exact h2
              rw [max_self]
              push_cast
              linarith))
        have hmemθ : θ ∈ realArc (M + 1) := by
          rw [realArc, Set.mem_Icc]
          have hpow : (2:ℝ)^(mm n) ≤ (2:ℝ)^(M+1) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
          exact ⟨by linarith [neg_le_abs θ, hhi, hpow], by linarith [hhi, hpow, le_abs_self θ]⟩
        have hmemθ' : θ' ∈ realArc (M + 1) := by
          rw [realArc, Set.mem_Icc]
          have hpow : (2:ℝ)^(mm n₀) ≤ (2:ℝ)^(M+1) :=
            zpow_le_zpow_right₀ (by norm_num) (by omega)
          exact ⟨by linarith [neg_le_abs θ', hhi', hpow], by linarith [hhi', hpow, le_abs_self θ']⟩
        have heq : α + (θ : Circ_bG) = α' + (θ' : Circ_bG) := by rw [hθ, hθ']; abel
        obtain ⟨hαeq, hθeq⟩ := hNA' α hα α' hα' θ hmemθ θ' hmemθ' heq
        have hltn : mm n₀ - d - 1 < mm n := by
          refine zpow_lt_of_lt ?_
          calc (2:ℝ)^(mm n₀ - d - 1) < |θ'| := hlo'
            _ = |θ| := by rw [hθeq]
            _ < (2:ℝ)^(mm n) := hhi
        have hltn' : mm n - d - 1 < mm n₀ := by
          refine zpow_lt_of_lt ?_
          calc (2:ℝ)^(mm n - d - 1) < |θ| := hlo
            _ = |θ'| := by rw [hθeq]
            _ < (2:ℝ)^(mm n₀) := hhi'
        have hkey : (d : ℤ) * |(Work.Analysis.EndVar.logN (Nat.floor (a n₀)))
            - (Work.Analysis.EndVar.logN (Nat.floor (a n)))| < (d : ℤ) + 1 := by
          have h1 : |(mm n : ℤ) - (mm n₀ : ℤ)| < (d : ℤ) + 1 := by
            rw [abs_lt]
            exact ⟨by omega, by omega⟩
          have hdif : (mm n : ℤ) - (mm n₀ : ℤ)
              = (d : ℤ) * ((Work.Analysis.EndVar.logN (Nat.floor (a n₀)))
                  - (Work.Analysis.EndVar.logN (Nat.floor (a n)))) := by
            simp only [hmm]; ring
          rw [hdif, abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ (d:ℤ))] at h1
          exact h1
        exact jj_close hd hkey
      have hsub : T ⊆ (s.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n))
            = Work.Analysis.EndVar.logN (Nat.floor (a n₀)) - 1))
          ∪ ((s.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n))
              = Work.Analysis.EndVar.logN (Nat.floor (a n₀))))
            ∪ (s.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n))
                = Work.Analysis.EndVar.logN (Nat.floor (a n₀)) + 1))) := by
        intro n hn
        have hT1 : n ∈ s := (Finset.mem_filter.mp hn).1
        rcases hjj n hn with h | h | h
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hT1, h⟩))
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hT1, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hT1, h⟩))
      have hcard2 : T.card ≤ (s.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n))
            = Work.Analysis.EndVar.logN (Nat.floor (a n₀)) - 1)).card
          + (s.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n))
            = Work.Analysis.EndVar.logN (Nat.floor (a n₀)))).card
          + (s.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n))
            = Work.Analysis.EndVar.logN (Nat.floor (a n₀)) + 1)).card := by
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_union_le
          (s.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n))
            = Work.Analysis.EndVar.logN (Nat.floor (a n₀)) - 1))
          ((s.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n))
            = Work.Analysis.EndVar.logN (Nat.floor (a n₀))))
            ∪ (s.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n))
              = Work.Analysis.EndVar.logN (Nat.floor (a n₀)) + 1)))
        have h3 := Finset.card_union_le
          (s.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n))
            = Work.Analysis.EndVar.logN (Nat.floor (a n₀))))
          (s.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n))
            = Work.Analysis.EndVar.logN (Nat.floor (a n₀)) + 1))
        omega
      have hc1 : (s.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n))
          = Work.Analysis.EndVar.logN (Nat.floor (a n₀)))).card ≤ Kc := by
        rw [hKc]
        exact logN_count hΛ ha ha1 s (hj := hj2 n₀ (Finset.mem_filter.mp hn₀).1)
      have hc2 : (s.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n))
          = Work.Analysis.EndVar.logN (Nat.floor (a n₀)) + 1)).card ≤ Kc := by
        rw [hKc]
        exact logN_count hΛ ha ha1 s (j := Work.Analysis.EndVar.logN (Nat.floor (a n₀)) + 1)
          (by have := hj2 n₀ (Finset.mem_filter.mp hn₀).1; omega)
      have hc3 : (s.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n))
          = Work.Analysis.EndVar.logN (Nat.floor (a n₀)) - 1)).card ≤ Kc := by
        by_cases h3 : 3 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n₀))
        · rw [hKc]
          exact logN_count hΛ ha ha1 s (j := Work.Analysis.EndVar.logN (Nat.floor (a n₀)) - 1)
            (by omega)
        · have hempty : (s.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n))
              = Work.Analysis.EndVar.logN (Nat.floor (a n₀)) - 1)) = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro n hn
            simp only [Finset.mem_filter] at hn
            have := hj2 n hn.1
            omega
          rw [hempty]; simp only [Finset.card_empty]; omega
      omega
  calc ∑ n ∈ s, ‖gSym ρ (d : ℤ) l₂ k₂ (Nat.floor (a n)) ξ‖ ^ 2
      ≤ ∑ n ∈ s, (if gSym ρ (d : ℤ) l₂ k₂ (Nat.floor (a n)) ξ = 0 then 0 else 1) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        by_cases h : gSym ρ (d : ℤ) l₂ k₂ (Nat.floor (a n)) ξ = 0
        · rw [h, norm_zero]; norm_num
        · rw [if_neg h]
          exact pow_le_one₀ (norm_nonneg _) (hnorm n hn)
    _ = ((T.card : ℕ) : ℝ) := by
        rw [hT, Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl (fun n hn => ?_)
        by_cases h : gSym ρ (d : ℤ) l₂ k₂ (Nat.floor (a n)) ξ = 0
        · simp [h]
        · simp [h]
    _ ≤ ((3 * Kc : ℕ) : ℝ) := by exact_mod_cast hcount
    _ ≤ ((3 * (Nat.ceil (Real.logb (Λ:ℝ) 2) + 2) : ℕ) : ℝ) ^ 2 := by
        rw [← hKc]
        have h1 : (1:ℝ) ≤ ((3 * Kc : ℕ) : ℝ) := by
          have : (1:ℕ) ≤ 3 * Kc := by omega
          exact_mod_cast this
        nlinarith [h1]

/-- The multiplier with zero symbol is zero. -/
theorem multiplierOf_zero_eq (F : L2Z) (h : MemLp (0 : Circ_bG → ℂ) ⊤ circleMeasure) :
    multiplierOf (0 : Circ_bG → ℂ) h F = 0 := by
  have htoLp : h.toLp (0 : Circ_bG → ℂ) = 0 := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp h, Lp.coeFn_zero ℂ ⊤ circleMeasure] with ξ h1 h2
    rw [h1, h2]
  show multiplier (h.toLp 0) F = 0
  rw [htoLp]
  have h2 : fourierZ (multiplier (0 : Lp ℂ ⊤ circleMeasure) F) = 0 := by
    rw [fourierZ_multiplier, Lp.zero_smul]
  calc multiplier (0 : Lp ℂ ⊤ circleMeasure) F
      = fourierZ.symm (fourierZ (multiplier (0 : Lp ℂ ⊤ circleMeasure) F)) :=
        (fourierZ.symm_apply_apply _).symm
    _ = 0 := by rw [h2, map_zero]


/-- Good major arcs imply non-aliasing, for the union of two arithmetic frequency sets. -/
theorem nonAliasing_of_size_bG' (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ L : ℕ) (K : ℤ),
      (K:ℝ) + C * (2:ℝ)^(ρ * (max l₁ L : ℝ)) < 0 →
      NonAliasing K (iwArithFreqs ρ l₁ ∪ iwArithFreqs ρ L) := by
  obtain ⟨Cρ, hCρ, hNA⟩ := exists_goodMajorArcs_nonAliasing hρ
  refine ⟨Cρ, hCρ, fun l₁ L K hK => ?_⟩
  have hgood : GoodMajorArcs ρ Cρ (max l₁ L) K := by
    rw [GoodMajorArcs, Nat.cast_max]
    linarith
  have hunion : iwArithFreqs ρ l₁ ∪ iwArithFreqs ρ L = iwArithFreqs ρ (max l₁ L) := by
    have hmono := iwArithFreqs_mono hρ hρ1
    refine Finset.Subset.antisymm ?_ ?_
    · intro α hα
      rcases Finset.mem_union.mp hα with h | h
      · exact hmono (le_max_left _ _) h
      · exact hmono (le_max_right _ _) h
    · rcases le_total l₁ L with h | h
      · exact fun α hα => Finset.mem_union_right _ (by rwa [max_eq_right h] at hα)
      · exact fun α hα => Finset.mem_union_left _ (by rwa [max_eq_left h] at hα)
  rw [hunion]
  exact hNA (max l₁ L) K hgood

/-- The squared `ℓ²` norm of an `ℓ²(ℤ)` element in terms of its function. -/
theorem eLpNorm_sq_of_L2Z (F : L2Z) :
    (eLpNorm (⇑F) 2 Measure.count) ^ (2:ℕ) = ENNReal.ofReal (‖F‖^2) := by
  rw [Work.Analysis.IWMultiplier.eLpNorm_two_count_eq_ofReal_lpNorm (⇑F) F.2]
  have h : (⟨⇑F, F.2⟩ : L2Z) = F := Subtype.ext rfl
  rw [h, ENNReal.ofReal_pow (norm_nonneg F) 2]

end

theorem besselG (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : ℤ[X]) :
    ∃ (B : ℝ≥0 → ℝ≥0) (C : ℝ), 0 < C ∧
      ∀ (l₂ k₂ : ℕ), 1 ≤ k₂ → ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      ∀ (s : Finset ℕ) (g : ℤ → ℂ), MemLp g 2 Measure.count →
      (∀ n ∈ s, ((max l₂ k₂ : ℕ) : ℝ) + C * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) ≤
          ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) →
      ∑ n ∈ s, (eLpNorm (Work.Analysis.EndVar.Gpiece (Work.KMTContract.kmtPj ρ) (P.natDegree : ℤ)
            0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g) 2 Measure.count) ^ (2 : ℕ)
        ≤ ((B Λ : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ) * (eLpNorm g 2 Measure.count) ^ (2 : ℕ) := by
  classical
  obtain ⟨Cna, hCna, hNA⟩ := nonAliasing_of_size_bG' ρ hρ hρ1
  by_cases hd0 : P.natDegree = 0
  · refine ⟨fun _ => 0, 1, one_pos, ?_⟩
    intro l₂ k₂ hk₂ a Λ hΛ ha ha1 s g hg hcond
    have hpiece : ∀ n ∈ s,
        Work.Analysis.EndVar.Gpiece (Work.KMTContract.kmtPj ρ) ((P.natDegree : ℤ)) 0 l₂
          ((k₂ : ℤ)) (Nat.floor (a n)) g = 0 := by
      intro n hn
      have h1 : Work.Analysis.EndVar.Gpiece (Work.KMTContract.kmtPj ρ)
            ((P.natDegree : ℤ)) 0 l₂ ((k₂ : ℤ)) (Nat.floor (a n)) g
          = ⇑(multiplierOf (gSym ρ ((P.natDegree : ℤ)) l₂ (k₂ : ℤ) (Nat.floor (a n)))
              (memLp_gSym _ _ _ _ _) (toL2Z hg)) :=
        piece_eq_gSym ρ hρ hρ1 ((P.natDegree : ℤ)) l₂ (k₂ : ℤ)
          (by exact_mod_cast (by omega : k₂ ≠ 0)) (Nat.floor (a n)) (toL2Z hg)
      have hsym : gSym ρ ((P.natDegree : ℤ)) l₂ (k₂ : ℤ) (Nat.floor (a n)) = 0 := by
        rw [show ((P.natDegree : ℤ)) = 0 by omega]
        simp [gSym, Work.Analysis.IonescuWainger.iwSymbolSet_zero]
      have h0 : MemLp (0 : Circ_bG → ℂ) ⊤ circleMeasure := by
        have h := memLp_gSym ρ ((P.natDegree : ℤ)) l₂ (k₂ : ℤ) (Nat.floor (a n))
        simpa using h.sub h
      have hz : multiplierOf (gSym ρ ((P.natDegree : ℤ)) l₂ (k₂ : ℤ) (Nat.floor (a n)))
            (memLp_gSym _ _ _ _ _) (toL2Z hg) = 0 := by
        rw [multiplierOf_congr_bG' (memLp_gSym _ _ _ _ _) h0 hsym]
        exact multiplierOf_zero_eq (toL2Z hg) h0
      rw [h1, hz]
      rfl
    rw [Finset.sum_eq_zero (fun n hn => by rw [hpiece n hn]; simp)]
    simp
  · have hd : 1 ≤ P.natDegree := by omega
    set Cval : ℝ := max 1 ((Cna + 3) / (P.natDegree : ℝ)) with hCval
    set Bfun : ℝ≥0 → ℝ≥0 :=
      fun Λ => ((3 * (Nat.ceil (Real.logb ((Λ : ℝ)) 2) + 2) : ℕ) : ℝ≥0) with hBfun
    have hCpos : 0 < Cval := lt_of_lt_of_le one_pos (le_max_left _ _)
    refine ⟨Bfun, Cval, hCpos, ?_⟩
    intro l₂ k₂ hk₂ a Λ hΛ ha ha1 s g hg hcond
    have hD1 : (1:ℝ) ≤ (2:ℝ)^(ρ*(l₂:ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
    have hsize : ∀ n ∈ s,
        ((((P.natDegree : ℤ)) * (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))
          + (k₂ : ℤ)) : ℤ) : ℝ) + Cna * (2:ℝ)^(ρ*(l₂:ℝ)) < -2 := by
      intro n hn
      have h1 := hcond n hn
      have hmk : ((k₂ : ℕ) : ℝ) ≤ ((max l₂ k₂ : ℕ) : ℝ) := by exact_mod_cast le_max_right l₂ k₂
      have hkl : ((k₂ : ℤ) : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)
          ≤ -Cval * (2:ℝ)^(ρ*(l₂:ℝ)) := by
        have h' : ((k₂ : ℕ) : ℝ) + Cval * (2:ℝ)^(ρ*(l₂:ℝ))
            ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ) := by linarith
        push_cast
        linarith
      have hdC : Cna + 3 ≤ ((P.natDegree : ℤ) : ℝ) * Cval := by
        have hcast : ((P.natDegree : ℤ) : ℝ) = (P.natDegree : ℝ) := by push_cast; ring
        have h2 : Cna + 3 ≤ Cval * (P.natDegree : ℝ) := by
          have h1 : (Cna + 3) / (P.natDegree : ℝ) ≤ Cval := le_max_right _ _
          have hpos : (0:ℝ) ≤ (P.natDegree : ℝ) := by positivity
          have hne : (P.natDegree : ℝ) ≠ 0 := by positivity
          have h3 := mul_le_mul_of_nonneg_right h1 hpos
          rwa [div_mul_cancel₀ _ hne] at h3
        rw [hcast, mul_comm]
        exact h2
      have htarget : ((P.natDegree : ℤ) : ℝ)
            * (((k₂ : ℤ) : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))
          ≤ -Cna * (2:ℝ)^(ρ*(l₂:ℝ)) - 3 := by
        have hdR : (0:ℝ) ≤ ((P.natDegree : ℤ) : ℝ) := by positivity
        have hmul := mul_le_mul_of_nonneg_left hkl hdR
        have hprod : (Cna + 3) * (2:ℝ)^(ρ*(l₂:ℝ))
            ≤ (((P.natDegree : ℤ) : ℝ) * Cval) * (2:ℝ)^(ρ*(l₂:ℝ)) :=
          mul_le_mul_of_nonneg_right hdC (by positivity)
        have h3 : -(Cna + 3) * (2:ℝ)^(ρ*(l₂:ℝ)) ≤ -Cna * (2:ℝ)^(ρ*(l₂:ℝ)) - 3 := by
          nlinarith [hD1]
        linarith [hmul, hprod, hD1]
      have hcast : ((((P.natDegree : ℤ)) * (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))
            + (k₂ : ℤ)) : ℤ) : ℝ)
          = ((P.natDegree : ℤ) : ℝ)
            * (((k₂ : ℤ) : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) := by
        push_cast
        ring
      rw [hcast]
      linarith
    have hj2 : ∀ n ∈ s, 2 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
      intro n hn
      have h1 := hcond n hn
      have hmk : ((k₂ : ℕ) : ℝ) ≤ ((max l₂ k₂ : ℕ) : ℝ) := by exact_mod_cast le_max_right l₂ k₂
      have hC1 : (1:ℝ) ≤ Cval := le_max_left _ _
      have hk2 : (1:ℝ) ≤ ((k₂ : ℕ) : ℝ) := by exact_mod_cast hk₂
      have hprod : (1:ℝ) ≤ Cval * (2:ℝ)^(ρ*(l₂:ℝ)) := by nlinarith [hC1, hD1]
      have hlog : (2:ℝ) ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ) := by
        linarith
      have h2 : (2:ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by exact_mod_cast hlog
      exact h2
    have hpoint : ∀ ξ : Circ_bG, ∑ i : {n // n ∈ s},
          ‖gSym ρ ((P.natDegree : ℤ)) l₂ (k₂ : ℤ) (Nat.floor (a (i:ℕ))) ξ‖ ^ 2
        ≤ (((3 * (Nat.ceil (Real.logb ((Λ:ℝ)) 2) + 2) : ℕ)) : ℝ)^2 := by
      intro ξ
      have hconv : (∑ i : {n // n ∈ s},
            ‖gSym ρ ((P.natDegree : ℤ)) l₂ (k₂ : ℤ) (Nat.floor (a (i:ℕ))) ξ‖ ^ 2)
          = ∑ n ∈ s, ‖gSym ρ ((P.natDegree : ℤ)) l₂ (k₂ : ℤ) (Nat.floor (a n)) ξ‖ ^ 2 :=
        sum_subtype_eq s
          (fun n => ‖gSym ρ ((P.natDegree : ℤ)) l₂ (k₂ : ℤ) (Nat.floor (a n)) ξ‖ ^ 2)
      rw [hconv]
      exact sum_sq_gSym_le hρ hρ1 hCna hNA hd
        (by exact_mod_cast (by omega : k₂ ≠ 0)) hΛ ha ha1 s hsize hj2 ξ
    have hbessel := Work.KMTPlan.B.besselMultiplierFamily
      (fun i : {n // n ∈ s} => gSym ρ ((P.natDegree : ℤ)) l₂ (k₂ : ℤ) (Nat.floor (a (i:ℕ))))
      (fun i => memLp_gSym _ _ _ _ _)
      (A := (((3 * (Nat.ceil (Real.logb ((Λ:ℝ)) 2) + 2) : ℕ)) : ℝ)) hpoint (toL2Z hg)
    calc ∑ n ∈ s, (eLpNorm (Work.Analysis.EndVar.Gpiece (Work.KMTContract.kmtPj ρ)
            (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g) 2 Measure.count) ^ (2 : ℕ)
        = ∑ n ∈ s, ENNReal.ofReal (‖multiplierOf
            (gSym ρ ((P.natDegree : ℤ)) l₂ (k₂ : ℤ) (Nat.floor (a n)))
            (memLp_gSym _ _ _ _ _) (toL2Z hg)‖^2) := by
          refine Finset.sum_congr rfl (fun n hn => ?_)
          have hpiece : Work.Analysis.EndVar.Gpiece (Work.KMTContract.kmtPj ρ)
                ((P.natDegree : ℤ)) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g
              = ⇑(multiplierOf (gSym ρ ((P.natDegree : ℤ)) l₂ (k₂ : ℤ) (Nat.floor (a n)))
                  (memLp_gSym _ _ _ _ _) (toL2Z hg)) :=
            piece_eq_gSym ρ hρ hρ1 ((P.natDegree : ℤ)) l₂ (k₂ : ℤ)
              (by exact_mod_cast (by omega : k₂ ≠ 0)) (Nat.floor (a n)) (toL2Z hg)
          rw [hpiece]
          exact eLpNorm_sq_of_L2Z _
      _ = ENNReal.ofReal (∑ n ∈ s, ‖multiplierOf
            (gSym ρ ((P.natDegree : ℤ)) l₂ (k₂ : ℤ) (Nat.floor (a n)))
            (memLp_gSym _ _ _ _ _) (toL2Z hg)‖^2) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun n hn => sq_nonneg _)]
      _ ≤ ENNReal.ofReal ((((3 * (Nat.ceil (Real.logb ((Λ:ℝ)) 2) + 2) : ℕ)) : ℝ)^2
            * ‖toL2Z hg‖^2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hconv : (∑ n ∈ s, ‖multiplierOf
                (gSym ρ ((P.natDegree : ℤ)) l₂ (k₂ : ℤ) (Nat.floor (a n)))
                (memLp_gSym _ _ _ _ _) (toL2Z hg)‖^2)
              = ∑ i : {n // n ∈ s}, ‖multiplierOf
                (gSym ρ ((P.natDegree : ℤ)) l₂ (k₂ : ℤ) (Nat.floor (a (i:ℕ))))
                (memLp_gSym _ _ _ _ _) (toL2Z hg)‖^2 :=
            (sum_subtype_eq s (fun n => ‖multiplierOf
                (gSym ρ ((P.natDegree : ℤ)) l₂ (k₂ : ℤ) (Nat.floor (a n)))
                (memLp_gSym _ _ _ _ _) (toL2Z hg)‖^2)).symm
          rw [hconv]
          exact hbessel
      _ = ((Bfun Λ : ℝ≥0) : ℝ≥0∞) ^ (2:ℕ) * (eLpNorm g 2 Measure.count) ^ (2:ℕ) := by
          have hGl : (eLpNorm g 2 Measure.count) ^ (2:ℕ)
              = ENNReal.ofReal (‖toL2Z hg‖^2) := by
            simpa using eLpNorm_sq_of_L2Z (toL2Z hg)
          have hA : ENNReal.ofReal ((((3 * (Nat.ceil (Real.logb ((Λ:ℝ)) 2) + 2) : ℕ)) : ℝ))
              = ((Bfun Λ : ℝ≥0) : ℝ≥0∞) := by
            show ENNReal.ofReal
              (((((3 * (Nat.ceil (Real.logb ((Λ:ℝ)) 2) + 2) : ℕ)) : ℝ≥0) : ℝ)) = _
            rw [ENNReal.ofReal_coe_nnreal]
          have hsq : ENNReal.ofReal ((((3 * (Nat.ceil (Real.logb ((Λ:ℝ)) 2) + 2) : ℕ)) : ℝ)^2)
              = ((Bfun Λ : ℝ≥0) : ℝ≥0∞) ^ (2:ℕ) := by
            rw [ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤
              (((3 * (Nat.ceil (Real.logb ((Λ:ℝ)) 2) + 2) : ℕ)) : ℝ)) 2, hA]
          rw [hGl, ENNReal.ofReal_mul (sq_nonneg _), hsq]
