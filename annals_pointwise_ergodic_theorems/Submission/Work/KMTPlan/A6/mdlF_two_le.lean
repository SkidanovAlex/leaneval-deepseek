/-
# The `ℓ²` bound for the model input `mdlF` with the constant `2 (1 + 2 · 2^{-u} Q²)`

`mdlF ρ u l f = Π_{l,≤-u} f = piExact (kmtPj ρ) l (-(u:ℤ)) f` is the difference of the two
Ionescu--Wainger projections `kmtProj ρ l (-(u:ℤ))` and `kmtProj ρ (l-1) (-(u:ℤ))` (a single one
when `l = 0`).  Each of them is the convolution `iwConv (iwArithFreqs ρ l')
(periodize (etaCut kmtEta (-(u:ℤ))))`, whose `ℓ²` norm is bounded by the sup norm of its symbol
(`eLpNorm_iwConv_two_le_of_symbol_bound`), so it suffices to bound that sup norm.  Three regimes:

* `u ≥ 2` (`2^{-u} < 1/2`): `mdlIwSymbolSet_sup_le` with `M = 1` applied to
  `ψ = etaCut kmtEta (-u)` (supported in `realArc (-u)`, bounded by `1`) gives the bound
  `1 + 2 · 2^{-u} Q²`; the difference of the two projections is then at most
  `2 (1 + 2 · 2^{-u} Q²)`.
* `u = 1`: the symbol has at most `#(iwArithFreqs ρ l')` non-zero terms, each of norm at most
  `‖periodize (etaCut kmtEta (-1))‖_∞ ≤ 1` (`norm_periodize_etaCut_le_one`), so it is bounded by
  `#(iwArithFreqs ρ l') ≤ Q²` (`card_iwArithFreqs_le`) and the difference by `2 Q² ≤ 2 + 2 Q²`.
* `u = 0`: the same with `‖periodize (etaCut kmtEta 0)‖_∞ ≤ 2`
  (`norm_periodize_etaCut_le_two`), giving `4 Q² ≤ 2 + 4 Q²`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.mdlCompositeAux
import Submission.Work.KMTPlan.A6.mdlIwSymbolSet_sup_le
import Submission.Work.KMTPlan.A6.eLpNorm_iwConv_two_le_of_symbol_bound
import Submission.Work.KMTPlan.A6.MdlSliceIntervalIntegrable
import Submission.Work.KMTPlan.A6.projVanishingF

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal BigOperators
open Work.Analysis.IonescuWainger Work.KMTContract

noncomputable section

/-- Unfolding of `mdlF` at `l = 0`: a single projection. -/
lemma mdlF_zero_eq (ρ : ℝ) (u : ℕ) (f : ℤ → ℂ) :
    mdlF ρ u 0 f = kmtProj ρ 0 (-(u : ℤ)) f := by
  rw [mdlF, Work.Analysis.EndVar.piExact, if_pos rfl]
  rfl

/-- Unfolding of `mdlF` for `l ≠ 0`: the difference of the two projections. -/
lemma mdlF_eq_sub (ρ : ℝ) (u : ℕ) {l : ℕ} (hl : l ≠ 0) (f : ℤ → ℂ) :
    mdlF ρ u l f = kmtProj ρ l (-(u : ℤ)) f - kmtProj ρ (l - 1) (-(u : ℤ)) f := by
  rw [mdlF, Work.Analysis.EndVar.piExact, if_neg hl]
  rfl

/-- If the periodisation of the cutoff `η_{≤k}` is bounded by `C ≥ 0`, then the symbol of
`kmtProj ρ l' k` is bounded by `#(iwArithFreqs ρ l') · C ≤ Q² C`. -/
lemma norm_iwSymbolSet_etaCut_le_of_card {k : ℤ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ξ : AddCircle (1 : ℝ), ‖periodize (etaCut Work.KMTContract.kmtEta k) ξ‖ ≤ C)
    (ρ : ℝ) (l' Q : ℕ) (hQ : ∀ q ∈ iwP ρ l', q ≤ Q) :
    ∀ θ : AddCircle (1 : ℝ),
      ‖iwSymbolSet (iwArithFreqs ρ l') (periodize (etaCut Work.KMTContract.kmtEta k)) θ‖
        ≤ (Q * Q : ℕ) * C := by
  intro θ
  refine le_trans (norm_iwSymbolSet_le (iwArithFreqs ρ l') hC θ) ?_
  have hcard : ((iwArithFreqs ρ l').card : ℝ) ≤ ((Q * Q : ℕ) : ℝ) := by
    exact_mod_cast card_iwArithFreqs_le ρ l' Q hQ
  exact mul_le_mul_of_nonneg_right hcard hC0

/-- The `ℓ²` bound for a single projection `kmtProj ρ l' k`, from a pointwise bound on its symbol. -/
lemma eLpNorm_kmtProj_le_of_symbol {ρ : ℝ} {l' : ℕ} {k : ℤ} {K : ℝ}
    (hK : ∀ θ : AddCircle (1 : ℝ),
      ‖iwSymbolSet (iwArithFreqs ρ l') (periodize (etaCut Work.KMTContract.kmtEta k)) θ‖ ≤ K)
    (hK0 : 0 ≤ K) {f : ℤ → ℂ} (hf : MemLp f 2 Measure.count) :
    eLpNorm (kmtProj ρ l' k f) 2 Measure.count
      ≤ ENNReal.ofReal K * eLpNorm f 2 Measure.count :=
  eLpNorm_iwConv_two_le_of_symbol_bound (iwArithFreqs ρ l') _ K hK0 hK
    (memLp_iwSymbolSet_etaCut _ k) f hf

/-- The sup norm bound for the symbol of the projection at height `-(u : ℤ)` in the regime
`2 ≤ u`. -/
lemma norm_iwSymbolSet_etaCut_neg_le (ρ : ℝ) {u l' Q : ℕ} (hu : 2 ≤ u)
    (hQ : ∀ q ∈ iwP ρ l', q ≤ Q) :
    ∀ θ : AddCircle (1 : ℝ),
      ‖iwSymbolSet (iwArithFreqs ρ l') (periodize (etaCut Work.KMTContract.kmtEta (-(u : ℤ)))) θ‖
        ≤ 1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * (Q : ℝ) ^ 2 := by
  have hk : (2 : ℝ) ^ (-(u : ℤ)) < 1 / 2 := by
    have h1 : ((2 : ℤ) : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu
    have h2 : ((-(u : ℤ)) : ℤ) ≤ (-(2 : ℤ)) := by omega
    have h3 : (2 : ℝ) ^ (-(u : ℤ)) ≤ (2 : ℝ) ^ (-(2 : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h2
    norm_num at h3 ⊢
    linarith
  have hsupp : ∀ ξ : ℝ, etaCut Work.KMTContract.kmtEta (-(u : ℤ)) ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (-(u : ℤ)) := by
    intro ξ hξ
    have h := Work.KMTAreas.A7.etaCut_ne_zero_mem_realArc (-(u : ℤ)) hξ
    rw [realArc, Set.mem_Icc] at h
    exact abs_le.mpr ⟨h.1, h.2⟩
  have hbd : ∀ ξ : ℝ, ‖etaCut Work.KMTContract.kmtEta (-(u : ℤ)) ξ‖ ≤ (1 : ℝ) :=
    fun ξ => norm_etaCut_le_one _ ξ
  have h := mdlIwSymbolSet_sup_le ρ l' (-(u : ℤ)) hk Q hQ 1 zero_le_one
    (etaCut Work.KMTContract.kmtEta (-(u : ℤ))) (measurable_etaCut _) hsupp hbd
  intro θ
  simpa using h θ

/-- **The `ℓ²` bound for the model input `mdlF ρ u l f` with the constant `2 (1 + 2 · 2^{-u} Q²)`,
under the denominator bounds at the two levels `l` and `l - 1`.** -/
theorem mdlF_two_le (ρ : ℝ) (u l Q : ℕ)
    (hQ : ∀ q ∈ Work.Analysis.IonescuWainger.iwP ρ l, q ≤ Q)
    (hQ' : ∀ q ∈ Work.Analysis.IonescuWainger.iwP ρ (l - 1), q ≤ Q) (f : ℤ → ℂ) :
    MeasureTheory.eLpNorm (mdlF ρ u l f) 2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (2 * (1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * (Q : ℝ) ^ 2))
        * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  have hpow0 : (0 : ℝ) < (2 : ℝ) ^ (-(u : ℤ)) := zpow_pos (by norm_num) _
  have hQ2 : (0 : ℝ) ≤ (Q : ℝ) ^ 2 := sq_nonneg _
  cases eq_or_ne (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ⊤ with
  | inl hf =>
    rw [hf, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (by nlinarith))]
    exact le_top
  | inr hf =>
    have hfmem : MemLp f 2 MeasureTheory.Measure.count :=
      MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hf)
    -- the per-level constant `Kp` and the resulting bound `2 Kp ≤ 2 (1 + 2 · 2^{-u} Q²)`
    suffices hmain :
      ∀ Kp : ℝ, 0 ≤ Kp → 2 * Kp ≤ 2 * (1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * (Q : ℝ) ^ 2) →
        (∀ (l' : ℕ), (∀ q ∈ iwP ρ l', q ≤ Q) →
          eLpNorm (kmtProj ρ l' (-(u : ℤ)) f) 2 Measure.count
            ≤ ENNReal.ofReal Kp * eLpNorm f 2 Measure.count) →
        eLpNorm (mdlF ρ u l f) 2 Measure.count
          ≤ ENNReal.ofReal (2 * (1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * (Q : ℝ) ^ 2))
            * eLpNorm f 2 Measure.count
    · rcases Nat.eq_zero_or_pos u with hu | hu
      · -- ## `u = 0`
        have hpow : (2 : ℝ) ^ (-(u : ℤ)) = 1 := by rw [hu]; norm_num
        have hbound2 : ∀ ξ : AddCircle (1 : ℝ),
            ‖periodize (etaCut Work.KMTContract.kmtEta (-(u : ℤ))) ξ‖ ≤ 2 := by
          intro ξ
          exact norm_periodize_etaCut_le_two (-(u : ℤ)) (by rw [hu]; norm_num) ξ
        refine hmain (2 * ((Q * Q : ℕ) : ℝ)) (by positivity) (by
          have h1 : ((Q * Q : ℕ) : ℝ) = (Q : ℝ) ^ 2 := by push_cast; ring
          rw [hpow, h1]; nlinarith) ?_
        intro l' hQl'
        refine eLpNorm_kmtProj_le_of_symbol (K := 2 * ((Q * Q : ℕ) : ℝ)) ?_ (by positivity) hfmem
        intro θ
        have h := norm_iwSymbolSet_etaCut_le_of_card (k := -(u : ℤ)) (C := 2) (by norm_num)
          hbound2 ρ l' Q hQl' θ
        linarith
      · rcases lt_or_ge u 2 with hu1 | hu2
        · -- ## `u = 1`
          have hu_eq : u = 1 := by omega
          have hpow : (2 : ℝ) ^ (-(u : ℤ)) = 1 / 2 := by rw [hu_eq]; norm_num
          have hbound1 : ∀ ξ : AddCircle (1 : ℝ),
              ‖periodize (etaCut Work.KMTContract.kmtEta (-(u : ℤ))) ξ‖ ≤ 1 := by
            intro ξ
            refine norm_periodize_etaCut_le_one ?_ ξ
            rw [hu_eq]
            norm_num
          refine hmain (((Q * Q : ℕ) : ℝ)) (by positivity) (by
            have h1 : ((Q * Q : ℕ) : ℝ) = (Q : ℝ) ^ 2 := by push_cast; ring
            rw [hpow, h1]; nlinarith) ?_
          intro l' hQl'
          refine eLpNorm_kmtProj_le_of_symbol (K := ((Q * Q : ℕ) : ℝ)) ?_ (by positivity) hfmem
          intro θ
          have h := norm_iwSymbolSet_etaCut_le_of_card (k := -(u : ℤ)) (C := 1) (by norm_num)
            hbound1 ρ l' Q hQl' θ
          linarith
        · -- ## `u ≥ 2`
          refine hmain (1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * (Q : ℝ) ^ 2) (by nlinarith) le_rfl ?_
          intro l' hQl'
          exact eLpNorm_kmtProj_le_of_symbol
            (norm_iwSymbolSet_etaCut_neg_le ρ hu2 hQl') (by nlinarith) hfmem
    · -- assemble: `mdlF` is the difference of the two projections
      intro Kp hKp0 hKpC hproj
      by_cases hl0 : l = 0
      · subst hl0
        rw [mdlF_zero_eq]
        refine le_trans (hproj 0 hQ) ?_
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_trans (by linarith) hKpC)) _
      · rw [mdlF_eq_sub ρ u hl0 f]
        have h1 := hproj l hQ
        have h2 := hproj (l - 1) hQ'
        refine le_trans (eLpNorm_sub_le (μ := Measure.count) (by norm_num)) ?_
        refine le_trans (add_le_add h1 h2) ?_
        calc ENNReal.ofReal Kp * eLpNorm f 2 Measure.count
              + ENNReal.ofReal Kp * eLpNorm f 2 Measure.count
            = (ENNReal.ofReal Kp + ENNReal.ofReal Kp) * eLpNorm f 2 Measure.count := by ring
          _ = ENNReal.ofReal (Kp + Kp) * eLpNorm f 2 Measure.count := by
              rw [ENNReal.ofReal_add hKp0 hKp0]
          _ = ENNReal.ofReal (2 * Kp) * eLpNorm f 2 Measure.count := by
              congr 2; ring
          _ ≤ ENNReal.ofReal (2 * (1 + 2 * (2 : ℝ) ^ (-(u : ℤ)) * (Q : ℝ) ^ 2))
                * eLpNorm f 2 Measure.count :=
              mul_le_mul_left (ENNReal.ofReal_le_ofReal hKpC) _

end

end Work.KMTPlan.A6
