/-
# The §7 single-scale estimate `ssu` from the fibre bounds (assembly)

This module assembles the paper's §7 single-scale estimate (Lemma `ssu` of Krause--Mirek--Tao,
Annals 195 (2022), arXiv:2008.00857) from

* the two §4 *linear* bounds for the randomised cutoffs (`randSymb_Tm_f_lp`,
  `randSymb_Tm_g_lp`), supplied here as hypotheses so that this file does not depend on their
  current state;
* the *fibre* `ℓ^p` bounds of `Work.KMTAreas.A7.fiberOpCum_lp_goodArcs` (the Ionescu--Wainger
  multiplier theorem of area `A1`, in the interpolated form `IwLqGeneral`) for the model symbols
  `mStarF u`, `mStargF d u`;
* the elementary `ℤ`-plumbing of `Work.KMTAreas.A7.FibrePlumbing` (the exact-height fibre is the
  difference of consecutive *cumulative* fibres);
* the residue `ℓ^p` aggregation `Work.KMTAreas.A7.eLpNorm_residueLp_le`;
* the good-major-arcs verification `Work.KMTAreas.A7.goodMajorArcs_uScale`;
* the crude (Young) fallback `Work.KMTAreas.A7.fiberOpD_lp_crude` for the finitely many scales at
  which good major arcs fails.

The conclusion is the *gain-free* form of `ssu`: the estimate with the weight
`⟨L⟩^A 2^{AρL}` and no decay in `L`, which is all that
`Work.KMTAreas.A7.SmallModelVar` consumes.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.fiberOpCum_lp_goodArcs
import Submission.Work.KMTAreas.A7.fiberOpD_lp_crude
import Submission.Work.KMTAreas.A7.FibrePlumbing
import Submission.Work.KMTAreas.A7.residueLp_fiberOpD_le
import Submission.Work.KMTAreas.A7.isLqMultiplierBound_modulated_etaCut
import Submission.Work.KMTAreas.A7.eLpNorm_residueLp_le
import Submission.Work.KMTAreas.A7.goodMajorArcs_uScale
import Submission.Work.KMTAreas.A7.ExceptionalSupport

set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

/-! ## Small bricks -/

/-- `ofReal` of a nonnegative product (the usable direction of `ENNReal.ofReal_mul`). -/
private lemma ofReal_mul_eq (a b : ℝ) (ha : 0 ≤ a) :
    ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (a * b) :=
  (ENNReal.ofReal_mul ha).symm

/-- `ofReal` of a nonnegative real, in terms of the `ℝ≥0` coercion. -/
private lemma ofReal_coe_eq (x : NNReal) : ENNReal.ofReal (x : ℝ) = (x : ENNReal) :=
  ENNReal.ofReal_coe_nnreal

/-- The final `ℝ≥0`-constant of the estimate: `max 1 ⌈x⌉₊`. -/
private def kcNN (x : ℝ) : NNReal := ⟨((max 1 ⌈x⌉₊ : ℕ) : ℝ), Nat.cast_nonneg _⟩

/-- The value of `kcNN`. -/
private lemma kcNN_coe (x : ℝ) : (kcNN x : ℝ) = (max 1 ⌈x⌉₊ : ℕ) := rfl

/-- `kcNN x` is at least `1`. -/
private lemma one_le_kcNN (x : ℝ) : 1 ≤ (kcNN x : ℝ) := by
  rw [kcNN_coe]; exact_mod_cast le_max_left 1 ⌈x⌉₊

/-- The final weight comparison: the product of the two §4 linear weights, enlarged by the two
`⟨l⟩ ≤ 1 + L` factors of the fibre bounds, is dominated by `(1+L)^{A_f + A_g + 4}
2^{(A_f + A_g + 4)ρL}`. -/
private lemma weight_comparison {Af Ag ρ L : ℝ} (hρ : 0 ≤ ρ) (hL : 0 ≤ L) :
    ((1 + L) * ((1 + L) ^ Af * (2 : ℝ) ^ (Af * ρ * L)))
        * ((1 + L) * ((1 + L) ^ Ag * (2 : ℝ) ^ (Ag * ρ * L)))
      ≤ (1 + L) ^ (Af + Ag + 4) * (2 : ℝ) ^ ((Af + Ag + 4) * ρ * L) := by
  have h0 : (0 : ℝ) < 1 + L := by linarith
  have h1 : (1 : ℝ) ≤ 1 + L := by linarith
  have hle : (1:ℝ) + 1 + Af + Ag ≤ Af + Ag + 4 := by linarith
  have hexp : Af * ρ * L + Ag * ρ * L ≤ (Af + Ag + 4) * ρ * L := by
    have h3 : (0 : ℝ) ≤ ρ * L := mul_nonneg hρ hL
    nlinarith
  have hfact : ((1 + L) * ((1 + L) ^ Af * (2 : ℝ) ^ (Af * ρ * L)))
        * ((1 + L) * ((1 + L) ^ Ag * (2 : ℝ) ^ (Ag * ρ * L)))
      = ((1 + L) * (1 + L)) * ((1 + L) ^ Af * (1 + L) ^ Ag) *
          ((2 : ℝ) ^ (Af * ρ * L) * (2 : ℝ) ^ (Ag * ρ * L)) := by
    ring
  rw [hfact]
  have hcomb1 : (1 + L) * (1 + L) * ((1 + L) ^ Af * (1 + L) ^ Ag)
      = (1 + L) ^ (1 + 1 + Af + Ag) := by
    rw [Real.rpow_add h0 (1 + 1 + Af) Ag, Real.rpow_add h0 (1 + 1 : ℝ) Af,
      Real.rpow_add h0 (1 : ℝ) 1, Real.rpow_one]
    ring
  have hcomb2 : (2 : ℝ) ^ (Af * ρ * L) * (2 : ℝ) ^ (Ag * ρ * L)
      = (2 : ℝ) ^ (Af * ρ * L + Ag * ρ * L) := (Real.rpow_add (by norm_num) _ _).symm
  rw [hcomb1, hcomb2]
  exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le h1 hle)
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (by positivity) (by positivity)

/-- `⟨l⟩ ≤ 1 + L` when `l ≤ l₁`, for the loss weight `L = lmaxR …`. -/
private lemma angleBracket_le_one_add_lmaxR {l₁ l₂ k₁ k₂ l : ℕ} (hl : l ≤ l₁) :
    (Work.Analysis.IWMultiplier.angleBracket l : ℝ) ≤ 1 + lmaxR l₁ l₂ k₁ k₂ := by
  have h2 : (l : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
    have h3 : (l : ℤ) ≤ Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
      unfold Work.Analysis.EndVar.lmax
      omega
    have h4 : (l : ℝ) ≤ (Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ) := by
      exact_mod_cast h3
    simpa [lmaxR] using h4
  have h5 : (Work.Analysis.IWMultiplier.angleBracket l : ℝ) = max 1 (l : ℝ) := by
    rw [Work.Analysis.IWMultiplier.angleBracket]
    push_cast
    rfl
  rw [h5]
  exact max_le (by linarith) (by linarith)

/-- `⟨l⟩ ≤ 1 + L` when `l ≤ l₂` (the `g`-side version). -/
private lemma angleBracket_le_one_add_lmaxR' {l₁ l₂ k₁ k₂ l : ℕ} (hl : l ≤ l₂) :
    (Work.Analysis.IWMultiplier.angleBracket l : ℝ) ≤ 1 + lmaxR l₁ l₂ k₁ k₂ := by
  have h := angleBracket_le_one_add_lmaxR (l₁ := l₂) (l₂ := l₁) (k₁ := k₁) (k₂ := k₂)
    (l := l) hl
  simpa only [lmaxR, Work.Analysis.EndVar.lmax, max_comm (l₁ : ℤ) (l₂ : ℤ)] using h

/-! ## The exact-height fibre bound at a bounded input -/

/-- The `ℓ^p` bound for the exact-height fibre `fiberOpD ρ l (mStarF u) n₀` at a bounded input,
from the two cumulative bounds with a *common* constant `C`. -/
private theorem fiberOpD_model_bound {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {p : ENNReal}
    (hple : 1 ≤ p) (l u : ℕ) (n₀ : ℤ) (v : ℤ → ℂ) {Cv : ℝ} (hv : ∀ y : ℤ, ‖v y‖ ≤ Cv)
    (hcw : Summable (fun j : ℤ => ‖cw (mStarF u) j‖)) (C : ENNReal)
    (h₁ : eLpNorm (fun x : ℤ => fiberOpCum ρ l (mStarF u) n₀ v x) p Measure.count
      ≤ C * eLpNorm v p Measure.count)
    (h₂ : eLpNorm (fun x : ℤ => fiberOpCum ρ (l - 1) (mStarF u) n₀ v x) p Measure.count
      ≤ C * eLpNorm v p Measure.count) :
    eLpNorm (fun x : ℤ => fiberOpD ρ l (mStarF u) n₀ v x) p Measure.count
      ≤ (C + C) * eLpNorm v p Measure.count := by
  by_cases hl : l = 0
  · subst hl
    rw [fiberOpD_zero_eq_fiberOpCum]
    exact h₂.trans (mul_le_mul_of_nonneg_right le_add_self zero_le)
  · have hl1 : 1 ≤ l := Nat.one_le_iff_ne_zero.mpr hl
    exact eLpNorm_fiberOpD_le_of_fiberOpCum hρ hρ1 hl1 hple (mStarF u) n₀ v hv hcw C C h₁ h₂

/-! ## The main assembly -/

theorem smallModelSingleScale_of_fibre_core (P : Polynomial ℤ) (p₁ p₂ : ENNReal)
    (hdeg : 2 ≤ P.natDegree) (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (hLinF : ∀ (C₀ : ℕ), 1 ≤ C₀ → ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ) (f : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
          (∀ n, ‖ε n‖ ≤ 1) → t ∈ Set.Icc ((1:ℝ)/2) 1 →
          MeasureTheory.eLpNorm (fun x : ℤ => Tm ρ l₁
              (randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) f x)
            p₁ MeasureTheory.Measure.count
            ≤ (C Λ : ENNReal) * ENNReal.ofReal ((1 + lmaxR l₁ l₂ k₁ k₂) ^ A *
                (2 : ℝ) ^ (A * ρ * lmaxR l₁ l₂ k₁ k₂)) *
              MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count)
    (hLinG : ∀ (C₀ : ℕ), 1 ≤ C₀ → ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ) (g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
          (∀ n, ‖ε n‖ ≤ 1) → t ∈ Set.Icc ((1:ℝ)/2) 1 →
          MeasureTheory.eLpNorm (fun x : ℤ => Tm ρ l₂
              (randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K) g x)
            p₂ MeasureTheory.Measure.count
            ≤ (C Λ : ENNReal) * ENNReal.ofReal ((1 + lmaxR l₁ l₂ k₁ k₂) ^ A *
                (2 : ℝ) ^ (A * ρ * lmaxR l₁ l₂ k₁ k₂)) *
              MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) :
    ∀ (C₀ : ℕ), 1 ≤ C₀ → ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε ε' : ℕ → ℂ)
          (f g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
          (∀ n, ‖ε n‖ ≤ 1) → (∀ n, ‖ε' n‖ ≤ 1) → t ∈ Set.Icc ((1:ℝ)/2) 1 →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              smallBtwist ρ P l₁ l₂
                (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂)))
                (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂)))
                (Tm ρ l₁ (randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) f)
                (Tm ρ l₂ (randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε' K) g) x)
            (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
          ≤ (C Λ : ENNReal) *
              ENNReal.ofReal ((1 + lmaxR l₁ l₂ k₁ k₂) ^ A *
                (2 : ℝ) ^ (A * ρ * lmaxR l₁ l₂ k₁ k₂)) *
              MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
              MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
  intro C₀ hC₀
  obtain ⟨Af, hAf, ρ₀f, hρ₀f, CF⟩ := hLinF C₀ hC₀
  obtain ⟨Ag, hAg, ρ₀g, hρ₀g, CG⟩ := hLinG C₀ hC₀
  obtain ⟨M, hMpos, hM⟩ := isLqMultiplierBound_modulated_etaCut
  refine ⟨Af + Ag + 4, by positivity, min (min ρ₀f ρ₀g) 1,
    lt_min (lt_min hρ₀f hρ₀g) one_pos, ?_⟩
  intro ρ hρ hρle
  have hρ1 : ρ ≤ 1 := le_trans hρle (min_le_right _ _)
  have hρ0 : 0 ≤ ρ := hρ.le
  have hρf : ρ ≤ ρ₀f := le_trans hρle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρg : ρ ≤ ρ₀g := le_trans hρle (le_trans (min_le_left _ _) (min_le_right _ _))
  obtain ⟨CFun, hCFun⟩ := CF ρ hρ hρf
  obtain ⟨CGun, hCGun⟩ := CG ρ hρ hρg
  -- the fibre bounds (the Ionescu--Wainger multiplier theorem)
  obtain ⟨Cρf, hCρf, Cfib, hCfib, hFibf⟩ := fiberOpCum_lp_goodArcs hA1 ρ hρ hρ1 p₁ hp₁ htp₁ M hM
  obtain ⟨Cρg, hCρg, Cfibg, hCfibg, hFibg⟩ := fiberOpCum_lp_goodArcs hA1 ρ hρ hρ1 p₂ hp₂ htp₂ M hM
  -- the good-major-arcs threshold
  obtain ⟨L₀, hL₀⟩ := goodMajorArcs_uScale (ρ := ρ) (Cρ := max Cρf Cρg) hρ
    (lt_max_of_lt_left hCρf)
  -- the crude fallback
  obtain ⟨Cc1, hCc1, hCrude1⟩ := fiberOpD_lp_crude (ρ := ρ) hρ hρ1 hp₁ htp₁ L₀
    (2 * (uScale ρ L₀ : ℤ) + 2)
  obtain ⟨Cc2, hCc2, hCrude2⟩ := fiberOpD_lp_crude (ρ := ρ) hρ hρ1 hp₂ htp₂ L₀
    ((P.natDegree : ℤ) * (2 * (uScale ρ L₀ : ℤ) + 2))
  -- the data-independent constants
  set Kf0 : ℝ := max (2 * (Cfib : ℝ) * (M : ℝ)) (max Cc1 1) with hKf0def
  set Kg0 : ℝ := max (2 * (Cfibg : ℝ) * (M : ℝ)) (max Cc2 1) with hKg0def
  have hKf0pos : 0 < Kf0 := by
    rw [hKf0def]
    exact lt_of_lt_of_le one_pos (le_trans (le_max_right Cc1 1) (le_max_right _ _))
  have hKg0pos : 0 < Kg0 := by
    rw [hKg0def]
    exact lt_of_lt_of_le one_pos (le_trans (le_max_right Cc2 1) (le_max_right _ _))
  have hKf0nn : 0 ≤ Kf0 := hKf0pos.le
  have hKg0nn : 0 ≤ Kg0 := hKg0pos.le
  refine ⟨fun Λ => kcNN ((CFun Λ : ℝ) * (CGun Λ : ℝ) * Kf0 * Kg0), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ K t ε ε' f g hΛ ha ha1 hε hε' ht
  -- data-dependent abbreviations
  set L : ℕ := smallL l₁ l₂ k₁ k₂ with hLdef
  set u : ℕ := uScale ρ L with hudef
  set F : ENNReal := MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count with hFdef
  set G : ENNReal := MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count with hGdef
  set H : ℤ → ℂ := Tm ρ l₁ (randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) f with hHdef
  set Kg : ℤ → ℂ := Tm ρ l₂ (randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε' K) g with hKgdef
  set Wf : ℝ := (1 + lmaxR l₁ l₂ k₁ k₂) ^ Af *
    (2 : ℝ) ^ (Af * ρ * lmaxR l₁ l₂ k₁ k₂) with hWfdef
  set Wg : ℝ := (1 + lmaxR l₁ l₂ k₁ k₂) ^ Ag *
    (2 : ℝ) ^ (Ag * ρ * lmaxR l₁ l₂ k₁ k₂) with hWgdef
  set Wfin : ℝ := (1 + lmaxR l₁ l₂ k₁ k₂) ^ (Af + Ag + 4) *
    (2 : ℝ) ^ ((Af + Ag + 4) * ρ * lmaxR l₁ l₂ k₁ k₂) with hWfindef
  have hLnn : 0 ≤ lmaxR l₁ l₂ k₁ k₂ := lmaxR_nonneg l₁ l₂ k₁ k₂
  have hWfnn : 0 ≤ Wf := by
    rw [hWfdef]
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by norm_num) _)
  have hWgnn : 0 ≤ Wg := by
    rw [hWgdef]
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by norm_num) _)
  have hWfinn : 0 ≤ Wfin := by
    rw [hWfindef]
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by norm_num) _)
  have hKcne : (kcNN ((CFun Λ : ℝ) * (CGun Λ : ℝ) * Kf0 * Kg0) : ENNReal) ≠ 0 := by
    simp only [ne_eq, ENNReal.coe_eq_zero, NNReal.coe_eq_zero]
    have h1 := one_le_kcNN ((CFun Λ : ℝ) * (CGun Λ : ℝ) * Kf0 * Kg0)
    linarith
  -- degeneracies
  by_cases hg0 : G = 0
  · have hgz : g = 0 := eq_zero_of_eLpNorm_count_eq_zero (p := p₂)
      (ne_of_gt (lt_trans zero_lt_one hp₂)) (by rw [← hGdef]; exact hg0)
    subst hgz
    have hzero : (fun x : ℤ => smallBtwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
        H (Tm ρ l₂ (randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε' K) 0) x) = 0 := by
      rw [Tm_apply_zero, smallBtwist_eq_zero_of_right]
    rw [hzero]
    simp
  by_cases hf0 : F = 0
  · have hfz : f = 0 := eq_zero_of_eLpNorm_count_eq_zero (p := p₁)
      (ne_of_gt (lt_trans zero_lt_one hp₁)) (by rw [← hFdef]; exact hf0)
    subst hfz
    have hzero : (fun x : ℤ => smallBtwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u)
        (Tm ρ l₁ (randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) 0) Kg x) = 0 := by
      rw [Tm_apply_zero, smallBtwist_eq_zero_of_left]
    rw [hzero]
    simp
  have hWpos : 0 < Wfin := lt_of_lt_of_le zero_lt_one (by
    have h1 : (1 : ℝ) ≤ 1 + lmaxR l₁ l₂ k₁ k₂ := by linarith
    rw [hWfindef]
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ ((Af + Ag + 4) * ρ * lmaxR l₁ l₂ k₁ k₂) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have h3 : (1 : ℝ) ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ (Af + Ag + 4) :=
      Real.one_le_rpow h1 (by positivity)
    nlinarith [h2, h3])
  by_cases hftop : F = ⊤
  · have htop : (kcNN ((CFun Λ : ℝ) * (CGun Λ : ℝ) * Kf0 * Kg0) : ENNReal) *
        ENNReal.ofReal Wfin * F * G = ⊤ := by
      rw [hftop]
      have hne : (kcNN ((CFun Λ : ℝ) * (CGun Λ : ℝ) * Kf0 * Kg0) : ENNReal) *
          ENNReal.ofReal Wfin ≠ 0 :=
        mul_ne_zero hKcne (ENNReal.ofReal_ne_zero_iff.mpr hWpos)
      rw [show (kcNN ((CFun Λ : ℝ) * (CGun Λ : ℝ) * Kf0 * Kg0) : ENNReal) *
            ENNReal.ofReal Wfin * ⊤ * G
          = ((kcNN ((CFun Λ : ℝ) * (CGun Λ : ℝ) * Kf0 * Kg0) : ENNReal) *
              ENNReal.ofReal Wfin * ⊤) * G from rfl,
        ENNReal.mul_top hne, ENNReal.top_mul hg0]
    rw [htop]
    exact le_top
  by_cases hgtop : G = ⊤
  · have htop : (kcNN ((CFun Λ : ℝ) * (CGun Λ : ℝ) * Kf0 * Kg0) : ENNReal) *
        ENNReal.ofReal Wfin * F * G = ⊤ := by
      rw [hgtop, ENNReal.mul_top]
      exact mul_ne_zero (mul_ne_zero hKcne (ENNReal.ofReal_ne_zero_iff.mpr hWpos)) hf0
    rw [htop]
    exact le_top
  -- the main case
  have hFlt : F < ⊤ := lt_top_iff_ne_top.mpr hftop
  have hGlt : G < ⊤ := lt_top_iff_ne_top.mpr hgtop
  have hLH : eLpNorm H p₁ Measure.count ≤ (CFun Λ : ENNReal) * ENNReal.ofReal Wf * F := by
    rw [hHdef, hFdef, hWfdef]
    exact hCFun a Λ l₁ l₂ k₁ k₂ K t ε f hΛ ha ha1 hε ht
  have hLKg : eLpNorm Kg p₂ Measure.count ≤ (CGun Λ : ENNReal) * ENNReal.ofReal Wg * G := by
    rw [hKgdef, hGdef, hWgdef]
    exact hCGun a Λ l₁ l₂ k₁ k₂ K t ε' g hΛ ha ha1 hε' ht
  have hHfin : eLpNorm H p₁ Measure.count < ⊤ := lt_of_le_of_lt hLH (by
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
      ENNReal.ofReal_lt_top) hFlt)
  have hKgfin : eLpNorm Kg p₂ Measure.count < ⊤ := lt_of_le_of_lt hLKg (by
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
      ENNReal.ofReal_lt_top) hGlt)
  obtain ⟨BH, hBH⟩ := bounded_of_eLpNorm_count_lt_top (p := p₁)
    (ne_of_gt (lt_trans zero_lt_one hp₁)) hHfin
  obtain ⟨BG, hBG⟩ := bounded_of_eLpNorm_count_lt_top (p := p₂)
    (ne_of_gt (lt_trans zero_lt_one hp₂)) hKgfin
  -- the fibre constant as an `ofReal` of a real product
  have hCf : (↑(Cfib * Work.Analysis.IWMultiplier.angleBracket l₁ * M) : ENNReal)
      = ENNReal.ofReal ((Cfib : ℝ) * (Work.Analysis.IWMultiplier.angleBracket l₁ : ℝ)
        * (M : ℝ)) := by
    rw [← ofReal_coe_eq (Cfib * Work.Analysis.IWMultiplier.angleBracket l₁ * M)]
    congr 1
  have hCg : (↑(Cfibg * Work.Analysis.IWMultiplier.angleBracket l₂ * M) : ENNReal)
      = ENNReal.ofReal ((Cfibg : ℝ) * (Work.Analysis.IWMultiplier.angleBracket l₂ : ℝ)
        * (M : ℝ)) := by
    rw [← ofReal_coe_eq (Cfibg * Work.Analysis.IWMultiplier.angleBracket l₂ * M)]
    congr 1
  have hbr1 : (Work.Analysis.IWMultiplier.angleBracket (l₁ - 1) : ℝ)
      ≤ (Work.Analysis.IWMultiplier.angleBracket l₁ : ℝ) := by
    rw [Work.Analysis.IWMultiplier.angleBracket, Work.Analysis.IWMultiplier.angleBracket]
    exact_mod_cast max_le_max le_rfl (Nat.sub_le l₁ 1)
  have hbr2 : (Work.Analysis.IWMultiplier.angleBracket (l₂ - 1) : ℝ)
      ≤ (Work.Analysis.IWMultiplier.angleBracket l₂ : ℝ) := by
    rw [Work.Analysis.IWMultiplier.angleBracket, Work.Analysis.IWMultiplier.angleBracket]
    exact_mod_cast max_le_max le_rfl (Nat.sub_le l₂ 1)
  -- the per-residue fibre bound, `f`-side
  have hfibF : ∀ n₀ : ℤ, eLpNorm (fun x : ℤ =>
        ‖(fiberOpD ρ l₁ (mStarF u) n₀ H x : ℂ)‖ₑ) p₁ Measure.count
      ≤ ENNReal.ofReal (Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂)) * eLpNorm H p₁ Measure.count := by
    intro n₀
    have hbase : eLpNorm (fun x : ℤ => (fiberOpD ρ l₁ (mStarF u) n₀ H x : ℂ)) p₁
        Measure.count = eLpNorm (fun x : ℤ => ‖(fiberOpD ρ l₁ (mStarF u) n₀ H x : ℂ)‖ₑ)
          p₁ Measure.count :=
      (eLpNorm_enorm (hf := AEStronglyMeasurable.of_discrete) _).symm
    rw [← hbase]
    by_cases hLc : L₀ ≤ L
    · have hl1L : l₁ ≤ L := by rw [hLdef]; simp only [smallL]; omega
      have hl1L' : l₁ - 1 ≤ L := by omega
      have hga : GoodMajorArcs ρ (max Cρf Cρg) l₁ (-(2 * (u : ℤ))) := hL₀ L l₁ hLc hl1L
      have hga' : GoodMajorArcs ρ (max Cρf Cρg) (l₁ - 1) (-(2 * (u : ℤ))) :=
        hL₀ L (l₁ - 1) hLc hl1L'
      have hgaf := GoodMajorArcs.mono_Cρ (le_max_left Cρf Cρg) hga
      have hgaf' := GoodMajorArcs.mono_Cρ (le_max_left Cρf Cρg) hga'
      have h₁ : eLpNorm (fun x : ℤ => fiberOpCum ρ l₁ (mStarF u) n₀ H x) p₁ Measure.count
          ≤ ENNReal.ofReal ((Cfib : ℝ) * (Work.Analysis.IWMultiplier.angleBracket l₁ : ℝ)
              * (M : ℝ)) * eLpNorm H p₁ Measure.count := by
        rw [← hCf]
        exact hFibf l₁ u hgaf n₀ H
      have h₂ : eLpNorm (fun x : ℤ => fiberOpCum ρ (l₁ - 1) (mStarF u) n₀ H x) p₁
          Measure.count ≤ ENNReal.ofReal ((Cfib : ℝ)
            * (Work.Analysis.IWMultiplier.angleBracket l₁ : ℝ) * (M : ℝ)) *
              eLpNorm H p₁ Measure.count := by
        refine (hFibf (l₁ - 1) u hgaf' n₀ H).trans (mul_le_mul_of_nonneg_right ?_ zero_le)
        rw [← ofReal_coe_eq (Cfib * Work.Analysis.IWMultiplier.angleBracket (l₁ - 1) * M)]
        refine ENNReal.ofReal_le_ofReal ?_
        push_cast
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbr1 (NNReal.coe_nonneg _)) (NNReal.coe_nonneg _)
      have hb := fiberOpD_model_bound hρ hρ1 (le_of_lt hp₁) l₁ u n₀ H hBH
        (summable_norm_cw_mStarF u)
        (ENNReal.ofReal ((Cfib : ℝ) * (Work.Analysis.IWMultiplier.angleBracket l₁ : ℝ)
          * (M : ℝ))) h₁ h₂
      refine hb.trans (mul_le_mul_of_nonneg_right ?_ zero_le)
      rw [show (ENNReal.ofReal ((Cfib : ℝ) * (Work.Analysis.IWMultiplier.angleBracket l₁ : ℝ)
            * (M : ℝ)) + ENNReal.ofReal ((Cfib : ℝ)
            * (Work.Analysis.IWMultiplier.angleBracket l₁ : ℝ) * (M : ℝ)))
          = ENNReal.ofReal (2 * ((Cfib : ℝ) * (Work.Analysis.IWMultiplier.angleBracket l₁ : ℝ)
            * (M : ℝ))) from by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : (2 * (Cfib : ℝ) * (M : ℝ)) ≤ Kf0 := by
        rw [hKf0def]; exact le_max_left _ _
      have h2 : (Work.Analysis.IWMultiplier.angleBracket l₁ : ℝ)
          ≤ 1 + lmaxR l₁ l₂ k₁ k₂ := angleBracket_le_one_add_lmaxR le_rfl
      calc 2 * ((Cfib : ℝ) * (Work.Analysis.IWMultiplier.angleBracket l₁ : ℝ) * (M : ℝ))
          = (2 * (Cfib : ℝ) * (M : ℝ)) *
              (Work.Analysis.IWMultiplier.angleBracket l₁ : ℝ) := by ring
        _ ≤ Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
    · have hl1L : l₁ ≤ L₀ := by rw [hLdef] at hLc; simp only [smallL] at hLc ⊢; omega
      have hmono : uScale ρ L ≤ uScale ρ L₀ :=
        ExcSupport.scaleCount_mono 1 hρ0 (le_of_lt (not_le.mp hLc))
      have hk : |(-(2 * (u : ℤ)))| ≤ 2 * (uScale ρ L₀ : ℤ) + 2 := by
        rw [abs_neg, abs_of_nonneg (by positivity)]
        have hu : (u : ℤ) ≤ (uScale ρ L₀ : ℤ) := by exact_mod_cast hmono
        linarith
      refine (hCrude1 l₁ hl1L (-(2 * (u : ℤ))) hk n₀ H).trans
        (mul_le_mul_of_nonneg_right ?_ zero_le)
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : Cc1 ≤ Kf0 := by
        rw [hKf0def]; exact le_trans (le_max_left Cc1 1) (le_max_right _ _)
      have h2 : (1 : ℝ) ≤ 1 + lmaxR l₁ l₂ k₁ k₂ := by linarith
      nlinarith [hCc1.le, hKf0nn, h1, h2]
  -- the per-residue fibre bound, `g`-side
  have hfibG : ∀ n₀ : ℤ, eLpNorm (fun x : ℤ =>
        ‖(fiberOpPD ρ P l₂ (mStargF P.natDegree u) n₀ Kg x : ℂ)‖ₑ) p₂ Measure.count
      ≤ ENNReal.ofReal (Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂)) * eLpNorm Kg p₂ Measure.count := by
    intro n₀
    have hbase : eLpNorm (fun x : ℤ =>
        (fiberOpPD ρ P l₂ (mStargF P.natDegree u) n₀ Kg x : ℂ)) p₂ Measure.count
        = eLpNorm (fun x : ℤ =>
          ‖(fiberOpPD ρ P l₂ (mStargF P.natDegree u) n₀ Kg x : ℂ)‖ₑ) p₂ Measure.count :=
      (eLpNorm_enorm (hf := AEStronglyMeasurable.of_discrete) _).symm
    rw [← hbase, fiberOpPD_eq_fiberOpD, mStargF_eq_mStarF P u]
    by_cases hLc : L₀ ≤ L
    · have hl2L : l₂ ≤ L := by rw [hLdef]; simp only [smallL]; omega
      have hl2L' : l₂ - 1 ≤ L := by omega
      have hga₀ : GoodMajorArcs ρ (max Cρf Cρg) l₂ (-(2 * (u : ℤ))) := hL₀ L l₂ hLc hl2L
      have hga₀' : GoodMajorArcs ρ (max Cρf Cρg) (l₂ - 1) (-(2 * (u : ℤ))) :=
        hL₀ L (l₂ - 1) hLc hl2L'
      have hcast : ((P.natDegree * u : ℕ) : ℤ) = (P.natDegree : ℤ) * (u : ℤ) := by
        push_cast; ring
      have hmonok : -(2 * ((P.natDegree * u : ℕ) : ℤ)) ≤ -(2 * (u : ℤ)) := by
        rw [hcast, neg_le_neg_iff]
        have hd1 : (1 : ℤ) ≤ (P.natDegree : ℤ) := by
          exact_mod_cast (le_trans (by norm_num : (1:ℕ) ≤ 2) hdeg)
        have hu : (0 : ℤ) ≤ (u : ℤ) := by positivity
        nlinarith
      have hga := GoodMajorArcs.mono_k
        (GoodMajorArcs.mono_Cρ (le_max_right Cρf Cρg) hga₀) hmonok
      have hga' := GoodMajorArcs.mono_k
        (GoodMajorArcs.mono_Cρ (le_max_right Cρf Cρg) hga₀') hmonok
      have h₁ : eLpNorm (fun x : ℤ =>
            fiberOpCum ρ l₂ (mStarF (P.natDegree * u)) (P.eval n₀) Kg x) p₂ Measure.count
          ≤ ENNReal.ofReal ((Cfibg : ℝ) * (Work.Analysis.IWMultiplier.angleBracket l₂ : ℝ)
              * (M : ℝ)) * eLpNorm Kg p₂ Measure.count := by
        rw [← hCg]
        exact hFibg l₂ (P.natDegree * u) hga (P.eval n₀) Kg
      have h₂ : eLpNorm (fun x : ℤ =>
            fiberOpCum ρ (l₂ - 1) (mStarF (P.natDegree * u)) (P.eval n₀) Kg x) p₂
            Measure.count ≤ ENNReal.ofReal ((Cfibg : ℝ)
              * (Work.Analysis.IWMultiplier.angleBracket l₂ : ℝ) * (M : ℝ)) *
              eLpNorm Kg p₂ Measure.count := by
        refine (hFibg (l₂ - 1) (P.natDegree * u) hga' (P.eval n₀) Kg).trans
          (mul_le_mul_of_nonneg_right ?_ zero_le)
        rw [← ofReal_coe_eq (Cfibg * Work.Analysis.IWMultiplier.angleBracket (l₂ - 1) * M)]
        refine ENNReal.ofReal_le_ofReal ?_
        push_cast
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbr2 (NNReal.coe_nonneg _)) (NNReal.coe_nonneg _)
      have hb := fiberOpD_model_bound hρ hρ1 (le_of_lt hp₂) l₂ (P.natDegree * u) (P.eval n₀) Kg
        hBG (summable_norm_cw_mStarF (P.natDegree * u))
        (ENNReal.ofReal ((Cfibg : ℝ) * (Work.Analysis.IWMultiplier.angleBracket l₂ : ℝ)
          * (M : ℝ))) h₁ h₂
      refine hb.trans (mul_le_mul_of_nonneg_right ?_ zero_le)
      rw [show (ENNReal.ofReal ((Cfibg : ℝ) * (Work.Analysis.IWMultiplier.angleBracket l₂ : ℝ)
            * (M : ℝ)) + ENNReal.ofReal ((Cfibg : ℝ)
            * (Work.Analysis.IWMultiplier.angleBracket l₂ : ℝ) * (M : ℝ)))
          = ENNReal.ofReal (2 * ((Cfibg : ℝ) * (Work.Analysis.IWMultiplier.angleBracket l₂ : ℝ)
            * (M : ℝ))) from by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : (2 * (Cfibg : ℝ) * (M : ℝ)) ≤ Kg0 := by
        rw [hKg0def]; exact le_max_left _ _
      have h2 : (Work.Analysis.IWMultiplier.angleBracket l₂ : ℝ)
          ≤ 1 + lmaxR l₁ l₂ k₁ k₂ := angleBracket_le_one_add_lmaxR' (l := l₂) le_rfl
      calc 2 * ((Cfibg : ℝ) * (Work.Analysis.IWMultiplier.angleBracket l₂ : ℝ) * (M : ℝ))
          = (2 * (Cfibg : ℝ) * (M : ℝ)) *
              (Work.Analysis.IWMultiplier.angleBracket l₂ : ℝ) := by ring
        _ ≤ Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
    · have hl2L : l₂ ≤ L₀ := by rw [hLdef] at hLc; simp only [smallL] at hLc ⊢; omega
      have hmono : uScale ρ L ≤ uScale ρ L₀ :=
        ExcSupport.scaleCount_mono 1 hρ0 (le_of_lt (not_le.mp hLc))
      have hcast : ((P.natDegree * u : ℕ) : ℤ) = (P.natDegree : ℤ) * (u : ℤ) := by
        push_cast; ring
      have hk : |(-(2 * ((P.natDegree * u : ℕ) : ℤ)))|
          ≤ (P.natDegree : ℤ) * (2 * (uScale ρ L₀ : ℤ) + 2) := by
        have hu : (u : ℤ) ≤ (uScale ρ L₀ : ℤ) := by exact_mod_cast hmono
        have hd : (0 : ℤ) ≤ (P.natDegree : ℤ) := by positivity
        rw [hcast, abs_neg, abs_of_nonneg (by positivity)]
        nlinarith
      refine (hCrude2 l₂ hl2L (-(2 * ((P.natDegree * u : ℕ) : ℤ))) hk (P.eval n₀) Kg).trans
        (mul_le_mul_of_nonneg_right ?_ zero_le)
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : Cc2 ≤ Kg0 := by
        rw [hKg0def]; exact le_trans (le_max_left Cc2 1) (le_max_right _ _)
      have h2 : (1 : ℝ) ≤ 1 + lmaxR l₁ l₂ k₁ k₂ := by linarith
      nlinarith [hCc2.le, hKg0nn, h1, h2]
  -- the residue aggregation
  have hresF : eLpNorm (fun y : ℤ => residueLp p₁.toReal (arithQ ρ (max l₁ l₂))
        (fun x n₀ => ‖(fiberOpD ρ l₁ (mStarF u) (n₀ : ℤ) H x : ℂ)‖ₑ) y) p₁ Measure.count
      ≤ ENNReal.ofReal (Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂)) * eLpNorm H p₁ Measure.count := by
    have hp₁pos : 0 < p₁.toReal :=
      ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one hp₁)) htp₁.ne
    have hcoe : ENNReal.ofReal p₁.toReal = p₁ := ENNReal.ofReal_toReal htp₁.ne
    have h := eLpNorm_residueLp_le (p := p₁.toReal) (q := arithQ ρ (max l₁ l₂)) hp₁pos
      (fun x n₀ => ‖(fiberOpD ρ l₁ (mStarF u) (n₀ : ℤ) H x : ℂ)‖ₑ)
      (ENNReal.ofReal (Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂)) * eLpNorm H p₁ Measure.count)
      (fun n₀ _ => by simpa only [hcoe] using hfibF (n₀ : ℤ))
    simpa only [hcoe] using h
  have hresG : eLpNorm (fun y : ℤ => residueLp p₂.toReal (arithQ ρ (max l₁ l₂))
        (fun x n₀ => ‖(fiberOpPD ρ P l₂ (mStargF P.natDegree u) (n₀ : ℤ) Kg x : ℂ)‖ₑ) y)
          p₂ Measure.count
      ≤ ENNReal.ofReal (Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂)) * eLpNorm Kg p₂ Measure.count := by
    have hp₂pos : 0 < p₂.toReal :=
      ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one hp₂)) htp₂.ne
    have hcoe : ENNReal.ofReal p₂.toReal = p₂ := ENNReal.ofReal_toReal htp₂.ne
    have h := eLpNorm_residueLp_le (p := p₂.toReal) (q := arithQ ρ (max l₁ l₂)) hp₂pos
      (fun x n₀ => ‖(fiberOpPD ρ P l₂ (mStargF P.natDegree u) (n₀ : ℤ) Kg x : ℂ)‖ₑ)
      (ENNReal.ofReal (Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂)) * eLpNorm Kg p₂ Measure.count)
      (fun n₀ _ => by simpa only [hcoe] using hfibG (n₀ : ℤ))
    simpa only [hcoe] using h
  -- the summability hypotheses of the bilinear reduction
  have hs₁ : ∀ (x : ℤ) (n₀ : ℤ), Summable (fun j : ℤ =>
      arithCharD ρ l₁ (n₀ - j) * cw (mStarF u) j * H (x - j)) := by
    intro x n₀
    refine Summable.of_norm_bounded
      ((summable_norm_cw_mStarF u).mul_left
        (((iwArithFreqs ρ l₁).card : ℝ) * max BH 1)) (fun j => ?_)
    have hcard : ‖arithCharD ρ l₁ (n₀ - j)‖ ≤ ((iwArithFreqs ρ l₁).card : ℝ) :=
      (norm_arithCharSet_le (diffFreqs ρ l₁) (n₀ - j)).trans
        (by exact_mod_cast Finset.card_le_card (diffFreqs_subset_iwArithFreqs ρ l₁))
    have h2 : ‖H (x - j)‖ ≤ max BH 1 := le_trans (hBH _) (le_max_left _ _)
    calc ‖arithCharD ρ l₁ (n₀ - j) * cw (mStarF u) j * H (x - j)‖
        = (‖arithCharD ρ l₁ (n₀ - j)‖ * ‖H (x - j)‖) * ‖cw (mStarF u) j‖ := by
          rw [norm_mul, norm_mul]; ring
      _ ≤ (((iwArithFreqs ρ l₁).card : ℝ) * max BH 1) * ‖cw (mStarF u) j‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hcard h2 (norm_nonneg _) (by positivity)) (norm_nonneg _)
  have hs₂ : ∀ (x : ℤ) (n₀ : ℤ), Summable (fun j : ℤ =>
      arithCharD ρ l₂ (P.eval n₀ - j) * cw (mStargF P.natDegree u) j * Kg (x - j)) := by
    intro x n₀
    refine Summable.of_norm_bounded
      ((summable_norm_cw_mStargF P u).mul_left
        (((iwArithFreqs ρ l₂).card : ℝ) * max BG 1)) (fun j => ?_)
    have hcard : ‖arithCharD ρ l₂ (P.eval n₀ - j)‖ ≤ ((iwArithFreqs ρ l₂).card : ℝ) :=
      (norm_arithCharSet_le (diffFreqs ρ l₂) (P.eval n₀ - j)).trans
        (by exact_mod_cast Finset.card_le_card (diffFreqs_subset_iwArithFreqs ρ l₂))
    have h2 : ‖Kg (x - j)‖ ≤ max BG 1 := le_trans (hBG _) (le_max_left _ _)
    calc ‖arithCharD ρ l₂ (P.eval n₀ - j) * cw (mStargF P.natDegree u) j * Kg (x - j)‖
        = (‖arithCharD ρ l₂ (P.eval n₀ - j)‖ * ‖Kg (x - j)‖)
            * ‖cw (mStargF P.natDegree u) j‖ := by
          rw [norm_mul, norm_mul]; ring
      _ ≤ (((iwArithFreqs ρ l₂).card : ℝ) * max BG 1) * ‖cw (mStargF P.natDegree u) j‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hcard h2 (norm_nonneg _) (by positivity)) (norm_nonneg _)
  -- the bilinear reduction
  have hbtw := eLpNorm_smallBtwist_le_of_fiber_bounds ρ P l₁ l₂ (mStarF u)
    (mStargF P.natDegree u) p₁ p₂ hp₁ htp₁ hp₂ htp₂ hsum hs₁ hs₂
    (ENNReal.ofReal (Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂)))
    (ENNReal.ofReal (Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂))) hresF hresG
  -- the constant bookkeeping
  have hAnn : (0 : ℝ) ≤ Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂) :=
    mul_nonneg hKf0nn (by linarith)
  have hBnn : (0 : ℝ) ≤ Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂) :=
    mul_nonneg hKg0nn (by linarith)
  have hreal : Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂) * (Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂)) *
      ((CFun Λ : ℝ) * Wf) * ((CGun Λ : ℝ) * Wg)
      ≤ (kcNN ((CFun Λ : ℝ) * (CGun Λ : ℝ) * Kf0 * Kg0) : ℝ) * Wfin := by
    have h1 : (CFun Λ : ℝ) * (CGun Λ : ℝ) * Kf0 * Kg0
        ≤ (kcNN ((CFun Λ : ℝ) * (CGun Λ : ℝ) * Kf0 * Kg0) : ℝ) := by
      rw [kcNN_coe]
      exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 _)
    have h2 : ((1 + lmaxR l₁ l₂ k₁ k₂) * Wf) * ((1 + lmaxR l₁ l₂ k₁ k₂) * Wg) ≤ Wfin := by
      rw [hWfdef, hWgdef, hWfindef]
      exact weight_comparison (ρ := ρ) hρ0 hLnn
    have hm := mul_le_mul h1 h2 (by positivity) (by positivity)
    calc Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂) * (Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂)) *
          ((CFun Λ : ℝ) * Wf) * ((CGun Λ : ℝ) * Wg)
        = ((CFun Λ : ℝ) * (CGun Λ : ℝ) * Kf0 * Kg0) *
            (((1 + lmaxR l₁ l₂ k₁ k₂) * Wf) * ((1 + lmaxR l₁ l₂ k₁ k₂) * Wg)) := by ring
      _ ≤ (kcNN ((CFun Λ : ℝ) * (CGun Λ : ℝ) * Kf0 * Kg0) : ℝ) * Wfin := hm
  have hAf' : ENNReal.ofReal (Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂))
      = ↑(NNReal.mk (Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂)) hAnn) :=
    ofReal_coe_eq (NNReal.mk (Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂)) hAnn)
  have hBf' : ENNReal.ofReal (Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂))
      = ↑(NNReal.mk (Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂)) hBnn) :=
    ofReal_coe_eq (NNReal.mk (Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂)) hBnn)
  have hWf' : ENNReal.ofReal Wf = ↑(NNReal.mk Wf hWfnn) := ofReal_coe_eq (NNReal.mk Wf hWfnn)
  have hWg' : ENNReal.ofReal Wg = ↑(NNReal.mk Wg hWgnn) := ofReal_coe_eq (NNReal.mk Wg hWgnn)
  have hWfin' : ENNReal.ofReal Wfin = ↑(NNReal.mk Wfin hWfinn) := ofReal_coe_eq (NNReal.mk Wfin hWfinn)
  have hfinal : ENNReal.ofReal (Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂)) *
        ENNReal.ofReal (Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂)) *
        (↑(CFun Λ) * ENNReal.ofReal Wf * F) * (↑(CGun Λ) * ENNReal.ofReal Wg * G)
      ≤ (kcNN ((CFun Λ : ℝ) * (CGun Λ : ℝ) * Kf0 * Kg0) : ENNReal) *
          ENNReal.ofReal Wfin * F * G := by
    rw [hAf', hBf', hWf', hWg', hWfin']
    have hLHS : (↑(NNReal.mk (Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂)) hAnn) *
          ↑(NNReal.mk (Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂)) hBnn) *
          (↑(CFun Λ) * ↑(NNReal.mk Wf hWfnn) * F) *
          (↑(CGun Λ) * ↑(NNReal.mk Wg hWgnn) * G) : ENNReal)
        = ↑((NNReal.mk (Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂)) hAnn) *
              (NNReal.mk (Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂)) hBnn) * (CFun Λ) *
              (NNReal.mk Wf hWfnn) * (CGun Λ) * (NNReal.mk Wg hWgnn)) * (F * G) := by
      rw [show (↑(NNReal.mk (Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂)) hAnn) *
            ↑(NNReal.mk (Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂)) hBnn) *
            (↑(CFun Λ) * ↑(NNReal.mk Wf hWfnn) * F) *
            (↑(CGun Λ) * ↑(NNReal.mk Wg hWgnn) * G) : ENNReal)
          = (↑(NNReal.mk (Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂)) hAnn) *
              ↑(NNReal.mk (Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂)) hBnn) * ↑(CFun Λ) *
              ↑(NNReal.mk Wf hWfnn) * ↑(CGun Λ) * ↑(NNReal.mk Wg hWgnn)) * (F * G)
          from by ring,
        ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_mul,
        ← ENNReal.coe_mul]
    have hRHS : ((kcNN ((CFun Λ : ℝ) * (CGun Λ : ℝ) * Kf0 * Kg0) : ENNReal) *
          ↑(NNReal.mk Wfin hWfinn) * F * G)
        = ↑(kcNN ((CFun Λ : ℝ) * (CGun Λ : ℝ) * Kf0 * Kg0) * (NNReal.mk Wfin hWfinn))
            * (F * G) := by
      rw [show ((kcNN ((CFun Λ : ℝ) * (CGun Λ : ℝ) * Kf0 * Kg0) : ENNReal) *
            ↑(NNReal.mk Wfin hWfinn) * F * G)
          = (kcNN ((CFun Λ : ℝ) * (CGun Λ : ℝ) * Kf0 * Kg0) : ENNReal) *
              ↑(NNReal.mk Wfin hWfinn) * (F * G) from by ring,
        ← ENNReal.coe_mul]
    rw [hLHS, hRHS]
    refine mul_le_mul_of_nonneg_right (ENNReal.coe_le_coe.mpr ?_) zero_le
    rw [← NNReal.coe_le_coe]
    push_cast
    have h := hreal
    linarith
  calc eLpNorm (fun x : ℤ => smallBtwist ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u) H Kg x)
        (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count
      ≤ ENNReal.ofReal (Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂)) *
          ENNReal.ofReal (Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂)) *
          (eLpNorm H p₁ Measure.count * eLpNorm Kg p₂ Measure.count) := hbtw
    _ ≤ ENNReal.ofReal (Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂)) *
          ENNReal.ofReal (Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂)) *
          (↑(CFun Λ) * ENNReal.ofReal Wf * F) * (↑(CGun Λ) * ENNReal.ofReal Wg * G) := by
        rw [show ENNReal.ofReal (Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂)) *
              ENNReal.ofReal (Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂)) *
              (↑(CFun Λ) * ENNReal.ofReal Wf * F) * (↑(CGun Λ) * ENNReal.ofReal Wg * G)
            = ENNReal.ofReal (Kf0 * (1 + lmaxR l₁ l₂ k₁ k₂)) *
              ENNReal.ofReal (Kg0 * (1 + lmaxR l₁ l₂ k₁ k₂)) *
              ((↑(CFun Λ) * ENNReal.ofReal Wf * F) * (↑(CGun Λ) * ENNReal.ofReal Wg * G))
            from by ring]
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        exact mul_le_mul hLH hLKg zero_le zero_le
    _ ≤ (kcNN ((CFun Λ : ℝ) * (CGun Λ : ℝ) * Kf0 * Kg0) : ENNReal) *
          ENNReal.ofReal Wfin * F * G := hfinal

end

end Work.KMTAreas.A7
