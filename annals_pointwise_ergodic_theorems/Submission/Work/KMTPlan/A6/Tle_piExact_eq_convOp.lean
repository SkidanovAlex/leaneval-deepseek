import Mathlib
import Submission.Work.KMTPlan.A6.MaeTleMdlF

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped BigOperators

/-- Membership in `ℝ_{≤k}` gives the absolute-value bound `|θ| ≤ 2^k`. -/
private lemma abs_le_of_mem_realArc {k : ℤ} {θ : ℝ}
    (h : θ ∈ Work.Analysis.IonescuWainger.realArc k) : |θ| ≤ (2 : ℝ) ^ k := by
  rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc] at h
  rw [abs_le]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **The cutoff is `1` on the arc `ℝ_{≤c-1}` when `2^c ≤ 1/2`.**  This is the "plateau"
statement `mae_Phi_eq_one_of_small` rewritten in the scale `c - 1` that is used below: if
`2^c ≤ 1/2` and `|θ| ≤ 2^{c-1}` then `periodize (etaCut kmtEta c) θ = 1`. -/
private lemma mae_Phi_eq_one_of_arc {c : ℤ} (hc : (2 : ℝ) ^ c ≤ 1 / 2) {θ : ℝ}
    (hθ : |θ| ≤ (2 : ℝ) ^ (c - 1)) :
    Work.Analysis.IonescuWainger.periodize
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta c)
        (θ : Work.Analysis.IonescuWainger.Circle) = 1 := by
  have he : (2 : ℝ) ^ (c - 1) = (2 : ℝ) ^ c / 2 := by
    rw [zpow_sub₀ (show (2 : ℝ) ≠ 0 by norm_num), zpow_one]
  exact mae_Phi_eq_one_of_small hc (hθ.trans_eq he)

/-- **The symbol of the exact-height multiplier is the product symbol
`periodize φ · periodize (etaCut c)`** when `φ` is supported in the arc `ℝ_{≤c-1}` with
`2^c ≤ 1/2` (the cutoff is identically `1` there). -/
private lemma mae_symbol_mul_etaCut_eq {c : ℤ} (hc : (2 : ℝ) ^ c ≤ 1 / 2) {φ : ℝ → ℂ}
    (hΦ : Work.Analysis.IonescuWainger.SupportedInArc (c - 1)
      (Work.Analysis.IonescuWainger.periodize φ)) :
    (fun ξ : Work.Analysis.IonescuWainger.Circle =>
        Work.Analysis.IonescuWainger.periodize φ ξ
          * Work.Analysis.IonescuWainger.periodize
              (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta c) ξ)
      = Work.Analysis.IonescuWainger.periodize φ := by
  funext ξ
  by_cases hξ : Work.Analysis.IonescuWainger.periodize φ ξ = 0
  · rw [hξ, zero_mul]
  · obtain ⟨θ, hθ, rfl⟩ := hΦ ξ hξ
    rw [mae_Phi_eq_one_of_arc hc (abs_le_of_mem_realArc hθ), mul_one]

/-- **The height-`≤ l` multiplier applied to the exact-height `l` projection is the exact-height
multiplier** (`bn-ident` of §6): `Tle ρ l φ ∘ Π_{l,≤c} = Tm ρ l φ` — equivalently, the model
input `Tle ρ l φ (piExact (kmtPj ρ) l c f)` is the convolution of `f` with the explicit kernel
`maeKer ρ l φ` of the exact-height multiplier. -/
theorem Tle_piExact_eq_convOp (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) (c : ℤ)
    (φ : ℝ → ℂ) (hc : (2 : ℝ) ^ c ≤ 1 / 2) {f : ℤ → ℂ}
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hnA : Work.Analysis.IonescuWainger.NonAliasing c
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l))
    (hφmem : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize φ) ⊤
        Work.Analysis.IonescuWainger.circleMeasure)
    (hΦ : Work.Analysis.IonescuWainger.SupportedInArc (c - 1)
        (Work.Analysis.IonescuWainger.periodize φ)) :
    Work.KMTAreas.A7.Tle ρ l φ
        (Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c f)
      = Work.KMTAreas.A7.convOp (Work.KMTPlan.A6.maeKer ρ l φ) f := by
  have hΦ' : Work.Analysis.IonescuWainger.SupportedInArc c
      (Work.Analysis.IonescuWainger.periodize φ) :=
    mae_supportedInArc_mono (by omega : c - 1 ≤ c) hΦ
  rw [mae_Tle_piExact_eq_iwConv ρ hρ hρ1 l c φ hφmem hf hnA hΦ',
    mae_symbol_mul_etaCut_eq hc hΦ]
  exact mae_Tm_eq_convOp_maeKer ρ l φ f

end Work.KMTPlan.A6
