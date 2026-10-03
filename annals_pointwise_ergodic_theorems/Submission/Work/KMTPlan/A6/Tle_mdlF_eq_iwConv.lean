import Mathlib
import Submission.Work.KMTPlan.A6.ModApproxErrCoreExact
import Submission.Work.KMTPlan.A6.besselG
import Submission.Work.KMTPlan.A6.projVanishingF
import Submission.Work.KMTAreas.A7.varphiNt_IW_facts

set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped BigOperators ENNReal NNReal
open Work.Analysis.IonescuWainger
open Work.Analysis.EndVar
open Work.Analysis.IWMultiplier
open Work.KMTAreas.A7
open Work.KMTContract

noncomputable section

/-- The exact-height arithmetic frequency set is contained in the height-`≤ l` set. -/
theorem diffFreqs_subset (ρ : ℝ) (l : ℕ) :
    Work.KMTAreas.A7.diffFreqs ρ l ⊆ iwArithFreqs ρ l := by
  unfold Work.KMTAreas.A7.diffFreqs
  by_cases h : l = 0
  · subst h; intro x hx; exact hx
  · rw [if_neg h]; exact Finset.sdiff_subset

/-- **Diagonal collapse of a product of two sums over nested index sets.**  Let `D ⊆ A` and let
`f g : ι → ℂ` satisfy `f a * g b ≠ 0 → a = b` for `a ∈ A`, `b ∈ D`.  Then
`(∑_{a ∈ A} f a) * (∑_{b ∈ D} g b) = ∑_{b ∈ D} f b * g b`. -/
private theorem sum_mul_sum_eq_diag_sdiff {ι : Type*} (A D : Finset ι) (hDA : D ⊆ A)
    (f g : ι → ℂ) (h1 : ∀ a ∈ A, ∀ b ∈ D, f a * g b ≠ 0 → a = b) :
    (∑ a ∈ A, f a) * (∑ b ∈ D, g b) = ∑ b ∈ D, f b * g b := by
  classical
  rw [Finset.sum_mul]
  have hstep : ∀ a ∈ A, f a * (∑ b ∈ D, g b) = if a ∈ D then f a * g a else 0 := by
    intro a ha
    rw [Finset.mul_sum]
    have hterm : ∀ b ∈ D, f a * g b = if a = b then f a * g b else 0 := by
      intro b hb
      by_cases hab : a = b
      · rw [if_pos hab]
      · rw [if_neg hab]
        by_contra hne
        exact hab (h1 a ha b hb hne)
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl hstep, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hDA]

/-- **The IW symbol over a smaller frequency set.**  If `A` is non-aliasing at scale `k`, `D ⊆ A`,
and `Φ`, `Ψ` are both supported in the arc `ℝ_{≤k}`, then
`iwSymbolSet A Φ * iwSymbolSet D Ψ = iwSymbolSet D (Φ * Ψ)`. -/
theorem iwSymbolSet_mul_diffFreqs (k : ℤ) {A D : Finset Circle} (hDA : D ⊆ A)
    (hA : NonAliasing k A) {Φ Ψ : Circle → ℂ}
    (hΦ : SupportedInArc k Φ) (hΨ : SupportedInArc k Ψ) :
    iwSymbolSet A Φ * iwSymbolSet D Ψ = iwSymbolSet D (Φ * Ψ) := by
  funext ξ
  simp only [iwSymbolSet_apply, Pi.mul_apply]
  refine sum_mul_sum_eq_diag_sdiff A D hDA _ _ ?_
  intro a ha b hb hne
  obtain ⟨hfa, hgb⟩ := mul_ne_zero_iff.mp hne
  obtain ⟨θ, hθ, hθξ⟩ := hΦ _ hfa
  obtain ⟨θ', hθ', hθ'ξ⟩ := hΨ _ hgb
  have e1 : a + (θ : Circle) = ξ := by rw [hθξ]; abel
  have e2 : b + (θ' : Circle) = ξ := by rw [hθ'ξ]; abel
  exact (hA a ha b (hDA hb) θ hθ θ' hθ' (e1.trans e2.symm)).1

/-- **Composition of two IW multipliers over nested frequency sets.**  If
`iwSymbolSet A Φ * iwSymbolSet D Ψ = iwSymbolSet D (Φ * Ψ)` (pointwise), then the composition of
the two multipliers is the multiplier with the product symbol. -/
theorem multiplierOf_comp_diff {A D : Finset Circle} {Φ Ψ : Circle → ℂ}
    (hA : MemLp (iwSymbolSet A Φ) ⊤ circleMeasure)
    (hD : MemLp (iwSymbolSet D Ψ) ⊤ circleMeasure)
    (hP : MemLp (iwSymbolSet D (Φ * Ψ)) ⊤ circleMeasure)
    (hsym : iwSymbolSet A Φ * iwSymbolSet D Ψ = iwSymbolSet D (Φ * Ψ)) :
    (multiplierOf (iwSymbolSet A Φ) hA).comp (multiplierOf (iwSymbolSet D Ψ) hD)
      = multiplierOf (iwSymbolSet D (Φ * Ψ)) hP := by
  have key : hA.toLp (iwSymbolSet A Φ) • hD.toLp (iwSymbolSet D Ψ)
      = hP.toLp (iwSymbolSet D (Φ * Ψ)) := by
    refine Lp.ext ?_
    have e1 : (hA.toLp (iwSymbolSet A Φ) • hD.toLp (iwSymbolSet D Ψ) :
          Lp ℂ ⊤ circleMeasure)
        =ᵐ[circleMeasure]
          (⇑(hA.toLp (iwSymbolSet A Φ)) • ⇑(hD.toLp (iwSymbolSet D Ψ)) : Circle → ℂ) :=
      Lp.coeFn_lpSMul _ _
    have e2 : ⇑(hA.toLp (iwSymbolSet A Φ)) =ᵐ[circleMeasure] iwSymbolSet A Φ :=
      MemLp.coeFn_toLp hA
    have e3 : ⇑(hD.toLp (iwSymbolSet D Ψ)) =ᵐ[circleMeasure] iwSymbolSet D Ψ :=
      MemLp.coeFn_toLp hD
    have e4 : ⇑(hP.toLp (iwSymbolSet D (Φ * Ψ))) =ᵐ[circleMeasure]
        iwSymbolSet A Φ * iwSymbolSet D Ψ :=
      (MemLp.coeFn_toLp hP).trans (Filter.Eventually.of_forall (fun x => (congrFun hsym x).symm))
    filter_upwards [e1, e2, e3, e4] with x hx1 hx2 hx3 hx4
    simp only [smul_eq_mul, Pi.mul_apply, hx1, hx2, hx3, hx4]
  apply ContinuousLinearMap.ext
  intro F
  show multiplier (hA.toLp (iwSymbolSet A Φ)) (multiplier (hD.toLp (iwSymbolSet D Ψ)) F)
      = multiplier (hP.toLp (iwSymbolSet D (Φ * Ψ))) F
  rw [multiplier_comp, key]

/-- **The functional calculus of the exact-height piece (`bn-ident`).**  Let `(l,c)` be
non-aliasing, `Φ = periodize φ` supported in the arc `ℝ_{≤c}` and in `L^∞`.  Then the composition
of the height-`≤ l` multiplier with symbol `Φ` with the exact-height-`l` projection
`Π_{l,≤c} = piExact l c` is the `diffFreqs`-multiplier with symbol `Φ · η_{≤c}`. -/
theorem Tle_piExact_eq_iwConv' (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) (c : ℤ)
    (φ : ℝ → ℂ) (hφmem : MemLp (periodize φ) ⊤ circleMeasure) {f : ℤ → ℂ}
    (hf : MemLp f 2 Measure.count)
    (hnA : NonAliasing c (iwArithFreqs ρ l))
    (hΦ : SupportedInArc c (periodize φ)) :
    Tle ρ l φ (piExact (kmtPj ρ) l c f)
      = iwConv (diffFreqs ρ l) (fun ξ => periodize φ ξ * periodize (etaCut kmtEta c) ξ) f := by
  set A : Finset Circle := iwArithFreqs ρ l with hAdef
  set D : Finset Circle := diffFreqs ρ l with hDdef
  set Φ : Circle → ℂ := periodize φ with hΦdef
  set Ψ : Circle → ℂ := periodize (etaCut kmtEta c) with hΨdef
  have hAmem : MemLp (iwSymbolSet A Φ) ⊤ circleMeasure := memLp_iwSymbolSet A hφmem
  have hΨmem : MemLp Ψ ⊤ circleMeasure := by rw [hΨdef]; exact memLp_periodize_etaCut c
  have hΨsupp : SupportedInArc c Ψ := by
    rw [hΨdef]; exact supportedInArc_periodize_etaCut c
  have hDmem : MemLp (iwSymbolSet D Ψ) ⊤ circleMeasure := memLp_iwSymbolSet D hΨmem
  have hPmem : MemLp (iwSymbolSet D (Φ * Ψ)) ⊤ circleMeasure :=
    memLp_iwSymbolSet D (hφmem.mul hΨmem)
  have hsym : iwSymbolSet A Φ * iwSymbolSet D Ψ = iwSymbolSet D (Φ * Ψ) :=
    iwSymbolSet_mul_diffFreqs c (by rw [hDdef, hAdef]; exact diffFreqs_subset ρ l) hnA hΦ hΨsupp
  have hcomp : (multiplierOf (iwSymbolSet A Φ) hAmem).comp (multiplierOf (iwSymbolSet D Ψ) hDmem)
      = multiplierOf (iwSymbolSet D (Φ * Ψ)) hPmem :=
    multiplierOf_comp_diff hAmem hDmem hPmem hsym
  have hmdl : piExact (kmtPj ρ) l c f = ⇑(multiplierOf (iwSymbolSet D Ψ) hDmem (toL2Z hf)) := by
    have h1 : piExact (kmtPj ρ) l c (⇑(toL2Z hf))
        = ⇑(multiplierOf (piSym ρ l c) (memLp_piSym ρ l c) (toL2Z hf)) :=
      piExact_eq_multiplier ρ hρ hρ1 l c (toL2Z hf)
    rw [multiplierOf_congr_bG' (memLp_piSym ρ l c) hDmem (by rfl)] at h1
    exact h1
  calc Tle ρ l φ (piExact (kmtPj ρ) l c f)
      = iwConv A Φ (piExact (kmtPj ρ) l c f) := rfl
    _ = iwConv A Φ (⇑(multiplierOf (iwSymbolSet D Ψ) hDmem (toL2Z hf))) := by rw [hmdl]
    _ = ⇑(iwOpSet A Φ hAmem (multiplierOf (iwSymbolSet D Ψ) hDmem (toL2Z hf))) :=
          iwConvEqIwOpSetMemlp hAmem _
    _ = ⇑((multiplierOf (iwSymbolSet A Φ) hAmem).comp
            (multiplierOf (iwSymbolSet D Ψ) hDmem) (toL2Z hf)) := rfl
    _ = ⇑(multiplierOf (iwSymbolSet D (Φ * Ψ)) hPmem (toL2Z hf)) := by rw [hcomp]
    _ = iwConv D (Φ * Ψ) (⇑(toL2Z hf)) := (iwConvEqIwOpSetMemlp hPmem (toL2Z hf)).symm
    _ = iwConv D (Φ * Ψ) f := by rw [toL2Z_coe hf]

/-- The modulated bump `φ_{N,t}` is bounded by `2` (the modulation is unimodular). -/
private lemma norm_varphiNt_le_two_local (N k : ℕ) (t : ℝ) (x : ℝ) :
    ‖Work.KMTAreas.A7.varphiNt N k t x‖ ≤ 2 := by
  rw [Work.KMTAreas.A7.varphiNt, norm_mul, Work.KMTAreas.A7.norm_ee, mul_one]
  by_cases hk : k = 0
  · rw [Work.KMTAreas.A7.varphiN, if_pos hk]
    exact le_trans (Work.KMTContract.norm_kmtEta_le _) (by norm_num)
  · rw [Work.KMTAreas.A7.varphiN, if_neg hk]
    calc ‖Work.KMTContract.kmtEta
            (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * x)
          - Work.KMTContract.kmtEta
            (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * x)‖
        ≤ ‖Work.KMTContract.kmtEta
            (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * x)‖
          + ‖Work.KMTContract.kmtEta
            (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * x)‖ :=
          norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (Work.KMTContract.norm_kmtEta_le _) (Work.KMTContract.norm_kmtEta_le _)
      _ = 2 := by norm_num

theorem Tle_mdlF_eq_iwConv (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (u l N k : ℕ) (t : ℝ)
    {f : ℤ → ℂ} (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hnA : Work.Analysis.IonescuWainger.NonAliasing (-(u : ℤ))
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l))
    (hΦ : Work.Analysis.IonescuWainger.SupportedInArc (-(u : ℤ))
        (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.varphiNt N k t))) :
    Work.KMTAreas.A7.Tle ρ l (Work.KMTAreas.A7.varphiNt N k t) (Work.KMTPlan.A6.mdlF ρ u l f)
      = Work.Analysis.IWMultiplier.iwConv (Work.KMTAreas.A7.diffFreqs ρ l)
          (fun ξ => Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.varphiNt N k t) ξ
            * Work.Analysis.IonescuWainger.periodize
                (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(u : ℤ))) ξ) f := by
  have hφmem : MemLp (periodize (Work.KMTAreas.A7.varphiNt N k t)) ⊤ circleMeasure := by
    have hRpos : (0 : ℝ) < (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    refine memLp_periodize (φ := Work.KMTAreas.A7.varphiNt N k t) (C := 2)
      (Work.KMTAreas.A7.contDiff_varphiNt N k t).continuous.measurable hRpos.le ?_ ?_
    · intro x hx
      by_contra hne
      exact absurd (Work.KMTAreas.A7.varphiNt_support N k t x hne) (not_le.mpr hx)
    · intro x
      exact norm_varphiNt_le_two_local N k t x
  exact Tle_piExact_eq_iwConv' ρ hρ hρ1 l (-(u : ℤ)) (Work.KMTAreas.A7.varphiNt N k t)
    hφmem hf hnA hΦ

end

end Work.KMTPlan.A6
