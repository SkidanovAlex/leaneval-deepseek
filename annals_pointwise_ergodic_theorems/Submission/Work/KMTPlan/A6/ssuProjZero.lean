import Mathlib
import Submission.Work.KMTPlan.A6.SsuDefs

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.KMTAreas.A7

noncomputable section

/-- **Vanishing of the product of two `iwSymbolSet`s over separated frequency sets.**

Let `Φ` be supported in the arc `ℝ_{≤k}` and `Ψ` in the arc `ℝ_{≤K}`, and suppose that for every
`α ∈ A`, `β ∈ D` the two frequencies are further apart than the sum of the two arc radii,
`2^k + 2^K < ‖β - α‖`.  Then `iwSymbolSet A Φ * iwSymbolSet D Ψ = 0`: a nonzero value at `ξ`
exhibits representations `ξ = α + θ = β + θ'` with `|θ| ≤ 2^k` and `|θ'| ≤ 2^K`, so that
`‖β - α‖ = ‖θ - θ'‖ ≤ 2^k + 2^K`, contradicting the separation hypothesis. -/
theorem iwSymbolSet_mul_eq_zero_of_separated {k K : ℤ}
    {A D : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ Ψ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hΦ : SupportedInArc k Φ) (hΨ : SupportedInArc K Ψ)
    (hsep : ∀ α ∈ A, ∀ β ∈ D, (2 : ℝ) ^ k + (2 : ℝ) ^ K < ‖β - α‖) :
    iwSymbolSet A Φ * iwSymbolSet D Ψ = 0 := by
  funext ξ
  simp only [Pi.mul_apply, iwSymbolSet, Pi.zero_apply]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero (fun α hα => Finset.sum_eq_zero (fun β hβ => ?_))
  by_contra hne
  obtain ⟨h1ne, h2ne⟩ := mul_ne_zero_iff.mp hne
  obtain ⟨θ, hθ, hθeq⟩ := hΦ (ξ - α) h1ne
  obtain ⟨θ', hθ', hθ'eq⟩ := hΨ (ξ - β) h2ne
  have hsum : α + (θ : Work.Analysis.IonescuWainger.Circle)
      = β + (θ' : Work.Analysis.IonescuWainger.Circle) := by
    rw [hθeq, hθ'eq]; abel
  have hβeq : β = α + (θ : Work.Analysis.IonescuWainger.Circle)
      - (θ' : Work.Analysis.IonescuWainger.Circle) := by
    rw [eq_sub_iff_add_eq]
    exact hsum.symm
  have hdiff : β - α = ((θ - θ' : ℝ) : Work.Analysis.IonescuWainger.Circle) := by
    rw [hβeq, AddCircle.coe_sub]; abel
  have hnorm : ‖β - α‖ ≤ |θ| + |θ'| := by
    rw [hdiff]
    calc ‖((θ - θ' : ℝ) : Work.Analysis.IonescuWainger.Circle)‖ ≤ ‖(θ - θ' : ℝ)‖ :=
          QuotientAddGroup.norm_mk_le_norm
      _ = |θ - θ'| := Real.norm_eq_abs _
      _ ≤ |θ| + |θ'| := by simpa [sub_eq_add_neg] using abs_add_le θ (-θ')
  have hb1 : |θ| ≤ (2 : ℝ) ^ k := by
    rw [realArc, Set.mem_Icc] at hθ; exact abs_le.mpr hθ
  have hb2 : |θ'| ≤ (2 : ℝ) ^ K := by
    rw [realArc, Set.mem_Icc] at hθ'; exact abs_le.mpr hθ'
  linarith [hsep α hα β hβ]

/-- **The composite of two Ionescu--Wainger multipliers vanishes when the product of the
symbols does.**  Both `iwOpSet`'s are Fourier multipliers on `ℓ²(ℤ)`, and the composite
multiplier is the multiplier by the product of the two symbols; if that product is identically
zero, `Lp` multiplication by it is zero, so the composite is zero. -/
theorem iwOpSet_iwOpSet_eq_zero_of_symbol_product
    {A D : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ Ψ : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hA : MemLp (iwSymbolSet A Φ) ⊤ circleMeasure)
    (hD : MemLp (iwSymbolSet D Ψ) ⊤ circleMeasure)
    (hprod : ∀ ξ, iwSymbolSet A Φ ξ * iwSymbolSet D Ψ ξ = 0)
    (F : L2Z) :
    iwOpSet A Φ hA (iwOpSet D Ψ hD F) = 0 := by
  have hsl : hA.toLp (iwSymbolSet A Φ) • hD.toLp (iwSymbolSet D Ψ) = 0 :=
    lp_smul_eq_zero hA hD hprod
  have hcomp : iwOpSet A Φ hA (iwOpSet D Ψ hD F)
      = multiplier (hA.toLp (iwSymbolSet A Φ) • hD.toLp (iwSymbolSet D Ψ)) F := by
    show multiplierOf (iwSymbolSet A Φ) hA (multiplierOf (iwSymbolSet D Ψ) hD F)
      = multiplier (hA.toLp (iwSymbolSet A Φ) • hD.toLp (iwSymbolSet D Ψ)) F
    rw [show multiplierOf (iwSymbolSet A Φ) hA = multiplier (hA.toLp (iwSymbolSet A Φ))
          from rfl,
      show multiplierOf (iwSymbolSet D Ψ) hD = multiplier (hD.toLp (iwSymbolSet D Ψ))
          from rfl,
      multiplier_comp]
  rw [hcomp, hsl, multiplier_zero_apply]

theorem ssuProjZero (ρ : ℝ) (l : ℕ) (hl : 1 ≤ l) (u : ℕ) (k' : ℤ) (φ : ℝ → ℂ) (f : ℤ → ℂ)
    (hΦ : MemLp (periodize φ) ⊤ circleMeasure)
    (hSupp : SupportedInArc (-(3 * (u : ℤ))) (periodize φ))
    (hsep : ∀ α ∈ iwArithFreqs ρ (l - 1), ∀ β ∈ Work.KMTAreas.A7.diffFreqs ρ l,
      (2 : ℝ) ^ k' + (2 : ℝ) ^ (-(3 * (u : ℤ))) < ‖β - α‖)
    (hf : MemLp f 2 Measure.count) :
    Work.KMTContract.kmtProj ρ (l - 1) k' (Work.KMTAreas.A7.Tm ρ l φ f) = 0 := by
  have hfℓ : Memℓp f 2 := memlpOfMemLpCount (by norm_num) (by norm_num) hf
  set F : L2Z := ⟨f, hfℓ⟩ with hFdef
  have hFcoe : ⇑F = f := rfl
  have hmD : MemLp (iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l) (periodize φ))
      ⊤ circleMeasure :=
    Work.Analysis.IWMultiplier.memLp_iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l) hΦ
  have hmA : MemLp (iwSymbolSet (iwArithFreqs ρ (l - 1)) (periodize (etaCut Work.KMTContract.kmtEta k')))
      ⊤ circleMeasure := memLp_iwSymbolSet_etaCut (iwArithFreqs ρ (l - 1)) k'
  have hprod : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      iwSymbolSet (iwArithFreqs ρ (l - 1)) (periodize (etaCut Work.KMTContract.kmtEta k')) ξ
        * iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l) (periodize φ) ξ = 0 :=
    fun ξ => congrFun (iwSymbolSet_mul_eq_zero_of_separated
      (supportedInArc_periodize_etaCut k') hSupp hsep) ξ
  have hTm : Work.KMTAreas.A7.Tm ρ l φ f
      = ⇑(iwOpSet (Work.KMTAreas.A7.diffFreqs ρ l) (periodize φ) hmD F) := by
    rw [← hFcoe]
    exact iwConvEqIwOpSetMemlp hmD F
  rw [hTm]
  change iwConv (iwArithFreqs ρ (l - 1)) (periodize (etaCut Work.KMTContract.kmtEta k'))
      ⇑(iwOpSet (Work.KMTAreas.A7.diffFreqs ρ l) (periodize φ) hmD F) = 0
  rw [iwConvEqIwOpSetMemlp hmA (iwOpSet (Work.KMTAreas.A7.diffFreqs ρ l) (periodize φ) hmD F)]
  rw [show iwOpSet (iwArithFreqs ρ (l - 1))
        (periodize (etaCut Work.KMTContract.kmtEta k')) hmA
        (iwOpSet (Work.KMTAreas.A7.diffFreqs ρ l) (periodize φ) hmD F) = 0 from
      iwOpSet_iwOpSet_eq_zero_of_symbol_product hmA hmD hprod F]
  rfl

end

end Work.KMTPlan.A6
