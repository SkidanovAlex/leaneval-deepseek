/-
# Vanishing of the outer projection on the piece `Gpiece`

This file proves `Work.KMTPlan.A6.projVanishingG`: the Ionescu--Wainger projection
`Pi_{<=L,<=d(-Log N + L)}` annihilates the second-function piece
`Gpiece (kmtPj rho) d 0 l2 k2 N g` of section 5 of Krause--Mirek--Tao, under the case hypothesis
`L < l2 or L + 2 <= k2`, the smallness hypothesis `max k2 L + 2 <= Log N` and the non-aliasing
hypothesis for the frequency set `(Q/Z)_{<=l2} union (Q/Z)_{<=L}` at the scale
`d(-Log N + max k2 L) + 1`.

The proof has three parts.

* The symbol of the piece vanishes against the symbol of the projection.  Writing
  `M_{l,k} = sum_{alpha in (Q/Z)_{<=l}} eta_{<=k}(. - alpha)` for the symbol of `kmtProj rho l k`,
  the piece's symbol is `sum_{alpha in Anew} Psi(. - alpha)` where `Anew = newFreqs rho l2` is
  the frequency set of height exactly `l2` and `Psi` is the difference of the two rescaled cutoffs
  at the scales `d(-Log N + k2)` and `d(-Log N + k2 - 1)`.  Every term of the product
  `M_{L,d(-Log N+L)} * sum_{alpha} Psi(. - alpha)` vanishes: the cross terms (`alpha != beta`) by
  non-aliasing (`Phi_sep`), the diagonal terms (`alpha = beta`, which can only occur in the case
  `L + 2 <= k2`) because on the arc `R_{<=d(-Log N+L)}` both cutoffs of `Psi` equal `1`
  (`Phi_eq_one_of_small`).
* The projections are Fourier multipliers on `l^2(Z)` (`iwConvEqIwOpSetMemlp`), so the composite
  of two projections is the multiplier by the product of their symbols.
* Assembly.  The piece is a linear combination of projections, hence of multipliers; the product
  of the symbols being zero makes the composite multiplier zero.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.Symbol
import Submission.Work.KMTAreas.A7.Basic
import Submission.Work.KMTPlan.A6.iwConvEqIwOpSetMemlp
import Submission.Work.KMTPlan.A6.memlpOfMemLpCount
import Submission.Work.KMTPlan.A6.multiplierOfSub
import Submission.Work.KMTContract.periodizeCoeEqTsum

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Submission.PointwiseErgodicTheorems

noncomputable section

/-- The frequency circle, disambiguated. -/
abbrev Circ : Type := Work.Analysis.IonescuWainger.Circle

/-- The bottom scale of the pieces, `a = -(u : Z)` for `u = 0`. -/
abbrev gzero : ℤ := -((0 : ℕ) : ℤ)

/-! ## The rescaled cutoffs and their basic properties -/

/-- The periodisation of the rescaled cutoff `eta_{<=k}` is bounded. -/
theorem memLp_periodize_etaCutG (k : ℤ) :
    MemLp (periodize (etaCut Work.KMTContract.kmtEta k)) ⊤ circleMeasure :=
  memLp_periodize (Work.KMTAreas.A7.contDiff_etaCut k).continuous.measurable
    (R := (2 : ℝ) ^ k) (C := 1) (le_of_lt (zpow_pos (by norm_num) k))
    (fun x hx => Work.KMTAreas.A7.etaCut_eq_zero_of_le (le_of_lt hx))
    (fun x => Work.KMTAreas.A7.norm_etaCut_le_one k x)

/-- The IW symbol of the rescaled cutoff is bounded. -/
theorem memLp_iwSymbolSet_etaCutG (A : Finset Circ) (k : ℤ) :
    MemLp (iwSymbolSet A (periodize (etaCut Work.KMTContract.kmtEta k))) ⊤ circleMeasure :=
  Work.Analysis.IWMultiplier.memLp_iwSymbolSet A (memLp_periodize_etaCutG k)

/-- The rescaled cutoff is supported in the arc `R_{<=k}`. -/
theorem supportedInArc_periodize_etaCutG (k : ℤ) :
    SupportedInArc k (periodize (etaCut Work.KMTContract.kmtEta k)) :=
  supportedInArc_periodize (fun _ hx => Work.KMTAreas.A7.etaCut_ne_zero_mem_realArc k hx)
    (Work.KMTAreas.A7.summable_etaCut_shift k)

/-- **The vanishing of a product of two IW symbols whose frequency sets are separated.**  If, for
all `beta in A` and `alpha in D`, the `alpha`-translate of `Psi` vanishes at every frequency where
the `beta`-translate of `Phi` does not, then the product of the two symbols vanishes. -/
theorem iwSymbolSet_mul_eq_zero_of {A D : Finset Circ} {Φ Ψ : Circ → ℂ}
    (hterm : ∀ β ∈ A, ∀ α ∈ D, ∀ ξ : Circ, Φ (ξ - β) = 0 ∨ Ψ (ξ - α) = 0) :
    iwSymbolSet A Φ * iwSymbolSet D Ψ = 0 := by
  funext ξ
  simp only [Pi.mul_apply, iwSymbolSet, Pi.zero_apply]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero (fun β hβ => Finset.sum_eq_zero (fun α hα => ?_))
  rcases hterm β hβ α hα ξ with h | h
  · rw [h, zero_mul]
  · rw [h, mul_zero]

/-! ## `L^infty` membership of the symbols -/

theorem memLp_PiEx (ρ : ℝ) (l : ℕ) (k : ℤ) : MemLp (PiEx ρ l k) ⊤ circleMeasure := by
  by_cases hl : l = 0
  · rw [PiEx, if_pos hl]
    exact memLp_iwSymbolSet_etaCutG (iwArithFreqs ρ 0) k
  · rw [PiEx, if_neg hl]
    exact (memLp_iwSymbolSet_etaCutG (iwArithFreqs ρ l) k).sub
      (memLp_iwSymbolSet_etaCutG (iwArithFreqs ρ (l - 1)) k)

theorem memLp_Gsym (ρ : ℝ) (d : ℤ) (l₂ : ℕ) (k₂ : ℤ) (N : ℕ) :
    MemLp (Gsym ρ d l₂ k₂ N) ⊤ circleMeasure := by
  by_cases hk : k₂ = gzero
  · rw [Gsym, if_pos hk]
    exact memLp_PiEx ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂))
  · rw [Gsym, if_neg hk]
    exact (memLp_PiEx ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂))).sub
      (memLp_PiEx ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + (k₂ - 1))))

/-! ## The `l^2` side: the projections as Fourier multipliers -/

/-- The symbol of `kmtProj rho l k`, as an element of `L^infty` of the frequency circle. -/
noncomputable def symL (ρ : ℝ) (l : ℕ) (k : ℤ) : Lp ℂ ⊤ circleMeasure :=
  (memLp_iwSymbolSet_etaCutG (iwArithFreqs ρ l) k).toLp
    (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k)))

/-- The projection `kmtProj rho l k` as a Fourier multiplier on `l^2(Z)`. -/
noncomputable def projCLMG (ρ : ℝ) (l : ℕ) (k : ℤ) : L2Z →L[ℂ] L2Z :=
  iwOpSet (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k))
    (memLp_iwSymbolSet_etaCutG (iwArithFreqs ρ l) k)

theorem projCLMG_eq_multiplier (ρ : ℝ) (l : ℕ) (k : ℤ) :
    projCLMG ρ l k = multiplier (symL ρ l k) := rfl

/-- **The projection acts on all of `l^2(Z)` by convolution with the Fourier coefficients of its
symbol** (`iwConvEqIwOpSetMemlp`), i.e. it is the multiplier by its symbol. -/
theorem kmtProj_eq_apply (ρ : ℝ) (l : ℕ) (k : ℤ) (F : L2Z) :
    Work.KMTContract.kmtProj ρ l k (⇑F) = ⇑(projCLMG ρ l k F) :=
  iwConvEqIwOpSetMemlp (memLp_iwSymbolSet_etaCutG (iwArithFreqs ρ l) k) F

/-- The `l^2` element attached to a function `g` in `l^2(Z)`. -/
noncomputable def toL2ZPG {g : ℤ → ℂ} (hg : MemLp g 2 Measure.count) : L2Z :=
  ⟨g, memlpOfMemLpCount (by norm_num) (by norm_num) hg⟩

@[simp] theorem toL2ZPG_coe {g : ℤ → ℂ} (hg : MemLp g 2 Measure.count) :
    ⇑(toL2ZPG hg) = g := rfl

/-- The `l^2` projection of a function in `l^2(Z)`. -/
theorem kmtProj_eq_apply_toL2Z (ρ : ℝ) (l : ℕ) (k : ℤ) {g : ℤ → ℂ}
    (hg : MemLp g 2 Measure.count) :
    Work.KMTContract.kmtProj ρ l k g = ⇑(projCLMG ρ l k (toL2ZPG hg)) :=
  kmtProj_eq_apply ρ l k (toL2ZPG hg)

/-! ## The exact-height combination and the piece, as continuous linear maps -/

/-- The symbol of `piExact (kmtPj rho) l k`, as an element of `L^infty`. -/
noncomputable def PmL (ρ : ℝ) (l : ℕ) (k : ℤ) : Lp ℂ ⊤ circleMeasure :=
  if l = 0 then symL ρ 0 k else symL ρ l k - symL ρ (l - 1) k

/-- The exact-height projection as a continuous linear map on `l^2(Z)`. -/
noncomputable def PiExCLM (ρ : ℝ) (l : ℕ) (k : ℤ) : L2Z →L[ℂ] L2Z :=
  if l = 0 then projCLMG ρ 0 k else projCLMG ρ l k - projCLMG ρ (l - 1) k

/-- The symbol of the piece `Gpiece (kmtPj rho) d 0 l2 k2 N`, as an element of `L^infty`. -/
noncomputable def Gm (ρ : ℝ) (d : ℤ) (l₂ : ℕ) (k₂ : ℤ) (N : ℕ) : Lp ℂ ⊤ circleMeasure :=
  if k₂ = gzero then PmL ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂))
  else PmL ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂))
      - PmL ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + (k₂ - 1)))

/-- The piece `Gpiece (kmtPj rho) d 0 l2 k2 N` as a continuous linear map on `l^2(Z)`. -/
noncomputable def Gclm (ρ : ℝ) (d : ℤ) (l₂ : ℕ) (k₂ : ℤ) (N : ℕ) : L2Z →L[ℂ] L2Z :=
  if k₂ = gzero then PiExCLM ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂))
  else PiExCLM ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂))
      - PiExCLM ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + (k₂ - 1)))

theorem PiExCLM_eq (ρ : ℝ) (l : ℕ) (k : ℤ) : PiExCLM ρ l k = multiplier (PmL ρ l k) := by
  by_cases hl : l = 0
  · rw [PiExCLM, if_pos hl, PmL, if_pos hl, projCLMG_eq_multiplier]
  · rw [PiExCLM, if_neg hl, PmL, if_neg hl, projCLMG_eq_multiplier, projCLMG_eq_multiplier,
      multiplier_sub]

theorem Gclm_eq (ρ : ℝ) (d : ℤ) (l₂ : ℕ) (k₂ : ℤ) (N : ℕ) :
    Gclm ρ d l₂ k₂ N = multiplier (Gm ρ d l₂ k₂ N) := by
  by_cases hk : k₂ = gzero
  · rw [Gclm, if_pos hk, Gm, if_pos hk, PiExCLM_eq]
  · rw [Gclm, if_neg hk, Gm, if_neg hk, PiExCLM_eq, PiExCLM_eq, ← multiplier_sub]

/-! ## The piece as a function -/

/-- At the level of functions, the exact-height combination is `PiEx`. -/
theorem piExact_eq (ρ : ℝ) (l : ℕ) (k : ℤ) (F : L2Z) :
    Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l k (⇑F)
      = ⇑(PiExCLM ρ l k F) := by
  by_cases hl : l = 0
  · rw [Work.Analysis.EndVar.piExact, if_pos hl, PiExCLM, if_pos hl]
    simp only [Work.KMTContract.kmtPj_proj]
    exact kmtProj_eq_apply ρ 0 k F
  · rw [Work.Analysis.EndVar.piExact, if_neg hl, PiExCLM, if_neg hl]
    simp only [Work.KMTContract.kmtPj_proj]
    rw [kmtProj_eq_apply, kmtProj_eq_apply]
    show ⇑(projCLMG ρ l k F) - ⇑(projCLMG ρ (l - 1) k F)
      = ⇑(projCLMG ρ l k F - projCLMG ρ (l - 1) k F)
    rw [lp.coeFn_sub]

/-- At the level of functions, the piece is `Gclm`. -/
theorem piece_eq (ρ : ℝ) (l₂ : ℕ) (k₂ : ℤ) (d : ℤ) (N : ℕ) (F : L2Z) :
    Work.Analysis.EndVar.piece (Work.KMTContract.kmtPj ρ) l₂
        (fun s => d * (-(Work.Analysis.EndVar.logN N) + s)) gzero k₂ (⇑F)
      = ⇑(Gclm ρ d l₂ k₂ N F) := by
  by_cases hk : k₂ = gzero
  · rw [Work.Analysis.EndVar.piece, if_pos hk, Gclm, if_pos hk]
    exact piExact_eq ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂)) F
  · rw [Work.Analysis.EndVar.piece, if_neg hk, Gclm, if_neg hk]
    rw [piExact_eq, piExact_eq]
    show ⇑(PiExCLM ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂)) F)
        - ⇑(PiExCLM ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + (k₂ - 1))) F)
      = ⇑(PiExCLM ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂)) F
          - PiExCLM ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + (k₂ - 1))) F)
    rw [lp.coeFn_sub]

/-! ## The `L^infty` symbols versus the pointwise symbols -/

/-- The `L^infty` symbol of the exact-height combination is a.e. the pointwise symbol `PiEx`. -/
theorem PmL_coe (ρ : ℝ) (l : ℕ) (k : ℤ) :
    (PmL ρ l k : Circ → ℂ) =ᵐ[circleMeasure] PiEx ρ l k := by
  by_cases hl : l = 0
  · rw [PmL, if_pos hl, PiEx, if_pos hl]
    exact MemLp.coeFn_toLp (memLp_iwSymbolSet_etaCutG (iwArithFreqs ρ 0) k)
  · rw [PmL, if_neg hl, PiEx, if_neg hl]
    have h2 : (symL ρ l k : Circ → ℂ) =ᵐ[circleMeasure]
        iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k)) :=
      MemLp.coeFn_toLp (memLp_iwSymbolSet_etaCutG (iwArithFreqs ρ l) k)
    have h3 : (symL ρ (l - 1) k : Circ → ℂ) =ᵐ[circleMeasure]
        iwSymbolSet (iwArithFreqs ρ (l - 1)) (periodize (etaCut Work.KMTContract.kmtEta k)) :=
      MemLp.coeFn_toLp (memLp_iwSymbolSet_etaCutG (iwArithFreqs ρ (l - 1)) k)
    filter_upwards [Lp.coeFn_sub (symL ρ l k) (symL ρ (l - 1) k), h2, h3] with ξ h1 h2' h3'
    rw [h1, Pi.sub_apply, h2', h3']
    rfl

/-- The `L^infty` symbol of the piece is a.e. the pointwise symbol `Gsym`. -/
theorem Gm_coe (ρ : ℝ) (d : ℤ) (l₂ : ℕ) (k₂ : ℤ) (N : ℕ) :
    (Gm ρ d l₂ k₂ N : Circ → ℂ) =ᵐ[circleMeasure] Gsym ρ d l₂ k₂ N := by
  by_cases hk : k₂ = gzero
  · rw [Gm, if_pos hk, Gsym, if_pos hk]
    exact PmL_coe ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂))
  · rw [Gm, if_neg hk, Gsym, if_neg hk]
    filter_upwards [Lp.coeFn_sub (PmL ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂)))
        (PmL ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + (k₂ - 1)))),
      PmL_coe ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + k₂)),
      PmL_coe ρ l₂ (d * (-(Work.Analysis.EndVar.logN N) + (k₂ - 1)))] with ξ h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    rfl

/-! ## The composite multiplier -/

theorem multiplier_zero_applyG (F : L2Z) :
    multiplier (0 : Lp ℂ ⊤ circleMeasure) F = 0 := by
  have h := fourierZ_multiplier (0 : Lp ℂ ⊤ circleMeasure) F
  rw [Lp.zero_smul] at h
  have h2 : multiplier (0 : Lp ℂ ⊤ circleMeasure) F
      = fourierZ.symm (fourierZ (multiplier (0 : Lp ℂ ⊤ circleMeasure) F)) :=
    (fourierZ.symm_apply_apply _).symm
  rw [h2, h, map_zero]

/-- **If the pointwise product of the outer symbol with the piece symbol vanishes, then the
composite multiplier vanishes.** -/
theorem symL_smul_Gm_eq_zero (ρ : ℝ) (L : ℕ) (K : ℤ) (d : ℤ) (l₂ : ℕ) (k₂ : ℤ) (N : ℕ)
    (h : ∀ ξ : Circ, iwSymbolSet (iwArithFreqs ρ L)
        (periodize (etaCut Work.KMTContract.kmtEta K)) ξ * Gsym ρ d l₂ k₂ N ξ = 0) :
    (symL ρ L K • Gm ρ d l₂ k₂ N : Lp ℂ ⊤ circleMeasure) = 0 := by
  refine Lp.ext ?_
  have h2 : (symL ρ L K : Circ → ℂ) =ᵐ[circleMeasure]
      iwSymbolSet (iwArithFreqs ρ L) (periodize (etaCut Work.KMTContract.kmtEta K)) :=
    MemLp.coeFn_toLp (memLp_iwSymbolSet_etaCutG (iwArithFreqs ρ L) K)
  filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := ⊤) (r := ⊤) (symL ρ L K)
      (Gm ρ d l₂ k₂ N),
    h2, Gm_coe ρ d l₂ k₂ N, Lp.coeFn_zero ℂ ⊤ circleMeasure] with ξ h1 h2' h3 h4
  rw [h1]
  show ⇑(symL ρ L K) ξ * ⇑(Gm ρ d l₂ k₂ N) ξ = ⇑(0 : Lp ℂ ⊤ circleMeasure) ξ
  rw [h2', h3, h4]
  exact h ξ

/-! ## The support and smallness lemmas for the rescaled cutoffs -/

/-- **Separation of two frequency translates.**  If the frequency set `A` is non-aliasing at the
scale `K`, then the `kα`-translate of `η_{≤kα}` vanishes wherever the `kβ`-translate of
`η_{≤kβ}` does not, provided `α ≠ β` and both scales are at most `K`. -/
theorem Phi_sep {K kβ kα : ℤ} {A : Finset Circ} (hNA : NonAliasing K A) {β α : Circ}
    (hβ : β ∈ A) (hα : α ∈ A) (hne : α ≠ β) (hkβ : kβ ≤ K) (hkα : kα ≤ K) (ξ : Circ)
    (h : periodize (etaCut Work.KMTContract.kmtEta kβ) (ξ - β) ≠ 0) :
    periodize (etaCut Work.KMTContract.kmtEta kα) (ξ - α) = 0 := by
  by_contra h'
  obtain ⟨θ, hθ, hθeq⟩ := supportedInArc_periodize_etaCutG kβ (ξ - β) h
  obtain ⟨θ', hθ', hθ'eq⟩ := supportedInArc_periodize_etaCutG kα (ξ - α) h'
  have hsum : β + (θ : Circ) = α + (θ' : Circ) := by
    rw [hθeq, hθ'eq]; abel
  have hres := hNA β hβ α hα θ (realArc_mono hkβ hθ) θ' (realArc_mono hkα hθ') hsum
  exact hne hres.1.symm

/-- **The cutoff is `1` on a small arc.**  If `2^k ≤ 1/2` and `|θ| ≤ 2^k/2`, then
`η_{≤k}` equals `1` at the circle point `θ`. -/
theorem Phi_eq_one_of_small {k : ℤ} (hk : (2 : ℝ) ^ k ≤ 1 / 2) {θ : ℝ}
    (hθ : |θ| ≤ (2 : ℝ) ^ k / 2) :
    periodize (etaCut Work.KMTContract.kmtEta k) (θ : Circ) = 1 := by
  rw [Work.KMTContract.periodizeCoeEqTsum (etaCut Work.KMTContract.kmtEta k) θ]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hzero : ∀ n : ℤ, n ≠ 0 → etaCut Work.KMTContract.kmtEta k (θ + (n : ℝ)) = 0 := by
    intro n hn
    rw [etaCut]
    refine Work.KMTContract.kmtEta_zero ?_
    rw [abs_div, abs_of_pos hpos, one_le_div hpos]
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast (Int.one_le_abs hn)
    have h2 : |(n : ℝ)| - |θ| ≤ |θ + (n : ℝ)| := by
      have h := abs_sub_abs_le_abs_sub (n : ℝ) (-θ)
      rw [sub_neg_eq_add] at h
      simpa [sub_eq_add_neg, add_comm] using h
    have h3 : (2 : ℝ) ^ k ≤ 1 - (2 : ℝ) ^ k / 2 := by linarith
    linarith [hpos, hθ]
  rw [tsum_eq_single 0 (fun n hn => hzero n hn)]
  simp only [Int.cast_zero, add_zero]
  rw [etaCut]
  refine Work.KMTContract.kmtEta_one ?_
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  linarith [hpos, hθ]

/-! ## The frequency set of exact height and the symbol of the piece -/

/-- The frequency set of height exactly `l`: `(Q/Z)_{≤l} \ (Q/Z)_{≤l-1}` for `l ≥ 1`, and
`(Q/Z)_{≤0}` for `l = 0` (where the projection is not written as a difference). -/
noncomputable def newFreqsG (ρ : ℝ) (l : ℕ) : Finset Circ :=
  if l = 0 then iwArithFreqs ρ 0 else iwArithFreqs ρ l \ iwArithFreqs ρ (l - 1)

theorem newFreqsG_subset (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) :
    newFreqsG ρ l ⊆ iwArithFreqs ρ l := by
  rw [newFreqsG]
  by_cases hl : l = 0
  · rw [if_pos hl, hl]
  · rw [if_neg hl]
    intro x hx
    exact (Finset.mem_sdiff.mp hx).1

theorem iwSymbolSet_subG (A : Finset Circ) (Φ Ψ : Circ → ℂ) :
    iwSymbolSet A (Φ - Ψ) = iwSymbolSet A Φ - iwSymbolSet A Ψ := by
  funext ξ
  simp only [iwSymbolSet, Pi.sub_apply]
  rw [Finset.sum_sub_distrib]

/-- **The symbol of the exact-height projection.** -/
theorem PiEx_eq_iwSymbolSet (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) (k : ℤ) :
    PiEx ρ l k = iwSymbolSet (newFreqsG ρ l) (periodize (etaCut Work.KMTContract.kmtEta k)) := by
  by_cases hl : l = 0
  · rw [PiEx, if_pos hl, newFreqsG, if_pos hl]
    rfl
  · rw [PiEx, if_neg hl, newFreqsG, if_neg hl]
    have hsd := iwSymbolSet_sdiff (iwArithFreqs ρ l) (iwArithFreqs ρ (l - 1))
      (iwArithFreqs_mono hρ hρ1 (Nat.pred_le l)) (periodize (etaCut Work.KMTContract.kmtEta k))
    rw [kmtSym, kmtSym, hsd]
    abel

/-- **The symbol of the piece.** -/
theorem Gsym_eq_iwSymbolSet (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (d : ℤ) (l₂ : ℕ) (k₂ : ℤ)
    (N : ℕ) :
    Gsym ρ d l₂ k₂ N = iwSymbolSet (newFreqsG ρ l₂)
      (if k₂ = gzero
        then periodize (etaCut Work.KMTContract.kmtEta (d * (-(Work.Analysis.EndVar.logN N) + k₂)))
        else periodize (etaCut Work.KMTContract.kmtEta (d * (-(Work.Analysis.EndVar.logN N) + k₂)))
             - periodize (etaCut Work.KMTContract.kmtEta
                 (d * (-(Work.Analysis.EndVar.logN N) + (k₂ - 1))))) := by
  by_cases hk : k₂ = gzero
  · rw [Gsym, if_pos hk, if_pos hk, PiEx_eq_iwSymbolSet ρ hρ hρ1 l₂]
  · rw [Gsym, if_neg hk, if_neg hk, PiEx_eq_iwSymbolSet ρ hρ hρ1 l₂,
      PiEx_eq_iwSymbolSet ρ hρ hρ1 l₂, iwSymbolSet_subG]

/-! ## The vanishing of the outer symbol times the symbol of the piece -/

theorem newFreqsG_disjoint (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l₂ L : ℕ} (hL : L < l₂) :
    ∀ α ∈ newFreqsG ρ l₂, α ∉ iwArithFreqs ρ L := by
  intro α hα
  rw [newFreqsG] at hα
  by_cases hl₂ : l₂ = 0
  · rw [if_pos hl₂] at hα
    omega
  · rw [if_neg hl₂] at hα
    have hα' := Finset.mem_sdiff.mp hα
    intro hαL
    exact hα'.2 (iwArithFreqs_mono hρ hρ1 (by omega) hαL)

theorem Gsym_mul_eq_zero (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (d : ℤ) (hd : 0 ≤ d)
    (l₂ L : ℕ) (k₂ : ℤ) (N : ℕ)
    (hcase : L < l₂ ∨ (L : ℤ) + 2 ≤ k₂)
    (hw : max k₂ (L : ℤ) + 2 ≤ Work.Analysis.EndVar.logN N)
    (hNA : NonAliasing (d * (-(Work.Analysis.EndVar.logN N) + max k₂ (L : ℤ)) + 1)
      (iwArithFreqs ρ l₂ ∪ iwArithFreqs ρ L)) :
    iwSymbolSet (iwArithFreqs ρ L)
        (periodize (etaCut Work.KMTContract.kmtEta
          (d * (-(Work.Analysis.EndVar.logN N) + (L : ℤ)))))
      * Gsym ρ d l₂ k₂ N = 0 := by
  have hmaxR : (L : ℤ) ≤ max k₂ (L : ℤ) := le_max_right _ _
  have hmaxL : k₂ ≤ max k₂ (L : ℤ) := le_max_left _ _
  have hκL_le : d * (-(Work.Analysis.EndVar.logN N) + (L : ℤ))
      ≤ d * (-(Work.Analysis.EndVar.logN N) + max k₂ (L : ℤ)) + 1 := by
    have h2 : 0 ≤ d * (max k₂ (L : ℤ) - (L : ℤ)) := mul_nonneg hd (by linarith)
    have h3 : d * (-(Work.Analysis.EndVar.logN N) + max k₂ (L : ℤ))
        - d * (-(Work.Analysis.EndVar.logN N) + (L : ℤ))
        = d * (max k₂ (L : ℤ) - (L : ℤ)) := by ring
    linarith
  have hκk_le : d * (-(Work.Analysis.EndVar.logN N) + k₂)
      ≤ d * (-(Work.Analysis.EndVar.logN N) + max k₂ (L : ℤ)) + 1 := by
    have h2 : 0 ≤ d * (max k₂ (L : ℤ) - k₂) := mul_nonneg hd (by linarith)
    have h3 : d * (-(Work.Analysis.EndVar.logN N) + max k₂ (L : ℤ))
        - d * (-(Work.Analysis.EndVar.logN N) + k₂)
        = d * (max k₂ (L : ℤ) - k₂) := by ring
    linarith
  have hκk1_le : d * (-(Work.Analysis.EndVar.logN N) + (k₂ - 1))
      ≤ d * (-(Work.Analysis.EndVar.logN N) + max k₂ (L : ℤ)) + 1 := by
    have h2 : 0 ≤ d * (max k₂ (L : ℤ) - (k₂ - 1)) := mul_nonneg hd (by linarith)
    have h3 : d * (-(Work.Analysis.EndVar.logN N) + max k₂ (L : ℤ))
        - d * (-(Work.Analysis.EndVar.logN N) + (k₂ - 1))
        = d * (max k₂ (L : ℤ) - (k₂ - 1)) := by ring
    linarith
  rw [Gsym_eq_iwSymbolSet ρ hρ hρ1 d l₂ k₂ N]
  refine iwSymbolSet_mul_eq_zero_of (A := iwArithFreqs ρ L) (D := newFreqsG ρ l₂) ?_
  intro β hβ α hα ξ
  by_cases hΦ : periodize (etaCut Work.KMTContract.kmtEta
      (d * (-(Work.Analysis.EndVar.logN N) + (L : ℤ)))) (ξ - β) = 0
  · exact Or.inl hΦ
  refine Or.inr ?_
  have hαA : α ∈ iwArithFreqs ρ l₂ ∪ iwArithFreqs ρ L :=
    Finset.mem_union_left _ (newFreqsG_subset ρ hρ hρ1 l₂ hα)
  have hβA : β ∈ iwArithFreqs ρ l₂ ∪ iwArithFreqs ρ L := Finset.mem_union_right _ hβ
  have hsepne : ∀ j : ℤ, j ≤ d * (-(Work.Analysis.EndVar.logN N) + max k₂ (L : ℤ)) + 1 →
      α ≠ β → periodize (etaCut Work.KMTContract.kmtEta j) (ξ - α) = 0 :=
    fun j hj hne => Phi_sep hNA hβA hαA hne hκL_le hj ξ hΦ
  have hcaseB_of : α = β → (L : ℤ) + 2 ≤ k₂ := by
    intro hab
    rcases hcase with hA | hB
    · exact absurd (hab ▸ hβ) (newFreqsG_disjoint ρ hρ hρ1 hA α hα)
    · exact hB
  by_cases hk : k₂ = gzero
  · rw [if_pos hk]
    by_cases hαβ : α = β
    · have hB := hcaseB_of hαβ
      rw [hk] at hB
      simp only [gzero] at hB
      omega
    · exact hsepne _ hκk_le hαβ
  · rw [if_neg hk, Pi.sub_apply]
    by_cases hαβ : α = β
    · rw [hαβ]
      have hB := hcaseB_of hαβ
      by_cases hd0 : d = 0
      · rw [hd0]
        simp
      · have hd1 : 1 ≤ d := by omega
        obtain ⟨θ, hθ, hθeq⟩ :=
          supportedInArc_periodize_etaCutG (d * (-(Work.Analysis.EndVar.logN N) + (L : ℤ)))
            (ξ - β) hΦ
        have hθabs : |θ| ≤ (2 : ℝ) ^ (d * (-(Work.Analysis.EndVar.logN N) + (L : ℤ))) := by
          rw [realArc, Set.mem_Icc] at hθ
          exact abs_le.mpr hθ
        have hlog : max k₂ (L : ℤ) + 2 ≤ Work.Analysis.EndVar.logN N := hw
        rw [← hθeq]
        have hA1 : d * (-(Work.Analysis.EndVar.logN N) + k₂) ≤ -1 := by
          have h1 : (2 : ℤ) ≤ Work.Analysis.EndVar.logN N - k₂ := by linarith
          have h2 : 2 ≤ d * (Work.Analysis.EndVar.logN N - k₂) := by nlinarith [hd1, h1]
          have h3 : d * (-(Work.Analysis.EndVar.logN N) + k₂)
              = -(d * (Work.Analysis.EndVar.logN N - k₂)) := by ring
          linarith
        have hA2 : d * (-(Work.Analysis.EndVar.logN N) + (L : ℤ)) + 1
            ≤ d * (-(Work.Analysis.EndVar.logN N) + k₂) := by
          have h1 : (2 : ℤ) ≤ k₂ - (L : ℤ) := by linarith
          have h2 : 2 ≤ d * (k₂ - (L : ℤ)) := by nlinarith [hd1, h1]
          have h3 : d * (-(Work.Analysis.EndVar.logN N) + k₂)
              - d * (-(Work.Analysis.EndVar.logN N) + (L : ℤ))
              = d * (k₂ - (L : ℤ)) := by ring
          linarith
        have hB1 : d * (-(Work.Analysis.EndVar.logN N) + (k₂ - 1)) ≤ -1 := by
          have h1 : (3 : ℤ) ≤ Work.Analysis.EndVar.logN N - (k₂ - 1) := by linarith
          have h2 : 3 ≤ d * (Work.Analysis.EndVar.logN N - (k₂ - 1)) := by nlinarith [hd1, h1]
          have h3 : d * (-(Work.Analysis.EndVar.logN N) + (k₂ - 1))
              = -(d * (Work.Analysis.EndVar.logN N - (k₂ - 1))) := by ring
          linarith
        have hB2 : d * (-(Work.Analysis.EndVar.logN N) + (L : ℤ)) + 1
            ≤ d * (-(Work.Analysis.EndVar.logN N) + (k₂ - 1)) := by
          have h1 : (1 : ℤ) ≤ k₂ - 1 - (L : ℤ) := by linarith
          have h2 : 1 ≤ d * (k₂ - 1 - (L : ℤ)) := by nlinarith [hd1, h1]
          have h3 : d * (-(Work.Analysis.EndVar.logN N) + (k₂ - 1))
              - d * (-(Work.Analysis.EndVar.logN N) + (L : ℤ))
              = d * (k₂ - 1 - (L : ℤ)) := by ring
          linarith
        rw [Phi_eq_one_of_small (k := d * (-(Work.Analysis.EndVar.logN N) + k₂))
              (by have := zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hA1
                  norm_num at this ⊢; exact this)
              (by
                have h4 : (2 : ℝ) ^ (d * (-(Work.Analysis.EndVar.logN N) + (L : ℤ)))
                    ≤ (2 : ℝ) ^ (d * (-(Work.Analysis.EndVar.logN N) + k₂)) / 2 := by
                  have h5 : d * (-(Work.Analysis.EndVar.logN N) + (L : ℤ))
                      ≤ d * (-(Work.Analysis.EndVar.logN N) + k₂) - 1 := by linarith
                  have h6 := zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) h5
                  rwa [zpow_sub_one₀ (by norm_num : (2:ℝ) ≠ 0)] at h6
                linarith),
            Phi_eq_one_of_small (k := d * (-(Work.Analysis.EndVar.logN N) + (k₂ - 1)))
              (by have := zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hB1
                  norm_num at this ⊢; exact this)
              (by
                have h4 : (2 : ℝ) ^ (d * (-(Work.Analysis.EndVar.logN N) + (L : ℤ)))
                    ≤ (2 : ℝ) ^ (d * (-(Work.Analysis.EndVar.logN N) + (k₂ - 1))) / 2 := by
                  have h5 : d * (-(Work.Analysis.EndVar.logN N) + (L : ℤ))
                      ≤ d * (-(Work.Analysis.EndVar.logN N) + (k₂ - 1)) - 1 := by linarith
                  have h6 := zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) h5
                  rwa [zpow_sub_one₀ (by norm_num : (2:ℝ) ≠ 0)] at h6
                linarith),
            sub_self]
    · rw [hsepne _ hκk_le hαβ, hsepne _ hκk1_le hαβ, sub_zero]

/-- **The target.**  The Ionescu--Wainger projection `Pi_{<=L,<=d(-Log N + L)}` annihilates the
§5 piece `Gpiece (kmtPj rho) d 0 l₂ k₂ N`. -/
theorem projVanishingG (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : ℤ[X]) (l₂ k₂ L N : ℕ) (g : ℤ → ℂ)
    (hk₂ : 1 ≤ k₂) (hcase : L < l₂ ∨ L + 2 ≤ k₂)
    (hw : max (k₂ : ℤ) (L : ℤ) + 2 ≤ Work.Analysis.EndVar.logN N)
    (hNA : Work.Analysis.IonescuWainger.NonAliasing
      ((P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + (max k₂ L : ℤ)) + 1)
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ ∪ Work.Analysis.IonescuWainger.iwArithFreqs ρ L))
    (hg : MemLp g 2 Measure.count) :
    Work.KMTContract.kmtProj ρ L ((P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + (L : ℤ)))
      (Work.Analysis.EndVar.Gpiece (Work.KMTContract.kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) N g) = 0 := by
  have hpiece : Work.Analysis.EndVar.Gpiece (Work.KMTContract.kmtPj ρ) (P.natDegree : ℤ) 0 l₂
        (k₂ : ℤ) N g
      = ⇑(Gclm ρ (P.natDegree : ℤ) l₂ (k₂ : ℤ) N (toL2ZPG hg)) := by
    rw [show Work.Analysis.EndVar.Gpiece (Work.KMTContract.kmtPj ρ) (P.natDegree : ℤ) 0 l₂
          (k₂ : ℤ) N g
        = Work.Analysis.EndVar.piece (Work.KMTContract.kmtPj ρ) l₂
            (fun s => (P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + s)) gzero (k₂ : ℤ) g
        from rfl]
    conv_lhs => rw [show g = ⇑(toL2ZPG hg) from (toL2ZPG_coe hg).symm]
    exact piece_eq ρ l₂ (k₂ : ℤ) (P.natDegree : ℤ) N (toL2ZPG hg)
  rw [hpiece, kmtProj_eq_apply, projCLMG_eq_multiplier, Gclm_eq, multiplier_comp]
  rw [symL_smul_Gm_eq_zero ρ L ((P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + (L : ℤ)))
      (P.natDegree : ℤ) l₂ (k₂ : ℤ) N ?_]
  · rw [multiplier_zero_applyG]
    exact rfl
  · intro ξ
    have hcase' : L < l₂ ∨ (L : ℤ) + 2 ≤ (k₂ : ℤ) := by
      rcases hcase with h | h
      · exact Or.inl h
      · exact Or.inr (by exact_mod_cast h)
    have hNA' : NonAliasing
        ((P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + max (k₂ : ℤ) (L : ℤ)) + 1)
        (iwArithFreqs ρ l₂ ∪ iwArithFreqs ρ L) := by
      simpa only [Nat.cast_max] using hNA
    have h0 := Gsym_mul_eq_zero ρ hρ hρ1 (P.natDegree : ℤ) (Int.natCast_nonneg _) l₂ L
      (k₂ : ℤ) N hcase' hw hNA'
    exact congrFun h0 ξ

end

end Work.KMTPlan.A6
