import Mathlib
import Submission.Work.KMTAreas.A7.SmallDefs
import Submission.Work.KMTAreas.A7.ExcAux
import Submission.Work.KMTAreas.A7.SmallExcSupport
import Submission.Work.KMTAreas.A7.KmtProjUniform
import Submission.Work.KMTAreas.A7.KmtKernelL1Uniform

set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar

/-! ## Auxiliary lemmas for the crude bound on the exceptional small scales -/

/-- The auxiliary scale `u = ⌊2^{2ρL}⌋` of the scale split is monotone in `ρ`. -/
lemma uScale_mono_rho (L : ℕ) : Monotone (fun ρ : ℝ => uScale ρ L) := by
  intro ρ ρ' h
  have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hexp : 2 * ρ * (L : ℝ) ≤ 2 * ρ' * (L : ℝ) := by nlinarith
  have h1 : ((1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))
      ≤ ((1 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * ρ' * (L : ℝ)) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  simp only [uScale, scaleCount, Int.floor_toNat]
  exact Nat.floor_mono h1

/-- **The support of the exceptional small scales is bounded uniformly in `ρ`.**  For
`ρ ≤ 1/(8C₀)` every admissible scale outside the main regime has all four parameters and the
scale itself bounded by a constant depending only on `C₀` (and not on `ρ`).  This is the form in
which `SmallExcSupport` is used by the crude estimate below: the constant `K` of `SmallExcBound`
must not depend on `ρ`.

The proof takes the sup over `ρ` at `ρ = 1/(8C₀)` (the largest admissible value) and uses that the
constraint `¬ mainRegime ρ k₁ k₂ N` becomes easier as `ρ` grows, since `uScale · L` is monotone. -/
theorem smallExcSupportUniform (C₀ : ℕ) (hC₀ : 1 ≤ C₀) :
    ∃ B : ℕ, ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 / (8 * (C₀ : ℝ)) →
      ∀ (l₁ l₂ k₁ k₂ N : ℕ),
        inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) N →
        ¬ mainRegime ρ k₁ k₂ N →
        max (max l₁ l₂) (max k₁ k₂) ≤ B ∧ N ≤ 2 ^ B := by
  have hC₀R : (0 : ℝ) < (C₀ : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hC₀)
  obtain ⟨B, hB⟩ := SmallExcSupport C₀ hC₀ (1 / (8 * (C₀ : ℝ)))
    (by apply div_pos one_pos; nlinarith) le_rfl
  refine ⟨B, ?_⟩
  intro ρ hρ hρle l₁ l₂ k₁ k₂ N hI hnot
  refine hB l₁ l₂ k₁ k₂ N hI (fun hmain => hnot ?_)
  have hu : uScale ρ (max k₁ k₂) ≤ uScale (1 / (8 * (C₀ : ℝ))) (max k₁ k₂) :=
    uScale_mono_rho _ hρle
  refine ⟨by have := hmain.1; omega, by have := hmain.2; omega⟩

/-- The exceptional small-scale family vanishes on a vanishing argument. -/
theorem smallExcPart_zero_left (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    smallExcPart ρ P C₀ a (0 : ℤ → ℂ) g l₁ l₂ k₁ k₂ = 0 := by
  funext n x
  rw [smallExcPart_apply]
  simp only [varpPiece, Fpiece, Gpiece, piece, piExact, kmtPj_proj, kmtProj_zero]
  by_cases h : (Nat.floor (a n)) = 0 <;> simp [h, AhalfR, Ahalf, Ablock]

/-- The exceptional small-scale family vanishes on a vanishing argument. -/
theorem smallExcPart_zero_right (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    smallExcPart ρ P C₀ a f (0 : ℤ → ℂ) l₁ l₂ k₁ k₂ = 0 := by
  funext n x
  rw [smallExcPart_apply]
  simp only [varpPiece, Fpiece, Gpiece, piece, piExact, kmtPj_proj, kmtProj_zero]
  by_cases h : (Nat.floor (a n)) = 0 <;> simp [h, AhalfR, Ahalf, Ablock]

/-- The variational norm of the zero sequence vanishes (for `r ≥ 1`). -/
lemma variationalNorm_zero' {r : ℝ≥0} (hr : 1 ≤ r) :
    variationalNorm r (0 : ℕ → ℂ) = 0 := by
  have h := variationalNorm_smul (r := r) hr (0 : ℂ) (0 : ℕ → ℂ)
  simpa using h

/-- **The crude bound for the exceptional small scales.** The family `smallExcPart` consists of the
§5 columns at the scales `N = ⌊a n⌋` which are admissible (`inIndexSet`), small
(`N ≤ splitCut ρ L`) and *outside* the §6 main regime.  By the proved structural lemma
`Work.KMTAreas.A7.SmallExcSupport`, for `ρ ≤ 1/(8 C₀)` all four parameters `l₁,l₂,k₁,k₂` and the
scale `N` are bounded by a constant `B(C₀)` alone, so that only finitely many lacunary scales
contribute (at most the first `nBound Λ B` ones).  The crude single-scale bound is then
`Submission.eLpNorm_variationalNorm_le_sum` (`V^r(u) ≤ ∑_n 4‖u n‖_{ℓ^p}`) followed by the Hölder
bound `Submission.eLpNorm_AhalfR_le` (`‖Ã_N(u,v)‖_{ℓ^p} ≤ ‖u‖_{p₁}‖v‖_{p₂}`) applied to the two
continuous pieces, whose `ℓ^q` norms are controlled by the uniform projection bound
`Work.KMTAreas.A7.KmtProjUniform` (or `Work.KMTAreas.A7.KmtProjCrude`).

The proof is the small-scale mirror image of `Work.KMTAreas.A7.ExceptionalBound_of_ingredients`
(`A7/ExcAux2.lean`) together with the helper lemmas of `A7/ExcAux.lean` (`eLpNorm_piece_le`,
`eLpNorm_varpPiece_le`, `logN_le_of_le_pow`, `floor_a_gt`, `eq_zero_of_eLpNorm_eq_zero`, the
zero-function cases), with the bound `excBnd C₀` replaced by the bound supplied by
`SmallExcSupport` (which gives `N ≤ 2 ^ B` and all four parameters `≤ B`), and with the hypothesis
`splitCut ρ L < N` of the large-scale exceptional regime dropped.  NB the file
`A7/ExcAux2.lean` currently does NOT build (heartbeat timeout), so `ExceptionalBound_of_ingredients`
cannot be imported; the relevant reusable ingredients are in `A7/ExcAux.lean`, which builds. -/
theorem SmallExcBound (P : ℤ[X]) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤)
    (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r → ∃ K : NNReal → NNReal,
      ∀ (ρ : ℝ) (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        0 < ρ → ρ ≤ 1 / (8 * (C₀ : ℝ)) → 1 < Λ →
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
        ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
            MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
  intro C₀ r hC₀ hr
  have hq1R : 1 < p₁.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt htp₁)).mpr hp₁
  have hq2R : 1 < p₂.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt htp₂)).mpr hp₂
  have hp₁eq : p₁ = ENNReal.ofReal p₁.toReal := (ENNReal.ofReal_toReal (ne_of_lt htp₁)).symm
  have hp₂eq : p₂ = ENNReal.ofReal p₂.toReal := (ENNReal.ofReal_toReal (ne_of_lt htp₂)).symm
  -- the `ρ`-uniform `ℓ^q` bounds for the Ionescu--Wainger projections
  obtain ⟨Rk, hRkpos, hRk⟩ := KmtKernelL1Uniform
  obtain ⟨C₁, _hC₁pos, hC₁⟩ := KmtProjUniform (q := p₁.toReal) hq1R (R := Rk) hRkpos hRk
  obtain ⟨C₂, _hC₂pos, hC₂⟩ := KmtProjUniform (q := p₂.toReal) hq2R (R := Rk) hRkpos hRk
  -- the parameter bound of the exceptional scales
  obtain ⟨B, hB⟩ := smallExcSupportUniform C₀ hC₀
  set B₀ : ℕ := max B 1 with hB₀def
  have hB₀1 : 1 ≤ B₀ := by rw [hB₀def]; exact le_max_right _ _
  have hB' : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 / (8 * (C₀ : ℝ)) → ∀ (l₁ l₂ k₁ k₂ N : ℕ),
      inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) N →
      ¬ mainRegime ρ k₁ k₂ N →
      max (max l₁ l₂) (max k₁ k₂) ≤ B₀ ∧ N ≤ 2 ^ B₀ := by
    intro ρ hρ hρle l₁ l₂ k₁ k₂ N hI hnot
    obtain ⟨h1, h2⟩ := hB ρ hρ hρle l₁ l₂ k₁ k₂ N hI hnot
    rw [hB₀def]
    exact ⟨le_trans h1 (le_max_left _ _),
      le_trans h2 (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))⟩
  set KB : ℕ := (P.natDegree + 1) * (B₀ + 2) + 2 with hKBdef
  set CC₁ : NNReal := envConst C₁ B₀ KB with hCC₁def
  set CC₂ : NNReal := envConst C₂ B₀ KB with hCC₂def
  set AA : ENNReal := ENNReal.ofReal (16 * (CC₁ : ℝ) * (CC₂ : ℝ)) with hAAdef
  let Kc : NNReal → NNReal := fun Λ =>
    ⟨max ((nBound Λ B₀ : ℝ) * (4 * (16 * (CC₁ : ℝ) * (CC₂ : ℝ)))) 1,
      le_trans zero_le_one (le_max_right _ _)⟩
  have hKBval : (P.natDegree + 1) * (B₀ + 2) + 2 ≤ KB := le_of_eq hKBdef.symm
  have hB₀KB : B₀ + 1 ≤ KB := by
    rw [hKBdef]
    nlinarith [Nat.zero_le P.natDegree]
  have hdom₁ : ∀ l' ∈ Finset.Icc 0 B₀, ∀ m' ∈ Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ),
      C₁ l' m' ≤ CC₁ := by
    intro l' hl' m' hm'
    rw [hCC₁def]
    exact le_envConst hl' hm'
  have hdom₂ : ∀ l' ∈ Finset.Icc 0 B₀, ∀ m' ∈ Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ),
      C₂ l' m' ≤ CC₂ := by
    intro l' hl' m' hm'
    rw [hCC₂def]
    exact le_envConst hl' hm'
  refine ⟨Kc, ?_⟩
  intro ρ a Λ l₁ l₂ k₁ k₂ f g hρ0 hρle hΛ ha ha1
  set Kcv : NNReal := Kc Λ with hKcvdef
  have hKdef : (Kc Λ : ENNReal) = (Kcv : ENNReal) := by rw [hKcvdef]
  have hKcvR : (Kcv : ℝ)
      = max ((nBound Λ B₀ : ℝ) * (4 * (16 * (CC₁ : ℝ) * (CC₂ : ℝ)))) 1 := by
    rw [hKcvdef] <;> rfl
  have hKcvval : (Kcv : ENNReal)
      = ENNReal.ofReal (max ((nBound Λ B₀ : ℝ) * (4 * (16 * (CC₁ : ℝ) * (CC₂ : ℝ)))) 1) := by
    rw [ENNReal.coe_nnreal_eq, hKcvR]
  have hKcvne : (Kcv : ENNReal) ≠ 0 := by
    intro h
    have h1 : Kcv = 0 := ENNReal.coe_eq_zero.mp h
    have h2 : (Kcv : ℝ) = 0 := by rw [h1] <;> rfl
    have h3 : (0 : ℝ) < (Kcv : ℝ) := by
      rw [hKcvR]
      exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    exact absurd h2 (ne_of_gt h3)
  have hKcne : (Kc Λ : ENNReal) ≠ 0 := fun h => hKcvne (hKdef.trans h)
  -- the single-scale arithmetic
  have hL1 : (nBound Λ B₀ : ENNReal) * (4 * AA)
      = ENNReal.ofReal ((nBound Λ B₀ : ℝ) * (4 * (16 * (CC₁ : ℝ) * (CC₂ : ℝ)))) := by
    rw [hAAdef, ← ENNReal.ofReal_natCast (nBound Λ B₀), ← ENNReal.ofReal_ofNat 4,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (nBound Λ B₀ : ℝ)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ (4 : ℝ))]
  have hJAA' : (nBound Λ B₀ : ENNReal) * (4 * AA) ≤ (Kcv : ENNReal) := by
    rw [hL1, hKcvval]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hJAA : (nBound Λ B₀ : ENNReal) * (4 * AA) ≤ (Kc Λ : ENNReal) :=
    hJAA'.trans (le_of_eq hKdef.symm)
  -- the exponent bookkeeping
  have hsum' : (ENNReal.ofReal p₁.toReal)⁻¹ + (ENNReal.ofReal p₂.toReal)⁻¹ ≤ 1 := by
    rw [← hp₁eq, ← hp₂eq]
    exact hsum
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  have hq : 1 ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  have hρ1 : ρ ≤ 1 := by
    have hC₀R : (0 : ℝ) < (C₀ : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hC₀)
    calc ρ ≤ 1 / (8 * (C₀ : ℝ)) := hρle
      _ ≤ 1 := by
          rw [div_le_one (by positivity : (0 : ℝ) < 8 * (C₀ : ℝ))]
          have hC₀1 : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
          linarith
  by_cases hfin : eLpNorm f p₁ Measure.count < ⊤ ∧ eLpNorm g p₂ Measure.count < ⊤
  · obtain ⟨hf_fin, hg_fin⟩ := hfin
    have hf_fin' : eLpNorm f (ENNReal.ofReal p₁.toReal) Measure.count < ⊤ := by
      rw [← hp₁eq]; exact hf_fin
    have hg_fin' : eLpNorm g (ENNReal.ofReal p₂.toReal) Measure.count < ⊤ := by
      rw [← hp₂eq]; exact hg_fin
    have hproj₁ : ∀ (l' : ℕ) (k' : ℤ) (u : ℤ → ℂ),
        eLpNorm (kmtProj ρ l' k' u) (ENNReal.ofReal p₁.toReal) Measure.count
          ≤ ENNReal.ofReal (C₁ l' k' : ℝ) *
            eLpNorm u (ENNReal.ofReal p₁.toReal) Measure.count :=
      fun l' k' u => hC₁ ρ hρ0 hρ1 l' k' u
    have hproj₂ : ∀ (l' : ℕ) (k' : ℤ) (u : ℤ → ℂ),
        eLpNorm (kmtProj ρ l' k' u) (ENNReal.ofReal p₂.toReal) Measure.count
          ≤ ENNReal.ofReal (C₂ l' k' : ℝ) *
            eLpNorm u (ENNReal.ofReal p₂.toReal) Measure.count :=
      fun l' k' u => hC₂ ρ hρ0 hρ1 l' k' u
    -- the support of the exceptional family
    have hsupp : ∀ n, n ∉ Finset.range (nBound Λ B₀) →
        (fun x : ℤ => smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 := by
      intro n hn
      have hn' : nBound Λ B₀ ≤ n := by simpa [Finset.mem_range] using hn
      have hgt : 2 ^ B₀ < Nat.floor (a n) := floor_a_gt hΛ ha ha1 B₀ hn'
      have hz : smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n = 0 :=
        smallExcPart_eq_zero ρ P C₀ a f g l₁ l₂ k₁ k₂ n (fun hExc => by
          obtain ⟨_hbnd, hN⟩ := hB' ρ hρ0 hρle l₁ l₂ k₁ k₂ (Nat.floor (a n)) hExc.1 hExc.2.2
          exact absurd hN (not_le.mpr hgt))
      funext x
      exact congrFun hz x
    have hmeas : ∀ n ∈ Finset.range (nBound Λ B₀),
        AEStronglyMeasurable
          (fun x : ℤ => smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) Measure.count :=
      fun n _ => (measurable_of_countable _).aestronglyMeasurable
    -- the single-term bound
    have hterm : ∀ n ∈ Finset.range (nBound Λ B₀),
        eLpNorm (fun x : ℤ => smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            ((p₁⁻¹ + p₂⁻¹)⁻¹) Measure.count
          ≤ AA * (eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count) := by
      intro n hn
      by_cases hExc : smallExcPred ρ C₀ a l₁ l₂ k₁ k₂ n
      · have hExc' : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ)
              (Nat.floor (a n)) ∧ Nat.floor (a n) ≤ splitCut ρ (smallL l₁ l₂ k₁ k₂) ∧
              ¬ mainRegime ρ k₁ k₂ (Nat.floor (a n)) := hExc
        obtain ⟨hbnd, hNm⟩ := hB' ρ hρ0 hρle l₁ l₂ k₁ k₂ (Nat.floor (a n)) hExc.1 hExc.2.2
        have hl₁B : l₁ ≤ B₀ := le_trans (le_trans (le_max_left l₁ l₂) (le_max_left _ _)) hbnd
        have hl₂B : l₂ ≤ B₀ := le_trans (le_trans (le_max_right l₁ l₂) (le_max_left _ _)) hbnd
        have hk₁B : k₁ ≤ B₀ := le_trans (le_trans (le_max_left k₁ k₂) (le_max_right _ _)) hbnd
        have hk₂B : k₂ ≤ B₀ := le_trans (le_trans (le_max_right k₁ k₂) (le_max_right _ _)) hbnd
        have hlog : logN (Nat.floor (a n)) ≤ (B₀ : ℤ) := logN_le_of_le_pow hNm hB₀1
        have hpre : (fun x : ℤ => smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            = varpPiece (kmtPj ρ) P P.natDegree (a n) f g l₁ l₂ k₁ k₂ := by
          funext x
          rw [smallExcPart_apply, if_pos hExc']
        have hFb : eLpNorm (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f)
            (ENNReal.ofReal p₁.toReal) Measure.count
            ≤ ENNReal.ofReal (4 * (CC₁ : ℝ)) *
              eLpNorm f (ENNReal.ofReal p₁.toReal) Measure.count := by
          have hmemF := mem_freq_F (N := Nat.floor (a n)) (k₁ := k₁) (B₀ := B₀) (KB := KB)
            hlog hk₁B hB₀KB
          exact eLpNorm_piece_le (ρ := ρ) (q := p₁.toReal) (C := C₁) (CC := CC₁) (B₀ := B₀)
            (KB := KB) (l := l₁) (κ := fun s => -(logN (Nat.floor (a n))) + s)
            (a := -(0 : ℤ)) (s := (k₁ : ℤ)) hq1R hl₁B hmemF.1 hmemF.2 hdom₁ hproj₁ f
        have hGb : eLpNorm (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ)
            (Nat.floor (a n)) g) (ENNReal.ofReal p₂.toReal) Measure.count
            ≤ ENNReal.ofReal (4 * (CC₂ : ℝ)) *
              eLpNorm g (ENNReal.ofReal p₂.toReal) Measure.count := by
          have hmemG := mem_freq_G (N := Nat.floor (a n)) (k₂ := k₂) (B₀ := B₀) (KB := KB)
            (d := P.natDegree) hlog hk₂B hKBval
          exact eLpNorm_piece_le (ρ := ρ) (q := p₂.toReal) (C := C₂) (CC := CC₂) (B₀ := B₀)
            (KB := KB) (l := l₂) (κ := fun s => (P.natDegree : ℤ) * (-(logN (Nat.floor (a n))) + s))
            (a := -(0 : ℤ)) (s := (k₂ : ℤ)) hq2R hl₂B hmemG.1 hmemG.2 hdom₂ hproj₂ g
        have hFmem : MemLp (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f)
            (ENNReal.ofReal p₁.toReal) Measure.count :=
          (MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt hFb (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf_fin')))
        have hGmem : MemLp (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ)
            (Nat.floor (a n)) g) (ENNReal.ofReal p₂.toReal) Measure.count :=
          (MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt hGb (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg_fin')))
        have hmain := eLpNorm_varpPiece_le (ρ := ρ) P a f g l₁ l₂ k₁ k₂ n hq1R hq2R
          (C₁ := C₁) (C₂ := C₂) (CC₁ := CC₁) (CC₂ := CC₂) (B₀ := B₀) (KB := KB)
          hdom₁ hdom₂ hsum' hproj₁ hproj₂ hl₁B hl₂B hk₁B hk₂B hKBval hlog hFmem hGmem
        have hmain' : eLpNorm (varpPiece (kmtPj ρ) P P.natDegree (a n) f g l₁ l₂ k₁ k₂)
            ((p₁⁻¹ + p₂⁻¹)⁻¹) Measure.count
            ≤ AA * (eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count) := by
          have h := hmain
          rw [← hp₁eq, ← hp₂eq] at h
          exact h
        rw [hpre]
        exact hmain'
      · have hExc' : ¬ (inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ)
              (Nat.floor (a n)) ∧ Nat.floor (a n) ≤ splitCut ρ (smallL l₁ l₂ k₁ k₂) ∧
              ¬ mainRegime ρ k₁ k₂ (Nat.floor (a n))) := hExc
        have hz : (fun x : ℤ => smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 := by
          funext x
          rw [smallExcPart_apply, if_neg hExc']
          simp
        rw [hz]
        simp
    refine (eLpNorm_variationalNorm_le_sum (r := r) (p := (p₁⁻¹ + p₂⁻¹)⁻¹)
      (μ := Measure.count) (u := fun n x => smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      (s := Finset.range (nBound Λ B₀)) hr1 hq hsupp hmeas).trans ?_
    refine (Finset.sum_le_sum (fun n hn => mul_le_mul' le_rfl (hterm n hn))).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc (nBound Λ B₀ : ENNReal)
          * (4 * (AA * (eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count)))
        = ((nBound Λ B₀ : ENNReal) * (4 * AA))
            * (eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count) := by ac_rfl
      _ ≤ (Kcv : ENNReal) * (eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count) :=
          mul_le_mul' hJAA' le_rfl
      _ = (Kc Λ : ENNReal) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count := by
          rw [hKdef, mul_assoc]
  · have hcase : eLpNorm f p₁ Measure.count = ⊤ ∨ eLpNorm g p₂ Measure.count = ⊤ := by
      by_contra h
      push_neg at h
      exact hfin ⟨lt_top_iff_ne_top.mpr h.1, lt_top_iff_ne_top.mpr h.2⟩
    rcases hcase with hA' | hB'
    · by_cases hg0 : eLpNorm g p₂ Measure.count = 0
      · have hp₂0 : p₂ ≠ 0 := by
          intro h; rw [h] at hp₂; exact absurd hp₂ (by norm_num)
        have hgzero : g = 0 := eq_zero_of_eLpNorm_eq_zero hp₂0 hg0
        have hzero : (fun x : ℤ => variationalNorm r (fun n : ℕ =>
            smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) = 0 := by
          funext x
          have hf : (fun n : ℕ => smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 := by
            funext n
            rw [hgzero]
            exact congrFun (congrFun (smallExcPart_zero_right ρ P C₀ a f l₁ l₂ k₁ k₂) n) x
          rw [hf, variationalNorm_zero' hr1]
          simp
        rw [hzero]
        simp
      · have hgne : eLpNorm g p₂ Measure.count ≠ 0 := hg0
        have htop : (Kc Λ : ENNReal) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count
            = ⊤ := by
          rw [hA', ENNReal.mul_top hKcne, ENNReal.top_mul hgne]
        rw [htop]
        exact le_top
    · by_cases hf0 : eLpNorm f p₁ Measure.count = 0
      · have hp₁0 : p₁ ≠ 0 := by
          intro h; rw [h] at hp₁; exact absurd hp₁ (by norm_num)
        have hfzero : f = 0 := eq_zero_of_eLpNorm_eq_zero hp₁0 hf0
        have hzero : (fun x : ℤ => variationalNorm r (fun n : ℕ =>
            smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) = 0 := by
          funext x
          have hf : (fun n : ℕ => smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 := by
            funext n
            rw [hfzero]
            exact congrFun (congrFun (smallExcPart_zero_left ρ P C₀ a g l₁ l₂ k₁ k₂) n) x
          rw [hf, variationalNorm_zero' hr1]
          simp
        rw [hzero]
        simp
      · have hfne : eLpNorm f p₁ Measure.count ≠ 0 := hf0
        have htop : (Kc Λ : ENNReal) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count
            = ⊤ := by
          rw [mul_assoc, hB', ENNReal.mul_top hfne, ENNReal.mul_top hKcne]
        rw [htop]
        exact le_top

end Work.KMTAreas.A7
