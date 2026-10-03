import Mathlib
import Submission.Work.KMTAreas.A7.ExcAux

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTContract
open Work.Analysis.EndVar

/-! ## The `ℓ¹`-sum comparison used at the end of the assembly -/

/-- The comparison turning the sum of the per-term bounds into the constant `K Λ`. -/
theorem term_sum_le {K : NNReal} (nB : ℕ) (M : ℝ) (X : ENNReal)
    (hK : (nB : ℝ) * (4 * M) ≤ (K : ℝ)) :
    (nB : ENNReal) * (4 * (ENNReal.ofReal M * X)) ≤ (K : ENNReal) * X := by
  have h4 : ENNReal.ofReal (4 * M) = 4 * ENNReal.ofReal M := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4), ENNReal.ofReal_ofNat]
  calc (nB : ENNReal) * (4 * (ENNReal.ofReal M * X))
      = ENNReal.ofReal (nB : ℝ) * (ENNReal.ofReal (4 * M) * X) := by
        rw [← ENNReal.ofReal_natCast (nB), h4]; ring
    _ = (ENNReal.ofReal (nB : ℝ) * ENNReal.ofReal (4 * M)) * X := by ring
    _ = ENNReal.ofReal ((nB : ℝ) * (4 * M)) * X := by
        rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (nB : ℝ))]
    _ ≤ ENNReal.ofReal ((K : ℝ)) * X := mul_le_mul' (ENNReal.ofReal_le_ofReal hK) le_rfl
    _ = (K : ENNReal) * X := by rw [ENNReal.ofReal_coe_nnreal]

theorem variationalNorm_zero (r : NNReal) (hr : 1 ≤ r) :
    variationalNorm r (0 : ℕ → ℂ) = 0 := by
  have h := variationalNorm_smul (r := r) hr (0 : ℂ) (0 : ℕ → ℂ)
  simpa using h

/-! ## The abstract parameter bound of the exceptional regime -/

/-- `SuppBound Bnd` is the parameter bound of the exceptional regime with an abstract bound
function `Bnd` (in the application `Bnd = excBnd`): if the three defining conditions of the
exceptional regime hold at the scale `N` then `N` and all four height parameters are bounded by
`Bnd C₀`. -/
def SuppBound (Bnd : ℕ → ℕ) : Prop :=
  (∀ C₀, 1 ≤ Bnd C₀) ∧
    ∀ (C₀ : ℕ) (ρ : ℝ) (l₁ l₂ k₁ k₂ N : ℕ), 1 ≤ C₀ → 0 < ρ → ρ ≤ 1 →
      l₁ ≤ heightScale C₀ N → l₂ ≤ heightScale C₀ N → k₁ ≤ heightScale C₀ N →
      k₂ ≤ heightScale C₀ N → ¬ mainRegime ρ k₁ k₂ N →
      splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < N →
      N ≤ 2 ^ (Bnd C₀) ∧ l₁ ≤ Bnd C₀ ∧ l₂ ≤ Bnd C₀ ∧ k₁ ≤ Bnd C₀ ∧ k₂ ≤ Bnd C₀

/-- **The final assembly.**  Given

* the `ρ`-uniform `ℓ^{q}` bounds for the Ionescu--Wainger projections (the conclusion of
  `Work.KMTAreas.A7.KmtProjUniform`, fed by `Work.KMTAreas.A7.KmtKernelL1Uniform`), and
* the parameter bound `Work.KMTAreas.A7.ExceptionalSupport` for the exceptional regime
  (`hSupp : SuppBound Bnd`),

the exceptional part obeys the variational estimate with a constant depending only on the
lacunarity parameter. -/
theorem ExceptionalBound_of_ingredients
    (hProj : ∀ (qR : ℝ), 1 < qR → ∃ C : ℕ → ℤ → NNReal, (∀ l k, 0 < C l k) ∧
      ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (l : ℕ) (k : ℤ) (u : ℤ → ℂ),
        eLpNorm (kmtProj ρ l k u) (ENNReal.ofReal qR) Measure.count
          ≤ ENNReal.ofReal (C l k : ℝ) * eLpNorm u (ENNReal.ofReal qR) Measure.count)
    {Bnd : ℕ → ℕ} (hSupp : SuppBound Bnd) :
    ∀ (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree) (hp₁ : 1 < p₁)
      (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1),
    ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r → ∃ K : NNReal → NNReal,
      ∀ (ρ : ℝ) (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        0 < ρ → ρ ≤ 1 → 1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) →
        eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
            exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count
        ≤ (K Λ : ENNReal) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count := by
  intro P p₁ p₂ hdeg hp₁ htp₁ hp₂ htp₂ hsum C₀ r hC₀ hr
  have hq1R : 1 < p₁.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt htp₁)).mpr hp₁
  have hq2R : 1 < p₂.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt htp₂)).mpr hp₂
  have hp₁eq : p₁ = ENNReal.ofReal p₁.toReal := (ENNReal.ofReal_toReal (ne_of_lt htp₁)).symm
  have hp₂eq : p₂ = ENNReal.ofReal p₂.toReal := (ENNReal.ofReal_toReal (ne_of_lt htp₂)).symm
  obtain ⟨C₁, hC₁pos, hC₁⟩ := hProj p₁.toReal hq1R
  obtain ⟨C₂, hC₂pos, hC₂⟩ := hProj p₂.toReal hq2R
  have hKBdef : (P.natDegree + 1) * (Bnd C₀ + 2) + 2 = (P.natDegree + 1) * (Bnd C₀ + 2) + 2 :=
    rfl
  have hdom₁ : ∀ l' ∈ Finset.Icc 0 (Bnd C₀),
      ∀ m' ∈ Finset.Icc (-(((P.natDegree + 1) * (Bnd C₀ + 2) + 2 : ℕ) : ℤ) - 1)
        (((P.natDegree + 1) * (Bnd C₀ + 2) + 2 : ℕ) : ℤ),
      C₁ l' m' ≤ envConst C₁ (Bnd C₀) ((P.natDegree + 1) * (Bnd C₀ + 2) + 2) := by
    intro l' hl' m' hm'
    exact le_envConst hl' hm'
  have hdom₂ : ∀ l' ∈ Finset.Icc 0 (Bnd C₀),
      ∀ m' ∈ Finset.Icc (-(((P.natDegree + 1) * (Bnd C₀ + 2) + 2 : ℕ) : ℤ) - 1)
        (((P.natDegree + 1) * (Bnd C₀ + 2) + 2 : ℕ) : ℤ),
      C₂ l' m' ≤ envConst C₂ (Bnd C₀) ((P.natDegree + 1) * (Bnd C₀ + 2) + 2) := by
    intro l' hl' m' hm'
    exact le_envConst hl' hm'
  set Kc : NNReal → NNReal := fun Λ =>
    ⟨max ((nBound Λ (Bnd C₀) : ℝ)
        * (4 * (16 * (envConst C₁ (Bnd C₀) ((P.natDegree + 1) * (Bnd C₀ + 2) + 2) : ℝ)
          * (envConst C₂ (Bnd C₀) ((P.natDegree + 1) * (Bnd C₀ + 2) + 2) : ℝ)))) 1,
      le_trans zero_le_one (le_max_right _ 1)⟩ with hKcdef
  refine ⟨Kc, ?_⟩
  intro ρ a Λ l₁ l₂ k₁ k₂ f g hρ0 hρ1 hΛ ha ha1
  have hKc1 : (1 : NNReal) ≤ Kc Λ := by
    rw [hKcdef]
    show (1 : ℝ) ≤ max ((nBound Λ (Bnd C₀) : ℝ)
        * (4 * (16 * (envConst C₁ (Bnd C₀) ((P.natDegree + 1) * (Bnd C₀ + 2) + 2) : ℝ)
          * (envConst C₂ (Bnd C₀) ((P.natDegree + 1) * (Bnd C₀ + 2) + 2) : ℝ)))) 1
    exact le_max_right _ 1
  have hKcne : (Kc Λ : ENNReal) ≠ 0 := by
    rw [Ne, ENNReal.coe_eq_zero]
    intro h
    have h1 := hKc1
    rw [h] at h1
    exact absurd h1 (by norm_num)
  have hsum' : (ENNReal.ofReal p₁.toReal)⁻¹ + (ENNReal.ofReal p₂.toReal)⁻¹ ≤ 1 := by
    rw [← hp₁eq, ← hp₂eq]; exact hsum
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  have hq : 1 ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  have hproj₁ : ∀ (l' : ℕ) (k' : ℤ) (u : ℤ → ℂ),
      eLpNorm (kmtProj ρ l' k' u) (ENNReal.ofReal p₁.toReal) Measure.count
        ≤ ENNReal.ofReal (C₁ l' k' : ℝ) * eLpNorm u (ENNReal.ofReal p₁.toReal) Measure.count :=
    hC₁ ρ hρ0 hρ1
  have hproj₂ : ∀ (l' : ℕ) (k' : ℤ) (u : ℤ → ℂ),
      eLpNorm (kmtProj ρ l' k' u) (ENNReal.ofReal p₂.toReal) Measure.count
        ≤ ENNReal.ofReal (C₂ l' k' : ℝ) * eLpNorm u (ENNReal.ofReal p₂.toReal) Measure.count :=
    hC₂ ρ hρ0 hρ1
  by_cases hfin : eLpNorm f p₁ Measure.count < ⊤ ∧ eLpNorm g p₂ Measure.count < ⊤
  · obtain ⟨hf_fin, hg_fin⟩ := hfin
    have hsupp : ∀ n, n ∉ Finset.range (nBound Λ (Bnd C₀)) →
        (fun x => exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 := by
      intro n hn
      have hn' : nBound Λ (Bnd C₀) ≤ n := by simpa [Finset.mem_range] using hn
      have hgt : 2 ^ (Bnd C₀) < Nat.floor (a n) := floor_a_gt hΛ ha ha1 (Bnd C₀) hn'
      refine exceptionalPart_eq_zero ρ P C₀ a f g l₁ l₂ k₁ k₂ n (fun hExc => ?_)
      obtain ⟨hl₁, hl₂, hk₁, hk₂⟩ := inIndexSet_iff_le.mp hExc.1
      have hbound := hSupp.2 C₀ ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) hC₀ hρ0 hρ1 hl₁ hl₂ hk₁ hk₂
        hExc.2.1 hExc.2.2
      exact absurd hbound.1 (not_le.mpr hgt)
    have hmeas : ∀ n ∈ Finset.range (nBound Λ (Bnd C₀)),
        AEStronglyMeasurable (fun x => exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          (Measure.count : Measure ℤ) :=
      fun n _ => (measurable_of_countable _).aestronglyMeasurable
    have hterm : ∀ n ∈ Finset.range (nBound Λ (Bnd C₀)),
        eLpNorm (fun x => exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            ((p₁⁻¹ + p₂⁻¹)⁻¹) Measure.count
          ≤ ENNReal.ofReal (16 * (envConst C₁ (Bnd C₀) ((P.natDegree + 1) * (Bnd C₀ + 2) + 2) : ℝ)
                * (envConst C₂ (Bnd C₀) ((P.natDegree + 1) * (Bnd C₀ + 2) + 2) : ℝ)) *
              (eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count) := by
      intro n _
      by_cases hExc : ExcPred ρ C₀ l₁ l₂ k₁ k₂ (Nat.floor (a n))
      · obtain ⟨hl₁, hl₂, hk₁, hk₂⟩ := inIndexSet_iff_le.mp hExc.1
        have hbound := hSupp.2 C₀ ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) hC₀ hρ0 hρ1 hl₁ hl₂ hk₁ hk₂
          hExc.2.1 hExc.2.2
        have hKBval : (P.natDegree + 1) * (Bnd C₀ + 2) + 2
            ≤ (P.natDegree + 1) * (Bnd C₀ + 2) + 2 := le_rfl
        have hB₀KB : Bnd C₀ + 1 ≤ (P.natDegree + 1) * (Bnd C₀ + 2) + 2 := by
          nlinarith [Nat.zero_le P.natDegree]
        have hlog : logN (Nat.floor (a n)) ≤ ((Bnd C₀ : ℕ) : ℤ) :=
          logN_le_of_le_pow hbound.1 (hSupp.1 C₀)
        have hFb : eLpNorm (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f)
            (ENNReal.ofReal p₁.toReal) Measure.count
            ≤ ENNReal.ofReal (4 * (envConst C₁ (Bnd C₀)
                ((P.natDegree + 1) * (Bnd C₀ + 2) + 2) : ℝ)) *
              eLpNorm f (ENNReal.ofReal p₁.toReal) Measure.count := by
          have hmemF := mem_freq_F hlog hbound.2.2.2.1 hB₀KB
          exact eLpNorm_piece_le (q := p₁.toReal) (C := C₁)
            (CC := envConst C₁ (Bnd C₀) ((P.natDegree + 1) * (Bnd C₀ + 2) + 2))
            (B₀ := Bnd C₀) (KB := (P.natDegree + 1) * (Bnd C₀ + 2) + 2) (l := l₁)
            (κ := fun s => -(logN (Nat.floor (a n))) + s) (a := 0) (s := (k₁ : ℤ))
            hq1R hbound.2.1 hmemF.1 hmemF.2 hdom₁ hproj₁ f
        have hGb : eLpNorm (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ)
            (Nat.floor (a n)) g) (ENNReal.ofReal p₂.toReal) Measure.count
            ≤ ENNReal.ofReal (4 * (envConst C₂ (Bnd C₀)
                ((P.natDegree + 1) * (Bnd C₀ + 2) + 2) : ℝ)) *
              eLpNorm g (ENNReal.ofReal p₂.toReal) Measure.count := by
          have hmemG := mem_freq_G (d := P.natDegree) hlog hbound.2.2.2.2 hKBval
          exact eLpNorm_piece_le (q := p₂.toReal) (C := C₂)
            (CC := envConst C₂ (Bnd C₀) ((P.natDegree + 1) * (Bnd C₀ + 2) + 2))
            (B₀ := Bnd C₀) (KB := (P.natDegree + 1) * (Bnd C₀ + 2) + 2) (l := l₂)
            (κ := fun s => (P.natDegree : ℤ) * (-(logN (Nat.floor (a n))) + s))
            (a := 0) (s := (k₂ : ℤ)) hq2R hbound.2.2.1 hmemG.1 hmemG.2 hdom₂ hproj₂ g
        have hf_fin' : eLpNorm f (ENNReal.ofReal p₁.toReal) Measure.count < ⊤ := by
          rw [← hp₁eq]; exact hf_fin
        have hg_fin' : eLpNorm g (ENNReal.ofReal p₂.toReal) Measure.count < ⊤ := by
          rw [← hp₂eq]; exact hg_fin
        have hFmem : MemLp (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f)
            (ENNReal.ofReal p₁.toReal) Measure.count := by
          refine MeasureTheory.memLp_iff.mpr ?_
          exact lt_of_le_of_lt hFb (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf_fin')
        have hGmem : MemLp (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ)
            (Nat.floor (a n)) g) (ENNReal.ofReal p₂.toReal) Measure.count := by
          refine MeasureTheory.memLp_iff.mpr ?_
          exact lt_of_le_of_lt hGb (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg_fin')
        have hmain := eLpNorm_exceptionalPart_le (B₀ := Bnd C₀)
          (KB := (P.natDegree + 1) * (Bnd C₀ + 2) + 2)
          (CC₁ := envConst C₁ (Bnd C₀) ((P.natDegree + 1) * (Bnd C₀ + 2) + 2))
          (CC₂ := envConst C₂ (Bnd C₀) ((P.natDegree + 1) * (Bnd C₀ + 2) + 2))
          P C₀ a f g l₁ l₂ k₁ k₂ n hq1R hq2R hdom₁ hdom₂ hsum' hproj₁ hproj₂
          hbound.2.1 hbound.2.2.1 hbound.2.2.2.1 hbound.2.2.2.2 hKBval hlog hExc hFmem hGmem
        rw [hp₁eq, hp₂eq]
        exact hmain
      · rw [exceptionalPart_eq_zero ρ P C₀ a f g l₁ l₂ k₁ k₂ n hExc]
        simp
    refine (eLpNorm_variationalNorm_le_sum (r := r) (p := (p₁⁻¹ + p₂⁻¹)⁻¹) hr1 hq
      hsupp hmeas).trans ?_
    have hsum_le : ∑ n ∈ Finset.range (nBound Λ (Bnd C₀)),
        4 * eLpNorm (fun x => exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          ((p₁⁻¹ + p₂⁻¹)⁻¹) Measure.count
        ≤ ∑ _n ∈ Finset.range (nBound Λ (Bnd C₀)),
          4 * (ENNReal.ofReal (16 * (envConst C₁ (Bnd C₀)
                ((P.natDegree + 1) * (Bnd C₀ + 2) + 2) : ℝ)
              * (envConst C₂ (Bnd C₀) ((P.natDegree + 1) * (Bnd C₀ + 2) + 2) : ℝ)) *
            (eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count)) :=
      Finset.sum_le_sum (fun n hn => mul_le_mul' le_rfl (hterm n hn))
    refine hsum_le.trans ?_
    calc ∑ _n ∈ Finset.range (nBound Λ (Bnd C₀)),
          4 * (ENNReal.ofReal (16 * (envConst C₁ (Bnd C₀)
                ((P.natDegree + 1) * (Bnd C₀ + 2) + 2) : ℝ)
              * (envConst C₂ (Bnd C₀) ((P.natDegree + 1) * (Bnd C₀ + 2) + 2) : ℝ)) *
            (eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count))
        = (nBound Λ (Bnd C₀) : ENNReal) *
            (4 * (ENNReal.ofReal (16 * (envConst C₁ (Bnd C₀)
                ((P.natDegree + 1) * (Bnd C₀ + 2) + 2) : ℝ)
              * (envConst C₂ (Bnd C₀) ((P.natDegree + 1) * (Bnd C₀ + 2) + 2) : ℝ)) *
              (eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (Kc Λ : ENNReal) * (eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count) := by
          refine term_sum_le (nB := nBound Λ (Bnd C₀))
            (M := 16 * (envConst C₁ (Bnd C₀) ((P.natDegree + 1) * (Bnd C₀ + 2) + 2) : ℝ)
              * (envConst C₂ (Bnd C₀) ((P.natDegree + 1) * (Bnd C₀ + 2) + 2) : ℝ))
            (X := _) ?_
          rw [hKcdef]
          exact le_max_left _ 1
      _ = (Kc Λ : ENNReal) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count := by
          ring
  · have htop_or : eLpNorm f p₁ Measure.count = ⊤ ∨ eLpNorm g p₂ Measure.count = ⊤ := by
      by_cases hA : eLpNorm f p₁ Measure.count = ⊤
      · exact Or.inl hA
      · refine Or.inr ?_
        by_contra hB
        exact hfin ⟨lt_top_iff_ne_top.mpr hA, lt_top_iff_ne_top.mpr hB⟩
    rcases lt_or_eq_of_le (show (0 : ENNReal) ≤ eLpNorm f p₁ Measure.count from bot_le) with hApos | hA0
    · rcases lt_or_eq_of_le (show (0 : ENNReal) ≤ eLpNorm g p₂ Measure.count from bot_le) with hBpos | hB0
      · have htop : (Kc Λ : ENNReal) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count
            = ⊤ := by
          rcases htop_or with h | h
          · have hA : eLpNorm f p₁ Measure.count = ⊤ := h
            rw [hA]
            simp [hKcne, ne_of_gt hBpos]
          · have hB : eLpNorm g p₂ Measure.count = ⊤ := h
            rw [hB]
            simp [hKcne, ne_of_gt hApos]
        rw [htop]
        exact le_top
      · have hp₂0 : p₂ ≠ 0 := by
          intro h; rw [h] at hp₂; exact absurd hp₂ (by norm_num)
        have hg0 : g = 0 := eq_zero_of_eLpNorm_eq_zero hp₂0 hB0.symm
        have hzero : (fun x : ℤ => variationalNorm r (fun n : ℕ =>
            exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) = 0 := by
          have hfam : (fun n : ℕ => exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n) = 0 := by
            rw [hg0]
            exact exceptionalPart_zero_right ρ P C₀ a f l₁ l₂ k₁ k₂
          calc (fun x : ℤ => variationalNorm r (fun n : ℕ =>
                exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              = (fun _ : ℤ => variationalNorm r (0 : ℕ → ℂ)) := by
                funext x
                congr 1
                funext n
                simpa only [Pi.zero_apply] using congrFun (congrFun hfam n) x
            _ = 0 := by
                funext x
                exact variationalNorm_zero r hr1
        rw [hzero, eLpNorm_zero]
        exact bot_le
    · have hp₁0 : p₁ ≠ 0 := by
        intro h; rw [h] at hp₁; exact absurd hp₁ (by norm_num)
      have hf0 : f = 0 := eq_zero_of_eLpNorm_eq_zero hp₁0 hA0.symm
      have hzero : (fun x : ℤ => variationalNorm r (fun n : ℕ =>
          exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) = 0 := by
        have hfam : (fun n : ℕ => exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n) = 0 := by
          rw [hf0]
          exact exceptionalPart_zero_left ρ P C₀ a g l₁ l₂ k₁ k₂
        calc (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
            = (fun _ : ℤ => variationalNorm r (0 : ℕ → ℂ)) := by
              funext x
              congr 1
              funext n
              simpa only [Pi.zero_apply] using congrFun (congrFun hfam n) x
          _ = 0 := by
              funext x
              exact variationalNorm_zero r hr1
      rw [hzero, eLpNorm_zero]
      exact bot_le

end

end Work.KMTAreas.A7
