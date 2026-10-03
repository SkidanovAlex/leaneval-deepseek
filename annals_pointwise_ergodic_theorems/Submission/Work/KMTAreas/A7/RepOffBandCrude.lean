import Mathlib
import Submission.Work.KMTAreas.A7.OffBandVarpPieceLp

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.EndVar

noncomputable section

theorem RepOffBandCrude (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ l₂ k₁ k₂ N : ℕ) (f g : ℤ → ℂ),
      l₁ ≤ B → l₂ ≤ B → k₁ ≤ B → k₂ ≤ B → N ≤ 2 ^ B →
      MeasureTheory.eLpNorm (Work.Analysis.EndVar.varpPiece (Work.KMTContract.kmtPj ρ) P P.natDegree
          (N : NNReal) f g l₁ l₂ k₁ k₂)
        (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by
  obtain ⟨R, hRpos, hR⟩ := KmtKernelL1Uniform
  have hq1R : 1 < p₁.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt htp₁)).mpr hp₁
  have hq2R : 1 < p₂.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt htp₂)).mpr hp₂
  obtain ⟨C₁, hC₁pos, hC₁⟩ := KmtProjUniform (q := p₁.toReal) hq1R hRpos hR
  obtain ⟨C₂, hC₂pos, hC₂⟩ := KmtProjUniform (q := p₂.toReal) hq2R hRpos hR
  set B₀ : ℕ := max B 1 with hB₀def
  have hBB₀ : B ≤ B₀ := le_max_left B 1
  have hB₀1 : 1 ≤ B₀ := le_max_right B 1
  set KB : ℕ := (P.natDegree + 1) * (B₀ + 2) + 2 with hKBdef
  set CC₁ : NNReal := envConst C₁ B₀ KB with hCC₁
  set CC₂ : NNReal := envConst C₂ B₀ KB with hCC₂
  have hCC₁pos : (0 : NNReal) < CC₁ := by rw [hCC₁]; exact envConst_pos hC₁pos B₀ KB
  have hCC₂pos : (0 : NNReal) < CC₂ := by rw [hCC₂]; exact envConst_pos hC₂pos B₀ KB
  refine ⟨16 * (CC₁ : ℝ) * (CC₂ : ℝ), ?_, ?_⟩
  · exact mul_pos (mul_pos (by norm_num) (by exact_mod_cast hCC₁pos)) (by exact_mod_cast hCC₂pos)
  intro l₁ l₂ k₁ k₂ N f g hl₁ hl₂ hk₁ hk₂ hN
  have hN' : N ≤ 2 ^ B₀ :=
    hN.trans (Nat.pow_le_pow_right (by norm_num : 0 < 2) hBB₀)
  have hlog : logN N ≤ (B₀ : ℤ) := logN_le_of_le_pow hN' hB₀1
  have hl₁' : l₁ ≤ B₀ := hl₁.trans hBB₀
  have hl₂' : l₂ ≤ B₀ := hl₂.trans hBB₀
  have hk₁' : k₁ ≤ B₀ := hk₁.trans hBB₀
  have hk₂' : k₂ ≤ B₀ := hk₂.trans hBB₀
  have hKBle : B₀ + 1 ≤ KB := by
    rw [hKBdef]; nlinarith [Nat.zero_le P.natDegree]
  have hKBval : (P.natDegree + 1) * (B₀ + 2) + 2 ≤ KB := by rw [hKBdef]
  have hdom₁ : ∀ l' ∈ Finset.Icc 0 B₀,
      ∀ m' ∈ Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ), C₁ l' m' ≤ CC₁ := by
    intro l' hl' m' hm'
    rw [hCC₁]
    exact le_envConst hl' hm'
  have hdom₂ : ∀ l' ∈ Finset.Icc 0 B₀,
      ∀ m' ∈ Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ), C₂ l' m' ≤ CC₂ := by
    intro l' hl' m' hm'
    rw [hCC₂]
    exact le_envConst hl' hm'
  have hproj₁ : ∀ (l' : ℕ) (k' : ℤ) (u : ℤ → ℂ),
      eLpNorm (Work.KMTContract.kmtProj ρ l' k' u) (ENNReal.ofReal p₁.toReal) Measure.count
        ≤ ENNReal.ofReal (C₁ l' k' : ℝ) *
          eLpNorm u (ENNReal.ofReal p₁.toReal) Measure.count := hC₁ ρ hρ hρ1
  have hproj₂ : ∀ (l' : ℕ) (k' : ℤ) (u : ℤ → ℂ),
      eLpNorm (Work.KMTContract.kmtProj ρ l' k' u) (ENNReal.ofReal p₂.toReal) Measure.count
        ≤ ENNReal.ofReal (C₂ l' k' : ℝ) *
          eLpNorm u (ENNReal.ofReal p₂.toReal) Measure.count := hC₂ ρ hρ hρ1
  have hp₁eq : ENNReal.ofReal p₁.toReal = p₁ := ENNReal.ofReal_toReal (ne_of_lt htp₁)
  have hp₂eq : ENNReal.ofReal p₂.toReal = p₂ := ENNReal.ofReal_toReal (ne_of_lt htp₂)
  have hmemF := mem_freq_F hlog hk₁' hKBle
  have hmemG := mem_freq_G (d := P.natDegree) hlog hk₂' hKBval
  have hFb : eLpNorm (Fpiece (Work.KMTContract.kmtPj ρ) 0 l₁ (k₁ : ℤ) N f)
        (ENNReal.ofReal p₁.toReal) Measure.count
      ≤ ENNReal.ofReal (4 * (CC₁ : ℝ)) * eLpNorm f (ENNReal.ofReal p₁.toReal) Measure.count :=
    eLpNorm_piece_le (q := p₁.toReal) (C := C₁) (CC := CC₁) (B₀ := B₀) (KB := KB) (l := l₁)
      (κ := fun s => -(logN N) + s) (a := 0) (s := (k₁ : ℤ))
      hq1R hl₁' hmemF.1 hmemF.2 hdom₁ hproj₁ f
  have hGb : eLpNorm (Gpiece (Work.KMTContract.kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) N g)
        (ENNReal.ofReal p₂.toReal) Measure.count
      ≤ ENNReal.ofReal (4 * (CC₂ : ℝ)) * eLpNorm g (ENNReal.ofReal p₂.toReal) Measure.count :=
    eLpNorm_piece_le (q := p₂.toReal) (C := C₂) (CC := CC₂) (B₀ := B₀) (KB := KB) (l := l₂)
      (κ := fun s => (P.natDegree : ℤ) * (-(logN N) + s)) (a := 0) (s := (k₂ : ℤ))
      hq2R hl₂' hmemG.1 hmemG.2 hdom₂ hproj₂ g
  have hFble : eLpNorm (Fpiece (Work.KMTContract.kmtPj ρ) 0 l₁ (k₁ : ℤ) N f)
        p₁ Measure.count
      ≤ ENNReal.ofReal (4 * (CC₁ : ℝ)) * eLpNorm f p₁ Measure.count := by
    rw [← hp₁eq]; exact hFb
  have hGble : eLpNorm (Gpiece (Work.KMTContract.kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) N g)
        p₂ Measure.count
      ≤ ENNReal.ofReal (4 * (CC₂ : ℝ)) * eLpNorm g p₂ Measure.count := by
    rw [← hp₂eq]; exact hGb
  have hfun : varpPiece (Work.KMTContract.kmtPj ρ) P P.natDegree (N : NNReal) f g l₁ l₂ k₁ k₂
      = bilinOp (khalf N P)
          (Fpiece (Work.KMTContract.kmtPj ρ) 0 l₁ (k₁ : ℤ) N f)
          (Gpiece (Work.KMTContract.kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) N g) := by
    funext x
    rw [varpPiece, BilinOpKhalf]
    simp only [Nat.floor_natCast]
  rw [hfun]
  refine (eLpNorm_khalf_bilinOp_le P N ((p₁⁻¹ + p₂⁻¹)⁻¹) p₁ p₂ (by rw [inv_inv])
      (ENNReal.one_le_inv.mpr hsum)
      (Fpiece (Work.KMTContract.kmtPj ρ) 0 l₁ (k₁ : ℤ) N f)
      (Gpiece (Work.KMTContract.kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) N g)).trans ?_
  calc eLpNorm (Fpiece (Work.KMTContract.kmtPj ρ) 0 l₁ (k₁ : ℤ) N f) p₁ Measure.count
        * eLpNorm (Gpiece (Work.KMTContract.kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) N g)
            p₂ Measure.count
      ≤ (ENNReal.ofReal (4 * (CC₁ : ℝ)) * eLpNorm f p₁ Measure.count)
        * (ENNReal.ofReal (4 * (CC₂ : ℝ)) * eLpNorm g p₂ Measure.count) :=
        mul_le_mul' hFble hGble
    _ = ENNReal.ofReal (16 * (CC₁ : ℝ) * (CC₂ : ℝ)) *
          (eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count) := by
        have h4₁ : ENNReal.ofReal (4 * (CC₁ : ℝ)) = 4 * ENNReal.ofReal (CC₁ : ℝ) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
        have h4₂ : ENNReal.ofReal (4 * (CC₂ : ℝ)) = 4 * ENNReal.ofReal (CC₂ : ℝ) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
        have h16 : ENNReal.ofReal (16 * (CC₁ : ℝ) * (CC₂ : ℝ))
            = 16 * ENNReal.ofReal (CC₁ : ℝ) * ENNReal.ofReal (CC₂ : ℝ) := by
          rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 16 * (CC₁ : ℝ)),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16), ENNReal.ofReal_ofNat]
        rw [h4₁, h4₂, h16]
        ring

end

end Work.KMTAreas.A7
