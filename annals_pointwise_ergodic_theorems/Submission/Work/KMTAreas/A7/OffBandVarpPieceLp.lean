import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedDefs
import Submission.Work.KMTAreas.A7.BilinOpKhalf
import Submission.Work.KMTAreas.A7.eLpNorm_khalf_bilinOp_le
import Submission.Work.KMTAreas.A7.ExcAux
import Submission.Work.KMTAreas.A7.KmtProjUniform
import Submission.Work.KMTAreas.A7.KmtKernelL1Uniform

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.EndVar

noncomputable section

/-- **The crude (O(1) in N) single-scale `ℓ^p` bound for the concrete §5 column `varpPiece`, in the
bounded off-band regime, with NO hypothesis on `f`, `g`.**

For fixed `ρ ∈ (0,1]` and a bound `B` on the heights `l₂,k₁,k₂` and on `Log N`, there is a constant
`C > 0` (depending only on `P, p₁, p₂, ρ, B`) such that for every `N : ℕ` with `Log N ≤ B` and every
`f, g : ℤ → ℂ`,

  `‖varpPiece (kmtPj ρ) P P.natDegree N f g 0 l₂ k₁ k₂‖_{ℓ^{(p₁⁻¹+p₂⁻¹)⁻¹}} ≤ C ‖f‖_{ℓ^{p₁}} ‖g‖_{ℓ^{p₂}}`.

This is the unconditional form (no `MemLp` side conditions), which is what the surrounding
lacunary summation needs.

Proof route.  By `Work.KMTAreas.A7.varpPiece`'s definition and
`Work.KMTAreas.A7.BilinOpKhalf` (`Submission/Work/KMTAreas/A7/BilinOpKhalf.lean`),
`varpPiece (kmtPj ρ) P P.natDegree N f g 0 l₂ k₁ k₂ = bilinOp (khalf ⌊N⌋ P) (Fpiece … f) (Gpiece … g)`;
`Work.KMTAreas.A7.eLpNorm_khalf_bilinOp_le`
(`Submission/Work/KMTAreas/A7/eLpNorm_khalf_bilinOp_le.lean`) then bounds its `ℓ^p` norm by
`‖Fpiece … f‖_{p₁}·‖Gpiece … g‖_{p₂}` with NO side condition.  Finally
`Work.KMTAreas.A7.eLpNorm_piece_le` (`Submission/Work/KMTAreas/A7/ExcAux.lean`) bounds the two pieces
by `4·CC₁·‖f‖_{p₁}` and `4·CC₂·‖g‖_{p₂}`, where `CCᵢ := envConst Cᵢ B KB`,
`KB := (P.natDegree+1)*(B+2)+2` and the projection constants `Cᵢ` come from `KmtProjUniform` fed by
`KmtKernelL1Uniform` (the instantiation of `ExceptionalBound_of_ingredients`,
`Submission/Work/KMTAreas/A7/ExcAux2.lean`, lines ~120-160); the height hypotheses `l₂,k₁,k₂ ≤ B`,
`logN N ≤ B` and `hKB` are exactly what `eLpNorm_piece_le` needs.  Take `C := 16·CC₁·CC₂`.
Do NOT route through `sd_varpPiece_eq_bilinOp` (it needs `BoundedZ f, g`). -/
theorem OffBandVarpPieceLp (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₂ k₁ k₂ N : ℕ) (f g : ℤ → ℂ),
      l₂ ≤ B → k₁ ≤ B → k₂ ≤ B → (Work.Analysis.EndVar.logN N).toNat ≤ B →
      MeasureTheory.eLpNorm (fun x : ℤ =>
          Work.Analysis.EndVar.varpPiece (Work.KMTContract.kmtPj ρ) P P.natDegree (N : NNReal)
            f g 0 l₂ k₁ k₂ x)
        (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C *
          (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
            MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by
  obtain ⟨R, hRpos, hR⟩ := KmtKernelL1Uniform
  have hq1R : 1 < p₁.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt htp₁)).mpr hp₁
  have hq2R : 1 < p₂.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt htp₂)).mpr hp₂
  obtain ⟨C₁, hC₁pos, hC₁⟩ := KmtProjUniform (q := p₁.toReal) hq1R hRpos hR
  obtain ⟨C₂, hC₂pos, hC₂⟩ := KmtProjUniform (q := p₂.toReal) hq2R hRpos hR
  set KB : ℕ := (P.natDegree + 1) * (B + 2) + 2 with hKBdef
  set CC₁ : NNReal := envConst C₁ B KB with hCC₁
  set CC₂ : NNReal := envConst C₂ B KB with hCC₂
  have hCC₁pos : (0 : NNReal) < CC₁ := by rw [hCC₁]; exact envConst_pos hC₁pos B KB
  have hCC₂pos : (0 : NNReal) < CC₂ := by rw [hCC₂]; exact envConst_pos hC₂pos B KB
  refine ⟨16 * (CC₁ : ℝ) * (CC₂ : ℝ), ?_, ?_⟩
  · exact mul_pos (mul_pos (by norm_num) (by exact_mod_cast hCC₁pos)) (by exact_mod_cast hCC₂pos)
  intro l₂ k₁ k₂ N f g hl₂ hk₁ hk₂ hlogNat
  have hlog : logN N ≤ (B : ℤ) := by
    have h0 : 0 ≤ logN N := logN_nonneg N
    have h1 : (((logN N).toNat : ℤ)) ≤ (B : ℤ) := by exact_mod_cast hlogNat
    rwa [Int.toNat_of_nonneg h0] at h1
  have hKBle : B + 1 ≤ KB := by
    rw [hKBdef]; nlinarith [Nat.zero_le P.natDegree]
  have hKBval : (P.natDegree + 1) * (B + 2) + 2 ≤ KB := by rw [hKBdef]
  have hdom₁ : ∀ l' ∈ Finset.Icc 0 B,
      ∀ m' ∈ Finset.Icc (-(KB : ℤ) - 1) (KB : ℤ), C₁ l' m' ≤ CC₁ := by
    intro l' hl' m' hm'
    rw [hCC₁]
    exact le_envConst hl' hm'
  have hdom₂ : ∀ l' ∈ Finset.Icc 0 B,
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
  have hmemF := mem_freq_F hlog hk₁ hKBle
  have hmemG := mem_freq_G (d := P.natDegree) hlog hk₂ hKBval
  have hFb : eLpNorm (Fpiece (Work.KMTContract.kmtPj ρ) 0 0 (k₁ : ℤ) N f)
        (ENNReal.ofReal p₁.toReal) Measure.count
      ≤ ENNReal.ofReal (4 * (CC₁ : ℝ)) * eLpNorm f (ENNReal.ofReal p₁.toReal) Measure.count :=
    eLpNorm_piece_le (q := p₁.toReal) (C := C₁) (CC := CC₁) (B₀ := B) (KB := KB) (l := 0)
      (κ := fun s => -(logN N) + s) (a := 0) (s := (k₁ : ℤ))
      hq1R (Nat.zero_le B) hmemF.1 hmemF.2 hdom₁ hproj₁ f
  have hGb : eLpNorm (Gpiece (Work.KMTContract.kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) N g)
        (ENNReal.ofReal p₂.toReal) Measure.count
      ≤ ENNReal.ofReal (4 * (CC₂ : ℝ)) * eLpNorm g (ENNReal.ofReal p₂.toReal) Measure.count :=
    eLpNorm_piece_le (q := p₂.toReal) (C := C₂) (CC := CC₂) (B₀ := B) (KB := KB) (l := l₂)
      (κ := fun s => (P.natDegree : ℤ) * (-(logN N) + s)) (a := 0) (s := (k₂ : ℤ))
      hq2R hl₂ hmemG.1 hmemG.2 hdom₂ hproj₂ g
  have hFble : eLpNorm (Fpiece (Work.KMTContract.kmtPj ρ) 0 0 (k₁ : ℤ) N f)
        p₁ Measure.count
      ≤ ENNReal.ofReal (4 * (CC₁ : ℝ)) * eLpNorm f p₁ Measure.count := by
    rw [← hp₁eq]; exact hFb
  have hGble : eLpNorm (Gpiece (Work.KMTContract.kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) N g)
        p₂ Measure.count
      ≤ ENNReal.ofReal (4 * (CC₂ : ℝ)) * eLpNorm g p₂ Measure.count := by
    rw [← hp₂eq]; exact hGb
  have hfun : (fun x : ℤ =>
        varpPiece (Work.KMTContract.kmtPj ρ) P P.natDegree (N : NNReal) f g 0 l₂ k₁ k₂ x)
      = (fun x : ℤ => bilinOp (khalf N P)
          (Fpiece (Work.KMTContract.kmtPj ρ) 0 0 (k₁ : ℤ) N f)
          (Gpiece (Work.KMTContract.kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) N g) x) := by
    funext x
    rw [varpPiece, BilinOpKhalf]
    simp only [Nat.floor_natCast]
  rw [hfun]
  refine (eLpNorm_khalf_bilinOp_le P N ((p₁⁻¹ + p₂⁻¹)⁻¹) p₁ p₂ (by rw [inv_inv])
      (ENNReal.one_le_inv.mpr hsum)
      (Fpiece (Work.KMTContract.kmtPj ρ) 0 0 (k₁ : ℤ) N f)
      (Gpiece (Work.KMTContract.kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) N g)).trans ?_
  calc eLpNorm (Fpiece (Work.KMTContract.kmtPj ρ) 0 0 (k₁ : ℤ) N f) p₁ Measure.count
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
