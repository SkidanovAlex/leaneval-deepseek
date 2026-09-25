import Mathlib
import Submission.Work.NN.Final.DiscExtDefs
import Submission.Work.NN.Final.flatOneSidedExtension
import Submission.Work.NN.Final.extensionByZeroBall
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Seeley.Setup
import Submission.Work.CR.Flat.Holder.holderNorm_comp_le_of_contDiffOn
import Submission.Work.NN.DiscRadial.holderNorm_comp_univ_contDiffOn
import Submission.Work.NN.Final.DiscExtFlat
import Submission.Work.NN.Final.discFoldHolderData
import Submission.Work.NN.Final.discUnfold2HolderData

noncomputable section
open scoped NNReal ENNReal ContDiff Topology
open Set Metric

namespace Work.NN.Final

theorem discExtOfFlat {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {c : ℝ} (hc : 1 < c) :
    Work.NN.Final.DiscExt α c := by
  intro X inst1 inst2
  set δ : ℝ := (c ^ 2 - 1) / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; nlinarith
  obtain ⟨C2, hC2pos, hC2spec⟩ := flatOneSidedExtension (E := X × ℂ) hα0 hα1 hδpos
  obtain ⟨L1, D1, E1, hL1, hD1, hE1⟩ :=
    discFoldHolderData (X := X) (c := c) hc hα0 hα1.le
  obtain ⟨C1, hC1pos, hC1⟩ :=
    Work.NN.DiscRadial.holderNorm_comp_univ_contDiffOn (X := X × ℂ) (Y := (X × ℂ) × ℝ)
      α hα0 L1 D1 E1
  obtain ⟨L3, D3, E3, hL3, hD3, hE3⟩ :=
    discUnfold2HolderData (X := X) (R := 2 * c) (by linarith) hα0 hα1.le
  obtain ⟨C3, hC3pos, hC3⟩ :=
    Work.NN.DiscRadial.holderNorm_comp_univ_contDiffOn (X := (X × ℂ) × ℝ) (Y := X × ℂ)
      α hα0 L3 D3 E3
  refine ⟨fun k => C1 k * C2 k * C3 k, fun k => mul_pos (mul_pos (hC1pos k) (hC2pos k)) (hC3pos k), ?_⟩
  intro k U g hU hgsm hgfin
  set W : Set (X × ℂ) := U ×ˢ Metric.ball (0 : ℂ) (2 * c) with hWdef
  have hWopen : IsOpen W := by rw [hWdef]; exact hU.prod Metric.isOpen_ball
  set s3 : Set ((X × ℂ) × ℝ) := W ×ˢ {t : ℝ | 0 < t} with hs3def
  have hs3open : IsOpen s3 := by rw [hs3def]; exact hWopen.prod isOpen_Ioi
  set t3 : Set (X × ℂ) := U ×ˢ Metric.ball (0 : ℂ) 1 with ht3def
  have ht3open : IsOpen t3 := by rw [ht3def]; exact hU.prod Metric.isOpen_ball
  have hmap3 : Set.MapsTo (discUnfold2 (X := X)) s3 t3 := by
    intro q hq
    rw [hs3def, Set.mem_prod] at hq
    obtain ⟨hqW, hqt⟩ := hq
    rw [hWdef, Set.mem_prod] at hqW
    rw [ht3def, Set.mem_prod]
    refine ⟨hqW.1, ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact norm_discUnfold2_snd_lt_one q hqt
  have hsm3 : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) (discUnfold2 (X := X)) s3 :=
    fun m => (contDiff_discUnfold2.contDiffOn (s := s3)).of_le (by exact_mod_cast le_top)
  set h : (X × ℂ) × ℝ → ℂ := fun q => g (discUnfold2 (X := X) q) with hhdef
  have hstep3 : Work.CR.Flat.holderNorm k α h s3
      ≤ ENNReal.ofReal (C3 k) * Work.CR.Flat.holderNorm k α g t3 := by
    have hh := hC3 k (discUnfold2 (X := X)) s3 t3 g hsm3 hs3open ht3open hmap3
      (hL3 U hU) (hD3 U hU) (hE3 U hU) (hgsm k le_rfl)
    simpa [hhdef, Function.comp_def] using hh
  have hhsm : ContDiffOn ℝ (k : WithTop ENat) h s3 := by
    rw [hhdef]
    exact (hgsm k le_rfl).comp ((contDiff_discUnfold2.contDiffOn (s := s3)).of_le (by exact_mod_cast le_top)) hmap3
  have hhfin : Work.CR.Flat.holderNorm k α h s3 ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hstep3
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by rwa [ht3def] at hgfin)
  obtain ⟨GG, hGGsm, hGGag, hGGnorm⟩ :=
    hC2spec k W h hWopen hhsm (by rwa [hs3def] at hhfin)
  set t1 : Set ((X × ℂ) × ℝ) := W ×ˢ {t : ℝ | -δ < t} with ht1def
  have ht1open : IsOpen t1 := by rw [ht1def]; exact hWopen.prod isOpen_Ioi
  set s1 : Set (X × ℂ) := U ×ˢ Metric.ball (0 : ℂ) c with hs1def
  have hs1open : IsOpen s1 := by rw [hs1def]; exact hU.prod Metric.isOpen_ball
  set G : X × ℂ → ℂ := fun p => GG (discFold (X := X) p) with hGdef
  have hmap1 : Set.MapsTo (discFold (X := X)) s1 t1 := by
    intro p hp
    rw [hs1def, Set.mem_prod] at hp
    obtain ⟨hpU, hpz⟩ := hp
    rw [Metric.mem_ball, dist_zero_right] at hpz
    rw [ht1def, Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rw [hWdef, Set.mem_prod]
      refine ⟨hpU, ?_⟩
      show p.2 ∈ Metric.ball (0 : ℂ) (2 * c)
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    · show discTau p.2 ∈ {t : ℝ | -δ < t}
      rw [hδdef]
      exact discTau_gt hc hpz
  have hsmF : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) (discFold (X := X)) s1 :=
    fun m => (contDiff_discFold.contDiffOn (s := s1)).of_le (by exact_mod_cast le_top)
  have hGsm' : ContDiffOn ℝ (k : WithTop ENat) G s1 := by
    have h1 : ContDiffOn ℝ (k : WithTop ENat) (GG ∘ discFold (X := X)) s1 :=
      hGGsm.comp (hsmF k) hmap1
    simpa [hGdef, Function.comp_def] using h1
  have hagree : ∀ p : X × ℂ, p.1 ∈ U → ‖p.2‖ < 1 → G p = g p := by
    intro p hpU hpz
    have h1 : (discFold (X := X) p).1 ∈ W := by
      rw [hWdef, Set.mem_prod]
      refine ⟨hpU, ?_⟩
      show p.2 ∈ Metric.ball (0 : ℂ) (2 * c)
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have h2 : 0 < (discFold (X := X) p).2 := by
      show 0 < discTau p.2
      exact discTau_pos_iff.mpr hpz
    have h3 := hGGag (discFold (X := X) p) h1 h2
    have h4 : G p = h (discFold (X := X) p) := h3
    rw [h4, hhdef]
    show g (discUnfold2 (discFold (X := X) p)) = g p
    rw [discUnfold2_discFold]
  have hbound : Work.CR.Flat.holderNorm k α G s1
      ≤ ENNReal.ofReal (C1 k * C2 k * C3 k) * Work.CR.Flat.holderNorm k α g t3 := by
    have hstep1 : Work.CR.Flat.holderNorm k α G s1
        ≤ ENNReal.ofReal (C1 k) * Work.CR.Flat.holderNorm k α GG t1 := by
      have hh := hC1 k (discFold (X := X)) s1 t1 GG hsmF hs1open ht1open hmap1
        (hL1 U hU) (hD1 U hU) (hE1 U hU) hGGsm
      simpa [hGdef, Function.comp_def] using hh
    calc Work.CR.Flat.holderNorm k α G s1
        ≤ ENNReal.ofReal (C1 k) * Work.CR.Flat.holderNorm k α GG t1 := hstep1
      _ ≤ ENNReal.ofReal (C1 k)
            * (ENNReal.ofReal (C2 k) * Work.CR.Flat.holderNorm k α h s3) :=
            mul_le_mul_of_nonneg_left hGGnorm (by simp)
      _ = (ENNReal.ofReal (C1 k) * ENNReal.ofReal (C2 k))
            * Work.CR.Flat.holderNorm k α h s3 := by ring
      _ = ENNReal.ofReal (C1 k * C2 k) * Work.CR.Flat.holderNorm k α h s3 := by
            rw [ENNReal.ofReal_mul (le_of_lt (hC1pos k))]
      _ ≤ ENNReal.ofReal (C1 k * C2 k)
            * (ENNReal.ofReal (C3 k) * Work.CR.Flat.holderNorm k α g t3) :=
            mul_le_mul_of_nonneg_left hstep3 (by simp)
      _ = (ENNReal.ofReal (C1 k * C2 k) * ENNReal.ofReal (C3 k))
            * Work.CR.Flat.holderNorm k α g t3 := by ring
      _ = ENNReal.ofReal (C1 k * C2 k * C3 k) * Work.CR.Flat.holderNorm k α g t3 := by
            rw [ENNReal.ofReal_mul (mul_nonneg (hC1pos k).le (hC2pos k).le)]
  exact ⟨G, hGsm', hagree, hbound⟩

end Work.NN.Final
