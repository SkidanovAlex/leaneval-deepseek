import Mathlib
import Submission.Work.NN.Final.DiscRadialDefs
import Submission.Work.NN.DiscRadial.Setup
import Submission.Work.NN.DiscRadial.Unfold
import Submission.Work.NN.DiscRadial.Comp
import Submission.Work.NN.DiscRadial.Assembly
import Submission.Work.NN.DiscRadial.Outer
import Submission.Work.NN.DiscRadial.discUnfoldExt_contDiffOn
import Submission.Work.NN.DiscRadial.holderNorm_one_ne_top_of_one_lt

noncomputable section
open scoped NNReal ENNReal ContDiff Topology
open Set Metric Filter

namespace Work.NN.DiscRadial

open Work.NN.Final

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The core estimate: for `β ≤ 1` and an open region `W` of directions, the unfolded extension
is `C^k` on the whole tube `W × (1 - c, 2)`. -/
theorem discUnfoldExt_contDiffOn_tube {k : ℕ} {g : X × ℂ → ℂ} {β c : ℝ} (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hc : 1 < c) {W : Set (X × ℂ)} (hW : IsOpen W)
    (hcd : ContDiffOn ℝ (k : WithTop ENat) (discUnfold g) (W ×ˢ Set.Ioo 0 2))
    (hfin : Work.CR.Flat.holderNorm k β (discUnfold g) (W ×ˢ Set.Ioo 0 2) ≠ ⊤) :
    ContDiffOn ℝ (k : WithTop ENat) (discUnfoldExt k g) (W ×ˢ Set.Ioo (1 - c) 2) := by
  have hN : ContDiffOn ℝ (k : WithTop ENat) (discUnfoldExt k g) (W ×ˢ Set.Iio (0:ℝ)) :=
    discUnfoldExt_neg_contDiffOn hβ0 hβ1 hW hcd hfin
  have hH : ContDiffOn ℝ (k : WithTop ENat) (discUnfoldExt k g) (W ×ˢ Set.Ioo 0 2) :=
    hcd.congr (fun z hz => discUnfoldExt_of_pos hz.2.1)
  set δ : ℝ := 2 / ((k : ℝ) + 2) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ2 : δ ≤ 2 := by
    rw [hδdef, div_le_iff₀ (by positivity)]
    nlinarith [show (0:ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]
  have hδpos : (0:ℝ) < 2 := by norm_num
  have hband : ContDiffOn ℝ (k : WithTop ENat) (discUnfoldExt k g) (W ×ˢ Set.Ioo (-δ) δ) :=
    discUnfoldExt_contDiffOn (ε := (2:ℝ)) (δ := δ) hβ0 hW hδpos hδ0 hδ2 hcd hfin
      (hN.mono (fun z hz => ⟨hz.1, hz.2.2⟩))
  intro z hz
  obtain ⟨hzW, hz1, hz2⟩ := hz
  have key : ∀ (s : Set ℝ), IsOpen s → z.2 ∈ s →
      ContDiffOn ℝ (k : WithTop ENat) (discUnfoldExt k g) (W ×ˢ s) →
      ContDiffWithinAt ℝ (k : WithTop ENat) (discUnfoldExt k g) (W ×ˢ Set.Ioo (1 - c) 2) z :=
    fun s hs hzs hf => (hf.contDiffAt ((hW.prod hs).mem_nhds ⟨hzW, hzs⟩)).contDiffWithinAt
  rcases lt_trichotomy z.2 (-δ) with h | h | h
  · exact key _ isOpen_Iio (Set.mem_Iio.mpr (by linarith)) hN
  · exact key _ isOpen_Iio (Set.mem_Iio.mpr (by linarith)) hN
  · rcases lt_trichotomy z.2 δ with h2 | h2 | h2
    · exact key _ isOpen_Ioo (Set.mem_Ioo.mpr ⟨h, h2⟩) hband
    · exact key _ isOpen_Ioo (Set.mem_Ioo.mpr ⟨by linarith, hz2⟩) hH
    · exact key _ isOpen_Ioo (Set.mem_Ioo.mpr ⟨by linarith, hz2⟩) hH

theorem disc_ext_contDiffOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {α : ℝ} (hα0 : 0 < α) {k : ℕ} {U : Set X} (hU : IsOpen U) {g : X × ℂ → ℂ} {c : ℝ}
    (hc : 1 < c)
    (hg : ∀ m : ℕ, m ≤ k → ContDiffOn ℝ (m : WithTop ENat) g (U ×ˢ Metric.ball (0 : ℂ) 1))
    (hfin : Work.CR.Flat.holderNorm k α g (U ×ˢ Metric.ball (0 : ℂ) 1) ≠ ⊤) :
    ContDiffOn ℝ (k : WithTop ENat)
      (Work.NN.Final.discExt k (Work.NN.Final.discWt k) Work.NN.Final.discScale g)
      (U ×ˢ Metric.ball (0 : ℂ) c) := by
  obtain ⟨β, hβ0, hβ1, hfinβ⟩ : ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧
      Work.CR.Flat.holderNorm k β g (U ×ˢ Metric.ball (0 : ℂ) 1) ≠ ⊤ := by
    by_cases h : α ≤ 1
    · exact ⟨α, hα0, h, hfin⟩
    · push_neg at h
      exact ⟨1, one_pos, le_rfl, holderNorm_one_ne_top_of_one_lt h hfin⟩
  have hgk : ContDiffOn ℝ (k : WithTop ENat) g (U ×ˢ Metric.ball (0 : ℂ) 1) :=
    hg k le_rfl
  intro p₀ hp₀
  rw [mem_prod] at hp₀
  obtain ⟨hp₀U, hp₀c⟩ := hp₀
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hp₀c
  by_cases hz0 : p₀.2 = 0
  · -- the origin slice: `discExt = g` near `p₀`
    have hball : {p : X × ℂ | ‖p.2‖ < 1} ∈ 𝓝 p₀ := by
      have : {z : ℂ | ‖z‖ < 1} ∈ 𝓝 (p₀.2) := by
        rw [hz0]
        simpa [Metric.ball, dist_eq_norm] using Metric.ball_mem_nhds (0:ℂ) one_pos
      exact (continuous_snd.continuousAt.preimage_mem_nhds this)
    have hev : (discExt k (discWt k) (discScale) g) =ᶠ[𝓝 p₀] g := by
      filter_upwards [hball, (hU.prod isOpen_ball).mem_nhds ⟨hp₀U, by rw [hz0]; exact Metric.mem_ball_self one_pos⟩]
        with p hp1 hp2
      exact discExt_of_norm_lt_one hp1
    have hgc : ContDiffAt ℝ (k : WithTop ENat) g p₀ :=
      hgk.contDiffAt ((hU.prod isOpen_ball).mem_nhds ⟨hp₀U, by rw [hz0]; exact Metric.mem_ball_self one_pos⟩)
    exact (hgc.congr_of_eventuallyEq hev).contDiffWithinAt
  · -- a point with `p₀.2 ≠ 0`
    set x₀ : X := p₀.1 with hx₀
    set u₀ : ℂ := p₀.2 / (‖p₀.2‖ : ℂ) with hu₀def
    have hu₀ : ‖u₀‖ = 1 := norm_div_norm_eq_one hz0
    obtain ⟨r, hr, hrU⟩ : ∃ r > 0, Metric.ball x₀ r ⊆ U :=
      Metric.mem_nhds_iff.mp (hU.mem_nhds hp₀U)
    set W : Set (X × ℂ) := Metric.ball x₀ r ×ˢ Metric.ball u₀ (1/2) with hWdef
    have hW : IsOpen W := isOpen_ball.prod isOpen_ball
    have hsub : W ⊆ U ×ˢ {u : ℂ | 1/2 < ‖u‖} := by
      rintro w ⟨hw1, hw2⟩
      exact ⟨hrU hw1, show (1:ℝ)/2 < ‖w.2‖ from half_lt_norm_of_mem_ball hu₀ hw2⟩
    have hcdW : ContDiffOn ℝ (k : WithTop ENat) (discUnfold g) (W ×ˢ Set.Ioo 0 2) :=
      (discUnfold_contDiffOn hU hgk).mono (fun z hz => ⟨hsub hz.1, hz.2⟩)
    have hfinW : Work.CR.Flat.holderNorm k β (discUnfold g) (W ×ˢ Set.Ioo 0 2) ≠ ⊤ :=
      discUnfold_holderNorm_ne_top hβ0 hβ1 hU hgk hfinβ hr hrU hu₀
    have hcomb : ContDiffOn ℝ (k : WithTop ENat) (discUnfoldExt k g) (W ×ˢ Set.Ioo (1 - c) 2) :=
      discUnfoldExt_contDiffOn_tube hβ0 hβ1 hc hW hcdW hfinW
    -- the image of `discSigma` stays in the tube
    have hsig : discSigma (X := X) p₀ ∈ W ×ˢ Set.Ioo (1 - c) 2 := by
      have hσ : (discSigma (X := X) p₀).2 = 1 - ‖p₀.2‖ := rfl
      refine ⟨⟨Metric.mem_ball_self hr, ?_⟩, ?_⟩
      · simp only [discSigma, hu₀def, Metric.mem_ball, dist_self]
        norm_num
      · rw [hσ]
        constructor <;> linarith [norm_nonneg p₀.2, hp₀c]
    have hcd1 : ContDiffAt ℝ (k : WithTop ENat) (discUnfoldExt k g) (discSigma (X := X) p₀) :=
      hcomb.contDiffAt ((hW.prod isOpen_Ioo).mem_nhds hsig)
    have hcd2 : ContDiffAt ℝ (k : WithTop ENat) (discSigma (X := X)) p₀ :=
      (contDiffOn_discSigma.of_le le_top).contDiffAt ((isOpen_ne.preimage continuous_snd).mem_nhds hz0)
    have hcomp : ContDiffAt ℝ (k : WithTop ENat) ((discUnfoldExt k g) ∘ (discSigma (X := X))) p₀ :=
      hcd1.comp p₀ hcd2
    have hev : (discExt k (discWt k) (discScale) g) =ᶠ[𝓝 p₀]
        ((discUnfoldExt k g) ∘ (discSigma (X := X))) := by
      filter_upwards [(isOpen_ne.preimage continuous_snd).mem_nhds hz0] with p hp
      exact discExt_eq_discUnfoldExt hp
    exact (hcomp.congr_of_eventuallyEq hev).contDiffWithinAt

end Work.NN.DiscRadial
