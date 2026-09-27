import Mathlib
import Submission.Work.Drive.N2Lead.mobiusUpperFootKit
import Submission.Work.Drive.N2Lead.mobiusUpperStarRowKit
import Submission.Work.Drive.N2Lead.mobiusModelImSubmersion
import Submission.Work.Drive.N2Lead.modelPicDefs
import Submission.Work.Drive.N2Lead.mobiusArcSmooth
import Submission.Work.Drive.N2Lead.mobius_upperArcs
import Submission.Work.N2Lead.absDerivSmoothTransitionLeTwo
import Submission.Work.Drive.N2Lead.modelPicRate
import Submission.Work.Compat.MFDerivCongrV433

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section


theorem mobiusUpperModelRate {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (S : Work.Drive.N2Lead.MobiusPacket D η) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ εp₀ : ℝ, 0 < εp₀ ∧ ∀ εp : ℝ, 0 < εp → εp ≤ εp₀ →
        ∃ D₀ : ℝ, 0 ≤ D₀ ∧ ∀ Dp : ℝ, D₀ ≤ Dp →
          ∀ (y : M) (v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) y),
            f y = f p + 3 * η / 2 →
            y ∈ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z (39 / 20) →
            mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ) f y v = 0 →
            v ≠ 0 →
            ¬ (∃ t : ℝ, mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℂ)
                (fun z : M => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z)) y v
              = t • (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y))) := by
  -- ## the constants
  set δ : ℝ := 1 / 20 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; norm_num
  have hδ₁ : δ < 1 / 10 := by rw [hδdef]; norm_num
  have hδ₂ : δ < 1 / 2 := by rw [hδdef]; norm_num
  set ηs : ℝ := Work.Drive.N2.packetEta D η with hηsdef
  have hs : 0 < ηs := by rw [hηsdef]; exact Work.Drive.N2.packetEta_pos D hη
  have hηs₁ : ηs < 3 / 800 := by
    rw [hηsdef]; exact packetEta_lt_three_eightieth D hsmall
  have hηs₂ : ηs < 1 / 10 := by linarith
  set eps : ℝ := Real.sqrt (S.a' ^ 2 + ηs) with hepsdef
  have heps : 0 < eps := by
    rw [hepsdef]
    exact Real.sqrt_pos.mpr (by nlinarith [S.ha'pos, hs])
  have hepsa : eps ≤ Real.sqrt (S.a' ^ 2 + ηs) := by rw [hepsdef]
  -- ## the bound on the slope of the smooth transition
  have hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ (3 : ℝ) :=
    fun x => le_trans (Work.N2Lead.absDerivSmoothTransitionLeTwo x) (by norm_num)
  have hsmall' : 4 * (3 : ℝ) * ηs ≤ δ := by
    rw [hδdef]; linarith
  -- ## the arc rows
  obtain ⟨harc1, harc2⟩ := mobius_upperArcs (η := ηs) (δ := δ) (s := ηs) (a' := S.a') (ε := eps)
    (C₀ := 3) hδ hδ₁ hs hηs₂ hs le_rfl hC₀ hsmall' S.ha'pos heps hepsa
  have hαsm : ContDiff ℝ 1 (mobiusAlpha ηs δ ηs S.a' eps) :=
    mobiusAlpha_contDiff (η := ηs) (δ := δ) (s := ηs) (a := S.a') (ε := eps) hδ hδ₂ hs
  have hβsm : ContDiff ℝ 1 (mobiusBeta ηs δ ηs S.a' eps) :=
    mobiusBeta_contDiff (η := ηs) (δ := δ) (s := ηs) (a := S.a') (ε := eps) hδ hδ₂ hs
  have hαy : ∀ w ∈ Set.Icc (-2) 2, 0 < (mobiusAlpha ηs δ ηs S.a' eps w) 1 :=
    fun w hw => (harc1 w hw).1
  have hβy : ∀ w ∈ Set.Icc (-2) 2, (mobiusBeta ηs δ ηs S.a' eps w) 1 < 0 :=
    fun w hw => (harc1 w hw).2
  have hαx : ∀ w ∈ Set.Icc (-2) 2,
      0 < deriv (fun u : ℝ => (mobiusAlpha ηs δ ηs S.a' eps u) 0) w :=
    fun w hw => (harc2 w hw).1
  have hβx : ∀ w ∈ Set.Icc (-2) 2,
      0 < deriv (fun u : ℝ => (mobiusBeta ηs δ ηs S.a' eps u) 0) w :=
    fun w hw => (harc2 w hw).2
  -- ## the model lemma
  obtain ⟨εp₀, hεp₀pos, hmodel⟩ :=
    modelPicRate (η := ηs) (δ := δ) (s := ηs) (a' := S.a') (ε := eps)
      hs hδ hδ₂ hs S.ha'pos heps hαsm hβsm hαy hβy hαx hβx
  refine ⟨eps, heps, εp₀, hεp₀pos, ?_⟩
  intro εp hεp hεple
  obtain ⟨D₀, hD₀nn, hD₀⟩ := hmodel εp hεp hεple
  refine ⟨D₀, hD₀nn, ?_⟩
  intro Dp hDp y v hy hreg hv hvne
  rintro ⟨t, ht⟩
  -- ## the geometric data at `y`
  have hUopen : IsOpen (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) :=
    isOpen_modelBall_mobius (D.φ D.j) (D.ρ D.j)
  have hZdiff : MDifferentiableAt (𝓡 2) 𝓘(ℝ,ℂ) S.Z y :=
    (S.hZsm.contMDiffAt (hUopen.mem_nhds hreg.1)).mdifferentiableAt (by simp)
  have hZc : ContinuousAt S.Z y := hZdiff.continuousAt
  have hζre : ((S.Z y) ^ 2).re = ηs := by
    have hlaw := lam0_sq_mul_packetEta (D := D) S
    have hne : S.lam0 ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt S.hlam0pos)
    have h2 : S.lam0 ^ 2 * ((S.Z y) ^ 2).re = S.lam0 ^ 2 * ηs := by
      have h3 : S.lam0 ^ 2 * ((S.Z y) ^ 2).re = 3 * η / 2 := by
        have h4 := S.hlev y hreg.1
        rw [hy] at h4
        linarith
      rw [h3, hlaw]
    exact mul_left_cancel₀ hne h2
  have hζne : S.Z y ≠ 0 := by
    intro h0
    have hpos : 0 < ((S.Z y) ^ 2).re := by rw [hζre]; exact hs
    rw [h0] at hpos; simp at hpos
  have hζim : |((S.Z y) ^ 2).im| < 39 / 20 := hreg.2
  obtain ⟨w, hwdef⟩ : ∃ w : ℂ, w = mfderiv (𝓡 2) 𝓘(ℝ,ℂ) S.Z y v := ⟨_, rfl⟩
  have hwne : w ≠ 0 := by
    intro h0
    refine hvne (S.hZimm y hreg.1 ?_)
    rw [← hwdef, h0, map_zero]
    rfl
  -- ## the level condition, transported to the chart
  have hμ : (2 * S.Z y * w).re = 0 := by
    have hfeq : f =ᶠ[𝓝 y] (fun z : M => f p + S.lam0 ^ 2 * ((S.Z z) ^ 2).re) := by
      filter_upwards [hUopen.mem_nhds hreg.1] with z hz
      exact S.hlev z hz
    have h1p : mfderiv (𝓡 2) 𝓘(ℝ,ℝ)
        (fun z : M => f p + S.lam0 ^ 2 * ((S.Z z) ^ 2).re) y v = 0 := by
      rw [← hfeq.mfderiv_eq_v433]; exact hv
    have hqc : MDifferentiableAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ)
        (fun ζ : ℂ => f p + S.lam0 ^ 2 * (ζ ^ 2).re) (S.Z y) :=
      (mdifferentiableAt_iff_differentiableAt (𝕜 := ℝ)).mpr (by fun_prop)
    have h1raw : (fderiv ℝ (fun ζ : ℂ => S.lam0 ^ 2 * (ζ ^ 2).re) (S.Z y))
        (mfderiv (𝓡 2) 𝓘(ℝ,ℂ) S.Z y v) = 0 := by
      have h1' : mfderiv (𝓡 2) 𝓘(ℝ,ℝ)
          ((fun ζ : ℂ => f p + S.lam0 ^ 2 * (ζ ^ 2).re) ∘ S.Z) y v = 0 := h1p
      rw [mfderiv_comp_apply (f := S.Z)
        (g := fun ζ : ℂ => f p + S.lam0 ^ 2 * (ζ ^ 2).re) y hqc hZdiff v] at h1'
      rw [mfderiv_eq_fderiv, fderiv_const_add] at h1'
      exact h1'
    have h1'' : (fderiv ℝ (fun ζ : ℂ => S.lam0 ^ 2 * (ζ ^ 2).re) (S.Z y)) w = 0 := by
      rw [hwdef]; exact h1raw
    rw [Work.Drive.N2.fderiv_smul_sq_re_apply] at h1''
    rcases mul_eq_zero.mp h1'' with h | h
    · exact absurd h (pow_ne_zero 2 (ne_of_gt S.hlam0pos))
    · exact h
  -- ## the germ equality with the plane model
  have hsplit : ∀ᶠ z in 𝓝 y, |((S.Z z) ^ 2).im| < 39 / 20 := by
    have hφ : ContinuousAt (fun ζ : ℂ => |(ζ ^ 2).im|) (S.Z y) :=
      (continuous_abs.comp (Complex.continuous_im.comp (continuous_id.pow 2))).continuousAt
    exact (hφ.tendsto.comp hZc.tendsto) (isOpen_Iio.mem_nhds hreg.2)
  have hgerm : (fun z : M => Work.Drive.N2Lead.proj2
        (Work.Drive.N2Lead.mobiusTwisted D η S eps εp Dp z))
      =ᶠ[𝓝 y] (fun z : M => modelPic ηs δ S.a' eps Dp εp (S.Z z)) := by
    filter_upwards [hUopen.mem_nhds hreg.1, hsplit] with z hz1 hz2
    have hmem : z ∈ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j))
        S.Z (39 / 20) := ⟨hz1, hz2⟩
    simp only [Work.Drive.N2Lead.mobiusTwisted, Work.Drive.N2Lead.mobiusWindowDrawing,
      Work.Drive.N2Lead.modelPic, if_pos hmem, hηsdef, hδdef]
  -- ## the value identity
  have hval : Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S eps εp Dp y)
      = modelPic ηs δ S.a' eps Dp εp (S.Z y) := hgerm.eq_of_nhds
  -- ## the chain rule
  have hKdiff : MDifferentiableAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) (modelPic ηs δ S.a' eps Dp εp) (S.Z y) :=
    ((contDiff_modelPic (η := ηs) (δ := δ) (a' := S.a') (ε := eps) (Dp := Dp) (εp := εp)
      hδ hδ₂).contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have hchain : (fderiv ℝ (modelPic ηs δ S.a' eps Dp εp) (S.Z y)) w
      = mfderiv (𝓡 2) 𝓘(ℝ,ℂ)
          (fun z : M => modelPic ηs δ S.a' eps Dp εp (S.Z z)) y v := by
    have h := mfderiv_comp_apply (f := S.Z) (g := modelPic ηs δ S.a' eps Dp εp) y hKdiff hZdiff v
    simp only [mfderiv_eq_fderiv] at h
    rw [hwdef]
    exact h.symm
  -- ## the contradiction
  have hkey : mfderiv (𝓡 2) 𝓘(ℝ,ℂ)
        (fun z : M => modelPic ηs δ S.a' eps Dp εp (S.Z z)) y v
      = t • (modelPic ηs δ S.a' eps Dp εp (S.Z y)) := by
    have hc : (mfderiv (𝓡 2) 𝓘(ℝ,ℂ)
          (fun z : M => modelPic ηs δ S.a' eps Dp εp (S.Z z)) y) v
        = (mfderiv (𝓡 2) 𝓘(ℝ,ℂ)
          (fun z : M => Work.Drive.N2Lead.proj2
            (Work.Drive.N2Lead.mobiusTwisted D η S eps εp Dp z)) y) v :=
      congrArg (fun L : TangentSpace (𝓡 2) y →L[ℝ] ℂ => L v) hgerm.mfderiv_eq_v433.symm
    exact hc.trans (ht.trans (congrArg (fun z : ℂ => t • z) hval))
  have hfin : (fderiv ℝ (modelPic ηs δ S.a' eps Dp εp) (S.Z y)) w
      = t • (modelPic ηs δ S.a' eps Dp εp (S.Z y)) := by
    rw [hchain]; exact hkey
  exact hD₀ Dp hDp (S.Z y) w hζne hζre hζim hμ hwne ⟨t, hfin⟩

end

end Work.Drive.N2Lead
