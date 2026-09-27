import Mathlib
import Submission.Work.Drive.N2Lead.mobiusUpperDefs
import Submission.Work.Drive.N2C.mobiusShape
import Submission.Work.Drive.N2Lead.mobiusPacketDefs
import Submission.Work.Drive.N2Lead.mobiusUpperStarRowKit
import Submission.Work.Drive.N2Lead.mobiusUpperFootKit
import Submission.Work.Drive.N2C.mfrFootPlumbing
import Submission.Work.Drive.N2C.mobiusModelPieceRows
import Submission.Work.Drive.N2C.mobiusBridgeCurveRow
import Submission.Work.Drive.N2C.mobiusPinCurveRow
import Submission.Work.Drive.N2C.mobiusArcCurveRow
import Submission.Work.Drive.N2Lead.mobiusUpperCoreKit
import Submission.Work.Drive.N2C.mfrParkPiece
import Submission.Work.Drive.N2C.mfrPinPiece
import Submission.Work.Drive.N2C.mfrFarPiece
import Submission.Work.Drive.N2Lead.arcRangeOrBridgeZone
import Submission.Work.Drive.N2Lead.saddlePacketRows
import Submission.Work.Drive.N2Lead.mobius_bridgeStar
import Submission.Work.Drive.N2Lead.arcZ_re_strictMono
import Submission.Work.Drive.N2Lead.polarRowZone
import Submission.Work.Drive.N2Lead.pinCurveRowUp
import Submission.Work.Drive.N2Lead.pinCurveRowDn
import Submission.Work.Drive.N2Lead.arcToPolarRowUp
import Submission.Work.Drive.N2Lead.arcToPolarRowDn
import Submission.Work.Drive.N2Lead.arcZ_rigid_bounds
import Submission.Work.Drive.N2Lead.profile_cos_ge
import Submission.Work.Compat.MFDerivCongrV433

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

section Helpers

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]

open scoped Manifold ContDiff Topology in
open Set Filter in
/-- **The value of the picture of a non-model level point whose foot is on the marked component**:
the picture is the polar picture at the angle `Θ t₀`. -/
lemma markedFootValue {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    {S : MobiusPacket D η} {ε εp Dp : ℝ} {y : M} {t₀ : ℝ}
    (hyD : y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z
      (39 / 20))
    (hfoot : Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y = S.L.γ S.i t₀) :
    proj2 (mobiusTwisted D η S ε εp Dp y) = polarPic S.r Dp εp ε (S.Θ t₀) := by
  rw [mobiusTwisted_foot (D := D) (η := η) (S := S) (ε := ε) (εp := εp) (Dp := Dp) hyD,
    hfoot, S.hC₀val t₀]
  rfl

open scoped Manifold ContDiff Topology in
open Set Filter in
/-- **The far piece**: a non-model level point whose foot is a parked component has its picture in
the left half-plane (so it is never zero and never on the positive real axis). -/
lemma farValue {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    {S : MobiusPacket D η} {ε εp Dp : ℝ} (hε : 0 < ε) (hε19 : ε ≤ 19) (hεp : 0 < εp)
    (hεp19 : εp ≤ 19) {j : Fin S.n} (hj : j ≠ S.i) {y : M} {t₀ : ℝ}
    (hyD : y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z
      (39 / 20))
    (hfoot : Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y = S.L.γ j t₀) :
    (proj2 (mobiusTwisted D η S ε εp Dp y)).re < 0 := by
  have hval := mobiusTwisted_far_proj (D := D) (S := S) (ε := ε) (εp := εp) (Dp := Dp)
    hε hε19 hεp hεp19 hj hyD hfoot
  rw [hval]
  have hre : (proj2 (farPos S.n j) + (Dp : ℂ) * Complex.I + proj2 (Work.Drive.N2.ang t₀)).re
      = -20 + Real.cos (2 * Real.pi * t₀) := by
    rw [Complex.add_re, Complex.add_re, Work.Drive.N2C.proj2_farPos,
      Work.Drive.N2C.re_proj2_ang]
    simp [Complex.mul_re]
  rw [hre]
  linarith [Real.cos_le_one (2 * Real.pi * t₀)]

open scoped Manifold ContDiff Topology in
open Set Filter in
/-- **The uniform sign rows of the two model arcs** (`pushedStarUniform` at the two Möbius arcs):
the pushed arcs keep the strict sign of their second coordinate. -/
lemma mobiusModelSignRows {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (S : MobiusPacket D η) {ε : ℝ} (hε : 0 < ε)
    (hεa : ε ≤ Real.sqrt (S.a' ^ 2 + Work.Drive.N2.packetEta D η)) :
    ∃ εp₀ : ℝ, 0 < εp₀ ∧ ∃ D₀ : ℝ, 0 ≤ D₀ ∧
      ∀ εp : ℝ, 0 < εp → εp ≤ εp₀ → ∀ Dp : ℝ, D₀ ≤ Dp →
        (∀ w ∈ Set.Icc (-2 : ℝ) 2,
          (pushY Dp εp 1 (mobiusAlpha (Work.Drive.N2.packetEta D η) (1 / 20)
            (Work.Drive.N2.packetEta D η) S.a' ε w)) 1 ≠ 0) ∧
        (∀ w ∈ Set.Icc (-2 : ℝ) 2,
          (pushY Dp εp 1 (mobiusBeta (Work.Drive.N2.packetEta D η) (1 / 20)
            (Work.Drive.N2.packetEta D η) S.a' ε w)) 1 ≠ 0) := by
  set ηs : ℝ := Work.Drive.N2.packetEta D η with hηsdef
  set δ : ℝ := 1 / 20 with hδdef
  have hs : 0 < ηs := by rw [hηsdef]; exact Work.Drive.N2.packetEta_pos D hη
  have hδ : 0 < δ := by rw [hδdef]; norm_num
  have hδ₁ : δ < 1 / 10 := by rw [hδdef]; norm_num
  have hδ₂ : δ < 1 / 2 := by rw [hδdef]; norm_num
  have hηs₁ : ηs < 3 / 800 := by
    rw [hηsdef]; exact packetEta_lt_three_eightieth D hsmall
  have hηs₂ : ηs < 1 / 10 := by linarith
  have hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ (3 : ℝ) :=
    fun x => le_trans (Work.N2Lead.absDerivSmoothTransitionLeTwo x) (by norm_num)
  have hsmall' : 4 * (3 : ℝ) * ηs ≤ δ := by rw [hδdef]; linarith
  obtain ⟨harc1, harc2⟩ := mobius_upperArcs (η := ηs) (δ := δ) (s := ηs) (a' := S.a') (ε := ε)
    (C₀ := 3) hδ hδ₁ hs hηs₂ hs le_rfl hC₀ hsmall' S.ha'pos hε hεa
  have hαsm : ContDiff ℝ 1 (mobiusAlpha ηs δ ηs S.a' ε) :=
    mobiusAlpha_contDiff (η := ηs) (δ := δ) (s := ηs) (a := S.a') (ε := ε) hδ hδ₂ hs
  have hβsm : ContDiff ℝ 1 (mobiusBeta ηs δ ηs S.a' ε) :=
    mobiusBeta_contDiff (η := ηs) (δ := δ) (s := ηs) (a := S.a') (ε := ε) hδ hδ₂ hs
  obtain ⟨εpα, hεpα, Dα, hDα, hαrow⟩ :=
    Work.Drive.N2C.pushedStarUniform (g := mobiusAlpha ηs δ ηs S.a' ε) (εs := (1 : ℝ))
      (a := (-2 : ℝ)) (b := 2) hαsm (Or.inl rfl) (by norm_num)
      (fun w hw => (harc2 w hw).1) (fun w hw => by simpa using (harc1 w hw).1)
  obtain ⟨εpβ, hεpβ, Dβ, hDβ, hβrow⟩ :=
    Work.Drive.N2C.pushedStarUniform (g := mobiusBeta ηs δ ηs S.a' ε) (εs := (-1 : ℝ))
      (a := (-2 : ℝ)) (b := 2) hβsm (Or.inr rfl) (by norm_num)
      (fun w hw => (harc2 w hw).2) (fun w hw => by
        have h := (harc1 w hw).2
        simp only [neg_one_mul]
        linarith)
  refine ⟨min εpα εpβ, lt_min hεpα hεpβ, max Dα Dβ, le_max_of_le_left hDα, ?_⟩
  intro εp hεp hεple Dp hDp
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · have h1 := (hαrow εp hεp (le_trans hεple (min_le_left _ _)) Dp
      (le_trans (le_max_left _ _) hDp) w hw).1
    rw [one_mul] at h1
    exact ne_of_gt h1
  · intro h0
    have h1 := (hβrow εp hεp (le_trans hεple (min_le_right _ _)) Dp
      (le_trans (le_max_right _ _) hDp) w hw).1
    rw [h0, mul_zero] at h1
    exact absurd h1 (lt_irrefl 0)

open scoped Manifold ContDiff Topology in
open Set Filter in
/-- **Clause 1 in the model region**: the picture of a model-region level point has non-zero
imaginary part (it is a pushed model arc). -/
lemma modelProjImNe {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    {S : MobiusPacket D η} {ε εp Dp : ℝ} {y : M}
    (hy : f y = f p + 3 * η / 2)
    (hreg : y ∈ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z
      (39 / 20))
    (hαrow : ∀ w ∈ Set.Icc (-2 : ℝ) 2,
      (pushY Dp εp 1 (mobiusAlpha (Work.Drive.N2.packetEta D η) (1 / 20)
        (Work.Drive.N2.packetEta D η) S.a' ε w)) 1 ≠ 0)
    (hβrow : ∀ w ∈ Set.Icc (-2 : ℝ) 2,
      (pushY Dp εp 1 (mobiusBeta (Work.Drive.N2.packetEta D η) (1 / 20)
        (Work.Drive.N2.packetEta D η) S.a' ε w)) 1 ≠ 0) :
    (proj2 (mobiusTwisted D η S ε εp Dp y)).im ≠ 0 := by
  obtain ⟨hre, him⟩ := model_zeta (D := D) S hy hreg
  have hwmem : ((S.Z y) ^ 2).im ∈ Set.Icc (-2 : ℝ) 2 := by
    have h := abs_lt.mp him
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  rcases model_value (D := D) S (ε := ε) (εp := εp) (Dp := Dp) hy hreg with h | h
  · -- the `α` branch (sign `-1`, positive second coordinate)
    have hr := hαrow _ hwmem
    intro h0
    have h1 : (proj2 (mobiusTwisted D η S ε εp Dp y)).im = 0 := h0
    rw [h] at h1
    exact hr (by simpa using h1)
  · have hr := hβrow _ hwmem
    intro h0
    have h1 : (proj2 (mobiusTwisted D η S ε εp Dp y)).im = 0 := h0
    rw [h] at h1
    exact hr (by simpa using h1)

set_option maxHeartbeats 1600000 in
open scoped Manifold ContDiff Topology in
open Set Filter in
/-- **The marked foot piece**: a non-model level point whose foot is on the marked component has its
picture equal to the polar picture at the angle `Θ t₀`, and the tangent line of the picture at that
point never passes through the origin, provided the polar picture has non-zero angular rate there.

The proof is the chain rule of `mfrParkPiece`, with the polar angle `Θ t₀` playing the role of the
parameter: the foot's velocity is a non-zero multiple of the level-curve velocity (row `L.ker` of the
packet), and the picture along the level curve is `polarPic ∘ Θ` by `hC₀val`. -/
theorem markedFootRate {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (S : MobiusPacket D η) {ε εp Dp : ℝ} (hεp : 0 < εp) (hDp : 0 ≤ Dp)
    {y : M} {t₀ : ℝ} (hy : f y = f p + 3 * η / 2)
    (hyD : y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z
      (39 / 20))
    (hfoot : Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y = S.L.γ S.i t₀)
    (hcurve : (star (polarPic S.r Dp εp ε (S.Θ t₀))
      * deriv (polarPic S.r Dp εp ε) (S.Θ t₀)).im ≠ 0) :
    proj2 (mobiusTwisted D η S ε εp Dp y) = polarPic S.r Dp εp ε (S.Θ t₀) ∧
      ∀ v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) y,
        mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ ℝ) f y v = 0 → v ≠ 0 →
        ¬ (∃ t : ℝ, mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ ℂ)
            (fun z : M => proj2 (mobiusTwisted D η S ε εp Dp z)) y v
          = t • proj2 (mobiusTwisted D η S ε εp Dp y)) := by
  classical
  have hval : proj2 (mobiusTwisted D η S ε εp Dp y) = polarPic S.r Dp εp ε (S.Θ t₀) :=
    markedFootValue D hyD hfoot
  have hnr : ¬ ∃ t : ℝ, deriv (polarPic S.r Dp εp ε) (S.Θ t₀)
      = t • polarPic S.r Dp εp ε (S.Θ t₀) := by
    refine Work.Drive.N2Lead.not_realMultiple_of_det
      (a := polarPic S.r Dp εp ε (S.Θ t₀))
      (b := deriv (polarPic S.r Dp εp ε) (S.Θ t₀)) ?_
    rw [← Work.Drive.N2C.mfr_star_mul_im_eq]
    exact hcurve
  refine ⟨hval, ?_⟩
  intro v hv hvne
  obtain ⟨hfootsm, -, hfootimm⟩ :=
    Work.Drive.N2.footMap_rows_noLaw (f := f) (Φ := D.Φ) (hf := hf) (hΦsm := D.hΦsm)
      (hΦ0 := D.hΦ0) (hΦcomp := D.hΦcomp) (a := f p - 3 * η / 2)
  set foot : M → M := Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) with hfootdef
  set Wp : M → Work.Drive.N2Lead.E3 := fun z : M =>
    pushY Dp εp 1 (twistX ε (-1) (S.C₀ z)) with hWpdef
  have hWpsm : ∀ z : M, ContMDiffAt (𝓡 2) (𝓡 3) tpTop Wp z := fun z =>
    mfr_contMDiffAt_pushed (D := D) (η := η) (S := S) (ε := ε) (εp := εp) (Dp := Dp) z
  have hmw : (fun z : M => proj2 (mobiusTwisted D η S ε εp Dp z))
      =ᶠ[𝓝 y] (fun z : M => proj2 (Wp (foot z))) := by
    filter_upwards [Work.Drive.N2C.mobiusTwisted_eventually_foot (D := D) (η := η) (S := S)
      (ε := ε) (εp := εp) (Dp := Dp) hη hsmall hf (y := y) hy hyD] with z hz
    simp only [hz, hfootdef, hWpdef]
  have hmf1 : mfderiv (𝓡 2) 𝓘(ℝ, ℂ)
        (fun z : M => proj2 (mobiusTwisted D η S ε εp Dp z)) y v
      = mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (Wp (foot z))) y v :=
    DFunLike.congr_fun hmw.mfderiv_eq_v433 v
  have hchain : mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (Wp (foot z))) y v
      = mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (Wp z)) (foot y)
          (mfderiv (𝓡 2) (𝓡 2) foot y v) :=
    mfr_mfderiv_proj2_comp_foot (A := Wp) hfootsm.contMDiffAt hWpsm v
  have hyband : f y ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) := by
    refine ⟨?_, ?_⟩ <;> rw [hy] <;> linarith
  set region : Set M :=
    Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z (39 / 20)
    with hregiondef
  have hregionopen : IsOpen region :=
    Work.Drive.N2.isOpen_saddleRegion
      (isOpen_modelBall_mobius (D.φ D.j) (D.ρ D.j)) S.hZsm
  have hycl_or_fr : y ∈ frontier region ∨ y ∉ closure region := by
    by_cases hfr : y ∈ frontier region
    · exact Or.inl hfr
    · refine Or.inr fun hcl => hfr ?_
      rw [frontier_eq_closure_inter_closure]
      refine ⟨hcl, ?_⟩
      rw [IsClosed.closure_eq (isClosed_compl_iff.mpr hregionopen)]
      exact hyD
  have hevland : (fun z : M => f (foot z)) =ᶠ[𝓝 y] (fun _ : M => f p - 3 * η / 2) := by
    rcases hycl_or_fr with hfr | hcl
    · exact S.hlandFr y hfr hyband
    · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hcl,
        hf.continuous.continuousAt (isOpen_Ioo.mem_nhds hyband)] with z hzcl hzf
      exact S.hfootval z (fun hzD => hzcl (subset_closure hzD)) hzf
  have hkerfoot : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (foot y) (mfderiv (𝓡 2) (𝓡 2) foot y v) = 0 := by
    have h0 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => f (foot z)) y v = 0 := by
      rw [hevland.mfderiv_eq_v433, mfderiv_const]
      rfl
    rw [mfr_mfderiv_f_comp_foot hfootsm.contMDiffAt hf.contMDiffAt v] at h0
    exact h0
  obtain ⟨s₀, hs₀⟩ :=
    S.L.ker S.i t₀ (mfderiv (𝓡 2) (𝓡 2) foot y v) (by rw [← hfoot]; exact hkerfoot)
  have hs₀ne : s₀ ≠ 0 := by
    intro h0
    refine hvne (hfootimm y v hv ?_)
    exact hs₀.symm.trans ((congrArg
      (fun c : ℝ => mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (S.L.γ S.i) t₀ c) h0).trans
        (map_zero (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (S.L.γ S.i) t₀)))
  have hlevel : mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (Wp z)) (S.L.γ S.i t₀)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (S.L.γ S.i) t₀ s₀)
      = deriv (fun u : ℝ => proj2 (Wp (S.L.γ S.i u))) t₀ * (s₀ : ℂ) :=
    mfr_mfderiv_levelCurve_eq_deriv (L := S.L) (W := Wp) (fun z _ => hWpsm z) S.i t₀ s₀
  have hcurve_eq : (fun u : ℝ => proj2 (Wp (S.L.γ S.i u)))
      = fun u : ℝ => polarPic S.r Dp εp ε (S.Θ u) := by
    funext u
    simp only [hWpdef]
    rw [S.hC₀val u]
    rfl
  have hderivcomp : deriv (fun u : ℝ => polarPic S.r Dp εp ε (S.Θ u)) t₀
      = deriv (polarPic S.r Dp εp ε) (S.Θ t₀) * deriv S.Θ t₀ := by
    have h2 : DifferentiableAt ℝ (polarPic S.r Dp εp ε) (S.Θ t₀) :=
      ((contDiff_polarPic S.hr Dp εp ε).differentiable (by simp)).differentiableAt
    have h1 : DifferentiableAt ℝ S.Θ t₀ := (S.hΘ.differentiable (by simp)).differentiableAt
    have hcomp : fderiv ℝ (fun u : ℝ => polarPic S.r Dp εp ε (S.Θ u)) t₀
        = (fderiv ℝ (polarPic S.r Dp εp ε) (S.Θ t₀)).comp (fderiv ℝ S.Θ t₀) := by
      simpa only [Function.comp_def] using fderiv_comp (x := t₀) h2 h1
    calc deriv (fun u : ℝ => polarPic S.r Dp εp ε (S.Θ u)) t₀
        = (fderiv ℝ (fun u : ℝ => polarPic S.r Dp εp ε (S.Θ u)) t₀) 1 :=
          fderiv_apply_one_eq_deriv.symm
      _ = ((fderiv ℝ (polarPic S.r Dp εp ε) (S.Θ t₀)).comp (fderiv ℝ S.Θ t₀)) 1 := by
          rw [hcomp]
      _ = (fderiv ℝ (polarPic S.r Dp εp ε) (S.Θ t₀)) ((fderiv ℝ S.Θ t₀) 1) := rfl
      _ = (fderiv ℝ (polarPic S.r Dp εp ε) (S.Θ t₀)) (deriv S.Θ t₀) := by
          rw [fderiv_apply_one_eq_deriv]
      _ = (fderiv ℝ (polarPic S.r Dp εp ε) (S.Θ t₀)) ((deriv S.Θ t₀) • (1 : ℝ)) := by
          rw [smul_eq_mul, mul_one]
      _ = (deriv S.Θ t₀) • ((fderiv ℝ (polarPic S.r Dp εp ε) (S.Θ t₀)) 1) := by
          rw [map_smul]
      _ = (deriv S.Θ t₀) • deriv (polarPic S.r Dp εp ε) (S.Θ t₀) := by
          rw [fderiv_apply_one_eq_deriv]
      _ = deriv (polarPic S.r Dp εp ε) (S.Θ t₀) * deriv S.Θ t₀ := by
          rw [Complex.real_smul]; ring
  have hGder : mfderiv (𝓡 2) 𝓘(ℝ, ℂ)
        (fun z : M => proj2 (mobiusTwisted D η S ε εp Dp z)) y v
      = deriv (polarPic S.r Dp εp ε) (S.Θ t₀) * (((deriv S.Θ t₀ * s₀ : ℝ)) : ℂ) := by
    rw [hmf1, hchain]
    have hfoot' : foot y = S.L.γ S.i t₀ := hfoot
    have hA : mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (Wp z)) (foot y)
          (mfderiv (𝓡 2) (𝓡 2) foot y v)
        = mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (Wp z))
          (S.L.γ S.i t₀) (mfderiv (𝓡 2) (𝓡 2) foot y v) := by rw [hfoot']
    have hB : mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (Wp z))
          (S.L.γ S.i t₀) (mfderiv (𝓡 2) (𝓡 2) foot y v)
        = mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (Wp z))
          (S.L.γ S.i t₀) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (S.L.γ S.i) t₀ s₀) :=
      congrArg (fun w => mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (Wp z))
        (S.L.γ S.i t₀) w) hs₀.symm
    rw [hA, hB, hlevel, hcurve_eq, hderivcomp]
    rw [Complex.ofReal_mul, mul_assoc]
  rintro ⟨t, ht⟩
  have hcne : deriv S.Θ t₀ * s₀ ≠ 0 := mul_ne_zero (S.hΘderiv t₀) hs₀ne
  rw [hGder, hval, Complex.real_smul] at ht
  have hd : deriv (polarPic S.r Dp εp ε) (S.Θ t₀)
      = (t / (deriv S.Θ t₀ * s₀)) • polarPic S.r Dp εp ε (S.Θ t₀) := by
    have hc' : (((deriv S.Θ t₀ * s₀ : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hcne
    have h1 : deriv (polarPic S.r Dp εp ε) (S.Θ t₀)
        = (((t : ℂ) * polarPic S.r Dp εp ε (S.Θ t₀))
            / (((deriv S.Θ t₀ * s₀ : ℝ)) : ℂ)) := by
      rw [eq_div_iff hc']
      exact ht
    rw [h1, Complex.real_smul]
    have h2 : (((t : ℂ) * polarPic S.r Dp εp ε (S.Θ t₀))
          / (((deriv S.Θ t₀ * s₀ : ℝ)) : ℂ))
        = ((t / (deriv S.Θ t₀ * s₀) : ℝ) : ℂ) * polarPic S.r Dp εp ε (S.Θ t₀) := by
      rw [Complex.ofReal_div]
      field_simp
    rw [h2]
  exact hnr ⟨t / (deriv S.Θ t₀ * s₀), hd⟩

open scoped Manifold ContDiff Topology in
open Set Filter in
/-- The integer-shift law of the level-curve parametrisation (from `LevelCurves.per`). -/
lemma levelCurve_gamma_add_int {f : M → ℝ} {u : ℝ} {n : ℕ}
    (L : Work.Drive.N2C.LevelCurves f u n) (i : Fin n) (x : ℝ) (k : ℤ) :
    L.γ i (x + k) = L.γ i x := by
  have hnat : ∀ (m : ℕ) (z : ℝ), L.γ i (z + (m : ℝ)) = L.γ i z := by
    intro m
    refine Nat.rec ?_ ?_ m
    · intro z
      simp
    · intro p ih z
      have hstep : (z + ((p + 1 : ℕ) : ℝ)) = (z + (p : ℝ)) + 1 := by push_cast; ring
      rw [hstep, L.per]
      exact ih z
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · rw [hm]
    simpa using hnat m x
  · rw [hm]
    have h := hnat m (x - (m : ℝ))
    have h1 : x - (m : ℝ) + (m : ℝ) = x := by ring
    rw [h1] at h
    have h2 : x + (-(m : ℤ) : ℤ) = x - (m : ℝ) := by push_cast; ring
    rw [h2]
    exact h.symm

open scoped Manifold ContDiff Topology in
open Set Filter in
/-- **The dichotomy of a marked foot**: a non-model level point whose foot lies on the marked
component is either in the bridge zone of the polar angle, or its foot is one of the two arc points
with `|w| ∈ [39/20, 99/50]`. -/
theorem markedFootDichotomy {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (S : MobiusPacket D η) (hshape : Work.Drive.N2C.MobiusShape D η S)
    {y : M} {t : ℝ} (hyb : f y ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η))
    (hyD : y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z
      (39 / 20))
    (hfoot : Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y = S.L.γ S.i t) :
    (∃ k : ℤ, |S.Θ t - (k : ℝ) * Real.pi|
        ≤ Work.Drive.N2Lead.mobiusPhiE (Work.Drive.N2.packetEta D η) (99 / 50)) ∨
      (∃ w : ℝ, Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y = S.L.γ S.i (hshape.tauU w) ∧
        39 / 20 ≤ |w| ∧ |w| < 99 / 50) ∨
      (∃ w : ℝ, Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y = S.L.γ S.i (hshape.tauL w) ∧
        39 / 20 ≤ |w| ∧ |w| < 99 / 50) := by
  classical
  set ηs : ℝ := Work.Drive.N2.packetEta D η with hηsdef
  have hηs : 0 < ηs := by rw [hηsdef]; exact Work.Drive.N2.packetEta_pos D hη
  have hηs₁ : ηs < 3 / 800 := by
    rw [hηsdef]; exact packetEta_lt_three_eightieth D hsmall
  have hηs_abs : |ηs| ≤ 1 := by rw [abs_of_pos hηs]; linarith
  have hm1 : (1 : ℝ) < 99 / 50 := by norm_num
  -- the second lift of `arcRangeOrBridgeZone`
  have hΘU : ∀ w ∈ Set.Icc (-(99 / 50 : ℝ)) (99 / 50), S.Θ (hshape.tauU w)
      = Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs) := fun w hw => hshape.hThetau w hw
  have hΘL : ∀ w ∈ Set.Icc (-(99 / 50 : ℝ)) (99 / 50),
      S.Θ ((fun u : ℝ => hshape.tauL (-u) - 1) w) = -(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs) := by
    intro w hw
    have hw' : -w ∈ Set.Icc (-(99 / 50 : ℝ)) (99 / 50) := ⟨by linarith [hw.2], by linarith [hw.1]⟩
    have h := hshape.hThetal (-w) hw'
    have hper := theta_add_int S.hΘper (-1 : ℤ) (hshape.tauL (-w))
    have hx : hshape.tauL (-w) + ((-1 : ℤ) : ℝ) = hshape.tauL (-w) - 1 := by push_cast; ring
    rw [hx] at hper
    rw [hper, h]
    have h2 : Real.arctan ((-w) / Work.Drive.N2.packetEta D η) = -Real.arctan (w / ηs) := by
      rw [← hηsdef, neg_div, Real.arctan_neg]
    rw [h2]
    push_cast
    ring
  rcases arcRangeOrBridgeZone hηs hm1 S.hΘmono S.hΘper hΘU hΘL t with hA | hL | hB
  · obtain ⟨w, hw, k, hk⟩ := hA
    have hwIcc : w ∈ Set.Icc (-(99 / 50 : ℝ)) (99 / 50) :=
      ⟨le_of_lt hw.1, le_of_lt hw.2⟩
    have hlt : |w| < 99 / 50 := abs_lt.mpr hw
    -- the foot is the upper arc point at `w`
    have hfoot' : Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y = S.L.γ S.i (hshape.tauU w) := by
      rw [hfoot, hk, levelCurve_gamma_add_int S.L S.i (hshape.tauU w) k]
    -- the pin value at the foot is `1`
    have hball : ‖arcZ ηs w‖ < 8 :=
      Work.Drive.N2C.norm_arcZ_lt_eight hηs_abs (le_trans (le_of_lt hlt) (by norm_num))
    have hZ : S.Z (S.L.γ S.i (hshape.tauU w)) = arcZ ηs w := hshape.hZu w hwIcc
    have hsrc : S.L.γ S.i (hshape.tauU w) ∈ (D.φ D.j).source := by
      rw [hshape.hZuPt w hwIcc]
      exact arcUpPt_mem_source D hball S.hlam0
    have hpin : pinTheta D S.Z (99 / 50) (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y) = 1 := by
      rw [hfoot']
      rw [pinTheta_eq_one_iff D (by norm_num) hsrc]
      refine ⟨?_, ?_⟩
      · rw [hZ, arcZ_sq_im]
        exact le_of_lt hlt
      · rw [hZ, norm_arcZ_sq]
        have h1 : ηs ^ 2 + w ^ 2 ≤ 16 := by
          have h2 : w ^ 2 < (99 / 50 : ℝ) ^ 2 := by
            nlinarith [abs_nonneg w, abs_lt.mp hlt]
          nlinarith [hηs₁, sq_nonneg ηs]
        calc Real.sqrt (ηs ^ 2 + w ^ 2) ≤ Real.sqrt 16 := Real.sqrt_le_sqrt h1
          _ = 4 := by norm_num
    have hc₀ := S.hbig y hyD hyb hpin
    rw [hfoot', hZ, arcZ_sq_im] at hc₀
    exact Or.inr (Or.inl ⟨w, hfoot', hc₀, hlt⟩)
  · obtain ⟨w, hw, k, hk⟩ := hL
    have hwIcc : w ∈ Set.Icc (-(99 / 50 : ℝ)) (99 / 50) :=
      ⟨le_of_lt hw.1, le_of_lt hw.2⟩
    have hlt : |w| < 99 / 50 := abs_lt.mpr hw
    -- the foot is the lower arc point at `-w`
    have hfoot' : Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y
        = S.L.γ S.i (hshape.tauL (-w)) := by
      rw [hfoot, hk]
      show S.L.γ S.i ((fun u : ℝ => hshape.tauL (-u) - 1) w + (k : ℝ)) = _
      rw [show ((fun u : ℝ => hshape.tauL (-u) - 1) w + (k : ℝ))
          = hshape.tauL (-w) + ((k : ℤ) + (-1) : ℤ) by push_cast; ring]
      exact levelCurve_gamma_add_int S.L S.i (hshape.tauL (-w)) ((k : ℤ) + (-1))
    have hlt' : |(-w)| < 99 / 50 := by rw [abs_neg]; exact hlt
    have hball : ‖arcZ ηs (-w)‖ < 8 :=
      Work.Drive.N2C.norm_arcZ_lt_eight hηs_abs (le_trans (le_of_lt hlt') (by norm_num))
    have hZ : S.Z (S.L.γ S.i (hshape.tauL (-w))) = -arcZ ηs (-w) := hshape.hZd (-w) ⟨by linarith [hw.2], by linarith [hw.1]⟩
    have hsrc : S.L.γ S.i (hshape.tauL (-w)) ∈ (D.φ D.j).source := by
      rw [hshape.hZdPt (-w) ⟨by linarith [hw.2], by linarith [hw.1]⟩]
      exact arcDnPt_mem_source D hball S.hlam0pos S.hlam0
    have hpin : pinTheta D S.Z (99 / 50) (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y) = 1 := by
      rw [hfoot']
      rw [pinTheta_eq_one_iff D (by norm_num) hsrc]
      refine ⟨?_, ?_⟩
      · rw [hZ, neg_sq, arcZ_sq_im]
        exact le_of_lt hlt'
      · rw [hZ, norm_neg, norm_arcZ_sq]
        have h1 : ηs ^ 2 + (-w) ^ 2 ≤ 16 := by
          have h2 : (-w) ^ 2 < (99 / 50 : ℝ) ^ 2 := by
            nlinarith [abs_nonneg w, abs_lt.mp hlt]
          nlinarith [hηs₁, sq_nonneg ηs]
        calc Real.sqrt (ηs ^ 2 + (-w) ^ 2) ≤ Real.sqrt 16 := Real.sqrt_le_sqrt h1
          _ = 4 := by norm_num
    have hc₀ := S.hbig y hyD hyb hpin
    rw [hfoot', hZ, neg_sq, arcZ_sq_im] at hc₀
    exact Or.inr (Or.inr ⟨-w, hfoot', by simpa using hc₀, by simpa using hlt⟩)
  · exact Or.inl hB

open scoped Manifold ContDiff Topology in
open Set Filter in
/-- The real part of the polar picture is `r θ · cos θ`. -/
lemma polarPic_re {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p} {η : ℝ}
    (S : MobiusPacket D η) (ε εp Dp : ℝ) (θ : ℝ) :
    (polarPic S.r Dp εp ε θ).re = S.r θ * Real.cos θ := by
  rw [show polarPic S.r Dp εp ε = Work.Drive.N2C.parkPicture S ε εp Dp from rfl]
  exact Work.Drive.N2C.park_picture_re S ε εp Dp θ

open scoped Manifold ContDiff Topology in
open Set Filter in
/-- The imaginary part of the polar picture vanishes only if the polar point is on one of the two
axes. -/
lemma polarPic_im_eq_zero {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p} {η : ℝ}
    (S : MobiusPacket D η) {ε εp Dp : ℝ} (hε : 0 < ε) (hεp : 0 < εp) (hDp : 0 ≤ Dp)
    {θ : ℝ} (h : (polarPic S.r Dp εp ε θ).im = 0) :
    S.r θ * Real.sin θ = 0 ∨ S.r θ * Real.cos θ = 0 := by
  rw [show polarPic S.r Dp εp ε = Work.Drive.N2C.parkPicture S ε εp Dp from rfl] at h
  exact Work.Drive.N2C.park_picture_im_eq_zero S hε hεp hDp h

open scoped Manifold ContDiff Topology in
open Set Filter in
/-- **The marked foot, read out of the trichotomy**: a non-model level point with a marked foot has
a canonical foot parameter `t₀` whose polar angle is off the imaginary axis, together with the
angular-rate row of the polar picture there. -/
theorem markedFootRows {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (S : MobiusPacket D η) (hshape : Work.Drive.N2C.MobiusShape D η S)
    {ε εp Dp : ℝ} (hε : 0 < ε) (hεp : 0 < εp) (hDp : 0 ≤ Dp)
    (hεlarge : ε ≤ 3 / 4) (hεpsmall : εp ≤ 3 / 4)
    (hεsmall : ∀ φ ∈ Set.Icc
      (-(Work.Drive.N2Lead.mobiusPhiE (Work.Drive.N2.packetEta D η) (99 / 50)))
      (Work.Drive.N2Lead.mobiusPhiE (Work.Drive.N2.packetEta D η) (99 / 50)),
      ε ≤ S.r φ * Real.cos φ)
    (harcZ : ∀ w : ℝ, 39 / 20 ≤ |w| →
      (3 / 4 : ℝ) ≤ |(arcZ (Work.Drive.N2.packetEta D η) w).re| ∧
      (3 / 4 : ℝ) ≤ (arcZ (Work.Drive.N2.packetEta D η) w).im)
    {y : M} {t : ℝ} (hyb : f y ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η))
    (hyD : y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z
      (39 / 20))
    (hfoot : Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y = S.L.γ S.i t) :
    ∃ t₀ : ℝ, Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y = S.L.γ S.i t₀ ∧
      Real.cos (S.Θ t₀) ≠ 0 ∧
      (star (polarPic S.r Dp εp ε (S.Θ t₀))
        * deriv (polarPic S.r Dp εp ε) (S.Θ t₀)).im ≠ 0 := by
  classical
  set ηs : ℝ := Work.Drive.N2.packetEta D η with hηsdef
  have hηs' : 0 < ηs := by rw [hηsdef]; exact Work.Drive.N2.packetEta_pos D hη
  have hm1 : (1 : ℝ) < 99 / 50 := by norm_num
  have hφElt : Work.Drive.N2Lead.mobiusPhiE ηs (99 / 50) < Real.pi / 2 :=
    (leadProfile_phiE hηs' (by norm_num)).2.2
  have hlo : ∀ φ ∈ Set.Icc (0 : ℝ) (Work.Drive.N2Lead.mobiusPhiE ηs (99 / 50)),
      Real.sqrt (ηs ^ 2 + (99 / 50) ^ 2) ≤ S.r φ ^ 2 := by
    intro φ hφ
    have habs : |φ - ((0 : ℤ) : ℝ) * Real.pi| ≤ Work.Drive.N2Lead.mobiusPhiE ηs (99 / 50) := by
      rw [Int.cast_zero, zero_mul, sub_zero, abs_of_nonneg hφ.1]
      exact hφ.2
    exact hshape.hlo φ 0 habs
  rcases markedFootDichotomy (D := D) hη hsmall S hshape hyb hyD hfoot with
    hB | ⟨w, hfootU, hc₀, hlt⟩ | ⟨w, hfootL, hc₀, hlt⟩
  · -- ### the bridge zone
    refine ⟨t, hfoot, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := hB
      intro hcos
      have hmem : S.Θ t - (k : ℝ) * Real.pi ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        obtain ⟨h1, h2⟩ := abs_le.mp hk
        exact ⟨by linarith, by linarith⟩
      have hcosy : Real.cos (S.Θ t - (k : ℝ) * Real.pi) ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo hmem)
      have hrel : Real.cos (S.Θ t)
          = (-1 : ℝ) ^ k * Real.cos (S.Θ t - (k : ℝ) * Real.pi) := by
        have hx : S.Θ t = (S.Θ t - (k : ℝ) * Real.pi) + (k : ℝ) * Real.pi := by ring
        rw [hx, Real.cos_add, Real.cos_int_mul_pi, Real.sin_int_mul_pi]
        ring
      rw [hrel] at hcos
      exact hcosy (mul_eq_zero.mp hcos |>.resolve_left
        (zpow_ne_zero k (by norm_num : (-1 : ℝ) ≠ 0)))
    · exact (polarRowZone (ηs := ηs) (m := 99 / 50)
        (φE := Work.Drive.N2Lead.mobiusPhiE ηs (99 / 50)) hηs' rfl hε hεp hDp
        (S.hr.of_le (by simp)) S.hrpos hshape.hrev hshape.hrpi hlo hshape.hrdec hεsmall
        (S.Θ t) hB).2
  · -- ### the upper arc
    have hwIoo : w ∈ Set.Ioo (-(99 / 50 : ℝ)) (99 / 50) := abs_lt.mp hlt
    have hwIcc : w ∈ Set.Icc (-(99 / 50 : ℝ)) (99 / 50) :=
      ⟨le_of_lt hwIoo.1, le_of_lt hwIoo.2⟩
    refine ⟨hshape.tauU w, hfootU, ?_, ?_⟩
    · intro hcos
      have hpolar := hshape.hpolarU w hwIcc
      have hre : (arcZ ηs w).re = 0 := by
        rw [← hpolar, Work.Drive.N2C.park_polar_re, hcos, mul_zero]
      have hw0 : w = 0 := by
        have h := arcZ_sq_im ηs w
        rw [pow_two, Complex.mul_im, hre] at h
        simp at h
        linarith
      rw [hw0, abs_zero] at hc₀
      linarith
    · have hrig := harcZ w hc₀
      have him : εp ≤ (arcZ ηs w).im := le_trans hεpsmall hrig.2
      have hrigid : ε ≤ |(arcZ ηs w).re| := le_trans hεlarge hrig.1
      have hcurve := pinCurveRowUp hηs' hε hεp hDp w hrigid him
      exact arcToPolarRowUp (ηs := ηs) (m := 99 / 50) hηs' (by norm_num) hε hεp hDp S.hr S.hΘ
        hshape.hThetau hshape.hpolarU hwIoo (hshape.hτu w hwIoo) hcurve
  · -- ### the lower arc
    have hwIoo : w ∈ Set.Ioo (-(99 / 50 : ℝ)) (99 / 50) := abs_lt.mp hlt
    have hwIcc : w ∈ Set.Icc (-(99 / 50 : ℝ)) (99 / 50) :=
      ⟨le_of_lt hwIoo.1, le_of_lt hwIoo.2⟩
    refine ⟨hshape.tauL w, hfootL, ?_, ?_⟩
    · intro hcos
      have hpolar := hshape.hpolarL w hwIcc
      have hre : (arcZ ηs w).re = 0 := by
        have h1 : (star (arcZ ηs w)).re = 0 := by
          rw [← hpolar, Work.Drive.N2C.park_polar_re, hcos, mul_zero]
        simpa using h1
      have hw0 : w = 0 := by
        have h := arcZ_sq_im ηs w
        rw [pow_two, Complex.mul_im, hre] at h
        simp at h
        linarith
      rw [hw0, abs_zero] at hc₀
      linarith
    · have hrig := harcZ w hc₀
      have him : εp ≤ (arcZ ηs w).im := le_trans hεpsmall hrig.2
      have hrigid : ε ≤ |(arcZ ηs w).re| := le_trans hεlarge hrig.1
      have hcurve := pinCurveRowDn hηs' hε hεp hDp w hrigid him
      exact arcToPolarRowDn (ηs := ηs) (m := 99 / 50) hηs' (by norm_num) hε hεp hDp S.hr S.hΘ
        hshape.hThetal hshape.hpolarL hwIoo (hshape.hτl w hwIoo) hcurve

open scoped Manifold ContDiff Topology in
open Set Filter in
/-- **The marked foot of a point with a positive real picture**: its polar angle is a multiple of
`2π`. -/
theorem markedFootAngleTwoPi {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (S : MobiusPacket D η) {ε εp Dp : ℝ} (hε : 0 < ε) (hεp : 0 < εp) (hDp : 0 ≤ Dp)
    {y : M} {t : ℝ}
    (hyD : y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z
      (39 / 20))
    (hpos : ∃ s : ℝ, 0 < s ∧
      proj2 (mobiusTwisted D η S ε εp Dp y) = ((s : ℝ) : ℂ))
    (hfoot : Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y = S.L.γ S.i t) :
    ∃ k : ℤ, S.Θ t = (k : ℝ) * (2 * Real.pi) := by
  obtain ⟨s, hs, hsv⟩ := hpos
  have hval := markedFootValue (D := D) (η := η) (S := S) (ε := ε) (εp := εp) (Dp := Dp) hyD hfoot
  have him : (polarPic S.r Dp εp ε (S.Θ t)).im = 0 := by rw [← hval, hsv]; simp
  have hre : (polarPic S.r Dp εp ε (S.Θ t)).re = s := by rw [← hval, hsv]; simp
  have him0 := polarPic_im_eq_zero (S := S) (ε := ε) (εp := εp) (Dp := Dp) hε hεp hDp him
  have hcos : S.r (S.Θ t) * Real.cos (S.Θ t) = s := by
    rw [← polarPic_re (S := S) (ε := ε) (εp := εp) (Dp := Dp) (θ := S.Θ t), hre]
  have hcospos : 0 < S.r (S.Θ t) * Real.cos (S.Θ t) := by rw [hcos]; exact hs
  have hsin : Real.sin (S.Θ t) = 0 := by
    rcases him0 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (ne_of_gt (S.hrpos _))
      · exact h'
    · rw [h] at hcospos
      exact absurd hcospos (lt_irrefl 0)
  have hcpos : 0 < Real.cos (S.Θ t) := by
    rcases mul_pos_iff.mp hcospos with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exact absurd h1 (not_lt.mpr (le_of_lt (S.hrpos _)))
  have hc1 : Real.cos (S.Θ t) = 1 := by
    have h : Real.cos (S.Θ t) ^ 2 = 1 := by
      have := Real.cos_sq_add_sin_sq (S.Θ t)
      rw [hsin] at this
      nlinarith
    nlinarith [hcpos]
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp hc1
  exact ⟨n, hn.symm⟩

end Helpers

theorem mobiusUpperCoreMarked {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (hsep : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η < 2 * D.ηd)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (S : Work.Drive.N2Lead.MobiusPacket D η) (hshape : Work.Drive.N2C.MobiusShape D η S) :
    ∃ (ε εp Dp : ℝ), 0 < ε ∧ ε ≤ 1 ∧ 0 < εp ∧ εp ≤ 1 ∧ 0 ≤ Dp ∧
      (∀ y : M, f y = f p + 3 * η / 2 →
        Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) ≠ 0) ∧
      (∀ (y : M), f y = f p + 3 * η / 2 →
        ‖Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)‖ ≤ Dp + 5 →
        ∀ v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) y,
        mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ) f y v = 0 →
        v ≠ 0 →
        ¬ (∃ t : ℝ, mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℂ)
            (fun z : M => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z)) y v
          = t • Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y))) ∧
      (∀ x y : M, f x = f p + 3 * η / 2 → f y = f p + 3 * η / 2 →
        (∃ s : ℝ, 0 < s ∧ Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp x) = ((s : ℝ) : ℂ)) →
        (∃ s : ℝ, 0 < s ∧ Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) = ((s : ℝ) : ℂ)) →
        x = y) := by
  classical
  -- ## the constants
  set ηs : ℝ := Work.Drive.N2.packetEta D η with hηsdef
  have hηs : 0 < ηs := by rw [hηsdef]; exact Work.Drive.N2.packetEta_pos D hη
  have hηs₁ : ηs < 3 / 800 := by
    rw [hηsdef]; exact packetEta_lt_three_eightieth D hsmall
  have hηs₂ : ηs < 1 / 10 := by linarith
  have hm1 : (1 : ℝ) < 99 / 50 := by norm_num
  have hφEpos : 0 < Work.Drive.N2Lead.mobiusPhiE ηs (99 / 50) :=
    (leadProfile_phiE hηs (by norm_num)).2.1
  have hφElt : Work.Drive.N2Lead.mobiusPhiE ηs (99 / 50) < Real.pi / 2 :=
    (leadProfile_phiE hηs (by norm_num)).2.2
  -- ## the twist radius and the push of the picture
  set ε : ℝ := min (1 / 8) (Real.sqrt (S.a' ^ 2 + ηs)) with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (Real.sqrt_pos_of_pos (by nlinarith [S.ha'pos, hηs]))
  have hεle8 : ε ≤ 1 / 8 := min_le_left _ _
  have hεle34 : ε ≤ 3 / 4 := by linarith
  have hε19 : ε ≤ 19 := by linarith
  have hεa : ε ≤ Real.sqrt (S.a' ^ 2 + ηs) := min_le_right _ _
  -- ## the two model rows
  obtain ⟨εpM, hεpM, D₀M, hD₀M, hmodelRows⟩ :=
    Work.Drive.N2C.mobiusModelPieceRows (D := D) hη hsmall hsep hf S hshape hε hεa
  obtain ⟨εpS, hεpS, D₀S, hD₀S, hsgn⟩ := mobiusModelSignRows (D := D) hη hsmall S hε hεa
  set εp : ℝ := min (1 / 8) (min εpM εpS) with hεpdef
  have hεp : 0 < εp := lt_min (by norm_num) (lt_min hεpM hεpS)
  have hεple8 : εp ≤ 1 / 8 := min_le_left _ _
  have hεple34 : εp ≤ 3 / 4 := by linarith
  have hεpleM : εp ≤ εpM := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεpleS : εp ≤ εpS := le_trans (min_le_right _ _) (min_le_right _ _)
  set Dp : ℝ := max D₀M (max D₀S 0) with hDpdef
  have hDp : 0 ≤ Dp := le_trans (le_max_right D₀S 0) (le_max_right D₀M (max D₀S 0))
  have hDpM : D₀M ≤ Dp := le_max_left _ _
  have hDpS : D₀S ≤ Dp := le_trans (le_max_left D₀S 0) (le_max_right D₀M (max D₀S 0))
  obtain ⟨hαrow, hβrow⟩ := hsgn εp hεp hεpleS Dp hDpS
  -- ## the profile and rigidity rows
  have hεsmall : ∀ φ ∈ Set.Icc (-(Work.Drive.N2Lead.mobiusPhiE ηs (99 / 50)))
      (Work.Drive.N2Lead.mobiusPhiE ηs (99 / 50)), ε ≤ S.r φ * Real.cos φ := by
    have h := profile_cos_ge (ηs := ηs) (m := 99 / 50)
      (φE := Work.Drive.N2Lead.mobiusPhiE ηs (99 / 50)) hηs hηs₂ hm1 rfl S.hrpos ?_
    · intro φ hφ
      exact le_trans hεle8 (le_trans (by norm_num) (h φ hφ))
    · intro φ hφ
      have habs : |φ - ((0 : ℤ) : ℝ) * Real.pi|
          ≤ Work.Drive.N2Lead.mobiusPhiE ηs (99 / 50) := by
        rw [Int.cast_zero, zero_mul, sub_zero]
        exact abs_le.mpr ⟨hφ.1, hφ.2⟩
      exact hshape.hlo φ 0 habs
  have harcZ : ∀ w : ℝ, 39 / 20 ≤ |w| →
      (3 / 4 : ℝ) ≤ |(arcZ ηs w).re| ∧ (3 / 4 : ℝ) ≤ (arcZ ηs w).im := by
    intro w hw
    obtain ⟨h1, h2⟩ := arcZ_rigid_bounds hηs (le_of_lt hηs₁) hw
    exact ⟨h2, h1⟩
  -- ## the three rows
  refine ⟨ε, εp, Dp, hε, ?_, hεp, ?_, hDp, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · -- ### clause 1: the picture never vanishes
    intro y hy
    by_cases hreg : y ∈ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j))
        S.Z (39 / 20)
    · intro h0
      exact modelProjImNe (D := D) (S := S) (ε := ε) (εp := εp) (Dp := Dp) hy hreg
        hαrow hβrow (by rw [h0]; simp)
    · have hyb : f y ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) :=
        ⟨by rw [hy]; linarith, by rw [hy]; linarith⟩
      obtain ⟨j, t, hfoot⟩ := S.L.cover (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y)
        (S.hfootval y hreg hyb)
      by_cases hji : j = S.i
      · subst hji
        obtain ⟨t₀, hfoot', hcos, -⟩ :=
          markedFootRows (D := D) hη hsmall S hshape hε hεp hDp hεle34 hεple34 hεsmall harcZ
            hyb hreg hfoot
        intro h0
        rw [markedFootValue (D := D) (η := η) (S := S) (ε := ε) (εp := εp) (Dp := Dp)
          hreg hfoot'] at h0
        have hre : S.r (S.Θ t₀) * Real.cos (S.Θ t₀) = 0 := by
          have := congrArg Complex.re h0
          simpa [polarPic_re S ε εp Dp] using this
        exact hcos (mul_eq_zero.mp hre |>.resolve_left (ne_of_gt (S.hrpos _)))
      · intro h0
        have hre := farValue (D := D) (S := S) (ε := ε) (εp := εp) (Dp := Dp) hε hε19 hεp
          (by linarith) hji hreg hfoot
        rw [h0] at hre
        simp at hre
  · -- ### clause 2: no radial tangent at the marked disc
    intro y hy hnorm v hv hvne
    by_cases hreg : y ∈ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j))
        S.Z (39 / 20)
    · exact (hmodelRows εp hεp hεpleM Dp hDpM y v hy hreg hv hvne).2
    · have hyb : f y ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) :=
        ⟨by rw [hy]; linarith, by rw [hy]; linarith⟩
      obtain ⟨j, t, hfoot⟩ := S.L.cover (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y)
        (S.hfootval y hreg hyb)
      by_cases hji : j = S.i
      · subst hji
        obtain ⟨t₀, hfoot', -, hrow⟩ :=
          markedFootRows (D := D) hη hsmall S hshape hε hεp hDp hεle34 hεple34 hεsmall harcZ
            hyb hreg hfoot
        exact (markedFootRate (D := D) hη hsmall hf S hεp hDp hy hreg hfoot' hrow).2 v hv hvne
      · exfalso
        have hval := mobiusTwisted_far_proj (D := D) (S := S) (ε := ε) (εp := εp) (Dp := Dp)
          hε hε19 hεp (by linarith) hji hreg hfoot
        have him : (proj2 (mobiusTwisted D η S ε εp Dp y)).im
            = 20 + 5 * ((j : ℕ) : ℝ) + Dp + Real.sin (2 * Real.pi * t) := by
          rw [hval, Complex.add_im, Complex.add_im, Work.Drive.N2C.proj2_farPos, Complex.mul_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
            Work.Drive.N2C.im_proj2_ang]
          simp
        have hge : Dp + 19 ≤ ‖proj2 (mobiusTwisted D η S ε εp Dp y)‖ := by
          have h1 := Complex.abs_im_le_norm (proj2 (mobiusTwisted D η S ε εp Dp y))
          rw [him] at h1
          have h2 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
          have h3 : -1 ≤ Real.sin (2 * Real.pi * t) := Real.neg_one_le_sin _
          rw [abs_of_nonneg (by linarith)] at h1
          linarith
        linarith
  · -- ### clause 3: two level points on the positive real axis are equal
    intro x y hx hy hpx hpy
    have hkey : ∀ z : M, f z = f p + 3 * η / 2 →
        (∃ s : ℝ, 0 < s ∧
          proj2 (mobiusTwisted D η S ε εp Dp z) = ((s : ℝ) : ℂ)) →
        ∃ (k : ℤ) (t : ℝ),
          Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) z = S.L.γ S.i t ∧
          S.Θ t = (k : ℝ) * (2 * Real.pi) := by
      intro z hz hpos
      by_cases hregz : z ∈ Work.Drive.N2.saddleRegion
          (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z (39 / 20)
      · exfalso
        have him := modelProjImNe (D := D) (S := S) (ε := ε) (εp := εp) (Dp := Dp) hz hregz
          hαrow hβrow
        obtain ⟨s, -, hsv⟩ := hpos
        rw [hsv] at him
        exact him (by simp)
      · have hzb : f z ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) :=
          ⟨by rw [hz]; linarith, by rw [hz]; linarith⟩
        obtain ⟨j, t, hfootz⟩ := S.L.cover (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) z)
          (S.hfootval z hregz hzb)
        by_cases hji : j = S.i
        · subst hji
          obtain ⟨k, hk⟩ := markedFootAngleTwoPi (D := D) (S := S) hε hεp hDp hregz hpos hfootz
          exact ⟨k, t, hfootz, hk⟩
        · exfalso
          obtain ⟨s, hs, hsv⟩ := hpos
          have hre := farValue (D := D) (S := S) (ε := ε) (εp := εp) (Dp := Dp) hε hε19 hεp
            (by linarith) hji hregz hfootz
          rw [hsv] at hre
          simp at hre
          linarith
    obtain ⟨k₁, t₁, hf₁, hk₁⟩ := hkey x hx hpx
    obtain ⟨k₂, t₂, hf₂, hk₂⟩ := hkey y hy hpy
    have ht : t₁ = t₂ + ((k₁ - k₂ : ℤ) : ℝ) := by
      refine S.hΘmono.injective ?_
      rw [theta_add_int S.hΘper (k₁ - k₂) t₂, hk₂, hk₁]
      push_cast
      ring
    have hfe : Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) x
        = Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y := by
      rw [hf₁, hf₂, ht]
      exact levelCurve_gamma_add_int S.L S.i t₂ (k₁ - k₂)
    have hxy : f x = f y := by rw [hx, hy]
    exact (Work.Drive.N2.footMap_rows_noLaw (f := f) (Φ := D.Φ) (hf := hf) (hΦsm := D.hΦsm)
      (hΦ0 := D.hΦ0) (hΦcomp := D.hΦcomp) (a := f p - 3 * η / 2)).2.1 x y hxy hfe


end

end Work.Drive.N2Lead
