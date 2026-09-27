import Mathlib
import Submission.Work.Drive.N2Lead.mobiusPacketDefs
import Submission.Work.Drive.N2Lead.saddleLowerCertifiedFleet
import Submission.Work.Drive.N2Lead.isCertifiedAt_of_ambientPath
import Submission.Work.Drive.N2Lead.certifiedTransferOnLevel
import Submission.Work.Drive.N2Lead.saddlePinFunction

/-!
# The anchor certificate of the Möbius saddle window

The drawing of `Work.Drive.N2Lead.MobiusPacket` is the park picture `A` on the anchor level (the
model piece and the park agree there, because the points of the model region are pinned and the foot
map is the identity on its own level), and the park picture is the slab twist `twistY a' 1` of the
star-shaped polar picture `C₀`.  The certificate of `C₀` is
`Work.Drive.N2Lead.saddleLowerCertifiedFleet`, and the twist is an ambient path
(`Work.Drive.N2Lead.isCertifiedAt_of_ambientPath`), which transfers the certificate back to `A`.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter
open Classical

noncomputable section

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- The pin function equals `1` at every point of the model region on the anchor level. -/
lemma pinTheta_eq_one_of_mem_region {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    {Z : M → ℂ} {η : ℝ} (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (hlev : ∀ y ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j),
      f y = f p + (D.ρ D.j / 8) ^ 2 * ((Z y) ^ 2).re)
    {x : M} (hx : x ∈ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j))
      Z (39 / 20))
    (hxf : f x = f p - 3 * η / 2) :
    Work.Drive.N2Lead.pinTheta D Z (99 / 50) x = 1 := by
  have hηs : 0 < Work.Drive.N2.packetEta D η := Work.Drive.N2.packetEta_pos D hη
  have hηs_lt : Work.Drive.N2.packetEta D η < 1 / 10 := by
    have h4 : Work.Drive.N2.packetEta D η = 3 * Work.Drive.N2.packetEtaB D η / 4 := by
      rw [Work.Drive.N2.packetEtaB_eq]; ring
    rw [h4]; linarith
  rw [Work.Drive.N2Lead.pinTheta_eq_one_iff D (by norm_num : (99 : ℝ) / 50 < 2) hx.1.1]
  refine ⟨le_of_lt (lt_trans hx.2 (by norm_num)), ?_⟩
  -- the real part of the square at the anchor level
  have hre : ((Z x) ^ 2).re = -(Work.Drive.N2.packetEta D η) := by
    have h := hlev x hx.1
    rw [hxf] at h
    have hlin : (D.ρ D.j / 8) ^ 2 * ((Z x) ^ 2).re = -(3 * η / 2) := by linarith
    have hlaw : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEta D η = 3 * η / 2 :=
      Work.Drive.N2.packetEta_law D η
    have hcancel : (D.ρ D.j / 8) ^ 2 * ((Z x) ^ 2).re
        = (D.ρ D.j / 8) ^ 2 * (-(Work.Drive.N2.packetEta D η)) := by
      rw [hlin]
      rw [← hlaw]
      ring
    exact mul_left_cancel₀ (ne_of_gt (pow_pos (div_pos (D.hρ D.j) (by norm_num)) 2)) hcancel

  -- the norm bound
  have hnorm2 : ‖(Z x) ^ 2‖ ^ 2 = ((Z x) ^ 2).re ^ 2 + ((Z x) ^ 2).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hlt : ‖(Z x) ^ 2‖ ^ 2 < 16 := by
    rw [hnorm2, hre]
    have h1 : (Work.Drive.N2.packetEta D η) ^ 2 < (1 / 10) ^ 2 := by nlinarith
    have h2 : ((Z x) ^ 2).im ^ 2 < (39 / 20) ^ 2 := by
      have := abs_lt.mp hx.2
      nlinarith [this.1, this.2]
    linarith
  have hnorm : ‖Z x‖ ^ 2 = ‖(Z x) ^ 2‖ := (norm_pow (Z x) 2).symm
  rw [hnorm]
  nlinarith [norm_nonneg ((Z x) ^ 2), sq_nonneg (‖(Z x) ^ 2‖ - 4)]

/-- **The anchor certificate of the Möbius saddle window.** -/
theorem mobiusLowerCertified {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) tpTop f)
    (S : MobiusPacket D η) :
    Work.Drive.N2C.IsCertifiedAt f (f p - 3 * η / 2) (mobiusWindowDrawing D η S) := by
  -- ## the certificate of the polar picture
  have hC₀cd : ContMDiff (𝓡 2) (𝓡 3) tpTop S.C₀ := fun x => S.hC₀sm x
  have hcertC₀ : Work.Drive.N2C.IsCertifiedAt f (f p - 3 * η / 2) S.C₀ :=
    saddleLowerCertifiedFleet (L := S.L) (hf := hf) (hreg := S.hreg) (A := S.C₀) hC₀cd
      (fun x y hx hy h => S.hC₀inj x y hx hy h)
      (fun x hx v hv hA => S.hC₀imm x hx v hv hA)
      (i := S.i) (r := S.r) (Θ := S.Θ) (R := 3) S.hC₀val S.hC₀far
      S.hr S.hrpos S.hrper S.hrR (by norm_num) S.hΘ S.hΘmono S.hΘderiv S.hΘper
  -- ## transfer along the twist
  have hiso : Work.Drive.N2C.IsLevelIsotopy f (f p - 3 * η / 2) (fun _ : ℝ => S.A) := by
    refine ⟨?_, ?_, ?_⟩
    · intro s y hy
      exact (S.A_sm y).comp (s, y) contMDiffAt_snd
    · intro s x y hx hy h
      exact S.A_inj hx hy h
    · intro s y hy v hv hA
      exact S.A_imm hy hv hA
  have h1 : Work.Drive.N2C.IsCertifiedAt f (f p - 3 * η / 2)
      (fun y : M => twistY S.a' (-1) (S.A y)) := by
    refine Work.Drive.N2Lead.isCertifiedAt_of_eqOn_level (A := S.C₀) (fun y hy => ?_) hcertC₀
    rw [S.hAeq y, twistY_comp, neg_add_cancel, twistY_zero]
  have hcertA : Work.Drive.N2C.IsCertifiedAt f (f p - 3 * η / 2) S.A :=
    Work.Drive.N2Lead.isCertifiedAt_of_ambientPath (hf := hf) (hreg := S.hreg)
      (g := S.A) hiso (ambientPath_twistY S.a') h1
  -- ## the drawing is the park picture on the anchor level
  refine Work.Drive.N2Lead.isCertifiedAt_of_eqOn_level (A := S.A)
    (W := mobiusWindowDrawing D η S) (fun y hy => ?_) hcertA
  rw [mobiusWindowDrawing]
  by_cases hx : y ∈ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j)
      (D.ρ D.j)) S.Z (39 / 20)
  · rw [if_pos hx]
    have hθ : Work.Drive.N2Lead.pinTheta D S.Z (99 / 50) y = 1 :=
      pinTheta_eq_one_of_mem_region D hη hsmall
        (fun z hz => by rw [← S.hlam0]; exact S.hlev z hz) hx hy
    exact S.hApin y hy hθ
  · rw [if_neg hx]
    rw [Work.Drive.N2Lead.footMap_eq_self_of_eq D.hΦ0 hy]

end

end Work.Drive.N2Lead
