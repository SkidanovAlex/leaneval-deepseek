import Mathlib
import Submission.Work.Drive.N2Lead.mobiusPacketDefs
import Submission.Work.Drive.N2Lead.mobiusWindowEngine

/-!
# The Möbius saddle window is a good drawing on the band

This is the engine application (`D2a`-off) for the packet of `Work.Drive.N2Lead.MobiusPacket`: the
drawing `mobiusWindowDrawing D η S` (model piece on the strip `|Im (Z ·)²| < 39/20`, transported park
picture outside) is a good drawing on the band `f p ± 2η`.

The engine is used in the form `Work.Drive.N2Lead.saddleWindow_of_packet_band_off_noTheta`, which
drops the (unused) smoothness row of the pin function — the row the original engine carries as
`_hθsm`, and which `pinTheta` does *not* satisfy (it is `0` off the chart source and `1` just inside
it, thanks to `hjunk`).
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

/-- The Möbius window drawing is a good drawing on the band `f p ± 2η`. -/
theorem mobiusGoodDrawing {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) tpTop f)
    (S : MobiusPacket D η) :
    Work.Drive.N2.GoodDrawingOn f (Set.Ioo (f p - 2 * η) (f p + 2 * η))
      (mobiusWindowDrawing D η S) := by
  have hηs : 0 < Work.Drive.N2.packetEta D η := Work.Drive.N2.packetEta_pos D hη
  have hηs_lt : Work.Drive.N2.packetEta D η < 1 / 10 := by
    have h4 : Work.Drive.N2.packetEta D η = 3 * Work.Drive.N2.packetEtaB D η / 4 := by
      rw [Work.Drive.N2.packetEtaB_eq]; ring
    rw [h4]; linarith
  have hηb_le : Work.Drive.N2.packetEta D η ≤ Work.Drive.N2.packetEtaB D η := by
    rw [Work.Drive.N2.packetEtaB_eq]; linarith
  have hηb_le2 : Work.Drive.N2.packetEtaB D η ≤ 4 * Work.Drive.N2.packetEta D η / 3 := by
    rw [Work.Drive.N2.packetEtaB_eq]
  have hbandm : f p - S.lam0 ^ 2 * Work.Drive.N2.packetEtaB D η = f p - 2 * η := by
    rw [S.hlam0]; rw [Work.Drive.N2.packetEtaB_law]
  have hbandp : f p + S.lam0 ^ 2 * Work.Drive.N2.packetEtaB D η = f p + 2 * η := by
    rw [S.hlam0]; rw [Work.Drive.N2.packetEtaB_law]
  have hlevv : S.lam0 ^ 2 * Work.Drive.N2.packetEta D η = 3 * η / 2 := by
    rw [S.hlam0]; rw [Work.Drive.N2.packetEta_law]
  -- the foot rows of the flow
  obtain ⟨hfootsm, hfootinj, hfootimm⟩ :=
    Work.Drive.N2.footMap_rows_noLaw (f := f) (Φ := D.Φ) (hf := hf) (hΦsm := D.hΦsm)
      (hΦ0 := D.hΦ0) (hΦcomp := D.hΦcomp) (a := f p - 3 * η / 2)
  -- the engine
  have hmain := saddleWindow_of_packet_band_off_noTheta (M := M)
    (f := f) (c := f p) (η := Work.Drive.N2.packetEta D η) (δ := 1 / 20) (c₀ := 39 / 20)
    (lam := S.lam0 ^ 2) (ηb := Work.Drive.N2.packetEtaB D η)
    (U := Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) (Z := S.Z)
    (foot := Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2))
    (θ := Work.Drive.N2Lead.pinTheta D S.Z (99 / 50)) (A := S.A)
    (hη := hηs) (hη' := hηs_lt) (hδ := by norm_num) (hδ' := by norm_num)
    (hlam := pow_pos S.hlam0pos 2) (hc₀ := by norm_num) (hc₀' := by norm_num)
    (hηb := hηb_le) (hηb₂ := hηb_le2) (hU := isOpen_modelBall_mobius _ _)
    (hf := hf) (hZsm := S.hZsm) (hZinj := S.hZinj) (hZimm := S.hZimm) (hlev := S.hlev)
    (hfoot := fun x => hfootsm.contMDiffAt) (hfootinj := hfootinj) (hfootimm := hfootimm)
    (hfootval := fun y hyD hyA => by
      simp only [hbandm, hbandp, hlevv] at hyA ⊢
      exact S.hfootval y hyD hyA)
    (hfrU := fun x hxfr hxA => by
      simp only [hbandm, hbandp, hlevv] at hxA ⊢
      exact S.hfrU x hxfr hxA)
    (hθ01 := fun x => Work.Drive.N2Lead.pinTheta_mem_Icc D x)
    (hAsm := fun x => S.A_sm x)
    (hAinj := fun x y hx hy h => by
      simp only [hbandm, hbandp, hlevv] at hx hy ⊢
      exact S.A_inj hx hy h)
    (hAimm := fun x hx v hv hA => by
      simp only [hbandm, hbandp, hlevv] at hx ⊢
      exact S.A_imm hx hv hA)
    (hApin := fun x hx hθ => by
      simp only [hlevv] at hx ⊢
      exact S.hApin x hx hθ)
    (hAoff := fun x hx hθ => by
      simp only [hlevv] at hx ⊢
      exact S.hAoff x hx hθ)
    (hseam := fun y hyb hZy => by
      simp only [hbandm, hbandp, hlevv] at hyb ⊢
      exact S.hseam y hyb hZy)
    (hcolFr := fun x hxfr hxA => by
      simp only [hbandm, hbandp, hlevv] at hxA ⊢
      exact S.hcolFr x hxfr hxA)
    (hfootFrint := fun x hxfr hxA => by
      simp only [hbandm, hbandp, hlevv] at hxA ⊢
      exact S.hfootFrint x hxfr hxA)
    (hlandFr := fun x hxfr hxA => by
      simp only [hbandm, hbandp, hlevv] at hxA ⊢
      exact S.hlandFr x hxfr hxA)
    (hbig := fun x hxD hxA hθ => by
      simp only [hbandm, hbandp, hlevv] at hxA ⊢
      exact S.hbig x hxD hxA hθ)
  -- identify the drawing
  have hband : Set.Ioo (f p - S.lam0 ^ 2 * Work.Drive.N2.packetEtaB D η)
      (f p + S.lam0 ^ 2 * Work.Drive.N2.packetEtaB D η)
      = Set.Ioo (f p - 2 * η) (f p + 2 * η) := by
    rw [hbandm, hbandp]
  have hfun : (fun x : M => if x ∈ Work.Drive.N2.saddleRegion
        (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z (39 / 20)
      then Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi (Work.Drive.N2.packetEta D η) (1 / 20)
        (S.Z x))
      else S.A (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) x))
      = mobiusWindowDrawing D η S := by
    funext x
    simp only [mobiusWindowDrawing]
  rw [hband, hfun] at hmain
  exact hmain

end

end Work.Drive.N2Lead
