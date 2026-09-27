import Mathlib
import Submission.Work.Drive.N2Lead.mobiusPacketDefs
import Submission.Work.Drive.N2Lead.saddleProfileRowsMobius
import Submission.Work.Drive.N2Lead.saddleBridgeRowMobius
import Submission.Work.Drive.N2Lead.saddleAngleFunctionMobius
import Submission.Work.Drive.N2Lead.pinSetup
import Submission.Work.Drive.N2Lead.mobiusPolarArcDn
import Submission.Work.Drive.N2Lead.saddleFlowRowsWide
import Submission.Work.Drive.N2C.mobiusPacketRows
import Submission.Work.Drive.N2C.mobiusProfileRows
import Submission.Work.Drive.N2C.mobiusShape

/-!
# `mobiusPacketExists`: the Möbius packet of the saddle window (H7 lane)

The Möbius (opposite-sign) branch of the certified saddle window: from the two arc lifts `τU`
(antitone) and `τL` (monotone) of the anchor level `f p - 3η/2` and the cyclic-order row of the four
endpoints, one builds a `Work.Drive.N2Lead.MobiusPacket D η`.

The construction mirrors `Work.Drive.N2Lead.saddleWindowCertifiedSplit` §1–§8:

* the scaled Morse coordinate `Z = cl_saddleZ D 1`, its chart companion `Zs = chartCplx D` and the
  rows `hZrel`, `hlev`, `hlevSs`, the `ODE` and the first integral `him` (the flow preserves
  `Im (Zs ·)²`), and the pin characterisation `hpinZ`;
* the angle function `Θ` from `Work.Drive.N2Lead.saddleAngleFunctionMobius` and the radial profile
  `r` from `Work.Drive.N2Lead.saddleProfileRowsMobius` (whose *lower* branch row is the Möbius one);
* the two complex arc rows `hArcU`, `hArcL` (`√(ηs / -cos (2θ)) exp (iθ) = arcZ ηs w`, resp.
  `= star (arcZ ηs w)`) from `Work.Drive.N2Lead.polarArc_eq_sqrt` and
  `Work.Drive.N2Lead.mobiusPolarArcDn`, and the off-arc radius row `hoff` from the Möbius bridge row
  `Work.Drive.N2Lead.saddleBridgeRowMobius`;
* the picture rows from `Work.Drive.N2C.mobiusPacketRowsTwist` (the polar picture `C₀` and its twist
  `A = twistY a' 1 ∘ C₀`);
* the seven flow rows from `Work.Drive.N2Lead.saddleFlowRowsWide` at the core constants.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter
open Classical

set_option maxHeartbeats 2000000

noncomputable section

theorem mobiusPacketExistsShape {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hs1 : D.s₁ D.j = 1) (hs2 : D.s₂ D.j = -1)
    (hjunk : ∀ y : M, y ∉ (D.φ D.j).source → D.φ D.j y = 0)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {η : ℝ} (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (hsep : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η < 2 * D.ηd)
    {n : ℕ} {L : Work.Drive.N2C.LevelCurves f (f p - 3 * η / 2) n} {i : Fin n}
    {τU τL : ℝ → ℝ}
    (hτUsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τU (Set.Ioo (-3) 3))
    (hτUd : ∀ w ∈ Set.Ioo (-3) 3, deriv τU w ≠ 0)
    (hτUanti : StrictAntiOn τU (Set.Ioo (-3) 3))
    (hτUval : ∀ w ∈ Set.Ioo (-3) 3,
      L.γ i (τU w) = Work.Drive.N2Lead.arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
    (hτLsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τL (Set.Ioo (-3) 3))
    (hτLd : ∀ w ∈ Set.Ioo (-3) 3, deriv τL w ≠ 0)
    (hτLmono : StrictMonoOn τL (Set.Ioo (-3) 3))
    (hτLval : ∀ w ∈ Set.Ioo (-3) 3,
      L.γ i (τL w) = Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
    (hord : τU (99 / 50) < τU (-(99 / 50)) ∧ τU (-(99 / 50)) < τL (-(99 / 50)) ∧
      τL (-(99 / 50)) < τL (99 / 50) ∧ τL (99 / 50) < τU (99 / 50) + 1) :
    ∃ S : Work.Drive.N2Lead.MobiusPacket D η, Nonempty (Work.Drive.N2C.MobiusShape D η S) := by
  classical
  -- ## §1. numeric rows
  have hρpos : 0 < D.ρ D.j := D.hρ D.j
  have hlam0pos : 0 < D.ρ D.j / 8 := div_pos hρpos (by norm_num)
  have hρc : (((D.ρ D.j / 8 : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact ne_of_gt hlam0pos
  have hlamEta : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEta D η = 3 * η / 2 :=
    Work.Drive.N2.packetEta_law D η
  have hlamEtaB : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η = 2 * η :=
    Work.Drive.N2.packetEtaB_law D η
  have hηb43 : Work.Drive.N2.packetEtaB D η = 4 * Work.Drive.N2.packetEta D η / 3 :=
    Work.Drive.N2.packetEtaB_eq D η
  have hηs_pos : 0 < Work.Drive.N2.packetEta D η := Work.Drive.N2.packetEta_pos D hη
  have hηb_pos : 0 < Work.Drive.N2.packetEtaB D η := Work.Drive.N2.packetEtaB_pos D hη
  have hηs_lt10 : Work.Drive.N2.packetEta D η < 1 / 10 := by linarith [hηb43, hsmall]
  have hηs_lt800 : Work.Drive.N2.packetEta D η < 3 / 800 := by linarith [hηb43, hsmall]
  have hηb_lt10 : Work.Drive.N2.packetEtaB D η < 1 / 10 := by linarith [hsmall]
  have hηs_lt_ηb : Work.Drive.N2.packetEta D η < Work.Drive.N2.packetEtaB D η := by
    linarith [hηb43, hηs_pos]
  have hηb_le : Work.Drive.N2.packetEtaB D η ≤ 4 * Work.Drive.N2.packetEta D η / 3 :=
    le_of_eq hηb43
  have h2ηd : 2 * η < 2 * D.ηd := by
    have h := hsep
    rw [hlamEtaB] at h
    exact h
  have hηd : η < D.ηd := by linarith
  have hRt : (2 : ℝ) ≤ 3 := by norm_num
  have hR19 : (3 : ℝ) < 19 := by norm_num
  have hm1 : (1 : ℝ) < 99 / 50 := by norm_num
  have hm2 : (99 / 50 : ℝ) < 2 := by norm_num
  have hm3 : (99 / 50 : ℝ) < 3 := by norm_num
  have hδ0 : (0 : ℝ) < 1 / 20 := by norm_num
  have hδhalf : (1 / 20 : ℝ) < 1 / 2 := by norm_num
  have hc19 : (39 / 20 : ℝ) + 2 * Work.Drive.N2.packetEta D η < 19 ^ 2 := by
    nlinarith [hηs_lt10]
  have hnum : (39 / 20 : ℝ) + 2 * Work.Drive.N2.packetEta D η
      < Real.sqrt ((Work.Drive.N2.packetEta D η) ^ 2 + (99 / 50 : ℝ) ^ 2) := by
    have h1 : (99 / 50 : ℝ)
        ≤ Real.sqrt ((Work.Drive.N2.packetEta D η) ^ 2 + (99 / 50 : ℝ) ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith)
    nlinarith [hηs_lt800]
  -- ## §2. the chart coordinate
  set Z : M → ℂ := Work.Drive.N2.cl_saddleZ D 1 with hZ
  set Zs : M → ℂ := Work.Drive.N2Lead.chartCplx D with hZs
  have hZs_apply : ∀ y : M, Zs y
      = ((D.φ D.j y 0 : ℝ) : ℂ) + ((D.φ D.j y 1 : ℝ) : ℂ) * Complex.I := by
    intro y; rw [hZs]; exact Work.Drive.N2Lead.chartCplx_apply D y
  have hZrel : ∀ y : M, Zs y = (((D.ρ D.j / 8 : ℝ)) : ℂ) * Z y := by
    intro y
    rw [hZs, hZ, Work.Drive.N2Lead.chartCplx, Work.Drive.N2.cl_saddleZ_apply,
      Work.Drive.N2Lead.cplxE2]
    field_simp
  have hZrel' : ∀ y : M, Work.Drive.N2Lead.chartCplx D y
      = (((D.ρ D.j / 8 : ℝ)) : ℂ) * Z y := by
    intro y; rw [← hZs]; exact hZrel y
  have hZsm_src : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z (D.φ D.j).source := by
    rw [hZ]
    exact (Work.Drive.N2.cl_scaleCLM (1 / (((D.ρ D.j / 8 : ℝ)) : ℂ))).contMDiff.comp_contMDiffOn
      (Work.Drive.N2.cl_chartZLM.contMDiff.comp_contMDiffOn (D.hφ D.j))
  have hZchart : ∀ y : M, Work.Drive.N2.chartZ (D.φ D.j) y = Zs y := by
    intro y; rw [hZs, Work.Drive.N2Lead.chartCplx_apply, Work.Drive.N2.chartZ_apply]
  have hZinjBall : Set.InjOn Z (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) := by
    rw [hZ]; exact Work.Drive.N2.cl_injOn_saddleZ D one_ne_zero
  have hZimmBall : ∀ x ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j),
      Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z x) := by
    intro x hx; rw [hZ]
    exact Work.Drive.N2.cl_injective_mfderiv_saddleZ D one_ne_zero hx
  have hlev : ∀ y ∈ (D.φ D.j).source,
      f y = f p + (D.ρ D.j / 8) ^ 2 * ((Z y) ^ 2).re := by
    intro y hy
    rw [hZ]
    exact Work.Drive.N2.cl_saddleZ_level D hs1 hs2 (by norm_num) (by norm_num) hy
  have hlevSs : ∀ y ∈ (D.φ D.j).source, f y = f p + ((Zs y) ^ 2).re := by
    intro y hy
    have h := D.hval D.j y hy
    rw [D.hxj, hs1, hs2] at h
    rw [h, hZs, Work.Drive.N2Lead.chartCplx, Work.Drive.N2Lead.cplxE2,
      Work.Drive.N2Lead.sq_re, Work.Drive.N2.chartQ]
    simp only [one_mul, neg_one_mul, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero, sub_zero]
    ring
  have hODE : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      HasDerivAt (fun σ : ℝ => D.φ D.j (D.Φ (σ, y)) 0)
        (Work.Drive.N2.chartMult (D.ρ D.j / 8) (‖D.φ D.j (D.Φ (t, y))‖ ^ 2)
          * ((1 : ℝ) * D.φ D.j (D.Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => D.φ D.j (D.Φ (σ, y)) 1)
        (Work.Drive.N2.chartMult (D.ρ D.j / 8) (‖D.φ D.j (D.Φ (t, y))‖ ^ 2)
          * ((-1 : ℝ) * D.φ D.j (D.Φ (t, y)) 1)) t := by
    intro y t hconf
    obtain ⟨h0, h1⟩ := D.hODE D.j y t hconf
    rw [hs1] at h0
    rw [hs2] at h1
    exact ⟨h0, h1⟩
  have him : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      ((Zs (D.Φ (t, y))) ^ 2).im = ((Zs y) ^ 2).im := by
    intro y t hconf
    exact Work.Drive.N2.im_sq_eq_of_flow_closedODE (D.φ D.j) Zs
      (fun m => by rw [hZs]; exact Work.Drive.N2Lead.chartCplx_apply D m) (D.ρ D.j / 8)
      hODE D.hΦ0 y t hconf
  have hpinZ : ∀ x : M,
      x ∈ Work.Drive.N2Lead.saddlePin D (f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEta D η)
          (99 / 50) ↔
      x ∈ (D.φ D.j).source ∧ ‖Z x‖ < 8 ∧
        f x = f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEta D η ∧
        |((Z x) ^ 2).im| ≤ 99 / 50 := by
    intro x
    rw [hZ]
    exact Work.Drive.N2Lead.saddlePin_eq_scaled D hlam0pos rfl hZrel'
  have hcollSrc : ∀ y : M,
      Z y ∈ Work.Drive.N2.saddleCollar (Work.Drive.N2.packetEtaB D η) (1 / 20) →
      y ∈ (D.φ D.j).source := by
    intro y hy
    by_contra hys
    have h0 : Zs y = 0 := by
      rw [hZs, Work.Drive.N2Lead.chartCplx, Work.Drive.N2Lead.cplxE2, hjunk y hys]
      simp
    have h1 : Z y = 0 := by
      have h := hZrel y
      rw [h0] at h
      have : (((D.ρ D.j / 8 : ℝ)) : ℂ) * Z y = 0 := h.symm
      exact (mul_eq_zero.mp this).resolve_left hρc
    rw [h1] at hy
    simp only [Work.Drive.N2.saddleCollar, Set.mem_setOf_eq] at hy
    have : |((0 : ℂ) ^ 2).im| = 0 := by simp
    rw [this] at hy
    linarith [hy.2.1, hδ0]
  -- ## §3. the two anchor arcs
  have harc_ball : ∀ w : ℝ, |w| ≤ 99 / 50 →
      ‖Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w‖ < 8 := by
    intro w hw
    refine Work.Drive.N2Lead.arcZ_norm_lt _ _ ?_ ?_
    · rw [abs_of_pos hηs_pos]; linarith [hηs_lt10]
    · linarith [hw, hm2]
  have hmabs : ∀ w : ℝ, w ∈ Set.Icc (-(99 / 50)) (99 / 50) → |w| ≤ 99 / 50 :=
    fun w hw => abs_le.mpr hw
  have hmIcc : ∀ w : ℝ, w ∈ Set.Icc (-(99 / 50)) (99 / 50) → w ∈ Set.Ioo (-3) 3 := by
    intro w hw; exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hmIoo : ∀ w : ℝ, w ∈ Set.Ioo (-(99 / 50)) (99 / 50) → w ∈ Set.Ioo (-3) 3 := by
    intro w hw; exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hmemT : ∀ w : ℝ, |w| ≤ 99 / 50 →
      Work.Drive.N2Lead.cE2
        (-((((D.ρ D.j / 8 : ℝ)) : ℂ) * Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w))
        ∈ (D.φ D.j).target := by
    intro w hw
    refine Work.Drive.N2.windowBall_subset_target D D.j ?_
    rw [Work.Drive.N2Lead.cE2_norm, norm_neg, norm_mul, Complex.norm_of_nonneg hlam0pos.le]
    nlinarith [harc_ball w hw, hρpos]
  have hZU : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      Z (Work.Drive.N2Lead.arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
        = Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w := by
    intro w hw
    rw [hZ]
    exact Work.Drive.N2Lead.Z_arcUpPt D (harc_ball w (hmabs w hw)) hlam0pos rfl hZrel'
  have hZL : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      Z (Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
        = -Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w := by
    intro w hw
    have hphi : D.φ D.j
        (Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
        = Work.Drive.N2Lead.cE2
          (-((((D.ρ D.j / 8 : ℝ)) : ℂ)
            * Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w)) :=
      (D.φ D.j).right_inv (hmemT w (hmabs w hw))
    have hchart : Work.Drive.N2Lead.chartCplx D
        (Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
        = -((((D.ρ D.j / 8 : ℝ)) : ℂ)
            * Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w) := by
      rw [Work.Drive.N2Lead.chartCplx, hphi, Work.Drive.N2Lead.cplxE2_cE2]
    have h := hZrel' (Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
    rw [hchart] at h
    have h2 : (((D.ρ D.j / 8 : ℝ)) : ℂ) * Z
        (Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
        = (((D.ρ D.j / 8 : ℝ)) : ℂ)
          * (-Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w) := by
      rw [← h]; ring
    exact mul_left_cancel₀ hρc h2
  have hαsrcU : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      Work.Drive.N2Lead.arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w
        ∈ (D.φ D.j).source := by
    intro w hw
    exact Work.Drive.N2Lead.arcUpPt_mem_source D (harc_ball w (hmabs w hw)) rfl
  have hαsrcL : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w
        ∈ (D.φ D.j).source := by
    intro w hw
    exact (D.φ D.j).map_target (hmemT w (hmabs w hw))
  have hτU' : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      L.γ i (τU w)
        = Work.Drive.N2Lead.arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w :=
    fun w hw => hτUval w (hmIcc w hw)
  have hτL' : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      L.γ i (τL w)
        = Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w :=
    fun w hw => hτLval w (hmIcc w hw)
  have hZinj_of : ∀ {x y : M}, x ∈ (D.φ D.j).source → y ∈ (D.φ D.j).source →
      Z x = Z y → x = y := by
    intro x y hx hy hxy
    have h1 : Work.Drive.N2Lead.chartCplx D x = Work.Drive.N2Lead.chartCplx D y := by
      have h := hZrel' x
      rw [hxy] at h
      exact h.trans (hZrel' y).symm
    have h2 : Work.Drive.N2.chartZ (D.φ D.j) x = Work.Drive.N2.chartZ (D.φ D.j) y := by
      rw [hZchart x, hZchart y]; exact h1
    have h3 : D.φ D.j x = D.φ D.j y := by
      have := congrArg Work.Drive.N2Lead.cplxVec h2
      rwa [Work.Drive.N2Lead.cplxVec_chartZ, Work.Drive.N2Lead.cplxVec_chartZ] at this
    exact (D.φ D.j).injOn hx hy h3
  have hZinjU : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50), ∀ x ∈ (D.φ D.j).source,
      Z x = Z (Work.Drive.N2Lead.arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w) →
      x = Work.Drive.N2Lead.arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w :=
    fun w hw x hx hZx => hZinj_of hx (hαsrcU w hw) hZx
  have hZinjL : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50), ∀ x ∈ (D.φ D.j).source,
      Z x = Z (Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w) →
      x = Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w :=
    fun w hw x hx hZx => hZinj_of hx (hαsrcL w hw) hZx
  have hreg : ∀ x : M, f x = f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEta D η →
      ¬ Work.Drive.Morse.IsCritical f x := by
    intro x hx hcrit
    obtain ⟨j', hj'⟩ := D.hcover x hcrit
    rcases eq_or_ne j' D.j with h | h
    · rw [← hj', h, D.hxj, hlamEta] at hx
      linarith
    · have hsep_i := D.hsep j' D.j h
      rw [hj', D.hxj, hx, hlamEta] at hsep_i
      have habs : |f p - 3 * η / 2 - f p| = 3 * η / 2 := by
        rw [show f p - 3 * η / 2 - f p = -(3 * η / 2) by ring, abs_neg,
          abs_of_pos (by linarith [hη] : (0 : ℝ) < 3 * η / 2)]
      rw [habs] at hsep_i
      linarith [h2ηd]
  -- ## §4. the angle function and the profile
  obtain ⟨Θ, hΘsm, hΘmono, hΘderiv, hΘper, hΘU, hΘL⟩ :=
    Work.Drive.N2Lead.saddleAngleFunctionMobius hηs_pos (by norm_num) hm3
      hτUsm hτUd hτUanti hτLsm hτLd hτLmono hord
  obtain ⟨r, hr, hrpos, hrper, hrpi, hrR, hrArcU, hrArcL, hrbridge, hrev, hrdec⟩ :=
    Work.Drive.N2C.saddleProfileRowsMobiusFull hηs_pos hηs_lt10 hm1 hm2 hRt
  have hoff : ∀ t : ℝ,
      (∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-(99 / 50)) (99 / 50) → t ≠ τU w + k) →
      (∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-(99 / 50)) (99 / 50) → t ≠ τL w + k) →
      (39 / 20 : ℝ) + 2 * Work.Drive.N2.packetEta D η < r (Θ t) ^ 2 :=
    Work.Drive.N2Lead.saddleBridgeRowMobius hηs_pos (by linarith : (0:ℝ) < 99 / 50)
      hΘmono hΘper
      (fun w hw => hΘU w hw) (fun w hw => hΘL w hw) hrbridge hnum
  have hArcU : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      r (Θ (τU w)) * Complex.exp (((Θ (τU w) : ℝ) : ℂ) * Complex.I)
        = Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w := by
    intro w hw
    rw [hΘU w hw, hrArcU w hw, Work.Drive.N2Lead.arcZ]
    exact (Work.Drive.N2Lead.polarArc_eq_sqrt hηs_pos w).1
  have hArcL : ∀ w ∈ Set.Icc (-(99 / 50)) (99 / 50),
      r (Θ (τL w)) * Complex.exp (((Θ (τL w) : ℝ) : ℂ) * Complex.I)
        = star (Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w) := by
    intro w hw
    rw [hΘL w hw, hrArcL w hw]
    exact Work.Drive.N2Lead.mobiusPolarArcDn hηs_pos w
  have hZsm' : ∀ x ∈ (D.φ D.j).source,
      ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z x :=
    fun x hx => hZsm_src.contMDiffAt ((D.φ D.j).open_source.mem_nhds hx)
  -- ## §5. the packet picture
  let L' : Work.Drive.N2C.LevelCurves f
      (f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEta D η) n :=
    { L with
      val := fun j x => by rw [hlamEta]; exact L.val j x
      cover := fun x hx => L.cover x (by rw [hlamEta] at hx; exact hx) }
  obtain ⟨C₀, A, hC₀sm, hC₀val, hC₀far, hC₀inj, hC₀imm, hAeq, hApin, hAoff⟩ :=
    Work.Drive.N2C.mobiusPacketRowsTwist (lam0 := D.ρ D.j / 8)
      (ηs := Work.Drive.N2.packetEta D η) (δ := 1 / 20) (c₀ := 39 / 20) (m := 99 / 50)
      (R := 3) (a' := Real.sqrt (Work.Drive.N2.packetEta D η) / 2) (n := n)
      hf D L' i (r := r) (Θ := Θ) (τU := τU) (τL := τL)
      (αU := fun w => Work.Drive.N2Lead.arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
      (αL := fun w => Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
      hreg hlam0pos hZsm' hlev hpinZ hZinjU hZinjL hαsrcU hαsrcL hZU hZL
      hηs_pos hηs_lt10 hδ0 (by norm_num : (1/20:ℝ) < 1/10) hm1 hm2 hRt hR19 hr hrpos hrper hrR
      hΘsm hΘmono hΘderiv hΘper hArcU hArcL hτU' hτL'
      (by positivity)
      (by have h : 2 * (Real.sqrt (Work.Drive.N2.packetEta D η) / 2)
            = Real.sqrt (Work.Drive.N2.packetEta D η) := by ring
          rw [h])
      hoff hc19
  -- ## §6. the seven flow rows of the engine
  have hsgn : D.s₁ D.j = - D.s₂ D.j := by rw [hs1, hs2]; norm_num
  obtain ⟨hflow1, hflow2, hflow3, hflow4, hflow5, hflow6, hflow7⟩ :=
    Work.Drive.N2Lead.saddleFlowRowsWide D hsgn (Zs := Zs) (Z := Z) (lam0 := D.ρ D.j / 8)
      (ηs := Work.Drive.N2.packetEta D η) (ηb := Work.Drive.N2.packetEtaB D η)
      (δ := 1 / 20) (c₀ := 39 / 20)
      hlam0pos rfl hZrel hZs_apply hZsm_src hlev hlevSs hODE him
      hηs_pos hηs_lt10 hδ0 (by norm_num : (1/20:ℝ) < 1/10) hηs_lt_ηb hηb_lt10
      (by norm_num : (2:ℝ) - 2 * (1/20) < 39/20) (by norm_num : (39/20:ℝ) < 2)
      (by norm_num : (39/20:ℝ) < 99/50) hsep hcollSrc
  have hbandm : f p - 2 * η = f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η := by
    rw [← hlamEtaB]
  have hbandp : f p + 2 * η = f p + (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η := by
    rw [← hlamEtaB]
  have hlevv : f p + 3 * η / 2
      = f p + (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEta D η := by
    rw [← hlamEta]
  -- ## §7. the packet
  refine ⟨{
    Z := Z
    lam0 := D.ρ D.j / 8
    hlam0pos := hlam0pos
    hlam0 := rfl
    hZsm := hZsm_src.mono (fun y hy => hy.1)
    hZinj := hZinjBall
    hZimm := hZimmBall
    hlev := fun y hy => hlev y hy.1
    n := n
    L := L
    i := i
    r := r
    Θ := Θ
    hr := hr
    hrpos := hrpos
    hrper := hrper
    hrR := hrR
    hΘ := hΘsm
    hΘmono := hΘmono
    hΘderiv := hΘderiv
    hΘper := hΘper
    a' := Real.sqrt (Work.Drive.N2.packetEta D η) / 2
    ha'pos := by positivity
    ha' := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      nlinarith [Real.sq_sqrt hηs_pos.le, hηs_lt10]
    C₀ := C₀
    hC₀sm := hC₀sm
    hC₀val := hC₀val
    hC₀far := hC₀far
    hC₀inj := by
      intro x y hx hy h
      exact hC₀inj x y (by rw [hlamEta]; exact hx) (by rw [hlamEta]; exact hy) h
    hC₀imm := by
      intro x hx v hv hC
      exact hC₀imm x (by rw [hlamEta]; exact hx) v hv hC
    A := A
    hAeq := hAeq
    hApin := by
      intro x hx hθ
      exact hApin x (by rw [hlamEta]; exact hx) hθ
    hAoff := by
      intro x hx hθ
      exact hAoff x (by rw [hlamEta]; exact hx) hθ
    hfootval := by
      intro y hy hyb
      have hyb' : f y ∈ Set.Ioo (f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η)
          (f p + (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η) := by
        rw [hlamEtaB]; exact hyb
      have h := hflow1 y hy hyb'
      rw [hlamEta] at h
      exact h
    hfrU := by
      intro x hx hxb
      have hxb' : f x ∈ Set.Ioo (f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η)
          (f p + (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η) := by
        rw [hlamEtaB]; exact hxb
      exact hflow2 x hx hxb'
    hseam := by
      intro y hyb hZy
      have hyb' : f y ∈ Set.Ioo (f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η)
          (f p + (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η) := by
        rw [hlamEtaB]; exact hyb
      have h := hflow3 y hyb' hZy
      rw [hlamEta] at h
      exact h
    hcolFr := by
      intro x hx hxb
      have hxb' : f x ∈ Set.Ioo (f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η)
          (f p + (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η) := by
        rw [hlamEtaB]; exact hxb
      have h := hflow4 x hx hxb'
      rw [← hlamEtaB]
      exact h
    hbig := by
      intro x hxr hxb hθ
      have hxb' : f x ∈ Set.Ioo (f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η)
          (f p + (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η) := by
        rw [hlamEtaB]; exact hxb
      rw [← hlamEta] at hθ ⊢
      exact hflow5 x hxr hxb' hθ
    hfootFrint := by
      intro x hx hxb
      have hxb' : f x ∈ Set.Ioo (f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η)
          (f p + (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η) := by
        rw [hlamEtaB]; exact hxb
      have h := hflow6 x hx hxb'
      rw [← hlamEta]
      exact h
    hlandFr := by
      intro x hx hxb
      have hxb' : f x ∈ Set.Ioo (f p - (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η)
          (f p + (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η) := by
        rw [hlamEtaB]; exact hxb
      have h := hflow7 x hx hxb'
      rw [hlamEta] at h
      exact h
    hreg := by
      intro x hx
      exact hreg x (by rw [hlamEta]; exact hx) },
    ?_⟩
  exact Nonempty.intro
    ⟨hrev, hrdec, hrbridge, τU, τL, (fun w hw => hΘU w hw), (fun w hw => hΘL w hw),
      (fun w hw => by rw [hτU' w hw]; exact hZU w hw),
      (fun w hw => by rw [hτL' w hw]; exact hZL w hw),
      (fun w hw => hτU' w hw), (fun w hw => hτL' w hw), hrpi, hnum, hArcU, hArcL,
      (fun w hw => ⟨(hτUsm.contDiffAt (isOpen_Ioo.mem_nhds (hmIoo w hw))).differentiableAt
          (by simp), hτUd w (hmIoo w hw)⟩),
      (fun w hw => ⟨(hτLsm.contDiffAt (isOpen_Ioo.mem_nhds (hmIoo w hw))).differentiableAt
          (by simp), hτLd w (hmIoo w hw)⟩)⟩

/-- **The Möbius packet, in the shape of the holder `Work.Drive.N2Lead.mobiusPacketExists`.** -/
theorem mobiusPacketExists {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hs1 : D.s₁ D.j = 1) (hs2 : D.s₂ D.j = -1)
    (hjunk : ∀ y : M, y ∉ (D.φ D.j).source → D.φ D.j y = 0)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {η : ℝ} (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (hsep : (D.ρ D.j / 8) ^ 2 * Work.Drive.N2.packetEtaB D η < 2 * D.ηd)
    {n : ℕ} {L : Work.Drive.N2C.LevelCurves f (f p - 3 * η / 2) n} {i : Fin n}
    {τU τL : ℝ → ℝ}
    (hτUsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τU (Set.Ioo (-3) 3))
    (hτUd : ∀ w ∈ Set.Ioo (-3) 3, deriv τU w ≠ 0)
    (hτUanti : StrictAntiOn τU (Set.Ioo (-3) 3))
    (hτUval : ∀ w ∈ Set.Ioo (-3) 3,
      L.γ i (τU w) = Work.Drive.N2Lead.arcUpPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
    (hτLsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τL (Set.Ioo (-3) 3))
    (hτLd : ∀ w ∈ Set.Ioo (-3) 3, deriv τL w ≠ 0)
    (hτLmono : StrictMonoOn τL (Set.Ioo (-3) 3))
    (hτLval : ∀ w ∈ Set.Ioo (-3) 3,
      L.γ i (τL w) = Work.Drive.N2Lead.arcDnPt D (D.ρ D.j / 8) (Work.Drive.N2.packetEta D η) w)
    (hord : τU (99 / 50) < τU (-(99 / 50)) ∧ τU (-(99 / 50)) < τL (-(99 / 50)) ∧
      τL (-(99 / 50)) < τL (99 / 50) ∧ τL (99 / 50) < τU (99 / 50) + 1) :
    Nonempty (Work.Drive.N2Lead.MobiusPacket D η) :=
  let ⟨S, _⟩ := mobiusPacketExistsShape D hs1 hs2 hjunk hf hη hsmall hsep
    hτUsm hτUd hτUanti hτUval hτLsm hτLd hτLmono hτLval hord
  ⟨S⟩

end

end Work.Drive.N2C
