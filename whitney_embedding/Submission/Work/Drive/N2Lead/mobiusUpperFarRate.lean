import Mathlib
import Submission.Work.Drive.N2Lead.mobiusUpperFootKit
import Submission.Work.Drive.N2C.lowerCert
import Submission.Work.Drive.N2Lead.mobiusGoodDrawing
import Submission.Work.Drive.N2.windowDatumSmoothN
import Submission.Work.Drive.N2Lead.isLevelIsotopy_squash
import Submission.Work.Compat.MFDerivCongrV433

/-!
# The rate row of the twisted Möbius picture on the parked (far) circles

At the level `f p + 3η/2`, a point `y` outside the model (saddle) region whose foot `foot y` lies on
a *parked* component `L.γ j t` (`j ≠ i`) of the anchor level `f p - 3η/2` has its twisted Möbius
picture on the round circle of radius `1` about `proj2 (farPos S.n j) + Dp·I`
(`Work.Drive.N2Lead.mobiusTwisted_far_proj`).  This file proves the corresponding *rate* row: the
tangent line of that circle never passes through its centre, so the picture is star-shaped about the
shifted parking spot there.

The two ingredients are

* the *value* row above (the picture is `centre + proj2 (ang t)`), and
* the *chain rule on the level*: because the foot map is smooth and lands on the anchor level, the
  derivative of the picture along a tangent vector `v ∈ ker df_y` is the derivative of the parked
  circle along the component, multiplied by the scalar `s₀` with
  `mfderiv foot y v = mfderiv (L.γ j) t s₀`.  The two slab maps (`twistX ε (-1)`, `pushY Dp εp 1`)
  are rigid on the parked circle's image, so they may be dropped before differentiating
  (`mfr_contMDiffAt_pushed`, `hcurve_eq` below).

The parked circle's own non-radiality is `Work.Drive.N2C.farCurve_deriv_not_radial`.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-! ## Auxiliary lemmas -/

/-- **Non-radiality is preserved by multiplying the direction by a nonzero real scalar.**  If `d` is
not a real multiple of `z - o`, then neither is `l · d` (`l ≠ 0`). -/
lemma mfr_not_smul_of_not_smul {D d z o : ℂ} {l : ℝ} (hl : l ≠ 0) (hD : D = (l : ℂ) * d)
    (h : ¬ ∃ t : ℝ, d = t • (z - o)) : ¬ ∃ t : ℝ, D = t • (z - o) := by
  rintro ⟨t, ht⟩
  refine h ⟨t / l, ?_⟩
  have h1 : d = ((t : ℂ) * (z - o)) / (l : ℂ) := by
    rw [eq_div_iff (Complex.ofReal_ne_zero.mpr hl), mul_comm d]
    rw [hD] at ht
    exact ht
  rw [h1, Complex.real_smul, Complex.ofReal_div]
  ring

/-- **The chain rule through the foot map for the planar picture.** -/
lemma mfr_mfderiv_proj2_comp_foot {y : M} {foot : M → M} {A : M → E3}
    (hfoot : ContMDiffAt (𝓡 2) (𝓡 2) tpTop foot y)
    (hA : ∀ z : M, ContMDiffAt (𝓡 2) (𝓡 3) tpTop A z) (v : TangentSpace (𝓡 2) y) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (A (foot z))) y v
      = mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (A z)) (foot y)
          (mfderiv (𝓡 2) (𝓡 2) foot y v) :=
  mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓘(ℝ, ℂ)) y (g := fun z : M => proj2 (A z))
    ((proj2CLM.mdifferentiableAt).comp (foot y) ((hA (foot y)).mdifferentiableAt (by simp)))
    (hfoot.mdifferentiableAt (by simp)) v

/-- **The chain rule through the foot map for a real-valued function.** -/
lemma mfr_mfderiv_f_comp_foot {y : M} {foot : M → M} {g : M → ℝ}
    (hfoot : ContMDiffAt (𝓡 2) (𝓡 2) tpTop foot y)
    (hg : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) tpTop g (foot y)) (v : TangentSpace (𝓡 2) y) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => g (foot z)) y v
      = mfderiv (𝓡 2) 𝓘(ℝ, ℝ) g (foot y) (mfderiv (𝓡 2) (𝓡 2) foot y v) :=
  mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓘(ℝ, ℝ)) y (g := g)
    (hg.mdifferentiableAt (by simp)) (hfoot.mdifferentiableAt (by simp)) v

/-- **The chain rule on a level curve**, in the form used here: the derivative of `proj2 ∘ W` along
the component `L.γ j` at the parameter `s`, in the direction `t₀`. -/
lemma mfr_mfderiv_levelCurve_eq_deriv {f : M → ℝ} {u : ℝ} {W : M → E3} {n : ℕ}
    (L : Work.Drive.N2C.LevelCurves f u n)
    (hWsm : ∀ y : M, f y = u → ContMDiffAt (𝓡 2) (𝓡 3) tpTop W y)
    (j : Fin n) (s t₀ : ℝ) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (W z)) (L.γ j s)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (L.γ j) s t₀)
      = deriv (fun u : ℝ => proj2 (W (L.γ j u))) s * (t₀ : ℂ) :=
  Work.Drive.N2C.mfderiv_levelCurve_eq_deriv L hWsm (fun j' u' => rfl) j s t₀

/-- **Smoothness of the pushed park picture** `pushY Dp εp 1 ∘ twistX ε (-1) ∘ C₀` (everywhere). -/
lemma mfr_contMDiffAt_pushed {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p} {η : ℝ}
    {S : MobiusPacket D η} {ε εp Dp : ℝ} (z : M) :
    ContMDiffAt (𝓡 2) (𝓡 3) tpTop
      (fun x : M => pushY Dp εp 1 (twistX ε (-1) (S.C₀ x))) z := by
  have h1 : ContDiff ℝ tpTop (pushY Dp εp 1) :=
    (contDiff_pushY Dp εp).comp (contDiff_const.prodMk contDiff_id)
  have h3 : ContMDiffAt (𝓡 2) (𝓡 3) tpTop (fun x : M => twistX ε (-1) (S.C₀ x)) z :=
    ((contDiff_twistX_fixed ε (-1)).contMDiff.contMDiffAt).comp z (S.hC₀sm z)
  exact (h1.contMDiff.contMDiffAt).comp z h3

/-- **The Möbius window drawing is the transported park picture near a frontier point of the model
region.**  This is the "front row" of the saddle engine
(`Work.Drive.N2Lead.saddleWindow_of_packet_band_off_noTheta`), isolated for the rate argument: on a
neighbourhood of a frontier point of the model strip the two branches of the drawing agree with
`A ∘ foot`. -/
lemma mfr_drawing_eventuallyEq_A {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p} {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200) (S : MobiusPacket D η) {y : M}
    (hyfr : y ∈ frontier
      (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z (39 / 20)))
    (hyband : f y ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η)) :
    (fun z : M => mobiusWindowDrawing D η S z)
      =ᶠ[𝓝 y] (fun z : M => S.A (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) z)) := by
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) tpTop f := Work.Drive.N2.wdsN_contMDiff_of_windowDatum D
  have hfootsm : ContMDiff (𝓡 2) (𝓡 2) tpTop
      (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2)) :=
    (Work.Drive.N2.footMap_rows_noLaw (f := f) (Φ := D.Φ) (hf := hf) (hΦsm := D.hΦsm)
      (hΦ0 := D.hΦ0) (hΦcomp := D.hΦcomp) (a := f p - 3 * η / 2)).1
  have hηs : 0 < Work.Drive.N2.packetEta D η := Work.Drive.N2.packetEta_pos D hη
  have hηs_lt : Work.Drive.N2.packetEta D η < 1 / 10 := by
    have h := Work.Drive.N2Lead.packetEta_lt_three_eightieth D hsmall
    linarith
  have hηb : Work.Drive.N2.packetEta D η ≤ Work.Drive.N2.packetEtaB D η := by
    rw [Work.Drive.N2.packetEtaB_eq]
    linarith
  have hfootV : ∀ᶠ z in 𝓝 y, Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) z
      ∈ interior ((Work.Drive.N2Lead.pinTheta D S.Z (99 / 50)) ⁻¹' {1}) :=
    (hfootsm.contMDiffAt.continuousAt).preimage_mem_nhds
      (isOpen_interior.mem_nhds (S.hfootFrint y hyfr hyband))
  have hband : ∀ᶠ z in 𝓝 y, f z ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) :=
    hf.continuous.continuousAt (isOpen_Ioo.mem_nhds hyband)
  filter_upwards [hfootV, hband, S.hlandFr y hyfr hyband, S.hcolFr y hyfr hyband]
    with z hzpin hzb hzland hzcol
  by_cases hzD : z ∈ Work.Drive.N2.saddleRegion
      (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z (39 / 20)
  · rw [mobiusWindowDrawing, if_pos hzD]
    have hθ : Work.Drive.N2Lead.pinTheta D S.Z (99 / 50)
        (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) z) = 1 := by
      have h := interior_subset hzpin
      simpa using h
    have hcolz : S.Z z ∈ Work.Drive.N2.saddleCollar (Work.Drive.N2.packetEtaB D η) (1 / 20) :=
      hzcol hzb
    rw [S.hApin _ hzland hθ, S.hseam z hzb hcolz,
      Work.Drive.N2Lead.saddlePsi_idempotent_of_mem_collarWide hηs hηs_lt hηb
        (by norm_num) (by norm_num) hcolz.1 hcolz.2.1 hcolz.2.2]
  · rw [mobiusWindowDrawing, if_neg hzD]

/-! ## The target -/

theorem mobiusUpperFarRate {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (S : Work.Drive.N2Lead.MobiusPacket D η) {ε εp Dp : ℝ}
    (hε : 0 < ε) (hε19 : ε ≤ 19) (hεp : 0 < εp) (hεp19 : εp ≤ 19) :
    ∀ (j : Fin S.n), j ≠ S.i →
      ∀ (y : M) (t : ℝ) (v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) y),
        f y = f p + 3 * η / 2 →
        y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z (39 / 20) →
        Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y = S.L.γ j t →
        Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)
            ≠ Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos S.n j) + (Dp : ℂ) * Complex.I ∧
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ ℝ) f y v = 0 → v ≠ 0 →
          ¬ (∃ s : ℝ, mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
              (modelWithCornersSelf ℝ ℂ)
              (fun z : M => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z)) y v
            = s • (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)
              - (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos S.n j) + (Dp : ℂ) * Complex.I)))) := by
  intro j hj y t v hy hyD hfoot
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) tpTop f := Work.Drive.N2.wdsN_contMDiff_of_windowDatum D
  obtain ⟨hfootsm, hfootinj, hfootimm⟩ :=
    Work.Drive.N2.footMap_rows_noLaw (f := f) (Φ := D.Φ) (hf := hf) (hΦsm := D.hΦsm)
      (hΦ0 := D.hΦ0) (hΦcomp := D.hΦcomp) (a := f p - 3 * η / 2)
  constructor
  · -- ## the value: the picture sits on the round circle about the shifted parking spot
    intro hcon
    have hval := mobiusTwisted_far_proj (D := D) (S := S) (ε := ε) (εp := εp) (Dp := Dp)
      hε hε19 hεp hεp19 hj hyD hfoot
    have hZ : proj2 (Work.Drive.N2.ang t) ≠ 0 := by
      intro h0
      have h1 := Work.Drive.N2C.norm_proj2_ang t
      rw [h0] at h1
      simp at h1
    have h2 : (proj2 (farPos S.n j) + (Dp : ℂ) * Complex.I) + proj2 (Work.Drive.N2.ang t)
        = (proj2 (farPos S.n j) + (Dp : ℂ) * Complex.I) + 0 := by
      rw [← hval, hcon, add_zero]
    exact hZ (add_left_cancel h2)
  · -- ## the rate row
    intro hv hvne
    rintro ⟨s, hs⟩
    set region : Set M :=
      Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z (39 / 20)
      with hregiondef
    set foot : M → M := Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) with hfootdef
    set Wp : M → E3 := fun z : M => pushY Dp εp 1 (twistX ε (-1) (S.C₀ z)) with hWpdef
    have hregionopen : IsOpen region :=
      Work.Drive.N2.isOpen_saddleRegion (isOpen_modelBall_mobius (D.φ D.j) (D.ρ D.j)) S.hZsm
    have hyband : f y ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) := by
      refine ⟨?_, ?_⟩ <;> rw [hy] <;> linarith
    have hland : f (foot y) = f p - 3 * η / 2 := by
      rw [hfootdef]
      exact S.hfootval y hyD hyband
    have hycl_or_fr : y ∈ frontier region ∨ y ∉ closure region := by
      by_cases hfr : y ∈ frontier region
      · exact Or.inl hfr
      · refine Or.inr fun hcl => hfr ?_
        rw [frontier_eq_closure_inter_closure]
        refine ⟨hcl, ?_⟩
        rw [IsClosed.closure_eq (isClosed_compl_iff.mpr hregionopen)]
        exact hyD
    -- the drawing is the transported park picture near `y`
    have hmwev : (fun z : M => mobiusWindowDrawing D η S z) =ᶠ[𝓝 y]
        (fun z : M => S.A (foot z)) := by
      rcases hycl_or_fr with hfr | hcl
      · exact mfr_drawing_eventuallyEq_A hη hsmall S hfr hyband
      · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hcl] with z hzcl
        rw [mobiusWindowDrawing, if_neg (fun hzD => hzcl (subset_closure hzD))]
    -- the picture is the pushed park picture near `y`
    have hmw : (fun z : M => proj2 (mobiusTwisted D η S ε εp Dp z)) =ᶠ[𝓝 y]
        (fun z : M => proj2 (Wp (foot z))) := by
      filter_upwards [hmwev] with z hz
      rw [mobiusTwisted, hz, S.hAeq (foot z), twistY_comp, neg_add_cancel, twistY_zero,
        hWpdef]
    -- the landing row is constantly the anchor level near `y`
    have hevland : (fun z : M => f (foot z)) =ᶠ[𝓝 y] (fun _ : M => f p - 3 * η / 2) := by
      rcases hycl_or_fr with hfr | hcl
      · exact S.hlandFr y hfr hyband
      · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hcl,
          hf.continuous.continuousAt (isOpen_Ioo.mem_nhds hyband)] with z hzcl hzf
        exact S.hfootval z (fun hzD => hzcl (subset_closure hzD)) hzf
    -- the derivative of the picture is that of `proj2 ∘ Wp ∘ foot`
    have hmf1 : mfderiv (𝓡 2) 𝓘(ℝ, ℂ)
          (fun z : M => proj2 (mobiusTwisted D η S ε εp Dp z)) y v
        = mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (Wp (foot z))) y v :=
      DFunLike.congr_fun hmw.mfderiv_eq_v433 v
    have hchain : mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (Wp (foot z))) y v
        = mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (Wp z)) (foot y)
            (mfderiv (𝓡 2) (𝓡 2) foot y v) :=
      mfr_mfderiv_proj2_comp_foot (A := Wp) hfootsm.contMDiffAt
        (fun z => mfr_contMDiffAt_pushed (D := D) (η := η) (S := S) (ε := ε) (εp := εp)
          (Dp := Dp) z) v
    -- the foot tangent lies in the kernel of `df` at the foot
    have hkerfoot : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (foot y) (mfderiv (𝓡 2) (𝓡 2) foot y v) = 0 := by
      have h0 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => f (foot z)) y v = 0 := by
        rw [hevland.mfderiv_eq_v433, mfderiv_const]
        rfl
      rw [mfr_mfderiv_f_comp_foot hfootsm.contMDiffAt (hf.contMDiffAt) v] at h0
      exact h0
    obtain ⟨s₀, hs₀⟩ := S.L.ker j t (mfderiv (𝓡 2) (𝓡 2) foot y v)
      (by rw [← hfoot]; exact hkerfoot)
    have hs₀ne : s₀ ≠ 0 := by
      intro h0
      refine hvne (hfootimm y v hv ?_)
      exact hs₀.symm.trans
        ((congrArg (fun c : ℝ => mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (S.L.γ j) t c) h0).trans
          (map_zero (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (S.L.γ j) t)))
    -- the pushed park curve, as a function of the component parameter
    have hcurve_eq : (fun u : ℝ => proj2 (Wp (S.L.γ j u)))
        = (fun u : ℝ => proj2 (farCurve S.n j u) + (Dp : ℂ) * Complex.I) := by
      funext u
      have hx : (farCurve S.n j u) 0 ≤ -ε := by
        have h := Work.Drive.N2C.re_proj2_farCurve S.n j u
        simp only [proj2] at h
        linarith [Real.cos_le_one (2 * Real.pi * u), hε19]
      have hy : εp ≤ (farCurve S.n j u) 1 := by
        have h := Work.Drive.N2C.im_proj2_farCurve S.n j u
        have h1 : -1 ≤ Real.sin (2 * Real.pi * u) := Real.neg_one_le_sin _
        have h3 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
        simp only [proj2] at h
        linarith
      show proj2 (pushY Dp εp 1 (twistX ε (-1) (S.C₀ (S.L.γ j u))))
        = proj2 (farCurve S.n j u) + (Dp : ℂ) * Complex.I
      rw [S.hC₀far j hj u, twistX_eq_self hε hx, proj2_pushY_of_le hεp hy]
    -- the derivative of the pushed park picture, along the level curve
    have hlevel : mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (Wp z)) (S.L.γ j t)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (S.L.γ j) t s₀)
        = deriv (fun u : ℝ => proj2 (farCurve S.n j u)) t * (s₀ : ℂ) := by
      have h := mfr_mfderiv_levelCurve_eq_deriv (L := S.L) (W := Wp)
        (fun z _ => mfr_contMDiffAt_pushed (D := D) (η := η) (S := S) (ε := ε) (εp := εp)
          (Dp := Dp) z) j t s₀
      rw [h, hcurve_eq, deriv_add_const]
    have hGder : mfderiv (𝓡 2) 𝓘(ℝ, ℂ)
          (fun z : M => proj2 (mobiusTwisted D η S ε εp Dp z)) y v
        = deriv (fun u : ℝ => proj2 (farCurve S.n j u)) t * (s₀ : ℂ) := by
      rw [hmf1, hchain]
      have hfoot' : foot y = S.L.γ j t := hfoot
      have hA : mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (Wp z)) (foot y)
            (mfderiv (𝓡 2) (𝓡 2) foot y v)
          = mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (Wp z)) (S.L.γ j t)
            (mfderiv (𝓡 2) (𝓡 2) foot y v) := by
        rw [hfoot']
      have hB : mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (Wp z)) (S.L.γ j t)
            (mfderiv (𝓡 2) (𝓡 2) foot y v)
          = mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (Wp z)) (S.L.γ j t)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (S.L.γ j) t s₀) :=
        congrArg (fun w => mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => proj2 (Wp z))
          (S.L.γ j t) w) hs₀.symm
      rw [hA, hB]
      exact hlevel
    -- the value of the picture and the non-radiality of the parked circle
    have hval := mobiusTwisted_far_proj (D := D) (S := S) (ε := ε) (εp := εp) (Dp := Dp)
      hε hε19 hεp hεp19 hj hyD hfoot
    have hzsub : proj2 (mobiusTwisted D η S ε εp Dp y)
          - (proj2 (farPos S.n j) + (Dp : ℂ) * Complex.I) = proj2 (Work.Drive.N2.ang t) := by
      rw [hval]
      ring
    have hnr : ¬ ∃ s' : ℝ, deriv (fun u : ℝ => proj2 (farCurve S.n j u)) t
        = s' • (proj2 (mobiusTwisted D η S ε εp Dp y)
            - (proj2 (farPos S.n j) + (Dp : ℂ) * Complex.I)) := by
      have h0 := Work.Drive.N2C.farCurve_deriv_not_radial S.n j t
      rw [Work.Drive.N2C.proj2_farCurve_sub S.n j t, ← hzsub] at h0
      exact h0
    refine mfr_not_smul_of_not_smul (l := s₀)
      (d := deriv (fun u : ℝ => proj2 (farCurve S.n j u)) t)
      (z := proj2 (mobiusTwisted D η S ε εp Dp y))
      (o := proj2 (farPos S.n j) + (Dp : ℂ) * Complex.I) hs₀ne ?_ hnr ⟨s, hs⟩
    rw [hGder, mul_comm]

end

end Work.Drive.N2Lead
