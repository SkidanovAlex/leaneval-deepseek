import Mathlib
import Submission.Work.Drive.N2C.mfrFootPlumbing
import Submission.Work.Drive.N2Lead.mobiusUpperFootKit
import Submission.Work.Drive.N2Lead.arcZ_re_strictMono
import Submission.Work.Drive.N2Lead.twistToolkit
import Submission.Work.Drive.N2Lead.mobiusUpperFarRate
import Submission.Work.Drive.N2C.mobiusPinCurveRow
import Submission.Work.Drive.N2C.arcImmersion
import Submission.Work.Drive.N2Lead.modelPicRate
import Submission.Work.Compat.MFDerivCongrV433

/-!
# The pin piece of the twisted Möbius upper picture

At the upper level `f = f p + 3η/2`, a point `y` outside the model region whose foot lands on the
*upper pinned arc* `L.γ i (τU w)` of the anchor level has its twisted Möbius picture equal to the
pushed, twisted model arc `G w` at the parameter `w`, and the derivative of the picture along any
non-zero `ker df`-direction is a *non-zero real multiple* of `deriv G w`; since the curve `G` has a
non-vanishing angular rate (`hcurve`), the picture is never radially aligned with its tangent.

The reduction uses the *model arc point* `arcUpPt D lam0 ηs` as a local parametrisation of the
anchor level: it is a `C^∞` immersion (proved in `N2C/arcImmersion.lean`), it agrees with
`L.γ i (τU ·)` on the closed pin interval (`MobiusShape.hZuPt`), and the picture of the arc point is
`G`.  Because the shape data are stated on a *closed* interval, the identification of derivatives
uses the fact that a differentiable function's derivative at an endpoint of an interval is
determined by its values on that interval (`mfr_deriv_eq_of_eqOn_Icc`).
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-! ## Two tools on the real line -/

/-- If `D` vanishes on `Icc a b` (`a < b`) and is differentiable at `w ∈ Icc a b` with `D w = 0`,
then `deriv D w = 0`: the difference quotient vanishes along the side of `w` inside the interval,
while the two-sided limit exists. -/
lemma mfr_deriv_eq_zero_of_eqOn_Icc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : ℝ → F} {a b w : ℝ} (hab : a < b) (hw : w ∈ Set.Icc a b)
    (h : ∀ u ∈ Set.Icc a b, D u = 0) (hd : DifferentiableAt ℝ D w) (hw0 : D w = 0) :
    deriv D w = 0 := by
  have hder : HasDerivAt D (deriv D w) w := hd.hasDerivAt
  rcases lt_or_eq_of_le hw.2 with hwb | hwb
  · have hδ : (0:ℝ) < b - w := sub_pos.mpr hwb
    have hev : (fun t : ℝ => t⁻¹ • (D (w + t) - D w)) =ᶠ[𝓝[>] (0:ℝ)] (fun _ : ℝ => (0:F)) := by
      filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
      have hwt : w + t ∈ Set.Icc a b := ⟨by linarith [hw.1, ht.1], by linarith [ht.2]⟩
      rw [h (w + t) hwt, hw0, sub_self, smul_zero]
    have h0 : Tendsto (fun t : ℝ => t⁻¹ • (D (w + t) - D w)) (𝓝[>] (0:ℝ)) (𝓝 (0:F)) :=
      Tendsto.congr' hev.symm tendsto_const_nhds
    exact tendsto_nhds_unique hder.tendsto_slope_zero_right h0
  · have hwa : a < w := by rw [hwb]; exact hab
    have hδ : (0:ℝ) < w - a := sub_pos.mpr hwa
    have hev : (fun t : ℝ => t⁻¹ • (D (w + t) - D w)) =ᶠ[𝓝[<] (0:ℝ)] (fun _ : ℝ => (0:F)) := by
      filter_upwards [Ioo_mem_nhdsLT (show -(w - a) < (0:ℝ) by linarith)] with t ht
      have hwt : w + t ∈ Set.Icc a b := ⟨by linarith [ht.1], by linarith [ht.2, hwb]⟩
      rw [h (w + t) hwt, hw0, sub_self, smul_zero]
    have h0 : Tendsto (fun t : ℝ => t⁻¹ • (D (w + t) - D w)) (𝓝[<] (0:ℝ)) (𝓝 (0:F)) :=
      Tendsto.congr' hev.symm tendsto_const_nhds
    exact tendsto_nhds_unique hder.tendsto_slope_zero_left h0

/-- **Agreement on a closed interval determines the derivative at every point of it.**  If two
functions agree on `Icc a b` (`a < b`) and are both differentiable at `w ∈ Icc a b`, then their
derivatives at `w` agree. -/
lemma mfr_deriv_eq_of_eqOn_Icc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g₁ g₂ : ℝ → F} {a b w : ℝ} (hab : a < b) (hw : w ∈ Set.Icc a b)
    (h : ∀ u ∈ Set.Icc a b, g₁ u = g₂ u)
    (h₁ : DifferentiableAt ℝ g₁ w) (h₂ : DifferentiableAt ℝ g₂ w) :
    deriv g₁ w = deriv g₂ w := by
  have hsub : deriv (g₁ - g₂) w = 0 :=
    mfr_deriv_eq_zero_of_eqOn_Icc hab hw
      (fun u hu => by simp only [Pi.sub_apply]; rw [h u hu, sub_self]) (h₁.sub h₂)
      (by simp only [Pi.sub_apply]; rw [h w hw, sub_self])
  rw [deriv_sub h₁ h₂] at hsub
  exact sub_eq_zero.mp hsub

/-- For a function `g : ℝ → F` into a normed space, the manifold derivative along `1` is the
classical derivative. -/
lemma mfr_mfderiv_one_eq_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ → F) (w : ℝ) :
    mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,F) g w 1 = deriv g w := by
  rw [mfderiv_eq_fderiv]
  calc (fderiv ℝ g w) 1 = (fderiv ℝ g w) ((1:ℝ) • (1:ℝ)) := by rw [one_smul]
    _ = (1:ℝ) • (fderiv ℝ g w) 1 := by rw [map_smul]
    _ = deriv g w := by rw [fderiv_apply_one_eq_deriv, one_smul]

/-- **The chain rule for a curve in a manifold**: the derivative of `F ∘ c` at `w` is the
manifold derivative of `F` at `c w` evaluated at the velocity of `c`. -/
lemma mfr_deriv_comp_curve {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {F : M → F'} {c : ℝ → M} {w : ℝ}
    (hF : MDifferentiableAt (𝓡 2) 𝓘(ℝ,F') F (c w))
    (hc : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) c w) :
    deriv (fun u : ℝ => F (c u)) w
      = (mfderiv (𝓡 2) 𝓘(ℝ,F') F (c w)) (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) c w 1) := by
  have h := mfderiv_comp_apply (I := 𝓘(ℝ,ℝ)) (I' := 𝓡 2) (I'' := 𝓘(ℝ,F')) w
    (f := c) (g := F) hF hc (1 : ℝ)
  have h' : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,F') (fun u : ℝ => F (c u)) w 1
      = (mfderiv (𝓡 2) 𝓘(ℝ,F') F (c w)) (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) c w 1) := h
  rw [mfr_mfderiv_one_eq_deriv] at h'
  exact h'

/-- The imaginary part of `star z * d` is the determinant `z.re * d.im - z.im * d.re`. -/
lemma mfr_star_mul_im_eq (z d : ℂ) : (star z * d).im = z.re * d.im - z.im * d.re := by
  have h : (star z : ℂ) = (⟨z.re, -z.im⟩ : ℂ) := by
    apply Complex.ext <;> simp
  rw [h, Complex.mul_im]
  ring


theorem mfrPinPiece {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (S : Work.Drive.N2Lead.MobiusPacket D η) (hshape : Work.Drive.N2C.MobiusShape D η S)
    {ε εp Dp : ℝ} (hε : 0 < ε) (hεp : 0 < εp) (hDp : 0 ≤ Dp)
    {y : M} {w c₀ : ℝ} (hy : f y = f p + 3 * η / 2)
    (hyD : y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j))
      S.Z (39 / 20))
    (hfoot : Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y = S.L.γ S.i (hshape.tauU w))
    (hc₀ : 0 < c₀) (hc₀w : c₀ ≤ |w|) (hw : |w| ≤ 99 / 50)
    (hεre : ε ≤ (Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w).re)
    (hεpim : εp ≤ (Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w).im)
    (hcurve : ∀ u : ℝ, c₀ ≤ |u| → |u| ≤ 99 / 50 →
      ε ≤ (Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) u).re →
      εp ≤ |(Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) u).im| →
      (star (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1)
          (Work.Drive.N2.cE3 (Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) u)))))
        * deriv (fun v : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1
            (Work.Drive.N2Lead.twistX ε (-1) (Work.Drive.N2.cE3
              (Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) v))))) u).im ≠ 0) :
    (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)).im ≠ 0 ∧
      ∀ v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) y,
        mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ) f y v = 0 →
        v ≠ 0 →
        ¬ (∃ t : ℝ, mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℂ)
            (fun z : M => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z)) y v
          = t • Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)) := by

  classical
  have hηs : 0 < Work.Drive.N2.packetEta D η := Work.Drive.N2.packetEta_pos D hη
  have hηs1 : |Work.Drive.N2.packetEta D η| ≤ 1 := by
    rw [abs_of_pos hηs]
    have h := Work.Drive.N2Lead.packetEta_lt_three_eightieth D hsmall
    linarith
  have hwm : w ∈ Set.Icc (-(99 / 50 : ℝ)) (99 / 50) := abs_le.mp hw
  have hw3 : w ∈ Set.Ioo (-3 : ℝ) 3 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hw
    exact ⟨by linarith, by linarith⟩
  -- ## the local abbreviations
  let foot : M → M := Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2)
  let Wp : M → Work.Drive.N2Lead.E3 :=
    fun z => Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1) (S.C₀ z))
  let K : Work.Drive.N2Lead.E3 → ℂ :=
    fun v => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1) v))
  let G : ℝ → ℂ := fun u => K (Work.Drive.N2.cE3 (Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) u))
  let Ap : ℝ → M := fun u => Work.Drive.N2Lead.arcUpPt D S.lam0 (Work.Drive.N2.packetEta D η) u
  let L₂ : ℝ → ℂ := fun u => Work.Drive.N2Lead.proj2 (Wp (Ap u))
  have hfoot' : foot y = S.L.γ S.i (hshape.tauU w) := hfoot
  -- ## 1. the value at `y`
  have hvalW : Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y
      = Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1) (S.C₀ (foot y))) :=
    Work.Drive.N2Lead.mobiusTwisted_foot (D := D) (η := η) (S := S) (ε := ε) (εp := εp)
      (Dp := Dp) hyD
  have hC0foot : S.C₀ (foot y)
      = Work.Drive.N2.cE3 (Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w) := by
    rw [hfoot', S.hC₀val (hshape.tauU w), hshape.hpolarU w hwm]
  have hvalG : Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) = G w := by
    rw [hvalW, hC0foot]
  -- ## 2. the imaginary part of the value
  have hsxw : (1 : ℝ) ≤ ((Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w).re + ε) / (2 * ε) := by
    rw [le_div_iff₀ (by linarith)]
    linarith [hεre]
  have hcosw : Real.cos (-(Real.pi * Real.smoothTransition
      (((Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w).re + ε) / (2 * ε)))) = -1 := by
    rw [Real.smoothTransition.one_of_one_le hsxw, mul_one, Real.cos_neg, Real.cos_pi]
  have hGval : G w = (⟨(Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w).re,
      -(Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w).im - Dp⟩ : ℂ) := by
    show Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1)
        (Work.Drive.N2.cE3 (Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w))))
      = (⟨(Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w).re,
          -(Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w).im - Dp⟩ : ℂ)
    rw [Work.Drive.N2Lead.proj2, Work.Drive.N2Lead.pushY_apply_zero, Work.Drive.N2Lead.pushY_apply_one,
      twistX_neg_one_cE3_zero, twistX_neg_one_cE3_one, hcosw]
    simp only [mul_neg, mul_one]
    congr 1
    exact pushProf_one_eq_sub hεp (by linarith [hεpim])
  have hGim : (G w).im ≠ 0 := by
    have hzpos : 0 < (Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w).im :=
      Work.Drive.N2Lead.ReStrictMono.im_arcZ_pos hηs w
    intro h0
    rw [hGval] at h0
    have h1 : (-(Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w).im - Dp) = 0 := by
      simpa using h0
    linarith
  -- the curve row at `w`
  have hc : (star (G w) * deriv G w).im ≠ 0 := by
    have h := hcurve w hc₀w hw hεre (le_trans hεpim (le_abs_self _))
    simpa only [G, K] using h
  -- ## 3. the picture near `y` is the pushed park picture of the foot
  obtain ⟨hfootsm0, hfootinj, hfootimm⟩ :=
    Work.Drive.N2.footMap_rows_noLaw (f := f) (Φ := D.Φ) (hf := hf) (hΦsm := D.hΦsm)
      (hΦ0 := D.hΦ0) (hΦcomp := D.hΦcomp) (a := f p - 3 * η / 2)
  have hfootsm : ContMDiff (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) foot := hfootsm0
  have hfootimm' : ∀ x : M, ∀ vt : TangentSpace (𝓡 2) x, mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f x vt = 0 →
      mfderiv (𝓡 2) (𝓡 2) foot x vt = 0 → vt = 0 := hfootimm
  have hyband : f y ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) :=
    ⟨by rw [hy]; linarith, by rw [hy]; linarith⟩
  have hregopen : IsOpen (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j))
      S.Z (39 / 20)) :=
    Work.Drive.N2.isOpen_saddleRegion (Work.Drive.N2Lead.isOpen_modelBall_mobius (D.φ D.j) (D.ρ D.j))
      S.hZsm
  have hycl_or_fr : y ∈ frontier (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j)
        (D.ρ D.j)) S.Z (39 / 20)) ∨
      y ∉ closure (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j))
        S.Z (39 / 20)) := by
    by_cases hfr : y ∈ frontier (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j)
      (D.ρ D.j)) S.Z (39 / 20))
    · exact Or.inl hfr
    · refine Or.inr fun hcl => hfr ?_
      rw [frontier_eq_closure_inter_closure]
      refine ⟨hcl, ?_⟩
      rw [IsClosed.closure_eq (isClosed_compl_iff.mpr hregopen)]
      exact hyD
  have hmwev : (fun z : M => Work.Drive.N2Lead.mobiusWindowDrawing D η S z) =ᶠ[𝓝 y]
      (fun z : M => S.A (foot z)) := by
    rcases hycl_or_fr with hfr | hcl
    · have h := Work.Drive.N2Lead.mfr_drawing_eventuallyEq_A (D := D) (η := η) hη hsmall S hfr hyband
      filter_upwards [h] with z hz
      exact hz
    · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hcl] with z hzcl
      rw [Work.Drive.N2Lead.mobiusWindowDrawing,
        if_neg (fun hzD => hzcl (subset_closure hzD))]
  have hmw : (fun z : M => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z))
      =ᶠ[𝓝 y] (fun z : M => Work.Drive.N2Lead.proj2 (Wp (foot z))) := by
    filter_upwards [hmwev] with z hz
    rw [Work.Drive.N2Lead.mobiusTwisted, hz, S.hAeq (foot z), Work.Drive.N2Lead.twistY_comp,
      neg_add_cancel, Work.Drive.N2Lead.twistY_zero]
  have hWpsm : ∀ z : M, ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) Wp z := fun z =>
    Work.Drive.N2Lead.mfr_contMDiffAt_pushed (D := D) (η := η) (S := S) (ε := ε) (εp := εp) (Dp := Dp) z
  have hFmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp z)) (foot y) :=
    (Work.Drive.N2Lead.proj2CLM.mdifferentiableAt).comp (foot y)
      ((hWpsm (foot y)).mdifferentiableAt (by simp))
  have hevland : (fun z : M => f (foot z)) =ᶠ[𝓝 y] (fun _ : M => f p - 3 * η / 2) := by
    rcases hycl_or_fr with hfr | hcl
    · have h := S.hlandFr y hfr hyband
      filter_upwards [h] with z hz
      exact hz
    · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hcl,
        hf.continuous.continuousAt (isOpen_Ioo.mem_nhds hyband)] with z hzcl hzf
      exact S.hfootval z (fun hzD => hzcl (subset_closure hzD)) hzf
  -- ## 4. the model arc point as a local parametrisation of the anchor level
  have hApw : Ap w = S.L.γ S.i (hshape.tauU w) := (hshape.hZuPt w hwm).symm
  have hApfoot : foot y = Ap w := hfoot'.trans hApw.symm
  have hFmdAp : MDifferentiableAt (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp z)) (Ap w) := by
    rw [← hApfoot]
    exact hFmd
  have hApmd : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) Ap w :=
    ((Work.Drive.N2C.contMDiffOn_arcUpPt D hηs hηs1 S.hlam0pos S.hlam0).contMDiffAt
      (Ioo_mem_nhds hw3.1 hw3.2)).mdifferentiableAt (by simp)
  have hballw : ‖Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w‖ < 8 :=
    Work.Drive.N2C.norm_arcZ_lt_eight hηs1 (le_of_lt (abs_lt.mpr ⟨hw3.1, hw3.2⟩))
  have hApsrc : Ap w ∈ (D.φ D.j).source := Work.Drive.N2Lead.arcUpPt_mem_source D hballw S.hlam0
  have hφmd : MDifferentiableAt (𝓡 2) (𝓡 2) (fun y : M => D.φ D.j y) (Ap w) :=
    ((D.hφ D.j).contMDiffAt ((D.φ D.j).open_source.mem_nhds hApsrc)).mdifferentiableAt (by simp)
  have hApne : mfderiv 𝓘(ℝ,ℝ) (𝓡 2) Ap w 1 ≠ 0 := by
    let F₀ : ℝ → EuclideanSpace ℝ (Fin 2) := fun u => D.φ D.j (Ap u)
    let Q : ℝ → ℂ := fun u => (S.lam0 : ℂ) * Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) u
    have hevF : F₀ =ᶠ[𝓝 w] (fun u : ℝ => Work.Drive.N2Lead.cE2 (Q u)) := by
      filter_upwards [Ioo_mem_nhds hw3.1 hw3.2] with u hu
      have hb : ‖Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) u‖ < 8 :=
        Work.Drive.N2C.norm_arcZ_lt_eight hηs1 (le_of_lt (abs_lt.mpr ⟨hu.1, hu.2⟩))
      exact Work.Drive.N2Lead.phi_arcUpPt D hb S.hlam0
    have hQderiv : HasDerivAt Q ((S.lam0 : ℂ) * (Complex.I /
        (2 * Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w))) w :=
      (Work.Drive.N2Lead.ReStrictMono.hasDerivAt_arcZ (Work.Drive.N2.packetEta D η) hηs w).const_mul
        (S.lam0 : ℂ)
    have hderC : HasDerivAt (fun u : ℝ => Work.Drive.N2Lead.cE2 (Q u))
        (Work.Drive.N2Lead.cE2 ((S.lam0 : ℂ) * (Complex.I /
          (2 * Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w)))) w := by
      have h := (Work.Drive.N2C.cE2L.hasFDerivAt).comp_hasDerivAt w hQderiv
      simpa only [Function.comp_def, Work.Drive.N2C.cE2L_apply] using h
    have hderF₀ : deriv F₀ w ≠ 0 := by
      rw [hevF.deriv_eq, hderC.deriv]
      intro h0
      have hne : ((S.lam0 : ℂ) * (Complex.I /
          (2 * Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) w))) ≠ 0 :=
        mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt S.hlam0pos))
          (div_ne_zero Complex.I_ne_zero
            (mul_ne_zero two_ne_zero (Work.Drive.N2Lead.ReStrictMono.arcZ_ne_zero_of_eta_pos hηs w)))
      refine hne (Work.Drive.N2Lead.cE2_injective ?_)
      rw [h0, ← Work.Drive.N2C.cE2L_apply (0 : ℂ), map_zero]
    have hchainF : mfderiv 𝓘(ℝ,ℝ) (𝓡 2) F₀ w 1
        = mfderiv (𝓡 2) (𝓡 2) (fun y : M => D.φ D.j y) (Ap w)
            (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) Ap w 1) :=
      mfderiv_comp_apply (I := 𝓘(ℝ,ℝ)) (I' := 𝓡 2) (I'' := 𝓡 2) w (f := Ap)
        (g := fun y : M => D.φ D.j y) hφmd hApmd 1
    intro h0
    have h1 : mfderiv 𝓘(ℝ,ℝ) (𝓡 2) F₀ w 1 = 0 := by rw [hchainF, h0, map_zero]
    exact hderF₀ (by rw [← mfr_mfderiv_one_eq_deriv]; exact h1)
  have hApker : mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (Ap w) (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) Ap w 1) = 0 := by
    have hconst : ∀ u ∈ Set.Icc (-(99 / 50 : ℝ)) (99 / 50),
        (fun u : ℝ => f (Ap u)) u = (fun _ : ℝ => f p - 3 * η / 2) u := by
      intro u hu
      show f (Ap u) = f p - 3 * η / 2
      rw [show Ap u = S.L.γ S.i (hshape.tauU u) from (hshape.hZuPt u hu).symm]
      exact S.L.val S.i (hshape.tauU u)
    have hmdFA : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun u : ℝ => f (Ap u)) w :=
      (hf.contMDiffAt.mdifferentiableAt (by simp)).comp w hApmd
    have hdiff : DifferentiableAt ℝ (fun u : ℝ => f (Ap u)) w := hmdFA.differentiableAt
    have hdiff2 : DifferentiableAt ℝ (fun _ : ℝ => f p - 3 * η / 2) w := differentiableAt_const _
    have hder : deriv (fun u : ℝ => f (Ap u)) w = 0 := by
      rw [mfr_deriv_eq_of_eqOn_Icc (by norm_num) hwm hconst hdiff hdiff2, deriv_const]
    have h1 := mfr_deriv_comp_curve (F := f) (c := Ap)
      (hf.contMDiffAt.mdifferentiableAt (by simp)) hApmd
    rw [hder] at h1
    exact h1.symm
  obtain ⟨q, hq⟩ := S.L.ker S.i (hshape.tauU w) (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) Ap w 1)
    (by rw [← hApw]; exact hApker)
  have hqne : q ≠ 0 := by
    intro h0
    refine hApne (by rw [← hq, h0]; exact map_zero _)
  have hL₂md : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) L₂ w := by
    simpa only [Function.comp_def] using hFmdAp.comp w hApmd
  have hL₂diff : DifferentiableAt ℝ L₂ w := hL₂md.differentiableAt
  have hagree : ∀ u ∈ Set.Icc (-(99 / 50 : ℝ)) (99 / 50), L₂ u = G u := by
    intro u hu
    show Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1)
        (S.C₀ (Ap u)))) = Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1
        (Work.Drive.N2Lead.twistX ε (-1) (Work.Drive.N2.cE3
          (Work.Drive.N2Lead.arcZ (Work.Drive.N2.packetEta D η) u))))
    rw [show Ap u = S.L.γ S.i (hshape.tauU u) from (hshape.hZuPt u hu).symm,
      S.hC₀val (hshape.tauU u), hshape.hpolarU u hu]
  have hGdiff : DifferentiableAt ℝ G w := by
    refine differentiableAt_of_deriv_ne_zero (𝕜 := ℝ) ?_
    intro h0
    exact hc (by rw [h0, mul_zero]; rfl)
  have hL₂der : deriv L₂ w = deriv G w :=
    mfr_deriv_eq_of_eqOn_Icc (by norm_num) hwm hagree hL₂diff hGdiff
  have hchainAp : mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp z)) (Ap w)
      (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) Ap w 1) = deriv L₂ w :=
    (mfr_deriv_comp_curve (F := fun z : M => Work.Drive.N2Lead.proj2 (Wp z)) (c := Ap) hFmdAp hApmd).symm
  -- ## 5. the derivative of the picture along `v`
  refine ⟨?_, ?_⟩
  · rw [hvalG]
    exact hGim
  · intro v hv hvne
    have hmf1 : mfderiv (𝓡 2) 𝓘(ℝ,ℂ)
          (fun z : M => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z)) y v
        = mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp (foot z))) y v :=
      DFunLike.congr_fun hmw.mfderiv_eq_v433 v
    have hchain : mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp (foot z))) y v
        = mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp z)) (foot y)
            (mfderiv (𝓡 2) (𝓡 2) foot y v) :=
      Work.Drive.N2Lead.mfr_mfderiv_proj2_comp_foot (A := Wp) hfootsm.contMDiffAt hWpsm v
    have hkerfoot : mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (foot y) (mfderiv (𝓡 2) (𝓡 2) foot y v) = 0 := by
      have h0 : mfderiv (𝓡 2) 𝓘(ℝ,ℝ) (fun z : M => f (foot z)) y v = 0 := by
        rw [hevland.mfderiv_eq_v433, mfderiv_const]
        rfl
      rw [Work.Drive.N2Lead.mfr_mfderiv_f_comp_foot hfootsm.contMDiffAt hf.contMDiffAt v] at h0
      exact h0
    obtain ⟨s₀, hs₀⟩ := S.L.ker S.i (hshape.tauU w) (mfderiv (𝓡 2) (𝓡 2) foot y v)
      (by rw [← hfoot']; exact hkerfoot)
    have hs₀ne : s₀ ≠ 0 := by
      intro h0
      refine hvne (hfootimm' y v hv ?_)
      exact hs₀.symm.trans
        ((congrArg (fun c : ℝ => mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (S.L.γ S.i) (hshape.tauU w) c) h0).trans
          (map_zero (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (S.L.γ S.i) (hshape.tauU w))))
    let Φ₁ : ℝ → ℂ := fun τ => Work.Drive.N2Lead.proj2 (Wp (S.L.γ S.i τ))
    have hderΦ : ∀ t₀ : ℝ, mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp z))
          (S.L.γ S.i (hshape.tauU w))
          (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (S.L.γ S.i) (hshape.tauU w) t₀)
        = deriv Φ₁ (hshape.tauU w) * (t₀ : ℂ) :=
      fun t₀ => Work.Drive.N2Lead.mfr_mfderiv_levelCurve_eq_deriv (L := S.L) (W := Wp)
        (fun y _ => hWpsm y) S.i (hshape.tauU w) t₀
    have hA : mfderiv (𝓡 2) 𝓘(ℝ,ℂ)
          (fun z : M => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z)) y v
        = deriv Φ₁ (hshape.tauU w) * (s₀ : ℂ) := by
      rw [hmf1, hchain, hfoot']
      have hstep : mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp z))
            (S.L.γ S.i (hshape.tauU w)) (mfderiv (𝓡 2) (𝓡 2) foot y v)
          = mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp z))
            (S.L.γ S.i (hshape.tauU w))
            (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (S.L.γ S.i) (hshape.tauU w) s₀) :=
        congrArg (fun w' => mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp z))
          (S.L.γ S.i (hshape.tauU w)) w') hs₀.symm
      exact hstep.trans (hderΦ s₀)
    have hB : deriv G w = deriv Φ₁ (hshape.tauU w) * (q : ℂ) := by
      rw [← hL₂der, ← hchainAp, hApw]
      have hstep : mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp z))
            (S.L.γ S.i (hshape.tauU w)) (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) Ap w 1)
          = mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp z))
            (S.L.γ S.i (hshape.tauU w))
            (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (S.L.γ S.i) (hshape.tauU w) q) :=
        congrArg (fun w' => mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp z))
          (S.L.γ S.i (hshape.tauU w)) w') hq.symm
      exact hstep.trans (hderΦ q)
    have hDv : mfderiv (𝓡 2) 𝓘(ℝ,ℂ)
          (fun z : M => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z)) y v
        = (s₀ / q) • deriv G w := by
      rw [hA, hB, Complex.real_smul]
      have hqC : ((q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqne
      have hs : ((s₀ / q : ℝ) : ℂ) = (s₀ : ℂ) / (q : ℂ) := by push_cast; ring
      rw [hs]
      field_simp
    rintro ⟨t, ht⟩
    refine Work.Drive.N2Lead.not_realMultiple_of_det (a := G w) (b := (s₀ / q) • deriv G w) ?_
      ⟨t, ?_⟩
    · have hfac : (G w).re * ((s₀ / q) • deriv G w).im - (G w).im * ((s₀ / q) • deriv G w).re
          = (s₀ / q) * ((star (G w) * deriv G w).im) := by
        rw [Complex.smul_im, Complex.smul_re, smul_eq_mul, smul_eq_mul, mfr_star_mul_im_eq]
        ring
      rw [hfac]
      exact mul_ne_zero (div_ne_zero hs₀ne hqne) hc
    · rw [← hDv, ht, hvalG]


end

end Work.Drive.N2C
