/-
Copyright: work module for the Elgindi finite-time singularity project.

# The mixed pairing identity

`Work.Blocks.IMC.mixed_pairing_identity` is the radial integration-by-parts identity that
identifies the mixed pairing

  `∫_z w z ² (∫_θ D_zG · D_z(∂_θ²G) σ)`,   `σ = thEta = sin(2θ)^{-η}`,

with

  `- ∫∫ (D_z²G + b · D_zG) · ∂_θ²G · w² σ`,   `b z = (z-3)/(1+z) = ThetaU.bcoef z`,

for `G` smooth on the open strip `(0,∞) × (-1, π/2+1)` and supported in `z ∈ [δ,R]` with
`0 < δ < R`.  Both integrands are supported in the compact set `[δ,R] × Iθ`, so all boundary
terms of the integration by parts vanish; the identity says that the radial operator
`D_z² + b D_z` is self-adjoint for the weight `w(z)² dz` (the coefficient `b` is exactly the
logarithmic derivative of `z w(z)²`).

The proof has four layers:

* elementary vanishing lemmas: every derived quantity of `G` vanishes for `z ∉ [δ,R]`;
* the one-dimensional integration by parts `z_ibp_mixed_slice` (a direct application of
  `Work.FTS.EllipticEst.ThetaU.radial_ibp_eta` to the slices, with `φ = z ∂_zG(·,θ)` and
  `ψ = ∂_θ²G(·,θ)`, the product rule converting `∂_z(z∂_zG)` into the operator `D_z² + b D_z`);
* the Fubini reduction `mixed_pairing_reduce` turning both the iterated and the product
  integrals into `θ`-iterated integrals, via the compactly supported Fubini lemmas of
  `Work.FTS.EllipticEst.ThetaU.K1Aux`;
* the assembly, integrating the slicewise identity in `θ`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.interpol_defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.ThetaU.OpenAux
import Submission.Work.FTS.EllipticEst.ThetaU.K1Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.IMC

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## Vanishing of the derived quantities off the support

A function which vanishes on the (open) complement of `[δ,R]` in the `z`-variable has all its
`z`- and `θ`-derivatives vanishing there too, since it is locally `0`. -/

theorem pz_eq_zero_of_notMem_Icc {δ R : ℝ} {F : ℝ → ℝ → ℝ}
    (h : ∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0) :
    ∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.pz F z θ = 0 := by
  intro z hz θ
  have hnb : ∀ᶠ z' in 𝓝 z, z' ∉ Set.Icc δ R :=
    isClosed_Icc.isOpen_compl.mem_nhds hz
  have hev : (fun z' : ℝ => F z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnb] with z' hz'
    exact h z' hz' θ
  show deriv (fun z' : ℝ => F z' θ) z = 0
  rw [hev.deriv_eq, deriv_const]

theorem pth_eq_zero_of_notMem_Icc {δ R : ℝ} {F : ℝ → ℝ → ℝ}
    (h : ∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0) :
    ∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.pth F z θ = 0 := by
  intro z hz θ
  have hfun : (fun θ' : ℝ => F z θ') = fun _ => (0 : ℝ) := funext fun θ' => h z hz θ'
  show deriv (fun θ' : ℝ => F z θ') θ = 0
  rw [hfun, deriv_const]

theorem Dz_eq_zero_of_notMem_Icc {δ R : ℝ} {F : ℝ → ℝ → ℝ}
    (h : ∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0) :
    ∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.Dz F z θ = 0 := by
  intro z hz θ
  show z * Work.Spaces.pz F z θ = 0
  rw [pz_eq_zero_of_notMem_Icc h z hz θ, mul_zero]

theorem pth_pth_eq_zero_of_notMem_Icc {δ R : ℝ} {F : ℝ → ℝ → ℝ}
    (h : ∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0) :
    ∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.pth (Work.Spaces.pth F) z θ = 0 :=
  pth_eq_zero_of_notMem_Icc (pth_eq_zero_of_notMem_Icc h)

theorem Dz_Dz_eq_zero_of_notMem_Icc {δ R : ℝ} {F : ℝ → ℝ → ℝ}
    (h : ∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0) :
    ∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.Dz (Work.Spaces.Dz F) z θ = 0 :=
  Dz_eq_zero_of_notMem_Icc (Dz_eq_zero_of_notMem_Icc h)

theorem Dz_pth_pth_eq_zero_of_notMem_Icc {δ R : ℝ} {F : ℝ → ℝ → ℝ}
    (h : ∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0) :
    ∀ z, z ∉ Set.Icc δ R → ∀ θ,
      Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth F)) z θ = 0 :=
  Dz_eq_zero_of_notMem_Icc (pth_pth_eq_zero_of_notMem_Icc h)

/-- Membership in `(0,δ) ∪ (R,∞)` implies being outside `[δ,R]`. -/
theorem notMem_Icc_of_lt_delta_or_gt {δ R z : ℝ} (h : (0 < z ∧ z < δ) ∨ R < z) :
    z ∉ Set.Icc δ R := by
  rcases h with ⟨-, h2⟩ | h2
  · exact fun hh => absurd hh.1 (not_le_of_gt h2)
  · exact fun hh => absurd hh.2 (not_le_of_gt h2)

/-! ## Slice smoothness -/

/-- The `z`-slice of `G`, of its `z`-derivative and of its second `θ`-derivative are smooth on
`(0,∞)` at every angle `θ ∈ Iθ`. -/
theorem slice_smooth_mixed {G : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Work.FTS.EllipticEst.ThetaU.OStrip)) :
    ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      ContDiffOn ℝ 2 (fun z => G z θ) (Set.Ioi 0)
      ∧ ContDiffOn ℝ 1 (fun z => Work.Spaces.pz G z θ) (Set.Ioi 0)
      ∧ ContDiffOn ℝ 1 (fun z => Work.Spaces.pth (Work.Spaces.pth G) z θ) (Set.Ioi 0) := by
  intro θ hθ
  have hmaps : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi 0)
      (Work.FTS.EllipticEst.ThetaU.OStrip) := by
    intro z hz
    exact ⟨hz, by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hslice2 : ContDiffOn ℝ 2 (fun z : ℝ => (z, θ)) (Set.Ioi 0) := by fun_prop
  have hslice1 : ContDiffOn ℝ 1 (fun z : ℝ => (z, θ)) (Set.Ioi 0) := by fun_prop
  have hG2 : ContDiffOn ℝ 2 (fun z : ℝ => G z θ) (Set.Ioi 0) := (hsm 2).comp hslice2 hmaps
  have hpz1 : ContDiffOn ℝ 1 (fun z : ℝ => Work.Spaces.pz G z θ) (Set.Ioi 0) := by
    have h := hG2.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)
    simpa only [Work.Spaces.pz] using h
  have hp2 : ContDiffOn ℝ 1 (fun z : ℝ => Work.Spaces.pth (Work.Spaces.pth G) z θ)
      (Set.Ioi 0) :=
    (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin (G := Work.Spaces.pth G) (n := 1)
      (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin (G := G) (n := 2) (hsm 3))).comp
      hslice1 hmaps
  exact ⟨hG2, hpz1, hp2⟩

/-! ## The one-dimensional integration by parts at fixed `θ` -/

/-- **Radial integration by parts in the mixed pairing, at fixed angle.**

Direct application of `Work.FTS.EllipticEst.ThetaU.radial_ibp_eta` with
`φ = z ∂_zG(·,θ) = D_zG(·,θ)` and `ψ = ∂_θ²G(·,θ)`: the boundary terms vanish because `φ` and
`ψ` are supported in `[δ,R]`, and the product rule turns `∂_z(z ∂_zG)` into
`D_z²G = z² ∂_z²G + z ∂_zG`. -/
theorem z_ibp_mixed_slice {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R) {G : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsG : ContDiffOn ℝ 2 (fun z => G z θ) (Set.Ioi 0))
    (hsψ : ContDiffOn ℝ 1 (fun z => Work.Spaces.pth (Work.Spaces.pth G) z θ) (Set.Ioi 0))
    (hsφ0 : ∀ z, (0 < z ∧ z < δ) ∨ R < z → Work.Spaces.pz G z θ = 0)
    (hsψ0 : ∀ z, (0 < z ∧ z < δ) ∨ R < z → Work.Spaces.pth (Work.Spaces.pth G) z θ = 0) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (Work.Spaces.Dz G z θ * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ))
      = - ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ
              + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
             * Work.Spaces.pth (Work.Spaces.pth G) z θ) := by
  -- the `z`-derivative slice is `C¹`, so `z ↦ z ∂_zG(z,θ)` is `C¹`
  have hpz : ContDiffOn ℝ 1 (fun z : ℝ => Work.Spaces.pz G z θ) (Set.Ioi 0) := by
    have h := hsG.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)
    simpa only [Work.Spaces.pz] using h
  have hφ : ContDiffOn ℝ 1 (fun z : ℝ => z * Work.Spaces.pz G z θ) (Set.Ioi 0) :=
    contDiffOn_id.mul hpz
  -- the product rule for `z ↦ z ∂_zG(z,θ)`
  have hderivφ : ∀ z ∈ Set.Ioi (0 : ℝ),
      deriv (fun y : ℝ => y * Work.Spaces.pz G y θ) z
        = Work.Spaces.pz G z θ + z * Work.Spaces.pz (Work.Spaces.pz G) z θ := by
    intro z hz
    have hd : HasDerivAt (fun y : ℝ => Work.Spaces.pz G y θ)
        (Work.Spaces.pz (Work.Spaces.pz G) z θ) z :=
      ((hpz.differentiableOn_one).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
    have h0 : HasDerivAt ((fun y : ℝ => y) * (fun y : ℝ => Work.Spaces.pz G y θ))
        (Work.Spaces.pz G z θ + z * Work.Spaces.pz (Work.Spaces.pz G) z θ) z := by
      simpa only [one_mul] using (hasDerivAt_id' (x := z)).mul hd
    have h1 : HasDerivAt (fun y : ℝ => y * Work.Spaces.pz G y θ)
        (Work.Spaces.pz G z θ + z * Work.Spaces.pz (Work.Spaces.pz G) z θ) z :=
      h0.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun y => by simp only [Pi.mul_apply]))
    exact h1.deriv
  -- the integration by parts from `OpenAux`
  have hmain := Work.FTS.EllipticEst.ThetaU.radial_ibp_eta (δ := δ) (R := R) hδ hδR
    (φ := fun z : ℝ => z * Work.Spaces.pz G z θ)
    (ψ := fun z : ℝ => Work.Spaces.pth (Work.Spaces.pth G) z θ) hφ hsψ
    (fun z hz => by rw [hsφ0 z hz]; ring) hsψ0
  -- rewrite the left-hand side
  have hL : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (Work.Spaces.Dz G z θ * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ))
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (z * Work.Spaces.pz G z θ)
          * (z * deriv (fun y : ℝ => Work.Spaces.pth (Work.Spaces.pth G) y θ) z) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    ring
  -- rewrite the right-hand side
  have hR : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (-(z * deriv (fun y : ℝ => y * Work.Spaces.pz G y θ) z)
            - (z - 3) / (1 + z) * (z * Work.Spaces.pz G z θ))
          * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
      = - ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ
              + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
             * Work.Spaces.pth (Work.Spaces.pth G) z θ) := by
    rw [show (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (-(z * deriv (fun y : ℝ => y * Work.Spaces.pz G y θ) z)
              - (z - 3) / (1 + z) * (z * Work.Spaces.pz G z θ))
            * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
        = ∫ z in Work.Spaces.Iz, - ((Work.Spaces.w z) ^ 2
          * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ
              + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
             * Work.Spaces.pth (Work.Spaces.pth G) z θ)) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_),
      MeasureTheory.integral_neg]
    rcases eq_or_ne z 0 with rfl | hz0
    · have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
      rw [hw0]; ring
    · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      have hd := hderivφ z hzpos
      have hDz : Work.Spaces.Dz (Work.Spaces.Dz G) z θ
          = z * (Work.Spaces.pz G z θ + z * Work.Spaces.pz (Work.Spaces.pz G) z θ) := by
        show z * Work.Spaces.pz (Work.Spaces.Dz G) z θ = _
        rw [show Work.Spaces.pz (Work.Spaces.Dz G) z θ
            = deriv (fun y : ℝ => y * Work.Spaces.pz G y θ) z from rfl, hd]
      rw [hDz, hd]
      simp only [Work.Spaces.Dz, Work.FTS.EllipticEst.ThetaU.bcoef]
      ring_nf
  rw [hL, hmain, hR]

/-! ## Continuity on the open strip of the two pairing integrands -/

theorem continuousOn_OStrip_Dz_mul_Dzpthpth {G : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Work.FTS.EllipticEst.ThetaU.OStrip)) :
    ContinuousOn (Function.uncurry (fun z θ => Work.Spaces.Dz G z θ
      * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ))
      (Work.FTS.EllipticEst.ThetaU.OStrip) := by
  have hA : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.Dz G))
      (Work.FTS.EllipticEst.ThetaU.OStrip) :=
    Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (G := G) (n := 1) (hsm 2)
  have hB : ContDiffOn ℝ 1
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G))))
      (Work.FTS.EllipticEst.ThetaU.OStrip) :=
    Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (n := 1)
      (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin (G := Work.Spaces.pth G) (n := 2)
        (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin (G := G) (n := 3) (hsm 4)))
  exact hA.continuousOn.mul hB.continuousOn

theorem continuousOn_OStrip_F2 {G : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Work.FTS.EllipticEst.ThetaU.OStrip)) :
    ContinuousOn (Function.uncurry (fun z θ => (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
      + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
        * Work.Spaces.pth (Work.Spaces.pth G) z θ))
      (Work.FTS.EllipticEst.ThetaU.OStrip) := by
  have hdd : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dz G)))
      (Work.FTS.EllipticEst.ThetaU.OStrip) :=
    Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (n := 1)
      (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (G := G) (n := 2) (hsm 3))
  have hd : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.Dz G))
      (Work.FTS.EllipticEst.ThetaU.OStrip) :=
    Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (G := G) (n := 1) (hsm 2)
  have hp2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth G)))
      (Work.FTS.EllipticEst.ThetaU.OStrip) :=
    Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin (n := 1)
      (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin (G := G) (n := 2) (hsm 3))
  have hb : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.ThetaU.bcoef p.1)
      (Work.FTS.EllipticEst.ThetaU.OStrip) := by
    have h1 : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.ThetaU.bcoef z) (Set.Ioi 0) := by
      rw [show Work.FTS.EllipticEst.ThetaU.bcoef = fun z : ℝ => (z - 3) / (1 + z) from rfl]
      refine ContinuousOn.div ((continuous_id.sub continuous_const).continuousOn)
        ((continuous_const.add continuous_id).continuousOn) ?_
      intro z hz
      have hz' : (0 : ℝ) < z := hz
      exact ne_of_gt (by linarith)
    exact h1.comp continuous_fst.continuousOn (fun p hp => hp.1)
  exact (hdd.continuousOn.add (hb.mul hd.continuousOn)).mul hp2.continuousOn

/-! ## From the strip to the quadrant, and bounds on the box -/

/-- A function continuous on the open strip `(0,∞) × (-1,π/2+1)` is continuous on the open
quadrant `(0,∞) × (0,π/2)` and bounded on the compact box `[δ,R] × Iθ`. -/
theorem continuousOn_quadrant_of_OStrip {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R) {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) (Work.FTS.EllipticEst.ThetaU.OStrip)) :
    ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
      ∧ ∃ Mb : ℝ, 0 ≤ Mb ∧ ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |F z θ| ≤ Mb := by
  have hbox : Set.Icc δ R ×ˢ Work.Spaces.Iθ ⊆ Work.FTS.EllipticEst.ThetaU.OStrip := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    exact ⟨lt_of_lt_of_le hδ hz.1, by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  refine ⟨hF.mono ?_, ?_⟩
  · rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    exact ⟨hz, by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  · obtain ⟨M, hM0, hM⟩ :=
      Work.FTS.EllipticEst.ThetaU.exists_bound_box hδ hδR (hF.mono hbox)
    exact ⟨M, hM0, hM⟩

/-! ## The Fubini reduction -/

/-- Vanishing of the first pairing integrand off the support. -/
theorem vanish_F1 {δ R : ℝ} {G : ℝ → ℝ → ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0) :
    ∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.Dz G z θ
      * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ = 0 := by
  intro z hz θ
  rw [Dz_eq_zero_of_notMem_Icc (F := G) hsupp z hz θ,
    Dz_pth_pth_eq_zero_of_notMem_Icc (F := G) hsupp z hz θ, mul_zero]

/-- Vanishing of the second pairing integrand off the support. -/
theorem vanish_F2 {δ R : ℝ} {G : ℝ → ℝ → ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0) :
    ∀ z, z ∉ Set.Icc δ R → ∀ θ, (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
      + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
        * Work.Spaces.pth (Work.Spaces.pth G) z θ = 0 := by
  intro z hz θ
  rw [Dz_Dz_eq_zero_of_notMem_Icc (F := G) hsupp z hz θ,
    Dz_eq_zero_of_notMem_Icc (F := G) hsupp z hz θ,
    pth_pth_eq_zero_of_notMem_Icc (F := G) hsupp z hz θ]
  ring

/-- **The Fubini reduction of the mixed pairing identity**: both the iterated `z`-integral on
the left and the product integral on the right of `mixed_pairing_identity` are rewritten as
`θ`-iterated integrals. -/
theorem mixed_pairing_reduce {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R) {G : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Work.FTS.EllipticEst.ThetaU.OStrip))
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
            * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
            * Work.FTS.EllipticEst.thEta θ))
      = ∫ θ in Work.Spaces.Iθ,
          (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (Work.Spaces.Dz G z θ
              * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ))
          * Work.FTS.EllipticEst.thEta θ
    ∧ (∫ p : ℝ × ℝ,
          ((Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
              + Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2)
            * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2
            * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ θ in Work.Spaces.Iθ,
          (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ
                + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
               * Work.Spaces.pth (Work.Spaces.pth G) z θ))
          * Work.FTS.EllipticEst.thEta θ := by
  have hc1 := continuousOn_OStrip_Dz_mul_Dzpthpth hsm
  have hc2 := continuousOn_OStrip_F2 hsm
  obtain ⟨hF1c, M1, -, hF1b⟩ :=
    continuousOn_quadrant_of_OStrip (δ := δ) (R := R) hδ hδR hc1
  obtain ⟨hF2c, M2, -, hF2b⟩ :=
    continuousOn_quadrant_of_OStrip (δ := δ) (R := R) hδ hδR hc2
  have hF1v := vanish_F1 (δ := δ) (R := R) hsupp
  have hF2v := vanish_F2 (δ := δ) (R := R) hsupp
  refine ⟨?_, ?_⟩
  · exact Work.FTS.EllipticEst.ThetaU.fubini_w_thEta (δ := δ) (R := R) hδ hF1c hF1v ⟨M1, hF1b⟩
  · have h1 := Work.FTS.EllipticEst.ThetaU.iterated_eq_prod (δ := δ) (R := R) hδ hF2c hF2v
      ⟨M2, hF2b⟩
    have h2 := Work.FTS.EllipticEst.ThetaU.fubini_w_thEta (δ := δ) (R := R) hδ hF2c hF2v
      ⟨M2, hF2b⟩
    rw [show (∫ p : ℝ × ℝ,
          ((Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
              + Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2)
            * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2
            * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        = ∫ p : ℝ × ℝ, (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
            * ((Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
                + Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2)
               * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => by ring)),
      ← h1, h2]

/-! ## The mixed pairing identity -/

theorem mixed_pairing_identity {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R) {G : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G) (Work.FTS.EllipticEst.ThetaU.OStrip))
    (h0 : ∀ z, G z 0 = 0) (hπ : ∀ z, G z (Real.pi / 2) = 0)
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
          * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
          * Work.FTS.EllipticEst.thEta θ))
      = - ∫ p : ℝ × ℝ,
          ((Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
              + Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2)
            * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2
            * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  obtain ⟨hredL, hredR⟩ := mixed_pairing_reduce (δ := δ) (R := R) hδ hδR hsm hsupp
  rw [hredL, hredR]
  -- the two `θ`-iterated integrals, with the slicewise integration by parts in between
  let P : ℝ → ℝ := fun θ => ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
    * (Work.Spaces.Dz G z θ * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
  let Q : ℝ → ℝ := fun θ => ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
    * ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ
        + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
       * Work.Spaces.pth (Work.Spaces.pth G) z θ)
  change (∫ θ in Work.Spaces.Iθ, P θ * Work.FTS.EllipticEst.thEta θ)
      = - ∫ θ in Work.Spaces.Iθ, Q θ * Work.FTS.EllipticEst.thEta θ
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, P θ = -Q θ := by
    intro θ hθ
    obtain ⟨hs1, -, hs3⟩ := slice_smooth_mixed (G := G) hsm θ hθ
    have hφ0 : ∀ z : ℝ, (0 < z ∧ z < δ) ∨ R < z → Work.Spaces.pz G z θ = 0 :=
      fun z hz => pz_eq_zero_of_notMem_Icc (F := G) hsupp z
        (notMem_Icc_of_lt_delta_or_gt hz) θ
    have hψ0 : ∀ z : ℝ, (0 < z ∧ z < δ) ∨ R < z →
        Work.Spaces.pth (Work.Spaces.pth G) z θ = 0 :=
      fun z hz => pth_pth_eq_zero_of_notMem_Icc (F := G) hsupp z
        (notMem_Icc_of_lt_delta_or_gt hz) θ
    exact z_ibp_mixed_slice (δ := δ) (R := R) (G := G) (θ := θ) hδ hδR hs1 hs3 hφ0 hψ0
  have hcongr : (∫ θ in Work.Spaces.Iθ, P θ * Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Work.Spaces.Iθ, -(Q θ * Work.FTS.EllipticEst.thEta θ) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ hθ => by rw [hpt θ hθ]; ring)
  rw [hcongr, MeasureTheory.integral_neg]

end Work.Blocks.IMC
