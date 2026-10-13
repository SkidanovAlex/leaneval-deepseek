import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.RegQ.pthU_slot_alg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `z`-derivative of the `U`-slot of the elliptic part, at a point

`Uop α Ψ = -3Ψ - α z ∂_z Ψ` and `PhiTil α F Φ = Φ - (1/(4α)) sin 2θ · L₁₂(F)`, so on the open
quadrant the `z`-derivative of the `U`-slot `Uop α (PhiTil α F Φ)/sin 2θ` splits into the mixed
jets of `Φ` and the angular moments of `F`:

`D_z (Uop α (PhiTil α F Φ)/sin 2θ)(z,θ)`
  `= (-3 D_zΦ - α D_z²Φ)/sin 2θ - (3/(4α)) Qang F 0 z - (1/4) Qang F 1 z`,

using the tower `z ∂_z L₁₂(F) = -Qang F 0` and `z ∂_z (Qang F 0) = Qang F 1`.
-/

noncomputable section

namespace Work.FTS_StreamBdry.SB4

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

theorem Dz_Epart_eq {α : ℝ} (hα : α ≠ 0) {F Φ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hΦ : ContDiffOn ℝ 2 (Function.uncurry Φ) Work.FTS.EllipticEst.Q0)
    (hL : ∀ z' ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z'' => Work.Construction.L12 F z'') (-(Work.Elliptic.Qang F 0 z' / z')) z')
    (hQ : HasDerivAt (Work.Elliptic.Qang F 0) (Work.Elliptic.Qang F 1 z / z) z) :
    Work.Spaces.Dz (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ
        / Work.Construction.s2 θ) z θ
      = (-3 * Work.Spaces.mixed 1 0 Φ z θ - α * Work.Spaces.mixed 2 0 Φ z θ)
          / Work.Construction.s2 θ
        - (3 / (4 * α)) * Work.Elliptic.Qang F 0 z - (1 / 4) * Work.Elliptic.Qang F 1 z := by
  have hSpos : 0 < Work.Construction.s2 θ := by
    rw [Work.Construction.s2]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hSne : Work.Construction.s2 θ ≠ 0 := ne_of_gt hSpos
  -- `z`-slices of `Φ` and of its `z`-partial
  have hsliceΦ : ContDiffOn ℝ 2 (fun z' => Φ z' θ) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_z_fin hΦ hθ
  have hpzΦc : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz Φ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pz_fin Work.FTS.EllipticEst.isOpen_Q0 hΦ
  have hslicepzΦ : ContDiffOn ℝ 1 (fun z' => Work.Spaces.pz Φ z' θ) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_z_fin hpzΦc hθ
  have hdΦ : DifferentiableAt ℝ (fun z' => Φ z' θ) z :=
    (hsliceΦ.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hdpzΦ : DifferentiableAt ℝ (fun z' => Work.Spaces.pz Φ z' θ) z :=
    (hslicepzΦ.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  -- the `z`-derivative data of `L₁₂(F)` and of `Qang F 0`
  have hLd : ∀ z' ∈ Set.Ioi (0 : ℝ),
      deriv (fun z'' => Work.Construction.L12 F z'') z'
        = -(Work.Elliptic.Qang F 0 z' / z') := fun z' hz' => (hL z' hz').deriv
  have hLdiff : ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z'' => Work.Construction.L12 F z'') z' :=
    fun z' hz' => (hL z' hz').differentiableAt
  have hevDerivL : (deriv (fun z'' => Work.Construction.L12 F z''))
      =ᶠ[𝓝 z] fun z' => -(Work.Elliptic.Qang F 0 z' / z') := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact hLd z' hz'
  have hdDerivL : DifferentiableAt ℝ (deriv (fun z'' => Work.Construction.L12 F z'')) z :=
    (hQ.differentiableAt.div differentiableAt_id (ne_of_gt hz)).neg.congr_of_eventuallyEq hevDerivL
  have hevZL : (fun z' => z' * deriv (fun z'' => Work.Construction.L12 F z'') z')
      =ᶠ[𝓝 z] fun z' => -(Work.Elliptic.Qang F 0 z') := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    have hz'ne : z' ≠ 0 := ne_of_gt hz'
    rw [hLd z' hz', mul_neg, neg_inj]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hz'ne]
  have hder2L : deriv (fun z' => z' * deriv (fun z'' => Work.Construction.L12 F z'') z') z
      = -(Work.Elliptic.Qang F 1 z / z) := by
    rw [hevZL.deriv_eq]
    exact hQ.neg.deriv
  -- the splitting of the `z`-derivative of `PhiTil`
  have hpzΨ : ∀ z' ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ
        = Work.Spaces.pz Φ z' θ
          - ((1 / (4 * α)) * Work.Construction.s2 θ)
              * deriv (fun z'' => Work.Construction.L12 F z'') z' := by
    intro z' hz'
    have h1 : DifferentiableAt ℝ (fun u => Φ u θ) z' :=
      (hsliceΦ.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz')
    have h2 : DifferentiableAt ℝ (fun u => Work.Construction.L12 F u) z' := hLdiff z' hz'
    have hfun : (fun u => Work.Construction.PhiTil α F Φ u θ)
        = (fun u => Φ u θ)
          - (fun u => ((1 / (4 * α)) * Work.Construction.s2 θ) * Work.Construction.L12 F u) := by
      funext u
      simp only [Pi.sub_apply, Work.Construction.PhiTil, Work.Construction.Theta]
    have hA : deriv (fun u => Φ u θ) z' = Work.Spaces.pz Φ z' θ := rfl
    have hB : deriv (fun u => ((1 / (4 * α)) * Work.Construction.s2 θ) * Work.Construction.L12 F u) z'
        = ((1 / (4 * α)) * Work.Construction.s2 θ)
            * deriv (fun z'' => Work.Construction.L12 F z'') z' :=
      deriv_const_mul _ h2
    rw [Work.Spaces.pz, hfun, deriv_sub h1 (h2.const_mul _), hA, hB]
  have hdΨ : DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α F Φ z' θ) z := by
    have hfun : (fun z' => Work.Construction.PhiTil α F Φ z' θ)
        = (fun z' => Φ z' θ)
          - (fun z' => ((1 / (4 * α)) * Work.Construction.s2 θ)
              * Work.Construction.L12 F z') := by
      funext u
      simp only [Pi.sub_apply, Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hfun]
    exact hdΦ.sub ((hLdiff z hz).const_mul _)
  have hderΨ : deriv (fun z' => Work.Construction.PhiTil α F Φ z' θ) z
      = Work.Spaces.pz Φ z θ
        - ((1 / (4 * α)) * Work.Construction.s2 θ)
            * deriv (fun z'' => Work.Construction.L12 F z'') z :=
    hpzΨ z hz
  -- the second-order splitting
  have hev2 : (fun z' => z' * Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ)
      =ᶠ[𝓝 z] fun z' => z' * Work.Spaces.pz Φ z' θ
        - ((1 / (4 * α)) * Work.Construction.s2 θ)
            * (z' * deriv (fun z'' => Work.Construction.L12 F z'') z') := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    rw [hpzΨ z' hz']
    ring
  have hd2Ψ : DifferentiableAt ℝ
      (fun z' => z' * Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ) z :=
    ((differentiableAt_id.mul hdpzΦ).sub
      (((differentiableAt_id.mul hdDerivL).const_mul
        ((1 / (4 * α)) * Work.Construction.s2 θ)))).congr_of_eventuallyEq hev2
  have hder2Ψ : deriv (fun z' => z' * Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ) z
      = Work.Spaces.pz (Work.Spaces.Dz Φ) z θ
        - ((1 / (4 * α)) * Work.Construction.s2 θ)
            * deriv (fun z' => z' * deriv (fun z'' => Work.Construction.L12 F z'') z') z := by
    rw [hev2.deriv_eq]
    have hdA : DifferentiableAt ℝ (fun z' => z' * Work.Spaces.pz Φ z' θ) z :=
      differentiableAt_id.mul hdpzΦ
    have hdC : DifferentiableAt ℝ
        (fun z' => z' * deriv (fun z'' => Work.Construction.L12 F z'') z') z :=
      differentiableAt_id.mul hdDerivL
    have hdD : DifferentiableAt ℝ (fun z' => ((1 / (4 * α)) * Work.Construction.s2 θ)
        * (z' * deriv (fun z'' => Work.Construction.L12 F z'') z')) z := hdC.const_mul _
    have hsub : deriv (fun z' => z' * Work.Spaces.pz Φ z' θ
          - ((1 / (4 * α)) * Work.Construction.s2 θ)
              * (z' * deriv (fun z'' => Work.Construction.L12 F z'') z')) z
        = deriv (fun z' => z' * Work.Spaces.pz Φ z' θ) z
          - deriv (fun z' => ((1 / (4 * α)) * Work.Construction.s2 θ)
              * (z' * deriv (fun z'' => Work.Construction.L12 F z'') z')) z :=
      (hdA.hasDerivAt.sub hdD.hasDerivAt).deriv
    have hpzA : deriv (fun z' => z' * Work.Spaces.pz Φ z' θ) z
        = Work.Spaces.pz (Work.Spaces.Dz Φ) z θ := rfl
    have hB : deriv (fun z' => ((1 / (4 * α)) * Work.Construction.s2 θ)
          * (z' * deriv (fun z'' => Work.Construction.L12 F z'') z')) z
        = ((1 / (4 * α)) * Work.Construction.s2 θ)
            * deriv (fun z' => z' * deriv (fun z'' => Work.Construction.L12 F z'') z') z :=
      deriv_const_mul _ hdC
    rw [hsub, hpzA, hB]
  -- the `D_z`-derivative of the `U`-slot
  have hUslot : Work.Spaces.Dz (fun z θ => Work.Construction.Uop α
        (Work.Construction.PhiTil α F Φ) z θ / Work.Construction.s2 θ) z θ
      = z * deriv (fun z' => Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z' θ) z
          / Work.Construction.s2 θ := by
    simp only [Work.Spaces.Dz, Work.Spaces.pz, deriv_div_const]
    ring
  have hUop : deriv (fun z' => Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z' θ) z
      = -3 * deriv (fun z' => Work.Construction.PhiTil α F Φ z' θ) z
        - α * deriv (fun z' => z' * Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ) z := by
    have hfun : (fun z' => Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z' θ)
        = fun z' => -3 * Work.Construction.PhiTil α F Φ z' θ
            - α * (z' * Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ) := by
      funext z'
      simp only [Work.Construction.Uop]
      ring
    have hA : deriv (fun z' => -3 * Work.Construction.PhiTil α F Φ z' θ) z
        = -3 * deriv (fun z' => Work.Construction.PhiTil α F Φ z' θ) z :=
      deriv_const_mul (-3) hdΨ
    have hB : deriv (fun z' => α * (z' * Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ)) z
        = α * deriv (fun z' => z' * Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ) z :=
      deriv_const_mul α hd2Ψ
    rw [hfun]
    rw [show (fun z' => -3 * Work.Construction.PhiTil α F Φ z' θ
          - α * (z' * Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ))
        = (fun z' => -3 * Work.Construction.PhiTil α F Φ z' θ)
          - (fun z' => α * (z' * Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ))
        from rfl]
    rw [deriv_sub (hdΨ.const_mul (-3)) (hd2Ψ.const_mul α), hA, hB]
  -- the two `z`-normalisations
  have hpzA : Work.Spaces.pz Φ z θ = Work.Spaces.mixed 1 0 Φ z θ / z := by
    show Work.Spaces.pz Φ z θ = (z * Work.Spaces.pz Φ z θ) / z
    rw [mul_comm, mul_div_cancel_right₀ _ (ne_of_gt hz)]
  have hpzB : Work.Spaces.pz (Work.Spaces.Dz Φ) z θ = Work.Spaces.mixed 2 0 Φ z θ / z := by
    show Work.Spaces.pz (Work.Spaces.Dz Φ) z θ = (z * Work.Spaces.pz (Work.Spaces.Dz Φ) z θ) / z
    rw [mul_comm, mul_div_cancel_right₀ _ (ne_of_gt hz)]
  rw [hUslot, hUop, hderΨ, hder2Ψ, hder2L, hLd z hz, hpzA, hpzB]
  field_simp
  ring

end Work.FTS_StreamBdry.SB4
