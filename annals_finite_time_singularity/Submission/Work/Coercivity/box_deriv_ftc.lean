/-
# The `z`-fundamental theorem of calculus on the box `(0,R) × Iθ`, with the
`sin(2θ)^{-η}` angular weight

This file proves `Work.Coercivity.box_deriv_ftc`, the identity

  `∫_{z∈(0,R)} ∫_{θ∈Iθ} ∂_z(z (D_z f(z,θ) w(z))²) · sin(2θ)^{-η}
      = ∫_{θ∈Iθ} R (D_z f(R,θ) w(R))² · sin(2θ)^{-η}`,

used in the `D_z`-coercivity chain of §6 of T. M. Elgindi, *Finite-time singularity
formation for `C^{1,α}` solutions to the incompressible Euler equations on `ℝ³`*,
Annals of Math. 194 (3) 2021.

Writing `BoxG f z θ = z (D_z f z θ · w z)²` (see `Coercivity/BoxAux`), the left-hand
side is the iterated integral of `∂_z(BoxG f)` against the angular weight.  The proof is

* the `θ`-slice identity `∫_{z∈(0,R)} ∂_z(BoxG f) z θ = BoxG f R θ` (the fundamental
  theorem of calculus, the boundary term at `z = 0` vanishing identically and in the
  limit `z → 0⁺`), which is the lemma `box_slice_ftc`;
* Fubini's theorem, licensed by the integrability of the product integrand, which the
  hypothesis `hC` (boundedness of `∂_z(BoxG f)` near `z = 0`) upgrades to a global bound
  on `(0,R) × Iθ` (`box_joint_bound`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.BoxAux
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Coercivity.box_joint_bound
import Submission.Work.Coercivity.box_slice_ftc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

theorem box_deriv_ftc (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hbd : ∀ θ ∈ Spaces.Iθ, Filter.Tendsto (fun z => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hC : ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ z ∈ Set.Ioo 0 δ, ∀ θ ∈ Spaces.Iθ,
      |deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z| ≤ C)
    {R : ℝ} (hR : 0 < R) :
    (∫ z in Set.Ioo 0 R, ∫ θ in Spaces.Iθ,
        deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
          * (Real.sin (2 * θ)) ^ (-Spaces.eta))
      = ∫ θ in Spaces.Iθ, R * (Spaces.Dz f R θ * Spaces.w R) ^ 2
          * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
  obtain ⟨M, hMpos, hMbd⟩ := box_joint_bound f hsm hC hR
  -- the angular weight and its integrability
  let p : ℝ → ℝ := fun θ => (Real.sin (2 * θ)) ^ (-Spaces.eta)
  have hp_int : IntegrableOn p Spaces.Iθ :=
    (Spaces.sin_two_rpow (-Spaces.eta) (by linarith [Spaces.eta_lt_one])
      (by linarith [Spaces.eta_nonneg])).1
  -- the integrand of the iterated integral
  let F : ℝ → ℝ → ℝ := fun z θ =>
    deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z * p θ
  have hμν : (volume.restrict (Set.Ioo (0 : ℝ) R)).prod (volume.restrict Spaces.Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict (Set.Ioo 0 R ×ˢ Spaces.Iθ) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  -- integrability of the product integrand, by domination with `M * p`
  have hdom : Integrable (fun q : ℝ × ℝ => M * p q.2)
      ((volume.restrict (Set.Ioo (0 : ℝ) R)).prod (volume.restrict Spaces.Iθ)) := by
    have h1 : Integrable (fun _ : ℝ => M) (volume.restrict (Set.Ioo (0 : ℝ) R)) :=
      integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    have h2 : Integrable p (volume.restrict Spaces.Iθ) := hp_int
    exact h1.mul_prod h2
  have hFint : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioo (0 : ℝ) R)).prod (volume.restrict Spaces.Iθ)) := by
    refine Integrable.mono' (g := fun q : ℝ × ℝ => M * p q.2) hdom ?_ ?_
    · -- a.e. strong measurability
      rw [hμν]
      have hbox : Set.Ioo (0 : ℝ) R ×ˢ Spaces.Iθ ⊆ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (π / 2 + 1) := by
        rintro ⟨z, θ⟩ hq
        exact ⟨hq.1.1, ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩⟩
      have hm1 : AEStronglyMeasurable (Function.uncurry (Spaces.pz (BoxG f)))
          ((volume : Measure (ℝ × ℝ)).restrict (Set.Ioo 0 R ×ˢ Spaces.Iθ)) :=
        ((contDiffOn_uncurry_pz_BoxG f hsm).continuousOn.mono hbox).aestronglyMeasurable
          (measurableSet_Ioo.prod measurableSet_Icc)
      have hm2 : AEStronglyMeasurable (fun q : ℝ × ℝ => p q.2)
          ((volume : Measure (ℝ × ℝ)).restrict (Set.Ioo 0 R ×ˢ Spaces.Iθ)) := by
        rw [← hμν]
        exact (Integrable.aestronglyMeasurable hp_int).comp_snd
      refine (hm1.mul hm2).congr (Filter.Eventually.of_forall (fun q => ?_))
      simp only [Function.uncurry, Pi.mul_apply, F, BoxG, Spaces.pz]
    · -- the pointwise bound
      rw [hμν]
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Icc)] with q hq
      obtain ⟨hqz, hqθ⟩ := hq
      have hpnn : 0 ≤ p q.2 :=
        Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hqθ.1])
          (by linarith [hqθ.2])) _
      have hb : |deriv (fun z' => z' * (Spaces.Dz f z' q.2 * Spaces.w z') ^ 2) q.1| ≤ M :=
        hMbd q.1 hqz q.2 hqθ
      have hnorm : ‖Function.uncurry F q‖
          = |deriv (fun z' => z' * (Spaces.Dz f z' q.2 * Spaces.w z') ^ 2) q.1| * p q.2 := by
        have hval : Function.uncurry F q
            = deriv (fun z' => z' * (Spaces.Dz f z' q.2 * Spaces.w z') ^ 2) q.1 * p q.2 := rfl
        rw [hval, Real.norm_eq_abs, abs_mul, abs_of_nonneg hpnn]
      rw [hnorm]
      exact mul_le_mul_of_nonneg_right hb hpnn
  -- Fubini
  have hswap := MeasureTheory.integral_integral_swap (μ := volume.restrict (Set.Ioo (0 : ℝ) R))
    (ν := volume.restrict Spaces.Iθ) hFint
  change (∫ z in Set.Ioo 0 R, ∫ θ in Spaces.Iθ, F z θ)
      = ∫ θ in Spaces.Iθ, R * (Spaces.Dz f R θ * Spaces.w R) ^ 2 * p θ
  rw [hswap]
  -- the radial slice identity
  have hinner : ∀ θ ∈ Spaces.Iθ,
      (∫ z, F z θ ∂(volume.restrict (Set.Ioo (0 : ℝ) R)))
        = R * (Spaces.Dz f R θ * Spaces.w R) ^ 2 * p θ := by
    intro θ hθ
    have h1 : (∫ z, F z θ ∂(volume.restrict (Set.Ioo (0 : ℝ) R)))
        = (∫ z, deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
            ∂(volume.restrict (Set.Ioo (0 : ℝ) R))) * p θ := by
      simp only [F]
      rw [MeasureTheory.integral_mul_const]
    have h2 : (∫ z, deriv (fun z' => z' * (Spaces.Dz f z' θ * Spaces.w z') ^ 2) z
            ∂(volume.restrict (Set.Ioo (0 : ℝ) R)))
        = R * (Spaces.Dz f R θ * Spaces.w R) ^ 2 :=
      box_slice_ftc f hsm hbd hC hR hθ
    rw [h1, h2]
  have hae : (fun θ => ∫ z, F z θ ∂(volume.restrict (Set.Ioo (0 : ℝ) R)))
      =ᵐ[volume.restrict Spaces.Iθ]
      (fun θ => R * (Spaces.Dz f R θ * Spaces.w R) ^ 2 * p θ) :=
    (ae_restrict_mem measurableSet_Icc).mono (fun θ hθ => hinner θ hθ)
  rw [MeasureTheory.integral_congr_ae hae]

end Work.Coercivity
