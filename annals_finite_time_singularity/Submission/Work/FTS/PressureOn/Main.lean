/-
# `Work.FTS.PressureOn.Main` — the pressure reconstruction

The main theorem of the area: `Work.FTS.PressureOn.PressureReconstructionOn α` (design §1 of
`FTS_PHYS_BRIDGE.md`).  The pressure is the explicit field

  `p := pressureOn ω = -‖u‖²/2 - q`,  `q := potOn ω = pressurePotential (lamb (physVel ω) ω · t)`,

and the proof has three parts:

* **(Step 4, the Weyl/Liouville step)** `Connect.hasFDerivAt_potOn_slice`: at every interior time the
  space slice `q(·,t)` has Fréchet derivative `innerSL ℝ (∂_t u - u×ω)`, obtained by applying
  `weyl_pair` to the pair `(q, ∂_t u - u×ω)` whose weak divergence and curl identities are supplied
  by `Connect.weakDiv_pair` (from `weakDiv_timeDeriv` and `weakPoisson`) and by `weakCurl_pair`;
* **(joint `C¹` of `p`)** `Connect.contDiffOn_potOn_uncurry_open` on the open strip and
  `Connect.contDiffWithinAt_potOn_at_zero` at the boundary time `0`, together with the smoothness of
  `-‖u‖²/2`, combine to the required `ContDiffOn ℝ 1 p.uncurry (univ ×ˢ Ico 0 T)`;
* **(Step 5, the Euler equation)** `EulerAssembly.euler_eq_of_gradient` turns the gradient identity
  into `∂_t u + (u·∇)u + ∇p = 0`.
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.EulerAssembly
import Submission.Work.FTS.PressureOn.Connect.hasFDerivAt_potOn_slice
import Submission.Work.FTS.PressureOn.Connect.contDiffOn_potOn_uncurry_open
import Submission.Work.FTS.PressureOn.Connect.contDiffWithinAt_potOn_at_zero
import Submission.Work.FTS.PressureOn.Connect.contDiff_slice_of_isContDiffHolderOn
import Submission.Work.FTS.PressureOn.Connect.contDiffOn_prod_Ico_of_Icc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter Gradient
open Work.FTS.Physical (physVel)
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.PressureOn

/-- **The pressure reconstruction on the physical solution (design §1).** -/
theorem pressureReconstructionOn (α : ℝ≥0) : PressureReconstructionOn α := by
  intro ω T u hstrips hcurl hdiv hsupp hcontDt hderiv hfderiv hpointwise
  -- ## the Weyl step at every interior time
  have hgq : ∀ t ∈ Set.Ioo 0 T, ∀ x, HasFDerivAt (potOn ω · t)
      (innerSL ℝ (timeDeriv (physVel ω) x t - crossVec (physVel ω x t) (ω x t))) x :=
    fun t ht x => Connect.hasFDerivAt_potOn_slice hstrips hcurl hdiv hsupp hcontDt hderiv
      hfderiv hpointwise ht x
  refine ⟨pressureOn ω, ?_, ?_⟩
  · -- ## joint `C¹` of the pressure on `ℝ³ × [0,T)`
    have hp : (pressureOn ω).uncurry
        = fun z : R3 × ℝ => -(‖physVel ω z.1 z.2‖ ^ 2 / 2) - potOn ω z.1 z.2 := by
      rw [pressureOn_eq]
      rfl
    rw [hp]
    refine ContDiffOn.sub ?_ ?_
    · -- the `-‖u‖²/2` part: joint `C¹` from the strips
      refine Connect.contDiffOn_prod_Ico_of_Icc (n := 1)
        (g := fun z : R3 × ℝ => -(‖physVel ω z.1 z.2‖ ^ 2 / 2)) ?_
      intro S hS
      have hsm : ContDiff ℝ 1 (fun v : R3 => -(‖v‖ ^ 2 / 2)) :=
        ((contDiff_norm_sq (𝕜 := ℝ) (E := R3) (n := 1)).div_const 2).neg
      have hcomp : (fun z : R3 × ℝ => -(‖physVel ω z.1 z.2‖ ^ 2 / 2))
          = (fun v : R3 => -(‖v‖ ^ 2 / 2)) ∘ (physVel ω).uncurry := rfl
      rw [hcomp]
      exact hsm.comp_contDiffOn (hstrips S hS).1
    · -- the potential part
      intro z hz
      obtain ⟨x, s⟩ := z
      rcases lt_or_eq_of_le hz.2.1 with h | h
      · -- interior time: `q` is `C¹` on the open strip
        have hopen : Set.univ ×ˢ Set.Ioo 0 T ∈ 𝓝 (x, s) :=
          (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨trivial, h, hz.2.2⟩
        have hcat : ContDiffAt ℝ 1 (fun z : R3 × ℝ => potOn ω z.1 z.2) (x, s) :=
          (Connect.contDiffOn_potOn_uncurry_open hstrips hcurl hsupp hcontDt hderiv hgq).contDiffAt
            hopen
        exact hcat.contDiffWithinAt
      · -- boundary time `s = 0`
        subst h
        exact Connect.contDiffWithinAt_potOn_at_zero (by simpa using hz.2.2) hstrips hcurl hsupp
          hcontDt hderiv hgq x
  · -- ## the Euler equation on `ℝ³ × (0,T)`
    intro x t ht
    have ht0 : (0 : ℝ) ≤ t := ht.1.le
    have htT : t < T := ht.2
    set S : ℝ := (t + T) / 2 with hSdef
    have hS0 : 0 < S := by rw [hSdef]; linarith
    have hST : S < T := by rw [hSdef]; linarith
    have htS : t < S := by rw [hSdef]; linarith
    have hS : S ∈ Set.Ioo 0 T := ⟨hS0, hST⟩
    have htIcc : t ∈ Set.Icc 0 S := ⟨ht0, htS.le⟩
    have htIco : t ∈ Set.Ico 0 T := ⟨ht0, htT⟩
    -- the space slice is `C¹`
    have hcd : ContDiff ℝ 1 (fun y => physVel ω y t) :=
      Connect.contDiff_slice_of_isContDiffHolderOn (hstrips S hS) htIcc
    have hu : HasFDerivAt (fun y => physVel ω y t)
        (fderiv ℝ (fun y => physVel ω y t) x) x :=
      (hcd.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt
    have hsq : DifferentiableAt ℝ (fun y => ‖physVel ω y t‖ ^ 2 / 2) x := by
      have h1 : DifferentiableAt ℝ (fun y => ‖physVel ω y t‖ ^ 2) x :=
        ((contDiff_norm_sq (𝕜 := ℝ) (E := R3) (n := 1)).contDiffAt.differentiableAt
          (by norm_num)).comp x hu.differentiableAt
      simpa [div_eq_mul_inv, one_div] using h1.mul_const ((1 : ℝ) / 2)
    exact euler_eq_of_gradient hu (fun z => hcurl t htIco z) hsq
      (hgq t ht x).differentiableAt (hgq t ht x)

end Work.FTS.PressureOn
