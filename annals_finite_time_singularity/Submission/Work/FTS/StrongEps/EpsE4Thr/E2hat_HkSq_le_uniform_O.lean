/-
Copyright: work module for the Elgindi finite-time singularity project.

# The open-class `α`-uniform `ℋⁿ`-bound for the `D_z`-commutator defect `Ê₂`

`Submission/Work/FTS/CoercivityFix/Assembly/E2hat_HkSq_le_uniform.lean` proves the uniform
estimate

  `HkSq α n (Ê₂ f) ≤ Cn · (HkSq α n f + HkSq α n (D_θ f))` for all `α ≥ -1/10`,

with a constant `Cn` depending only on `n` — but under the *frozen* class `RegQ α (n+1) f`,
which contains the `SmoothQuad` (flatness at `z = 0`) component.  The level-four route of the
chapter runs on the *open* class `RegQo` (`EpsE4Thr/OpenClass.lean`), so this file ports the
whole chain to `SmoothOpen` data:

* the pointwise slot estimate is `E2hatOAux.E2hat_HkIntegrand_le_uniform_pt` (support modules
  `E2hatOAux/OpenLeibniz.lean`, `E2hatOAux/ZmulBound.lean`, `E2hatOAux/PtBound.lean`), whose
  two ingredients are the open-class Leibniz rule for a `z`-only multiplier
  (`E2hatOAux.mixed_zmul_SO`), replacing the `SmoothQuad`-based `E2Bound.mixed_zmul`, and the
  open-class subadditivity `GalFields.HkSum.HkIntegrand_add_le_open`, replacing
  `LocData.HkIntegrand_add_le`;
* the two `ℋⁿ`-memberships used for the monotonicity of the iterated integrals are
  `OpenPkg.HkMem_mono_open` (from `ℋ^{n+1}`) and `IPGen.HkMem_Dth_le` (for `D_θ f`, valid
  throughout `α ≥ -1/10`), replacing `LocDataExt.HkMem_mono` and
  `E2Bound.HkMem_dth_of_RegQ_ge`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.PtBound
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.EllipticEst.Vop_bound_reg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- `Iθ = [0,π/2]` and `(0,π/2)` differ by a null set. -/
private lemma restrict_Iθ_eq_Ioo :
    (volume : Measure ℝ).restrict Work.Spaces.Iθ
      = (volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2)) :=
  (MeasureTheory.restrict_Ioo_eq_restrict_Icc (μ := (volume : Measure ℝ)) (a := 0)
    (b := π / 2)).symm

/-- **The `α`-uniform `ℋⁿ`-defect estimate on the open class.**  For every `α > 0` and every
`f ∈ RegQo α (n+1)`,

`HkSq α n (Ê₂ f) ≤ Cn · (HkSq α n f + HkSq α n (D_θ f))`

with a constant `Cn` depending only on `n`.  The angular slices are controlled pointwise by
`E2hatOAux.E2hat_HkIntegrand_le_uniform_pt` on `(0,π/2)` (a null complement of `Iθ`), and the
outer integrals by monotonicity, using `OpenPkg.HkMem_mono_open` for `f` and
`IPGen.HkMem_Dth_le` for `D_θ f`. -/
theorem E2hat_HkSq_le_uniform_O (n : ℕ) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ α : ℝ, 0 < α → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongEps.EpsE4Thr.RegQo α (n + 1) f →
        Work.Spaces.HkSq α n (Work.FTS.CoercivityFix.E2hat f)
          ≤ Cn * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
  obtain ⟨Cn, hCnpos, hpt⟩ := E2hatOAux.E2hat_HkIntegrand_le_uniform_pt n
  refine ⟨Cn, hCnpos, ?_⟩
  intro α hαpos f hf
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.1
  have hmemf : Work.Spaces.HkMem α (n + 1) f := hf.2.1
  have hmf : Work.Spaces.HkMem α n f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm n (Nat.le_succ n) hmemf
  have hmth : Work.Spaces.HkMem α n (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := n) (by linarith : -(1 / 10 : ℝ) ≤ α) hsm hmemf
  -- the angular slice inequality, for every `z ∈ Iz`
  have hsl : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ)
        ≤ Cn * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
          + (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ)) := by
    intro z hz
    have hzge : 0 ≤ z := hz
    rw [restrict_Iθ_eq_Ioo]
    rcases eq_or_lt_of_le hzge with hz0 | hzpos
    · subst hz0
      simp [Work.FTS.EllipticEst.HkIntegrand_eq_zero_of_z_eq_zero']
    · have h1 : Integrable (fun θ => Work.Spaces.HkIntegrand α n f z θ)
          ((volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))) := by
        have h : Integrable (fun θ => Work.Spaces.HkIntegrand α n f z θ)
            ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
          hmf.1 z (Set.mem_Ici.mpr hzpos.le)
        rwa [restrict_Iθ_eq_Ioo] at h
      have h2 : Integrable (fun θ => Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ)
          ((volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))) := by
        have h : Integrable (fun θ => Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ)
            ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
          hmth.1 z (Set.mem_Ici.mpr hzpos.le)
        rwa [restrict_Iθ_eq_Ioo] at h
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (μ := (volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2)))
        (f := fun θ => Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ)
        (g := fun θ => Cn * (Work.Spaces.HkIntegrand α n f z θ
            + Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ))
        (Eventually.of_forall fun θ =>
          Work.Spaces.HkIntegrand_nonneg α n (Work.FTS.CoercivityFix.E2hat f) z θ)
        ((h1.add h2).const_mul Cn)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => hpt α f hαpos hsm z hzpos θ hθ))
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add h1 h2] at hmono
      exact hmono
  -- the outer integral, by monotonicity
  have hint : Integrable (fun z => Cn *
      ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
        + (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ)))
      ((volume : Measure ℝ).restrict Work.Spaces.Iz) := (hmf.2.add hmth.2).const_mul Cn
  have hout := MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg
      (fun θ => Work.Spaces.HkIntegrand_nonneg α n (Work.FTS.CoercivityFix.E2hat f) z θ))
    hint (MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)
      (fun z hz => hsl z hz))
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hmf.2 hmth.2] at hout
  simpa only [Work.Spaces.HkSq] using hout

end Work.FTS.StrongEps.EpsE4Thr
