/-
# `Work.LWP.Main` — the consumer-facing entry points of the LWP chapter

This module collects, in one place, the two shapes the downstream areas consume:

* **`Work.LWP.lwp_main`** — the Lichtenstein–Gunther local existence result for assembled data;
* **`Work.LWP.theorem1_shape_of_maximal_at_one`** — the exact `(p,u)`-shape of `theorem_1` for
  the assembly, obtained from a maximal solution on `[0,1)` and the Beale–Kato–Majda criterion.

It also bundles the chapter's named analytic inputs into the structure `Work.LWP.LWPInputs`.
-/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.LWP.BiotSavart
import Submission.Work.LWP.LocalExistence
import Submission.Work.LWP.BKM
import Submission.Work.LWP.CurlFree.curlFree_isGradient
import Submission.Work.LWP.BiotSavart.biotSavart_reflZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.LWP

/-- **The analytic inputs of the LWP chapter, bundled.**  Every theorem of
`Submission/Work/LWP/` is conditional on (a subset of) these; `NOTES.md` states what a proof of
each requires. -/
structure LWPInputs (α : NNReal) : Prop where
  /-- the Calderón–Zygmund/Schauder estimate: the `C^{1,α}` closure of Biot–Savart (item 1) -/
  schauder : BiotSavartSchauder α
  /-- the Biot–Savart law `∇×(BS ω) = ω`, `div (BS ω) = 0` -/
  law : BiotSavartLaw
  /-- reflection equivariance of Biot–Savart (the odd clause).  **No longer a true input**: it is
  proved as `Work.LWP.biotSavartReflection_holds`
  (`Submission/Work/LWP/BiotSavart/biotSavart_reflZ.lean`); the field is kept so that the bundle
  stays stable. -/
  reflection : BiotSavartReflection
  /-- the Picard iteration for the vorticity equation (item 2) -/
  transport : VorticityTransportExistence α
  /-- the elliptic reconstruction of the pressure -/
  pressure : PressureReconstruction α
  /-- propagation of the odd symmetry -/
  oddProp : IsOddPropagates
  /-- the Poincaré lemma on `ℝ³` (used in the classical pressure argument).  **No longer a true
  input**: it is proved as `Work.LWP.curlFreeIsGradient_holds`
  (`Submission/Work/LWP/CurlFree/curlFree_isGradient.lean`). -/
  poincare : CurlFreeIsGradient
  /-- uniqueness in the Lichtenstein–Gunther class -/
  uniqueness : EulerUniqueness α
  /-- the Beale–Kato–Majda continuation criterion (item 3) -/
  bkm : BKMExtension α
  /-- existence of a maximal solution -/
  maxExists : MaximalSolutionExists α

variable {α : NNReal}

/-- **Item 2, consumer-facing**: local existence in the Lichtenstein–Gunther class, from the
bundled inputs. -/
theorem lwp_main (H : LWPInputs α) {u₀ : R3 → R3} (hdata : EulerData α u₀)
    (hbs : EulerDataBS α u₀) (hself : ∀ x, u₀ x = biotSavart (vorticity u₀) x) :
    ∃ T : ℝ, 0 < T ∧ ∃ p : R3 → ℝ → ℝ, ∃ u : R3 → ℝ → R3, LGClass α u₀ T p u :=
  local_existence H.transport H.pressure H.oddProp hdata hbs hself

/-- **Item 1, consumer-facing**: the assembly's datum construction.  An `L¹`, bounded,
`α`-Hölder, divergence-free vorticity `ω₀` with the `α`-power decay clause produces
Lichtenstein–Gunther admissible data `u₀ = biotSavart ω₀`, provided the velocity is odd. -/
theorem lwp_data (H : LWPInputs α) {ω₀ : R3 → R3} (hint : Integrable ω₀)
    (hb : IsBoundedFun ω₀) (hh : Holder α ω₀) (hdiv : ∀ x, div ω₀ x = 0)
    (hodd : IsOdd (biotSavart ω₀)) (hdec : VorticityDecay α ω₀) :
    EulerData α (biotSavart ω₀) :=
  eulerData_of_biotSavart H.schauder H.law hint hb hh hdiv hodd hdec

/-- **Item 3, consumer-facing: the `(p,u)` shape of `theorem_1`.**

From a maximal solution on `[0,1)` (whose existence is the input `MaximalSolutionExists`), the
BKM continuation criterion, and the two mild side conditions that the vorticity sup-norm is
non-negative and integrable on `(0,t)` for every `t < 1`, one obtains the exact `(p,u)`-part of
`theorem_1`'s conclusion: the solution exists on `[0,1)` in the challenge's predicate, is odd at
every time, is jointly `C^{1,α}` on every compact strip, and its BKM integral diverges at
`1`. -/
theorem theorem1_shape_of_maximal_at_one (H : LWPInputs α) {u₀ : R3 → R3}
    (hmax : MaximalSolution α u₀ 1)
    (hnn : ∀ s, 0 ≤ (⨆ x, ‖vorticity (fun y => hmax.u y s) x‖))
    (hint : ∀ t ∈ Ico 0 1,
      IntegrableOn (fun s => ⨆ x, ‖vorticity (fun y => hmax.u y s) x‖) (Ioc 0 t)) :
    ∃ p : R3 → ℝ → ℝ, ∃ u : R3 → ℝ → R3,
      (∀ t ∈ Ico 0 1, IsOdd (u · t)) ∧
      IsLocalEulerEquationSolution p u₀ 1 u ∧
      (∀ T ∈ Ioo 0 1, IsContDiffHolderOn ℝ α u.uncurry (univ ×ˢ Icc 0 T)) ∧
      Tendsto (fun t => ∫ s in 0..t, ⨆ x, ‖(vorticity (u · s)) x‖) (𝓝[<] 1) atTop :=
  ⟨hmax.p, hmax.u, hmax.odd, hmax.sol, hmax.spacetime,
   bkm_divergence_of_maximal_one_of_integrable H.bkm hmax hnn hint |>.2.2.2⟩

/-- The same conclusion at the maximal time `T` (whatever it is), for an assembly that rescales
time to land the blow-up at `1`. -/
theorem theorem1_shape_of_maximal (H : LWPInputs α) {u₀ : R3 → R3} {T : ℝ}
    (hmax : MaximalSolution α u₀ T)
    (hnn : ∀ s, 0 ≤ (⨆ x, ‖vorticity (fun y => hmax.u y s) x‖))
    (hint : ∀ t ∈ Ico 0 T,
      IntegrableOn (fun s => ⨆ x, ‖vorticity (fun y => hmax.u y s) x‖) (Ioc 0 t)) :
    Tendsto (bkm hmax.u) (𝓝[<] T) atTop :=
  bkm_divergence_of_maximal H.bkm hmax (bkm_monoOn hmax.T_pos.le hnn hint)


/-- **`CurlFreeIsGradient` is not an input any more**: the Poincaré lemma on `ℝ³` is proved in
`Submission/Work/LWP/CurlFree/curlFree_isGradient.lean`.  This lemma lets a consumer fill the
`poincare` field of `LWPInputs`. -/
theorem curlFreeIsGradient_holds : CurlFreeIsGradient := CurlFree.curlFree_isGradient


/-- **The assembly's complete data package.**  A compactly supported vorticity `ω₀` that is `L¹`,
bounded, `α`-Hölder and divergence-free, with odd velocity and the `α`-power decay clause,
produces simultaneously the analytic datum class `EulerData`, the Biot–Savart-compatible class
`EulerDataBS` (with the decay field automatic) and the self-consistency clause `hself` needed by
`local_existence`. -/
theorem assembly_data (H : LWPInputs α) {ω₀ : R3 → R3} {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hint : Integrable ω₀) (hω : ∀ y, ‖ω₀ y‖ ≤ M) (hh : Holder α ω₀)
    (hdiv : ∀ x, div ω₀ x = 0) (hsupp : ∀ y, ω₀ y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hodd : IsOdd (biotSavart ω₀)) (hdec : VorticityDecay α ω₀) :
    EulerData α (biotSavart ω₀) ∧ EulerDataBS α (biotSavart ω₀) ∧
      (∀ x, biotSavart ω₀ x = biotSavart (vorticity (biotSavart ω₀)) x) :=
  ⟨eulerData_of_biotSavart H.schauder H.law hint (isBoundedFun_of_norm_le hω) hh hdiv hodd hdec,
   eulerDataBS_of_compactSupport H.law hR hM hint hω hh hdiv hsupp,
   self_eq_biotSavart_of_biotSavart H.law hint (isBoundedFun_of_norm_le hω) hdiv⟩

/-- **The whole chapter, for the assembly, in one statement**: compactly supported
Lichtenstein–Gunther data produce a local solution in the challenge's class. -/
theorem assembly_lwp (H : LWPInputs α) {ω₀ : R3 → R3} {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hint : Integrable ω₀) (hω : ∀ y, ‖ω₀ y‖ ≤ M) (hh : Holder α ω₀)
    (hdiv : ∀ x, div ω₀ x = 0) (hsupp : ∀ y, ω₀ y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hodd : IsOdd (biotSavart ω₀)) (hdec : VorticityDecay α ω₀) :
    ∃ T : ℝ, 0 < T ∧ ∃ p : R3 → ℝ → ℝ, ∃ u : R3 → ℝ → R3,
      LGClass α (biotSavart ω₀) T p u :=
  let h := assembly_data H hR hM hint hω hh hdiv hsupp hodd hdec
  lwp_main H h.1 h.2.1 h.2.2


/-- **`BiotSavartReflection` is not an input any more**: the reflection equivariance of the
Biot–Savart operator is proved in
`Submission/Work/LWP/BiotSavart/biotSavart_reflZ.lean`. -/
theorem biotSavartReflection_holds : BiotSavartReflection :=
  fun _ hω x => BiotSavart.biotSavart_reflZ hω x


/-- **Assembling `LWPInputs` from the genuinely open inputs.**  Two of the ten fields
(`reflection`, `poincare`) have been proved in this chapter, so a consumer needs to supply only
the remaining eight: the Schauder estimate, the Biot–Savart law, the Picard iteration, the
pressure reconstruction, oddness propagation, uniqueness, the BKM criterion, and existence of the
maximal solution. -/
theorem lwpInputs_of {α : NNReal} (schauder : BiotSavartSchauder α) (law : BiotSavartLaw)
    (transport : VorticityTransportExistence α) (pressure : PressureReconstruction α)
    (oddProp : IsOddPropagates) (uniqueness : EulerUniqueness α) (bkm : BKMExtension α)
    (maxExists : MaximalSolutionExists α) : LWPInputs α :=
  ⟨schauder, law, biotSavartReflection_holds, transport, pressure, oddProp,
   curlFreeIsGradient_holds, uniqueness, bkm, maxExists⟩

end Work.LWP
