/-
# `ELAssembly` — `Pa_far`: the attracting petal lies in the far side of the `α`-pair

The field `Pa_far` of the input bundle `Work.ELAssembly.AssemblyInputs` (equivalently the last
portrait input of the assembly of `Z1Nest`/`B2Data`) is the statement that the Leau–Fatou
attracting petal at the root-parabolic point `z₁` lies in the **far side** of the `α`-pair, i.e.
in the wake side `X₀` of the root portrait: the component of the complement of
`R(α₁) ∪ {z₁} ∪ R(α₂)` through the arc `W₀ = (α₁, α₂)`.

This file *derives* it from the bundle's own two inputs:

* `d.wake (10N+1)` (the L-wake hypothesis of `Work.EL.RootParabolic`): the `(10N+1)`-st point of
  the critical orbit of `T_c` — i.e. `(F c)^[N] c` with `F c = (T_c)^{10} = (Tantibar c)^[5]` —
  lies in the wake side `X_{(10N) % 5} = X₀`; and
* `fl.enters_Pa c d.crit.1 d.crit.2`: some iterate `(F c)^[N] c` of the critical value lies in
  the petal `fl.Pa`.

We therefore get a point `z* = (F c)^[N] c` which lies in **both** the petal and the far side.
The petal then has to lie in the far side: `fl.Pa ⊆ K c` (the orbits in `Pa` converge to `z₁`,
`Work.ELAssembly.Pa_subset_K_of_flowerData`), the pair curve meets `K c` only in its landing point
`z₁` (the rays are disjoint from `K c`, `Work.EL.paramRay_subset_compl`), and `z₁ ∉ Pa`; so `Pa`
is a preconnected set avoiding the pair curve, and hence is contained in the connected component
of `z*`, which is the far side (`Set.IsPreconnected.subset_connectedComponentIn` and
`connectedComponentIn_eq`).

The conclusion is exactly the input `Pa_far` of `Work.ELRig.Z1Nest`
(`Submission/Work/ELRig/Inputs.lean`).
-/
import Mathlib
import Submission.Work.ELAssembly.portraitCount_of_flowerData
import Submission.Work.ELAssembly.Defs
import Submission.Work.ELTop.pairSides_decomposition
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELNest.Defs
import Submission.Work.ELTop.RigInput

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

namespace Work.ELAssembly

variable {c : ℂ}

/-! ## The wake side of index `0` -/

/-- The wake side `X₀` of the root portrait is the far side of the `α`-pair: both are the
component of the complement of `R(α₁) ∪ {z₁} ∪ R(α₂)` through the arc `W₀ = (371, 404)/1023`
(the `min`/`max` of `alphaPairRaw` are `α₁`, `α₂` because `α₁ < α₂`, and `wakeLo 0`, `wakeHi 0`
are these two angles). -/
theorem wakeSide_zero (d : Work.EL.RootParabolic c) :
    Work.EL.wakeSide d.hN d.z₁ 0 = Work.EL.pairSide (alphaPairOf d) := by
  simp only [Work.EL.wakeSide, Work.EL.alphaPairRaw, Work.EL.wakeLo, Work.EL.wakeHi,
    Work.EL.pairSide, Work.EL.pairSideThroughArc, Work.ELAssembly.alphaPairOf,
    Work.EL.alpha1, Work.EL.alpha2, Function.iterate_zero_apply]
  norm_num

/-! ## The petal avoids the `α`-pair curve -/

/-- The attracting petal avoids the curve `R(α₁) ∪ {z₁} ∪ R(α₂)`: the petal lies in `K c`, the
pair curve meets `K c` only at the landing point `z₁`, and `z₁ ∉ Pa`. -/
theorem Pa_subset_compl_pairCurve (d : Work.EL.RootParabolic c)
    (fl : Work.ELNest.FlowerData c d.z₁) :
    fl.Pa ⊆ (Work.EL.pairCurve (alphaPairOf d))ᶜ := by
  intro z hz hcurve
  have hzK : z ∈ Work.EL.K c := Pa_subset_K_of_flowerData fl hz
  rw [Work.EL.mem_pairCurve_iff] at hcurve
  rcases hcurve with h | h | h
  · exact (Work.EL.paramRay_subset_compl d.hN _ h) hzK
  · rw [h] at hz
    exact fl.z₀_not_mem hz
  · exact (Work.EL.paramRay_subset_compl d.hN _ h) hzK

/-! ## The target -/

theorem Pa_far_of {c : ℂ} (d : Work.EL.RootParabolic c) (fl : Work.ELNest.FlowerData c d.z₁) :
    fl.Pa ⊆ Work.EL.pairSide (Work.ELAssembly.alphaPairOf d) := by
  -- an iterate of the critical value which enters the petal
  obtain ⟨N, hNmem⟩ := fl.enters_Pa c d.crit.1 d.crit.2
  -- the same point lies in the wake side `X₀` by the L-wake hypothesis: it is the `(10N+1)`-st
  -- point `(Tantibar c)^[10N+1] 0` of the critical orbit of `T_c`, and `10N ≡ 0 [MOD 5]`
  have hfar : (Work.EL.F c)^[N] c ∈ Work.EL.pairSide (Work.ELAssembly.alphaPairOf d) := by
    have hconv : (Tantibar c)^[10 * N + 1] 0 = (Work.EL.F c)^[N] c := by
      have hT0 : (Tantibar c) 0 = c := by simp [LeanEval.ComplexAnalysis.Tantibar]
      rw [Function.iterate_succ_apply, hT0, Function.iterate_mul (Tantibar c) 10 N,
        ← Work.ELNest.F_eq_tantibar]
      rfl
    have hmod : (10 * N + 1 - 1) % 5 = 0 := by
      have h1 : 10 * N + 1 - 1 = 10 * N := by omega
      rw [h1]
      exact Nat.mod_eq_zero_of_dvd ⟨2 * N, by ring⟩
    have hw := d.wake (10 * N + 1) (by omega)
    rw [hconv, hmod] at hw
    rwa [wakeSide_zero d] at hw
  -- the petal is preconnected and avoids the pair curve
  have hsub : fl.Pa ⊆ (Work.EL.pairCurve (Work.ELAssembly.alphaPairOf d))ᶜ :=
    Pa_subset_compl_pairCurve d fl
  have hcomp : fl.Pa ⊆ connectedComponentIn
      (Work.EL.pairCurve (Work.ELAssembly.alphaPairOf d))ᶜ ((Work.EL.F c)^[N] c) :=
    fl.isPreconnected_Pa.subset_connectedComponentIn hNmem hsub
  -- and the far side is exactly the component of that point
  have heq : Work.EL.pairSide (Work.ELAssembly.alphaPairOf d)
      = connectedComponentIn (Work.EL.pairCurve (Work.ELAssembly.alphaPairOf d))ᶜ
          ((Work.EL.F c)^[N] c) := by
    rw [show Work.EL.pairSide (Work.ELAssembly.alphaPairOf d)
        = connectedComponentIn (Work.EL.pairCurve (Work.ELAssembly.alphaPairOf d))ᶜ
            (Work.EL.rayPt d.hN
              (Work.EL.alpha1 + Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2 / 2) 2)
        from rfl]
    exact connectedComponentIn_eq hfar
  rw [heq]
  exact hcomp

end Work.ELAssembly
