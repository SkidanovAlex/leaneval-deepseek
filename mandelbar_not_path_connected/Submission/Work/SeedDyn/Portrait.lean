/-
# The orbit-portrait count `PortraitCount` (§2 of `NOTES_LEAD_mandelbar_seed.md`)

This module collects the `Work.PortraitCount` interface of the SeedDyn area: the count of rays
landing at a preimage of a two-ray point of the dynamical plane (`Work.ELPull.PortraitCount`,
`Submission/Work/ELPull/Defs.lean`), proved from the local injectivity of `T_c` off its critical
point and the impossibility of a ray landing at the critical value `c` when the critical orbit
enters the attracting petal of the parabolic flower.

## Contents

* `Work.PortraitCount.injOn_Tantibar_ball` (P1): `T_c` is injective on the ball of radius
  `‖y'‖/2` about a point `y' ≠ 0`.
* `Work.PortraitCount.eq_add_half_of_T_eq` (P2): two angles of `[0,1)` with the same doubled
  angle differ by `1/2`.
* `Work.PortraitCount.rayPt_ne` (P3): distinct angles modulo `1` give distinct ray points.
* `Work.PortraitCount.portraitCount_of_ne_zero` (P4): the count at a preimage `y' ≠ 0` of a
  two-ray point.
* `Work.PortraitCount.portraitCount_of_noRayAtCritValue` (P5): the count at a parameter where no
  ray lands at the critical value `c`.
* `Work.PortraitCount.noRayAtCritValue_of_flower` (P6, EL flavour) and
  `Work.PortraitCount.noRayAtCritValue` (ELPull flavour, through the adapter `elDynB`): no ray
  lands at `c` once the critical orbit enters the attracting petal `Pa ⊆ K_c`.
* `Work.PortraitCount.portraitCount_of_flower`: the count for an arbitrary
  `Work.ELPull.DynB c` with such a flower; this is the form `Work.ELAssembly` consumes.
* `Work.PortraitCount.portraitCount`: the same from the `Work.EL.RootParabolic` bundle, in the
  form requested by the design note.

The statements P1–P4, P6 and the `EL → ELPull` adapter are proved in the sibling modules
`Submission/Work/SeedDyn/PortraitCount/*.lean` (namespace `Work.SeedDyn.PortraitCount`) and are
re-exported here under the canonical `Work.PortraitCount` names.
-/
import Mathlib
import Submission.Work.SeedDyn.Defs
import Submission.Work.SeedDyn.Main
import Submission.Work.SeedDyn.PortraitCount.injOn_Tantibar_ball
import Submission.Work.SeedDyn.PortraitCount.eq_add_half_of_T_eq
import Submission.Work.SeedDyn.PortraitCount.rayPt_ne
import Submission.Work.SeedDyn.PortraitCount.portraitCount_of_ne_zero
import Submission.Work.SeedDyn.PortraitCount.noRayAtCritValue_of_flower
import Submission.Work.SeedDyn.PortraitCount.exists_elPullDynB
import Submission.Work.SeedDyn.PortraitCount.portraitCount_of_flower
import Submission.Work.ELPull.portrait_step
import Submission.Work.ELTop.Defs
import Submission.Work.ELRig.Pa_subset_K

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open Classical Filter

namespace Work.PortraitCount

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-! ## (P1)–(P4): the local count off the critical point -/

/-- **(P1)**  `T_c(z) = z̄² + c` is injective on the ball of radius `‖y'‖/2` about a point
`y' ≠ 0`: two preimages of the same value differ by a sign, and two antipodal points cannot both
lie in a ball of radius half the distance of its centre from the origin. -/
theorem injOn_Tantibar_ball {c y' : ℂ} (hy' : y' ≠ 0) :
    Set.InjOn (Tantibar c) (Metric.ball y' (‖y'‖ / 2)) :=
  Work.SeedDyn.PortraitCount.injOn_Tantibar_ball hy'

/-- **(P2)**  Two angles of `[0,1)` with the same doubled angle `T θ = fract (-2θ)` differ by
`1/2`. -/
theorem eq_add_half_of_T_eq {θ' θ'' : ℝ}
    (h' : θ' ∈ Set.Ico (0 : ℝ) 1) (h'' : θ'' ∈ Set.Ico (0 : ℝ) 1)
    (hT : Work.ELPull.T θ' = Work.ELPull.T θ'') (hne : θ' ≠ θ'') :
    θ'' = θ' + 1 / 2 ∨ θ' = θ'' + 1 / 2 :=
  Work.SeedDyn.PortraitCount.eq_add_half_of_T_eq h' h'' hT hne

/-- **(P3)**  At a fixed level `t > 1`, the ray points of two angles with different fractional
parts are distinct. -/
theorem rayPt_ne {c : ℂ} (hN : Work.ELPull.DynB c) {θ' θ'' t : ℝ}
    (ht : 1 < t) (h : Int.fract θ' ≠ Int.fract θ'') :
    hN.rayPt θ' t ≠ hN.rayPt θ'' t :=
  Work.SeedDyn.PortraitCount.rayPt_ne hN ht h

/-- **(P4)**  The orbit-portrait count at a preimage `y' ≠ 0` of a two-ray point.  (The two-ray
hypothesis is not needed: `T_c` is a local bijection off the critical point, and the only pairs of
distinct angles with equal `T`-image are antipodal, which would force `y' = -y'`.) -/
theorem portraitCount_of_ne_zero {c : ℂ} (hN : Work.ELPull.DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c))
    {y' : ℂ} (hy' : y' ≠ 0) {θ' θ'' : ℝ}
    (h' : θ' ∈ Set.Ico (0 : ℝ) 1) (h'' : θ'' ∈ Set.Ico (0 : ℝ) 1)
    (l' : Work.ELPull.LandsN hN θ' y') (l'' : Work.ELPull.LandsN hN θ'' y')
    (hT : Work.ELPull.T θ' = Work.ELPull.T θ'') : θ' = θ'' :=
  Work.SeedDyn.PortraitCount.portraitCount_of_ne_zero hN hφ hy' h' h'' l' l'' hT

/-! ## (P5): the count where no ray lands at the critical value -/

/-- **(P5)**  If no ray lands at the critical value `c` (so that `c` is not the landing point of
any external ray, which holds when `c` is an interior point of the filled Julia set), then the
orbit-portrait count holds at every two-ray point of the dynamical plane.

Indeed `y' = 0` would force `y = T_c 0 = c`, and a ray landing at `y' = 0` would map to a ray
landing at `c`; and `y' ≠ 0` is (P4). -/
theorem portraitCount_of_noRayAtCritValue {c : ℂ} (hN : Work.ELPull.DynB c)
    (hcv : ∀ θ : ℝ, ¬ Work.ELPull.LandsN hN θ c) : Work.ELPull.PortraitCount hN := by
  intro y y' hy htwo θ' θ'' h' h'' l' l'' hT
  by_cases hy' : y' = 0
  · subst hy'
    have himg := Work.ELPull.landsN_image hN
      (Work.SeedDyn.isDynBottcher_dynPhiOf_of_dynB hN) l'
    have hT0 : Tantibar c 0 = c := by simp [Tantibar]
    rw [hT0] at himg
    exact absurd himg (hcv (Work.ELPull.T θ'))
  · exact Work.SeedDyn.PortraitCount.portraitCount_of_ne_zero hN
      (Work.SeedDyn.isDynBottcher_dynPhiOf_of_dynB hN) hy' h' h'' l' l'' hT

/-! ## (P6): no ray lands at the critical value, from the flower -/

/-- **(P6, EL flavour)**  If the critical orbit of `F c = (T_c)^[10]` enters the attracting petal
`Pa` of the parabolic flower at `z₁`, then `c` is an interior point of the filled Julia set, and
no external ray can land there. -/
theorem noRayAtCritValue_of_flower {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (henter : ∃ N : ℕ, (Work.EL.F c)^[N] c ∈ fl.Pa) :
    ∀ θ : ℝ, ¬ Work.EL.LandsN d.hN θ c :=
  Work.SeedDyn.PortraitCount.noRayAtCritValue_of_flower d fl henter

/-! ## The count from the flower, in the forms the consumers use -/

/-- The **`EL → ELPull` adapter** used by `Work.PortraitCount.portraitCount`: an `ELPull.DynB c`
whose ray-landing relation agrees with that of the `EL`-flavoured data. -/
noncomputable def elDynB {c : ℂ} (d : Work.EL.RootParabolic c) : Work.ELPull.DynB c :=
  Classical.choose (Work.SeedDyn.PortraitCount.exists_elPullDynB d.bottcher d.hN)

/-- The ray-landing relation of the adapted dynamical Böttcher data is the `EL` one. -/
theorem landsN_elDynB {c : ℂ} (d : Work.EL.RootParabolic c) (θ : ℝ) (y : ℂ) :
    Work.ELPull.LandsN (elDynB d) θ y ↔ Work.EL.LandsN d.hN θ y :=
  Classical.choose_spec (Work.SeedDyn.PortraitCount.exists_elPullDynB d.bottcher d.hN) θ y

/-- **No ray lands at the critical value**, in the `ELPull` flavour: once the critical orbit of
`F c = (T_c)^[10]` enters the attracting petal `Pa` of the parabolic flower at `z₁`, the critical
value `c` is an interior point of the filled Julia set and hence is not the landing point of any
external ray. -/
theorem noRayAtCritValue_of_flower_pull {c z₁ : ℂ} (hN : Work.ELPull.DynB c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.ELPull.F c) ((Tantibar c)^[5]) z₁)
    (henter : ∃ N : ℕ, (Work.ELPull.F c)^[N] c ∈ fl.Pa) :
    ∀ θ : ℝ, ¬ Work.ELPull.LandsN hN θ c :=
  Work.SeedDyn.PortraitCount.noRayAtCritValue_of_flower_pull hN fl henter

/-- The **orbit-portrait count from the flower**, for an arbitrary dynamical Böttcher datum
`hN : Work.ELPull.DynB c`: if the critical orbit of `F c = (T_c)^[10]` enters the attracting
petal `Pa` of the parabolic flower at `z₁`, then the count holds.  This is the form
`Work.ELAssembly` consumes (`hcount` of its `portrait_five` inputs). -/
theorem portraitCount_of_flower {c z₁ : ℂ} (hN : Work.ELPull.DynB c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.ELPull.F c) ((Tantibar c)^[5]) z₁)
    (henter : ∃ N : ℕ, (Work.ELPull.F c)^[N] c ∈ fl.Pa) :
    Work.ELPull.PortraitCount hN :=
  Work.SeedDyn.PortraitCount.portraitCount_of_flower hN fl henter

/-- The **orbit-portrait count of the root-parabolic bundle** `d : Work.EL.RootParabolic c`,
in the form requested by the design note: from the parabolic flower `fl` at `d.z₁` and the entry
of the critical orbit into its petal `Pa`. -/
theorem portraitCount {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (henter : ∃ N : ℕ, (Work.EL.F c)^[N] c ∈ fl.Pa) :
    Work.ELPull.PortraitCount (elDynB d) :=
  portraitCount_of_flower (elDynB d) fl henter

end

end Work.PortraitCount
