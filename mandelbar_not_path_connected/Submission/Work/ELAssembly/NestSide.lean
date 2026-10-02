/-
# `ELAssembly` — NEST (T6) in the orientation-complete form, and the defect of `NestData.nest_side`

`Work.ELNest.NestData.nest_side` (used by `Q_succ_subset` to prove `Q̂_{n+1} ⊆ Q̂_n`) reads

```lean
nest_side : ∀ P Q, InArc P.a Q.b (Q.a + 1) → InArc P.b Q.b (Q.a + 1) →
  Disjoint (pairCurve P) (pairCurve Q) → pairSideNear P ⊆ pairSideNear Q
```

— both angles of `P` lie in the *near* arc of `Q`.  This does **not** determine the orientation of
the pair `(P.a, P.b)`: from `P.a, P.b ∈ near arc(Q)` one can have either (i) the near arc of `P`
contained in that of `Q` (the case of the certificate, where the conclusion is true), or (ii) the
reverse (e.g. the toy configuration `Q = (0, 1/2)`, `P = (6/10, 7/10)`, whose curves are disjoint
rays: then near arc `P = (7/10, 16/10)` contains the far arc `(1/2, 1)` of `Q`, so `pairSideNear P`
is *not* contained in `pairSideNear Q`).  See `NOTES_FALSE_nest_side.md`.

The orientation-complete hypothesis is the **near-arc inclusion** `near arc(P) ⊆ near arc(Q)`
(equivalently the far-arc inclusion `far arc(Q) ⊆ far arc(P)`), and with it the statement is a
two-line corollary of ELTop's `pairSide_subset_pairSide` — which is what this file records, so
that a repair of the ELNest interface (or an assembly that needs the general form) has the
transport ready.
-/
import Mathlib
import Submission.Work.ELTop.pairSide_subset_pairSide
import Submission.Work.ELRig.Defs

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

namespace Work.ELAssembly

/-- The far side of the reversed pair is the near side of the pair (the companion of
`Work.ELTop.pairSideNear_reversePair`). -/
theorem pairSide_reversePair {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (P : Work.EL.CoPair hN) :
    Work.EL.pairSide (Work.ELTop.reversePair P) = Work.EL.pairSideNear P := by
  have hcurve : Work.EL.RawPair.curve hN (Work.ELTop.reversePair P).toRawPair
      = Work.EL.RawPair.curve hN P.toRawPair := by
    show Work.EL.paramRay hN ((Work.ELTop.reversePair P).a) ∪
        {((Work.ELTop.reversePair P).y : ℂ)} ∪ Work.EL.paramRay hN ((Work.ELTop.reversePair P).b)
      = Work.EL.paramRay hN P.a ∪ {P.y} ∪ Work.EL.paramRay hN P.b
    rw [Work.ELTop.reversePair_a, Work.ELTop.reversePair_b, Work.ELTop.reversePair_y,
      Work.ELTop.paramRay_add_one_of hN P.a]
    ext z
    simp only [Set.mem_union, Set.mem_singleton_iff]
    tauto
  have hlen : Work.EL.arcLen P.b (P.a + 1) = Work.EL.arcLen P.b P.a := by
    unfold Work.EL.arcLen
    rw [show P.a + 1 - P.b = (P.a - P.b) + (1 : ℤ) by push_cast; ring, Int.fract_add_intCast]
  unfold Work.EL.pairSide Work.EL.pairSideNear Work.EL.pairSideThroughArc
  rw [Work.ELTop.reversePair_a, Work.ELTop.reversePair_b]
  unfold Work.EL.RawPair.sideThrough
  rw [hcurve, hlen]

/-- **NEST (T6), orientation-complete form.**  If the near arc of `P` is contained in the near arc
of `Q` and the two pair curves are disjoint, then the near side of `P` is contained in the near
side of `Q`.

This is the corrected form of `Work.ELNest.NestData.nest_side`; the field's version, which only
assumes that the two angles of `P` lie in the near arc of `Q`, is not derivable in general (see
`NOTES_FALSE_nest_side.md`). -/
theorem nest_side_of_nearArc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (P Q : Work.EL.CoPair hN)
    (harc : ∀ θ : ℝ, Work.EL.InArc θ P.b (P.a + 1) → Work.EL.InArc θ Q.b (Q.a + 1))
    (hdisj : Disjoint (Work.EL.pairCurve P) (Work.EL.pairCurve Q)) :
    Work.EL.pairSideNear P ⊆ Work.EL.pairSideNear Q := by
  have hdisj' : Disjoint (Work.EL.pairCurve (Work.ELTop.reversePair P))
      (Work.EL.pairCurve Q) := by
    rw [Work.ELTop.pairCurve_reversePair]
    exact hdisj
  have hres := Work.ELTop.pairSide_subset_pairSideNear hN hJ (Work.ELTop.reversePair P) Q
    hdisj' (fun θ hθ => harc θ (by simpa using hθ))
  rwa [pairSide_reversePair P] at hres

end Work.ELAssembly
