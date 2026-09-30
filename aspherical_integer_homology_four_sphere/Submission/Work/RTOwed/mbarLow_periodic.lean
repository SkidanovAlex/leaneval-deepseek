import Mathlib
import Submission.Work.RTOwed.CuspRigid
import Submission.Work.RTOwed.cuspChart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

/-!
# Periodicity of the cusp chart `mbarLow` under the cusp lattice

The chart `Work.RTOwed.mbarLow v` of the `v`-th cusp is, by definition, the `mk` of `cuspLowPt v`,
which depends on the point `q : CuspE4` only through

* the cube `cubeOf v (uhsXj q)`,
* the reduced coordinate `redV v (uhsXj q)`,
* the height `q 3`.

The lattice `Λ_v = diag (latMod v) · ℤ³` acts by translations of the horizontal coordinates
(`liftE4`); the reduction to the unit cube is `Λ_v`-periodic
(`cuspCert.cubeOf_intVec_lat`, `cuspCert.redV_intVec_of`), so the chart is invariant.
-/

/-- **`cuspLowPt` depends only on the cube, the reduced coordinate and the height**: if the three
data agree, the chart values agree (this covers both the genuine and the junk branch). -/
theorem cuspLowPt_congr (v : Fin 5) {q q' : CuspE4}
    (h1 : cubeOf v (uhsXj q) = cubeOf v (uhsXj q'))
    (h2 : redV v (uhsXj q) = redV v (uhsXj q'))
    (h3 : q 3 = q' 3) :
    cuspLowPt v q = cuspLowPt v q' := by
  classical
  have hval : redChart v (cubeOf v (uhsXj q)) q
      = redChart v (cubeOf v (uhsXj q')) q' := by
    simp only [redChart, h1, h2, h3]
  simp only [cuspLowPt]
  by_cases hc : redChart v (cubeOf v (uhsXj q)) q ∈ Work.FoldInst.Qbar
  · have hc' : redChart v (cubeOf v (uhsXj q')) q' ∈ Work.FoldInst.Qbar := hval ▸ hc
    rw [dif_pos hc, dif_pos hc']
    exact Prod.ext (congrArg cubeBit h1) (Subtype.ext hval)
  · have hc' : redChart v (cubeOf v (uhsXj q')) q' ∉ Work.FoldInst.Qbar :=
      fun h => hc (hval ▸ h)
    rw [dif_neg hc, dif_neg hc']

theorem mbarLow_periodic (v : Fin 5) (q : Work.RTOwed.CuspE4) (L : Work.RTOwed.CuspE3)
    (hL : Work.RTOwed.latVec v L) :
    Work.RTOwed.mbarLow v (q + Work.RTOwed.liftE4 L) = Work.RTOwed.mbarLow v q := by
  choose k hk using hL
  have hL' : L = cuspCert.intVec (fun i => (Work.Cusp.latMod v i : ℤ) * k i) := by
    apply PiLp.ext; intro i
    rw [hk i, cuspCert.intVec_apply]
    push_cast
    ring
  have huhs : uhsXj (q + liftE4 L) = uhsXj q + L := by
    apply PiLp.ext; intro i
    fin_cases i <;>
      simp [uhsXj, xOf4, cuspH, liftE4_apply] <;>
      ring
  have hcube : cubeOf v (uhsXj (q + liftE4 L)) = cubeOf v (uhsXj q) := by
    rw [huhs, hL']
    exact cuspCert.cubeOf_intVec_lat v (uhsXj q) k
  have hred : redV v (uhsXj (q + liftE4 L)) = redV v (uhsXj q) := by
    rw [huhs, hL']
    exact cuspCert.redV_intVec_of v (uhsXj q) _
      (cuspCert.cubeOf_intVec_lat v (uhsXj q) k)
  have hht : (q + liftE4 L) 3 = q 3 := by
    simp [liftE4_apply]
  have hlow : cuspLowPt v (q + liftE4 L) = cuspLowPt v q :=
    cuspLowPt_congr v hcube hred hht
  show FoldInst.mk (cuspLowPt v (q + liftE4 L)) = FoldInst.mk (cuspLowPt v q)
  rw [hlow]

end Work.RTOwed
