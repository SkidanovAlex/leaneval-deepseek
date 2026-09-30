import Mathlib
import Submission.Work.RTOwed.cuspChart
import Submission.Work.RTOwed.cuspDev
import Submission.Work.RTOwed.cuspCert.CuspSupport
import Submission.Work.RTOwed.cuspCert.lattice_bridge
import Submission.Work.RTOwed.cuspCert.mbarPt_continuous
import Submission.Work.RTOwed.cuspCert.cubeOfMod_corner_dvd

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

/-- The finite check on the lookup table: the unit box with lower corner `cubeCorner a` selects the
cube `a`. -/
theorem cubeOfMod_cubeCorner : ∀ a : Fin 48,
    Work.Cusp.cubeOfMod (Work.Cusp.cubeCusp a) (Work.Cusp.cubeCorner a) = a := by
  decide

/-- **The canonical cube and offset of a half-open cell.**

Let `u := uhsXj q - cuspCert.lamV v k` lie in the half-open unit box
`[cubeCorner a, cubeCorner a + 1)³` of the cube `a` of the cusp `v`.  Then the canonical cube of the
cube coordinate `uhsXj q` is `a` itself, and the canonical offset is the one defining `u`.

Route.  From `u ∈ cuspCert.halfopenBox a` one gets `⌊u i⌋ = Cusp.cubeCorner a i`
(`Int.floor_eq_iff`), hence, since `uhsXj q = u + cuspCert.lamV v k` and `cuspCert.lamK v k` is an
integer vector, `⌊(uhsXj q) i⌋ = Cusp.cubeCorner a i + cuspCert.lamK v k i`
(`Int.floor_add_intCast`), i.e. `floorV (uhsXj q) = fun i => Cusp.cubeCorner a i + Cusp.latMod v i * k i`.
Therefore `cubeOf v (uhsXj q) = Cusp.cubeOfMod v (Cusp.cubeCorner a)`
(`Cusp.cubeOfMod_add_latMod` of `Submission/Work/RTOwed/cuspCert/lattice_bridge.lean`), and that
cube is `a` whenever `Cusp.cubeCusp a = v` — the finite check `cubeOfMod_cubeCorner` above.  The
second component is then the definitional computation
`redV v (uhsXj q) = uhsXj q - floorV (uhsXj q) + cubeCorner a = uhsXj q - cuspCert.lamV v k`. -/
theorem cubeOf_halfopen (v : Fin 5) {a : Fin 48} (hca : Work.Cusp.cubeCusp a = v) {k : Fin 3 → ℤ}
    {q : Work.RTOwed.CuspE4}
    (hu : Work.RTOwed.uhsXj q - Work.RTOwed.cuspCert.lamV v k
      ∈ Work.RTOwed.cuspCert.halfopenBox a) :
    Work.RTOwed.cubeOf v (Work.RTOwed.uhsXj q) = a ∧
      Work.RTOwed.redV v (Work.RTOwed.uhsXj q)
        = Work.RTOwed.uhsXj q - Work.RTOwed.cuspCert.lamV v k := by
  have hfloor : Work.RTOwed.floorV (Work.RTOwed.uhsXj q)
      = fun i => Work.Cusp.cubeCorner a i + Work.RTOwed.cuspCert.lamK v k i := by
    funext i
    have hu' := hu i
    have hfloor_u : ⌊(Work.RTOwed.uhsXj q - Work.RTOwed.cuspCert.lamV v k) i⌋
        = Work.Cusp.cubeCorner a i := by
      rw [Int.floor_eq_iff]
      exact ⟨hu'.1, hu'.2⟩
    have heq : (Work.RTOwed.uhsXj q) i
        = (Work.RTOwed.uhsXj q - Work.RTOwed.cuspCert.lamV v k) i
          + (Work.RTOwed.cuspCert.lamK v k i : ℝ) := by
      rw [show (Work.RTOwed.uhsXj q) i
          = ((Work.RTOwed.uhsXj q - Work.RTOwed.cuspCert.lamV v k)
              + Work.RTOwed.cuspCert.lamV v k) i from by
            rw [sub_add_cancel]]
      simp only [PiLp.add_apply, Work.RTOwed.cuspCert.lamV]
    show ⌊(Work.RTOwed.uhsXj q) i⌋ = _
    rw [heq, Int.floor_add_intCast, hfloor_u]
  have hcube : Work.RTOwed.cubeOf v (Work.RTOwed.uhsXj q) = a := by
    show Work.Cusp.cubeOfMod v (Work.RTOwed.floorV (Work.RTOwed.uhsXj q)) = a
    rw [hfloor]
    rw [show (fun i => Work.Cusp.cubeCorner a i + Work.RTOwed.cuspCert.lamK v k i)
        = (fun i => Work.Cusp.cubeCorner a i + (Work.Cusp.latMod v i : ℤ) * k i) from rfl]
    rw [Work.RTOwed.cuspCert.cubeOfMod_add_latMod]
    rw [← hca]
    exact cubeOfMod_cubeCorner a
  refine ⟨hcube, ?_⟩
  apply PiLp.ext; intro i
  have hfl : ⌊(Work.RTOwed.uhsXj q) i⌋
      = Work.Cusp.cubeCorner a i + Work.RTOwed.cuspCert.lamK v k i := by
    have := congrFun hfloor i
    simpa only [Work.RTOwed.floorV] using this
  simp only [Work.RTOwed.redV, PiLp.toLp_apply]
  rw [hcube, hfl]
  simp only [PiLp.sub_apply, Work.RTOwed.cuspCert.lamV]
  push_cast
  ring

end Work.RTOwed
