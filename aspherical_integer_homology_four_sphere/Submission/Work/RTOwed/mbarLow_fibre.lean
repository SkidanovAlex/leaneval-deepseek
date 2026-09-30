import Mathlib
import Submission.Work.RTOwed.mbarLow_inj
import Submission.Work.RTOwed.cuspChartBeta
import Submission.Work.RTOwed.cuspChart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

open Work.FoldInst

/-!
# The fibre of the cusp chart `mbarLow`

This is the field **(F2)** `fibre` of `Work.RTOwed.CuspRigid` for the concrete chart
`Work.RTOwed.mbarLow`: two points of the chimney (`11/10 ≤ q 3 ≤ β (xOf q)`, likewise for `q'`)
with the same image under the chart differ by a vector of the cusp lattice `Λ_v = diag(latMod v)·ℤ³`
in their horizontal parts, and have the same height.

The proof is the first half of the argument of `Work.RTOwed.mbarLow_inj_of` — the "walk" of
`Work.RTOwed.actX_Ksub_walk` to the cube of `q'`, then the separation
`Work.RTOwed.chartKlein_cubeBox_sep` of distinct cubes of the same copy and the injectivity
`Work.RTOwed.chartKlein_injOn` of the single-cube chart.  Only the *final* step of
`mbarLow_inj_of` (the passage from "the difference is a lattice vector" to "the difference is `0`",
which needs the narrow box hypothesis) is absent here.
-/

theorem mbarLow_fibre {v : Fin 5} {q q' : Work.RTOwed.CuspE4} (h11 : 11 / 10 ≤ q 3)
    (hc : q 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q)) (h11' : 11 / 10 ≤ q' 3)
    (hc' : q' 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q'))
    (h : Work.RTOwed.mbarLow v q = Work.RTOwed.mbarLow v q') :
    Work.RTOwed.latVec v (Work.Cusp.xOf q' - Work.Cusp.xOf q) ∧ q' 3 = q 3 := by
  -- the ceilings of the two chart cubes
  have hceil : q 3 ≤ ceilH (chartCube v q) (chartRed v q) :=
    le_ceilH_chartRed (v := v) (q := q) (by rw [xOf4_eq_xOf]; exact hc)
  have hceil' : q' 3 ≤ ceilH (chartCube v q') (chartRed v q') :=
    le_ceilH_chartRed (v := v) (q := q') (by rw [xOf4_eq_xOf]; exact hc')
  have hm : chartKlein (chartCube v q) (mkE4 (chartRed v q) (q 3)) ∈ Qbar :=
    chartKlein_mem (chartCube v q) (redV_mem_cubeBox v (uhsXj q)) h11 hceil
  have hm' : chartKlein (chartCube v q') (mkE4 (chartRed v q') (q' 3)) ∈ Qbar :=
    chartKlein_mem (chartCube v q') (redV_mem_cubeBox v (uhsXj q')) h11' hceil'
  -- the two chart values, in explicit form
  have hYq : mbarLow v q
      = mk (xbarOf (chartCube v q) (chartKlein (chartCube v q) (mkE4 (chartRed v q) (q 3))) hm) := by
    rw [mbarLow_eq_beta v h11 (by rw [xOf4_eq_xOf]; exact hc)]
    exact congrArg mk (Prod.ext rfl (Subtype.ext rfl))
  have hYq' : mbarLow v q'
      = mk (xbarOf (chartCube v q') (chartKlein (chartCube v q') (mkE4 (chartRed v q') (q' 3))) hm') := by
    rw [mbarLow_eq_beta v h11' (by rw [xOf4_eq_xOf]; exact hc')]
    exact congrArg mk (Prod.ext rfl (Subtype.ext rfl))
  -- the identification group element
  obtain ⟨γ, hγ, hact⟩ : ∃ γ ∈ Ksub (chartKlein (chartCube v q) (mkE4 (chartRed v q) (q 3))),
      actX γ (xbarOf (chartCube v q) (chartKlein (chartCube v q) (mkE4 (chartRed v q) (q 3))) hm)
        = xbarOf (chartCube v q') (chartKlein (chartCube v q') (mkE4 (chartRed v q') (q' 3))) hm' := by
    have hrel : rel (xbarOf (chartCube v q) (chartKlein (chartCube v q) (mkE4 (chartRed v q) (q 3))) hm)
        (xbarOf (chartCube v q') (chartKlein (chartCube v q') (mkE4 (chartRed v q') (q' 3))) hm') := by
      have hq_eq : mk (xbarOf (chartCube v q) (chartKlein (chartCube v q) (mkE4 (chartRed v q) (q 3))) hm)
          = mk (xbarOf (chartCube v q') (chartKlein (chartCube v q') (mkE4 (chartRed v q') (q' 3))) hm') := by
        rw [← hYq, ← hYq']; exact h
      exact setoid_iff.mp (Quotient.exact hq_eq)
    exact hrel
  -- the copy bit and the Klein point carried by `γ`
  have hbit : cubeBit (chartCube v q') = cubeBit (chartCube v q) + γ.2 := by
    have := congrArg Prod.fst hact
    simpa [xbarOf, actX_fst] using this.symm
  have hK : act γ.1 (chartKlein (chartCube v q) (mkE4 (chartRed v q) (q 3)))
      = chartKlein (chartCube v q') (mkE4 (chartRed v q') (q' 3)) := by
    have := congrArg (fun w : Xbar => w.2.1) hact
    simpa [xbarOf, actX_snd] using this
  -- the walk to the cube of `q'`
  obtain ⟨b, L, hL, hbL, hbbit, hbwalk⟩ :=
    actX_Ksub_walk (redV_mem_cubeBox v (uhsXj q)) h11 hceil hγ
  have hcubeOf : Cusp.cubeCusp (cubeOf v (uhsXj q)) = v :=
    cuspCert.cubeCusp_cubeOfMod v _
  have h1 : cubeBit b = cubeBit (chartCube v q') := hbbit.trans hbit.symm
  have h2 : chartKlein b (mkE4 (redV v (uhsXj q) + cuspCert.intVec L) (q 3))
      = chartKlein (chartCube v q') (mkE4 (chartRed v q') (q' 3)) := hbwalk.symm.trans hK
  -- the cubes agree, by the separation of same-bit cubes
  have hab : chartCube v q' = b := by
    by_contra hne
    exact chartKlein_cubeBox_sep hne h1.symm (redV_mem_cubeBox v (uhsXj q')) hbL h11' h11 h2.symm
  -- injectivity of the chart at the common cube
  have h2' : chartKlein b (mkE4 (redV v (uhsXj q) + cuspCert.intVec L) (q 3))
      = chartKlein b (mkE4 (chartRed v q') (q' 3)) := by rw [hab] at h2; exact h2
  have h3 : mkE4 (redV v (uhsXj q) + cuspCert.intVec L) (q 3) = mkE4 (chartRed v q') (q' 3) :=
    chartKlein_injOn b
      (show (0 : ℝ) < (mkE4 (redV v (uhsXj q) + cuspCert.intVec L) (q 3)) 3 from by
        simpa using lt_of_lt_of_le (by norm_num) h11)
      (show (0 : ℝ) < (mkE4 (chartRed v q') (q' 3)) 3 from by
        simpa using lt_of_lt_of_le (by norm_num) h11') h2'
  obtain ⟨hzL, hss⟩ := mkE4_inj h3
  -- the difference of the reduced coordinates is a lattice vector
  have hlatL : latVec v (cuspCert.intVec L) := by
    intro i
    obtain ⟨k, hk⟩ := hL i
    rw [hcubeOf] at hk
    refine ⟨k, ?_⟩
    rw [cuspCert.intVec_apply, hk]
    push_cast
    ring
  have hlat1 : latVec v (redV v (uhsXj q') - redV v (uhsXj q)) := by
    have hL' : redV v (uhsXj q') - redV v (uhsXj q) = cuspCert.intVec L := by
      have h2 : redV v (uhsXj q') = redV v (uhsXj q) + cuspCert.intVec L := hzL.symm
      rw [h2]; abel
    rw [hL']; exact hlatL
  have hlat2 : latVec v (cuspCert.intVec (cuspShift v (uhsXj q') - cuspShift v (uhsXj q))) := by
    rw [cuspCert.intVec_sub]
    exact cuspCert.latVec_sub (cuspCert.latVec_cuspShift v _) (cuspCert.latVec_cuspShift v _)
  have hdiff : Cusp.xOf q' - Cusp.xOf q
      = (redV v (uhsXj q') - redV v (uhsXj q))
        + cuspCert.intVec (cuspShift v (uhsXj q') - cuspShift v (uhsXj q)) := by
    have h := cuspCert.sub_eq_redV_shift v (uhsXj q') (uhsXj q)
    have hco : uhsXj q' - uhsXj q = Cusp.xOf q' - Cusp.xOf q := by
      apply PiLp.ext
      intro i
      simp only [uhsXj, xOf4_eq_xOf, PiLp.sub_apply, PiLp.add_apply, cuspH, PiLp.toLp_apply]
      ring
    rwa [hco] at h
  have hlatx : latVec v (Cusp.xOf q' - Cusp.xOf q) := by
    rw [hdiff]
    exact cuspCert.latVec_add hlat1 hlat2
  exact ⟨hlatx, hss.symm⟩

end Work.RTOwed
