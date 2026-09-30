import Mathlib
import Submission.Work.RTOwed.cuspChartBeta
import Submission.Work.RTOwed.cuspChartRegion
import Submission.Work.RTOwed.chartKlein_strict
import Submission.Work.FoldInst.Quotient
import Submission.Work.FoldInst.Atlas
import Submission.Work.FoldInst.Polytope
import Submission.Work.RTOwed.cuspCert.mbarPt_inj
import Submission.Work.RTOwed.cuspCert.CuspSupport
import Submission.Work.RTOwed.cuspCert.lattice_bridge
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.TopBox
import Submission.Work.RTOwed.chartKlein_height_lt
import Submission.Work.RTOwed.chartKlein_injOn
import Submission.Work.RTOwed.actX_Ksub_walk

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

open Work.FoldInst

/-! ## Bookkeeping for the coordinates of a point of `E4` -/

/-- Reassembling the coordinates of a point of `E4`. -/
theorem mkE4_xOf4 (q : CuspE4) : mkE4 (xOf4 q) (q 3) = q := by
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

/-- The decomposition `mkE4` is injective. -/
theorem mkE4_inj {x x' : CuspE3} {s s' : ℝ} (h : mkE4 x s = mkE4 x' s') :
    x = x' ∧ s = s' := by
  have h3 : s = s' := congrFun (congrArg (fun q : CuspE4 => (q : Fin 4 → ℝ)) h) 3
  have hx : x = x' := by
    apply PiLp.ext
    intro i
    have h' := congrFun (congrArg (fun q : CuspE4 => (q : Fin 4 → ℝ)) h) i.castSucc
    fin_cases i <;> simpa [mkE4] using h'
  exact ⟨hx, h3⟩

/-! ## The separation of distinct cubes of the same copy -/

/-- **Two distinct cubes of the same copy never give the same chart point above the level
`11/10`.**  Combination of `Work.RTOwed.chartKlein_height_lt` (analytic separation) with the
injectivity `Work.RTOwed.chartKlein_injOn` of the Möbius chart. -/
theorem chartKlein_cubeBox_sep {a b : Fin 48} (hne : a ≠ b) (hbit : cubeBit a = cubeBit b)
    {x x' : CuspE3} (hx : x ∈ cubeBox a) (hx' : x' ∈ cubeBox b)
    {s s' : ℝ} (hs : 11 / 10 ≤ s) (hs' : 11 / 10 ≤ s') :
    chartKlein a (mkE4 x s) ≠ chartKlein b (mkE4 x' s') := by
  intro hEq
  obtain ⟨x₂, s₂, hs₂pos, hs₂lt, h₂⟩ := chartKlein_height_lt hne hbit hx hs
  have hb : chartKlein b (mkE4 x₂ s₂) = chartKlein b (mkE4 x' s') := by rw [← h₂, hEq]
  have hpos' : (0 : ℝ) < s' := lt_of_lt_of_le (by norm_num) hs'
  have hxx := chartKlein_injOn b hs₂pos hpos' hb
  obtain ⟨-, hs_eq⟩ := mkE4_inj hxx
  linarith [hs₂lt, hs_eq]

/-! ## Injectivity of the cusp chart on a narrow chimney box -/

/-- **Injectivity of the cusp chart on a narrow chimney box.**  `D` is any set of points whose
horizontal part lies in a box of side `2δ ≤ 1` and whose height lies in `(11/10, beta]`. -/
theorem mbarLow_inj_of {v : Fin 5} {c : CuspE3} {δ : ℝ} (hδ : δ ≤ 1 / 2) {D : Set CuspE4}
    (hD : ∀ q ∈ D, (∀ i, |Cusp.xOf q i - c i| < δ) ∧ 11 / 10 < q 3 ∧
      q 3 ≤ Cusp.beta (Cusp.xOf q)) :
    Set.InjOn (mbarLow v) D := by
  intro q hq q' hq' heq
  obtain ⟨hbox, hq11, hqceil⟩ := hD q hq
  obtain ⟨hbox', hq'11, hq'ceil⟩ := hD q' hq'
  have hs11 : 11 / 10 ≤ q 3 := le_of_lt hq11
  have hs'11 : 11 / 10 ≤ q' 3 := le_of_lt hq'11
  -- the two chart values, and their ceilings
  have hceil : q 3 ≤ ceilH (chartCube v q) (chartRed v q) :=
    le_ceilH_chartRed (v := v) (q := q) (by rw [xOf4_eq_xOf]; exact hqceil)
  have hceil' : q' 3 ≤ ceilH (chartCube v q') (chartRed v q') :=
    le_ceilH_chartRed (v := v) (q := q') (by rw [xOf4_eq_xOf]; exact hq'ceil)
  have hm : chartKlein (chartCube v q) (mkE4 (chartRed v q) (q 3)) ∈ Qbar :=
    chartKlein_mem (chartCube v q) (redV_mem_cubeBox v (uhsXj q)) hs11 hceil
  have hm' : chartKlein (chartCube v q') (mkE4 (chartRed v q') (q' 3)) ∈ Qbar :=
    chartKlein_mem (chartCube v q') (redV_mem_cubeBox v (uhsXj q')) hs'11 hceil'
  have hYq : mbarLow v q
      = mk (xbarOf (chartCube v q) (chartKlein (chartCube v q) (mkE4 (chartRed v q) (q 3))) hm) := by
    rw [mbarLow_eq_beta v hs11 (by rw [xOf4_eq_xOf]; exact hqceil)]
    exact congrArg mk (Prod.ext rfl (Subtype.ext rfl))
  have hYq' : mbarLow v q'
      = mk (xbarOf (chartCube v q') (chartKlein (chartCube v q') (mkE4 (chartRed v q') (q' 3))) hm') := by
    rw [mbarLow_eq_beta v hs'11 (by rw [xOf4_eq_xOf]; exact hq'ceil)]
    exact congrArg mk (Prod.ext rfl (Subtype.ext rfl))
  -- the identification group element
  obtain ⟨γ, hγ, hact⟩ : ∃ γ ∈ Ksub (chartKlein (chartCube v q) (mkE4 (chartRed v q) (q 3))),
      actX γ (xbarOf (chartCube v q) (chartKlein (chartCube v q) (mkE4 (chartRed v q) (q 3))) hm)
        = xbarOf (chartCube v q') (chartKlein (chartCube v q') (mkE4 (chartRed v q') (q' 3))) hm' := by
    have hrel : rel (xbarOf (chartCube v q) (chartKlein (chartCube v q) (mkE4 (chartRed v q) (q 3))) hm)
        (xbarOf (chartCube v q') (chartKlein (chartCube v q') (mkE4 (chartRed v q') (q' 3))) hm') := by
      have hq_eq : mk (xbarOf (chartCube v q) (chartKlein (chartCube v q) (mkE4 (chartRed v q) (q 3))) hm)
          = mk (xbarOf (chartCube v q') (chartKlein (chartCube v q') (mkE4 (chartRed v q') (q' 3))) hm') := by
        rw [← hYq, ← hYq']; exact heq
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
  -- the walk
  obtain ⟨b, L, hL, hbL, hbbit, hbwalk⟩ :=
    actX_Ksub_walk (redV_mem_cubeBox v (uhsXj q)) hs11 hceil hγ
  have hcubeOf : Cusp.cubeCusp (cubeOf v (uhsXj q)) = v :=
    cuspCert.cubeCusp_cubeOfMod v _
  have h1 : cubeBit b = cubeBit (chartCube v q') := hbbit.trans hbit.symm
  have h2 : chartKlein b (mkE4 (redV v (uhsXj q) + cuspCert.intVec L) (q 3))
      = chartKlein (chartCube v q') (mkE4 (chartRed v q') (q' 3)) := hbwalk.symm.trans hK
  -- the cubes agree, by the separation of same-bit cubes
  have hab : chartCube v q' = b := by
    by_contra hne
    exact chartKlein_cubeBox_sep hne h1.symm (redV_mem_cubeBox v (uhsXj q')) hbL hs'11 hs11 h2.symm
  -- injectivity of the chart at the common cube
  have h2' : chartKlein b (mkE4 (redV v (uhsXj q) + cuspCert.intVec L) (q 3))
      = chartKlein b (mkE4 (chartRed v q') (q' 3)) := by rw [hab] at h2; exact h2
  have h3 : mkE4 (redV v (uhsXj q) + cuspCert.intVec L) (q 3) = mkE4 (chartRed v q') (q' 3) :=
    chartKlein_injOn b
      (show (0 : ℝ) < (mkE4 (redV v (uhsXj q) + cuspCert.intVec L) (q 3)) 3 from by
        simpa using lt_of_lt_of_le (by norm_num) hs11)
      (show (0 : ℝ) < (mkE4 (chartRed v q') (q' 3)) 3 from by
        simpa using lt_of_lt_of_le (by norm_num) hs'11) h2'
  obtain ⟨hzL, hss⟩ := mkE4_inj h3
  -- the difference of the horizontal parts is a lattice vector
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
    have hc : uhsXj q' - uhsXj q = Cusp.xOf q' - Cusp.xOf q := by
      apply PiLp.ext
      intro i
      simp only [uhsXj, xOf4_eq_xOf, PiLp.sub_apply, PiLp.add_apply, cuspH, PiLp.toLp_apply]
      ring
    rwa [hc] at h
  have hlatx : latVec v (Cusp.xOf q' - Cusp.xOf q) := by
    rw [hdiff]
    exact cuspCert.latVec_add hlat1 hlat2
  -- narrowness
  have hxeq : Cusp.xOf q' = Cusp.xOf q := by
    apply PiLp.ext
    intro i
    obtain ⟨k, hk⟩ := hlatx i
    have hbound : |Cusp.xOf q' i - Cusp.xOf q i| < 1 := by
      have h1 : |Cusp.xOf q i - c i| < δ := hbox i
      have h2 : |Cusp.xOf q' i - c i| < δ := hbox' i
      have htri : |Cusp.xOf q' i - Cusp.xOf q i|
          ≤ |Cusp.xOf q' i - c i| + |Cusp.xOf q i - c i| := by
        have h := abs_sub_le (Cusp.xOf q' i) (c i) (Cusp.xOf q i)
        have hc : |c i - Cusp.xOf q i| = |Cusp.xOf q i - c i| := abs_sub_comm _ _
        rwa [hc] at h
      have h3 : |Cusp.xOf q' i - Cusp.xOf q i| < 2 * δ := by linarith
      linarith
    have hbound' : |((Cusp.xOf q' - Cusp.xOf q) i)| < 1 := by
      simpa only [PiLp.sub_apply] using hbound
    rw [hk] at hbound'
    have hbound'' : |((Cusp.latMod v i : ℤ) : ℝ) * (k : ℝ)| < 1 := by
      simpa using hbound'
    have hmod : (1 : ℝ) ≤ ((Cusp.latMod v i : ℤ) : ℝ) := by
      have := cuspCert.latMod_pos v i
      exact_mod_cast this
    have hkabs : |(k : ℝ)| < 1 := by
      have h2 : |((Cusp.latMod v i : ℤ) : ℝ) * (k : ℝ)| < 1 := hbound''
      rw [abs_mul] at h2
      have hmod' : (1 : ℝ) ≤ |((Cusp.latMod v i : ℤ) : ℝ)| := by
        rw [abs_of_nonneg (by positivity)]
        exact hmod
      have := abs_nonneg (k : ℝ)
      nlinarith [hmod', this, h2]
    have hk0 : k = 0 := by
      have := abs_lt.mp hkabs
      have h1 : (-1 : ℤ) < k := by exact_mod_cast this.1
      have h2 : k < 1 := by exact_mod_cast this.2
      omega
    have hk' : Cusp.xOf q' i - Cusp.xOf q i = 0 := by
      have h := hk
      rw [hk0] at h
      simpa using h
    exact sub_eq_zero.mp hk'
  -- conclusion
  have hq1 : q = mkE4 (Cusp.xOf q) (q 3) := by
    rw [← xOf4_eq_xOf]; exact (mkE4_xOf4 q).symm
  have hq2 : q' = mkE4 (Cusp.xOf q') (q' 3) := by
    rw [← xOf4_eq_xOf]; exact (mkE4_xOf4 q').symm
  rw [hq1, hq2, hxeq, ← hss]

/-! ## The stated injectivity -/

theorem mbarLow_inj (v : Fin 5) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2) :
    Set.InjOn (Work.RTOwed.mbarLow v)
      {q : Work.Cusp.E4 | q ∈ Work.Cusp.cuspChartBox v c δ ∧
        q 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q)} ∧
    Set.InjOn (Work.RTOwed.mbarLow v)
      {q : Work.Cusp.E4 | q ∈ Work.Cusp.cuspBoxTop v c δ ∧
        q 3 ≤ Work.Cusp.beta (Work.Cusp.xOf q)} := by
  constructor
  · refine mbarLow_inj_of (v := v) (c := c) (δ := δ) hδ (fun q hq => ?_)
    obtain ⟨hbox, h11, hJ, hu1, hu2⟩ := hq.1
    exact ⟨hbox, by simpa [Cusp.s1] using h11, hq.2⟩
  · refine mbarLow_inj_of (v := v) (c := c) (δ := δ) hδ (fun q hq => ?_)
    obtain ⟨hbox, h11, hTop⟩ := hq.1
    exact ⟨hbox, by simpa [Cusp.s1] using h11, hq.2⟩

end Work.RTOwed
