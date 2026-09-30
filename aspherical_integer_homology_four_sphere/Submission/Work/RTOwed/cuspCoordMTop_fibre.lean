import Mathlib
import Submission.Work.RTOwed.FillAtlas
import Submission.Work.RTOwed.cuspCert.lattice_bridge
import Submission.Work.Cusp.cuspCoordMTop_continuous
import Submission.Work.Cusp.mbarPt_eq_iff
import Submission.Work.Cusp.cuspCoordM_injective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOWed

/-- **The fibre of the collar coordinate, across two boxes.**  If the coordinate inclusions of two
collar boxes of the same cusp send `q` and `q'` to the same point of `M̂`, then `q'` and `q` differ
by a (necessarily horizontal) lattice vector and have the same height.

Route.  If `q` is strictly below the ceiling (`q 3 < β (xOf q)`) then so is `q'`: otherwise the
equality would read `a.incMbar (D.mbarLow q) = a.incW v _`, forcing `D.mbarLow q ∈ a.Tset`
(`Work.Cusp.incMbar_eq_incW_imp`) against `D.mbarLow_not_TsetTop`; and symmetrically.  In the
hyperbolic branch `a.incMbar_injective` gives `D.mbarLow q = D.mbarLow q'`, and `(R v).fibre` —
applicable because `11/10 < q 3 ≤ β (xOf q)` (`11/10 < q 3` and `q 3 < sTop` from
`q ∈ cuspBoxTop`) — gives `latVec v (xOf q' - xOf q)` and `q' 3 = q 3`.  In the filling branch
`a.incW_injective v` gives `cuspInvOuter v q = cuspInvOuter v q'` and `outerY v (xOf q) ≡
outerY v (xOf q') (mod ℤ²)`; with `Work.Cusp.cuspInvOuter_fst_eq_smulTop`
(`t • bndOfU u = t' • bndOfU u'`, `0 < t, t'` by `Work.Cusp.cuspInvOuter_nrm_Top`),
`Work.Cusp.bndOfU_sub_int`, `Work.Cusp.addCircle_sub_int`, `Work.Cusp.outerY_fst`,
`Work.Cusp.outerY_snd`, `Work.Cusp.kappaCoord_sub`, `Work.Cusp.kappaCoord_expansion` one gets
`xOf q' - xOf q ∈ Work.Cusp.lattice v`, i.e. `latVec v (xOf q' - xOf q)` by
`Work.RTOwed.cuspCert.lattice_eq`; then `Work.Cusp.beta_lattice_periodic` and `t = t'` force
`q' 3 = q 3`. -/
theorem cuspCoordMTop_fibre (g : Work.RTInstance.GlueHomeo)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
    (R : ∀ v : Work.Space.Cusp, Work.RTOwed.CuspRigid g v (D v))
    (v : Work.Space.Cusp) (c₁ : Work.Cusp.E3) (δ₁ : ℝ) (q : Work.Cusp.E4)
    (h₁ : q ∈ Work.Cusp.cuspBoxTop v c₁ δ₁)
    (c₂ : Work.Cusp.E3) (δ₂ : ℝ) (q' : Work.Cusp.E4)
    (h₂ : q' ∈ Work.Cusp.cuspBoxTop v c₂ δ₂)
    (heq : Work.Cusp.cuspCoordMTop (Work.RTInstance.assemblyOf g) v (D v) c₁ δ₁ ⟨q, h₁⟩ =
      Work.Cusp.cuspCoordMTop (Work.RTInstance.assemblyOf g) v (D v) c₂ δ₂ ⟨q', h₂⟩) :
    Work.RTOwed.latVec v (Work.Cusp.xOf q' - Work.Cusp.xOf q) ∧ q' 3 = q 3 := by
  let a : Work.Space.Assembly := Work.RTInstance.assemblyOf g
  by_cases hbq : q 3 < Work.Cusp.beta (Work.Cusp.xOf q)
  · by_cases hbq' : q' 3 < Work.Cusp.beta (Work.Cusp.xOf q')
    · -- ### Both points lie strictly below the ceiling: the fibre of `mbarLow`
      have h' : a.incMbar ((D v).mbarLow q) = a.incMbar ((D v).mbarLow q') := by
        have hh := heq
        rw [Work.Cusp.cuspCoordMTop_eq_le a v (D v) c₁ δ₁ ⟨q, h₁⟩ (le_of_lt hbq),
            Work.Cusp.cuspCoordMTop_eq_le a v (D v) c₂ δ₂ ⟨q', h₂⟩ (le_of_lt hbq')] at hh
        exact hh
      exact (R v).fibre (le_of_lt (by simpa [Work.Cusp.s1] using h₁.2.1)) (le_of_lt hbq)
        (le_of_lt (by simpa [Work.Cusp.s1] using h₂.2.1)) (le_of_lt hbq')
        (a.incMbar_injective h')
    · -- ### `q` strictly below, `q'` on or above the ceiling: impossible
      exfalso
      have hsrc₂ : q' ∈ Work.Cusp.cuspSourceTop v c₂ δ₂ := ⟨h₂, not_lt.mp hbq'⟩
      have hlow : Work.Cusp.cuspCoordMTop a v (D v) c₁ δ₁ ⟨q, h₁⟩ =
          a.incMbar ((D v).mbarLow q) :=
        Work.Cusp.cuspCoordMTop_eq_le a v (D v) c₁ δ₁ ⟨q, h₁⟩ (le_of_lt hbq)
      have hhigh : Work.Cusp.cuspCoordMTop a v (D v) c₂ δ₂ ⟨q', h₂⟩ =
          Work.Cusp.cuspCoordMTopUp a v (D v) c₂ δ₂ ⟨q', hsrc₂⟩ :=
        Work.Cusp.cuspCoordMTop_eq_ge a v (D v) c₂ δ₂ ⟨q', h₂⟩ (not_lt.mp hbq')
      have hmix : a.incMbar ((D v).mbarLow q) =
          Work.Cusp.cuspCoordMTopUp a v (D v) c₂ δ₂ ⟨q', hsrc₂⟩ :=
        hlow.symm.trans (heq.trans hhigh)
      simp only [Work.Cusp.cuspCoordMTopUp] at hmix
      obtain ⟨hx, -⟩ := Work.Cusp.incMbar_eq_incW_imp a v hmix
      exact ((D v).mbarLow_not_TsetTop c₁ δ₁ h₁ hbq) hx
  · by_cases hbq' : q' 3 < Work.Cusp.beta (Work.Cusp.xOf q')
    · -- ### `q` on or above, `q'` strictly below the ceiling: impossible
      exfalso
      have hsrc₁ : q ∈ Work.Cusp.cuspSourceTop v c₁ δ₁ := ⟨h₁, not_lt.mp hbq⟩
      have hhigh : Work.Cusp.cuspCoordMTop a v (D v) c₁ δ₁ ⟨q, h₁⟩ =
          Work.Cusp.cuspCoordMTopUp a v (D v) c₁ δ₁ ⟨q, hsrc₁⟩ :=
        Work.Cusp.cuspCoordMTop_eq_ge a v (D v) c₁ δ₁ ⟨q, h₁⟩ (not_lt.mp hbq)
      have hlow : Work.Cusp.cuspCoordMTop a v (D v) c₂ δ₂ ⟨q', h₂⟩ =
          a.incMbar ((D v).mbarLow q') :=
        Work.Cusp.cuspCoordMTop_eq_le a v (D v) c₂ δ₂ ⟨q', h₂⟩ (le_of_lt hbq')
      have hmix : a.incMbar ((D v).mbarLow q') =
          Work.Cusp.cuspCoordMTopUp a v (D v) c₁ δ₁ ⟨q, hsrc₁⟩ :=
        hlow.symm.trans (heq.symm.trans hhigh)
      simp only [Work.Cusp.cuspCoordMTopUp] at hmix
      obtain ⟨hx, -⟩ := Work.Cusp.incMbar_eq_incW_imp a v hmix
      exact ((D v).mbarLow_not_TsetTop c₂ δ₂ h₂ hbq') hx
    · -- ### Both points lie on or above the ceiling: the fibre of the filling gluing
      have hsrc₁ : q ∈ Work.Cusp.cuspSourceTop v c₁ δ₁ := ⟨h₁, not_lt.mp hbq⟩
      have hsrc₂ : q' ∈ Work.Cusp.cuspSourceTop v c₂ δ₂ := ⟨h₂, not_lt.mp hbq'⟩
      -- the two recovered filling points agree
      have hup : Work.Cusp.cuspCoordMTopUp a v (D v) c₁ δ₁ ⟨q, hsrc₁⟩ =
          Work.Cusp.cuspCoordMTopUp a v (D v) c₂ δ₂ ⟨q', hsrc₂⟩ := by
        rw [← Work.Cusp.cuspCoordMTop_eq_ge a v (D v) c₁ δ₁ ⟨q, h₁⟩ (not_lt.mp hbq),
            ← Work.Cusp.cuspCoordMTop_eq_ge a v (D v) c₂ δ₂ ⟨q', h₂⟩ (not_lt.mp hbq')]
        exact heq
      simp only [Work.Cusp.cuspCoordMTopUp] at hup
      have hpair := a.incW_injective v hup
      -- the recovered layer points agree
      have hfst : (Work.Cusp.cuspInvOuter v q).1 = (Work.Cusp.cuspInvOuter v q').1 := by
        have h1 := congrArg
          (fun z : Work.Space.SquarePt × a.Torus v => (z.1 : Work.Cusp.E2)) hpair
        simpa using h1
      -- the torus coordinates agree modulo the period of the torus
      have hsnd : ∀ i : Fin 2,
          (((Work.Cusp.cuspInvOuter v q).2 i : ℝ) : AddCircle (1 : ℝ)) =
          (((Work.Cusp.cuspInvOuter v q').2 i : ℝ) : AddCircle (1 : ℝ)) := by
        have h2 := congrArg
          (fun z : Work.Space.SquarePt × a.Torus v => z.2) hpair
        have h2' := (D v).tor.symm.injective h2
        intro i
        exact congrFun h2' i
      -- the two boundary directions agree
      have hfx := Work.Cusp.cuspInvOuter_fst_eq_smulTop v c₁ δ₁ q hsrc₁
      have hfy := Work.Cusp.cuspInvOuter_fst_eq_smulTop v c₂ δ₂ q' hsrc₂
      have hnrm : Work.Cusp.nrm (Work.Cusp.cuspInvOuter v q).1 =
          Work.Cusp.nrm (Work.Cusp.cuspInvOuter v q').1 := congrArg Work.Cusp.nrm hfst
      have hpos : 0 < Work.Cusp.nrm (Work.Cusp.cuspInvOuter v q).1 :=
        lt_trans (by norm_num [Work.Cusp.layerLo])
          (Work.Cusp.cuspInvOuter_nrm_Top v c₁ δ₁ q hsrc₁).1
      have hbnd : Work.Cusp.bndOfU (Work.Cusp.outerU v (Work.Cusp.xOf q)) =
          Work.Cusp.bndOfU (Work.Cusp.outerU v (Work.Cusp.xOf q')) := by
        have hh := hfst
        rw [hfx, hfy, ← hnrm] at hh
        exact (smul_right_inj (ne_of_gt hpos)).mp hh
      -- the two ceiling points agree, so their cusp coordinates differ by a lattice vector
      have hmb : (D v).mbarPt (Work.Cusp.xOf q') = (D v).mbarPt (Work.Cusp.xOf q) := by
        apply a.incMbar_injective
        rw [Work.Cusp.incMbar_mbarPt_eq a v (D v) (Work.Cusp.xOf q'),
            Work.Cusp.incMbar_mbarPt_eq a v (D v) (Work.Cusp.xOf q)]
        refine Work.Cusp.incW_pair_congr a v ?_ ?_
        · exact hbnd.symm
        · refine congrArg (D v).tor.symm ?_
          funext i
          show ((((Work.Cusp.cuspInvOuter v q').2 : Work.Cusp.E2) i : ℝ) : AddCircle (1 : ℝ)) =
              ((((Work.Cusp.cuspInvOuter v q).2 : Work.Cusp.E2) i : ℝ) : AddCircle (1 : ℝ))
          exact (hsnd i).symm
      have hmem : Work.Cusp.xOf q' - Work.Cusp.xOf q ∈ Work.Cusp.lattice v :=
        (Work.Cusp.mbarPt_eq_iff a v (D v) (Work.Cusp.xOf q') (Work.Cusp.xOf q)).mp hmb
      -- and the heights agree
      have hm : ∀ i : Fin 2, ∃ m : ℤ, (Work.Cusp.cuspInvOuter v q).2 i =
          (Work.Cusp.cuspInvOuter v q').2 i + (m : ℝ) :=
        fun i => (Work.Cusp.addCircle_one_coe_eq_iff _ _).mp (hsnd i)
      choose m hm using hm
      have hy : (Work.Cusp.cuspInvOuter v q).2 =
          (Work.Cusp.cuspInvOuter v q').2 + Work.Cusp.ofInt2 m := by
        ext i
        fin_cases i
        · simpa [Work.Cusp.ofInt2, PiLp.add_apply] using hm 0
        · simpa [Work.Cusp.ofInt2, PiLp.add_apply] using hm 1
      have h3 : q' 3 = q 3 := by
        rw [← Work.Cusp.cuspInvOuter_heightTop v c₂ δ₂ q' hsrc₂,
            ← Work.Cusp.cuspInvOuter_heightTop v c₁ δ₁ q hsrc₁]
        rw [hfst, hy]
        exact (Work.Cusp.collarS_add_int v (Work.Cusp.cuspInvOuter v q').1
          (Work.Cusp.cuspInvOuter v q').2 m).symm
      have hlat : Work.RTOwed.latVec v (Work.Cusp.xOf q' - Work.Cusp.xOf q) := by
        have h : (Work.Cusp.xOf q' - Work.Cusp.xOf q) ∈
            (Work.Cusp.lattice v : Set Work.Cusp.E3) := hmem
        rw [Work.RTOwed.cuspCert.lattice_eq v] at h
        exact h
      exact ⟨hlat, h3⟩

end Work.RTOWed
