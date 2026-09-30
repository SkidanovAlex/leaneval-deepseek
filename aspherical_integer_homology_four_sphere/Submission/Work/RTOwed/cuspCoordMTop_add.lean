import Mathlib
import Submission.Work.RTOwed.FillAtlas
import Submission.Work.RTOwed.cuspCert.lattice_bridge
import Submission.Work.RTOwed.cuspTorus_homeo_boundary_explicit
import Submission.Work.Cusp.cuspCoordMTop_continuous
import Submission.Work.Cusp.beta_lattice_periodic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOWed

/-! ## Elementary coordinates of the horizontal lift `liftE4`

`Work.RTOwed.liftE4 L` is the vector `L ∈ E3` with a zero height coordinate.  Two facts about it are
used constantly below: the horizontal part `xOf` shifts by `L`, and the height coordinate is
unchanged. -/

/-- The horizontal part `xOf` of `q + liftE4 L` is `xOf q + L`. -/
lemma xOf_add_liftE4 (q : Work.Cusp.E4) (L : Work.Cusp.E3) :
    Work.Cusp.xOf (q + Work.RTOwed.liftE4 L) = Work.Cusp.xOf q + L := by
  ext i
  fin_cases i <;> simp [Work.Cusp.xOf, Work.RTOwed.liftE4]

/-- The height coordinate of `q + liftE4 L` is the height coordinate of `q`. -/
lemma add_liftE4_apply_three (q : Work.Cusp.E4) (L : Work.Cusp.E3) :
    (q + Work.RTOwed.liftE4 L) 3 = q 3 := by
  simp [Work.RTOwed.liftE4]

/-! ## The outer inverse `cuspInvOuter` in terms of `xOf`, `β`, `outerU`, `outerY`

`cuspInvOuter` is written with `let`-bound abbreviations; this is the same formula with the `let`s
exposed, so that the lattice periodicity of `β` (`Work.Cusp.beta_lattice_periodic`) and of the
boundary map (`Work.RTOwed.cuspBdryMap_periodic`) can be applied to it. -/

/-- **The outer inverse `cuspInvOuter`, with the `let`-abbreviations exposed.**  The recovered layer
parameter depends only on the height `q 3` and on the ceiling `β (xOf q)`; the recovered square point
is `t • bndOfU (outerU v (xOf q))` and the recovered torus coordinates are `outerY v (xOf q)`. -/
lemma cuspInvOuter_apply (v : Work.Space.Cusp) (q : Work.Cusp.E4) :
    Work.Cusp.cuspInvOuter v q
      = ((1 + (Real.log (q 3) - Real.log (Work.Cusp.beta (Work.Cusp.xOf q))) /
            (2 * (Real.log (Work.Cusp.beta (Work.Cusp.xOf q)) - Real.log Work.Cusp.sJ)))
            • Work.Cusp.bndOfU (Work.Cusp.outerU v (Work.Cusp.xOf q)),
          Work.Cusp.outerY v (Work.Cusp.xOf q)) := rfl

/-- **The unslabbed collar coordinate `cuspCoordMTop` is invariant under a lattice shift of its
argument, across two (a priori different) boxes.**  For `L ∈ Λ_v` (`Work.RTOwed.latVec v L`), a point
`q` of one collar box and the shifted point `q + liftE4 L` of another, the two coordinate inclusions
into `M̂` agree.

The value of `cuspCoordMTop` does not depend on the box parameters `c, δ` (only the membership proof
does), so this is the statement that `cuspCoordMTop` is `Λ_v`-periodic in its argument.

Route.  `xOf (q + liftE4 L) = xOf q + L` and `(q + liftE4 L) 3 = q 3`, so the branch test
`q 3 < β (xOf q)` is unchanged by `Work.Cusp.beta_lattice_periodic`.  In the hyperbolic branch both
sides are `a.incMbar (D.mbarLow _)` and `(R v).periodic` (with `latVec v L`) gives equality.  In the
filling branch write `cuspInvOuter v q = (t • bndOfU (outerU v (xOf q)), outerY v (xOf q))`; `t`
depends only on `q 3` and `β (xOf q)` (both shift-invariant), `outerU v (xOf q + L)` differs from
`outerU v (xOf q)` by an integer (use `Work.RTOwed.cuspCert.lattice_eq` to get
`L ∈ Work.Cusp.lattice v`, then `AddSubgroup.closure_induction` with the generator shifts
`Work.Cusp.outerU_add_kv_int`, `Work.Cusp.outerY_add_kv_fst_int`, `Work.Cusp.outerY_add_kv_snd_int`
and additivity `Work.Cusp.kappaCoord_add`), and similarly for `outerY`; `Work.Cusp.bndOfU_add_int`
and integer shifts in `AddCircle (1:ℝ)` finish. -/
theorem cuspCoordMTop_add (g : Work.RTInstance.GlueHomeo)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
    (R : ∀ v : Work.Space.Cusp, Work.RTOwed.CuspRigid g v (D v))
    (v : Work.Space.Cusp) (c₁ : Work.Cusp.E3) (δ₁ : ℝ) (q : Work.Cusp.E4)
    (h₁ : q ∈ Work.Cusp.cuspBoxTop v c₁ δ₁) (L : Work.Cusp.E3)
    (hL : Work.RTOwed.latVec v L) (c₂ : Work.Cusp.E3) (δ₂ : ℝ)
    (h₂ : q + Work.RTOwed.liftE4 L ∈ Work.Cusp.cuspBoxTop v c₂ δ₂) :
    Work.Cusp.cuspCoordMTop (Work.RTInstance.assemblyOf g) v (D v) c₁ δ₁ ⟨q, h₁⟩ =
      Work.Cusp.cuspCoordMTop (Work.RTInstance.assemblyOf g) v (D v) c₂ δ₂
        ⟨q + Work.RTOwed.liftE4 L, h₂⟩ := by
  -- The two coordinate facts, and the lattice shift of the ceiling and of the boundary map.
  have hx : Work.Cusp.xOf (q + Work.RTOwed.liftE4 L) = Work.Cusp.xOf q + L :=
    xOf_add_liftE4 q L
  have h3 : (q + Work.RTOwed.liftE4 L) 3 = q 3 :=
    add_liftE4_apply_three q L
  have hmem : L ∈ Work.Cusp.lattice v := by
    show L ∈ (Work.Cusp.lattice v : Set Work.Cusp.E3)
    rw [Work.RTOwed.cuspCert.lattice_eq]
    exact hL
  have hbdry := Work.RTOwed.cuspBdryMap_periodic v (Work.Cusp.xOf q) L hmem
  have hbnd : Work.Cusp.bndOfU (Work.Cusp.outerU v (Work.Cusp.xOf q + L))
      = Work.Cusp.bndOfU (Work.Cusp.outerU v (Work.Cusp.xOf q)) :=
    congrArg (fun z => (z.1.1.1 : Work.Cusp.E2)) hbdry
  have htorus :
      (fun i => ((Work.Cusp.outerY v (Work.Cusp.xOf q + L) i : ℝ) : AddCircle (1 : ℝ)))
        = (fun i => ((Work.Cusp.outerY v (Work.Cusp.xOf q) i : ℝ) : AddCircle (1 : ℝ))) :=
    congrArg (fun z => z.1.2) hbdry
  have hbeta : Work.Cusp.beta (Work.Cusp.xOf (q + Work.RTOwed.liftE4 L))
      = Work.Cusp.beta (Work.Cusp.xOf q) := by
    rw [hx]
    exact Work.Cusp.beta_lattice_periodic v (Work.Cusp.xOf q) L hmem
  by_cases hlt : q 3 < Work.Cusp.beta (Work.Cusp.xOf q)
  · -- Below the ceiling on both sides: the hyperbolic branch, `incMbar ∘ mbarLow`.
    have hlt' : (q + Work.RTOwed.liftE4 L) 3
        < Work.Cusp.beta (Work.Cusp.xOf (q + Work.RTOwed.liftE4 L)) := by
      rw [h3, hbeta]
      exact hlt
    rw [Work.Cusp.cuspCoordMTop_eq_le (Work.RTInstance.assemblyOf g) v (D v) c₁ δ₁ ⟨q, h₁⟩
          (le_of_lt hlt),
        Work.Cusp.cuspCoordMTop_eq_le (Work.RTInstance.assemblyOf g) v (D v) c₂ δ₂
          ⟨q + Work.RTOwed.liftE4 L, h₂⟩ (le_of_lt hlt')]
    rw [(R v).periodic q L hL]
  · -- On or above the ceiling on both sides: the filling branch, `incW ∘ cuspInvOuter`.
    have hge : Work.Cusp.beta (Work.Cusp.xOf q) ≤ q 3 := not_lt.mp hlt
    have hge' : Work.Cusp.beta (Work.Cusp.xOf (q + Work.RTOwed.liftE4 L))
        ≤ (q + Work.RTOwed.liftE4 L) 3 := by
      rw [h3, hbeta]
      exact hge
    rw [Work.Cusp.cuspCoordMTop_eq_ge (Work.RTInstance.assemblyOf g) v (D v) c₁ δ₁ ⟨q, h₁⟩ hge,
        Work.Cusp.cuspCoordMTop_eq_ge (Work.RTInstance.assemblyOf g) v (D v) c₂ δ₂
          ⟨q + Work.RTOwed.liftE4 L, h₂⟩ hge']
    unfold Work.Cusp.cuspCoordMTopUp
    refine Work.Cusp.incW_pair_congr (Work.RTInstance.assemblyOf g) v ?_ ?_
    · -- The recovered square point: the layer parameter `t` is unchanged, and `bndOfU ∘ outerU` is
      -- invariant because `outerU` shifts by an integer (via the boundary map `cuspBdryMap`).
      show (Work.Cusp.cuspInvOuter v q).1
        = (Work.Cusp.cuspInvOuter v (q + Work.RTOwed.liftE4 L)).1
      rw [cuspInvOuter_apply v q, cuspInvOuter_apply v (q + Work.RTOwed.liftE4 L),
        h3, hbeta, hx, hbnd]
    · -- The recovered torus coordinates: `outerY` shifts by integers, invisible in `AddCircle 1`.
      show (D v).tor.symm (fun i => (((Work.Cusp.cuspInvOuter v q).2 i : ℝ) : AddCircle (1 : ℝ)))
        = (D v).tor.symm (fun i =>
            (((Work.Cusp.cuspInvOuter v (q + Work.RTOwed.liftE4 L)).2 i : ℝ) : AddCircle (1 : ℝ)))
      congr 1
      funext i
      rw [cuspInvOuter_apply v q, cuspInvOuter_apply v (q + Work.RTOwed.liftE4 L), hx]
      exact (congrFun htorus i).symm

end Work.RTOWed
