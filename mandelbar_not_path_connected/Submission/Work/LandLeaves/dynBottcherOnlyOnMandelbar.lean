/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# Ledger item 2 — `DynBottcherOnlyOnMandelbar`, proved without any winding argument

`Work.LANDCL.DynBottcherOnlyOnMandelbar` says: if `φ` is a Böttcher coordinate of `T_c` on the
*whole* escaping set (`Work.ParamRays.IsDynBottcher c φ`), then `c` lies in the mandelbar.

The ledger §5 records the intended proof as a *winding* argument (a loop around the escaping
critical value has winding `±1`, which `conj (·)²` carries to `∓2`).  That argument is not needed:
the tricorn satisfies

`T_c (-z) = conj (-z)² + c = conj z² + c = T_c z`,

i.e. **`T_c` is even**.  Hence for any continuous Böttcher coordinate the function
`ρ z = φ (-z) / φ z` is continuous on the escaping set, takes values in `{±1}` (from the Böttcher
equation at `z` and at `-z`, whose right-hand sides agree because `T_c` is even) and equals `-1`
far out (asymptotic clause).  By preconnectedness of the escaping set
(`Work.ParamRays.isPreconnected_escapingSet`, proved in the workspace) `ρ` is *constant*, so
**`φ` is odd**: `φ (-z) = -φ z` — this is `Work.Landing.Rays.isDynBottcher_odd`, already in the
tree.

Now if `c ∉ Mandelbar` then the critical orbit is unbounded, hence the critical point `0`
escapes (`Work.ParamRays.escaping_iff_not_bounded` + `mem_mandelbar_iff_bounded`), so `0` is a
point of the escaping set.  Evaluating the oddness at `z = 0` gives `φ 0 = -φ 0`, i.e. `φ 0 = 0`,
contradicting `Work.ParamRays.IsDynBottcher.ne_zero` (`φ` has no zeros on the escaping set).

So the obstruction is the *symmetry* `T_c (-z) = T_c z`, not monodromy: a continuous solution of
`φ ∘ T_c = conj ∘ φ²` blowing up like the identity at infinity cannot be single-valued on a set
containing the critical point.  (Pointwise solutions do exist off the mandelbar — e.g.
`z ↦ exp (G_c z)` — which is why the defect is invisible to a pointwise numerical check: what
fails is *continuity*, i.e. the consistency of the square-root choices.)

Hence the whole GM/LANDCL chain may drop the winding chapter for this input; the ledger's item 2
is discharged here.
-/
import Submission.Work.LandLeaves.Defs
import Submission.Work.LANDCL.Defs
import Submission.Work.Landing.Rays.preimage_mem_dynRay
import Submission.Work.ParamRays.Interface
import Submission.Work.LANDCL.GM
import Submission.Work.Bottcher.CritBottcherExists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **Ledger item 2.**  A Böttcher coordinate on the whole escaping set exists only inside the
mandelbar: `Work.LANDCL.DynBottcherOnlyOnMandelbar`.

The proof is the parity/oddness argument described in the module docstring: a continuous solution
of `φ (T_c z) = conj (φ z)²` is forced to be odd (`Work.Landing.Rays.isDynBottcher_odd`), while
off the mandelbar the critical point `0` belongs to the escaping set, where `φ 0 ≠ 0`. -/
theorem dynBottcherOnlyOnMandelbar : Work.LANDCL.DynBottcherOnlyOnMandelbar := by
  intro c ⟨φ, hφ⟩
  by_contra hc
  -- off the mandelbar the critical point escapes, so it lies in the escaping set
  have h0 : Work.ParamRays.Escaping c 0 :=
    (Work.ParamRays.escaping_iff_not_bounded c 0).mpr
      (fun hb => hc ((Work.ParamRays.mem_mandelbar_iff_bounded c).mpr hb))
  -- a Böttcher coordinate is odd on the escaping set
  have hodd : φ (-0) = -φ 0 := Work.Landing.Rays.isDynBottcher_odd hφ h0
  have hne : φ 0 ≠ 0 := hφ.ne_zero h0
  simp only [neg_zero] at hodd
  -- `φ 0 = -φ 0` forces `φ 0 = 0`, contradicting `ne_zero`
  exact hne (by
    have h : φ 0 + φ 0 = 0 := eq_neg_iff_add_eq_zero.mp hodd
    exact add_self_eq_zero.mp h)

/-! ## Consequences: the scope statement in both directions -/

/-- **`IsDynBottcher` exists exactly on the mandelbar.**  Together with
`Work.Bottcher.exists_isDynBottcher_of_mem_mandelbar` (the existence half, proved in the Böttcher
area), `dynBottcherOnlyOnMandelbar` gives the equivalence which the docstrings of the
`ParamRays`/`Landing` areas state informally: a Böttcher coordinate of `T_c` on the whole escaping
set exists **iff** `c` lies in the mandelbar. -/
theorem dynBottcherExists_iff_mem_mandelbar (c : ℂ) :
    Work.ParamRays.DynBottcherExists c ↔ c ∈ Mandelbar :=
  ⟨fun h => dynBottcherOnlyOnMandelbar c h,
    fun hc => Work.Bottcher.exists_isDynBottcher_of_mem_mandelbar c hc⟩

/-- **A parameter at which a dynamic ray lands lies in the mandelbar** — the scope input of
`Work.LANDCL.GM.mem_mandelbar_of_landsAt` discharged, so that no caller has to pass
`DynBottcherOnlyOnMandelbar` around. -/
theorem mem_mandelbar_of_landsAt {c : ℂ} {θ : ℝ} {y : ℂ} (h : Work.Landing.landsAt c θ y) :
    c ∈ Mandelbar :=
  Work.LANDCL.GM.mem_mandelbar_of_landsAt dynBottcherOnlyOnMandelbar h

/-! ## The consequence for the `gm` row

With `DynBottcherOnlyOnMandelbar` proved, the reduction `Work.LANDCL.repellingRayParamStable`
(Goldberg–Milnor B.1 in parameter form) depends on the two remaining inputs `NakaneInput` (the
parameter Böttcher map) and `GoldbergMilnorB1` (the dynamical stability of the landing at a
repelling point) only. -/

/-- **`gm` with the scope input discharged**: Goldberg–Milnor B.1 in parameter form from the
parameter Böttcher map and the dynamical Goldberg–Milnor statement. -/
theorem repellingRayParamStable_of_goldbergMilnor (hN : Work.ParamRays.NakaneInput)
    (hB1 : Work.LANDCL.GoldbergMilnorB1) : Work.FSeed.RepellingRayParamStable :=
  Work.LANDCL.repellingRayParamStable hN hB1 dynBottcherOnlyOnMandelbar

end Work.LandLeaves
