import Mathlib
import Submission.Work.Serre.DiscPair.discPairTargetLine
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.C1Cyl
import Submission.Work.Thom.Cohomology
import Submission.Work.Serre.Engine
import Submission.Work.StemsB.Fibrations
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.Serre.EulerFibreRoot
import Submission.Work.Serre.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The two inputs that every formulation of the E3(b) detection takes as hypotheses (area H5)

The E3(b) "detection" (the fibre restriction `H^{r+1}(cyl q, A) → H^{r+1}(P_b, A_b)` is non-zero /
an iso — `Work.RatHurewicz.discPairFibreRestriction`, `Work.Serre.DiscPair.fibreRestrictionNonvanishing`,
`Work.Serre._opcr.fibreRestriction_ne_zero_of_invisible`,
`Work.Serre._opcr.fibreRestriction_ne_zero_of_pairComparison`, …) is stated in the workspace in
several equivalent forms, and **all of them carry the same two side conditions as hypotheses**:

* `hpos` — `¬ IsZero (RelCoh ℚ (r+1) (cyl q) (range (cylIncl q)))`, i.e. the relative Thom group is
  non-zero.  In the cellular-step context this is a *consequence of the induction hypothesis*: the
  proved `Work.Serre.DiscPair.discPairTargetLine` gives `RelCoh ℚ (r+1) (cyl q) (range (cylIncl q))
  ≅ ℚ` from `IH`, and `ℚ` is not a zero module (`cellStep_relCoh_ne_zero` below).
* the *case* hypothesis of the invisible branch of the detection (in the `_opcr` files: `hinvis`,
  resp. the vanishing of `H^r(X;ℚ) → H^r(F_b;ℚ)`).  This is a hypothesis of an **exhaustive case
  split** on the fibration (visible branch: the fibre restriction is non-zero for trivial reasons,
  `fibreRestriction_ne_zero_of_visible`); it is neither implied by the other hypotheses nor a defect.
  A bundle in the visible branch (e.g. a trivial `S^r`-bundle) satisfies its negation, so such a
  bundle is not a counterexample.  Unconditional instead is `cellStep_cylRetract_fibre_zero` below:
  the composite `F_b ↪ cyl q --cylRetract--> Γ'` is the constant map at `b`.

Both lemmas are stated in the *cellular-step* context (the hypotheses of
`Work.Stems.thomCylCellStepRace`), i.e. exactly where the detection is consumed.  Nothing here
duplicates the detection itself: these are its two bookkeeping inputs, isolated so that a prover of
the detection (or of the cellular step) can use them instead of re-deriving them.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Stems

/-- **`hpos` in the cellular-step context.**  The induction hypothesis makes the relative Thom group
non-zero: `Work.Serre.DiscPair.discPairTargetLine` gives it isomorphic to `ℚ`. -/
theorem cellStep_relCoh_ne_zero (r N D : ℕ) (hr : 1 ≤ r) (hD : 2 ≤ D) (hrN : r ≤ N)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (CategoryTheory.Iso (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r)
        (ModuleCat.of ℚ ℚ)))
    (IH : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q
      (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f)))) :
    ¬ CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q)
        (Set.range (Work.Serre.cylIncl q))) := by
  obtain ⟨e⟩ := Work.Serre.DiscPair.discPairTargetLine r N D hr hD hrN hΓ ι f q hq hpc hvan hgen IH
  intro hz
  have hzq : CategoryTheory.Limits.IsZero (ModuleCat.of ℚ ℚ) :=
    CategoryTheory.Limits.IsZero.of_iso hz e.symm
  haveI : Subsingleton ℚ := ModuleCat.isZero_iff_subsingleton.mp hzq
  exact one_ne_zero (Subsingleton.elim (1 : ℚ) 0)

/-!
## Note (H5, 2026-09-27) — a withdrawn claim

An earlier version of this file claimed that the hypothesis

```
hinvis : ∀ a : Coh ℚ r ↥(Set.range (cylIncl q)), (CohMap (A_b ↪ A) ℚ r).hom a = 0
```

of `Work.Serre._opcr.fibreRestriction_ne_zero_of_{invisible,pairComparison}` is *false*, and hence
that those statements are vacuous.  **That claim is withdrawn** (project-lead probe round, same
day): `hinvis` (equivalently: `H^r(X;ℚ) → H^r(F_b;ℚ) = 0`) is the hypothesis of the **invisible
branch** of an *exhaustive case split* on the fibration; the visible branch is
`Work.Serre._opcr.fibreRestriction_ne_zero_of_visible`.  A case hypothesis that fails for some `q`
is not a vacuity — the trivial `S^r`-bundle lies in the *visible* branch, which is exactly why it
refutes nothing.  The companion declaration `Work.Stems.hinvisRefuted` was cancelled for the same
reason and must not be used.

`cellStep_relCoh_ne_zero` (the `hpos` input) is unaffected: it is a *consequence* of the induction
hypothesis, and it is used by every formulation of the detection.
-/

/-- **The retraction followed by the fibre inclusion is constant.**  The composite of the fibre
inclusion `F_b = (cylRetract q)⁻¹{b} ↪ cyl q` with `cylRetract q` is the constant map at `b`; hence
the pullback of every positive-degree class of `Γ` to the fibre vanishes.  (Unconditional; it is
*not* the case hypothesis of the invisible branch, which concerns the fibre inclusion alone.) -/
theorem cellStep_cylRetract_fibre_zero {Γ : Type} [TopologicalSpace Γ] {X : Type}
    [TopologicalSpace X] (q : C(X, Γ)) (b : Γ) {m : ℕ} (hm : 0 < m) :
    ∀ a : Work.Thom.Coh ℚ m Γ,
      (Work.Thom.CohMap
        ((Work.Serre.cylRetract q).comp (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥((Work.Serre.cylRetract q) ⁻¹' {b}), Work.Serre.cyl q))) ℚ m).hom a = 0 := by
  intro a
  have hcomp : (Work.Serre.cylRetract q).comp (⟨Subtype.val, continuous_subtype_val⟩ :
      C(↥((Work.Serre.cylRetract q) ⁻¹' {b}), Work.Serre.cyl q))
      = ContinuousMap.const _ b := by
    ext x
    exact Set.mem_singleton_iff.mp x.2
  rw [hcomp]
  have hfac : ContinuousMap.const (↥((Work.Serre.cylRetract q) ⁻¹' {b})) b
      = (ContinuousMap.const PUnit b).comp
        (ContinuousMap.const (↥((Work.Serre.cylRetract q) ⁻¹' {b})) PUnit.unit) := rfl
  rw [hfac, Work.Thom.CohMap_comp]
  have hz : CategoryTheory.Limits.IsZero (Work.Thom.Coh ℚ m PUnit) :=
    Work.Serre.isZero_coh_of_ratAcyclic (Work.Serre.ratAcyclic_of_contractible PUnit) hm
  have hzero : Work.Thom.CohMap
      (ContinuousMap.const (↥((Work.Serre.cylRetract q) ⁻¹' {b})) PUnit.unit) ℚ m = 0 :=
    CategoryTheory.Limits.IsZero.eq_zero_of_src hz _
  rw [hzero]
  simp

end Work.Stems
