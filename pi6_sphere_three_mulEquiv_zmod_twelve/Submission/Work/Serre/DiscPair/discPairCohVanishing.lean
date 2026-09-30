import Mathlib
import Submission.Work.Serre.DiscPair.discCellStepCoh

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The new-cell groups of the disc-pair bundle vanish off the fibre degree (cohomologically)

For `Γ' = attachCells (D-2) Γ ι f` and a Serre fibration `q : X → Γ'` whose fibre pairs
`((cylRetract q)⁻¹{c}, range (cylIncl q))` over the cell centres have relative rational cohomology
concentrated in degree `r+1` through degree `N+1`, the relative cohomology of the disc-pair bundle
`(cyl q, (cylRetract q)⁻¹Γ ∪ range (cylIncl q))` vanishes in every degree `m ≤ N+1` except
`m = D + r + 1`.

This is the *vanishing of the obstruction* of the cell-by-cell construction of the relative Thom
class: a relative class over the old part extends over the attached cells precisely because these
groups vanish in the two degrees `r+1` and `r+2` (see `Work.Serre.isIso_triple_f_of_isZero`).
-/

set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.DiscPair

noncomputable section

/-- A product of zero `ℚ`-modules is a zero `ℚ`-module. -/
theorem isZero_pi {ι : Type} {M : ι → ModuleCat ℚ} (h : ∀ i, IsZero (M i)) :
    IsZero (ModuleCat.of ℚ (∀ i, ↥(M i))) := by
  refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => ?_⟩
  funext i
  haveI : Subsingleton ↥(M i) := ModuleCat.subsingleton_of_isZero (h i)
  exact Subsingleton.elim _ _

/-- **The new-cell groups of the disc-pair bundle vanish off the fibre degree.** -/
theorem isZero_relCoh_discPairNewCells (D : ℕ) (hD : 2 ≤ D) (Γ : Type) [TopologicalSpace Γ]
    (ι : Type) (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (hne : ∀ i : ι, Nonempty (Work.StemsB.fibre q (Work.Serre.csrCentre (D - 2) Γ ι f i)))
    (r N : ℕ)
    (hcone : ∀ i : ι, ∀ j : ℕ, j ≤ N + 1 → j ≠ r + 1 →
      CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j
        ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D - 2) Γ ι f i})
        {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}))
    (m : ℕ) (hmD : D ≤ m) (hm : m ≤ N + 1 + D) (hmne : m ≠ D + r + 1) :
    CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ m (Work.Serre.cyl q)
      ((Work.Serre.cylRetract q) ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f) ∪
        Set.range (Work.Serre.cylIncl q))) := by
  classical
  obtain ⟨e⟩ := discCellStepCoh D hD Γ ι f q hq hne m hmD
  refine IsZero.of_iso ?_ e
  refine isZero_pi (fun i => ?_)
  refine hcone i (m - D) (by omega) ?_
  omega

end

end Work.Serre.DiscPair
