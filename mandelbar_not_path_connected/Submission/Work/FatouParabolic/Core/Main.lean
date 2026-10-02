/-
Copyright: subproject `Submission/Work/FatouParabolic/` of `mandelbar_not_path_connected`.

# The petal/Liouville core of Fatou's theorem: assembly

This module assembles the design of `Submission/Work/FatouParabolic/NOTES.md` §4 into

> **`Work.FatouParabolic.exists_isCriticalPoint_in_basin_of_flowerImageFix`**: a polynomial map
> `F` of degree `≥ 2` with a multiplier-one fixed point `z₀` which has a Leau–Fatou flower with
> the petal image property has a critical point in the basin of `z₀`.

The proof is the corrected design of the lead's note `NOTES_LEAD_mandelbar_gaps2.md` §2.1:

1. let `Ω₀` be the **immediate basin** `Core.immBasin F z₀ p₀` through a petal point `p₀` (the
   component of the punctured basin through `p₀`, Q1 of the note).  It is open, preconnected,
   `F`-invariant and bounded by the escape estimate;
2. if `Ω₀` contained no critical point, every iterate `F^[n] : Ω₀ → Ω₀` would be a covering
   (`Core.isCoveringMap_iterate_immBasin`, Q2);
3. the inverse petal coordinate `Ψ₀ = (φa)⁻¹` on the tail strips
   (`Core.exists_petalInverse`, Q3) lifts through those coverings to holomorphic functions on
   larger and larger strips (`Core.exists_strip_lift`, Q4), which glue to an entire function
   `Ψ̂` with values in the bounded `Ω₀` (Q5);
4. `Ψ̂` is bounded and entire, hence constant by Liouville, but it agrees on a tail strip with
   the injective `Ψ₀` (Q6, `Core.exists_isCriticalPoint_in_immBasin`): contradiction.

The older statements in this file that take `ParabolicBasinSimplyConnected` (which is *false* for
the full basin, see `Core/Defs.lean`) are kept only because sibling files use them; they are
documented as superseded.
-/
import Mathlib
import Submission.Work.FatouParabolic.Core.Defs
import Submission.Work.FatouParabolic.Core.isOpen_puncturedBasin
import Submission.Work.FatouParabolic.Core.isBounded_puncturedBasin_of_escape
import Submission.Work.FatouParabolic.Core.extFatou_independent
import Submission.Work.FatouParabolic.Core.extFatou_abel
import Submission.Work.FatouParabolic.Core.extFatou_differentiableOn
import Submission.Work.FatouParabolic.Core.extFatou_injective_of_injOn
import Submission.Work.FatouParabolic.Core.extFatou_surjective_of_imageStrip
import Submission.Work.FatouParabolic.Core.false_of_bounded_of_injOn_of_surjective
import Submission.Work.FatouParabolic.Core.injOn_of_simplyConnected_of_noCriticalPoint
import Submission.Work.FatouParabolic.Core.ImmBasin.Defs
import Submission.Work.FatouParabolic.Core.exists_isCriticalPoint_in_immBasin
import Submission.Work.FatouParabolic.Poly.isPolynomialMap_surjective
import Submission.Work.FatouParabolic.Poly.isPolynomialMap_basinEscape
import Submission.Work.FatouParabolic.Poly.isPolynomialMap_differentiable

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter

namespace Work.FatouParabolic

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-! ## The corrected core (no simple-connectivity hypothesis) -/

/-- **Fatou's theorem in the simple parabolic case, from the flower alone** (Q6 of
`NOTES_LEAD_mandelbar_gaps2.md` §2.1): a polynomial map of degree `≥ 2` with a multiplier-one
fixed point `z₀` which has a Leau–Fatou flower with the petal image property has a critical point
in the basin of `z₀`.  No simple connectivity of a basin is assumed: the inverse branch of the
coverings `F^[n]` is lifted along the petal orbit on horizontal strips, and Liouville is applied
to the resulting bounded entire function. -/
theorem exists_isCriticalPoint_in_basin_of_flowerImageFix {F g : ℂ → ℂ} {z₀ : ℂ}
    (hF : IsPolynomialMapOfDegreeAtLeastTwo F) (hfix : F z₀ = z₀) (h1 : deriv F z₀ = 1)
    (fl : FlowerImageFix F g z₀) :
    ∃ w : ℂ, IsCriticalPoint F w ∧ w ∈ basin F z₀ := by
  obtain ⟨p₀, hp₀Pg⟩ := fl.Pg_nonempty
  have hp₀ : p₀ ∈ fl.Pa := fl.Pg_sub hp₀Pg
  obtain ⟨w, hwΩ, hw0⟩ := Core.exists_isCriticalPoint_in_immBasin hF hfix h1 fl hp₀
  exact ⟨w, hw0, Core.immBasin_subset_basin hwΩ⟩

/-! ## The superseded form (via simple connectivity of the full basin) -/

/-- **The Liouville contradiction of the design.**  If the punctured basin of `z₀` carries a
flower whose petal image contains the tails of horizontal strips, and the extended Fatou
coordinate is injective on the basin, then no point of the basin is a critical point. -/
theorem not_forall_deriv_ne_zero_of_flower {F g : ℂ → ℂ} {z₀ : ℂ}
    (hF : Differentiable ℂ F) (hfix : F z₀ = z₀) (hsurj : Function.Surjective F)
    (hesc : BasinEscape F) (fl : Work.FatouCoordFix.ParabolicFlowerFix F g z₀)
    (hstrip : PetalImageStrip fl.toParabolicFlower)
    (hinj : Set.InjOn F (puncturedBasin F z₀)) :
    ¬ (∀ w ∈ puncturedBasin F z₀, deriv F w ≠ 0) := by
  intro hnocrit
  have hopen : IsOpen (puncturedBasin F z₀) :=
    Core.isOpen_puncturedBasin fl hfix hF
  have hdiff : DifferentiableOn ℂ (extFatou fl) (puncturedBasin F z₀) :=
    Core.extFatou_differentiableOn fl hF hopen
  have hbdd : Bornology.IsBounded (puncturedBasin F z₀) :=
    Core.isBounded_puncturedBasin_of_escape (F := F) (z₀ := z₀) hesc
  have hinjE : Set.InjOn (extFatou fl) (puncturedBasin F z₀) :=
    Core.extFatou_injective_of_injOn fl hinj
  have hsurjE : ∀ τ : ℂ, ∃ z ∈ puncturedBasin F z₀, extFatou fl z = τ :=
    Core.extFatou_surjective_of_imageStrip hfix hsurj fl hstrip
  exact Core.false_of_bounded_of_injOn_of_surjective fl hopen hdiff hbdd hinjE hsurjE

/-- Superseded form of the core (it assumes simple connectivity of the *full* punctured basin,
which is false in general — see `Core/Defs.lean`), kept because
`Core/exists_criticalPoint_in_basin_of_rootParabolic` uses it.  Use
`Work.FatouParabolic.exists_isCriticalPoint_in_basin_of_flowerImageFix` instead. -/
theorem exists_isCriticalPoint_in_basin_of_flowerImageFix_of_simplyConnected {F g : ℂ → ℂ}
    {z₀ : ℂ} (hF : IsPolynomialMapOfDegreeAtLeastTwo F) (hfix : F z₀ = z₀)
    (h1 : deriv F z₀ = 1) (fl : FlowerImageFix F g z₀)
    (hsc : ParabolicBasinSimplyConnected F z₀) :
    ∃ w : ℂ, IsCriticalPoint F w ∧ w ∈ basin F z₀ := by
  have hdiff : Differentiable ℂ F := Poly.isPolynomialMap_differentiable hF
  have hsurj : Function.Surjective F := Poly.isPolynomialMap_surjective hF
  have hesc : BasinEscape F := Poly.isPolynomialMap_basinEscape hF
  have hnot : ¬ (∀ w ∈ puncturedBasin F z₀, deriv F w ≠ 0) := by
    intro hnocrit
    have hinj : Set.InjOn F (puncturedBasin F z₀) :=
      Core.injOn_of_simplyConnected_of_noCriticalPoint hdiff hfix hsurj hesc hsc hnocrit
    exact not_forall_deriv_ne_zero_of_flower hdiff hfix hsurj hesc fl.toParabolicFlowerFix
      fl.petalImageStrip hinj hnocrit
  push_neg at hnot
  obtain ⟨w, hwΩ, hw0⟩ := hnot
  exact ⟨w, hw0, puncturedBasin_subset_basin hwΩ⟩

end

end Work.FatouParabolic
