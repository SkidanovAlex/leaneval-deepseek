import Mathlib
import Submission.Work.RatHurewicz.cycleModelFiniteImage2
import Submission.Work.Serre.Defs

/-!
# The support of a rational cycle: a space with finitely generated `π₁`

This file records `Work.Rat.RankOneC1.exists_model_of_cycle_fg`: every rational cycle `z` in
degree `n + 1 ≥ 1` on a space `X` with trivial `π₀` is carried by a cycle `w` on a space `Y` with
finitely generated `π₁`, via a map `φ : Y → X` which sends the base point of `Y` to `x₀`.

It is the `π₁`-torsion-free variant of `Work.RatHurewicz.cycleModelFiniteImage2` (which concludes
that the *image* of `π₁(Y)` in `π₁(X)` is finite, using that `π₁(X)` is torsion): here only the
finiteness of `π₁(Y)` itself is needed, so the torsion hypothesis is dropped.

This is the first half of the reduction of `Work.Rat.RankOneC1Ab` to the finitely generated case:
the second half is the killing step `Work.Rat.RankOneC1.exists_killedModel_based`.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Work.Rat

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **The support of a rational cycle, as a space with finitely generated `π₁`.** -/
theorem exists_model_of_cycle_fg {X : Type} [TopologicalSpace X] (x₀ : X) (n : ℕ)
    (hconnX : Subsingleton (HomotopyGroup (Fin 0) X x₀))
    (z : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X (n + 1))
    (hz : (Work.Cohomology.singularChains ℚ (TopCat.of X)).d (n + 1) n z = 0) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (y₀ : Y) (φ : C(Y, X))
      (w : (Work.Cohomology.singularChains ℚ (TopCat.of Y)).X (n + 1)),
      φ y₀ = x₀ ∧
      Subsingleton (HomotopyGroup (Fin 0) Y y₀) ∧
      (Work.Cohomology.singularChains ℚ (TopCat.of Y)).d (n + 1) n w = 0 ∧
      (Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of X) (TopCat.ofHom φ)).f (n + 1) w = z ∧
      Group.FG (HomotopyGroup (Fin 1) Y y₀) := by
  classical
  by_cases hz0 : z = 0
  · refine ⟨PUnit, inferInstance, PUnit.unit, ⟨fun _ => x₀, continuous_const⟩, 0, rfl, ?_, ?_, ?_, ?_⟩
    · exact Work.Stems.subsingleton_of_contractible (N := Fin 0) PUnit.unit
    · rw [map_zero]
    · rw [map_zero, hz0]
    · haveI : Subsingleton (HomotopyGroup (Fin 1) PUnit PUnit.unit) :=
        Work.Stems.subsingleton_of_contractible (N := Fin 1) PUnit.unit
      haveI : Finite (HomotopyGroup (Fin 1) PUnit PUnit.unit) := Finite.of_subsingleton
      exact Group.fg_iff_monoid_fg.mpr Monoid.fg_of_finite
  · haveI hne : Nonempty (Work.RatHurewicz.cycleMData hconnX n z).Idx := by
      obtain ⟨s, hs⟩ := Work.RatHurewicz.cycleSupport_nonempty_of_ne_zero (n + 1) z hz0
      exact ⟨⟨s, hs⟩⟩
    refine ⟨Work.RatHurewicz.Model (Work.RatHurewicz.cycleMData hconnX n z), inferInstance,
      Work.RatHurewicz.modelBase (Work.RatHurewicz.cycleMData hconnX n z),
      Work.RatHurewicz.cycleModelToX hconnX n z, Work.RatHurewicz.cycleChain hconnX n z,
      Work.RatHurewicz.cycleModelToX_modelBase hconnX n z,
      Work.RatHurewicz.subsingleton_pi0_model _, ?_, ?_, ?_⟩
    · exact Work.RatHurewicz.cycleChain_d hconnX n z hz
    · exact Work.RatHurewicz.cycleChain_map hconnX n z
    · exact Work.RatHurewicz.piOneModel_fg (Work.RatHurewicz.cycleMData hconnX n z)

end

end Work.Rat
