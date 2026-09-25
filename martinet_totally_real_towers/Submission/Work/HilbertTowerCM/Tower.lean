import Mathlib
import Submission.Work.HilbertTowerCM.Defs

/-!
# `Work.HilbertTowerCM.Tower` -- the levels supplied by an infinite unramified pro-`2` extension

`Work.ClassFieldTower.InfiniteProTwoExtension F` (the arithmetic output of the Route-B plan:
the maximal unramified pro-`2` extension of `F` is infinite) supplies, for every `N`, a finite
Galois unramified extension `L/F` with `[L : F] ≥ N` and `rootDiscr L = rootDiscr F`
(`Work.ClassFieldTower.MaximalUnramifiedProP.exists_unramifiedNumberField_rootDiscr_eq`).  Here
we package those levels as `UnramifiedLevel F` and record that their `ℚ`-degree is unbounded.

**This is all that the infinitude statement gives.**  Turning it into the benchmark needs in
addition that the levels have a large *real part* or are CM: that is the content of the walls of
`Work.HilbertTowerCM.Defs`, and it is **not** automatic — see `Work.HilbertTowerCM.Obstruction`.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace Work.HilbertTowerCM

/-- **The levels of an infinite unramified pro-`2` extension.**  For every `N` there is an
unramified level over `F` of `F`-degree at least `N`, hence (by the tower formula) of
`ℚ`-degree at least `N`. -/
theorem exists_level_finrank_ge {F : Type} [Field F] [NumberField F]
    (h : ClassFieldTower.InfiniteProTwoExtension F) (N : ℕ) :
    ∃ L : UnramifiedLevel F, N ≤ Module.finrank ℚ L.L := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨L, iL, iNL, iAL, hfd, hgal, hdeg, hdiff, -⟩ :=
    M.exists_unramifiedNumberField_rootDiscr_eq hM (N * Module.finrank ℚ F)
  letI : Field L := iL
  letI : NumberField L := iNL
  letI : Algebra F L := iAL
  letI : FiniteDimensional F L := hfd
  letI : IsGalois F L := hgal
  refine ⟨{ L := L, isUnramified := hdiff }, ?_⟩
  have hmul : Module.finrank ℚ F * Module.finrank F L = Module.finrank ℚ L :=
    Module.finrank_mul_finrank ℚ F L
  have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  have h1 : N ≤ Module.finrank F L :=
    le_trans (Nat.le_mul_of_pos_right N hpos) hdeg
  have h2 : Module.finrank F L ≤ Module.finrank ℚ L := by
    rw [← hmul]
    exact Nat.le_mul_of_pos_left _ hpos
  exact le_trans h1 h2

/-- Levels of unbounded `F`-degree exist in an infinite unramified pro-`2` extension. -/
theorem exists_level_finrankF_ge {F : Type} [Field F] [NumberField F]
    (h : ClassFieldTower.InfiniteProTwoExtension F) (N : ℕ) :
    ∃ L : UnramifiedLevel F, N ≤ Module.finrank F L.L := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨L, iL, iNL, iAL, hfd, hgal, hdeg, hdiff, -⟩ :=
    M.exists_unramifiedNumberField_rootDiscr_eq hM N
  letI : Field L := iL
  letI : NumberField L := iNL
  letI : Algebra F L := iAL
  letI : FiniteDimensional F L := hfd
  letI : IsGalois F L := hgal
  exact ⟨{ L := L, isUnramified := hdiff }, hdeg⟩

end Work.HilbertTowerCM
