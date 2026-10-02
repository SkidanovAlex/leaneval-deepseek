/-
# `Work.SeedFatou` — Fatou's strong form at the seed: vocabulary and bridges

The area `Submission/Work/SeedFatou/` proves

* `Work.SeedFatou.fatouCritInBasin : Work.SeedExist.FatouCritInBasin S.c S.z₁ (flowerOf S).Pg`
  for **every** `S : Work.SeedExist.RootSeedData`;
* `Work.SeedFatou.rootArcHeightZero : Work.FinalFix.RootArcHeightZero` with no hypothesis.

The route is that of `NOTES_LEAD_mandelbar_final2.md` §2.2 (steps A1–A9, lemmas B1–B7): the
**simple** Fatou theorem `Work.FatouParabolic2.exists_petalData_of_simple` supplies petal data at
the simple parabolic point `z₁` of `F c = (T_c)^[10]`; the Liouville/covering step
`Work.FatouParabolic2.exists_criticalPoint_in_immBasin` locates a critical point `w` of `F c` in
the *immediate* basin `Ω` through a petal point; the two clauses of `FatouCritInBasin` are then
read off `Ω` by elementary iterate bookkeeping.

This file fixes the vocabulary: the seed map `F`, its identification with `(T_c)^[10]`, the
commutation of the `T_c`- and `F c`-iterates, and the packaged immediate-basin datum
`Work.SeedFatou.CritImmData` consumed by the two clause lemmas.

## Main definitions

* `Work.SeedFatou.CritImmData S` — a critical point `w` of `F c` in a preconnected,
  `F c`-invariant subset `Ω` of `interior (basin (F c) z₁)` that contains the half-petal `Pg`;
* `Work.SeedFatou.ContinuousTantibar`, `F_iterate_comm_T` — the elementary bridges.
-/
import Mathlib
import Submission.Work.SeedExist.Setup
import Submission.Work.SeedExist.Flower
import Submission.Work.SeedExist.Sides.notMem_interior_of_flower
import Submission.Work.SeedExist.Sides.mapsTo_seed_U
import Submission.Work.SeedLimit.derivTsqIterateK
import Submission.Work.FatouParabolic2.exists_criticalPoint_in_immBasin
import Submission.Work.FatouParabolic2.fatouParabolicInput_simple
import Submission.Work.FatouParabolic.Poly.tsq_iterate_isPolynomialMap
import Submission.Work.ELRig.Pa_subset_K
import Submission.Work.Final.equatorLeak_shift
import Submission.Work.ELPull.tantibar_openMap
import Submission.Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Work.SeedFatou

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Elementary bridges -/

/-- `T_c : z ↦ z̄² + c` is continuous (it is a polynomial in `z` and `z̄`). -/
theorem continuous_tantibar (c : ℂ) : Continuous (Tantibar c) := by
  rw [show Tantibar c = fun z : ℂ => (starRingEnd ℂ) z ^ 2 + c from rfl]
  continuity

/-- **`F c = (T_c)^[10]`**: the second return map of the tricorn is the tenth iterate of `T_c`. -/
theorem F_eq_tantibar_ten (c : ℂ) : Work.FSeed.F c = (Tantibar c)^[10] :=
  funext fun z => (Work.FSeed.Tantibar_iterate_ten c z).symm

/-- The `n`-th iterate of `F c` is the `10 n`-th iterate of `T_c`. -/
theorem F_iterate_eq_tantibar_ten (c : ℂ) (n : ℕ) :
    (Work.FSeed.F c)^[n] = (Tantibar c)^[10 * n] := by
  rw [F_eq_tantibar_ten c, ← Function.iterate_mul]

/-- **The `T_c`- and the `F c`-iterates commute**: `F c = (T_c)^[10]` is itself a `T_c`-iterate. -/
theorem F_iterate_comm_T (c : ℂ) (n j : ℕ) (z : ℂ) :
    (Work.FSeed.F c)^[n] ((Tantibar c)^[j] z) = (Tantibar c)^[j] ((Work.FSeed.F c)^[n] z) := by
  calc (Work.FSeed.F c)^[n] ((Tantibar c)^[j] z)
      = (Tantibar c)^[10 * n] ((Tantibar c)^[j] z) := by rw [F_iterate_eq_tantibar_ten]
    _ = (Tantibar c)^[10 * n + j] z :=
        (Function.iterate_add_apply (Tantibar c) (10 * n) j z).symm
    _ = (Tantibar c)^[j + 10 * n] z := by rw [show 10 * n + j = j + 10 * n from by omega]
    _ = (Tantibar c)^[j] ((Tantibar c)^[10 * n] z) :=
        Function.iterate_add_apply (Tantibar c) j (10 * n) z
    _ = (Tantibar c)^[j] ((Work.FSeed.F c)^[n] z) := by rw [F_iterate_eq_tantibar_ten]

/-- `S.c` is the image of the critical point `0`: `T_c 0 = c`. -/
theorem Tantibar_zero (c : ℂ) : Tantibar c 0 = c := by
  simp [Tantibar]

/-! ## The packaged immediate-basin datum of the seed -/

/-- **The immediate-basin datum of the seed**: a critical point `w` of `F c = (T_c)^[10]` lying in
a preconnected `F c`-invariant set `Ω ⊆ interior (basin (F c) z₁)` which contains the
`g`-invariant half-petal `Pg` of the repaired Leau–Fatou flower `flowerOf S`.

This is the output of step A4–A5 of `NOTES_LEAD_mandelbar_final2.md` §2.2 (lemma B3): the petal
point `p₀ ∈ Pg ∩ pd.Pa` produces `Ω := immBasin (F c) z₁ p₀`, and `Pg ⊆ Ω` because `Pg` is
preconnected, open and contained in the basin.

Both clauses of `Work.SeedExist.FatouCritInBasin` are read off this datum. -/
structure CritImmData (S : Work.SeedExist.RootSeedData) where
  /-- the immediate basin of `z₁` through the petal point `p₀` -/
  Ω : Set ℂ
  /-- the critical point of `F c` found in `Ω` -/
  w : ℂ
  isPreconnected_Ω : IsPreconnected Ω
  Ω_subset : Ω ⊆ interior (Work.FatouParabolic.basin (Work.FSeed.F S.c) S.z₁)
  mapsTo_Ω : Set.MapsTo (Work.FSeed.F S.c) Ω Ω
  /-- the half-petal of the flower of the seed lies in `Ω` -/
  Pg_subset : (Work.SeedExist.flowerOf S).Pg ⊆ Ω
  w_mem : w ∈ Ω
  /-- `w` is a critical point of `F c` -/
  deriv_w_eq_zero : deriv (Work.FSeed.F S.c) w = 0

end Work.SeedFatou

end
