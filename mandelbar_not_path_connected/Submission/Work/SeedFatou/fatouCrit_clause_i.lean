/-
# Clause (i) of `FatouCritInBasin` at the seed

Clause (i) of `Work.SeedExist.FatouCritInBasin` says that some `T_c`-iterate (with exponent
`< 5`) of a point of the half-petal `Pg` of the repaired Leau--Fatou flower of the seed lies in
the connected component of the critical point `0` in `interior (K c)`.

This file reads the clause off the packaged immediate-basin datum `Work.SeedFatou.CritImmData S`
of `SeedFatou/Defs.lean`:

* the critical point `w` of `F c = (T_c)^[10]` lying in `Ω` reaches the critical point `0` of
  `T_c` within fewer than `10` `T_c`-steps (`exists_Tantibar_iterate_eq_zero_aux`, from the
  critical-point criterion `Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff`);
* `Ω` is preconnected and lies in `interior (K c)` (`basin_subset_K_aux`: an orbit converging to
  a point is bounded); hence so does `(T_c)^[k] '' Ω` (`image_interior_K_aux`: `T_c` is an open
  map and preserves `K c`), and it contains `0 = (T_c)^[k] w`; so it is contained in the
  connected component of `0`;
* the exponent is reduced modulo `5` using the `g = (T_c)^[5]`-invariance of `Pg`.

The auxiliary lemmas are `private` (the public counterparts live in the sibling files
`basin_subset_K.lean`, `image_interior_K_subset.lean`, `exists_tantibar_iterate_eq_zero.lean`).
-/
import Mathlib
import Submission.Work.SeedFatou.Defs
import Submission.Work.FatouParabolic.Critical.tsq_iterate_of_Tantibar_eq_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.SeedFatou

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Auxiliary facts -/

/-! ### The basin of `z₁` under `F c` lies in the filled Julia set of `T_c` -/

/-- **A convergent sub-orbit is bounded**: if the `F c = (T_c)^[10]`-orbit of `z` converges to
`z₁`, the whole `T_c`-orbit of `z` is bounded, i.e. `z ∈ K c`. -/
private theorem basin_subset_K_aux (c z₁ : ℂ) :
    Work.FatouParabolic.basin (Work.FSeed.F c) z₁ ⊆ Work.EL.K c := by
  intro z hz
  show Work.ParamRays.BoundedOrbit c z
  have hsub : Tendsto (fun n : ℕ => (Tantibar c)^[10 * n] z) atTop (nhds z₁) :=
    (show Tendsto (fun n : ℕ => (Work.FSeed.F c)^[n] z) atTop (nhds z₁) from hz).congr'
      (Eventually.of_forall fun n => congrFun (F_iterate_eq_tantibar_ten c n) z)
  exact Work.ELRig.boundedOrbit_of_tendsto_iterate_mul (c := c) (w := z₁) (z := z)
    (by norm_num) hsub

/-! ### `T_c` preserves the filled Julia set -/

/-- `T_c` maps the filled Julia set `K c = {z | BoundedOrbit c z}` into itself: the orbit of
`T_c z` is the tail of the orbit of `z`. -/
private theorem mapsTo_K_Tantibar (c : ℂ) :
    MapsTo (Tantibar c) (Work.EL.K c) (Work.EL.K c) := by
  intro z hz
  obtain ⟨M, hM⟩ := hz
  exact ⟨M, fun n => by
    rw [← Work.ParamRays.orbit_one_add c z n]
    exact hM (n + 1)⟩

/-! ### The interior of the filled Julia set is `T_c`-invariant -/

/-- **`(T_c)^[k] '' interior (K c) ⊆ interior (K c)`**, for every `k`.  For `k = 1`: `T_c` is an
open map, so the image of the open set `interior (K c)` is open, and it lies in `K c`; an open
subset of `K c` lies in `interior (K c)` (`interior_maximal`).  Induct. -/
private theorem image_interior_K_aux (c : ℂ) (k : ℕ) :
    (Tantibar c)^[k] '' interior (Work.EL.K c) ⊆ interior (Work.EL.K c) := by
  have hstep : (Tantibar c) '' interior (Work.EL.K c) ⊆ interior (Work.EL.K c) :=
    interior_maximal
      (fun y hy => by
        obtain ⟨z, hz, rfl⟩ := hy
        exact mapsTo_K_Tantibar c (interior_subset hz))
      ((Work.ELPull.isOpenMap_Tantibar c) (interior (Work.EL.K c)) isOpen_interior)
  induction k with
  | zero => simp
  | succ k ih =>
      calc (Tantibar c)^[k.succ] '' interior (Work.EL.K c)
          = (Tantibar c) '' ((Tantibar c)^[k] '' interior (Work.EL.K c)) := by
            rw [Function.iterate_succ', Set.image_comp]
        _ ⊆ (Tantibar c) '' interior (Work.EL.K c) := Set.image_mono ih
        _ ⊆ interior (Work.EL.K c) := hstep

/-! ### A critical point of `F c = (T_c)^[10]` reaches `0` within `9` steps -/

/-- **A critical point of `F c = (T_c)^[10]` reaches the critical point `0` of `T_c` in fewer
than `10` steps.**  The critical points of the iterates of `Tsq c = (T_c)^[2]` are located by
`Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff`: some `j < 5` has `(Tsq c)^[j] w = 0`
or `T_c ((Tsq c)^[j] w) = 0`, i.e. `(T_c)^[2j] w = 0` or `(T_c)^[2j+1] w = 0`. -/
private theorem exists_Tantibar_iterate_eq_zero_aux {c w : ℂ}
    (h : deriv (Work.FSeed.F c) w = 0) :
    ∃ k : ℕ, k < 10 ∧ (Tantibar c)^[k] w = 0 := by
  have h' : deriv ((Work.Landing.Tsq c)^[5]) w = 0 := h
  obtain ⟨j, hj, hcase⟩ :=
    (Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff c (m := 5)).mp h'
  have hj5 : j < 5 := Finset.mem_range.mp hj
  have h2 : (Work.Landing.Tsq c)^[j] = (Tantibar c)^[2 * j] := by
    rw [Work.FatouParabolic.Critical.tsq_eq_Tantibar_iterate_two]
    rw [← Function.iterate_mul]
  rcases hcase with hcase | hcase
  · refine ⟨2 * j, by omega, ?_⟩
    rw [← h2]
    exact hcase
  · refine ⟨2 * j + 1, by omega, ?_⟩
    rw [Function.iterate_succ_apply']
    rw [← h2]
    exact hcase

/-! ## Clause (i) -/

theorem fatouCrit_clause_i (S : Work.SeedExist.RootSeedData) (D : Work.SeedFatou.CritImmData S) :
    ∃ i : ℕ, i < 5 ∧ ∃ x ∈ (Work.SeedExist.flowerOf S).Pg,
      (LeanEval.ComplexAnalysis.Tantibar S.c)^[i] x ∈
        connectedComponentIn (interior (Work.EL.K S.c)) 0 := by
  obtain ⟨k, _hk10, hkw⟩ := exists_Tantibar_iterate_eq_zero_aux D.deriv_w_eq_zero
  -- `Ω` lies in the interior of the filled Julia set
  have hΩK : D.Ω ⊆ interior (Work.EL.K S.c) :=
    fun z hz => interior_mono (basin_subset_K_aux S.c S.z₁) (D.Ω_subset hz)
  -- so does `(T_c)^[k] '' Ω`, and the latter is preconnected
  have hAK : (Tantibar S.c)^[k] '' D.Ω ⊆ interior (Work.EL.K S.c) :=
    subset_trans (Set.image_mono hΩK) (image_interior_K_aux S.c k)
  have hApre : IsPreconnected ((Tantibar S.c)^[k] '' D.Ω) :=
    D.isPreconnected_Ω.image ((Tantibar S.c)^[k])
      ((continuous_tantibar S.c).iterate k).continuousOn
  have h0A : (0 : ℂ) ∈ (Tantibar S.c)^[k] '' D.Ω := by
    rw [← hkw]
    exact ⟨D.w, D.w_mem, rfl⟩
  have hAc : (Tantibar S.c)^[k] '' D.Ω ⊆
      connectedComponentIn (interior (Work.EL.K S.c)) 0 :=
    hApre.subset_connectedComponentIn h0A hAK
  -- take a point of the half-petal
  obtain ⟨x₀, hx₀⟩ := (Work.SeedExist.flowerOf S).Pg_nonempty
  have hxK : (Tantibar S.c)^[k] x₀ ∈ connectedComponentIn (interior (Work.EL.K S.c)) 0 :=
    hAc ⟨x₀, D.Pg_subset hx₀, rfl⟩
  -- `Pg` is invariant under `g = (T_c)^[5]`
  have hgiter : ∀ a : ℕ, ((Tantibar S.c)^[5])^[a] x₀ ∈ (Work.SeedExist.flowerOf S).Pg := by
    intro a
    induction a with
    | zero => simpa using hx₀
    | succ a ih =>
        simpa only [Function.iterate_succ_apply'] using
          (Work.SeedExist.flowerOf S).mapsTo_g_Pg ih
  have hy : (Tantibar S.c)^[5 * (k / 5)] x₀ ∈ (Work.SeedExist.flowerOf S).Pg := by
    rw [Function.iterate_mul]
    exact hgiter (k / 5)
  -- reduce the exponent `k` modulo `5`
  have hsplit : (Tantibar S.c)^[k] x₀ =
      (Tantibar S.c)^[k % 5] ((Tantibar S.c)^[5 * (k / 5)] x₀) := by
    conv_lhs => rw [← Nat.mod_add_div k 5]
    rw [Function.iterate_add_apply]
  refine ⟨k % 5, Nat.mod_lt k (by norm_num),
    (Tantibar S.c)^[5 * (k / 5)] x₀, hy, ?_⟩
  rw [← hsplit]
  exact hxK

end Work.SeedFatou

end
