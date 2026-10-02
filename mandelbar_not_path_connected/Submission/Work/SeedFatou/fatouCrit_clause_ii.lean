import Mathlib
import Submission.Work.SeedFatou.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.SeedFatou.fatouCrit_clause_ii`

Clause (ii) of Fatou's theorem in the strong form, at the seed: if a critical point `w` of
`F c = (T_c)^[10]` lies in a forward-invariant set `Ω ⊆ interior (basin (F c) z₁)` that contains
the `g`-invariant half-petal `Pg` of the repaired Leau–Fatou flower (`g = (T_c)^[5]`), then some
`F c`-iterate of the critical value `c` lies in a `T_c`-iterate `(T_c)^[j] '' Pg` with `j < 5`.

The proof is iterate bookkeeping, and nothing else.

* `w ∈ Ω ⊆ interior (basin (F c) z₁)`; since `basin (F c) z₁ ⊆ K c`
  (`Work.ELRig.boundedOrbit_of_tendsto_iterate_mul`: a `T_c`-orbit with a convergent
  subsequence is bounded) while `z₁ ∉ interior (K c)`
  (`Work.SeedExist.Sides.notMem_interior_of_flower`), every `F c`-iterate of `w` lies in
  `interior (K c)` and hence misses `z₁`.  So `w` is in the *punctured* basin of `z₁`, and the
  flower's `enters_Pg` field gives `N` with `y := (F c)^[N] w ∈ Pg`.
* A critical point of `F c = (Tsq c)^[5]` reaches `0` within `9` steps
  (`Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff`), say `(T_c)^[k] w = 0`,
  `k < 10`.  Since `T_c 0 = c`, this reads `c = (T_c)^[k+1] w`.
* The `F c`- and the `T_c`-iterates commute (`F c = (T_c)^[10]`), so
  `(F c)^[N] c = (T_c)^[k+1] ((F c)^[N] w) = (T_c)^[k+1] y`.
* Write `k + 1 = j + 5 a` with `j < 5`; then `(T_c)^[k+1] y = (T_c)^[j] ((T_c)^[5]^[a] y)` and
  `(T_c)^[5]^[a] y ∈ Pg` because `Pg` is `g = (T_c)^[5]`-invariant.

The two auxiliary facts `basin_subset_K_aux` and `exists_tantibar_iterate_eq_zero_aux` are the
statements of the sibling lemmas `Work.SeedFatou.basin_subset_K` and
`Work.SeedFatou.exists_tantibar_iterate_eq_zero`, reproduced here privately so that this file
depends only on `Work.SeedFatou.Defs`.
-/

namespace Work.SeedFatou

open Filter Function Set
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar)

set_option linter.unusedVariables false

/-- The basin of the fixed point `z₁` of `F c = (T_c)^[10]` is contained in the filled Julia set
of `T_c`: its `T_c`-orbit has a convergent subsequence (the indices divisible by `10`), hence is
bounded.  This is `Work.SeedFatou.basin_subset_K`. -/
private theorem basin_subset_K_aux (c z₁ : ℂ) :
    Work.FatouParabolic.basin (Work.FSeed.F c) z₁ ⊆ Work.EL.K c := by
  intro z hz
  have hiter : ∀ n : ℕ, (Work.FSeed.F c)^[n] z = (Tantibar c)^[10 * n] z := by
    intro n
    rw [F_eq_tantibar_ten c, Function.iterate_mul]
  have hsub : Tendsto (fun n : ℕ => (Tantibar c)^[10 * n] z) atTop (𝓝 z₁) :=
    Tendsto.congr' (Eventually.of_forall hiter) hz
  exact Work.ELRig.boundedOrbit_of_tendsto_iterate_mul (by norm_num) hsub

/-- A critical point of `F c = (T_c)^[10]` reaches `0` within `9` `T_c`-steps: the critical points
of `Tsq c = (T_c)^[2]` are `0` and the `T_c`-preimages of `0`, and `F c = (Tsq c)^[5]`.  This is
`Work.SeedFatou.exists_tantibar_iterate_eq_zero`. -/
private theorem exists_tantibar_iterate_eq_zero_aux {c w : ℂ}
    (h : deriv (Work.FSeed.F c) w = 0) :
    ∃ k : ℕ, k < 10 ∧ (Tantibar c)^[k] w = 0 := by
  have h5 : deriv ((Work.Landing.Tsq c)^[5]) w = 0 := h
  rcases (Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff c (m := 5)).mp h5 with
    ⟨j, hj, hcase⟩
  rw [Finset.mem_range] at hj
  have hTj : (Tantibar c)^[2 * j] w = (Work.Landing.Tsq c)^[j] w := by
    rw [Function.iterate_mul, Work.FSeed.Tantibar_iterate_two]
  rcases hcase with hz | hz
  · exact ⟨2 * j, by omega, by rw [hTj, hz]⟩
  · refine ⟨2 * j + 1, by omega, ?_⟩
    have hstep : (Tantibar c)^[2 * j + 1] w = Tantibar c ((Tantibar c)^[2 * j] w) := by
      rw [show 2 * j + 1 = 1 + 2 * j from by omega, Function.iterate_add_apply,
        Function.iterate_one]
    rw [hstep, hTj, hz]

theorem fatouCrit_clause_ii (S : Work.SeedExist.RootSeedData) (D : Work.SeedFatou.CritImmData S) :
    ∃ N j : ℕ, j < 5 ∧
      (Work.FSeed.F S.c)^[N] S.c ∈
        (LeanEval.ComplexAnalysis.Tantibar S.c)^[j] '' (Work.SeedExist.flowerOf S).Pg := by
  obtain ⟨k, hk, hk0⟩ := exists_tantibar_iterate_eq_zero_aux D.deriv_w_eq_zero
  have hfix : Work.EL.F S.c S.z₁ = S.z₁ := Work.Final.Tantibar_five_fix S.g_fix
  have hz₁K : S.z₁ ∉ interior (Work.EL.K S.c) :=
    Work.SeedExist.Sides.notMem_interior_of_flower (Work.SeedExist.flowerOf S) hfix
  have hΩK : D.Ω ⊆ interior (Work.EL.K S.c) :=
    fun z hz => interior_mono (basin_subset_K_aux S.c S.z₁) (D.Ω_subset hz)
  -- every `F c`-iterate of the critical point `w` misses the parabolic point `z₁`
  have hno : ∀ n : ℕ, (Work.FSeed.F S.c)^[n] D.w ≠ S.z₁ := by
    intro n h
    have hK : (Work.FSeed.F S.c)^[n] D.w ∈ interior (Work.EL.K S.c) :=
      hΩK (Work.FatouCoord.mapsTo_iterate_of_mapsTo D.mapsTo_Ω n D.w_mem)
    rw [h] at hK
    exact hz₁K hK
  have hconv : Tendsto (fun n : ℕ => (Work.FSeed.F S.c)^[n] D.w) atTop (nhds S.z₁) :=
    interior_subset (D.Ω_subset D.w_mem)
  -- so the orbit of `w` enters the `g`-invariant half-petal
  obtain ⟨N, hN⟩ := (Work.SeedExist.flowerOf S).enters_Pg D.w hconv hno
  -- `c` is the `(k+1)`-st `T_c`-iterate of `w`, because `T_c 0 = c` and `(T_c)^[k] w = 0`
  have hc : (Tantibar S.c)^[k + 1] D.w = S.c := by
    have h1 : (Tantibar S.c)^[k + 1] D.w = Tantibar S.c ((Tantibar S.c)^[k] D.w) :=
      Function.iterate_succ_apply' (Tantibar S.c) k D.w
    rw [h1, hk0, Tantibar_zero]
  -- hence the `F c`-orbit of `c` is a `T_c`-iterate of the `F c`-orbit of `w`
  have hceq : (Work.FSeed.F S.c)^[N] S.c =
      (Tantibar S.c)^[k + 1] ((Work.FSeed.F S.c)^[N] D.w) := by
    calc (Work.FSeed.F S.c)^[N] S.c
        = (Work.FSeed.F S.c)^[N] ((Tantibar S.c)^[k + 1] D.w) := by rw [hc]
      _ = (Tantibar S.c)^[k + 1] ((Work.FSeed.F S.c)^[N] D.w) :=
          F_iterate_comm_T S.c N (k + 1) D.w
  -- split `k + 1 = j + 5 a` with `j < 5`; the `(T_c)^[5]`-iterates of `Pg` stay in `Pg`
  have hstep : ∀ (y : ℂ) (a b : ℕ),
      (Tantibar S.c)^[b + 5 * a] y = (Tantibar S.c)^[b] (((Tantibar S.c)^[5])^[a] y) := by
    intro y a b
    rw [Function.iterate_add_apply, Function.iterate_mul]
  have hkj : k + 1 = (k + 1) % 5 + 5 * ((k + 1) / 5) := by
    have h := Nat.div_add_mod (k + 1) 5
    omega
  have hsplit : (Tantibar S.c)^[k + 1] ((Work.FSeed.F S.c)^[N] D.w) =
      (Tantibar S.c)^[(k + 1) % 5]
        (((Tantibar S.c)^[5])^[(k + 1) / 5] ((Work.FSeed.F S.c)^[N] D.w)) := by
    have h := hstep ((Work.FSeed.F S.c)^[N] D.w) ((k + 1) / 5) ((k + 1) % 5)
    rw [← hkj] at h
    exact h
  exact ⟨N, (k + 1) % 5, Nat.mod_lt _ (by norm_num),
    ((Tantibar S.c)^[5])^[(k + 1) / 5] ((Work.FSeed.F S.c)^[N] D.w),
    Work.FatouCoord.mapsTo_iterate_of_mapsTo (Work.SeedExist.flowerOf S).mapsTo_g_Pg
      ((k + 1) / 5) hN,
    by rw [← hsplit, ← hceq]⟩

end Work.SeedFatou
