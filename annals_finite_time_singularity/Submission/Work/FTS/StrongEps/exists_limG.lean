/-
# `StrongEps/exists_limG.lean` — **E5, new frozen form** (OPEN LEAF)

curric-46 lead install (2026-10-11) of `cbc/fts_strongeps_c1c5_ruling.md` §5 with review fix F5
(`cbc/fts_strongeps_c1c5_ruling_REVIEW.md`): the α-threshold `α₂` is chosen AFTER `C₀, Ce, Cs`
(the wire fixes them before α), BEFORE `K, ρ, Φs, E, g₀`.

Changes against `EpsLimit.exists_limH` (which stays, off the `theorem_1_v2` cone):
* hypothesis `EllLimOK` → `EllLimOK3` (C1: Gap 1 = `E5Aux3.contDiffOn_two_E_of_EllLimOK3`);
* conclusion `ExistsLimH` → `ExistsLimG` (C5: no uniqueness; ONE global family);
* `EpsUniformMem` unchanged (C2/C3/C4 are theorems).

Construction (ruling §5): horizons `T = n`, `ε_k ↓ 0` below every `ε₁(m)`, nested extraction by
`E5Extract_of_mem_seq`, horizons glued by the fixed-ε uniqueness D1
(`IsEpsSolP_eq_of_epsClass`), `g := clampQ F g₀`; each `EpsLimPkg` clause is the per-horizon
assembly at a horizon `N ≥ T` (`c1` is on `Ioo 0 T` for each horizon).

**STATUS (session 20).**  This leaf is the only remaining `sorry` of the area, and everything it
needs is now proved **except one statement-level obstacle**:

* the per-horizon assembly `E5G.EpsLimPkg_of_horizon_full` (with `hlim`, `hcontR`, `hWc`, `hapx`
  all derived) and its complete form `E5G.EpsLimPkg_of_horizon_comp` (`hdbd` derived too, via
  `E5G.hdbd_of_tower` + `E5G.hlim_slots_of_tower`);
* the horizon gluing `E5G.ExistsLimG_of_horizon_pkgs`;
* the curried assembly `E5G.ExistsLimG_assembly`, which takes **both** `StarPkgo2 α Cs Φs` **and**
  `StarPkg6 α Cs6 Φs`, together with `L3Data α₂ Ce C3 Cpow`;
* the last step is that the frozen hypotheses here provide `StarPkgo2` but **not** `StarPkg6`:
  `StarPkg6OfCore`/`StarPkgo2OfCore` both *lift* `VocabO2.StarCore` (whose content is the order-7
  flatness `FlatW 7 (Ycheck α Φs) (Cs*α)`), and no lemma produces a `StarCore` from a `StarPkgo2` —
  the latter carries only order-4 `𝒲^{4,∞}` fields, while the `ℋ⁵`/order-6 algebra of the `hdbd`
  row needs order-5/6 sup bounds.  The proved reduction is `E5G.ExistsLimG_of_core`, which takes
  `StarCore α Cs Φs` instead of `StarPkgo2` (the two `OfCore` lifts then supply both packages).
  So the ruling needed is: either replace this hypothesis by `StarCore` (or by `StarPkg6`), or
  build the missing `StarPkgo2 → StarCore` bridge (which would have to manufacture the order-7
  flatness of `Ycheck α Φs` from order-4 data).
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsLimitDefsG

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **E5 (C1–C5 ruling, F5 order)**.  OPEN LEAF — see the module header: the frozen hypothesis
`StarPkgo2 α Cs Φs` cannot supply the `StarPkg6` the ℋ⁵/ℋ⁶ rows need, and the **proved, axiom-clean
replacement** is `Work.FTS.StrongEps.E5G.exists_limG_core` (same statement with `StarCore α Cs Φs`
and `0 < Cs`).  Changing this hypothesis requires the matching change in
`GlobalStrong2Prime.global_strong2'_proved` (whose `StarPkgo2` argument it passes on) and therefore
in the lead's `FinalV2/Producers.lean:103` and the wire; that is why the swap is left to the lead. -/
theorem exists_limG {C₀ Ce Cs : ℝ} : ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂,
    ∀ {K : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    IsSmoothKernel ρ →
    (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    EllLimOK3 α E → Work.FTS.VocabO2.StarPkgo2 α Cs Φs → MuLamOK α C₀ Φs E →
    EpsUniformMem α ρ Φs E g₀ C₀ K → ExistsLimG α C₀ K Φs E g₀ := by
  sorry

end Work.FTS.StrongEps
