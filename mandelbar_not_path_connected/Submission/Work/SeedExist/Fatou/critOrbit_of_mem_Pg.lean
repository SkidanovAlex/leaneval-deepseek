/-
# The critical orbit of the seed converges to the parabolic point — and never hits it

`Work.SeedExist.Fatou.critOrbit_of_mem_Pg`.  The hypotheses are only the flower `fl` of the
parabolic point `z₁` of `F c = (T_c)^[10]` (with antiholomorphic square root `g = (T_c)^5`) and
the datum `hPg` that some `F c`-iterate of the critical value `c` lies in the `g`-invariant
half-petal `Pg`.  The conclusion is the contract's clause W9 (the `crit` clause of
`NOTES_LEAD_mandelbar_seed.md`): the whole critical orbit converges to `z₁`, and no point of it
is `z₁` itself.

Three ingredients, all of them *derived* here from the flower:

* `Work.FSeed.F c` is the polynomial `(Tantibar c)^[10]`, hence **continuous**
  (`continuous_FSeed_F`), and the parabolic point of a flower is a **fixed point** of a
  continuous map (`flower_fixPoint`): if `z ∈ Pg` then `F^[n] z → z₁` (the field `tendsto_Pa`
  of the flower), so `F (F^[n] z) = F^[n + 1] z → z₁` as well, and continuity of `F` at `z₁`
  gives `F z₁ = z₁`.  (In the applications `F z₁ = z₁` is `Work.FQC.F_fix`, which needs the
  root-parabolic data `d`; the flower alone carries it because `F c` is an explicit polynomial.)
* the tail of the critical orbit past its entry time `N` stays in `Pg` (`mapsTo_F_Pg` iterated)
  and therefore converges to `z₁` (`tendsto_Pg`), which gives the `Tendsto` of the whole orbit
  by a shift: `fun n => F^[n + N] c = fun n => F^[n] (F^[N] c)`;
* for the non-hitting clause: if `F^[N] c ∈ Pg` and `F^[n] c = z₁`, then for `n ≤ N` we get
  `F^[N] c = F^[N - n] z₁ = z₁ ∈ Pg` (the fixed-point relation `flower_fixPoint`), and for
  `N ≤ n` we have `F^[n] c ∈ Pg` directly; in both cases `z₁ ∈ Pg` contradicts the flower's
  `z₀_not_mem_Pg`.
-/
import Mathlib
import Submission.Work.SeedExist.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function Set
open scoped Topology

namespace Work.SeedExist.Fatou

/-- `Tantibar c` is continuous: it is the antiholomorphic polynomial `z ↦ (conj z)^2 + c`. -/
theorem continuous_tantibar_seed (c : ℂ) : Continuous (LeanEval.ComplexAnalysis.Tantibar c) := by
  rw [show LeanEval.ComplexAnalysis.Tantibar c =
    fun z : ℂ => (starRingEnd ℂ) z ^ 2 + c from rfl]
  continuity

/-- The seed map `F c = (T_c)^[10]` is continuous (it is a polynomial iterate). -/
theorem continuous_FSeed_F (c : ℂ) : Continuous (Work.FSeed.F c) := by
  have h : Work.FSeed.F c = (LeanEval.ComplexAnalysis.Tantibar c)^[10] :=
    Work.EL.F_eq_tantibar c
  rw [h]
  exact (continuous_tantibar_seed c).iterate 10

/-- **The parabolic point of a flower of the seed map is fixed by `F c`.**  The petals of the
flower converge to `z₁` (field `tendsto_Pa`), so continuity of the explicit polynomial `F c` at
`z₁` forces `F c z₁ = z₁`. -/
theorem flower_fixPoint {c : ℂ} {z₁ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.FSeed.F c)
      ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) z₁) :
    (Work.FSeed.F c) z₁ = z₁ := by
  obtain ⟨z, hz⟩ := fl.Pg_nonempty
  have h1 : Tendsto (fun n : ℕ => (Work.FSeed.F c) ((Work.FSeed.F c)^[n] z)) atTop
      (nhds ((Work.FSeed.F c) z₁)) :=
    (continuous_FSeed_F c).continuousAt.tendsto.comp (fl.tendsto_Pg hz)
  have h2 : Tendsto (fun n : ℕ => (Work.FSeed.F c)^[n] ((Work.FSeed.F c) z)) atTop
      (nhds z₁) := fl.tendsto_Pg (fl.mapsTo_F_Pg hz)
  have heq : (fun n : ℕ => (Work.FSeed.F c) ((Work.FSeed.F c)^[n] z))
      = fun n : ℕ => (Work.FSeed.F c)^[n] ((Work.FSeed.F c) z) := by
    funext n
    exact (Function.iterate_succ_apply' (Work.FSeed.F c) n z).symm.trans
      (Function.iterate_succ_apply (Work.FSeed.F c) n z)
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

theorem critOrbit_of_mem_Pg {c : ℂ} {z₁ : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.FSeed.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) z₁)
    (hPg : ∃ N : ℕ, (Work.FSeed.F c)^[N] c ∈ fl.Pg) :
    Filter.Tendsto (fun n : ℕ => (Work.FSeed.F c)^[n] c) Filter.atTop (nhds z₁) ∧
      ∀ n : ℕ, (Work.FSeed.F c)^[n] c ≠ z₁ := by
  obtain ⟨N, hN⟩ := hPg
  have hfix : (Work.FSeed.F c) z₁ = z₁ := flower_fixPoint fl
  -- the tail of the critical orbit (in `Pg`) converges to `z₁`
  have htail : Tendsto (fun n : ℕ => (Work.FSeed.F c)^[n + N] c) atTop (nhds z₁) := by
    simpa only [Function.iterate_add_apply] using (fl.tendsto_Pg hN)
  refine ⟨(Filter.tendsto_add_atTop_iff_nat N).mp htail, fun n => ?_⟩
  by_cases hNn : N ≤ n
  · intro hhit
    have hmem : (Work.FSeed.F c)^[n - N] ((Work.FSeed.F c)^[N] c) ∈ fl.Pg :=
      fl.mapsTo_iterate_F_Pg (n - N) hN
    have heq2 : (Work.FSeed.F c)^[n - N] ((Work.FSeed.F c)^[N] c) = (Work.FSeed.F c)^[n] c := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hNn]
    rw [← heq2] at hhit
    exact fl.z₀_not_mem_Pg (hhit ▸ hmem)
  · intro hhit
    have hlt : n < N := Nat.lt_of_not_le hNn
    have h1 : (Work.FSeed.F c)^[N] c = (Work.FSeed.F c)^[N - n] ((Work.FSeed.F c)^[n] c) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt hlt)]
    have hN1 : (Work.FSeed.F c)^[N] c = z₁ := by
      rw [h1, hhit, Function.iterate_fixed hfix]
    exact fl.z₀_not_mem_Pg (hN1 ▸ hN)

end Work.SeedExist.Fatou
