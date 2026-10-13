import Submission.Work.DSMap.Mix2
import Submission.Work.DSDEN.Basic

/-!
# DSDEN — main deliverables: the `DEN` node and the unit lemma of the MIX2 route

Subproject of the direct-summand development (curric-46 lead), LeanEval problem
`direct_summand`, mixed-characteristic area.  Source of the nodes:
`sources/dsmap/direct_summand_mix2.md` §"Task 3" (`DEN`, and the unit lemma), frozen interface:
`Submission/Work/DSMap/Mix2.lean` (read-only).

## Deliverables

* `Work.DSDEN.exists_chart_gens_proved` — **DEN**: for a `DSMap.PerfectoidData p W` and a *finite*
  family `s : ι → W[1/p]` (`W[1/p] = Localization.Away (p : W)`) there is `e : ℕ` and
  `t : ι → W` with
  `algebraMap (t k) = algebraMap (ϖ₀ ^ (p * e)) * s k` for all `k`,
  i.e. `ϖ₀^{p e}` is a common denominator for the family.  The generator at a chosen index may
  then be *normalised* to be exactly `ϖ₀^{p e}` — that is the form in which the MIX2 glue uses
  it (`Function.update t j (Q.ϖ 0 ^ (p * e))`); see `Work.DSDEN.exists_chart_gens_update`.
* `Work.DSDEN.isUnit_varpi_pow_proved` — `ϖ₀ ^ e` is a unit in `W[1/p]` (so in particular the
  common denominator `ϖ₀^{p e}` of `DEN` is invertible, and `t j = ϖ₀^{p e}` satisfies the
  hypotheses of `DSMap.Mix2.area_SEC`).

Both statements are *identical* to the frozen `DSMap.Mix2.exists_chart_gens`,
`DSMap.Mix2.isUnit_varpi_pow` up to universe names and binder names; they are also re-exported
under those frozen names' namespaces as `DSMap.Mix2.exists_chart_gens_proved`,
`DSMap.Mix2.isUnit_varpi_pow_proved`, so that a consumer may write either
`exact exists_chart_gens_proved p W Q s` in place of the `sorry`, or
`exact DSMap.Mix2.exists_chart_gens_proved p W Q s`.

The proof of `DEN` is the two-line corollary of `Work.DSDEN.exists_common_denom_mul_unit`
(`Submission/Work/DSDEN/Basic.lean`) with `x = p` and `v` the unit of `Q.unit`
(`ϖ₀^p = p * v`, hence `ϖ₀^{p e} = (p v)^e`).

The MIX2 glue that consumes both is replayed in `Submission/Work/DSDEN/GlueM6G.lean`
(`Work.DSDEN.area_M6G_proved`, statement verbatim the frozen `DSMap.Mix2.area_M6G`), and the two
call sites are checked in `Submission/Work/DSDEN/Integration.lean`.  See
`Submission/Work/DSDEN/NOTES.md` for the whole area.
-/

set_option linter.style.haveILetI false

universe a b c u v

namespace Work.DSDEN

open DSMap

/-! ## DEN: common denominators `ϖ₀^{p e}` -/

/-- **DEN**, universe-general form: `W` and the index type `ι` may live in *different* universes
(this is the form to use when the index set is, say, `Fin (N+1)` rather than
`ULift (Fin (N+1))`; the frozen statement pins both to one universe). -/
theorem exists_chart_gens_proved_univ {W : Type u} [CommRing W] {ι : Type v} [Finite ι]
    (p : ℕ) [Fact p.Prime] (Q : PerfectoidData p W) (s : ι → Localization.Away (p : W)) :
    ∃ (e : ℕ) (t : ι → W), ∀ k,
      algebraMap W _ (t k) = algebraMap W _ (Q.ϖ 0 ^ (p * e)) * s k := by
  obtain ⟨v, hv⟩ := Q.unit
  obtain ⟨e, t, ht⟩ := exists_common_denom_mul_unit (p : W) v s
  refine ⟨e, t, fun k => ?_⟩
  have hpow : ((p : W) * (v : W)) ^ e = Q.ϖ 0 ^ (p * e) := by rw [← hv, pow_mul]
  rw [ht k, hpow]

/-- **DEN** (frozen name `DSMap.Mix2.exists_chart_gens`): a finite family in `W[1/p]` has a common
denominator of the form `ϖ₀^{p e}`. -/
theorem exists_chart_gens_proved (p : ℕ) [Fact p.Prime] (W : Type a) [CommRing W]
    (Q : PerfectoidData p W) {ι : Type a} [Finite ι] (s : ι → Localization.Away (p : W)) :
    ∃ (e : ℕ) (t : ι → W), ∀ k,
      algebraMap W _ (t k) = algebraMap W _ (Q.ϖ 0 ^ (p * e)) * s k :=
  exists_chart_gens_proved_univ p Q s

/-- (frozen name `DSMap.Mix2.isUnit_varpi_pow`) `ϖ₀ ^ e` is a unit of `W[1/p]`: `ϖ₀^p = p · v`
is the product of `p`, which is inverted in `W[1/p]`, with a unit of `W`. -/
theorem isUnit_varpi_pow_proved (p : ℕ) [Fact p.Prime] {W : Type a} [CommRing W]
    (Q : PerfectoidData p W) (e : ℕ) :
    IsUnit (algebraMap W (Localization.Away (p : W)) (Q.ϖ 0 ^ e)) := by
  obtain ⟨v, hv⟩ := Q.unit
  have h1 : IsUnit (algebraMap W (Localization.Away (p : W)) (Q.ϖ 0) ^ p) := by
    rw [← map_pow, hv, map_mul]
    exact (IsLocalization.Away.algebraMap_isUnit _).mul (v.isUnit.map _)
  rw [map_pow]
  exact ((isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp h1).pow e

/-- `ϖ₀` itself is a unit of `W[1/p]` (the `e = 1` case of `isUnit_varpi_pow_proved`, in the
form in which the chart map `area_SEC` consumes it). -/
theorem isUnit_algebraMap_varpi (p : ℕ) [Fact p.Prime] {W : Type a} [CommRing W]
    (Q : PerfectoidData p W) :
    IsUnit (algebraMap W (Localization.Away (p : W)) (Q.ϖ 0)) := by
  simpa using isUnit_varpi_pow_proved p Q 1

end Work.DSDEN

/-! ## Re-exports under the frozen names' namespace -/

namespace DSMap.Mix2

open DSMap

/-- `DSMap.Mix2.exists_chart_gens` proved (classifies under the name requested by the lead). -/
theorem exists_chart_gens_proved (p : ℕ) [Fact p.Prime] (W : Type a) [CommRing W]
    (Q : PerfectoidData p W) {ι : Type a} [Finite ι] (s : ι → Localization.Away (p : W)) :
    ∃ (e : ℕ) (t : ι → W), ∀ k,
      algebraMap W _ (t k) = algebraMap W _ (Q.ϖ 0 ^ (p * e)) * s k :=
  Work.DSDEN.exists_chart_gens_proved p W Q s

/-- `DSMap.Mix2.isUnit_varpi_pow` proved (classifies under the name requested by the lead). -/
theorem isUnit_varpi_pow_proved (p : ℕ) [Fact p.Prime] {W : Type a} [CommRing W]
    (Q : PerfectoidData p W) (e : ℕ) :
    IsUnit (algebraMap W (Localization.Away (p : W)) (Q.ϖ 0 ^ e)) :=
  Work.DSDEN.isUnit_varpi_pow_proved p Q e

end DSMap.Mix2

/-! ## Type-identity checks against the frozen statements -/

namespace Work.DSDEN

open DSMap

/-- The frozen statement of `DSMap.Mix2.exists_chart_gens`, written out verbatim and proved from
`Work.DSDEN.exists_chart_gens_proved`. -/
example (p : ℕ) [Fact p.Prime] (W : Type a) [CommRing W]
    (Q : PerfectoidData p W) {ι : Type a} [Finite ι] (s : ι → Localization.Away (p : W)) :
    ∃ (e : ℕ) (t : ι → W), ∀ k,
      algebraMap W _ (t k) = algebraMap W _ (Q.ϖ 0 ^ (p * e)) * s k :=
  exists_chart_gens_proved p W Q s

/-- The same statement, proved from the *frozen* `DSMap.Mix2.exists_chart_gens`, showing the two
statements are interderivable. -/
example (p : ℕ) [Fact p.Prime] (W : Type a) [CommRing W]
    (Q : PerfectoidData p W) {ι : Type a} [Finite ι] (s : ι → Localization.Away (p : W)) :
    ∃ (e : ℕ) (t : ι → W), ∀ k,
      algebraMap W _ (t k) = algebraMap W _ (Q.ϖ 0 ^ (p * e)) * s k :=
  DSMap.Mix2.exists_chart_gens p W Q s

/-- The frozen statement of `DSMap.Mix2.isUnit_varpi_pow`, written out verbatim and proved from
`Work.DSDEN.isUnit_varpi_pow_proved`. -/
example (p : ℕ) [Fact p.Prime] {W : Type a} [CommRing W]
    (Q : PerfectoidData p W) (e : ℕ) :
    IsUnit (algebraMap W (Localization.Away (p : W)) (Q.ϖ 0 ^ e)) :=
  isUnit_varpi_pow_proved p Q e

/-- The same statement, proved from the *frozen* `DSMap.Mix2.isUnit_varpi_pow`. -/
example (p : ℕ) [Fact p.Prime] {W : Type a} [CommRing W]
    (Q : PerfectoidData p W) (e : ℕ) :
    IsUnit (algebraMap W (Localization.Away (p : W)) (Q.ϖ 0 ^ e)) :=
  DSMap.Mix2.isUnit_varpi_pow p Q e

end Work.DSDEN
