/-
# The critical domain `{G_c > G_c 0}`: elementary API

The parameter-plane Böttcher coordinate of `T_c(z) = z̄² + c` lives on the **critical domain**

`critDomain c = {z | paramPotential c < greenFun c z} = {z | G_c 0 < G_c z}`,

the largest domain on which `T_c` is (anti-)conformal.  This file collects the elementary
facts about it, which the whole `ParamRaysCrit` area is built on:

* `critDomain c` is `T_c`-invariant (`Tantibar_mem_critDomain`, `orbit_mem_critDomain`) and is
  contained in the escaping set (`critDomain_subset_escapingSet`);
* off the mandelbar it contains the critical value `c` (`self_mem_critDomain`), and on the
  mandelbar it *is* the escaping set (`critDomain_eq_escapingSet`);
* the two Böttcher predicates are related by `IsDynBottcher.isCritBottcher` (always) and
  `isCritBottcher_iff_isDynBottcher` (for `c ∈ M*`).

## Main results

* `Work.ParamRays.mem_critDomain`, `Work.ParamRays.paramPotential_nonneg`.
* `Work.ParamRays.greenFun_eq_zero_iff_boundedOrbit`, `Work.ParamRays.greenFun_pos_iff_escaping`.
* `Work.ParamRays.paramPotential_eq_zero_iff`, `Work.ParamRays.paramPotential_pos` : the
  parameter potential vanishes exactly on the mandelbar and is positive off it.
* `Work.ParamRays.critDomain_subset_escapingSet`, `Work.ParamRays.Tantibar_mem_critDomain`,
  `Work.ParamRays.orbit_mem_critDomain`, `Work.ParamRays.self_mem_critDomain`,
  `Work.ParamRays.critDomain_eq_escapingSet`.
* `Work.ParamRays.IsDynBottcher.isCritBottcher`,
  `Work.ParamRays.isCritBottcher_iff_isDynBottcher` (and `isCritBottcher_zero_id` : the
  predicate is not vacuous).
-/
import Submission.Work.ParamRays.Bottcher
import Submission.Work.ParamRays.MbDefs
import Submission.Work.ParamRays.greenFun_orbit
import Submission.Work.ParamRays.greenFun_eq_zero_of_bounded
import Submission.Work.ParamRays.greenFun_pos_of_lt
import Submission.Work.ParamRays.isDynBottcher_unique

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology ComplexConjugate

namespace Work.ParamRays

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Elementary rewritings -/

theorem mem_critDomain {c z : ℂ} : z ∈ critDomain c ↔ paramPotential c < greenFun c z :=
  Iff.rfl

theorem paramPotential_nonneg (c : ℂ) : 0 ≤ paramPotential c := greenFun_nonneg c 0

theorem orbit_one (c z : ℂ) : orbit c z 1 = Tantibar c z := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, orbit_succ, orbit_zero]

theorem Tantibar_zero (c : ℂ) : Tantibar c 0 = c := by
  simp [Tantibar]

/-- The first iterate of the critical point is the critical value. -/
theorem critOrbit_one' (c : ℂ) : orbit c 0 1 = c := by
  rw [orbit_one, Tantibar_zero]

/-! ## The Green function, escaping and bounded orbits -/

/-- A point escapes iff its orbit is not bounded.  (This is the converse direction of
`Work.ParamRays.escaping_iff_not_bounded`, phrased separately so that this file does not have to
import `ParamRays/Interface.lean`, where the latter lives and which imports this module.) -/

theorem escaping_of_not_bounded {c z : ℂ} (h : ¬ BoundedOrbit c z) : Escaping c z := by
  rw [BoundedOrbit] at h
  push_neg at h
  obtain ⟨N, hN⟩ := h (max 2 ‖c‖)
  exact Escaping.of_shift (escaping_of_lt_norm c _ hN)

/-- The Green function vanishes exactly on the filled Julia set.  (The two implications are
`greenFun_eq_zero_of_bounded` and the escape criterion; this is the same statement as
`Work.ParamRays.greenFun_eq_zero_iff` of `ParamRays/Interface.lean`, which imports this
module.) -/
theorem greenFun_eq_zero_iff_boundedOrbit (c z : ℂ) : greenFun c z = 0 ↔ BoundedOrbit c z := by
  refine ⟨fun h => ?_, greenFun_eq_zero_of_bounded c z⟩
  by_contra hb
  rw [BoundedOrbit] at hb
  push_neg at hb
  obtain ⟨N, hN⟩ := hb (max 2 ‖c‖)
  have hpos := greenFun_pos_of_lt c (orbit c z N) hN
  rw [greenFun_orbit, h, mul_zero] at hpos
  exact lt_irrefl 0 hpos

/-- The Green function is positive exactly on the escaping set. -/
theorem greenFun_pos_iff_escaping (c z : ℂ) : 0 < greenFun c z ↔ Escaping c z := by
  constructor
  · intro h
    by_contra hz
    have hb : BoundedOrbit c z := by
      by_contra hb
      exact hz (escaping_of_not_bounded hb)
    have h0 := (greenFun_eq_zero_iff_boundedOrbit c z).mpr hb
    linarith
  · intro hz
    have hb : ¬ BoundedOrbit c z := fun hb => by
      obtain ⟨M, hM⟩ := hb
      obtain ⟨a, ha⟩ :=
        Filter.eventually_atTop.mp (Escaping.eventually_gt hz (M + 1))
      linarith [ha a le_rfl, hM a]
    have h0 := (greenFun_eq_zero_iff_boundedOrbit c z).mp
    refine lt_of_le_of_ne (greenFun_nonneg c z) (Ne.symm fun hzero => hb ?_)
    exact (greenFun_eq_zero_iff_boundedOrbit c z).mp hzero

/-- The parameter potential vanishes exactly on the mandelbar. -/
theorem paramPotential_eq_zero_iff (c : ℂ) : paramPotential c = 0 ↔ c ∈ Mb := by
  rw [paramPotential, greenFun_eq_zero_iff_boundedOrbit, mem_mandelbar_iff_bounded]

/-- Outside the mandelbar the parameter potential is positive.  (This is
`Work.ParamRays.paramPotential_pos`, kept here so that the `ParamRaysCrit` area can use it
without importing `ParamRays/Interface.lean`, which imports this module.) -/
theorem paramPotential_pos {c : ℂ} (hc : c ∉ Mb) : 0 < paramPotential c := by
  have hnb : ¬ BoundedOrbit c 0 := hc
  rw [BoundedOrbit] at hnb
  push_neg at hnb
  obtain ⟨N, hN⟩ := hnb (max 2 ‖c‖)
  have hpos : 0 < greenFun c (orbit c 0 N) := greenFun_pos_of_lt c _ hN
  rw [greenFun_orbit] at hpos
  have h2 : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have : 0 < greenFun c 0 := by nlinarith
  simpa [paramPotential] using this

/-! ## The critical domain -/

/-- The critical domain is contained in the escaping set: `G_c z > G_c 0 ≥ 0` implies
`G_c z > 0`. -/
theorem critDomain_subset_escapingSet (c : ℂ) : critDomain c ⊆ escapingSet c := by
  intro z hz
  rw [mem_critDomain] at hz
  rw [mem_escapingSet]
  exact (greenFun_pos_iff_escaping c z).mp
    (lt_of_le_of_lt (paramPotential_nonneg c) hz)

/-- The critical domain is `T_c`-invariant: `G_c (T_c z) = 2 G_c z ≥ G_c z`. -/
theorem Tantibar_mem_critDomain {c z : ℂ} (hz : z ∈ critDomain c) :
    Tantibar c z ∈ critDomain c := by
  rw [mem_critDomain] at hz ⊢
  have hT : greenFun c (Tantibar c z) = 2 * greenFun c z := by
    have h := greenFun_orbit c z 1
    rw [orbit_one] at h
    simpa using h
  rw [hT]
  nlinarith [paramPotential_nonneg c, hz]

/-- Along an orbit the critical domain is invariant. -/
theorem orbit_mem_critDomain {c z : ℂ} (hz : z ∈ critDomain c) (n : ℕ) :
    orbit c z n ∈ critDomain c := by
  induction n with
  | zero => simpa using hz
  | succ n ih => rw [orbit_succ]; exact Tantibar_mem_critDomain ih

/-- Off the mandelbar the critical value `c` lies in the critical domain: `G_c c = 2 G_c 0`
and `G_c 0 > 0`. -/
theorem self_mem_critDomain {c : ℂ} (hc : c ∉ Mb) : c ∈ critDomain c := by
  rw [mem_critDomain]
  have hG : greenFun c c = 2 * paramPotential c := by
    have h := greenFun_orbit c 0 1
    rw [critOrbit_one'] at h
    simpa [paramPotential] using h
  rw [hG]
  linarith [paramPotential_pos hc]

/-- On the mandelbar the critical domain is the whole escaping set: there `G_c 0 = 0`. -/
theorem critDomain_eq_escapingSet {c : ℂ} (hc : c ∈ Mb) : critDomain c = escapingSet c := by
  have h0 : paramPotential c = 0 := greenFun_eq_zero_of_bounded c 0 hc
  ext z
  rw [mem_critDomain, mem_escapingSet, h0]
  exact greenFun_pos_iff_escaping c z

/-! ## The two Böttcher predicates -/

/-- Every dynamical Böttcher coordinate is a critical Böttcher coordinate. -/
theorem IsDynBottcher.isCritBottcher {c : ℂ} {φ : ℂ → ℂ} (h : IsDynBottcher c φ) :
    IsCritBottcher c φ :=
  ⟨h.1.mono (critDomain_subset_escapingSet c),
    fun z hz => h.2.1 z (critDomain_subset_escapingSet c hz), h.2.2⟩

/-- `IsCritBottcher` is not vacuous: for `c = 0` the identity is a critical Böttcher coordinate
(the critical domain of `T_0` is its escaping set, where `isDynBottcher_zero_id` applies). -/
theorem isCritBottcher_zero_id : IsCritBottcher 0 id :=
  isDynBottcher_zero_id.isCritBottcher

/-- On the mandelbar the two Böttcher predicates coincide (the critical domain is the
escaping set). -/
theorem isCritBottcher_iff_isDynBottcher {c : ℂ} (hc : c ∈ Mb) {φ : ℂ → ℂ} :
    IsCritBottcher c φ ↔ IsDynBottcher c φ := by
  have hEq := critDomain_eq_escapingSet hc
  refine ⟨fun h => ⟨hEq.symm ▸ h.1, fun z hz => h.2.1 z (hEq.symm ▸ hz), h.2.2⟩,
    IsDynBottcher.isCritBottcher⟩

end Work.ParamRays
