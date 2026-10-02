/-
# The parameter ray interface: positivity, levels and rays

This file derives the working interface of the parameter-ray area from the definitions of
`MbDefs.lean` and the Böttcher-coordinate lemmas proved in `Bottcher.lean` and its companion
modules: the critical value escapes, `‖Φ c‖ = exp (2 * paramPotential c)`, the level sets of the
potential, and the fact that the potential vanishes exactly on the mandelbar.

## Main results

* `Work.ParamRays.Escaping.of_orbit`, `Work.ParamRays.escapes_criticalValue`.
* `Work.ParamRays.norm_Phi_eq_exp` : `‖Φ c‖ = exp (2 * paramPotential c)`.
* `Work.ParamRays.one_lt_norm_Phi` : `1 < ‖Φ c‖` outside the mandelbar.
* `Work.ParamRays.potential_eq_zero_iff` : `potential c = 0 ↔ c ∈ Mb`.
-/
import Submission.Work.ParamRays.MbDefs
import Submission.Work.ParamRaysCrit.CritDomain
import Submission.Work.ParamRaysCrit.CritBottcher.IsCritBottcher_modulus
import Submission.Work.ParamRays.IsDynBottcher_modulus
import Submission.Work.ParamRays.greenFun_orbit
import Submission.Work.ParamRays.greenFun_pos_of_lt
import Submission.Work.ParamRays.greenFun_eq_zero_of_bounded

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology ComplexConjugate

namespace Work.ParamRays

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## The critical value escapes -/

/-- If a tail of the orbit of `w` escapes, then the orbit of `w` escapes. -/
theorem Escaping.of_orbit {c w : ℂ} (n : ℕ) (h : Escaping c (orbit c w n)) : Escaping c w := by
  simp only [Escaping] at h ⊢
  rw [← tendsto_add_atTop_iff_nat n]
  have h' : (fun a : ℕ => ‖orbit c w (a + n)‖) = fun a : ℕ => ‖orbit c (orbit c w n) a‖ := by
    funext a
    rw [Nat.add_comm a n]
    exact congrArg Norm.norm (orbit_add c w n a)
  rw [h']
  exact h

/-- Outside the mandelbar the critical orbit is unbounded. -/
theorem not_bounded_criticalOrbit {c : ℂ} (hc : c ∉ Mb) : ¬ BoundedOrbit c 0 := hc

/-- `orbit c 0 1 = c`: the critical value is the first point of the critical orbit. -/
theorem orbit_zero_one (c : ℂ) : orbit c 0 1 = c := by
  simp [orbit_succ, Tantibar]

/-- Outside the mandelbar the critical value escapes. -/
theorem escapes_criticalValue {c : ℂ} (hc : c ∉ Mb) : Escaping c c := by
  have hnb : ¬ BoundedOrbit c 0 := hc
  rw [BoundedOrbit] at hnb
  push_neg at hnb
  obtain ⟨N, hN⟩ := hnb (max 2 ‖c‖)
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h
    · exfalso
      rw [h0] at hN
      simp only [critOrbit, orbit, Function.iterate_zero, id_eq, norm_zero,
        max_lt_iff] at hN
      linarith [hN.1]
    · exact h
  have hesc : Escaping c (critOrbit c N) := escaping_of_lt_norm c _ hN
  obtain ⟨m, hm⟩ : ∃ m : ℕ, N = m + 1 := ⟨N - 1, by omega⟩
  have hcrit : critOrbit c N = orbit c c m := by
    rw [hm, critOrbit]
    rw [show m + 1 = 1 + m from Nat.add_comm m 1, orbit_add, orbit_zero_one]
  rw [hcrit] at hesc
  exact Escaping.of_orbit m hesc

/-! ## Escaping versus bounded orbits -/

/-- A point escapes if and only if its orbit is not bounded. -/
theorem escaping_iff_not_bounded (c z : ℂ) : Escaping c z ↔ ¬ BoundedOrbit c z := by
  constructor
  · intro h hb
    obtain ⟨M, hM⟩ := hb
    obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp (Escaping.eventually_gt h (M + 1))
    have h1 := ha a le_rfl
    have h2 := hM a
    linarith
  · intro h
    rw [BoundedOrbit] at h
    push_neg at h
    obtain ⟨N, hN⟩ := h (max 2 ‖c‖)
    exact Escaping.of_orbit N (escaping_of_lt_norm c _ hN)

/-- The mandelbar is the complement of the escaping set of the critical point. -/
theorem mem_mandelbar_iff_not_escaping (c : ℂ) : c ∈ Mb ↔ ¬ Escaping c 0 := by
  rw [mem_mandelbar_iff_bounded, escaping_iff_not_bounded, not_not]

/-- The Green function vanishes exactly on the filled Julia set. -/
theorem greenFun_eq_zero_iff (c z : ℂ) : greenFun c z = 0 ↔ BoundedOrbit c z := by
  refine ⟨fun h => ?_, greenFun_eq_zero_of_bounded c z⟩
  by_contra hb
  rw [BoundedOrbit] at hb
  push_neg at hb
  obtain ⟨N, hN⟩ := hb (max 2 ‖c‖)
  have hpos : 0 < greenFun c (orbit c z N) := greenFun_pos_of_lt c _ hN
  rw [greenFun_orbit] at hpos
  have h2 : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have : 0 < greenFun c z := by nlinarith
  linarith

/-! ## The modulus of the parameter Böttcher map -/

/-- The modulus of the parameter Böttcher map is the exponential of `2` times the potential of
the critical point.

The ingredient is `IsCritBottcher_modulus` — the modulus of a **critical** Böttcher coordinate at
the critical value — applied through `self_mem_critDomain` (for `c ∉ Mb` the critical value lies
in the critical domain).  The corresponding statement for `IsDynBottcher` would be false here,
because `IsDynBottcher c φ` is unsatisfiable off the mandelbar. -/
theorem norm_Phi_eq_exp (hB : BottcherExists) {c : ℂ} (hc : c ∉ Mb) :
    ‖Phi c‖ = Real.exp (2 * paramPotential c) := by
  have hφ : ∃ φ : ℂ → ℂ, IsCritBottcher c φ := hB c hc
  have hmod := Work.ParamRaysCrit.CritBottcher.IsCritBottcher_modulus
    (Classical.choose_spec hφ) (self_mem_critDomain hc)
  rw [Phi_eq_choose hc hφ, hmod]
  have hshift : greenFun c c = 2 * paramPotential c := by
    have h2 := greenFun_orbit c 0 1
    rw [orbit_zero_one] at h2
    simpa [paramPotential] using h2
  rw [hshift]

/-- Outside the mandelbar the parameter Böttcher map has modulus bigger than `1`. -/
theorem one_lt_norm_Phi (hB : BottcherExists) {c : ℂ} (hc : c ∉ Mb) : 1 < ‖Phi c‖ := by
  rw [norm_Phi_eq_exp hB hc, ← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by linarith [paramPotential_pos hc])

/-! ## The potential -/

/-- The potential vanishes exactly on the mandelbar. -/
theorem potential_eq_zero_iff (hB : BottcherExists) (c : ℂ) : potential c = 0 ↔ c ∈ Mb := by
  constructor
  · intro h
    by_contra hc
    rw [potential, dif_neg hc] at h
    have h1 : 1 < ‖Phi c‖ := one_lt_norm_Phi hB hc
    have h2 : 0 < Real.log ‖Phi c‖ := Real.log_pos h1
    linarith
  · intro hc
    exact potential_eq_zero_of_mem hc

/-- The equipotential of level `R` is the level set of the potential. -/
theorem mem_equipotential_iff_potential (hB : BottcherExists) {R : ℝ} {c : ℂ} :
    c ∈ equipotential R ↔ c ∉ Mb ∧ Real.exp (potential c) = R := by
  rw [mem_equipotential]
  have hpos : ∀ {c : ℂ}, c ∉ Mb → 0 < ‖Phi c‖ := fun hc =>
    lt_trans zero_lt_one (one_lt_norm_Phi hB hc)
  constructor
  · rintro ⟨hc, hR⟩
    exact ⟨hc, by rw [potential, dif_neg hc, Real.exp_log (hpos hc), hR]⟩
  · rintro ⟨hc, hR⟩
    refine ⟨hc, ?_⟩
    rw [potential, dif_neg hc] at hR
    rw [← hR, Real.exp_log (hpos hc)]

/-- The potential is positive outside the mandelbar. -/
theorem potential_pos (hB : BottcherExists) {c : ℂ} (hc : c ∉ Mb) : 0 < potential c := by
  rw [potential, dif_neg hc]
  exact Real.log_pos (one_lt_norm_Phi hB hc)

end Work.ParamRays
