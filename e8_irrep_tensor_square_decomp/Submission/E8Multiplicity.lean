import Submission.E8Freudenthal
import Submission.E8Orbit
import Submission.E8Support
import Submission.E8Checks

/-!
# The character of the irreducible quotient `L(ω₁+ω₈) = V ⧸ N`

This file proves the three remaining hypotheses of `Submission.E8Character.eq_of_freudenthal`
(or of `Submission.E8Checks.mfun_unique`) for the actual multiplicity function
`mul N ν = finrank ℂ ↥(Lwt N ν)`:

* `mul_lam`: the `λ`-weight space is one-dimensional (`lamZ` = `ω₁+ω₈`);
* `mul_support`: every non-zero weight is dominated by `λ`;
* `mul_dc`: `W`-invariance of the multiplicities (hypothesis (c)), via the simple reflections.

Hypothesis (d) — the Freudenthal recursion — is `Submission.E8Freudenthal.freudenthal_mul`.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators Matrix

namespace Submission.E8Multiplicity

open Submission.E8WeightSpaces Submission.VermaWeight
open Submission.E8Casimir
open Submission.E8Freudenthal
open Submission.E8Character
open Submission.WeylReflect Submission.WeylWeights

/-! ## (a) The `λ`-weight space is one-dimensional -/

theorem finrank_Lwt_lam (N : Submodule U V) (hvN : v ∉ N) :
    Module.finrank ℂ ↥(Lwt N lamZ) = 1 := by
  have h1 : Lwt N lamZ = Lw N 0 := by
    rw [Lw_eq_Lwt N 0, wtZ_zero]
  have h2 : Lw N 0 = ℂ ∙ vbar N := by
    have hthis : Lw N 0 = (Wm (0 : Fin 8 → ℕ)).map (mkQc N) := rfl
    rw [hthis, show Wm (0 : Fin 8 → ℕ) = ℂ ∙ v from Wm_zero_eq, Submodule.map_span,
      Set.image_singleton]
    rfl
  rw [h1, h2, finrank_span_singleton (vbar_ne_zero N hvN)]

theorem mul_lam (N : Submodule U V) (hvN : v ∉ N) : mul N lamZ = 1 := by
  show ((Module.finrank ℂ ↥(Lwt N lamZ) : ℕ) : ℚ) = 1
  rw [finrank_Lwt_lam N hvN]
  norm_num

/-! ## (b) The support condition -/

theorem lt_finrank_of_ne_bot {N : Submodule U V} {μ : Fin 8 → ℤ} (h : Lwt N μ ≠ ⊥) :
    0 < dmul N μ := by
  haveI : Nontrivial ↥(Lwt N μ) := Submodule.nontrivial_iff_ne_bot.mpr h
  exact Module.finrank_pos

theorem mul_support (N : Submodule U V) {w : Fin 8 → ℤ} (h : mul N w ≠ 0) :
    lamZ - w = 0 ∨ posCon (lamZ - w) := by
  have hb : Lwt N w ≠ ⊥ := by
    intro hbot
    apply h
    show ((Module.finrank ℂ ↥(Lwt N w) : ℕ) : ℚ) = 0
    rw [show Module.finrank ℂ ↥(Lwt N w) = 0 from by
      rw [hbot]
      exact Module.finrank_zero_of_subsingleton]
    norm_num
  obtain ⟨x, hx, hx0⟩ := (Lwt N w).ne_bot_iff.mp hb
  obtain ⟨m, hm⟩ := exists_wtZ_of_mem_Lwt N hx hx0
  refine Or.inr ?_
  have h2 : lamZ - w = (A8 *ᵥ (fun a => (m a : ℤ))) := by
    rw [hm, wtZ_eq]; abel
  rw [h2, posCon_iff_exists]
  exact ⟨m, rfl⟩

/-! ## (c) `W`-invariance -/

/-- Iterating a list of simple reflections does not change the multiplicity. -/
theorem finrank_Lwt_foldl (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (L : List (Fin 8)) (ν : Fin 8 → ℤ) :
    Module.finrank ℂ ↥(Lwt N (L.foldl (fun w i => sref i w) ν))
      = Module.finrank ℂ ↥(Lwt N ν) := by
  induction L generalizing ν with
  | nil => rfl
  | cons i L ih =>
      rw [List.foldl_cons, ih, ← Submission.E8WInvariance.finrank_Lwt_sref N hvN hmax i ν]

theorem mul_dc (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (w : Fin 8 → ℤ) :
    mul N (dc w) = mul N w := by
  have hdc : dc w = (dcListAux 130 w).foldl (fun w i => sref i w) w := by
    rw [← Submission.E8Orbit.dcX_eq_dc, Submission.E8Orbit.dcX,
      Submission.E8Orbit.dcl_eq_foldl]
  rw [hdc]
  show ((Module.finrank ℂ ↥(Lwt N ((dcListAux 130 w).foldl (fun w i => sref i w) w)) : ℕ) : ℚ)
      = ((Module.finrank ℂ ↥(Lwt N w) : ℕ) : ℚ)
  rw [finrank_Lwt_foldl N hvN hmax]

/-! ## The character of `L(ω₁+ω₈)` -/

/-- **The multiplicity function of `L = V ⧸ N` is the candidate character `mfun`.** -/
theorem mfun_eq_mul (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) :
    ∀ w : Fin 8 → ℤ, (Submission.E8Numerics.mfun w : ℚ) = mul N w :=
  Submission.E8Checks.mfun_unique (mul N)
    (by rw [show Submission.E8Enum.lam = lamZ from rfl]; exact mul_lam N hvN)
    (fun w h => mul_support N h)
    (fun w => mul_dc N hvN hmax w)
    (fun ν _ _ hcon => by
      have h := freudenthal_mul N ν hcon
      rw [Int.cast_sub] at h
      exact h)

end Submission.E8Multiplicity
