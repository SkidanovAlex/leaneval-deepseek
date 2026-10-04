import Mathlib
import Submission.Work.Diff.MP.Basic
import Submission.Work.Diff.MP.frobDot_nonpos_of_frobDist_min

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.MP

open Submission.Diff.Alg
open Work.Diff.MP

/-!
# Nearest point and supporting hyperplane for a closed convex set of curvature arrays

`Curv4 n = Fin n → Fin n → Fin n → Fin n → ℝ` is finite dimensional, and `frobDot` is the
Euclidean inner product `∑ᵢⱼₖₗ R i j k l * S i j k l`, with `frobNorm R = √(frobDot R R)` and
`frobDist P S = frobNorm (P - S)`.  In this file we prove:

* `exists_frobDist_min`: a closed, Frobenius-bounded, nonempty `K` contains a point nearest to `P`;
* `frob_nearest_supporting`: that nearest point is unique, and when `P ∉ K` the vector
  `u = (P - v)/‖P - v‖` is a unit outward normal of `K` at `v`, i.e.
  `frobDot u (P - v) = frobDist P v` and `frobDot u (S - v) ≤ 0` for every `S ∈ K`.

The uniqueness is the standard Hilbert-space argument: at both nearest points the obtuse-angle
inequality `frobDot (P - x) (S - x) ≤ 0` holds (`frobDot_nonpos_of_frobDist_min`), and testing the
two inequalities at the other point gives `frobDot (w - v) (w - v) ≤ 0`, hence `w = v`.
-/

/-- **Existence of a nearest point.** A closed nonempty subset `K` of `Curv4 n` which is bounded
for the Frobenius norm is compact (it is closed and bounded for the instance norm, by
`norm_le_frobNorm`, and `Curv4 n` is a proper space), so the continuous function
`S ↦ frobDist P S` attains its minimum on it. -/
theorem exists_frobDist_min (n : ℕ) (K : Set (Curv4 n)) (hKc : IsClosed K) (hKne : K.Nonempty)
    (hKbd : ∃ ρ, ∀ S ∈ K, frobNorm S ≤ ρ) (P : Curv4 n) :
    ∃ v ∈ K, ∀ S ∈ K, frobDist P v ≤ frobDist P S := by
  obtain ⟨ρ, hρ⟩ := hKbd
  have hcomp : IsCompact K := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨hKc, ?_⟩
    refine isBounded_iff_forall_norm_le.mpr ⟨max ρ 0, fun x hx => ?_⟩
    exact le_trans (norm_le_frobNorm x) (le_trans (hρ x hx) (le_max_left ρ 0))
  have hcont : Continuous fun S : Curv4 n => frobDist P S := by
    simp only [frobDist]
    exact continuous_frobNorm.comp (continuous_const.sub continuous_id)
  obtain ⟨v, hvK, hvmin⟩ := hcomp.exists_isMinOn hKne hcont.continuousOn
  exact ⟨v, hvK, fun S hS => hvmin hS⟩

/-- **Nearest point and supporting hyperplane.** For a closed convex nonempty Frobenius-bounded
`K` and any `P`, there is a *unique* nearest point `v ∈ K` of `P`, and if `P ∉ K` then
`u = (P - v)/frobDist P v` is a unit vector with `frobDot u (P - v) = frobDist P v` and
`frobDot u (S - v) ≤ 0` for all `S ∈ K`. -/
theorem frob_nearest_supporting (n : ℕ) (K : Set (Curv4 n)) (hKc : IsClosed K) (hKcv : Convex ℝ K)
    (hKne : K.Nonempty) (hKbd : ∃ ρ, ∀ S ∈ K, frobNorm S ≤ ρ) (P : Curv4 n) :
    ∃ v ∈ K, (∀ S ∈ K, frobDist P v ≤ frobDist P S) ∧
      (∀ w ∈ K, (∀ S ∈ K, frobDist P w ≤ frobDist P S) → w = v) ∧
      (P ∉ K → ∃ u, frobNorm u = 1 ∧ frobDot u (P - v) = frobDist P v ∧
        ∀ S ∈ K, frobDot u (S - v) ≤ 0) := by
  obtain ⟨v, hvK, hvmin⟩ := exists_frobDist_min n K hKc hKne hKbd P
  -- the obtuse-angle inequality at the nearest point `v`
  have hchar : ∀ S ∈ K, frobDot (P - v) (S - v) ≤ 0 :=
    frobDot_nonpos_of_frobDist_min n K hKcv P v hvK hvmin
  refine ⟨v, hvK, hvmin, ?_, ?_⟩
  · -- uniqueness of the nearest point
    intro w hwK hwmin
    have hwchar : ∀ S ∈ K, frobDot (P - w) (S - w) ≤ 0 :=
      frobDot_nonpos_of_frobDist_min n K hKcv P w hwK hwmin
    have h1 : frobDot (P - v) (w - v) ≤ 0 := hchar w hwK
    have h2 : 0 ≤ frobDot (P - w) (w - v) := by
      have h := hwchar v hvK
      rw [show v - w = -(w - v) by abel, frobDot_neg_right] at h
      linarith
    have h3 : frobDot (w - v) (w - v) ≤ 0 := by
      have hsub : w - v = (P - v) - (P - w) := by abel
      calc frobDot (w - v) (w - v)
          = frobDot ((P - v) - (P - w)) (w - v) := by rw [hsub]
        _ = frobDot (P - v) (w - v) - frobDot (P - w) (w - v) := frobDot_sub_left _ _ _
        _ ≤ 0 := by linarith
    have h4 : frobDot (w - v) (w - v) = 0 := le_antisymm h3 (frobDot_self_nonneg _)
    exact sub_eq_zero.mp ((frobDot_self_eq_zero_iff _).mp h4)
  · -- the outward normal `u = (P - v)/frobDist P v`
    intro hPK
    have hPv : P ≠ v := fun h => hPK (h ▸ hvK)
    have hPv' : P - v ≠ 0 := sub_ne_zero.mpr hPv
    have hd : 0 < frobDist P v := by
      rw [frobDist]
      refine lt_of_le_of_ne (frobNorm_nonneg _) ?_
      intro h
      exact hPv' ((frobNorm_eq_zero_iff _).mp h.symm)
    refine ⟨(frobDist P v)⁻¹ • (P - v), ?_, ?_, ?_⟩
    · rw [frobNorm_smul, abs_of_pos (inv_pos.mpr hd)]
      exact inv_mul_cancel₀ (ne_of_gt hd)
    · rw [frobDot_smul_left, ← frobNorm_sq (P - v)]
      have key : (frobNorm (P - v))⁻¹ * (frobNorm (P - v) * frobNorm (P - v))
          = frobNorm (P - v) := inv_mul_cancel_left₀ (ne_of_gt hd) _
      simpa only [frobDist, pow_two] using key
    · intro S hS
      rw [frobDot_smul_left]
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (inv_pos.mpr hd)) (hchar S hS)

end Work.Diff.MP
