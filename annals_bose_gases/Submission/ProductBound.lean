import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.OneParticle
import Submission.ProductState
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 2 — boundedness of the box energy above (product trial states).

A normalized one-particle state `φ` in the box of side `L` (built by scaling a fixed
smooth bump of the unit box) gives an `N`-particle product trial state whose Rayleigh
quotient is bounded above by

    N · (kinetic of φ) + N² · ‖φ‖∞² · ‖v‖₁ ,

and with the scaled bump the one-particle kinetic is `O(1/L²)` and `‖φ‖∞²` is
`O(1/L³)`, yielding the a priori upper bound

    boxEnergy N L v ≤ C · (N : ℝ)/L² + C · (N : ℝ)² · ‖v‖₁ / L³

for all `1 ≤ L`, with a universal constant `C > 0`.  (No nonnegativity of `v` is
needed for this *upper* bound.)

The pieces come from two modules:

* `Submission.OneParticle`: a smooth bump `oneParticle L` supported inside
  `cube L`, with `∫ (oneParticle L)² = 1`, pointwise square bound `supC / L³`
  and kinetic bound `kinC / L²` (universal `supC`, `kinC`); see
  `oneParticle_facts`.

* `Submission.ProductState`: for any such `φ` (abstractly: `ContDiff`, support
  in the cube, square bound `sp`, `L²`-norm one) an `N`-particle product trial
  state `Ψ` with Rayleigh quotient
  `boxQuot N L v Ψ ≤ N · ∫|φ·Δφ| + N² · sp · ∫|v|`; see `productState_facts`.

The box energy is the infimum of the Rayleigh quotients, so `boxEnergy ≤
boxQuot` when the quotients are bounded below; when they are not bounded below
the infimum is `0` (the default value of `sInf` of an unbounded-below set in
`ℝ`), which is still below the nonnegative right-hand side.  This is why no
sign assumption on `v` is needed.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Glue: from a bounded Rayleigh quotient to a box-energy bound -/

/-- If one admissible state has Rayleigh quotient at most `b ≥ 0`, then the box
energy (an infimum) is at most `b`: either the quotient family is bounded below
(use the trial state) or its infimum is `0 ≤ b`. -/
lemma boxEnergy_le_of_boxQuot_le {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L)
    {Ψ : CInfty0Box N L} {b : ℝ} (hb0 : 0 ≤ b) (h : boxQuot N L v Ψ ≤ b) :
    boxEnergy N L v ≤ b := by
  by_cases hbdd : BddBelow (Set.range (boxQuot N L v))
  · haveI : Nonempty (CInfty0Box N L) := nonempty_CInfty0Box N hL
    calc
      boxEnergy N L v = ⨅ Φ : CInfty0Box N L, boxQuot N L v Φ := boxEnergy_eq_ciInf_boxQuot N L v
      _ ≤ boxQuot N L v Ψ := ciInf_le hbdd Ψ
      _ ≤ b := h
  · have hzero : boxEnergy N L v = 0 := by
      rw [boxEnergy_eq_ciInf_boxQuot]
      rw [show (⨅ Φ : CInfty0Box N L, boxQuot N L v Φ) = sInf (Set.range (boxQuot N L v)) by rfl]
      rw [csInf_of_not_bddBelow hbdd]
      simp
    rw [hzero]
    exact hb0

/-- The a priori bound `C·N/L² + C·N²·‖v‖₁/L³` is nonnegative for `0 < C`,
`0 < L`. -/
lemma bound_nonneg (C : ℝ) (hC : 0 < C) (N : ℕ) (L : ℝ) (hL : 0 < L) (v : ℝ³ → ℝ) :
    0 ≤ C * (N : ℝ) / L ^ 2 + C * (N : ℝ) ^ 2 * (∫ x, |v x|) / L ^ 3 := by
  have hN : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
  have hv : 0 ≤ ∫ x, |v x| := integral_nonneg (fun x => abs_nonneg (v x))
  have h1 : 0 ≤ C * (N : ℝ) / L ^ 2 := div_nonneg (mul_nonneg hC.le hN) (sq_nonneg L)
  have h2 : 0 ≤ C * (N : ℝ) ^ 2 * (∫ x, |v x|) / L ^ 3 := by
    exact div_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg (N : ℝ))) hv) (pow_nonneg hL.le 3)
  linarith

/-! ## The a priori upper bound on the box energy -/

lemma boxEnergy_upper_bound {v : ℝ³ → ℝ} (hv1 : MemLp v 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) {L : ℝ}, 1 ≤ L →
      boxEnergy N L v ≤ C * (N : ℝ) / L ^ 2 + C * (N : ℝ) ^ 2 * (∫ x, |v x|) / L ^ 3 := by
  let C : ℝ := max supC (max kinC 1)
  refine ⟨C, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ C := le_trans (le_max_right kinC 1) (le_max_right supC (max kinC 1))
    exact lt_of_lt_of_le zero_lt_one h1
  · intro N L hL1
    have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
    rcases oneParticle_facts (L := L) hL1 with ⟨hφc, hφts, hnorm, hsc0, hsq, hkin⟩
    let sp : ℝ := supC / L ^ 3
    have hsp0 : 0 ≤ sp := div_nonneg hsc0 (pow_nonneg hLpos.le 3)
    have hsq' : ∀ x : ℝ³, (oneParticle L x) ^ 2 ≤ sp := by
      intro x
      exact hsq x
    have hK0 : 0 ≤ ∫ x : ℝ³, |oneParticle L x * Δ (oneParticle L) x| :=
      integral_nonneg (fun x => abs_nonneg _)
    have hv0 : 0 ≤ ∫ x : ℝ³, |v x| := integral_nonneg (fun x => abs_nonneg (v x))
    obtain ⟨Ψ, hΨ⟩ := productState_facts (N := N) (L := L) (v := v) hLpos hv1
      (φ := oneParticle L) (sp := sp) hsp0 hφc hφts hsq' hnorm
    let b : ℝ := (N : ℝ) * (∫ x : ℝ³, |oneParticle L x * Δ (oneParticle L) x|) +
        (N : ℝ) ^ 2 * sp * (∫ x : ℝ³, |v x|)
    have hb0 : 0 ≤ b := by
      dsimp [b]
      have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
      exact add_nonneg (mul_nonneg hN0 hK0)
        (mul_nonneg (mul_nonneg (sq_nonneg (N : ℝ)) hsp0) hv0)
    have hE : boxEnergy N L v ≤ b := boxEnergy_le_of_boxQuot_le hLpos hb0 hΨ
    have hgoal : b ≤ C * (N : ℝ) / L ^ 2 + C * (N : ℝ) ^ 2 * (∫ x, |v x|) / L ^ 3 := by
      dsimp [b, sp]
      have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
      have hkinc : kinC ≤ C := le_trans (le_max_left kinC 1) (le_max_right supC (max kinC 1))
      have hkin1 : kinC / L ^ 2 ≤ C / L ^ 2 :=
        div_le_div_of_nonneg_right hkinc (sq_nonneg L)
      have hNkin : (N : ℝ) * (∫ x : ℝ³, |oneParticle L x * Δ (oneParticle L) x|) ≤
          (N : ℝ) * (kinC / L ^ 2) := mul_le_mul_of_nonneg_left hkin hN0
      have hNkin2 : (N : ℝ) * (kinC / L ^ 2) ≤ (N : ℝ) * (C / L ^ 2) :=
        mul_le_mul_of_nonneg_left hkin1 hN0
      have hterm1 : (N : ℝ) * (∫ x : ℝ³, |oneParticle L x * Δ (oneParticle L) x|) ≤ C * (N : ℝ) / L ^ 2 := by
        calc
          (N : ℝ) * (∫ x : ℝ³, |oneParticle L x * Δ (oneParticle L) x|) ≤ (N : ℝ) * (kinC / L ^ 2) := hNkin
          _ ≤ (N : ℝ) * (C / L ^ 2) := hNkin2
          _ = C * (N : ℝ) / L ^ 2 := by
            field_simp [pow_ne_zero 2 (ne_of_gt hLpos)]
      have hsupc : supC ≤ C := le_max_left supC (max kinC 1)
      have hpart : (N : ℝ) ^ 2 * (supC / L ^ 3) * (∫ x, |v x|) ≤
          C * (N : ℝ) ^ 2 * (∫ x, |v x|) / L ^ 3 := by
        have hsc1 : supC / L ^ 3 ≤ C / L ^ 3 := div_le_div_of_nonneg_right hsupc (pow_nonneg hLpos.le 3)
        have hm1 : (N : ℝ) ^ 2 * (supC / L ^ 3) * (∫ x, |v x|) ≤
            (N : ℝ) ^ 2 * (C / L ^ 3) * (∫ x, |v x|) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsc1 (sq_nonneg (N : ℝ))) hv0
        calc
          (N : ℝ) ^ 2 * (supC / L ^ 3) * (∫ x, |v x|) ≤ (N : ℝ) ^ 2 * (C / L ^ 3) * (∫ x, |v x|) := hm1
          _ = C * (N : ℝ) ^ 2 * (∫ x, |v x|) / L ^ 3 := by
            field_simp [pow_ne_zero 3 (ne_of_gt hLpos)]
      linarith
    exact le_trans hE hgoal

/-- The `L¹` norm of the potential (finite for `MemLp v 1`). -/
noncomputable def vL1 (v : ℝ³ → ℝ) : ℝ := ∫ x, |v x|

/-- If the density `N/L³` is bounded above by `ρ₀` then the box energy density is
bounded above uniformly in the box side: for all `L ≥ 1` with `N/L³ ≤ ρ₀`,
`E(N,L)/L³ ≤ C·(ρ₀²·‖v‖₁ + ρ₀)`. -/
lemma boxDensity_upper_bound {v : ℝ³ → ℝ} (hv1 : MemLp v 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ₀ : ℝ) (N : ℕ) {L : ℝ}, 1 ≤ L → 0 ≤ ρ₀ →
      (N : ℝ) / L ^ 3 ≤ ρ₀ →
        boxEnergy N L v / L ^ 3 ≤ C * (ρ₀ ^ 2 * vL1 v + ρ₀) := by
  rcases boxEnergy_upper_bound hv1 with ⟨C₀, hC0pos, hbd⟩
  refine ⟨C₀, hC0pos, ?_⟩
  intro ρ₀ N L hL1 hρ0 hdens
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hE : boxEnergy N L v ≤ C₀ * (N : ℝ) / L ^ 2 + C₀ * (N : ℝ) ^ 2 * vL1 v / L ^ 3 := hbd N hL1
  have hEdiv : boxEnergy N L v / L ^ 3 ≤ (C₀ * (N : ℝ) / L ^ 2 + C₀ * (N : ℝ) ^ 2 * vL1 v / L ^ 3) / L ^ 3 :=
    div_le_div_of_nonneg_right hE (pow_nonneg hLpos.le 3)
  let x : ℝ := (N : ℝ) / L ^ 3
  have hx0 : 0 ≤ x := div_nonneg (by exact_mod_cast Nat.zero_le N) (pow_nonneg hLpos.le 3)
  have hx : x ≤ ρ₀ := hdens
  have hx2 : x ^ 2 ≤ ρ₀ ^ 2 := pow_le_pow_left₀ hx0 hx 2
  have hv0 : 0 ≤ vL1 v := by
    unfold vL1
    exact integral_nonneg (fun x => abs_nonneg (v x))
  have hC0ge : 0 ≤ C₀ := hC0pos.le
  have htermA : C₀ * (N : ℝ) / L ^ 5 ≤ C₀ * ρ₀ := by
    have hNL : (N : ℝ) / L ^ 5 = x / L ^ 2 := by
      dsimp [x]
      field_simp [pow_ne_zero 3 (ne_of_gt hLpos), pow_ne_zero 5 (ne_of_gt hLpos),
        pow_ne_zero 2 (ne_of_gt hLpos)]
    have hL2ge1 : 1 ≤ L ^ 2 := by nlinarith [hL1]
    have hxL2 : x / L ^ 2 ≤ ρ₀ := by
      have hstep : x / L ^ 2 ≤ x := by
        rw [div_le_iff₀ (pow_pos hLpos 2)]
        calc
          x = x * 1 := by ring
          _ ≤ x * L ^ 2 := mul_le_mul_of_nonneg_left hL2ge1 hx0
      exact le_trans hstep hx
    calc
      C₀ * (N : ℝ) / L ^ 5 = C₀ * ((N : ℝ) / L ^ 5) := by ring
      _ ≤ C₀ * ρ₀ := by
        rw [hNL]
        exact mul_le_mul_of_nonneg_left hxL2 hC0ge
  have htermB : C₀ * (N : ℝ) ^ 2 * vL1 v / L ^ 6 ≤ C₀ * (ρ₀ ^ 2 * vL1 v) := by
    have hNL2 : (N : ℝ) ^ 2 / L ^ 6 = x ^ 2 := by
      dsimp [x]
      field_simp [pow_ne_zero 3 (ne_of_gt hLpos), pow_ne_zero 6 (ne_of_gt hLpos)]
    calc
      C₀ * (N : ℝ) ^ 2 * vL1 v / L ^ 6 = C₀ * (((N : ℝ) ^ 2 / L ^ 6) * vL1 v) := by ring
      _ = C₀ * (x ^ 2 * vL1 v) := by rw [hNL2]
      _ ≤ C₀ * (ρ₀ ^ 2 * vL1 v) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx2 hv0) hC0ge
  calc
    boxEnergy N L v / L ^ 3 ≤ (C₀ * (N : ℝ) / L ^ 2 + C₀ * (N : ℝ) ^ 2 * vL1 v / L ^ 3) / L ^ 3 := hEdiv
    _ = C₀ * (N : ℝ) / L ^ 5 + C₀ * (N : ℝ) ^ 2 * vL1 v / L ^ 6 := by
      field_simp [pow_ne_zero 3 (ne_of_gt hLpos)]
    _ ≤ C₀ * ρ₀ + C₀ * (ρ₀ ^ 2 * vL1 v) := add_le_add htermA htermB
    _ = C₀ * (ρ₀ ^ 2 * vL1 v + ρ₀) := by ring

end BoseGases

end Submission
