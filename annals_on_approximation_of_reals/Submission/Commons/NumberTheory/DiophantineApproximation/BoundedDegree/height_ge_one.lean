import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Algebraic.Integral

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

open scoped BigOperators

/-- The naive height of an algebraic number (supremum of the absolute values of the numerators of the coefficients of its minimal polynomial after clearing denominators) is at least 1. -/
theorem height_ge_one (α : ℂ) (hα : IsAlgebraic ℚ α) :
    1 ≤ (((let p := minpoly ℚ α;
          let D := Multiset.lcm (Multiset.map (fun i ↦ (p.coeff i).den) p.support.val);
          Finset.sup p.support (fun i ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ)) := by
  let p : Polynomial ℚ := minpoly ℚ α
  let D : ℕ := Multiset.lcm (Multiset.map (fun i : ℕ ↦ (p.coeff i).den) p.support.val)
  change (1 : ℝ) ≤ ((p.support.sup (fun i : ℕ ↦ (D * p.coeff i).num.natAbs) : ℕ) : ℝ)
  have hp_monic : p.Monic := by
    dsimp [p]
    exact minpoly.monic (isAlgebraic_iff_isIntegral.mp hα)
  have hp_ne_zero : p ≠ 0 := hp_monic.ne_zero
  have hD_ne_zero : D ≠ 0 := by
    dsimp [D]
    exact (Multiset.lcm_ne_zero_iff _).2 (by
      intro hz
      rw [Multiset.mem_map] at hz
      rcases hz with ⟨i, hi, hden⟩
      exact (Rat.den_nz (p.coeff i)) hden)
  obtain ⟨i0, hi0⟩ : p.support.Nonempty := p.support_nonempty.mpr hp_ne_zero
  have hcoeff : p.coeff i0 ≠ 0 := (Polynomial.mem_support_iff).mp hi0
  have hf_ge_one : (1 : ℕ) ≤ (D * p.coeff i0).num.natAbs := by
    have hprod_ne : (D * p.coeff i0 : ℚ) ≠ 0 := by
      exact mul_ne_zero (Nat.cast_ne_zero.mpr hD_ne_zero) hcoeff
    have hnum_ne : (D * p.coeff i0).num ≠ 0 := Rat.num_ne_zero.mpr hprod_ne
    have hpos : 0 < (D * p.coeff i0).num.natAbs := Int.natAbs_pos.mpr hnum_ne
    omega
  have hle : (D * p.coeff i0).num.natAbs ≤ p.support.sup (fun i : ℕ ↦ (D * p.coeff i).num.natAbs) :=
    Finset.le_sup (f := fun i : ℕ ↦ (D * p.coeff i).num.natAbs) hi0
  exact_mod_cast (le_trans hf_ge_one hle)

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree