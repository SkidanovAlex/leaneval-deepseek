import Mathlib
import Submission.Work.BMF.halasz_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

open Finset Real Complex

/-- Termwise bound: for a prime `p`, a `1`-bounded `f` and any real `t`,
`Re (f p · p^{-(1+α+it)}) ≤ 1/p` when `α ≥ 0`. -/
lemma re_mul_cpow_le_inv (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) (α t : ℝ) (hα : 0 ≤ α) :
    (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re ≤ (1 : ℝ) / p := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have := hp.two_le; exact_mod_cast (by omega : 1 ≤ p)
  have hnorm : ‖(p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))‖ = (p : ℝ) ^ (-(1 + α)) := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    congr 1
    simp [Complex.neg_re, Complex.add_re, Complex.mul_re]
  have hterm : (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re
      ≤ (p : ℝ) ^ (-(1 + α)) := by
    calc (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))).re
        ≤ ‖f p * (p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))‖ := Complex.re_le_norm _
      _ = ‖f p‖ * ‖(p : ℂ) ^ (-((1 + α : ℝ) + t * Complex.I))‖ := norm_mul _ _
      _ ≤ 1 * (p : ℝ) ^ (-(1 + α)) :=
          mul_le_mul (hb p) (le_of_eq hnorm) (norm_nonneg _) (by norm_num)
      _ = (p : ℝ) ^ (-(1 + α)) := one_mul _
  have hrpow : (p : ℝ) ^ (-(1 + α)) ≤ (1 : ℝ) / p := by
    have hle : (p : ℝ) ^ (-(1 + α)) ≤ (p : ℝ) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    rw [Real.rpow_neg_one] at hle
    rwa [one_div]
  linarith

/-- Trivial bound on `Wsup`: `Wsup f x α T ≤ Zrcp x` for a `1`-bounded `f` and `α ≥ 0`.
Indeed every term of the prime sum is at most `1/p` in absolute value, and `Zrcp x = Σ_{p ≤ x} 1/p`. -/
theorem Wsup_le_Zrcp (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (x T α : ℝ) (hα : 0 ≤ α) :
    Work.BMF.Wsup f x α T ≤ Work.BMF.Zrcp x := by
  have key : ∀ (t : {t : ℝ // |t| ≤ T}),
      (Work.BMF.vF f x ((1 + α : ℝ) + t.1 * Complex.I)).re ≤ Work.BMF.Zrcp x := by
    intro t
    rw [Work.BMF.vF, Work.BMF.Zrcp]
    rw [show (∑ p ∈ (⌊x⌋₊).primesLE, f p * (p : ℂ) ^ (-((1 + α : ℝ) + t.1 * Complex.I))).re
        = ∑ p ∈ (⌊x⌋₊).primesLE,
            (f p * (p : ℂ) ^ (-((1 + α : ℝ) + t.1 * Complex.I))).re
        from map_sum Complex.reAddGroupHom _ _]
    exact Finset.sum_le_sum (fun p hp =>
      re_mul_cpow_le_inv f hb (Nat.prime_of_mem_primesLE hp) α t.1 hα)
  unfold Work.BMF.Wsup
  rw [show (⨆ (t : {t : ℝ // |t| ≤ T}),
      (Work.BMF.vF f x ((1 + α : ℝ) + t.1 * Complex.I)).re)
    = sSup (Set.range (fun t : {t : ℝ // |t| ≤ T} =>
      (Work.BMF.vF f x ((1 + α : ℝ) + t.1 * Complex.I)).re)) from rfl]
  by_cases hT : 0 ≤ T
  · haveI : Nonempty {t : ℝ // |t| ≤ T} := ⟨⟨0, by simp; linarith⟩⟩
    exact ciSup_le key
  · have hE : IsEmpty {t : ℝ // |t| ≤ T} :=
      ⟨fun t => absurd (le_trans (abs_nonneg t.1) t.2) hT⟩
    rw [Set.range_eq_empty_iff.mpr hE, Real.sSup_empty]
    rw [Work.BMF.Zrcp]
    exact Finset.sum_nonneg fun p _ => by positivity

end Work.BMF.mrlas
