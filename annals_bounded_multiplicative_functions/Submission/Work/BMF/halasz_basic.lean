import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.halasz_defs
import Submission.Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Elementary framework lemmas for the complex Halász theorem

Nonnegativity/monotonicity facts about `mHal`, the trivial bound `‖Mf‖ ≤ x`, and the
identification of the infimum appearing in `halasz_complex` with `mHal f x (2*T)`.
-/

namespace Work.BMF

open Finset Real Complex
open BoundedMultiplicativeFunctions
open scoped ComplexConjugate

/-- Each summand of `mHalSum` is nonnegative. -/
lemma mHal_term_nonneg {f : ℕ → ℂ} (hb : ∀ n, ‖f n‖ ≤ 1) {p : ℕ} (hp : p.Prime) (t : ℝ) :
    0 ≤ (1 - (f p * (p : ℂ) ^ (-(Complex.I * t))).re) / p := by
  have hnorm : ‖(p : ℂ) ^ (-(Complex.I * t))‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    simp
  have h1 : (f p * (p : ℂ) ^ (-(Complex.I * t))).re ≤ 1 := by
    calc (f p * (p : ℂ) ^ (-(Complex.I * t))).re
        ≤ ‖f p * (p : ℂ) ^ (-(Complex.I * t))‖ := Complex.re_le_norm _
      _ = ‖f p‖ * ‖(p : ℂ) ^ (-(Complex.I * t))‖ := by rw [Complex.norm_mul]
      _ ≤ 1 * 1 := mul_le_mul (hb p) (le_of_eq hnorm) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  exact div_nonneg (by linarith) (by positivity)

/-- `mHalSum f x t ≥ 0` for `1`-bounded `f`. -/
lemma mHalSum_nonneg {f : ℕ → ℂ} (hb : ∀ n, ‖f n‖ ≤ 1) (x t : ℝ) :
    0 ≤ mHalSum f x t := by
  unfold mHalSum
  exact Finset.sum_nonneg fun p hp => mHal_term_nonneg hb (Nat.prime_of_mem_primesLE hp) t

/-- `mHal f x T ≥ 0`. -/
lemma mHal_nonneg (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (x T : ℝ) (hT : 0 ≤ T) :
    0 ≤ mHal f x T := by
  haveI : Nonempty {t : ℝ // |t| ≤ T} := ⟨⟨0, by simp; linarith⟩⟩
  refine le_ciInf (fun t => ?_)
  exact mHalSum_nonneg hb x t.1

/-- `mHal` is antitone in the window: enlarging the window can only decrease the minimum. -/
lemma mHal_anti (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (x T T' : ℝ) (h : T ≤ T') (hT : 0 ≤ T) :
    mHal f x T' ≤ mHal f x T := by
  have hbdd : BddBelow (Set.range (fun u : {u : ℝ // |u| ≤ T'} => mHalSum f x u.1)) :=
    ⟨0, by rintro _ ⟨u, rfl⟩; exact mHalSum_nonneg hb x u.1⟩
  haveI : Nonempty {t : ℝ // |t| ≤ T} := ⟨⟨0, by simp; linarith⟩⟩
  have hmain : (⨅ (u : {u : ℝ // |u| ≤ T'}), mHalSum f x u.1)
      ≤ (⨅ (t : {t : ℝ // |t| ≤ T}), mHalSum f x t.1) :=
    le_ciInf (fun t => ciInf_le hbdd ⟨t.1, le_trans t.2 h⟩)
  exact hmain

/-- Trivial bound: `mHal f x T ≤ 2 Zrcp x` (test `t = 0`). -/
lemma mHal_le_two_Zrcp (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (x T : ℝ) (hT : 0 ≤ T) :
    mHal f x T ≤ 2 * Zrcp x := by
  have hbdd : BddBelow (Set.range (fun u : {u : ℝ // |u| ≤ T} => mHalSum f x u.1)) :=
    ⟨0, by rintro _ ⟨u, rfl⟩; exact mHalSum_nonneg hb x u.1⟩
  have hle : mHal f x T ≤ mHalSum f x 0 := ciInf_le hbdd ⟨0, by simp; linarith⟩
  have hpt : mHalSum f x 0 ≤ 2 * Zrcp x := by
    have h2 : ∀ p ∈ (⌊x⌋₊).primesLE,
        (1 - (f p * (p : ℂ) ^ (-(Complex.I * (0:ℝ)))).re) / p ≤ (2 : ℝ) / (p : ℝ) := by
      intro p hp
      have hp' : p.Prime := Nat.prime_of_mem_primesLE hp
      have hnorm : ‖(p : ℂ) ^ (-(Complex.I * (0:ℝ)))‖ = 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hp'.pos]; simp
      have h1 : (f p * (p : ℂ) ^ (-(Complex.I * (0:ℝ)))).re ≤ 1 := by
        calc (f p * (p : ℂ) ^ (-(Complex.I * (0:ℝ)))).re
            ≤ ‖f p * (p : ℂ) ^ (-(Complex.I * (0:ℝ)))‖ := Complex.re_le_norm _
          _ = ‖f p‖ * ‖(p : ℂ) ^ (-(Complex.I * (0:ℝ)))‖ := by rw [Complex.norm_mul]
          _ ≤ 1 * 1 := mul_le_mul (hb p) (le_of_eq hnorm) (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      have h1' : -(f p * (p : ℂ) ^ (-(Complex.I * (0:ℝ)))).re ≤ 1 := by
        calc -(f p * (p : ℂ) ^ (-(Complex.I * (0:ℝ)))).re
            ≤ |(f p * (p : ℂ) ^ (-(Complex.I * (0:ℝ)))).re| := neg_le_abs _
          _ ≤ ‖f p * (p : ℂ) ^ (-(Complex.I * (0:ℝ)))‖ := Complex.abs_re_le_norm _
          _ = ‖f p‖ * ‖(p : ℂ) ^ (-(Complex.I * (0:ℝ)))‖ := by rw [Complex.norm_mul]
          _ ≤ 1 * 1 := mul_le_mul (hb p) (le_of_eq hnorm) (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      have hp1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp'.pos
      rw [div_le_div_iff_of_pos_right hp1]
      linarith
    unfold mHalSum
    calc ∑ p ∈ (⌊x⌋₊).primesLE, (1 - (f p * (p : ℂ) ^ (-(Complex.I * (0:ℝ)))).re) / p
        ≤ ∑ p ∈ (⌊x⌋₊).primesLE, (2 : ℝ) / (p : ℝ) := Finset.sum_le_sum h2
      _ = 2 * Zrcp x := by
          rw [Zrcp, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun p _ => by rw [div_eq_mul_inv, one_div])
  exact hle.trans hpt

/-- `Zrcp ≥ 0`. -/
lemma Zrcp_nonneg (y : ℝ) : 0 ≤ Zrcp y := by
  unfold Zrcp
  exact Finset.sum_nonneg fun p _ => by positivity

/-- `Zrcp` is monotone. -/
lemma Zrcp_mono : Monotone Zrcp := by
  intro x y hxy
  unfold Zrcp
  apply Finset.sum_le_sum_of_subset_of_nonneg (Nat.primesLE_mono (Nat.floor_mono hxy))
  intro p _ _; positivity

/-- `‖Mf f x‖ ≤ ⌊x⌋₊` for `1`-bounded `f`. -/
lemma Mf_norm_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (x : ℝ) :
    ‖Mf f x‖ ≤ (⌊x⌋₊ : ℝ) := by
  calc ‖Mf f x‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) := Finset.sum_le_sum fun n _ => hb n
    _ = (⌊x⌋₊ : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc]
        norm_num

/-- `‖Mf f x‖ ≤ x` for `1`-bounded `f` and `x ≥ 0`. -/
lemma Mf_norm_le_x (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (x : ℝ) (hx : 0 ≤ x) :
    ‖Mf f x‖ ≤ x :=
  (Mf_norm_le f hb x).trans (Nat.floor_le hx)

/-- The infimum appearing in the statement of `halasz_complex` equals `mHal f x (2*T)`. -/
lemma target_M_eq_mHal (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (x t : ℝ) :
    BoundedMultiplicativeFunctions.𝔻 f (fun n ↦ (n : ℂ) ^ (Complex.I * t)) x ^ 2 =
      mHalSum f x t := by
  have hconj : ∀ p : ℕ, conj ((p : ℂ) ^ (Complex.I * t)) = (p : ℂ) ^ (-(Complex.I * t)) := by
    intro p
    have h := Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg (Nat.cast_nonneg p) (Complex.I * t)
    have hcast : (((p : ℝ) : ℂ)) = (p : ℂ) := by push_cast; ring
    rw [hcast] at h
    rw [show (starRingEnd ℂ) (Complex.I * t) = -(Complex.I * t) by
        rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring] at h
    exact h
  have hS : (∑ p ∈ (⌊x⌋₊).primesLE,
      (1 - (f p * conj ((p : ℂ) ^ (Complex.I * t))).re) / p) = mHalSum f x t := by
    unfold mHalSum
    exact Finset.sum_congr rfl (fun p _ => by rw [hconj p])
  unfold BoundedMultiplicativeFunctions.𝔻
  rw [hS, show (mHalSum f x t) ^ (1 / 2 : ℝ) = Real.sqrt (mHalSum f x t) from
      (Real.sqrt_eq_rpow _).symm, Real.sq_sqrt (mHalSum_nonneg hb x t)]

end Work.BMF
