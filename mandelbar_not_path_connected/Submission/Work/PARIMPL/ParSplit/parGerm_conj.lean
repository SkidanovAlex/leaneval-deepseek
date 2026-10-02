import Mathlib
import Submission.Work.PARIMPL.ParSplit.ParWall
import Submission.Work.PARIMPL.ParSplit.parLam_eq
import Submission.Work.PARIMPL.ParSplit.parRho_ne_zero
import Submission.Work.PARIMPL.ParSplit.splitPair_exists
import Submission.Work.PARIMPL.ParSplit.divByMonic_X_sq_sub_C
import Submission.Work.PARIMPL.ParSplit.Sqrt
import Submission.Work.PARIMPL.ParSplit.parChartSq
import Submission.Work.PARIMPL.ParSplit.Hp_double_root_count

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 4000
set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology
open Polynomial

noncomputable section

namespace Work.PARIMPL.ParSplit

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-! ## 1. Degree bounds -/

theorem natDegree_X_add_C_le (u : ℂ) : (X + C u : ℂ[X]).natDegree ≤ 1 := by
  calc (X + C u : ℂ[X]).natDegree
      ≤ max (X : ℂ[X]).natDegree (C u).natDegree := natDegree_add_le _ _
    _ ≤ 1 := by rw [natDegree_X, natDegree_C]; simp

theorem natDegree_Phi_le (S : SplitData d) (c : ℂ) : (Phi S c).natDegree ≤ wallN := by
  unfold Phi
  calc ((Qpoly c).comp (X + C (S.m c))).natDegree
      ≤ (Qpoly c).natDegree * (X + C (S.m c)).natDegree := natDegree_comp_le
    _ ≤ 1024 * 1 := Nat.mul_le_mul (natDegree_Qpoly c) (natDegree_X_add_C_le _)
    _ = wallN := by norm_num [wallN]

/-! ## 2. `Rpoly` is the quotient of `Phi` by `X ^ 2 - C (Gc S c)` -/

theorem psi_eq_zero_of_natDegree_lt (S : SplitData d) (c : ℂ) {k : ℕ}
    (hk : (Phi S c).natDegree < k) : psi S c k = 0 := by
  unfold psi phi
  refine Finset.sum_eq_zero (fun j hj => ?_)
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := Phi S c) ?_, mul_zero]
  simp only [Finset.mem_range] at hj
  omega

theorem coeff_Rpoly (S : SplitData d) (c : ℂ) (k : ℕ) : (Rpoly S c).coeff k = psi S c k := by
  have hker : (∑ x ∈ Finset.range (wallN + 1), C (psi S c x) * X ^ x).coeff k
      = ∑ x ∈ Finset.range (wallN + 1), (if k = x then psi S c x else 0) := by
    rw [Polynomial.finsetSum_coeff]
    exact Finset.sum_congr rfl (fun x _ => Polynomial.coeff_C_mul_X_pow (psi S c x) x k)
  unfold Rpoly
  rw [hker, Finset.sum_ite_eq]
  split_ifs with hmem
  · rfl
  · exact (psi_eq_zero_of_natDegree_lt S c (by
      rw [Finset.mem_range] at hmem
      have := natDegree_Phi_le S c; omega)).symm

theorem Rpoly_eq_divByMonic (S : SplitData d) (c : ℂ) :
    Rpoly S c = Phi S c /ₘ (X ^ 2 - C (Gc S c)) := by
  rw [divByMonic_X_sq_sub_C]
  refine Polynomial.ext (fun k => ?_)
  rw [coeff_Rpoly]
  have hker : (∑ x ∈ Finset.range ((Phi S c).natDegree + 1),
        C (∑ j ∈ Finset.range ((Phi S c).natDegree + 1),
          (Gc S c) ^ j * (Phi S c).coeff (x + 2 + 2 * j)) * X ^ x).coeff k
      = ∑ x ∈ Finset.range ((Phi S c).natDegree + 1),
        (if k = x then (∑ j ∈ Finset.range ((Phi S c).natDegree + 1),
          (Gc S c) ^ j * (Phi S c).coeff (x + 2 + 2 * j)) else 0) := by
    rw [Polynomial.finsetSum_coeff]
    exact Finset.sum_congr rfl (fun x _ => Polynomial.coeff_C_mul_X_pow
      (∑ j ∈ Finset.range ((Phi S c).natDegree + 1),
        (Gc S c) ^ j * (Phi S c).coeff (x + 2 + 2 * j)) x k)
  rw [hker, Finset.sum_ite_eq]
  split_ifs with hmem
  · unfold psi phi
    rw [show (∑ j ∈ Finset.range (wallN + 1),
            (Gc S c) ^ j * (Phi S c).coeff (k + 2 * j + 2))
        = ∑ j ∈ Finset.range (wallN + 1),
            (Gc S c) ^ j * (Phi S c).coeff (k + 2 + 2 * j) from
      Finset.sum_congr rfl (fun j _ => by
        rw [show k + 2 * j + 2 = k + 2 + 2 * j from by omega])]
    symm
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      have := natDegree_Phi_le S c; omega
    · intro x hx hxn
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := Phi S c) ?_, mul_zero]
      simp only [Finset.mem_range] at hx hxn
      omega
  · rw [psi_eq_zero_of_natDegree_lt S c (by
      rw [Finset.mem_range] at hmem; omega)]

/-! ## 3. The decomposition `Phi = (X² - Gc) Rpoly + remainder` -/

theorem Phi_decomp (S : SplitData d) (c : ℂ) :
    Phi S c = (X ^ 2 - C (Gc S c)) * Rpoly S c + Phi S c %ₘ (X ^ 2 - C (Gc S c)) := by
  have h := Polynomial.modByMonic_add_div (Phi S c) (X ^ 2 - C (Gc S c))
  rw [Rpoly_eq_divByMonic S c]
  conv_lhs => rw [← h]
  ring

theorem degree_rem_lt_two (S : SplitData d) (c : ℂ) :
    (Phi S c %ₘ (X ^ 2 - C (Gc S c))).degree < (2 : WithBot ℕ) := by
  have hmonic : (X ^ 2 - C (Gc S c) : ℂ[X]).Monic :=
    Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have h := Polynomial.degree_modByMonic_lt (Phi S c) hmonic
  rwa [Polynomial.degree_X_pow_sub_C (by norm_num : (0 : ℕ) < 2) (Gc S c)] at h

theorem rem_eq_linear (S : SplitData d) (c : ℂ) :
    Phi S c %ₘ (X ^ 2 - C (Gc S c))
      = C ((Phi S c %ₘ (X ^ 2 - C (Gc S c))).coeff 0)
        + C ((Phi S c %ₘ (X ^ 2 - C (Gc S c))).coeff 1) * X := by
  set R := Phi S c %ₘ (X ^ 2 - C (Gc S c))
  refine Polynomial.ext (fun n => ?_)
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  · have hzero : R.coeff n = 0 :=
      (Polynomial.degree_lt_iff_coeff_zero R 2).mp (degree_rem_lt_two S c) n hn
    have hr : (C (R.coeff 0) + C (R.coeff 1) * X).coeff n = 0 := by
      have h1 : ¬ (n = 0) := by omega
      have h2 : ¬ (1 = n) := by omega
      simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
        Polynomial.coeff_X, h1, h2, ↓reduceIte, mul_zero, add_zero]
    rw [hzero, hr]

theorem eval_Rpoly (S : SplitData d) (c w : ℂ) : (Rpoly S c).eval w = Rfun S c w := by
  unfold Rpoly Rfun
  rw [Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl (fun k _ => by simp)

theorem eval_Phi (S : SplitData d) (c w : ℂ) :
    (Phi S c).eval w = (Qpoly c).eval (S.m c + w) := by
  have h : (Phi S c).eval w = (Qpoly c).eval ((X + C (S.m c) : ℂ[X]).eval w) := by
    unfold Phi
    rw [Polynomial.eval_comp]
  rw [h, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, add_comm]

theorem rem_eval_add (S : SplitData d) (c w : ℂ) :
    (Qpoly c).eval (S.m c + w)
      = (w ^ 2 - Gc S c) * Rfun S c w
        + (Phi S c %ₘ (X ^ 2 - C (Gc S c))).coeff 0
        + (Phi S c %ₘ (X ^ 2 - C (Gc S c))).coeff 1 * w := by
  have h1 : (Qpoly c).eval (S.m c + w) = (Phi S c).eval w := (eval_Phi S c w).symm
  rw [h1]
  conv_lhs => rw [Phi_decomp S c, rem_eq_linear S c]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, eval_Rpoly]
  ring

/-! ## 4. The two fixed points kill the remainder coefficients -/

theorem Qpoly_eval_fixed_add (S : SplitData d) {c : ℂ} (hc : c ∈ ball c₀ S.ρ) :
    (Qpoly c).eval (S.m c + S.E c / 2) = 0 := by
  rw [Qpoly_eval, S.fixed_add c hc, sub_self]

theorem Qpoly_eval_fixed_sub (S : SplitData d) {c : ℂ} (hc : c ∈ ball c₀ S.ρ) :
    (Qpoly c).eval (S.m c + -(S.E c / 2)) = 0 := by
  rw [show S.m c + -(S.E c / 2) = S.m c - S.E c / 2 from by ring, Qpoly_eval,
    S.fixed_sub c hc, sub_self]

theorem pair_add_sub {x y : ℂ} (h1 : x + y = 0) (h2 : x - y = 0) : x = 0 ∧ y = 0 := by
  have hsum : x + y + (x - y) = 0 := by rw [h1, h2, add_zero]
  have hxx : x + x = 0 := by
    rw [show x + y + (x - y) = x + x from by ring] at hsum
    exact hsum
  have hx : x = 0 := add_self_eq_zero.mp hxx
  refine ⟨hx, ?_⟩
  rw [hx, zero_add] at h1
  exact h1

theorem rem_coeffs (S : SplitData d) {c : ℂ} (hc : c ∈ ball c₀ S.ρ) :
    (Phi S c %ₘ (X ^ 2 - C (Gc S c))).coeff 0 = 0 ∧
    (Phi S c %ₘ (X ^ 2 - C (Gc S c))).coeff 1 * S.E c = 0 := by
  have hGc : Gc S c = (S.E c / 2) ^ 2 := rfl
  have e1 : (Phi S c %ₘ (X ^ 2 - C (Gc S c))).coeff 0
      + (Phi S c %ₘ (X ^ 2 - C (Gc S c))).coeff 1 * (S.E c / 2) = 0 := by
    have h := rem_eval_add S c (S.E c / 2)
    rw [Qpoly_eval_fixed_add S hc] at h
    rw [hGc] at h ⊢
    rw [h]
    ring
  have e2 : (Phi S c %ₘ (X ^ 2 - C (Gc S c))).coeff 0
      - (Phi S c %ₘ (X ^ 2 - C (Gc S c))).coeff 1 * (S.E c / 2) = 0 := by
    have h := rem_eval_add S c (-(S.E c / 2))
    rw [Qpoly_eval_fixed_sub S hc] at h
    rw [hGc] at h ⊢
    rw [h]
    ring
  obtain ⟨hA0, hB0⟩ := pair_add_sub e1 e2
  refine ⟨hA0, ?_⟩
  have hE : (Phi S c %ₘ (X ^ 2 - C (Gc S c))).coeff 1 * S.E c
      = ((Phi S c %ₘ (X ^ 2 - C (Gc S c))).coeff 1 * (S.E c / 2)) * 2 := by ring
  simp [hE, hB0]

theorem coeff_one_Phi (S : SplitData d) (c : ℂ) :
    (Phi S c).coeff 1 = (Qpoly c).derivative.eval (S.m c) := by
  have h : Phi S c = Polynomial.taylor (S.m c) (Qpoly c) := by
    unfold Phi
    rw [Polynomial.taylor_apply]
  rw [h, Polynomial.taylor_coeff_one]

theorem coeff_one_rem (S : SplitData d) (c : ℂ) :
    (Phi S c %ₘ (X ^ 2 - C (Gc S c))).coeff 1
      = (Phi S c).coeff 1 + Gc S c * psi S c 1 := by
  have h := Phi_decomp S c
  have hc : (Phi S c).coeff 1
      = (((X ^ 2 - C (Gc S c)) * Rpoly S c)).coeff 1
        + (Phi S c %ₘ (X ^ 2 - C (Gc S c))).coeff 1 := by
    conv_lhs => rw [h]
    rw [Polynomial.coeff_add]
  have hprod : (((X ^ 2 - C (Gc S c)) * Rpoly S c)).coeff 1 = -(Gc S c * psi S c 1) := by
    rw [sub_mul, Polynomial.coeff_sub]
    have hX : ((X ^ 2 : ℂ[X]) * Rpoly S c).coeff 1 = 0 := by
      rw [Polynomial.coeff_X_pow_mul', ite_eq_right (by norm_num : ¬ (2 ≤ 1))]
    have hC : (C (Gc S c) * Rpoly S c).coeff 1 = Gc S c * psi S c 1 := by
      rw [Polynomial.coeff_C_mul, coeff_Rpoly]
    rw [hX, hC]
    ring
  rw [hprod] at hc
  rw [hc]
  ring

theorem rem_eq_zero (S : SplitData d) {c : ℂ} (hc : c ∈ ball c₀ S.ρ)
    (hE : S.E c = 0 → (Qpoly c).derivative.eval (S.m c) = 0) :
    Phi S c %ₘ (X ^ 2 - C (Gc S c)) = 0 := by
  have ha := (rem_coeffs S hc).1
  have hb : (Phi S c %ₘ (X ^ 2 - C (Gc S c))).coeff 1 = 0 := by
    by_cases hEc : S.E c = 0
    · rw [coeff_one_rem, coeff_one_Phi, hE hEc]
      have hG : Gc S c = 0 := by simp [Gc, hEc]
      simp [hG]
    · exact (mul_eq_zero.mp (rem_coeffs S hc).2).resolve_right hEc
  rw [rem_eq_linear S c, ha, hb]
  simp

/-! ## 5. The shifted germ identity -/

theorem Qpoly_eval_shift_local (S : SplitData d) {c : ℂ} (hc : c ∈ ball c₀ S.ρ)
    (hE : S.E c = 0 → (Qpoly c).derivative.eval (S.m c) = 0) (w : ℂ) :
    (Qpoly c).eval (S.m c + w) = (w ^ 2 - Gc S c) * Rfun S c w := by
  rw [rem_eval_add S c w, rem_eq_zero S hc hE]
  simp

/-! ## 7. The conjugation of the germ -/

theorem parGerm_conj {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (S : Work.PARIMPL.ParSplit.SplitData d) :
    ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∀ c ∈ Metric.ball c₀ ρ', ∀ ζ : ℂ,
      Work.EL.F c (S.m c + Work.PARIMPL.ParSplit.parS S c * ζ)
        = S.m c + Work.PARIMPL.ParSplit.parS S c *
            (ζ + (ζ ^ 2 - (Work.PARIMPL.ParSplit.parA S c) ^ 2)
              * Work.PARIMPL.ParSplit.parHgerm S c ζ) := by
  obtain ⟨ρa, hρa, hρaS, hA⟩ := parChartSq S
  obtain ⟨ρb, hρb, hρbS, hB⟩ := Hp_double_root_count S
  refine ⟨min ρa ρb, lt_min hρa hρb, le_trans (min_le_left _ _) hρaS, ?_⟩
  intro c hc ζ
  have hca : c ∈ ball c₀ ρa :=
    mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hc) (min_le_left _ _))
  have hcb : c ∈ ball c₀ ρb :=
    mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hc) (min_le_right _ _))
  have hcS : c ∈ ball c₀ S.ρ :=
    mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hc) (le_trans (min_le_left _ _) hρaS))
  obtain ⟨hs0, hsa⟩ := hA c hca
  have hQ := Qpoly_eval_shift_local S hcS (hB c hcb) (parS S c * ζ)
  have hF := Qpoly_eval c (S.m c + parS S c * ζ)
  rw [hQ] at hF
  have key : Work.EL.F c (S.m c + parS S c * ζ) - (S.m c + parS S c * ζ)
      = parS S c * ((ζ ^ 2 - (parA S c) ^ 2) * parHgerm S c ζ) := by
    rw [← hF, ← hsa]
    unfold parHgerm
    ring
  rw [sub_eq_iff_eq_add] at key
  rw [key]
  ring

end Work.PARIMPL.ParSplit
