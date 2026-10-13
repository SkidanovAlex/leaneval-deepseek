/-
# `Fstar_jet_rel`

The profile `F_* z = 2z/(1+z)²` of the fundamental model, and its iterated
`z∂_z`-jets: there is a universal constant `K > 0` with

  `|D_z^b F_* z| ≤ K · F_* z`  for `b ≤ 6`, `z > 0`.

Since `F_*` vanishes like `2z` at `z = 0`, the point of the statement is that the
*jets relative to the profile* stay bounded -- the ratio `D_z^b F_*/F_*` is a
rational function which extends continuously to `[0,∞)`.

## Route

* `F_*` is analytic on `(-1,∞)` and `∂_z^k F_* z = 2(-1)^k k! (z-k)/(1+z)^{k+2}`
  (`deriv_iter_FM_Fstar_eq`); hence

    `z^k ∂_z^k F_* z = F_* z · (-1)^k k! (z^{k-1}(z-k))/(1+z)^k`,

  and `|z^{k-1}(z-k)| ≤ (k+1)(1+z)^k` for `z > 0`, so

    `|z^k ∂_z^k F_* z| ≤ (k+1)! F_* z`.

* the Stirling expansion `D_z^b = ∑_{k≤b} S(b,k) z^k ∂_z^k`
  (`Spaces.DzIter_eq_sum_scoef`) and the coefficient-mass bound
  `Spaces.abs_sum_scoef_mul_le` then give
  `|D_z^b F_* z| ≤ bell b · 5040 · F_* z ≤ 877 · 5040 · F_* z` for `b ≤ 6`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FM.Core
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.FTS.CoercivityFix.E2Bound.zop_phi_bound
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
import Submission.Work.Spaces.DzIter_le_of_pzIter

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6.aux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary profile facts -/

/-- `F_* z > 0` for `z > 0`. -/
private lemma Fstar_pos {z : ℝ} (hz : 0 < z) : 0 < Work.FM.Fstar z := by
  rw [Work.FM.Fstar]
  positivity

/-- For `k ≥ 1` and `z > 0`, `|z^{k-1}(z-k)| ≤ (k+1)(1+z)^k`. -/
private lemma abs_zpow_pred_mul_sub_le (k : ℕ) (hk : 1 ≤ k) {z : ℝ} (hz : 0 < z) :
    |z ^ (k - 1) * (z - (k : ℝ))| ≤ ((k : ℝ) + 1) * (1 + z) ^ k := by
  have hk1 : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk
  have hrew : z ^ (k - 1) * (z - (k : ℝ)) = z ^ k - (k : ℝ) * z ^ (k - 1) := by
    rw [mul_sub, ← pow_succ, hk1]
    ring
  rw [hrew]
  have hz1 : (1 : ℝ) ≤ 1 + z := by linarith
  have hA : z ^ k ≤ (1 + z) ^ k := pow_le_pow_left₀ hz.le (by linarith) k
  have hB : z ^ (k - 1) ≤ (1 + z) ^ k := by
    calc z ^ (k - 1) ≤ (1 + z) ^ (k - 1) := pow_le_pow_left₀ hz.le (by linarith) (k - 1)
      _ ≤ (1 + z) ^ k := pow_le_pow_right₀ hz1 (by omega)
  have h1 : |z ^ k - (k : ℝ) * z ^ (k - 1)| ≤ z ^ k + (k : ℝ) * z ^ (k - 1) := by
    rw [abs_le]
    constructor <;> nlinarith [pow_nonneg hz.le k, pow_nonneg hz.le (k - 1)]
  nlinarith [h1, hA, hB]

/-- **The weighted plain derivatives of the profile, relative to the profile**:
`|z^k ∂_z^k F_* z| ≤ (k+1)! · F_* z` for `z > 0`. -/
private lemma zpow_deriv_FM_Fstar_le (k : ℕ) {z : ℝ} (hz : 0 < z) :
    |z ^ k * deriv^[k] (fun z => Work.FM.Fstar z) z| ≤ ((k + 1).factorial : ℝ) * Work.FM.Fstar z := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hzI : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  rcases k with _ | m
  · rw [pow_zero, one_mul, Function.iterate_zero_apply, abs_of_pos (Fstar_pos hz)]
    norm_num
  · rw [Work.FTS.StrongPersist.H6Pair6Aux.deriv_iter_FM_Fstar_eq (m + 1) hzI]
    have hkey : z ^ (m + 1) * (2 * (-1 : ℝ) ^ (m + 1) * (((m + 1).factorial : ℝ))
          * (z - (((m + 1 : ℕ) : ℝ))) / (1 + z) ^ (m + 1 + 2))
        = Work.FM.Fstar z * (((-1 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ))
          * (z ^ m * (z - (((m + 1 : ℕ) : ℝ))) / (1 + z) ^ (m + 1))) := by
      rw [Work.FM.Fstar]
      field_simp
      ring
    rw [hkey, abs_mul, abs_of_pos (Fstar_pos hz)]
    have hb : |((-1 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ))
        * (z ^ m * (z - (((m + 1 : ℕ) : ℝ))) / (1 + z) ^ (m + 1))|
        ≤ ((m + 1 + 1).factorial : ℝ) := by
      rw [abs_mul]
      have hc : |(-1 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ)| = ((m + 1).factorial : ℝ) := by
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      rw [hc, abs_div, abs_of_pos (pow_pos hz1 (m + 1)), ← mul_div_assoc]
      rw [div_le_iff₀ (pow_pos hz1 (m + 1))]
      have hnum := abs_zpow_pred_mul_sub_le (m + 1) (Nat.le_add_left 1 m) hz
      have hnum' : |z ^ m * (z - (((m + 1 : ℕ) : ℝ)))|
          ≤ (((m + 1 : ℕ) : ℝ) + 1) * (1 + z) ^ (m + 1) := by
        simpa only [Nat.add_sub_cancel] using hnum
      calc ((m + 1).factorial : ℝ) * |z ^ m * (z - (((m + 1 : ℕ) : ℝ)))|
          ≤ ((m + 1).factorial : ℝ) * ((((m + 1 : ℕ) : ℝ) + 1) * (1 + z) ^ (m + 1)) :=
            mul_le_mul_of_nonneg_left hnum' (Nat.cast_nonneg _)
        _ = (((m + 1 + 1).factorial : ℝ)) * (1 + z) ^ (m + 1) := by
            have hf : (((m + 1 + 1).factorial : ℝ))
                = ((m + 1).factorial : ℝ) * ((((m + 1 : ℕ) : ℝ)) + 1) := by
              rw [Nat.factorial_succ (m + 1)]; push_cast; ring
            rw [hf]; ring
    calc Work.FM.Fstar z * |((-1 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ))
            * (z ^ m * (z - (((m + 1 : ℕ) : ℝ))) / (1 + z) ^ (m + 1))|
        ≤ Work.FM.Fstar z * ((m + 1 + 1).factorial : ℝ) :=
          mul_le_mul_of_nonneg_left hb (Fstar_pos hz).le
      _ = (((m + 1) + 1).factorial : ℝ) * Work.FM.Fstar z := by ring

/-! ## The Bell-number bound -/

private lemma bell_le (b : ℕ) (hb : b ≤ 6) : (Work.Spaces.bell b : ℝ) ≤ 877 := by
  exact_mod_cast Work.FTS.StrongPersist.H6Pair6Aux.bell_le_seven b (by omega)

private lemma factorial_succ_le (k : ℕ) (hk : k ≤ 6) : ((k + 1).factorial : ℝ) ≤ 5040 := by
  have h : (k + 1).factorial ≤ Nat.factorial 7 := Nat.factorial_le (by omega)
  have h7 : ((Nat.factorial 7 : ℕ) : ℝ) = 5040 := by norm_num
  calc ((k + 1).factorial : ℝ) ≤ ((Nat.factorial 7 : ℕ) : ℝ) := by exact_mod_cast h
    _ = 5040 := h7

/-! ## The theorem -/

theorem Fstar_jet_rel : ∃ K : ℝ, 0 < K ∧ ∀ b : ℕ, b ≤ 6 → ∀ z : ℝ, 0 < z →
    |Work.Elliptic.DzdIter b Work.FM.Fstar z| ≤ K * Work.FM.Fstar z := by
  refine ⟨877 * 5040, by norm_num, ?_⟩
  intro b hb z hz
  have hzI : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have h0I : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, Real.pi_div_two_pos.le⟩
  have hsmooth : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ ⊤ (fun z => (fun z _ => Work.FM.Fstar z) z θ) (Set.Ioi (-1)) :=
    fun _ _ => Work.FTS.StrongPersist.H6Pair6Aux.contDiffOn_FM_Fstar_analytic
  rw [show Work.Elliptic.DzdIter b Work.FM.Fstar z
      = Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z 0 from
    (Work.Elliptic.DzIter_rad Work.FM.Fstar b z 0).symm]
  rw [Work.Spaces.DzIter_eq_sum_scoef hsmooth b z hzI 0 h0I]
  have hx : ∀ k ≤ b, |z ^ k * Work.Spaces.pzIter k (fun z _ => Work.FM.Fstar z) z 0|
      ≤ 5040 * Work.FM.Fstar z := by
    intro k hk
    rw [Work.FTS.StrongPersist.H6Pair6Aux.pzIter_zonly_eq_FM_deriv_iter]
    refine (zpow_deriv_FM_Fstar_le k hz).trans ?_
    exact mul_le_mul_of_nonneg_right (factorial_succ_le k (le_trans hk hb)) (Fstar_pos hz).le
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b (5040 * Work.FM.Fstar z)
    (fun k => z ^ k * Work.Spaces.pzIter k (fun z _ => Work.FM.Fstar z) z 0) hx
  refine hsum.trans ?_
  calc (Work.Spaces.bell b : ℝ) * (5040 * Work.FM.Fstar z)
      ≤ 877 * (5040 * Work.FM.Fstar z) :=
        mul_le_mul_of_nonneg_right (bell_le b hb)
          (mul_nonneg (by norm_num) (Fstar_pos hz).le)
    _ = (877 * 5040) * Work.FM.Fstar z := by ring

end Work.FTS.StrongEps.E4R3.Nblock6.aux
