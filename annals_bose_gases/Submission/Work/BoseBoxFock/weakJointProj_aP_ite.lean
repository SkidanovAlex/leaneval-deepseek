import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.weakAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

/-!
# `Work.BoseBoxFock.weakJointProj_aP_ite`

The weak-class (measurable, everywhere bounded) port of
`Work.BoseFixB2.Sector.aP_blockOp_eq_zero` / `…aP_jointProj_eq_self` of
`Sector/jointProj_orthogonal.lean`: the joint sector projection `E_W = jointProj ℓ W` is an
eigenvector of the slot mean `P_k` for every slot `k < n`,

    P_k (E_W Φ) = 0                if `k ∈ W`   (the sector carries the factor `Q_k`),
    P_k (E_W Φ) = E_W Φ            if `k ∉ W`   (the sector carries the factor `P_k`).

The continuous proof is transcribed with continuity replaced by *measurability + a global
sup-bound* of the intermediate iterated products `blockOp ℓ W m Φ`
(`|blockOp ℓ W m Φ| ≤ 2^m C`, from `Work.BoseBoxFock.sectorXSpow_decomp_blockOp_abs_le`, which
needs no regularity at all).  Those two facts are exactly what the weak commutation lemmas of
`Work.BoseBoxFock.Weak` (`aP_comm`, `aP_aQ_comm`, `aP_aQ_self_eq_zero`) require.

Besides the two inductions only the hypothesis-free structural facts are used

* `Weak.aP_of_constIn`: `P_k` fixes every function that does not depend on the `k`-th slot;
* `Weak.constIn_aP` / `Weak.constIn_aQ`: slot-independence in the slot `i` is preserved by the
  operators of another slot `j ≠ i`;
* `Weak.aP_const_in_coord` (already in `weakAux`): `P_k G` does not depend on the `k`-th slot.
-/

namespace Weak

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Submission.BoseGases

/-! ## 1. The zero state -/

theorem aP_zero {n : ℕ} {ℓ : ℝ} (i : Fin n) : aP ℓ i (0 : X n → ℝ) = 0 := by
  funext x
  simp [aP]

theorem aQ_zero {n : ℕ} {ℓ : ℝ} (i : Fin n) : aQ ℓ i (0 : X n → ℝ) = 0 := by
  funext x
  simp [aQ, aP_zero]

/-! ## 2. Slot-independence

`ConstIn k F` says that `F` does not depend on the `k`-th slot.  The three lemmas below are the
`ConstIn`-half of the continuous induction; all three are hypothesis-free (they only compare
integrands pointwise). -/

/-- `F` does not depend on the `k`-th slot. -/
def ConstIn {n : ℕ} (k : Fin n) (F : X n → ℝ) : Prop :=
  ∀ (x : X n) (z : Sp), F (Function.update x k z) = F x

/-- `Pₖ` fixes every function that does not depend on the `k`-th slot. -/
theorem aP_of_constIn {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (k : Fin n) {F : X n → ℝ}
    (hF : ConstIn k F) : aP ℓ k F = F := by
  funext x
  calc aP ℓ k F x = (1 / ℓ ^ 3) * (∫ y in acube ℓ, F x) := by
        unfold aP
        congr 1
        apply integral_congr_ae
        filter_upwards with y
        exact hF x y
    _ = F x := by
        rw [integral_const_acube ℓ hℓ]
        field_simp [ne_of_gt hℓ]

/-- Slot-independence in the slot `i` is preserved by the mean operator in another slot. -/
theorem constIn_aP {n : ℕ} {ℓ : ℝ} {i j : Fin n} (hij : i ≠ j) {F : X n → ℝ}
    (hF : ConstIn i F) : ConstIn i (aP ℓ j F) := by
  intro x z
  unfold aP
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  rw [Function.update_comm hij z y x]
  exact hF (Function.update x j y) z

/-- Slot-independence in the slot `i` is preserved by the complement operator in another slot. -/
theorem constIn_aQ {n : ℕ} {ℓ : ℝ} {i j : Fin n} (hij : i ≠ j) {F : X n → ℝ}
    (hF : ConstIn i F) : ConstIn i (aQ ℓ j F) := by
  intro x z
  unfold aQ
  rw [hF x z, constIn_aP hij hF x z]

/-! ## 3. Measurability of the iterated products -/

/-- Every partial product `blockOp ℓ W m Φ` of a measurable state is measurable. -/
theorem blockOp_measurable {n : ℕ} {ℓ : ℝ} (W : Finset ℕ) {Φ : X n → ℝ}
    (hΦm : Measurable Φ) : ∀ k, k ≤ n → Measurable (Work.BoseFixB2.blockOp ℓ W k Φ) := by
  intro k
  induction k with
  | zero => intro _; simpa using hΦm
  | succ k ih =>
      intro hk
      have hkn : k < n := Nat.lt_of_succ_le hk
      rw [Work.BoseFixB2.blockOp_succ W hkn Φ]
      have hprev := ih (Nat.le_of_lt hkn)
      by_cases hmem : k ∈ W
      · rw [if_pos hmem]; exact aQ_measurable ⟨k, hkn⟩ hprev
      · rw [if_neg hmem]; exact aP_measurable ⟨k, hkn⟩ hprev

/-! ## 4. The two inductions -/

/-- **`Pₖ` kills the sector `W` as soon as the recursion has passed the slot `k`**, for `k ∈ W`
(the `k ∈ W` half of `aP_blockOp_eq_zero`). -/
theorem aP_blockOp_eq_zero_weak {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (W : Finset ℕ) {Φ : X n → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C) {k : ℕ} (hk : k < n)
    (hkW : k ∈ W) :
    ∀ m, k < m → m ≤ n → aP ℓ ⟨k, hk⟩ (Work.BoseFixB2.blockOp ℓ W m Φ) = 0 := by
  intro m
  induction m with
  | zero => intro h1 h2; omega
  | succ m ih =>
      intro hkm hmn
      have hmn' : m < n := Nat.lt_of_succ_le hmn
      have hkm' : k ≤ m := Nat.lt_succ_iff.mp hkm
      have hGm : Measurable (Work.BoseFixB2.blockOp ℓ W m Φ) :=
        blockOp_measurable W hΦm m (Nat.le_of_lt hmn')
      have hGb : ∀ x, |Work.BoseFixB2.blockOp ℓ W m Φ x| ≤ 2 ^ m * C :=
        sectorXSpow_decomp_blockOp_abs_le hℓ W hC hΦb m (Nat.le_of_lt hmn')
      have hCb : 0 ≤ 2 ^ m * C := mul_nonneg (by positivity) hC
      rw [Work.BoseFixB2.blockOp_succ W hmn' Φ]
      rcases lt_or_eq_of_le hkm' with hlt | heq
      · -- the new slot `m` is another slot: `Pₖ` commutes with the operator at slot `m`
        have hne : (⟨k, hk⟩ : Fin n) ≠ ⟨m, hmn'⟩ := by
          intro hcon; have := congrArg Fin.val hcon; simp at this; omega
        have ih' := ih hlt (Nat.le_of_lt hmn')
        by_cases hmW : m ∈ W
        · rw [if_pos hmW]
          funext x
          rw [aP_aQ_comm hℓ hne hCb hGm hGb x, ih']
          exact congrFun (aQ_zero (⟨m, hmn'⟩ : Fin n)) x
        · rw [if_neg hmW]
          funext x
          rw [aP_comm hℓ hne hCb hGm hGb x, ih']
          exact congrFun (aP_zero (⟨m, hmn'⟩ : Fin n)) x
      · -- the new slot `m = k` is the slot itself: it contributes `Qₖ`
        rw [show (⟨m, hmn'⟩ : Fin n) = ⟨k, hk⟩ from Fin.ext heq.symm]
        rw [if_pos (heq ▸ hkW)]
        exact aP_aQ_self_eq_zero hℓ ⟨k, hk⟩ hCb hGm hGb

/-- **The sector `W` no longer depends on the slot `k` as soon as the recursion has passed the
slot `k`**, for `k ∉ W` (the `k ∉ W` half of `aP_jointProj_eq_self`). -/
theorem constIn_blockOp_weak {n : ℕ} {ℓ : ℝ} (W : Finset ℕ) {Φ : X n → ℝ} {k : ℕ}
    (hk : k < n) (hkW : k ∉ W) :
    ∀ m, k < m → m ≤ n → ConstIn ⟨k, hk⟩ (Work.BoseFixB2.blockOp ℓ W m Φ) := by
  intro m
  induction m with
  | zero => intro h1 h2; omega
  | succ m ih =>
      intro hkm hmn
      have hmn' : m < n := Nat.lt_of_succ_le hmn
      have hkm' : k ≤ m := Nat.lt_succ_iff.mp hkm
      rw [Work.BoseFixB2.blockOp_succ W hmn' Φ]
      rcases lt_or_eq_of_le hkm' with hlt | heq
      · -- the new slot `m` is another slot: it preserves independence of the slot `k`
        have hne : (⟨k, hk⟩ : Fin n) ≠ ⟨m, hmn'⟩ := by
          intro hcon; have := congrArg Fin.val hcon; simp at this; omega
        have ih' := ih hlt (Nat.le_of_lt hmn')
        by_cases hmW : m ∈ W
        · rw [if_pos hmW]; exact constIn_aQ hne ih'
        · rw [if_neg hmW]; exact constIn_aP hne ih'
      · -- the new slot `m = k` is the slot itself: it contributes the mean `Pₖ`
        rw [show (⟨m, hmn'⟩ : Fin n) = ⟨k, hk⟩ from Fin.ext heq.symm]
        rw [if_neg (heq ▸ hkW)]
        exact aP_const_in_coord ⟨k, hk⟩ (Work.BoseFixB2.blockOp ℓ W m Φ)

end Weak

/-! ## 5. The theorem -/

/-- **The joint sector projection is an eigenvector of the slot mean**, in the measurable/bounded
state class.  `E_W = jointProj ℓ W` is the iterated product over the slots `0,…,n−1` of `Q_i = 1 − P_i`
for `i ∈ W` and `P_i = aP ℓ i` for `i ∉ W` (`Work.BoseFixB2.jointProj = blockOp ℓ W n`), so applying
the slot mean at a slot `k < n` either kills the sector (`k ∈ W`, the sector carries the factor
`Q_k`) or fixes it (`k ∉ W`, the sector carries the factor `P_k`).

The proof is the port of `Work.BoseFixB2.Sector.aP_blockOp_eq_zero` /
`…aP_jointProj_eq_self` from the continuous class (`ContDiff`) to the measurable/bounded class:
the slot means of *distinct* slots commute (`Work.BoseBoxFock.Weak.aP_comm`,
`…aP_aQ_comm`, `…aQ_comm`, all Fubini for bounded measurable states), and `P_k Q_k = 0`
(`Work.BoseBoxFock.Weak.aP_aQ_self_eq_zero`).  Boundedness of the intermediate iterated products
`blockOp ℓ W m Φ` (`< 2^m C`, from `Work.BoseBoxFock.sectorXSpow_decomp_blockOp_abs_le`) replaces
continuity. -/
theorem weakJointProj_aP_ite {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {k : ℕ} (hk : k < n)
    (W : Finset ℕ) {Φ : Submission.BoseGases.X n → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hΦm : Measurable Φ) (hΦb : ∀ x, |Φ x| ≤ C) :
    Submission.BoseGases.aP ℓ ⟨k, hk⟩ (Work.BoseFixB2.jointProj ℓ W Φ)
      = if k ∈ W then 0 else Work.BoseFixB2.jointProj ℓ W Φ := by
  by_cases h : k ∈ W
  · rw [if_pos h]
    show Submission.BoseGases.aP ℓ ⟨k, hk⟩ (Work.BoseFixB2.blockOp ℓ W n Φ) = 0
    exact Weak.aP_blockOp_eq_zero_weak hℓ W hC hΦm hΦb hk h n hk le_rfl
  · rw [if_neg h]
    show Submission.BoseGases.aP ℓ ⟨k, hk⟩ (Work.BoseFixB2.blockOp ℓ W n Φ)
      = Work.BoseFixB2.blockOp ℓ W n Φ
    exact Weak.aP_of_constIn hℓ ⟨k, hk⟩ (Weak.constIn_blockOp_weak W hk h n hk le_rfl)

end Work.BoseBoxFock
