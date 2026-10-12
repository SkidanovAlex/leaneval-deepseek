import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseFixB2.Sector.jointProj_orthogonal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Sector.nPlusPow_jointProj`

The joint sector projection `E_S = ∏_{i∈S} Q_i ∏_{j∉S} P_j` (`Work.BoseFixB2.jointProj`,
`S ⊆ {0,…,n−1}`) is an **eigenvector of the excitation-number operator** `n₊ = ΣᵢQᵢ`
(`Work.BoseBox.nPlusFun = nPlusPow ℓ n 1`) with eigenvalue `|S|`:

    n₊^m (E_S Φ) = |S|^m · E_S Φ       (all m ≥ 0, Φ smooth).

This is the elementary spectral fact underlying FS §6 (`lem:LocMatrices`,
`final_v2.tex` ll. 1365–1445): the slot operators `Pᵢ, Qᵢ = 1 − Pᵢ` form a commuting
family of projections (`aP_comm`, `aP_aQ_comm`), so `E_S` is the joint eigenvector
with eigenvalue `0` on the slots `∉ S` and `1` on the slots `∈ S`; summing the `n`
slots gives the eigenvalue `|S|`, and the eigenvalue multiplies under iteration
(`n₊` is homogeneous, `aP_const_smul`/`aQ_const_smul`).

## Contents

* `aQ_jointProj_of_mem` — `Q_k (E_S Φ) = E_S Φ` for `k ∈ S` (`k < n`);
* `aQ_jointProj_of_notMem` — `Q_k (E_S Φ) = 0` for `k ∉ S` (`k < n`);
* `nPlusFun_smul` — homogeneity of `n₊` under a pointwise scalar;
* `nPlusFun_jointProj` — the `m = 1` case: `n₊ (E_S Φ) = |S| · E_S Φ`;
* `nPlusPow_jointProj` — the all-`m` statement (the target).

The `m`-induction is immediate from the two facts just listed: the induction
hypothesis writes `n₊^m E_S = |S|^m • E_S`, `n₊` is homogeneous over a scalar, and
`n₊ (E_S) = |S| • E_S`.
-/

noncomputable section

namespace Work.BoseFixB2.Sector

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The two slot eigenvector identities -/

/-- **`Q_k` fixes the sector `E_S` when `k ∈ S`.**  The mean `P_k` annihilates `E_S`
(it contains the factor `Q_k`), so `Q_k = 1 − P_k` fixes it. -/
lemma aQ_jointProj_of_mem {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {S : Finset ℕ} {k : ℕ}
    (hkS : k ∈ S) (hkn : k < n) {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    aQ ℓ ⟨k, hkn⟩ (jointProj ℓ S Φ) = jointProj ℓ S Φ := by
  have hP : aP ℓ ⟨k, hkn⟩ (jointProj ℓ S Φ) = 0 := aP_blockOp_eq_zero hℓ hkn hkS hΦ
  funext x
  show jointProj ℓ S Φ x - aP ℓ ⟨k, hkn⟩ (jointProj ℓ S Φ) x = jointProj ℓ S Φ x
  rw [congrFun hP x]
  simp

/-- **`Q_k` kills the sector `E_S` when `k ∉ S`.**  The slot `k` of `E_S` carries the
mean `P_k`, and `E_S` does not depend on the `k`-th variable there, so `P_k` fixes
`E_S` and `Q_k = 1 − P_k` annihilates it. -/
lemma aQ_jointProj_of_notMem {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {S : Finset ℕ} {k : ℕ}
    (hkS : k ∉ S) (hkn : k < n) {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    aQ ℓ ⟨k, hkn⟩ (jointProj ℓ S Φ) = 0 := by
  have hP : aP ℓ ⟨k, hkn⟩ (jointProj ℓ S Φ) = jointProj ℓ S Φ :=
    aP_jointProj_eq_self hℓ hkn hkS hΦ
  funext x
  show jointProj ℓ S Φ x - aP ℓ ⟨k, hkn⟩ (jointProj ℓ S Φ) x = (0 : ℝ)
  rw [congrFun hP x, sub_self]

/-! ## 2. Homogeneity of `n₊` and the eigenvalue identity -/

/-- **`n₊` is homogeneous**: `n₊(c • Ψ) = c • n₊Ψ`.  Immediate from the linearity of
the slot operators `Q_i = 1 − P_i` (`aQ_const_smul`). -/
lemma nPlusFun_smul (ℓ : ℝ) {N : ℕ} (c : ℝ) (Ψ : X N → ℝ) :
    Work.BoseBox.nPlusFun ℓ (fun x => c * Ψ x)
      = fun x => c * Work.BoseBox.nPlusFun ℓ Ψ x := by
  have hfun : (fun x : X N => c * Ψ x) = c • Ψ := by
    funext x
    simp
  funext x
  rw [hfun]
  simp only [Work.BoseBox.nPlusFun]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => aQ_const_smul ℓ i Ψ c x)

/-- The cardinality of the slots `i : Fin n` belonging to `S`, for `S ⊆ {0,…,n−1}`. -/
lemma card_filter_univ_eq {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range n) :
    (Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ S)).card = S.card := by
  refine Finset.card_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro b hb
    exact ⟨⟨b, Finset.mem_range.mp (hS hb)⟩, by simp [hb], rfl⟩

/-- **The eigenvalue identity**: the excitation number of the sector `E_S` is `|S|`,

    `n₊ (E_S Φ) = |S| · E_S Φ            (S ⊆ {0,…,n−1}, Φ continuous)`.

Each of the `n` slot operators either fixes `E_S` (`i ∈ S`) or kills it (`i ∉ S`), so
the sum over the slots keeps exactly the `|S|` slots of `S`. -/
lemma nPlusFun_jointProj {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    Work.BoseBox.nPlusFun ℓ (jointProj ℓ S Φ)
      = fun x => (S.card : ℝ) * jointProj ℓ S Φ x := by
  funext x
  simp only [Work.BoseBox.nPlusFun]
  have hE : ∀ i : Fin n,
      aQ ℓ i (jointProj ℓ S Φ) x
        = if (i : ℕ) ∈ S then jointProj ℓ S Φ x else 0 := by
    intro i
    by_cases hmem : (i : ℕ) ∈ S
    · rw [if_pos hmem]
      exact congrFun (aQ_jointProj_of_mem hℓ hmem i.isLt hΦ) x
    · rw [if_neg hmem]
      simpa using congrFun (aQ_jointProj_of_notMem hℓ hmem i.isLt hΦ) x
  rw [Finset.sum_congr rfl (fun i _ => hE i)]
  rw [← Finset.sum_filter (s := Finset.univ) (p := fun i : Fin n => (i : ℕ) ∈ S)
        (f := fun _ => jointProj ℓ S Φ x),
      Finset.sum_const, nsmul_eq_mul, card_filter_univ_eq hS]

/-! ## 3. The iterates of `n₊` on a sector -/

/-- The two defining equations of `Work.BoseBox.nPlusPow`, as rewrite rules. -/
private lemma nPlusPow_zero (ℓ : ℝ) (N : ℕ) (Φ : X N → ℝ) :
    Work.BoseBox.nPlusPow ℓ N 0 Φ = Φ := rfl

private lemma nPlusPow_succ (ℓ : ℝ) (N m : ℕ) (Φ : X N → ℝ) :
    Work.BoseBox.nPlusPow ℓ N (m + 1) Φ
      = Work.BoseBox.nPlusFun ℓ (Work.BoseBox.nPlusPow ℓ N m Φ) := rfl

/-- **Every iterate of `n₊` acts on the sector `E_S` by the power of the eigenvalue**:

    `n₊^m (E_S Φ) = |S|^m · E_S Φ`.

Induction on `m`: the case `m + 1` is `n₊(c • E_S Φ) = c • n₊(E_S Φ)` (homogeneity,
`nPlusFun_smul`) combined with the eigenvalue identity `nPlusFun_jointProj`. -/
theorem nPlusPow_jointProj {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (m : ℕ) :
    Work.BoseBox.nPlusPow ℓ n m (Work.BoseFixB2.jointProj ℓ S Φ)
      = fun x => (S.card : ℝ) ^ m * Work.BoseFixB2.jointProj ℓ S Φ x := by
  have hΦc : Continuous Φ := hΦ.continuous
  induction m with
  | zero =>
      rw [nPlusPow_zero]
      funext x
      simp
  | succ m ih =>
      rw [nPlusPow_succ, ih, nPlusFun_smul ℓ ((S.card : ℝ) ^ m) (jointProj ℓ S Φ),
        nPlusFun_jointProj hℓ hS hΦc]
      funext x
      rw [pow_succ]
      ring

end Work.BoseFixB2.Sector
