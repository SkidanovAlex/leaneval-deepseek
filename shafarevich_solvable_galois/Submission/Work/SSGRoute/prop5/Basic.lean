/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Proposition 5 of Schmidt–Wingberg: the commutator word and the value map

This file sets up the *raw* data of Proposition 5 of Schmidt–Wingberg (arXiv:math/9809211, §2):

* `commWord j x` : the `j`-fold left-normed commutator `⁅x₀, ⁅x₁, ⋯ ⁅x_{j-2}, x_{j-1}⋯⁆⁆`
  (in Mathlib's commutator convention `⁅a,b⁆ = a b a⁻¹ b⁻¹`);
* the value map `valFn p G i j d` on `j`-tuples of elements of the free `G`-operator group
  `F(d)`, whose value is the class of `(commWord j x) ^ (p ^ (i-j))` in the graded piece
  `E(d,(i,j)) = F(d)^{(i,j)}/F(d)^{(i,j)+1}`.

Everything here is elementary; the only group-theoretic input is `pow_mem_pSeries` below.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Refined
import Submission.Work.ProP.lowerCentralSeries_le_pCentralSeries
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped commutatorElement

set_option maxHeartbeats 1600000

namespace Work.SSGRoute.prop5

universe u

/-! ## The `j`-fold left-normed commutator word -/

/-- `commWord j x` is the `j`-fold left-normed commutator
`⁅x 0, ⁅x 1, ⋯ ⁅x (j-2), x (j-1) ⋯⁆⁆` (Mathlib's commutator convention). -/
def commWord {P : Type*} [Group P] : (j : ℕ) → (Fin j → P) → P
  | 0, _ => 1
  | 1, x => x 0
  | (k + 2), x => ⁅x 0, commWord (k + 1) (fun t => x t.succ)⁆

@[simp] lemma commWord_zero {P : Type*} [Group P] (x : Fin 0 → P) : commWord 0 x = 1 := rfl

@[simp] lemma commWord_one {P : Type*} [Group P] (x : Fin 1 → P) : commWord 1 x = x 0 := rfl

@[simp] lemma commWord_succ_succ {P : Type*} [Group P] (k : ℕ) (x : Fin (k + 2) → P) :
    commWord (k + 2) x = ⁅x 0, commWord (k + 1) (fun t => x t.succ)⁆ := rfl

lemma commutator_top_lowerCentralSeries_le (P : Type*) [Group P] (n : ℕ) :
    ⁅(⊤ : Subgroup P), (⊤ : Subgroup P).lowerCentralSeries n⁆ ≤
      (⊤ : Subgroup P).lowerCentralSeries (n + 1) := by
  rw [Subgroup.commutator_comm, Subgroup.lowerCentralSeries_succ]

/-- The `j`-fold commutator of arbitrary elements lies in the `j`-th term of the lower
central series. -/
lemma commWord_mem_lowerCentralSeries {P : Type*} [Group P] (j : ℕ) (x : Fin j → P) :
    commWord j x ∈ (⊤ : Subgroup P).lowerCentralSeries (j - 1) := by
  match j, x with
  | 0, x => simp
  | 1, x => rw [commWord_one]; exact Subgroup.mem_top _
  | (k + 2), x =>
      rw [commWord_succ_succ]
      have hc : commWord (k + 1) (fun t => x t.succ) ∈
          (⊤ : Subgroup P).lowerCentralSeries ((k + 1) - 1) :=
        commWord_mem_lowerCentralSeries (k + 1) _
      have hmem : ⁅x 0, commWord (k + 1) (fun t => x t.succ)⁆ ∈
          (⊤ : Subgroup P).lowerCentralSeries (((k + 1) - 1) + 1) :=
        commutator_top_lowerCentralSeries_le P ((k + 1) - 1)
          (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) hc)
      simpa using hmem

/-- Powers of elements of `γ_k` lie in the `p`-central series term `P_{k+t}`: iterated
`p`-th powers raise the `p`-central index by one. -/
lemma pow_mem_pSeries (p : ℕ) {P : Type*} [Group P] (k t : ℕ) (hk : 1 ≤ k) (x : P)
    (hx : x ∈ (⊤ : Subgroup P).lowerCentralSeries (k - 1)) :
    x ^ (p ^ t) ∈ Work.Shrinking.pCentralSeries p P (k + t - 1) := by
  have hle : x ∈ Work.Shrinking.pCentralSeries p P (k - 1) :=
    Work.ProP.lowerCentralSeries_le_pCentralSeries p P (k - 1) hx
  induction t with
  | zero => simpa using hle
  | succ t ih =>
      have hpow : x ^ (p ^ (t + 1)) = (x ^ (p ^ t)) ^ p := by rw [pow_succ, pow_mul]
      rw [hpow]
      have hstep := Work.Shrinking.pow_mem_pCentralSeries_succ p P ih
      have hidx : (k + t - 1) + 1 = k + (t + 1) - 1 := by omega
      rwa [hidx] at hstep

/-! ## The value map of Proposition 5 -/

/-- The membership of the raw commutator value in the refined term `F(d)^{(i,j)}`. -/
lemma commWord_pow_mem_refinedTerm (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    (i j d : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (x : Fin j → Work.Shrinking.freeOperatorGroup G d) :
    (commWord j x) ^ (p ^ (i - j)) ∈
      Work.CohomologicalShrinking.refinedTerm p (Work.Shrinking.freeOperatorGroup G d) i j := by
  rw [Work.CohomologicalShrinking.refinedTerm]
  refine Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · have hmem := pow_mem_pSeries p j (i - j) hj (commWord j x)
      (commWord_mem_lowerCentralSeries j x)
    have hidx : j + (i - j) - 1 = i - 1 := by omega
    rwa [hidx] at hmem
  · exact pow_mem (commWord_mem_lowerCentralSeries j x) _

/-- The value of the paper's map `φ_τ` on a `j`-tuple `x` of elements of `F(d)`: the class of
`(⁅x₀,⁅x₁,⋯⁆⁆)^{p^{i-j}}` in the graded piece `E(d,(i,j))`, with the membership witness as an
explicit argument. -/
noncomputable def valFnOf (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i) (x : Fin j → Work.Shrinking.freeOperatorGroup G d)
    (h : (commWord j x) ^ (p ^ (i - j)) ∈
      Work.CohomologicalShrinking.refinedTerm p (Work.Shrinking.freeOperatorGroup G d) i j) :
    Work.CohomologicalShrinking.E p G d i j := by
  haveI : ((Work.CohomologicalShrinking.refinedTerm p (Work.Shrinking.freeOperatorGroup G d)
        (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2).subgroupOf
      (Work.CohomologicalShrinking.refinedTerm p (Work.Shrinking.freeOperatorGroup G d) i j)).Normal :=
    (Work.CohomologicalShrinking.refinedTerm_normal p (Work.Shrinking.freeOperatorGroup G d)
      (Work.CohomologicalShrinking.tauSucc i j).1
      (Work.CohomologicalShrinking.tauSucc i j).2).subgroupOf _
  exact Additive.ofMul (QuotientGroup.mk' _ ⟨(commWord j x) ^ (p ^ (i - j)), h⟩)

/-- The value map of Proposition 5. -/
noncomputable def valFn (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i) (x : Fin j → Work.Shrinking.freeOperatorGroup G d) :
    Work.CohomologicalShrinking.E p G d i j :=
  valFnOf p G i j d hj hji x (commWord_pow_mem_refinedTerm p G i j d hj hji x)

lemma valFn_eq (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i) (x : Fin j → Work.Shrinking.freeOperatorGroup G d) :
    valFn p G i j d hj hji x =
      valFnOf p G i j d hj hji x (commWord_pow_mem_refinedTerm p G i j d hj hji x) := rfl

end Work.SSGRoute.prop5
