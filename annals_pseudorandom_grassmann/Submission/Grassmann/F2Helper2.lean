import Submission.Grassmann.F2Helper
import Submission.Commons.Combinatorics.QBinomial.gb_pow_sum_le
import Submission.Commons.Combinatorics.QBinomial.gb_pair_pow_sum_lt_one
import Submission.Commons.Analysis.Inequalities.sum_sq_le_mul_sum_of_pointwise

/-!
# `lem:F2` of arXiv:2209.04243 — the Cauchy--Schwarz step

This file continues `Submission/Grassmann/F2Helper.lean` (`lem:F2 helper`) with the corollary
`lem:F2`: Cauchy--Schwarz turns the triangle-inequality bound into a sum of *squares* of the
`(L_{V₁}∘L_{W₁}[f])²` Fourier coefficients, at the cost of the explicit weight
`q^{7d(i+j)}` and of the arithmetic bound `Σ_{(i,j)≠(0,0)} q^{-2d(i+j)} < 1`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-- The `ℝ`-valued version of `sum_sum_ite_and`. -/
lemma sum_sum_ite_and_real {α β : Type*} [Fintype α] [Fintype β]
    (p : α → Prop) (q : β → Prop) (z : ℝ) :
    (∑ a : α, ∑ b : β, (if p a ∧ q b then z else 0))
      = (Fintype.card {a : α // p a} : ℝ) * (Fintype.card {b : β // q b} : ℝ) * z := by
  have h : ∀ (a : α) (b : β),
      (if p a ∧ q b then z else 0)
        = (if p a then (1 : ℝ) else 0) * ((if q b then (1 : ℝ) else 0) * z) := by
    intro a b
    by_cases ha : p a <;> by_cases hb : q b <;> simp [ha, hb]
  simp only [h]
  rw [← Finset.sum_mul_sum]
  have h2 : (∑ b : β, (if q b then (1 : ℝ) else 0) * z)
      = (∑ b : β, (if q b then (1 : ℝ) else 0)) * z := (Finset.sum_mul _ _ _).symm
  rw [h2]
  have hp : (∑ a : α, (if p a then (1 : ℝ) else 0)) = (Fintype.card {a : α // p a} : ℝ) := by
    rw [Finset.sum_boole]
    rw [← Fintype.card_subtype p]
  have hq : (∑ b : β, (if q b then (1 : ℝ) else 0)) = (Fintype.card {b : β // q b} : ℝ) := by
    rw [Finset.sum_boole]
    rw [← Fintype.card_subtype q]
  rw [hp, hq]
  ring

/-- `finrank (range X) = X.rank`. -/
lemma finrank_range_mulVecLin {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    Module.finrank 𝔽₂ ↥(LinearMap.range X.mulVecLin) = X.rank := rfl

/-- Rank--nullity in the form used below. -/
lemma finrank_ker_mulVecLin {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    Module.finrank 𝔽₂ ↥(LinearMap.ker X.mulVecLin) = m - X.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
  rw [Module.finrank_pi, Fintype.card_fin] at h
  have hfin : Module.finrank 𝔽₂ ↥(LinearMap.range X.mulVecLin) = X.rank := rfl
  omega

/-- `m - finrank (ker X) = X.rank`. -/
lemma sub_finrank_ker {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    m - Module.finrank 𝔽₂ ↥(LinearMap.ker X.mulVecLin) = X.rank := by
  rw [finrank_ker_mulVecLin]
  have : X.rank ≤ m := Matrix.rank_le_width X
  omega

/-- The predicate `V₁ ∈ 𝓥_i(X)`. -/
def condV {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂) (i : ℕ)
    (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) : Prop :=
  V₁ ≤ LinearMap.range X.mulVecLin ∧ Module.finrank 𝔽₂ V₁ = i

/-- The predicate `W₁ ∈ 𝓦_j(X)`. -/
def condW {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂) (j : ℕ)
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) : Prop :=
  LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ W₁ = m - j

lemma card_condV {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂) (i : ℕ) :
    (Nat.card {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂) // condV X i V₁})
      = Commons.Combinatorics.QBinomial.gb X.rank i := by
  have h1 : Nat.card {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂) // condV X i V₁}
      = Commons.Combinatorics.QBinomial.gb
          (Module.finrank 𝔽₂ ↥(LinearMap.range X.mulVecLin)) i :=
    Commons.LinearAlgebra.Submodule.card_submodule_le_finrank_eq_gb n
      (LinearMap.range X.mulVecLin) i
  rw [h1, finrank_range_mulVecLin]

lemma card_condW {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂) (j : ℕ) (hj : j ≤ m) :
    (Nat.card {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂) // condW X j W₁})
      = Commons.Combinatorics.QBinomial.gb X.rank j := by
  have h1 : Nat.card {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂) // condW X j W₁}
      = Commons.Combinatorics.QBinomial.gb
          (m - Module.finrank 𝔽₂ ↥(LinearMap.ker X.mulVecLin)) j :=
    Commons.LinearAlgebra.Submodule.card_superspace_codim_eq_gb_of_le m
      (LinearMap.ker X.mulVecLin) j hj
  rw [h1, sub_finrank_ker]

/-- **The number of pairs `(V₁,W₁)` counted by the `𝓕₂` bound** is the product of the two
Gaussian binomials `gb (rank X) i` and `gb (rank X) j`. -/
theorem card_cond_eq {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂) (i j : ℕ) (hj : j ≤ m) :
    (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
      (if V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧
          Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j
        then (1 : ℝ) else 0))
      = (Commons.Combinatorics.QBinomial.gb X.rank i : ℝ) *
        (Commons.Combinatorics.QBinomial.gb X.rank j : ℝ) := by
  classical
  have hstep : ∀ (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)),
      (if V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧
          Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j
        then (1 : ℝ) else 0)
        = (if V₁ ≤ LinearMap.range X.mulVecLin ∧ Module.finrank 𝔽₂ V₁ = i
              then (1 : ℝ) else 0) *
          (if LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ W₁ = m - j
              then (1 : ℝ) else 0) := by
    intro V₁ W₁
    by_cases h1 : V₁ ≤ LinearMap.range X.mulVecLin ∧ Module.finrank 𝔽₂ V₁ = i
    · by_cases h2 : LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ W₁ = m - j
      · rw [if_pos ⟨h1.1, h2.1, h1.2, h2.2⟩, if_pos h1, if_pos h2, mul_one]
      · rw [if_neg (fun h => h2 ⟨h.2.1, h.2.2.2⟩), if_pos h1, if_neg h2, mul_zero]
    · rw [if_neg (fun h => h1 ⟨h.1, h.2.2.1⟩), if_neg h1, zero_mul]
  have hcardV : (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂),
        (if V₁ ≤ LinearMap.range X.mulVecLin ∧ Module.finrank 𝔽₂ V₁ = i
          then (1 : ℝ) else 0))
      = (Nat.card {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂) // condV X i V₁} : ℝ) := by
    rw [Finset.sum_boole]
    rw [← Fintype.card_subtype (fun x : Submodule 𝔽₂ (Fin n → 𝔽₂) =>
      x ≤ LinearMap.range X.mulVecLin ∧ Module.finrank 𝔽₂ x = i)]
    rw [Nat.card_eq_fintype_card]
    congr 1
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp [condV]))
  have hcardW : (∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ W₁ = m - j
          then (1 : ℝ) else 0))
      = (Nat.card {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂) // condW X j W₁} : ℝ) := by
    rw [Finset.sum_boole]
    rw [← Fintype.card_subtype (fun x : Submodule 𝔽₂ (Fin m → 𝔽₂) =>
      LinearMap.ker X.mulVecLin ≤ x ∧ Module.finrank 𝔽₂ x = m - j)]
    rw [Nat.card_eq_fintype_card]
    congr 1
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun x => by simp [condW]))
  calc (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧
            Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j
          then (1 : ℝ) else 0))
      = ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
          (if V₁ ≤ LinearMap.range X.mulVecLin ∧ Module.finrank 𝔽₂ V₁ = i
            then (1 : ℝ) else 0) *
          (if LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ W₁ = m - j
            then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun V₁ _ => Finset.sum_congr rfl fun W₁ _ => hstep V₁ W₁
    _ = (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂),
          (if V₁ ≤ LinearMap.range X.mulVecLin ∧ Module.finrank 𝔽₂ V₁ = i
            then (1 : ℝ) else 0)) *
        (∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
          (if LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ W₁ = m - j
            then (1 : ℝ) else 0)) := by
        rw [← Finset.sum_mul_sum]
    _ = (Nat.card {V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂) // condV X i V₁} : ℝ) *
        (Nat.card {W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂) // condW X j W₁} : ℝ) := by
        rw [hcardV, hcardW]
    _ = (Commons.Combinatorics.QBinomial.gb X.rank i : ℝ) *
        (Commons.Combinatorics.QBinomial.gb X.rank j : ℝ) := by
        rw [card_condV, card_condW X j hj]

/-- Sums over `range (N+1)` of a function vanishing above `k` reduce to `range (k+1)`. -/
lemma sum_range_eq_of_vanishing {f : ℕ → ℝ} {k N : ℕ} (hk : k ≤ N)
    (h : ∀ j, k < j → j ≤ N → f j = 0) :
    (∑ j ∈ Finset.range (N + 1), f j) = ∑ j ∈ Finset.range (k + 1), f j := by
  refine (Finset.sum_subset (s₁ := Finset.range (k + 1)) (s₂ := Finset.range (N + 1))
    (Finset.range_subset_range.mpr (by omega)) ?_).symm
  intro j hj hjn
  have hjN : j ≤ N := by
    simp only [Finset.mem_range] at hj
    omega
  have hkj : k < j := by
    simp only [Finset.mem_range] at hjn
    omega
  exact h j hkj hjN

/-- **The arithmetic bound of `lem:F2`**: the weighted count of the pairs `(i,j)` is at most `1`. -/
lemma sum_b_le_one {m n : ℕ} (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂) (hX : X.rank ≤ d) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
      (if i = 0 ∧ j = 0 then 0 else
        (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
          (if (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) then (1 : ℝ) else 0)) *
        ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2))) ≤ 1 := by
  classical
  have hstep : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        (if i = 0 ∧ j = 0 then 0 else
          (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
            (if (V₁ ≤ LinearMap.range X.mulVecLin ∧ LinearMap.ker X.mulVecLin ≤ W₁ ∧ Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j) then (1 : ℝ) else 0)) *
          ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2)))
      = (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        (if i = 0 ∧ j = 0 then 0 else
          (Commons.Combinatorics.QBinomial.gb X.rank i : ℝ) *
            (Commons.Combinatorics.QBinomial.gb X.rank j : ℝ) *
          ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2))) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    have hjm : j ≤ m := by
      simp only [Finset.mem_range] at hj
      omega
    have hinner := card_cond_eq X i j hjm
    by_cases hcase : i = 0 ∧ j = 0
    · rw [if_pos hcase, if_pos hcase]
    · rw [if_neg hcase, if_neg hcase, hinner]
  rw [hstep]
  have hrn : X.rank ≤ n := Matrix.rank_le_height X
  have hrm : X.rank ≤ m := Matrix.rank_le_width X
  have hsubi : Finset.range (X.rank + 1) ⊆ Finset.range (n + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have hzeroi : ∀ i ∈ Finset.range (n + 1), i ∉ Finset.range (X.rank + 1) →
      (∑ j ∈ Finset.range (m + 1),
        (if i = 0 ∧ j = 0 then 0 else
          (Commons.Combinatorics.QBinomial.gb X.rank i : ℝ) *
            (Commons.Combinatorics.QBinomial.gb X.rank j : ℝ) *
          ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2))) = 0 := by
    intro i hi hin
    have hlt : X.rank < i := by
      simp only [Finset.mem_range] at hi hin
      omega
    have hg : (Commons.Combinatorics.QBinomial.gb X.rank i : ℝ) = 0 := by
      rw [Commons.Combinatorics.QBinomial.gb_eq_zero_of_lt X.rank i hlt]
      norm_num
    apply Finset.sum_eq_zero
    intro j hj
    have hne : ¬ (i = 0 ∧ j = 0) := by
      intro hc; omega
    rw [if_neg hne, hg]
    ring
  have hzeroj : ∀ (i : ℕ) (j : ℕ), j ∈ Finset.range (m + 1) →
      j ∉ Finset.range (X.rank + 1) →
      (if i = 0 ∧ j = 0 then 0 else
          (Commons.Combinatorics.QBinomial.gb X.rank i : ℝ) *
            (Commons.Combinatorics.QBinomial.gb X.rank j : ℝ) *
          ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2)) = 0 := by
    intro i j hj hjn
    have hlt : X.rank < j := by
      simp only [Finset.mem_range] at hj hjn
      omega
    have hg : (Commons.Combinatorics.QBinomial.gb X.rank j : ℝ) = 0 := by
      rw [Commons.Combinatorics.QBinomial.gb_eq_zero_of_lt X.rank j hlt]
      norm_num
    have hne : ¬ (i = 0 ∧ j = 0) := by
      intro hc; omega
    rw [if_neg hne, hg]
    ring
  refine le_trans (le_of_eq ?_) (le_of_lt (Commons.Combinatorics.QBinomial.gb_pair_pow_sum_lt_one d X.rank hX))
  refine (Finset.sum_subset hsubi hzeroi).symm.trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_subset (s₁ := Finset.range (X.rank + 1)) (s₂ := Finset.range (m + 1))
    (f := fun j => if i = 0 ∧ j = 0 then 0 else
      (Commons.Combinatorics.QBinomial.gb X.rank i : ℝ) *
        (Commons.Combinatorics.QBinomial.gb X.rank j : ℝ) *
      ((2 : ℝ) ^ (7 * d * (i + j)))⁻¹ * (2 : ℝ) ^ (4 * i ^ 2 + 4 * j ^ 2))
    (Finset.range_subset_range.mpr (by omega)) (fun j hj hjn => hzeroj i j hj hjn)]

end

end Submission.Grassmann
