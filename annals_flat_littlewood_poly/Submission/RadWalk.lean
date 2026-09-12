import Mathlib
import Submission.LMWalk

/-!
The Lovett--Meka walk with Rademacher (sign) steps.

At every step the walk moves by `γ` times a sum of Rademacher multiples of the vectors of an
orthonormal basis of the current free subspace.  All randomness is finitely many signs, so the
probability machinery used later is purely finite.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory

noncomputable section

namespace Submission.Discrepancy

/-- The current free subspace (orthogonal complement of the frozen constraints). -/
def Omod {n : ℕ} {ι : Type*} [Fintype ι] (δ : ℝ) (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ)
    (x : Vec n) : Submodule ℝ (Vec n) :=
  (Wspan v (frozenVars δ x) (frozenRows δ x0 v c x))ᗮ

lemma finrank_Omod_le (n : ℕ) {ι : Type*} [Fintype ι] (δ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (x : Vec n) : Module.finrank ℝ (Omod δ x0 v c x) ≤ n := by
  exact le_trans (Submodule.finrank_le (Omod δ x0 v c x)) (by simp)

/-- An orthonormal basis vector of the free subspace, coerced to `Vec n`. -/
def obasis {n : ℕ} {ι : Type*} [Fintype ι] (δ : ℝ) (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ)
    (x : Vec n) (k : Fin (Module.finrank ℝ (Omod δ x0 v c x))) : Vec n :=
  ((stdOrthonormalBasis ℝ (Omod δ x0 v c x) k : Omod δ x0 v c x) : Vec n)

/-- Norm of a basis vector is one. -/
lemma obasis_norm (n : ℕ) {ι : Type*} [Fintype ι] (δ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (x : Vec n) (k : Fin (Module.finrank ℝ (Omod δ x0 v c x))) :
    ‖obasis δ x0 v c x k‖ = 1 := by
  unfold obasis
  rw [← Submodule.coe_norm]
  exact (stdOrthonormalBasis ℝ (Omod δ x0 v c x)).orthonormal.1 k

/-- Basis vectors are orthogonal. -/
lemma obasis_inner (n : ℕ) {ι : Type*} [Fintype ι] (δ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (x : Vec n) (k l : Fin (Module.finrank ℝ (Omod δ x0 v c x))) :
    ⟪obasis δ x0 v c x k, obasis δ x0 v c x l⟫ = if k = l then 1 else 0 := by
  unfold obasis
  rw [← Submodule.coe_inner]
  let b := stdOrthonormalBasis ℝ (Omod δ x0 v c x)
  have hn : ∀ i, ‖b i‖ = 1 := b.orthonormal.1
  by_cases hkl : k = l
  · subst l
    have hsq : ⟪b k, b k⟫ = ‖b k‖ ^ 2 := by
      simpa using (inner_self_eq_norm_sq (b k) : (inner ℝ (b k) (b k)).re = ‖b k‖ ^ 2)
    rw [hsq, hn k]
    simp
  · rw [if_neg hkl]
    exact b.orthonormal.2 hkl

/-- The step vector chosen from `n` signs. -/
def radVec {n : ℕ} {ι : Type*} [Fintype ι] (δ : ℝ) (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ)
    (x : Vec n) (ε : Fin n → Bool) : Vec n :=
  let d := Module.finrank ℝ (Omod δ x0 v c x)
  ∑ k : Fin d,
    if ε ⟨k.val, by exact Nat.lt_of_lt_of_le k.isLt (finrank_Omod_le n δ x0 v c x)⟩ then
      obasis δ x0 v c x k
    else - obasis δ x0 v c x k

/-- One walk step with signs. -/
def radStep {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ)
    (x : Vec n) (ε : Fin n → Bool) : Vec n :=
  x + γ • radVec δ x0 v c x ε

/-- Trajectory of the sign walk. -/
def rseq {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ)
    (ε : ℕ → Fin n → Bool) : ℕ → Vec n
  | 0 => x0
  | t + 1 => radStep δ γ x0 v c (rseq δ γ x0 v c ε t) (ε t)


/-- Membership of the basis vector in the free subspace. -/
lemma obasis_mem {n : ℕ} {ι : Type*} [Fintype ι] (δ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (x : Vec n) (k : Fin (Module.finrank ℝ (Omod δ x0 v c x))) :
    obasis δ x0 v c x k ∈ Omod δ x0 v c x := by
  unfold obasis
  exact (stdOrthonormalBasis ℝ (Omod δ x0 v c x) k : Omod δ x0 v c x).property

/-- The signed summand stays in the free subspace. -/
lemma radVec_mem {n : ℕ} {ι : Type*} [Fintype ι] (δ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (x : Vec n) (ε : Fin n → Bool) : radVec δ x0 v c x ε ∈ Omod δ x0 v c x := by
  unfold radVec
  apply Submodule.sum_mem
  intro k hk
  by_cases hε : ε ⟨k.val, by exact Nat.lt_of_lt_of_le k.isLt (finrank_Omod_le n δ x0 v c x)⟩
  · simpa [hε] using obasis_mem δ x0 v c x k
  · rw [if_neg hε]
    simpa using (Submodule.neg_mem (Omod δ x0 v c x) (obasis_mem δ x0 v c x k))

/-- Coordinate of a frozen variable is untouched by the step. -/
lemma radVec_coord_zero {n : ℕ} {ι : Type*} [Fintype ι] (δ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (x : Vec n) (ε : Fin n → Bool) {i : Fin n} (hi : i ∈ frozenVars δ x) :
    (radVec δ x0 v c x ε) i = 0 := by
  have hmem := radVec_mem δ x0 v c x ε
  have hb : basis n i ∈ Wspan v (frozenVars δ x) (frozenRows δ x0 v c x) := by
    refine Submodule.subset_span (by
      left
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  have horth : ⟪basis n i, radVec δ x0 v c x ε⟫ = 0 :=
    ((Submodule.mem_orthogonal (K := Wspan v (frozenVars δ x) (frozenRows δ x0 v c x))
      (radVec δ x0 v c x ε)).1 hmem) (basis n i) hb
  exact (vin_basis n i (radVec δ x0 v c x ε)).symm.trans (by simpa [vin] using horth)

/-- Frozen rows are untouched. -/
lemma radVec_row_zero {n : ℕ} {ι : Type*} [Fintype ι] (δ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (x : Vec n) (ε : Fin n → Bool) {j : ι} (hj : j ∈ frozenRows δ x0 v c x) :
    vin (radVec δ x0 v c x ε) (v j) = 0 := by
  have hmem := radVec_mem δ x0 v c x ε
  have hb : v j ∈ Wspan v (frozenVars δ x) (frozenRows δ x0 v c x) := by
    refine Submodule.subset_span (by
      right
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
  have horth : ⟪v j, radVec δ x0 v c x ε⟫ = 0 :=
    ((Submodule.mem_orthogonal (K := Wspan v (frozenVars δ x) (frozenRows δ x0 v c x))
      (radVec δ x0 v c x ε)).1 hmem) (v j) hb
  have hc := real_inner_comm (x := radVec δ x0 v c x ε) (y := v j)
  simpa [vin] using hc.symm.trans horth

lemma rseq_succ {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (ε : ℕ → Fin n → Bool) (t : ℕ) :
    rseq δ γ x0 v c ε (t + 1) = rseq δ γ x0 v c ε t + γ • radVec δ x0 v c (rseq δ γ x0 v c ε t) (ε t) := rfl

/-- A frozen variable stays frozen under `radStep`. -/
lemma frozenVars_mono_rad {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (ε : ℕ → Fin n → Bool) (t : ℕ) : frozenVars δ (rseq δ γ x0 v c ε t) ⊆
    frozenVars δ (rseq δ γ x0 v c ε (t + 1)) := by
  intro i hi
  have hstep : (rseq δ γ x0 v c ε (t + 1)) i = (rseq δ γ x0 v c ε t) i := by
    rw [rseq_succ]
    have hz : (radVec δ x0 v c (rseq δ γ x0 v c ε t) (ε t)) i = 0 :=
      radVec_coord_zero δ x0 v c (rseq δ γ x0 v c ε t) (ε t) hi
    simp [hz]
  unfold frozenVars at hi ⊢
  simp only [Finset.mem_univ, Finset.mem_filter, true_and] at hi ⊢
  rw [hstep]
  exact hi

/-- A frozen row stays frozen under `radStep`. -/
lemma frozenRows_mono_rad {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (ε : ℕ → Fin n → Bool) (t : ℕ) : frozenRows δ x0 v c (rseq δ γ x0 v c ε t) ⊆
    frozenRows δ x0 v c (rseq δ γ x0 v c ε (t + 1)) := by
  intro j hj
  have hz : vin (radVec δ x0 v c (rseq δ γ x0 v c ε t) (ε t)) (v j) = 0 :=
    radVec_row_zero δ x0 v c (rseq δ γ x0 v c ε t) (ε t) hj
  have hx : vin (rseq δ γ x0 v c ε (t + 1) - x0) (v j) =
      vin (rseq δ γ x0 v c ε t - x0) (v j) := by
    rw [rseq_succ]
    have hbil : vin (rseq δ γ x0 v c ε t + γ • radVec δ x0 v c (rseq δ γ x0 v c ε t) (ε t) - x0) (v j)
        = vin (rseq δ γ x0 v c ε t - x0) (v j) + γ * vin (radVec δ x0 v c (rseq δ γ x0 v c ε t) (ε t)) (v j) := by
      simp [vin, inner_add_left, inner_smul_left, inner_sub_left, inner_add_right]
      ring
    rw [hbil, hz, mul_zero, add_zero]
  unfold frozenRows at hj ⊢
  simp only [Finset.mem_univ, Finset.mem_filter, true_and] at hj ⊢
  rw [hx]
  exact hj

/-- Frozen sets grow with time. -/
lemma frozenVars_subset_le_rad {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (ε : ℕ → Fin n → Bool) {s t : ℕ} (hst : s ≤ t) :
    frozenVars δ (rseq δ γ x0 v c ε s) ⊆ frozenVars δ (rseq δ γ x0 v c ε t) := by
  refine Nat.le_induction ?_ ?_ t hst
  · intro x hx; exact hx
  · intro t hst ih i hi
    exact frozenVars_mono_rad δ γ x0 v c ε t (ih hi)

lemma frozenRows_subset_le_rad {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (ε : ℕ → Fin n → Bool) {s t : ℕ} (hst : s ≤ t) :
    frozenRows δ x0 v c (rseq δ γ x0 v c ε s) ⊆ frozenRows δ x0 v c (rseq δ γ x0 v c ε t) := by
  refine Nat.le_induction ?_ ?_ t hst
  · intro x hx; exact hx
  · intro t hst ih i hi
    exact frozenRows_mono_rad δ γ x0 v c ε t (ih hi)


end Discrepancy

end Submission
