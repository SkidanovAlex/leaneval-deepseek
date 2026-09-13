import Submission.Grassmann.Laplacian

/-!
# The dictators of `L(V,W)`: rank-one characters

The "dictators" on the shortcode space `L(V,W) = L(𝔽₂ⁿ, 𝔽₂ᵐ)` are the indicators
`1_{Av=w}` (`v ∈ V`, `w ∈ W`) and `1_{A*φ=ψ}`; each is a **degree-`1`** function
(arXiv:2209.04243, Proposition 3.2).

Here we prove this for the first family.  The key point is the elementary identity

  `∑_{φ} mchar (v ⊗ φ) A = 2^m · 1_{A·v = 0}`,

where `v ⊗ φ` is the rank-one matrix `(i,j) ↦ v i * φ j`.  Since every `v ⊗ φ` has rank
at most `1`, the indicator `1_{A·v=0}` lies in the level-`≤1` span, i.e. has degree `≤ 1`;
shifting gives the same for `1_{A·v=w}`.
-/

open Matrix Finset BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

/-! ## Rank-one matrices -/

/-- The rank-one matrix `v ⊗ φ : L(𝔽₂ᵐ, 𝔽₂ⁿ)`, `(i,j) ↦ v i * φ j`. -/
def rankOne {m n : ℕ} (v : Fin n → ZMod 2) (φ : Fin m → ZMod 2) :
    Matrix (Fin n) (Fin m) (ZMod 2) :=
  fun i j => v i * φ j

lemma rankOne_mulVec {m n : ℕ} (v : Fin n → ZMod 2) (φ : Fin m → ZMod 2)
    (w : Fin m → ZMod 2) :
    (rankOne v φ).mulVec w = (∑ j : Fin m, φ j * w j) • v := by
  funext i
  simp only [Matrix.mulVec, dotProduct, rankOne, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma rank_rankOne_le_one {m n : ℕ} (v : Fin n → ZMod 2) (φ : Fin m → ZMod 2) :
    (rankOne v φ).rank ≤ 1 := by
  rw [Matrix.rank]
  have hle : LinearMap.range (rankOne v φ).mulVecLin ≤
      Submodule.span (ZMod 2) ({v} : Set (Fin n → ZMod 2)) := by
    rintro _ ⟨w, rfl⟩
    show (rankOne v φ).mulVec w ∈ _
    rw [rankOne_mulVec]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  refine le_trans (Submodule.finrank_mono hle) ?_
  refine le_trans (finrank_span_le_card _) ?_
  simp

/-- The trace formula for rank-one matrices. -/
lemma trace_rankOne_mul {m n : ℕ} (v : Fin n → ZMod 2) (φ : Fin m → ZMod 2)
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Matrix.trace (rankOne v φ * A) = ∑ j : Fin m, φ j * (A.mulVec v) j := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, rankOne, Matrix.mulVec,
    dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma mchar_rankOne {m n : ℕ} (v : Fin n → ZMod 2) (φ : Fin m → ZMod 2)
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    mchar (rankOne v φ) A = ZMod.stdAddChar (∑ j : Fin m, φ j * (A.mulVec v) j) := by
  rw [mchar_eq_trace, trace_rankOne_mul]

/-- **The dictator identity**: `∑_φ mchar (v ⊗ φ) A = 2^m · 1_{A·v = 0}`. -/
theorem sum_mchar_rankOne {m n : ℕ} (v : Fin n → ZMod 2)
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (∑ φ : Fin m → ZMod 2, mchar (rankOne v φ) A) =
      (2 : ℂ) ^ m * (if A.mulVec v = 0 then 1 else 0) := by
  have hstep : ∀ φ : Fin m → ZMod 2,
      mchar (rankOne v φ) A = ∏ j : Fin m, ZMod.stdAddChar (φ j * (A.mulVec v) j) := by
    intro φ
    rw [mchar_rankOne, stdAddChar_sum]
  rw [Finset.sum_congr rfl (fun φ _ => hstep φ),
    sum_prod_pi (fun j (a : ZMod 2) => ZMod.stdAddChar (a * (A.mulVec v) j))]
  have h1 : ∀ j : Fin m, (∑ a : ZMod 2, ZMod.stdAddChar (a * (A.mulVec v) j)) =
      (if (A.mulVec v) j = 0 then (2 : ℂ) else 0) := by
    intro j
    rw [← sum_stdAddChar_mul_two ((A.mulVec v) j)]
  rw [Finset.prod_congr rfl (fun j _ => h1 j),
    prod_ite_zero (2 : ℂ) (fun j : Fin m => (A.mulVec v) j), Fintype.card_fin]
  have hfun : (fun j : Fin m => (A.mulVec v) j) = A.mulVec v := rfl
  rw [hfun]
  by_cases hA : A.mulVec v = 0
  · simp [hA]
  · simp [hA]

/-- The indicator `1_{A·v = 0}` has degree at most `1`. -/
theorem degLe_indicator_mulVec_zero {m n : ℕ} (v : Fin n → ZMod 2) :
    DegLe 1 (fun A : Matrix (Fin m) (Fin n) (ZMod 2) =>
      if A.mulVec v = 0 then (1 : ℂ) else 0) := by
  have hmem : ((2 : ℂ) ^ m • (fun A : Matrix (Fin m) (Fin n) (ZMod 2) =>
      if A.mulVec v = 0 then (1 : ℂ) else 0)) ∈ charLe (m := m) (n := n) 1 := by
    have heq : ((2 : ℂ) ^ m • (fun A : Matrix (Fin m) (Fin n) (ZMod 2) =>
        if A.mulVec v = 0 then (1 : ℂ) else 0)) =
        ∑ φ : Fin m → ZMod 2, (mchar (rankOne v φ) : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) := by
      funext A
      rw [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, sum_mchar_rankOne]
    rw [heq]
    refine Submodule.sum_mem _ fun φ _ => ?_
    exact mchar_mem_charLe (rank_rankOne_le_one v φ)
  rw [degLe_iff_mem_charLe]
  have h2 : ((2 : ℂ) ^ m)⁻¹ • ((2 : ℂ) ^ m • (fun A : Matrix (Fin m) (Fin n) (ZMod 2) =>
      if A.mulVec v = 0 then (1 : ℂ) else 0)) ∈ charLe (m := m) (n := n) 1 :=
    Submodule.smul_mem _ _ hmem
  rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)), one_smul] at h2

/-- The indicator `1_{A·v = w}` has degree at most `1`. -/
theorem degLe_indicator_mulVec_eq {m n : ℕ} {v : Fin n → ZMod 2} (hv : v ≠ 0)
    (w : Fin m → ZMod 2) :
    DegLe 1 (fun A : Matrix (Fin m) (Fin n) (ZMod 2) =>
      if A.mulVec v = w then (1 : ℂ) else 0) := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hv (funext h)
  have hvi : v i = 1 := by
    have h1 : (v i).val ≠ 0 := fun h0 => hi ((ZMod.val_eq_zero _).mp h0)
    have h2 : (v i).val < 2 := ZMod.val_lt _
    have h3 : (v i).val = 1 := by omega
    exact ZMod.val_injective 2 h3
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin m) (Fin n) (ZMod 2), B.mulVec v = w := by
    refine ⟨fun j l => if l = i then w j else 0, ?_⟩
    funext j
    show (∑ l : Fin n, (if l = i then w j else 0) * v l) = w j
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, hvi, mul_one]
    · intro l _ hl; rw [if_neg hl, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hshift := degLe_shift B (degLe_indicator_mulVec_zero (m := m) (n := n) v)
  have heq : (fun A : Matrix (Fin m) (Fin n) (ZMod 2) => if A.mulVec v = w then (1 : ℂ) else 0) =
      shift B (fun A : Matrix (Fin m) (Fin n) (ZMod 2) =>
        if A.mulVec v = 0 then (1 : ℂ) else 0) := by
    funext A
    rw [shift]
    by_cases h : A.mulVec v = w
    · have hz : (A + B).mulVec v = 0 := by
        rw [Matrix.add_mulVec A B v, hB, h]
        exact funext fun j => CharTwo.add_self_eq_zero (w j)
      rw [if_pos h, if_pos hz]
    · have hne : (A + B).mulVec v ≠ 0 := by
        intro hh
        rw [Matrix.add_mulVec A B v, hB] at hh
        apply h
        have hww : w + w = (0 : Fin m → ZMod 2) :=
          funext fun j => CharTwo.add_self_eq_zero (w j)
        have hkey : A.mulVec v + (w + w) = (A.mulVec v + w) + w := (add_assoc _ _ _).symm
        rw [hww, add_zero] at hkey
        rw [hh, zero_add] at hkey
        exact hkey
      rw [if_neg h, if_neg hne]
  rw [heq]; exact hshift

end

end Submission.Grassmann
