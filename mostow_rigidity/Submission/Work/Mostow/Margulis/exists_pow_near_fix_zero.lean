import Mathlib
import Submission.Work.Mostow.margulisPairDefs
import Submission.Work.Mostow.abs_mat_le_tpart_actO
import Submission.Work.Mostow.poSheet
import Submission.Work.Mostow.Margulis.exists_pair_dist_le_bdd

/-!
# A bounded power of a matrix fixing the base point is near the identity

Let `X ∈ O(n,1)` fix the base point `0` of the chart (i.e. `actO X 0 = 0`).  Then `X` lies in
the stabiliser of `0`, which is (essentially) the compact group `O(n)`: for every `A` with
`actO A 0 = 0` the entries of `mat A` are bounded by `tpart (actO A 0) = 1`
(`Work.Mostow.abs_mat_le_tpart_actO`) and, by `mat_inv_entry`, so are the entries of the
inverse.

Hence the powers `X ^ k` all live in the entrywise unit cube, a compact — in particular
totally bounded — subset of the matrix space.  Pigeonholing (`exists_uniform_pair_dist_le_bdd`,
which furnishes the bound on the second index *before* the sequence) two powers
`X ^ i`, `X ^ j` (`i < j`) are `δ`-close entrywise for `δ = ε / (n+1)`, and since

  `mat (X ^ (j - i)) = mat (X ^ j) * (mat (X ^ i))⁻¹`

has entries bounded by `1`, the difference `mat (X ^ (j-i)) - 1 = (mat (X^j) - mat (X^i)) *
(mat (X^i))⁻¹` has entries bounded by `(n+1) * δ = ε`.  So `X ^ (j-i)` is entrywise `ε`-near
the identity, with `j - i` bounded independently of `X`.  This is the compactness step of the
Margulis lemma used by the `PO(n,1)` rigidity proof.
-/

namespace Work.Mostow.Margulis

open Submission.Mostow

/-- The entrywise unit cube in the space of `(n+1) × (n+1)` matrices is totally bounded. -/
theorem totallyBounded_entryCube (n : ℕ) :
    TotallyBounded {M : (Fin n ⊕ Fin 1) → (Fin n ⊕ Fin 1) → ℝ | ∀ i j, |M i j| ≤ 1} := by
  have h : IsCompact (Set.univ.pi (fun _ : Fin n ⊕ Fin 1 =>
      Set.univ.pi (fun _ : Fin n ⊕ Fin 1 => Set.Icc (-1 : ℝ) 1))) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  have hset : {M : (Fin n ⊕ Fin 1) → (Fin n ⊕ Fin 1) → ℝ | ∀ i j, |M i j| ≤ 1}
      = Set.univ.pi (fun _ : Fin n ⊕ Fin 1 =>
          Set.univ.pi (fun _ : Fin n ⊕ Fin 1 => Set.Icc (-1 : ℝ) 1)) := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Icc, abs_le]
  rw [hset]; exact h.totallyBounded

/-- Powers of a matrix fixing the base point of the chart still fix it. -/
theorem actO_pow_fix_zero {n : ℕ} (X : O1 n) (hX : actO X (0 : E n) = 0) (k : ℕ) :
    actO (X ^ k) (0 : E n) = 0 := by
  induction k with
  | zero => rw [pow_zero, poSheet_actO_one]
  | succ m ih => rw [pow_succ, poSheet_actO_mul, hX, ih]

/-- Every entry of every power of a matrix fixing the base point is bounded by `1`. -/
theorem abs_mat_pow_le_one {n : ℕ} (X : O1 n) (hX : actO X (0 : E n) = 0) (k : ℕ)
    (a b : Fin n ⊕ Fin 1) : |mat (X ^ k) a b| ≤ 1 := by
  have h := abs_mat_le_tpart_actO (X ^ k) a b
  rw [actO_pow_fix_zero X hX k] at h
  simpa [tpart] using h

/-- **Main lemma.**  For every `ε > 0` there is a bound `N`, depending only on `n` and `ε`,
such that every `X ∈ O(n,1)` fixing the base point of the chart has a power `X ^ j` with
`0 < j ≤ N` that is entrywise `ε`-near the identity. -/
theorem exists_pow_near_fix_zero (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ X : Submission.Mostow.O1 n,
      Submission.Mostow.actO X (0 : Submission.Mostow.E n) = 0 →
        ∃ j : ℕ, 0 < j ∧ j ≤ N ∧ Work.Mostow.Near1 (X ^ j) ε := by
  have hmsz : (0 : ℝ) < msz n := lt_of_lt_of_le zero_lt_one (one_le_msz n)
  have hδpos : 0 < ε / msz n := div_pos hε hmsz
  obtain ⟨N₀, hunif⟩ :=
    exists_uniform_pair_dist_le_bdd (totallyBounded_entryCube n) hδpos
  refine ⟨N₀ + 1, Nat.succ_pos _, ?_⟩
  intro X hX
  have hbound : ∀ k : ℕ, ∀ a b : Fin n ⊕ Fin 1, |mat (X ^ k) a b| ≤ 1 :=
    fun k => abs_mat_pow_le_one X hX k
  obtain ⟨i, j, hij, hjle, hdist⟩ :=
    hunif (fun k => fun a b => mat (X ^ k) a b) (fun k => hbound k)
  refine ⟨j - i, by omega, by omega, ?_⟩
  -- two close powers give a small entrywise bound on `mat (X ^ i) - mat (X ^ j)`
  have hclose : ∀ a b : Fin n ⊕ Fin 1, |mat (X ^ i) a b - mat (X ^ j) a b| ≤ ε / msz n := by
    intro a b
    have h1 : ∀ c : Fin n ⊕ Fin 1, dist (mat (X ^ i) c) (mat (X ^ j) c) ≤ ε / msz n :=
      (dist_pi_le_iff (le_of_lt hδpos)).mp hdist
    have h3 : dist (mat (X ^ i) a b) (mat (X ^ j) a b) ≤ ε / msz n :=
      (dist_pi_le_iff (le_of_lt hδpos)).mp (h1 a) b
    rwa [Real.dist_eq] at h3
  intro a b
  -- factorisation `mat (X ^ (j-i)) = mat (X ^ j) * mat ((X ^ i)⁻¹)`
  have hfac : mat (X ^ (j - i)) = mat (X ^ j) * mat ((X ^ i)⁻¹) := by
    have hu : X ^ (j - i) * X ^ i = X ^ j := by
      rw [← pow_add, Nat.sub_add_cancel (le_of_lt hij)]
    have hu2 : X ^ (j - i) = X ^ j * (X ^ i)⁻¹ := by
      rw [← hu, mul_assoc, mul_inv_cancel, mul_one]
    rw [hu2, mat_mul_coe]
  have hBB : mat (X ^ i) * mat ((X ^ i)⁻¹) = mat (1 : O1 n) := by
    rw [← mat_mul_coe, mul_inv_cancel]
  have h1 : (mat (X ^ i) * mat ((X ^ i)⁻¹)) a b = dE n a b := by
    rw [hBB, mat_one_entry]
  have hkey : mat (X ^ (j - i)) a b - dE n a b
      = ∑ c : Fin n ⊕ Fin 1, (mat (X ^ j) a c - mat (X ^ i) a c) * mat ((X ^ i)⁻¹) c b := by
    have hdiff : (mat (X ^ j) * mat ((X ^ i)⁻¹)) a b - (mat (X ^ i) * mat ((X ^ i)⁻¹)) a b
        = ∑ c : Fin n ⊕ Fin 1,
            (mat (X ^ j) a c - mat (X ^ i) a c) * mat ((X ^ i)⁻¹) c b := by
      rw [Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [hfac, ← h1]; exact hdiff
  rw [hkey]
  have hinv : ∀ c : Fin n ⊕ Fin 1, |mat ((X ^ i)⁻¹) c b| ≤ 1 := by
    intro c
    rw [mat_inv_entry, abs_mul, abs_mul, abs_pmSign, abs_pmSign, one_mul, one_mul]
    exact hbound i b c
  have hcl : ∀ c : Fin n ⊕ Fin 1, |mat (X ^ j) a c - mat (X ^ i) a c| ≤ ε / msz n := fun c =>
    le_trans (le_of_eq (abs_sub_comm _ _)) (hclose a c)
  calc |∑ c : Fin n ⊕ Fin 1, (mat (X ^ j) a c - mat (X ^ i) a c) * mat ((X ^ i)⁻¹) c b|
      ≤ ∑ c : Fin n ⊕ Fin 1,
          |(mat (X ^ j) a c - mat (X ^ i) a c) * mat ((X ^ i)⁻¹) c b| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c : Fin n ⊕ Fin 1, (ε / msz n) * 1 := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hcl c) (hinv c) (abs_nonneg _) (le_of_lt hδpos)
    _ = ε := by
        rw [Finset.sum_congr rfl (fun c _ => mul_one _), sum_const_sum, ← mul_div_assoc,
          mul_div_cancel_left₀ _ (ne_of_gt hmsz)]

end Work.Mostow.Margulis
