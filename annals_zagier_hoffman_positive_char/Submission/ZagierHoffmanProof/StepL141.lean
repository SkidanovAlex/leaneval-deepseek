import Submission.ZagierHoffmanProof.StepL140
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L141: ★ `maink_g5_aSide_prefix_drop` — the G5 a-side measure drop (SESSION 259m)

With the two closers from PLAN SESSION 259l applied:
  • `maink_g5_iter_cA_psum_front` ends with `simp` (the `nsmul_eq_mul` step
    introduces the `↑(k−1)` cast);
  • `maink_g5_iter_cA_pad0_at` pins the index val with an explicit `have hval`
    + `Nat.sub_self` (simp cannot see through the index coercion).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The iterate's cA prefix of length k−1 is `(k−1)·q` (the all-q front). -/
lemma maink_g5_iter_cA_psum_front (r : ℕ) (s : Fin r → ℕ+) (k : ℕ)
    (R0 : BinaryRel F) (i₀ : R0.ιA) :
    psum ((RelData.BCqIter F (k - 1) (toData F R0)).cA
        (RelData.iterIdx F (k - 1) (toData F R0) i₀)) (k - 1) =
      (k - 1) * Nat.card F := by
  classical
  change (∑ j ∈ Finset.range (k - 1),
      pad0 ((RelData.BCqIter F (k - 1) (toData F R0)).cA
        (RelData.iterIdx F (k - 1) (toData F R0) i₀)) j) = (k - 1) * Nat.card F
  have hq : ∀ j ∈ Finset.range (k - 1),
      pad0 ((RelData.BCqIter F (k - 1) (toData F R0)).cA
        (RelData.iterIdx F (k - 1) (toData F R0) i₀)) j = Nat.card F :=
    fun j hj => BCqIter_cA_pad0_front F (k - 1) R0 i₀ j (Finset.mem_range.mp hj)
  rw [Finset.sum_congr rfl hq, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_id]

/-- The iterate's k-th entry (index k−1) is the base tuple's head. -/
lemma maink_g5_iter_cA_pad0_at (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k)
    (R0 : BinaryRel F) (i₀ : R0.ιA) :
    pad0 ((RelData.BCqIter F (k - 1) (toData F R0)).cA
        (RelData.iterIdx F (k - 1) (toData F R0) i₀)) (k - 1) =
      ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) := by
  classical
  have hpos : 0 < R0.depA i₀ := R0.hdepA i₀
  have hlt : k - 1 < R0.depA i₀ + (k - 1) := by omega
  have hdep_eq : (RelData.BCqIter F (k - 1) (toData F R0)).depA
      (RelData.iterIdx F (k - 1) (toData F R0) i₀) = R0.depA i₀ + (k - 1) :=
    RelData.BCqIter_depA_at F (k - 1) (toData F R0) i₀
  have hdepQ : k - 1 < (RelData.BCqIter F (k - 1) (toData F R0)).depA
      (RelData.iterIdx F (k - 1) (toData F R0) i₀) := by rw [hdep_eq]; exact hlt
  rw [pad0_of_lt _ hdepQ]
  have hcv := RelData.BCqIter_cA_value F (k - 1) (toData F R0) i₀ ⟨k - 1, hlt⟩
  have hcast : (Fin.cast (RelData.BCqIter_depA_at F (k - 1) (toData F R0) i₀).symm
        ⟨k - 1, hlt⟩) = (⟨k - 1, hdepQ⟩ : Fin ((RelData.BCqIter F (k - 1) (toData F R0)).depA
          (RelData.iterIdx F (k - 1) (toData F R0) i₀))) := by
    apply Fin.ext
    simp
  rw [← hcast, hcv]
  rw [dif_neg (by simp only [Fin.val_mk]; omega)]
  have hb0 : 0 < (toData F R0).depA i₀ := R0.hdepA i₀
  have hidx : (⟨(⟨k - 1, hlt⟩ : Fin ((toData F R0).depA i₀ + (k - 1))).val - (k - 1),
        by simp only [Fin.val_mk]; omega⟩ : Fin ((toData F R0).depA i₀)) = ⟨0, hb0⟩ := by
    apply Fin.ext
    show (⟨k - 1, hlt⟩ : Fin ((toData F R0).depA i₀ + (k - 1))).val - (k - 1) = 0
    have hval : ((⟨k - 1, hlt⟩ : Fin ((toData F R0).depA i₀ + (k - 1))).val) = k - 1 := rfl
    rw [hval, Nat.sub_self]
  rw [hidx]
  rfl

/-- ★ The G5 a-side measure drop: `psum (D.cA i) k < psum s k`. -/
theorem maink_g5_aSide_prefix_drop (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k)
    (hkr : k ≤ r)
    (hallq : ∀ x : ℕ, x < k - 1 → pad0 s x = Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hhead : ∀ i : R0.ιA, i ≠ u →
      ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ)) :
    let D := RelData.BCqIter F (k - 1) (toData F R0)
    ∀ i : D.ιA, i ≠ RelData.iterIdx F (k - 1) (toData F R0) u →
      psum (D.cA i) k < psum s k := by
  classical
  intro D i hi
  let i₀ : R0.ιA := Eq.mpr (RelData.BCqIter_ιA F (k - 1) (toData F R0)).symm i
  have hiter : RelData.iterIdx F (k - 1) (toData F R0) i₀ = i := by
    dsimp only [RelData.iterIdx, i₀]
    exact eq_mpr_symm_id (RelData.BCqIter_ιA F (k - 1) (toData F R0)) i
  have hfront : psum (D.cA (RelData.iterIdx F (k - 1) (toData F R0) i₀)) (k - 1)
      = (k - 1) * Nat.card F := maink_g5_iter_cA_psum_front F r s k R0 i₀
  have hat : pad0 (D.cA (RelData.iterIdx F (k - 1) (toData F R0) i₀)) (k - 1)
      = ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) :=
    maink_g5_iter_cA_pad0_at F r s k hk1 R0 i₀
  have hsucc := psum_succ (D.cA i) (k - 1)
  have hkk : (k - 1) + 1 = k := by omega
  rw [hkk] at hsucc
  have hmember : psum (D.cA i) k
      = (k - 1) * Nat.card F + ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) := by
    rw [hsucc, ← hiter, hfront, hat]
  have hs : psum s k = (k - 1) * Nat.card F + (s ⟨k - 1, by omega⟩ : ℕ) := by
    have hs1 := psum_succ s (k - 1)
    rw [hkk] at hs1
    rw [hs1, pad0_of_lt s (by omega : k - 1 < r),
      maink_g5_psum_front F r s k hallq]
  rw [hmember, hs]
  have hh := hhead i₀ (by intro hc; exact hi (by rw [← hiter, hc]))
  omega

end ZagierHoffmanPositiveChar
