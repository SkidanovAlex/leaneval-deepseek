import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The diagonal formal multilinear series of a doubly indexed sequence

Given `a : ℕ → ℕ → ℂ` whose entries satisfy `‖a m n‖ * r ^ (m + n) ≤ M`, we build a formal
multilinear series `p` on `ℂ × ℂ` whose `N`-th term is the "diagonal" polynomial

`p N (fun _ => y) = ∑_{k ≤ N} a k (N - k) * y.1 ^ k * y.2 ^ (N - k)`

and whose operator norms obey `‖p N‖ * (r / 2) ^ N ≤ M`.  This is the multilinear-series form of a
power series in two variables that is holomorphic on the polydisc of radius `r / 2`.
-/

namespace Work.TMComp.MAnalytic

open Finset

/-- The `N`-th term of the diagonal formal multilinear series attached to `a`: it sends a tuple
`v : Fin N → ℂ × ℂ` to `∑_{k ≤ N} a k (N - k) * ∏_{i < k} (v i).1 * ∏_{i ≥ k} (v i).2`. -/
noncomputable def diagCM (a : ℕ → ℕ → ℂ) (N : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin N => ℂ × ℂ) ℂ :=
  ∑ k ∈ Finset.range (N + 1),
    a k (N - k) • (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin N) ℂ).compContinuousLinearMap
      (fun i : Fin N => if (i : ℕ) < k then (ContinuousLinearMap.fst ℂ ℂ ℂ)
        else (ContinuousLinearMap.snd ℂ ℂ ℂ))

/-- Evaluation of `diagCM` on an arbitrary tuple. -/
lemma diagCM_apply (a : ℕ → ℕ → ℂ) (N : ℕ) (v : Fin N → ℂ × ℂ) :
    diagCM a N v = ∑ k ∈ Finset.range (N + 1),
      a k (N - k) * ∏ i : Fin N, (if (i : ℕ) < k then (v i).1 else (v i).2) := by
  simp only [diagCM, _root_.sum_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : (i : ℕ) < k <;> simp [h]

/-- Each individual factor of the diagonal series has operator norm at most `1`. -/
lemma norm_factor_le (N k : ℕ) :
    ‖(ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin N) ℂ).compContinuousLinearMap
      (fun i : Fin N => if (i : ℕ) < k then (ContinuousLinearMap.fst ℂ ℂ ℂ)
        else (ContinuousLinearMap.snd ℂ ℂ ℂ))‖ ≤ 1 := by
  calc ‖(ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin N) ℂ).compContinuousLinearMap
        (fun i : Fin N => if (i : ℕ) < k then (ContinuousLinearMap.fst ℂ ℂ ℂ)
          else (ContinuousLinearMap.snd ℂ ℂ ℂ))‖
      ≤ ‖ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin N) ℂ‖ *
          ∏ i : Fin N, ‖(if (i : ℕ) < k then (ContinuousLinearMap.fst ℂ ℂ ℂ)
            else (ContinuousLinearMap.snd ℂ ℂ ℂ))‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ∏ i : Fin N, ‖(if (i : ℕ) < k then (ContinuousLinearMap.fst ℂ ℂ ℂ)
            else (ContinuousLinearMap.snd ℂ ℂ ℂ))‖ := by
        rw [ContinuousMultilinearMap.norm_mkPiAlgebra, one_mul]
    _ ≤ 1 := by
        apply Finset.prod_le_one₀
        · intro i hi; positivity
        · intro i hi
          by_cases h : (i : ℕ) < k
          · rw [if_pos h]; exact ContinuousLinearMap.norm_fst_le ℂ ℂ ℂ
          · rw [if_neg h]; exact ContinuousLinearMap.norm_snd_le ℂ ℂ ℂ

/-- The operator norm of `diagCM a N` is bounded by the sum of the norms of its coefficients. -/
lemma norm_diagCM_le (a : ℕ → ℕ → ℂ) (N : ℕ) :
    ‖diagCM a N‖ ≤ ∑ k ∈ Finset.range (N + 1), ‖a k (N - k)‖ := by
  rw [diagCM]
  calc ‖∑ k ∈ Finset.range (N + 1),
        a k (N - k) • (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin N) ℂ).compContinuousLinearMap
          (fun i : Fin N => if (i : ℕ) < k then (ContinuousLinearMap.fst ℂ ℂ ℂ)
            else (ContinuousLinearMap.snd ℂ ℂ ℂ))‖
      ≤ ∑ k ∈ Finset.range (N + 1), ‖a k (N - k) •
          (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin N) ℂ).compContinuousLinearMap
          (fun i : Fin N => if (i : ℕ) < k then (ContinuousLinearMap.fst ℂ ℂ ℂ)
            else (ContinuousLinearMap.snd ℂ ℂ ℂ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (N + 1), ‖a k (N - k)‖ := by
        apply Finset.sum_le_sum
        intro k hk
        calc ‖a k (N - k) • (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin N) ℂ).compContinuousLinearMap
              (fun i : Fin N => if (i : ℕ) < k then (ContinuousLinearMap.fst ℂ ℂ ℂ)
                else (ContinuousLinearMap.snd ℂ ℂ ℂ))‖
            ≤ ‖a k (N - k)‖ * ‖(ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin N) ℂ).compContinuousLinearMap
              (fun i : Fin N => if (i : ℕ) < k then (ContinuousLinearMap.fst ℂ ℂ ℂ)
                else (ContinuousLinearMap.snd ℂ ℂ ℂ))‖ :=
              ContinuousMultilinearMap.opNorm_smul_le _ _
          _ ≤ ‖a k (N - k)‖ * 1 := by gcongr; exact norm_factor_le N k
          _ = ‖a k (N - k)‖ := mul_one _

/-- The diagonal evaluation of the product of the chosen coordinates. -/
lemma prod_diag_const (N k : ℕ) (y : ℂ × ℂ) (hk : k ≤ N) :
    ∏ i : Fin N, (if (i : ℕ) < k then y.1 else y.2) = y.1 ^ k * y.2 ^ (N - k) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < k then y.1 else y.2) N]
  conv_lhs => rw [show N = k + (N - k) from (Nat.add_sub_cancel' hk).symm]
  rw [Finset.prod_range_add]
  rw [show (∏ x ∈ Finset.range k, (if x < k then y.1 else y.2)) = ∏ _x ∈ Finset.range k, y.1 from
        Finset.prod_congr rfl (fun x hx => if_pos (Finset.mem_range.mp hx))]
  rw [show (∏ x ∈ Finset.range (N - k), (if k + x < k then y.1 else y.2)) =
        ∏ _x ∈ Finset.range (N - k), y.2 from
        Finset.prod_congr rfl (fun x _ => if_neg (by omega))]
  simp only [Finset.prod_const, Finset.card_range]

/-- The elementary estimate `(∑_{k ≤ N} t k) * (r / 2) ^ N ≤ M` when `t k * r ^ N ≤ M`
for all `k ≤ N`. (Here `N + 1 ≤ 2 ^ N` is used.) -/
lemma diag_arith {M r : ℝ} (hM : 0 ≤ M) (N : ℕ) (t : ℕ → ℝ)
    (ht : ∀ k, k ≤ N → t k * r ^ N ≤ M) :
    (∑ k ∈ Finset.range (N + 1), t k) * (r / 2) ^ N ≤ M := by
  rw [Finset.sum_mul]
  have hterm : ∀ k ∈ Finset.range (N + 1), t k * (r / 2) ^ N ≤ M / 2 ^ N := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp hk
    calc t k * (r / 2) ^ N = t k * r ^ N / 2 ^ N := by rw [div_pow]; ring
      _ ≤ M / 2 ^ N := div_le_div_of_nonneg_right (ht k hkN) (by positivity)
  calc ∑ k ∈ Finset.range (N + 1), t k * (r / 2) ^ N
      ≤ ∑ _k ∈ Finset.range (N + 1), M / 2 ^ N := Finset.sum_le_sum hterm
    _ = (N + 1) * (M / 2 ^ N) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ = M * (N + 1) / 2 ^ N := by ring
    _ ≤ M := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ N)]
        have hle : ((N : ℝ) + 1) ≤ (2 : ℝ) ^ N := by
          exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := N))
        exact mul_le_mul_of_nonneg_left hle hM

theorem formalMultilinearSeries_diagonal (a : ℕ → ℕ → ℂ) {M r : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hb : ∀ m n : ℕ, ‖a m n‖ * r ^ (m + n) ≤ M) :
    ∃ p : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ,
      (∀ (N : ℕ) (y : ℂ × ℂ),
        p N (fun _ : Fin N => y)
          = ∑ k ∈ Finset.range (N + 1), a k (N - k) * y.1 ^ k * y.2 ^ (N - k)) ∧
      (∀ N : ℕ, ‖p N‖ * (r / 2) ^ N ≤ M) := by
  refine ⟨fun N => diagCM a N, ?_, ?_⟩
  · intro N y
    rw [diagCM_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp hk
    rw [prod_diag_const N k y hkN]
    ring
  · intro N
    calc ‖diagCM a N‖ * (r / 2) ^ N
        ≤ (∑ k ∈ Finset.range (N + 1), ‖a k (N - k)‖) * (r / 2) ^ N :=
          mul_le_mul_of_nonneg_right (norm_diagCM_le a N) (by positivity)
      _ ≤ M := diag_arith hM N (fun k => ‖a k (N - k)‖) (fun k hk => by
          have h := hb k (N - k)
          rwa [show k + (N - k) = N from Nat.add_sub_cancel' hk] at h)

end Work.TMComp.MAnalytic
