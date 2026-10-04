import Mathlib
import Submission.Work.Diff.STE.flat.TowerDefs
import Submission.Work.Diff.STE.summable_wt_zpow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Rapid coefficient decay gives a uniform weighted `ℓ²` bound

`Work.Diff.STE.flat.CSq_le_of_decay`: if the coefficient family `c t k a b` decays faster than
*every* polynomial in the weight `⟨k⟩² = wt k`, uniformly in `t ∈ [0, τ)`, in the frequency `k`
and in the matrix indices `a b`, then the weighted `ℓ²` mass

`CSq N (fun k => c t k a b) = ∑_k ⟨k⟩^{2N} ‖c t k a b‖²`

is bounded uniformly in `t`, `a` and `b`.

The proof is the elementary one.  Fix a decay order `Mdec` with `N ≤ Mdec` (in the application
`Mdec = N + n + 1`, so that `⟨k⟩^{-Mdec}` is summable on `ℤⁿ`, see
`Work.Diff.STE.summable_wt_zpow`).  The decay hypothesis gives `‖c t k a b‖ ≤ C ⟨k⟩^{-2Mdec}`,
hence

`⟨k⟩^{2N} ‖c t k a b‖² ≤ C² ⟨k⟩^{-2Mdec} / ⟨k⟩^{2(Mdec-N)} · ⟨k⟩^{2N}·… ` — concretely
`⟨k⟩^{2N} ‖c t k a b‖² ≤ C² ⟨k⟩^{-2Mdec}` as soon as `N ≤ Mdec`,

and summing the summable majorant `C² ⟨k⟩^{-2Mdec}` gives the uniform bound `C² ∑_k ⟨k⟩^{-2Mdec}`.
-/

namespace Work.Diff.STE.flat

open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- **Summability of the dual weight `⟨k⟩^{-s}` on the lattice `ℤⁿ`**: for `n < 2s` the family
`k ↦ (⟨k⟩²)^{-s}` is summable.  (This is `Work.Diff.STE.summable_wt_zpow` rewritten with a natural
power.) -/
lemma summable_wt_inv' {n s : ℕ} (hs : n < 2 * s) :
    Summable (fun k : Fin n → ℤ => ((Work.Diff.STE.wt k) ^ s)⁻¹) :=
  ((Work.Diff.STE.summable_wt_zpow (ι := Fin n) s (by rwa [Fintype.card_fin])).congr
    fun k => by simp [zpow_neg])

/-- **Pointwise form of the decay-to-`ℓ²` estimate.**  If `‖γ k‖ ⟨k⟩^{Mdec} ≤ C` for every `k` and
`s ≤ Mdec`, then `⟨k⟩^{2s} ‖γ k‖² ≤ C² ⟨k⟩^{-2Mdec}`.

(This is the single-term inequality behind `Work.Diff.STE.flat.summable_weighted_of_decay`: the
factor `⟨k⟩^{2s} / ⟨k⟩^{4Mdec}` is at most `⟨k⟩^{-2Mdec}` because `⟨k⟩² ≥ 1`.) -/
lemma wt_pow_mul_norm_sq_le {s Mdec : ℕ} (hNM : s ≤ Mdec) {C : ℝ}
    {γ : (Fin n → ℤ) → ℂ} (h : ∀ k : Fin n → ℤ, ‖γ k‖ * (Work.Diff.STE.wt k) ^ Mdec ≤ C)
    (k : Fin n → ℤ) :
    (Work.Diff.STE.wt k) ^ s * ‖γ k‖ ^ 2 ≤ C ^ 2 * ((Work.Diff.STE.wt k) ^ Mdec)⁻¹ := by
  have hx : (0 : ℝ) < (Work.Diff.STE.wt k) ^ Mdec := pow_pos (Work.Diff.STE.wt_pos k) Mdec
  have hle : ‖γ k‖ ≤ C * ((Work.Diff.STE.wt k) ^ Mdec)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hx]
    exact h k
  have hxs : (Work.Diff.STE.wt k) ^ s ≤ (Work.Diff.STE.wt k) ^ Mdec :=
    pow_le_pow_right₀ (Work.Diff.STE.wt_one_le k) hNM
  have hkey : (Work.Diff.STE.wt k) ^ s * (((Work.Diff.STE.wt k) ^ Mdec)⁻¹) ^ 2
      ≤ ((Work.Diff.STE.wt k) ^ Mdec)⁻¹ := by
    have h2 : (Work.Diff.STE.wt k) ^ Mdec * (((Work.Diff.STE.wt k) ^ Mdec)⁻¹) ^ 2
        = ((Work.Diff.STE.wt k) ^ Mdec)⁻¹ := by
      rw [pow_two, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hx), one_mul]
    calc (Work.Diff.STE.wt k) ^ s * (((Work.Diff.STE.wt k) ^ Mdec)⁻¹) ^ 2
        = (Work.Diff.STE.wt k) ^ s * (((Work.Diff.STE.wt k) ^ Mdec) ^ 2)⁻¹ := by rw [inv_pow]
      _ ≤ (Work.Diff.STE.wt k) ^ Mdec * (((Work.Diff.STE.wt k) ^ Mdec) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hxs (inv_nonneg.mpr (by positivity))
      _ = (Work.Diff.STE.wt k) ^ Mdec * (((Work.Diff.STE.wt k) ^ Mdec)⁻¹) ^ 2 := by
          rw [inv_pow]
      _ = ((Work.Diff.STE.wt k) ^ Mdec)⁻¹ := h2
  calc (Work.Diff.STE.wt k) ^ s * ‖γ k‖ ^ 2
      ≤ (Work.Diff.STE.wt k) ^ s * (C * ((Work.Diff.STE.wt k) ^ Mdec)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hle 2)
          (pow_nonneg (Work.Diff.STE.wt_pos k).le s)
    _ = C ^ 2 * ((Work.Diff.STE.wt k) ^ s * (((Work.Diff.STE.wt k) ^ Mdec)⁻¹) ^ 2) := by ring
    _ ≤ C ^ 2 * ((Work.Diff.STE.wt k) ^ Mdec)⁻¹ := mul_le_mul_of_nonneg_left hkey (sq_nonneg _)

theorem CSq_le_of_decay {n : ℕ} {τ : ℝ} (N : ℕ)
    (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hdec : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k : Fin n → ℤ,
      ∀ a b : Fin n, ‖c t k a b‖ * (Work.Diff.STE.wt k) ^ M ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ a b : Fin n,
      Work.Diff.STE.CSq N (fun k : Fin n → ℤ => c t k a b) ≤ C := by
  -- the decay order is chosen so that `⟨k⟩^{-(N+n+1)}` is summable on `ℤⁿ`
  obtain ⟨C₁, _hC₁nn, hC₁⟩ := hdec (N + n + 1)
  refine ⟨C₁ ^ 2 * ∑' k : Fin n → ℤ, ((Work.Diff.STE.wt k) ^ (N + n + 1))⁻¹, ?_, ?_⟩
  · exact mul_nonneg (sq_nonneg _)
      (tsum_nonneg fun k => inv_nonneg.mpr (pow_nonneg (Work.Diff.STE.wt_pos k).le _))
  · intro t ht a b
    have hcard : n < 2 * (N + n + 1) := by omega
    have hsumR : Summable (fun k : Fin n → ℤ =>
        C₁ ^ 2 * ((Work.Diff.STE.wt k) ^ (N + n + 1))⁻¹) :=
      (summable_wt_inv' (n := n) hcard).mul_left _
    have hpw : ∀ k : Fin n → ℤ, (Work.Diff.STE.wt k) ^ N * ‖c t k a b‖ ^ 2
        ≤ C₁ ^ 2 * ((Work.Diff.STE.wt k) ^ (N + n + 1))⁻¹ := fun k =>
      wt_pow_mul_norm_sq_le (n := n) (s := N) (Mdec := N + n + 1) (by omega)
        (fun k => hC₁ t ht k a b) k
    have hsumL : Summable (fun k : Fin n → ℤ =>
        (Work.Diff.STE.wt k) ^ N * ‖c t k a b‖ ^ 2) :=
      Summable.of_nonneg_of_le
        (fun k => mul_nonneg (pow_nonneg (Work.Diff.STE.wt_pos k).le N) (sq_nonneg _)) hpw hsumR
    calc Work.Diff.STE.CSq N (fun k : Fin n → ℤ => c t k a b)
        = ∑' k : Fin n → ℤ, (Work.Diff.STE.wt k) ^ N * ‖c t k a b‖ ^ 2 := rfl
      _ ≤ ∑' k : Fin n → ℤ, C₁ ^ 2 * ((Work.Diff.STE.wt k) ^ (N + n + 1))⁻¹ :=
          Summable.tsum_le_tsum hpw hsumL hsumR
      _ = C₁ ^ 2 * ∑' k : Fin n → ℤ, ((Work.Diff.STE.wt k) ^ (N + n + 1))⁻¹ :=
          tsum_mul_left

end

end Work.Diff.STE.flat
