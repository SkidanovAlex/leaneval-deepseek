import Mathlib
import Submission.Work.ResMath.defs

/-!
# `‖B‖ ≤ 1` for the resampling matrix `B` (paper §4.1)

`B = P_sᵀ · D' · (J/2) · C · P_t` (see `HvdH.resB`).  Each of the five factors is a contraction
for the sup norm on `Fin _ → ℂ`:

* `P_t` and `C` (`HvdH.permT`, `HvdH.rowSel`) have at most one non-zero entry per row, of modulus
  `1`;
* `D' = diag(e^{π α² β_ℓ²} / 2^{2α²-2})` is diagonal with entries of modulus `≤ 1` (hypothesis
  `hD'`);
* `J/2` is a contraction with constant `7/8` (hypothesis `hJ`);
* `P_sᵀ` has at most one non-zero entry per row, because `j ↦ t j mod s` is injective when
  `s` and `t` are coprime (`hstc`).

The generic fact used for all of them is `mulVec_norm_le_one`: a matrix all of whose rows have
`∑_j ‖M i j‖ ≤ 1` is a contraction for the sup norm.
-/

namespace Work.ResMath

/-- A row of a `0/1`-pattern matrix whose support has at most one point is a contraction row:
`∑_i [g i = c] ≤ 1` for an injective `g`. -/
lemma sum_ite_eq_le_one {t : ℕ} {β : Type*} [DecidableEq β] (g : Fin t → β)
    (hg : Function.Injective g) (c : β) :
    ∑ i : Fin t, (if g i = c then (1 : ℝ) else 0) ≤ 1 := by
  by_cases h : ∃ i : Fin t, g i = c
  · obtain ⟨i₀, hi₀⟩ := h
    rw [Finset.sum_eq_single i₀]
    · simp [hi₀]
    · intro b _ hb
      by_cases hbc : g b = c
      · exact absurd (hg (hbc.trans hi₀.symm)) hb
      · simp [hbc]
    · intro hmem; exact absurd (Finset.mem_univ i₀) hmem
  · have h0 : ∑ i : Fin t, (if g i = c then (1 : ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [ite_eq_right (not_exists.mp h i)]
    rw [h0]; norm_num

/-- A matrix whose rows have `ℓ¹`-mass at most `1` is a contraction for the sup norm on `Fin _ → ℂ`. -/
lemma mulVec_norm_le_one {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) (v : n → ℂ)
    (h : ∀ i, ∑ j, ‖M i j‖ ≤ 1) : ‖M.mulVec v‖ ≤ ‖v‖ := by
  have key : ∀ i, ‖(M.mulVec v) i‖ ≤ ‖v‖ := by
    intro i
    rw [Matrix.mulVec_apply]
    calc ‖M.row i ⬝ᵥ v‖ ≤ ∑ j, ‖M i j * v j‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖M i j‖ * ‖v‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _)
      _ = (∑ j, ‖M i j‖) * ‖v‖ := by rw [Finset.sum_mul]
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right (h i) (norm_nonneg _)
      _ = ‖v‖ := one_mul _
  rw [Pi.norm_def, Pi.norm_def]
  exact_mod_cast Finset.sup_le (fun i _ => by exact_mod_cast key i)

/-- Every row of `P_t` (`HvdH.permT`) has `ℓ¹`-mass at most `1`. -/
lemma permT_row (s t : ℕ) (i : Fin t) : ∑ j : Fin t, ‖HvdH.permT s t i j‖ ≤ 1 := by
  refine le_trans (Finset.sum_le_sum fun j _ => ?_)
    (sum_ite_eq_le_one (fun j : Fin t => (j:ℕ)) (fun a b h => Fin.ext h) ((t - s * (i:ℕ) % t) % t))
  by_cases h : (j:ℕ) = (t - s * (i:ℕ) % t) % t
  · rw [show HvdH.permT s t i j = 1 by simp [HvdH.permT, h], ite_eq_left h, norm_one]
  · rw [show HvdH.permT s t i j = 0 by simp [HvdH.permT, h], ite_eq_right h, norm_zero]

/-- Every row of `C` (`HvdH.rowSel`) has `ℓ¹`-mass at most `1`. -/
lemma rowSel_row (s t : ℕ) (i : Fin s) : ∑ j : Fin t, ‖HvdH.rowSel s t i j‖ ≤ 1 := by
  refine le_trans (Finset.sum_le_sum fun j _ => ?_)
    (sum_ite_eq_le_one (fun j : Fin t => (j:ℤ)) (fun a b h => Fin.ext (Int.ofNat.inj h))
      (HvdH.rnd ((t * (i:ℕ) : ℝ) / s)))
  by_cases h : (j:ℤ) = HvdH.rnd ((t * (i:ℕ) : ℝ) / s)
  · rw [show HvdH.rowSel s t i j = 1 by simp [HvdH.rowSel, h], ite_eq_left h, norm_one]
  · rw [show HvdH.rowSel s t i j = 0 by simp [HvdH.rowSel, h], ite_eq_right h, norm_zero]

/-- Every row of `P_sᵀ` (`HvdH.permS` transposed) has `ℓ¹`-mass at most `1`; coprimality of `s` and
`t` makes `j ↦ t j mod s` injective. -/
lemma permS_transpose_row (s t : ℕ) (hs : 2 ≤ s) (hcop : Nat.Coprime s t) (i : Fin s) :
    ∑ j : Fin s, ‖(HvdH.permS s t).transpose i j‖ ≤ 1 := by
  have hinj : Function.Injective (fun j : Fin s => t * (j:ℕ) % s) := by
    intro a b hab
    have hm : t * (a:ℕ) ≡ t * (b:ℕ) [MOD s] := hab
    have h1 : (a:ℕ) ≡ (b:ℕ) [MOD s / s.gcd t] :=
      Nat.ModEq.cancel_left_div_gcd (by omega) hm
    rw [show s.gcd t = 1 from hcop, Nat.div_one] at h1
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt h1 a.isLt b.isLt)
  refine le_trans (Finset.sum_le_sum fun j _ => ?_)
    (sum_ite_eq_le_one (fun j : Fin s => t * (j:ℕ) % s) hinj (i:ℕ))
  by_cases h : t * (j:ℕ) % s = (i:ℕ)
  · have hentry : (HvdH.permS s t).transpose i j = 1 := by
      simp only [Matrix.transpose_apply, HvdH.permS]
      rw [ite_eq_left h.symm]
    rw [hentry, norm_one, ite_eq_left h]
  · have hentry : (HvdH.permS s t).transpose i j = 0 := by
      simp only [Matrix.transpose_apply, HvdH.permS]
      rw [ite_eq_right (fun (hc : (i:ℕ) = t * (j:ℕ) % s) => h hc.symm)]
    rw [hentry, norm_zero, ite_eq_right h]

/-- Every row of the diagonal matrix `D'` (`HvdH.diagD'`) has `ℓ¹`-mass at most `1`; this is
exactly the hypothesis that its diagonal entries have modulus at most `1`. -/
lemma diagD'_row (s t α : ℕ) (hD' : ∀ ℓ : Fin s, ‖HvdH.diagD' s t α ℓ ℓ‖ ≤ 1) (i : Fin s) :
    ∑ j : Fin s, ‖HvdH.diagD' s t α i j‖ ≤ 1 := by
  rw [Finset.sum_eq_single i]
  · exact hD' i
  · intro b _ hb
    have hz : HvdH.diagD' s t α i b = 0 := by
      simp [HvdH.diagD', HvdH.diagD, Ne.symm hb]
    rw [hz, norm_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem resB_norm_le (s t α : ℕ) (hs : 2 ≤ s) (hst : s < t) (hstc : Nat.Coprime s t) (hα : 2 ≤ α)
    (hD' : ∀ ℓ : Fin s, ‖HvdH.diagD' s t α ℓ ℓ‖ ≤ 1)
    (hJ : ∀ u : Fin s → ℂ, ‖((1 / 2 : ℂ) • HvdH.Jmat s t α).mulVec u‖ ≤ 7 / 8 * ‖u‖)
    (v : Fin t → ℂ) : ‖(HvdH.resB s t α).mulVec v‖ ≤ ‖v‖ := by
  have _hst := hst
  have _hα := hα
  have hres : (HvdH.resB s t α).mulVec v =
      (HvdH.permS s t).transpose.mulVec
        ((HvdH.diagD' s t α).mulVec
          (((1 / 2 : ℂ) • HvdH.Jmat s t α).mulVec
            ((HvdH.rowSel s t).mulVec ((HvdH.permT s t).mulVec v)))) := by
    simp only [HvdH.resB, ← Matrix.mulVec_mulVec]
  rw [hres]
  calc ‖(HvdH.permS s t).transpose.mulVec
        ((HvdH.diagD' s t α).mulVec
          (((1 / 2 : ℂ) • HvdH.Jmat s t α).mulVec
            ((HvdH.rowSel s t).mulVec ((HvdH.permT s t).mulVec v))))‖
      ≤ ‖(HvdH.diagD' s t α).mulVec
          (((1 / 2 : ℂ) • HvdH.Jmat s t α).mulVec
            ((HvdH.rowSel s t).mulVec ((HvdH.permT s t).mulVec v)))‖ :=
        mulVec_norm_le_one _ _ (permS_transpose_row s t hs hstc)
    _ ≤ ‖((1 / 2 : ℂ) • HvdH.Jmat s t α).mulVec
          ((HvdH.rowSel s t).mulVec ((HvdH.permT s t).mulVec v))‖ :=
        mulVec_norm_le_one _ _ (diagD'_row s t α hD')
    _ ≤ 7 / 8 * ‖(HvdH.rowSel s t).mulVec ((HvdH.permT s t).mulVec v)‖ := hJ _
    _ ≤ 7 / 8 * ‖(HvdH.permT s t).mulVec v‖ :=
        mul_le_mul_of_nonneg_left (mulVec_norm_le_one _ _ (rowSel_row s t)) (by norm_num)
    _ ≤ 7 / 8 * ‖v‖ :=
        mul_le_mul_of_nonneg_left (mulVec_norm_le_one _ _ (permT_row s t)) (by norm_num)
    _ ≤ ‖v‖ := by linarith [norm_nonneg v]

end Work.ResMath
