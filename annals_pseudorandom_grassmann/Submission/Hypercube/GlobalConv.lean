import Mathlib
import Submission.Hypercube.CondHyp

/-!
# The converse equivalence: small influences imply small restrictions (Lemma 2.12)

This file formalises Lemma 2.12 of arXiv:2209.04243 — the converse of Lemma 2.11
(`inflPair_le_of_global`): if all the influences `I_{T,x}[f]` with `T ⊆ S` are at most `ε`,
then the restriction `f_{S→x}` has squared `L²`-norm at most `2^{2|S|}ε`.  (The paper notes
that this direction is not used in the sequel, but it completes the §2 warm-up chapter.)

The proof uses the identity `f = ∑_{T ⊆ S} E_{S\T}[L_T f]`, the contraction property of the
resampling operators `E_T`, and the elementary bound `‖∑_T g_T‖₂ ≤ ∑_T ‖g_T‖₂`.
-/

open Finset BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Hypercube

noncomputable section

variable {n : ℕ}

/-- **The inversion identity**: `f = ∑_{T ⊆ S} E_{S\T}[L_T f]`. -/
theorem sum_ES_lapS_powerset (S : Finset (Fin n)) (f : (Fin n → ZMod 2) → ℂ) :
    (∑ T ∈ S.powerset, ES (S \ T) (lapS f T)) = f := by
  classical
  refine eq_of_walshFourier_eq fun R => ?_
  rw [walshFourier_sum]
  have hterm : ∀ T ∈ S.powerset,
      walshFourier (ES (S \ T) (lapS f T)) R =
        (if R ∩ (S \ T) = ∅ then (if T ⊆ R then walshFourier f R else 0) else 0) := by
    intro T _
    rw [walshFourier_ES, walshFourier_lapS]
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_eq_single (R ∩ S)]
  · have h1 : R ∩ (S \ (R ∩ S)) = ∅ := by
      rw [show S \ (R ∩ S) = S \ R from by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto]
      exact Finset.inter_sdiff_self R S
    rw [if_pos h1, if_pos Finset.inter_subset_left]
  · intro T hT hne
    have hTS : T ⊆ S := Finset.mem_powerset.mp hT
    by_cases hTR : T ⊆ R
    · have hex : ∃ r, r ∈ R ∩ S ∧ r ∉ T := by
        by_contra hc
        simp only [not_exists, not_and] at hc
        exact hne (Finset.Subset.antisymm
          (fun x hx => Finset.mem_inter.mpr ⟨hTR hx, hTS hx⟩)
          (fun x hx => of_not_not (hc x hx)))
      obtain ⟨r, hr, hrnT⟩ := hex
      have hne' : R ∩ (S \ T) ≠ ∅ :=
        Finset.nonempty_iff_ne_empty.mp ⟨r, Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hr).1,
            Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hr).2, hrnT⟩⟩⟩
      rw [if_neg hne']
    · by_cases hc : R ∩ (S \ T) = ∅
      · rw [if_pos hc, if_neg hTR]
      · rw [if_neg hc]
  · intro h
    exact absurd (Finset.mem_powerset.mpr Finset.inter_subset_right) h

/-- **Lemma 2.12 of arXiv:2209.04243**: if all influences `I_{T,x}[f]` for `T ⊆ S` are at most
`ε`, then the restriction `f_{S→x}` has squared `L²`-norm at most `2^{2|S|}ε`. -/
theorem mu_restr_le_of_inflPair_le (S : Finset (Fin n)) (x : Fin n → ZMod 2)
    (f : (Fin n → ZMod 2) → ℂ) {ε : ℝ}
    (h : ∀ T : Finset (Fin n), T ⊆ S → inflPair T x f ≤ ε) :
    mu (restr S x f) ≤ (2 : ℝ) ^ (2 * S.card) * ε := by
  classical
  have hf : restr S x f = ∑ T ∈ S.powerset, ES (S \ T) (Dfun T x f) := by
    conv_lhs => rw [← sum_ES_lapS_powerset S f]
    rw [restr_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTS : T ⊆ S := Finset.mem_powerset.mp hT
    rw [restr_ES (S \ T) S Finset.sdiff_subset x (lapS f T),
      show S \ (S \ T) = T from by
        ext a
        simp only [Finset.mem_sdiff]
        constructor
        · intro h
          by_contra hna
          exact h.2 ⟨h.1, hna⟩
        · intro ha
          exact ⟨hTS ha, fun h => h.2 ha⟩, Dfun_apply]
  rw [hf]
  have hcardR : ((S.powerset.card : ℕ) : ℝ) = (2 : ℝ) ^ S.card := by
    rw [Finset.card_powerset]; push_cast; ring
  calc mu (∑ T ∈ S.powerset, ES (S \ T) (Dfun T x f))
      ≤ (S.powerset.card : ℝ) * ∑ T ∈ S.powerset, mu (ES (S \ T) (Dfun T x f)) :=
        mu_sum_le_card_mul _ _
    _ ≤ (S.powerset.card : ℝ) * ∑ T ∈ S.powerset, ε := by
        gcongr with T hT
        exact le_trans (mu_ES_le _ _) (h T (Finset.mem_powerset.mp hT))
    _ = (2 : ℝ) ^ (2 * S.card) * ε := by
        rw [Finset.sum_const, nsmul_eq_mul, hcardR, ← mul_assoc, ← pow_add,
          show S.card + S.card = 2 * S.card from by ring]

end

end Submission.Hypercube
