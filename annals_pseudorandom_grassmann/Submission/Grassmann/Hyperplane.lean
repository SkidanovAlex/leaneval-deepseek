import Mathlib
import Submission.Grassmann.LevelOne

/-!
# The level-`1` "dictators": hyperplane indicators

The structural objects appearing in the conclusion of the KMS theorem are
`SubGr k ℓ A B` with `dim A + codim B ≤ r`; the smallest ones (`r = 1`, `A = ⊥`,
`codim B = 1`) are exactly the sets `{L : L ≤ H}` for a hyperplane `H ≤ 𝔽₂ᵏ`.

This file shows that these are **degree-`≤ 1` functions** on the Grassmann graph: the
indicator of `{L : L ≤ H}` lies in `V_1 = range (Ψ_1)`.  Concretely, for a hyperplane `H` and
`L : GrVertex k ℓ`,

  `Ψ_1 (W ↦ [W ≤ H]) (L) = if L ≤ H then 2^ℓ - 1 else 2^(ℓ-1) - 1`,

so `[L ≤ H]` is an affine combination of the constant function and an element of `V_1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open PseudorandomGrassmann
open Module Finset Filter
open Classical

local notation "𝔽₂" => ZMod 2

namespace Submission.Grassmann
namespace F2

noncomputable section

variable {k ℓ : ℕ}

attribute [local instance] Classical.propDecidable

/-- The number of lines contained in a subspace `U` is `2 ^ (finrank U) - 1`. -/
lemma card_lines_le (U : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    Nat.card {W : GrVertex k 1 // W.1 ≤ U} = 2 ^ Module.finrank 𝔽₂ U - 1 := by
  have hcard : Nat.card {W : GrVertex k 1 // W.1 ≤ U} = (SubGr k 1 ⊥ U).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext W
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SubGr, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨bot_le, h⟩, fun h => h.2⟩
  rw [hcard, card_SubGr_eq_grCount (k := k) (ℓ := 1) ⊥ U bot_le
    (by rw [finrank_bot]; omega)]
  rw [finrank_bot, Nat.sub_zero, Nat.sub_zero, grCount_one]

/-- The indicator of the lines lying in a subspace `H`, as a function on lines. -/
def lineInd (H : Submodule 𝔽₂ (Fin k → 𝔽₂)) : GrVertex k 1 → ℚ :=
  fun W => if W.1 ≤ H then 1 else 0

/-- If `H` is a hyperplane and `L ⊄ H`, then `L ⊓ H` is a hyperplane of `L`. -/
lemma finrank_inf_hyperplane (H : Submodule 𝔽₂ (Fin k → 𝔽₂))
    (hH : Module.finrank 𝔽₂ H = k - 1) (L : GrVertex k ℓ) (hL : ¬ L.1 ≤ H) :
    Module.finrank 𝔽₂ ↥(L.1 ⊓ H) = ℓ - 1 := by
  have hne : L.1 ⊓ H ≠ L.1 := fun h => hL (h ▸ inf_le_right)
  have hlt : Module.finrank 𝔽₂ ↥(L.1 ⊓ H) < ℓ := by
    have h := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left hne)
    rwa [L.2] at h
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq L.1 H
  rw [L.2, hH] at h1
  have h2 : Module.finrank 𝔽₂ ↥(L.1 ⊔ H) ≤ k := by
    have := Submodule.finrank_le (L.1 ⊔ H)
    rwa [finrank_fin_fun] at this
  omega

/-- **`Ψ₁` of a hyperplane indicator.** -/
theorem upFun_lineInd (hℓ : 1 ≤ ℓ) (H : Submodule 𝔽₂ (Fin k → 𝔽₂))
    (hH : Module.finrank 𝔽₂ H = k - 1) (L : GrVertex k ℓ) :
    upFun 1 (lineInd H) L =
      if L.1 ≤ H then ((2 ^ ℓ - 1 : ℕ) : ℚ) else ((2 ^ (ℓ - 1) - 1 : ℕ) : ℚ) := by
  have hset : ∀ W : GrVertex k 1, (if W.1 ≤ L.1 then lineInd H W else 0)
      = if W.1 ≤ L.1 ⊓ H then (1 : ℚ) else 0 := by
    intro W
    rw [lineInd]
    by_cases h1 : W.1 ≤ L.1 <;> by_cases h2 : W.1 ≤ H
    · rw [if_pos h1, if_pos h2, if_pos (le_inf h1 h2)]
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 (le_trans h inf_le_right))]
    · rw [if_neg h1, if_neg (fun h => h1 (le_trans h inf_le_left))]
    · rw [if_neg h1, if_neg (fun h => h1 (le_trans h inf_le_left))]
  rw [upFun, Finset.sum_congr rfl (fun W _ => hset W), ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul]
  have hcnt : (Finset.univ.filter (fun W : GrVertex k 1 => W.1 ≤ L.1 ⊓ H)).card
      = Nat.card {W : GrVertex k 1 // W.1 ≤ L.1 ⊓ H} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcnt, card_lines_le]
  by_cases hLH : L.1 ≤ H
  · rw [if_pos hLH, inf_eq_left.mpr hLH, L.2]
    ring
  · rw [if_neg hLH, finrank_inf_hyperplane H hH L hLH]
    ring

/-- **The hyperplane indicator is a degree-`≤ 1` function.** -/
theorem hyperplaneInd_mem_Vup (hℓ : 1 ≤ ℓ) (H : Submodule 𝔽₂ (Fin k → 𝔽₂))
    (hH : Module.finrank 𝔽₂ H = k - 1) :
    (fun L : GrVertex k ℓ => if L.1 ≤ H then (1 : ℚ) else 0) ∈ Vup (k := k) (ℓ := ℓ) 1 := by
  have hdecomp : upFun 1 (lineInd H)
      = fun L : GrVertex k ℓ =>
          ((2 ^ (ℓ - 1) - 1 : ℕ) : ℚ)
            + ((2 ^ (ℓ - 1) : ℕ) : ℚ) * (if L.1 ≤ H then (1 : ℚ) else 0) := by
    funext L
    rw [upFun_lineInd hℓ H hH L]
    by_cases h : L.1 ≤ H
    · rw [if_pos h, if_pos h, mul_one]
      have h1 : 1 ≤ 2 ^ (ℓ - 1) := Nat.one_le_two_pow
      have h2 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
      push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
      conv_lhs => rw [show ℓ = (ℓ - 1) + 1 from by omega, pow_succ]
      ring
    · rw [if_neg h, if_neg h, mul_zero, add_zero]
  have hmem : upFun 1 (lineInd H) ∈ Vup (k := k) (ℓ := ℓ) 1 := ⟨lineInd H, rfl⟩
  have hconst : (fun _ : GrVertex k ℓ => ((2 ^ (ℓ - 1) - 1 : ℕ) : ℚ))
      ∈ Vup (k := k) (ℓ := ℓ) 1 := by
    have h0 : (fun _ : GrVertex k ℓ => ((2 ^ (ℓ - 1) - 1 : ℕ) : ℚ))
        ∈ Vup (k := k) (ℓ := ℓ) 0 := by
      have hmem0 := Submodule.smul_mem (Vup (k := k) (ℓ := ℓ) 0)
        (((2 ^ (ℓ - 1) - 1 : ℕ) : ℚ)) one_mem_Vup_zero
      convert hmem0 using 1
      funext L
      simp
    exact Vup_pred_le (k := k) (ℓ := ℓ) hℓ 1 (by omega) (by omega) h0
  have hsmul : ((2 ^ (ℓ - 1) : ℕ) : ℚ) •
      (fun L : GrVertex k ℓ => if L.1 ≤ H then (1 : ℚ) else 0)
      ∈ Vup (k := k) (ℓ := ℓ) 1 := by
    have hsub := Submodule.sub_mem _ hmem hconst
    rw [hdecomp] at hsub
    have heq : ((fun L : GrVertex k ℓ =>
        ((2 ^ (ℓ - 1) - 1 : ℕ) : ℚ)
          + ((2 ^ (ℓ - 1) : ℕ) : ℚ) * (if L.1 ≤ H then (1 : ℚ) else 0))
        - (fun _ : GrVertex k ℓ => ((2 ^ (ℓ - 1) - 1 : ℕ) : ℚ)))
        = ((2 ^ (ℓ - 1) : ℕ) : ℚ) •
            (fun L : GrVertex k ℓ => if L.1 ≤ H then (1 : ℚ) else 0) := by
      ext L
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rwa [heq] at hsub
  have hne : ((2 ^ (ℓ - 1) : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))
  have hfin : ((2 ^ (ℓ - 1) : ℕ) : ℚ)⁻¹ •
      (((2 ^ (ℓ - 1) : ℕ) : ℚ) •
        (fun L : GrVertex k ℓ => if L.1 ≤ H then (1 : ℚ) else 0))
      = (fun L : GrVertex k ℓ => if L.1 ≤ H then (1 : ℚ) else 0) := by
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [← hfin]
  exact Submodule.smul_mem _ _ hsmul

/-- The constant functions lie in `V_0`. -/
lemma const_mem_Vup_zero (c : ℚ) :
    (fun _ : GrVertex k ℓ => c) ∈ Vup (k := k) (ℓ := ℓ) 0 := by
  have hmem0 := Submodule.smul_mem (Vup (k := k) (ℓ := ℓ) 0) c one_mem_Vup_zero
  convert hmem0 using 1
  funext L
  simp

/-- The sum of the hyperplane indicator over all vertices is the size of `SubGr k ℓ ⊥ H`. -/
lemma sum_hyperplaneInd (H : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    (∑ L : GrVertex k ℓ, (if L.1 ≤ H then (1 : ℚ) else 0))
      = ((SubGr k ℓ ⊥ H).card : ℚ) := by
  have hset : (Finset.univ.filter (fun L : GrVertex k ℓ => L.1 ≤ H)) = SubGr k ℓ ⊥ H := by
    ext L
    simp [SubGr]
  rw [← Finset.sum_filter, hset, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The centred hyperplane indicator is a level-`1` function.** -/
theorem hyperplaneInd_centered_mem_LvlAll (hℓ : 1 ≤ ℓ) (H : Submodule 𝔽₂ (Fin k → 𝔽₂))
    (hH : Module.finrank 𝔽₂ H = k - 1) :
    (fun L : GrVertex k ℓ => (if L.1 ≤ H then (1 : ℚ) else 0) - dens (SubGr k ℓ ⊥ H))
      ∈ LvlAll k ℓ 1 := by
  rw [LvlAll_succ (by norm_num : (1 : ℕ) ≠ 0), Lvl, Submodule.mem_inf]
  have hd : dens (SubGr k ℓ ⊥ H) * (Fintype.card (GrVertex k ℓ) : ℚ)
      = ((SubGr k ℓ ⊥ H).card : ℚ) := dens_mul_card' _
  have hsum : (∑ L : GrVertex k ℓ,
        ((if L.1 ≤ H then (1 : ℚ) else 0) - dens (SubGr k ℓ ⊥ H))) = 0 := by
    rw [Finset.sum_sub_distrib, sum_hyperplaneInd, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    rw [← hd]
    ring
  constructor
  · exact Submodule.sub_mem _ (hyperplaneInd_mem_Vup hℓ H hH)
      (Vup_pred_le (k := k) (ℓ := ℓ) hℓ 1 (by omega) (by omega)
        (const_mem_Vup_zero _))
  · rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    obtain ⟨c, rfl⟩ := Vup_zero_const hn
    rw [stdInner_apply, ← Finset.mul_sum, hsum, mul_zero]

/-- The number of `ℓ`-subspaces contained in a hyperplane `H`. -/
lemma card_GrVertex_le_hyperplane (H : Submodule 𝔽₂ (Fin k → 𝔽₂))
    (hH : Module.finrank 𝔽₂ H = k - 1) (hℓ : ℓ ≤ k) :
    Nat.card {L : GrVertex k ℓ // L.1 ≤ H} = grCount (k - 1) ℓ := by
  have hcard : Nat.card {L : GrVertex k ℓ // L.1 ≤ H} = (SubGr k ℓ ⊥ H).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext L
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SubGr, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨bot_le, h⟩, fun h => h.2⟩
  rw [hcard, card_SubGr_eq_grCount (k := k) (ℓ := ℓ) ⊥ H bot_le (by rw [finrank_bot]; omega),
    finrank_bot, hH]
  rw [Nat.sub_zero, Nat.sub_zero]

end

end F2
end Submission.Grassmann
