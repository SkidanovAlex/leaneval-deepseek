import Mathlib
import Submission.Work.Higman.Layers.Defs
import Submission.Work.Higman.Layers.finrank_eq_n_of_isInv_ne
import Submission.Work.Higman.Layers.exists_isInv_ne_bot_ne_top
import Submission.Work.Higman.Layers.exists_isInv_isCompl

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.Higman.Layers

/-- The `𝔽₂`-dimension of `V` is read off from its cardinality: `|V| = 2 ^ finrank V`. -/
theorem finrank_eq_two_mul {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {n : ℕ} (hcard : Nat.card V = 2 ^ (2 * n)) :
    Module.finrank (ZMod 2) V = 2 * n := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hv : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)]
    norm_num
  have h : 2 ^ (2 * n) = 2 ^ Module.finrank (ZMod 2) V := by rw [← hv, hcard]
  exact (Nat.pow_right_injective (le_refl 2) h).symm

/-- `2 ^ n - 1` is odd, for `1 ≤ n`. -/
theorem odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = 2 * m :=
    ⟨2 ^ (n - 1), by rw [← pow_succ', Nat.sub_add_cancel hn]⟩
  have hge : 2 ≤ 2 ^ n :=
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact ⟨m - 1, by omega⟩

/-- **The two constituents of `V`.**  If `V` is a finite `𝔽₂`-space of cardinality `2 ^ (2 * n)`
carrying `σ` of order `2 ^ n - 1` which is semiregular on `V ∖ {0}`, then `V` is the direct sum
of two `σ`-simple subspaces of dimension `n`.

Every non-zero invariant subspace has dimension `n` (`finrank_eq_n_of_isInv_ne`), and `V` is not
irreducible (`exists_isInv_ne_bot_ne_top`), so there is a simple invariant subspace `C₁` of
dimension `n`; Maschke for the odd order `2 ^ n - 1` (`exists_isInv_isCompl`) provides an
invariant complement `C₂`, which again has dimension `n` and is therefore simple. -/
theorem exists_two_constituents {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {σ : V →ₗ[ZMod 2] V} {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card V = 2 ^ (2 * n))
    (horder : orderOf σ = 2 ^ n - 1) (hsr : Work.Higman.Layers.Semiregular σ) :
    ∃ C₁ C₂ : Submodule (ZMod 2) V,
      Work.Higman.Layers.IsSimpleMod σ C₁ ∧ Work.Higman.Layers.IsSimpleMod σ C₂ ∧
      C₁ ⊓ C₂ = ⊥ ∧ C₁ ⊔ C₂ = ⊤ ∧
      Module.finrank (ZMod 2) C₁ = n ∧ Module.finrank (ZMod 2) C₂ = n := by
  classical
  have hfrV : Module.finrank (ZMod 2) V = 2 * n := finrank_eq_two_mul hcard
  -- a non-zero proper `σ`-invariant subspace; it has dimension `n`
  obtain ⟨C₁, hC₁inv, hC₁ne, hC₁top⟩ :=
    exists_isInv_ne_bot_ne_top (V := V) (σ := σ) (n := n) hn hcard horder
  have hC₁fr : Module.finrank (ZMod 2) C₁ = n :=
    finrank_eq_n_of_isInv_ne hn hcard horder hsr hC₁inv hC₁ne hC₁top
  -- an invariant complement of `C₁`
  have hσD : σ ^ (2 ^ n - 1) = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one σ
  obtain ⟨C₂, hC₂inv, hC₂disj, hC₂sup⟩ :=
    exists_isInv_isCompl (σ := σ) (D := 2 ^ n - 1) (odd_two_pow_sub_one hn) hσD hC₁inv
  -- its dimension is `2 * n - n = n`
  have hC₂fr : Module.finrank (ZMod 2) C₂ = n := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq (K := ZMod 2) C₁ C₂
    rw [hC₂sup, hC₂disj, finrank_top, finrank_bot, hC₁fr, hfrV] at hsum
    omega
  have hC₂top : C₂ ≠ ⊤ := by
    intro h
    have hfr : Module.finrank (ZMod 2) C₂ = Module.finrank (ZMod 2) V := by
      rw [h]
      exact finrank_top (R := ZMod 2) (M := V)
    rw [hC₂fr, hfrV] at hfr
    omega
  -- both are simple, since `n` is the only non-zero proper dimension
  have hsimple₁ : Work.Higman.Layers.IsSimpleMod σ C₁ := by
    refine ⟨hC₁inv, hC₁ne, ?_⟩
    intro W hWle hWinv
    by_cases hWb : W = ⊥
    · exact Or.inl hWb
    · refine Or.inr ?_
      have hWt : W ≠ ⊤ := fun h => hC₁top (le_antisymm le_top (h ▸ hWle))
      have hWfr : Module.finrank (ZMod 2) W = n :=
        finrank_eq_n_of_isInv_ne hn hcard horder hsr hWinv hWb hWt
      exact Submodule.eq_of_le_of_finrank_eq hWle (by rw [hWfr, hC₁fr])
  have hsimple₂ : Work.Higman.Layers.IsSimpleMod σ C₂ := by
    refine ⟨hC₂inv, ?_, ?_⟩
    · intro hbot
      rw [hbot] at hC₂fr
      simp at hC₂fr
      omega
    · intro W hWle hWinv
      by_cases hWb : W = ⊥
      · exact Or.inl hWb
      · refine Or.inr ?_
        have hWt : W ≠ ⊤ := fun h => hC₂top (le_antisymm le_top (h ▸ hWle))
        have hWfr : Module.finrank (ZMod 2) W = n :=
          finrank_eq_n_of_isInv_ne hn hcard horder hsr hWinv hWb hWt
        exact Submodule.eq_of_le_of_finrank_eq hWle (by rw [hWfr, hC₂fr])
  exact ⟨C₁, C₂, hsimple₁, hsimple₂, hC₂disj, hC₂sup, hC₁fr, hC₂fr⟩

end Work.Higman.Layers
