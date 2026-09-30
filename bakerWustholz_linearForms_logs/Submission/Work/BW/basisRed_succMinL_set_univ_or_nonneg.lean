import Mathlib
import Submission.Work.BW.basisRed_defs
import Submission.Work.BW.wNorm_smul

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The successive-minimum level set is either all of `ℝ` or contained in `[0, ∞)`

For the weighted `ℓ¹` norm `wNorm A c` on `ℝⁿ` and its successive minimum
`succMinL`, the set of levels `t` at which the lattice points of norm `≤ t` span
a subspace of dimension at least `j` is upward closed. Because `wNorm A c` is
positively homogeneous (`wNorm A c (k • x) = k * wNorm A c x` for `k ≥ 0`), this
upward closed set is either *all* of `ℝ` or else contains no negative real: as
soon as a negative level `t₁` makes the span `j`-dimensional, scaling by a large
positive integer `k` with `k * t₁ ≤ t` keeps `j` linearly independent lattice
points inside the level set of *every* `t`.
-/

namespace Work.BW

theorem basisRed_succMinL_set_univ_or_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℝ)
    (j : ℕ) :
    ({t : ℝ | j ≤ Module.finrank ℝ (Submodule.span ℝ {x : Fin n → ℝ |
        (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ Work.BW.wNorm A c x ≤ t})} = Set.univ)
      ∨ ({t : ℝ | j ≤ Module.finrank ℝ (Submodule.span ℝ {x : Fin n → ℝ |
        (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ Work.BW.wNorm A c x ≤ t})} ⊆ Set.Ici 0) := by
  by_cases h : ({t : ℝ | j ≤ Module.finrank ℝ (Submodule.span ℝ {x : Fin n → ℝ |
      (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ Work.BW.wNorm A c x ≤ t})} ⊆ Set.Ici 0)
  · exact Or.inr h
  · left
    obtain ⟨t₁, ht₁, ht₁neg⟩ := Set.not_subset.mp h
    have ht₁neg' : t₁ < 0 := by
      have : ¬ (0 ≤ t₁) := by simpa [Set.mem_Ici] using ht₁neg
      exact not_le.mp this
    -- every level `t` is in the set
    have key : ∀ t : ℝ, j ≤ Module.finrank ℝ (Submodule.span ℝ {x : Fin n → ℝ |
        (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ Work.BW.wNorm A c x ≤ t}) := by
      intro t
      -- choose a positive integer `k` with `k * t₁ ≤ t`
      obtain ⟨k, hk1, hkt⟩ : ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) * t₁ ≤ t := by
        obtain ⟨k, hk⟩ := exists_nat_ge (max (t / t₁) 1)
        refine ⟨k, ?_, ?_⟩
        · exact_mod_cast le_trans (le_max_right _ _) hk
        · have hk' : t / t₁ ≤ (k : ℝ) := le_trans (le_max_left _ _) hk
          have h1 := mul_le_mul_of_nonpos_right hk' (le_of_lt ht₁neg')
          rwa [div_mul_cancel₀ t (ne_of_lt ht₁neg')] at h1
      have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one hk1'
      have hknonneg : (0 : ℝ) ≤ (k : ℝ) := le_of_lt hkpos
      have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
      -- the level sets
      let T : Set (Fin n → ℝ) := {x : Fin n → ℝ |
        (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ Work.BW.wNorm A c x ≤ t₁}
      let St : Set (Fin n → ℝ) := {x : Fin n → ℝ |
        (∃ v : Fin n → ℤ, x = fun i => (v i : ℝ)) ∧ Work.BW.wNorm A c x ≤ t}
      have hT : j ≤ Module.finrank ℝ (Submodule.span ℝ T) := ht₁
      -- scaling by `k`
      let e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
        LinearEquiv.smulOfNeZero ℝ (Fin n → ℝ) (k : ℝ) hkne
      have himage : e '' T ⊆ St := by
        rintro y ⟨x, hx, rfl⟩
        obtain ⟨v, rfl⟩ := hx.1
        refine ⟨⟨fun i => k * v i, ?_⟩, ?_⟩
        · rw [LinearEquiv.smulOfNeZero_apply]
          funext i
          simp [Pi.smul_apply]
        · rw [LinearEquiv.smulOfNeZero_apply, Work.BW.wNorm_smul, abs_of_nonneg hknonneg]
          exact le_trans (mul_le_mul_of_nonneg_left hx.2 hknonneg) hkt
      have hle : Module.finrank ℝ (Submodule.span ℝ (e '' T)) ≤
          Module.finrank ℝ (Submodule.span ℝ St) :=
        Submodule.finrank_mono (Submodule.span_mono himage)
      have heq : Module.finrank ℝ (Submodule.span ℝ (e '' T)) =
          Module.finrank ℝ (Submodule.span ℝ T) := by
        rw [Submodule.span_image_linearEquiv]
        exact LinearEquiv.finrank_map_eq e (Submodule.span ℝ T)
      calc j ≤ Module.finrank ℝ (Submodule.span ℝ T) := hT
        _ = Module.finrank ℝ (Submodule.span ℝ (e '' T)) := heq.symm
        _ ≤ Module.finrank ℝ (Submodule.span ℝ St) := hle
    ext t
    simp only [Set.mem_univ, iff_true]
    exact key t

end Work.BW
