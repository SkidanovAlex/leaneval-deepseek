import Mathlib
import Submission.Work.BW.relation_lattice_defs
import Submission.Work.BW.exists_relation_span

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
namespace Work.BW

open Complex

/-! ## The `ℚ`-dimension of `Vrel ℓ`

For a family of complex logarithms `ℓ : Fin m → ℂ` we study

  `Vrel ℓ = {v : Fin m → ℚ | ∑ᵢ vᵢℓᵢ ∈ 2πiℚ}`,

the `ℚ`-form of the relation lattice of `ℓ`.  If `ℓ` is `ℚ`-dependent but every one of its
`m - 1`-element subfamilies is `ℚ`-independent, then `dim_ℚ (Vrel ℓ) ≤ 2`:

* the kernel `K` of the linear form `v ↦ ∑ᵢ vᵢℓᵢ` is spanned by the (unique up to scalars)
  relation between the `ℓᵢ`, so `dim K ≤ 1` (`hmin`);
* modulo `K`, an element of `Vrel ℓ` is determined by the residue class of `∑ᵢ vᵢℓᵢ` in
  `ℂ ⧸ (2πiℚ)`, which is one-dimensional because `2πiℚ` is one-dimensional over `ℚ`.

Both bounds combine to `dim Vrel ℓ ≤ 1 + 1 = 2`. -/

/-- The `ℚ`-linear form `v ↦ ∑ᵢ vᵢℓᵢ` on rational exponent vectors. Its kernel is the space of
`ℚ`-linear relations between the `ℓᵢ`, and `Vrel ℓ` is the preimage of `2πiℚ` under it. -/
noncomputable def formQ {m : ℕ} (ℓ : Fin m → ℂ) : (Fin m → ℚ) →ₗ[ℚ] ℂ where
  toFun v := ∑ i, (v i : ℂ) * ℓ i
  map_add' v w := by simp only [Pi.add_apply, Rat.cast_add, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    show (∑ i, ((c * v i : ℚ) : ℂ) * ℓ i) = (c : ℂ) * (∑ i, (v i : ℂ) * ℓ i)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring

@[simp] lemma formQ_apply {m : ℕ} (ℓ : Fin m → ℂ) (v : Fin m → ℚ) :
    formQ ℓ v = ∑ i, (v i : ℂ) * ℓ i := rfl

/-- Membership in `Vrel ℓ`, transported to the linear form `formQ ℓ`. -/
@[simp] lemma mem_Vrel {m : ℕ} (ℓ : Fin m → ℂ) (v : Fin m → ℚ) :
    v ∈ Vrel ℓ ↔ ∃ q : ℚ, formQ ℓ v = (q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := Iff.rfl

theorem relation_lattice_Vrel_finrank_le_two {m : ℕ} (ℓ : Fin m → ℂ)
    (hdep : ¬ LinearIndependent ℚ ℓ)
    (hmin : ∀ i, LinearIndependent ℚ (fun j : {j : Fin m // j ≠ i} => ℓ j)) :
    Module.finrank ℚ (Vrel ℓ) ≤ 2 := by
  obtain ⟨r, -, hr0, hrel⟩ := exists_relation_span ℓ hdep hmin
  have hrs : formQ ℓ r = 0 := hr0
  -- the kernel of `formQ ℓ` is spanned by the single relation `r`
  have hker : (formQ ℓ).ker = Submodule.span ℚ ({r} : Set (Fin m → ℚ)) := by
    refine le_antisymm ?_ ?_
    · intro v hv
      rw [Submodule.mem_span_singleton]
      rw [LinearMap.mem_ker] at hv
      obtain ⟨c, hc⟩ := hrel v hv
      exact ⟨c, hc.symm⟩
    · intro v hv
      rw [Submodule.mem_span_singleton] at hv
      obtain ⟨c, hc⟩ := hv
      rw [LinearMap.mem_ker, ← hc, map_smul, hrs, smul_zero]
  by_cases hA : ∀ v ∈ Vrel ℓ, formQ ℓ v = 0
  · -- `Vrel ℓ` is contained in the one-dimensional kernel
    have hle : Vrel ℓ ≤ (formQ ℓ).ker := fun v hv => by
      rw [LinearMap.mem_ker]; exact hA v hv
    calc Module.finrank ℚ (Vrel ℓ) ≤ Module.finrank ℚ ((formQ ℓ).ker) :=
          Submodule.finrank_mono hle
      _ = Module.finrank ℚ (Submodule.span ℚ ({r} : Set (Fin m → ℚ))) := by rw [hker]
      _ ≤ 1 := by
            have h := finrank_span_le_card (R := ℚ) ({r} : Set (Fin m → ℚ))
            simpa using h
      _ ≤ 2 := by norm_num
  · -- otherwise `Vrel ℓ` is contained in `span {w, r}` for a suitable `w`
    push Not at hA
    obtain ⟨v0, hv0, hv0ne⟩ := hA
    rw [mem_Vrel] at hv0
    obtain ⟨q, hq⟩ := hv0
    have hqne : q ≠ 0 := by
      rintro rfl
      simp at hq
      exact hv0ne hq
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hqne
    set w : Fin m → ℚ := q⁻¹ • v0 with hw
    have hwV : formQ ℓ w = (1 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hw, map_smul, hq, Rat.smul_def]
      rw [Rat.cast_inv, ← mul_assoc, inv_mul_cancel₀ hqC, one_mul]
    have hVle : Vrel ℓ ≤ Submodule.span ℚ ({w, r} : Set (Fin m → ℚ)) := by
      intro u hu
      obtain ⟨qu, hqu⟩ := (mem_Vrel ℓ u).mp hu
      have hmem : u - qu • w ∈ (formQ ℓ).ker := by
        rw [LinearMap.mem_ker, map_sub, map_smul, hqu, hwV, Rat.smul_def]
        ring
      rw [hker] at hmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      have hueq : u = qu • w + c • r := by rw [hc]; abel
      rw [hueq]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ qu (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ c (Submodule.subset_span (by simp)))
    calc Module.finrank ℚ (Vrel ℓ) ≤
            Module.finrank ℚ (Submodule.span ℚ ({w, r} : Set (Fin m → ℚ))) :=
          Submodule.finrank_mono hVle
      _ ≤ 2 := by
          refine le_trans (finrank_span_le_card (R := ℚ) ({w, r} : Set (Fin m → ℚ))) ?_
          simp only [Set.toFinset_insert, Set.toFinset_singleton]
          exact Finset.card_le_two

end Work.BW
