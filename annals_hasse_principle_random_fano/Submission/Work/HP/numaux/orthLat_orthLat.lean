import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.numaux.rk_orthLatDefs
import Submission.Work.HP.numaux.castL_smul_mem_range
import Submission.Work.HP.numaux.castL_mem_spread_iff

/-!
# The double orthogonal complement of a primitive lattice

For an integral lattice `Λ ⊆ ℤ^ι` with `ι` finite, taking the integer-orthogonal complement
twice returns the *saturation* of `Λ`.  In particular, if `Λ` is primitive (= saturated,
pure), the double orthogonal complement is `Λ` itself:

`orthLat (orthLat Λ) = Λ`  for `IsPrimLat Λ`.

The proof goes through the rational spread `spread Λ ⊆ ℚ^ι` of `rk_orthLatDefs`:

* the orthogonal lattice spreads to the rational orthogonal complement,
  `spread (orthLat Λ) = stdB.orthogonal (spread Λ)`;
* the rational double orthogonal complement of a subspace is the subspace itself,
  `stdB.orthogonal (stdB.orthogonal V) = V`;
* the integer points of `spread Λ` are exactly the saturation `satLat Λ`
  (`castL_mem_spread_iff`, proved in a sibling file).

Then, for `b ∈ orthLat (orthLat Λ)`, the vector `castL b` lies in
`(spread Λ)^⊥⊥ = spread Λ`, so `b ∈ satLat Λ = Λ` by primitivity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace Work.HP.numaux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## General facts about the rational spread -/

/-- For a `ℤ`-submodule `I` of `ℚ^ι` containing an integer multiple of every vector and a
`ℚ`-subspace `V`, the `ℚ`-span of the lattice points of `V` (i.e. of `V ⊓ I`) is `V`. -/
private theorem span_restrictScalars_inf (V : Submodule ℚ (ι → ℚ)) (I : Submodule ℤ (ι → ℚ))
    (hI : ∀ y : ι → ℚ, ∃ M : ℤ, M ≠ 0 ∧ M • y ∈ I) :
    Submodule.span ℚ (↑(V.restrictScalars ℤ ⊓ I) : Set (ι → ℚ)) = V := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    intro x hx
    exact hx.1
  · intro y hy
    obtain ⟨M, hM, hMy⟩ := hI y
    have hMyV : M • y ∈ V := V.smul_mem M hy
    have hmem : M • y ∈ (V.restrictScalars ℤ ⊓ I : Submodule ℤ (ι → ℚ)) := ⟨hMyV, hMy⟩
    have hspan : ((M : ℚ))⁻¹ • (M • y) ∈
        Submodule.span ℚ (↑(V.restrictScalars ℤ ⊓ I) : Set (ι → ℚ)) :=
      Submodule.smul_mem _ _ (Submodule.subset_span hmem)
    have hcast : ((M : ℚ))⁻¹ • (M • y) = y := by
      rw [← Int.cast_smul_eq_zsmul ℚ M y, smul_smul, inv_mul_cancel₀, one_smul]
      simp [Int.cast_ne_zero.mpr hM]
    rwa [hcast] at hspan

/-- The standard bilinear form `⟨x,y⟩ = ∑ᵢ xᵢyᵢ` on `ℚ^ι` is nondegenerate. -/
private lemma stdB_nondegenerate : (stdB (ι := ι)).Nondegenerate := by
  constructor
  · intro x hx
    funext i
    have h := hx (Pi.single i 1)
    simpa [stdB_apply, Pi.single_apply] using h
  · intro x hx
    funext i
    have h := hx (Pi.single i 1)
    rw [stdB_comm] at h
    simpa [stdB_apply, Pi.single_apply] using h

/-- The standard bilinear form on `ℚ^ι` is reflexive, so taking the orthogonal complement of a
subspace twice returns the subspace. -/
theorem stdB_orthogonal_orthogonal (V : Submodule ℚ (ι → ℚ)) :
    stdB.orthogonal (stdB.orthogonal V) = V :=
  LinearMap.BilinForm.orthogonal_orthogonal stdB_nondegenerate
    (fun x y h => by simpa [stdB_comm] using h) V

/-! ## Elementary lemmas -/

/-- The standard pairing on `ℤ^ι` is the restriction of the standard bilinear form on `ℚ^ι`
along the coordinatewise inclusion. -/
private lemma stdB_castL (v w : ι → ℤ) : stdB (castL v) (castL w) = (dotI v w : ℚ) := by
  rw [stdB_apply, dotI]
  simp only [castL_apply, Int.cast_sum, Int.cast_mul]

/-- The image of a vector of `Λ` under the coordinatewise inclusion lies in the rational
spread of `Λ`. -/
private lemma castL_mem_spread {Λ : Submodule ℤ (ι → ℤ)} {x : ι → ℤ} (hx : x ∈ Λ) :
    castL x ∈ spread Λ := by
  rw [spread]
  exact Submodule.subset_span (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)

/-- An integer vector is orthogonal to `Λ` exactly when its image in `ℚ^ι` is orthogonal to the
rational spread of `Λ` with respect to the standard bilinear form. -/
lemma castL_mem_orthogonal_spread_iff {Λ : Submodule ℤ (ι → ℤ)} {a : ι → ℤ} :
    castL a ∈ stdB.orthogonal (spread Λ) ↔ a ∈ orthLat Λ := by
  constructor
  · intro h x hx
    have h1 := (LinearMap.BilinForm.mem_orthogonal_iff.mp h) (castL x) (castL_mem_spread hx)
    rw [stdB_castL] at h1
    have h2 : dotI x a = 0 := by exact_mod_cast h1
    rwa [dotI_comm]
  · intro ha
    have hle : spread Λ ≤ LinearMap.ker (stdB (castL a) : (ι → ℚ) →ₗ[ℚ] ℚ) := by
      rw [spread_eq_span_image, Submodule.span_le]
      rintro n ⟨x, hx, rfl⟩
      show stdB (castL a) (castL x) = 0
      rw [stdB_castL]
      exact_mod_cast mem_orthLat.mp ha x hx
    intro n hn
    have h1 := hle hn
    show stdB n (castL a) = 0
    rw [stdB_comm]
    exact h1

/-- The rational spread of the orthogonal lattice is the rational orthogonal complement of the
rational spread. -/
private lemma spread_orthLat_eq_orthogonal (Λ : Submodule ℤ (ι → ℤ)) :
    spread (orthLat Λ) = stdB.orthogonal (spread Λ) := by
  have hAI : (stdB.orthogonal (spread Λ)).restrictScalars ℤ ⊓
        LinearMap.range (castL (ι := ι)) = (orthLat Λ).map (castL (ι := ι)) := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨hy, z, rfl⟩
      exact Submodule.mem_map.mpr ⟨z, castL_mem_orthogonal_spread_iff.mp hy, rfl⟩
    · rintro y ⟨a, ha, rfl⟩
      exact ⟨castL_mem_orthogonal_spread_iff.mpr ha, ⟨a, rfl⟩⟩
  calc spread (orthLat Λ)
      = Submodule.span ℚ (↑((orthLat Λ).map (castL (ι := ι))) : Set (ι → ℚ)) := rfl
    _ = Submodule.span ℚ (↑((stdB.orthogonal (spread Λ)).restrictScalars ℤ ⊓
          LinearMap.range (castL (ι := ι))) : Set (ι → ℚ)) := by rw [hAI]
    _ = stdB.orthogonal (spread Λ) := span_restrictScalars_inf _ _ castL_smul_mem_range

/-! ## The double orthogonal complement -/

/-- The double orthogonal complement of an integral lattice is its saturation. -/
theorem orthLat_orthLat_eq_satLat (Λ : Submodule ℤ (ι → ℤ)) :
    orthLat (orthLat Λ) = satLat Λ := by
  refine le_antisymm ?_ ?_
  · intro b hb
    have h1 : castL b ∈ spread (orthLat (orthLat Λ)) := castL_mem_spread hb
    rw [spread_orthLat_eq_orthogonal (orthLat Λ), spread_orthLat_eq_orthogonal Λ,
      stdB_orthogonal_orthogonal (spread Λ)] at h1
    exact (castL_mem_spread_iff Λ b).mp h1
  · intro x hx
    obtain ⟨m, hm, hmx⟩ := mem_satLat.mp hx
    rw [mem_orthLat]
    intro a ha
    have h1 : dotI a (m • x) = 0 := (mem_orthLat.mp ha) (m • x) hmx
    rw [dotI_smul_right] at h1
    have h2 : dotI a x = 0 := (mul_eq_zero.mp h1).resolve_left hm
    rwa [dotI_comm]

theorem orthLat_orthLat {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Submodule ℤ (ι → ℤ))
    (h : IsPrimLat Λ) : orthLat (orthLat Λ) = Λ := by
  rw [orthLat_orthLat_eq_satLat, satLat_eq_of_isPrimLat h]

end Work.HP.numaux
