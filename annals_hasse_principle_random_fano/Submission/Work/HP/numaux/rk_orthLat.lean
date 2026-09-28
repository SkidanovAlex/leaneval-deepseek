import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.numaux.rk_orthLatDefs

/-!
# Rank of the orthogonal lattice

For an integral lattice `Λ ⊆ ℤ^ι` (a `ℤ`-submodule) we compute the rank of its orthogonal
complement `orthLat Λ = {a : ℤ^ι | ∀ x ∈ Λ, ⟨a,x⟩ = 0}`:

  `rk (orthLat Λ) = Fintype.card ι - rk Λ`.

The proof passes to the rational span.  With `castL : ℤ^ι →ₗ[ℤ] ℚ^ι` the coordinatewise
inclusion and `spread L ⊆ ℚ^ι` the `ℚ`-span of the rational points of `L`, we have

* `finrank ℚ (spread L) = finrank ℤ L`               (`spread_finrank`),
* `spread (orthLat Λ) = stdB.orthogonal (spread Λ)`  (`spread_orthLat_eq_orthogonal`),

where `stdB` is the standard nondegenerate bilinear form `⟨x,y⟩ = ∑ i, x i * y i` on `ℚ^ι`.
The claim then follows from Mathlib's `LinearMap.BilinForm.finrank_orthogonal` and
`Module.finrank_fintype_fun_eq_card`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Finset

namespace Work.HP.numaux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The pairing against the standard form -/

lemma stdB_castL (v w : ι → ℤ) : stdB (castL v) (castL w) = (dotI v w : ℚ) := by
  rw [stdB_apply, dotI]
  simp only [castL_apply, Int.cast_sum, Int.cast_mul]

/-! ### Clearing denominators -/

/-- Every rational vector has a nonzero integer multiple which is integer valued. -/
lemma castL_denom (y : ι → ℚ) :
    ∃ M : ℤ, M ≠ 0 ∧ M • y ∈ LinearMap.range (castL (ι := ι)) := by
  set M : ℤ := ∏ j, ((y j).den : ℤ) with hM
  refine ⟨M, ?_, ?_⟩
  · rw [hM]; positivity
  · refine LinearMap.mem_range.mpr
      ⟨fun i => (y i).num * ∏ j ∈ Finset.univ.erase i, ((y j).den : ℤ), ?_⟩
    ext i
    have hsplit : M = ((y i).den : ℤ) * ∏ j ∈ Finset.univ.erase i, ((y j).den : ℤ) := by
      rw [hM, ← Finset.mul_prod_erase Finset.univ (fun j => ((y j).den : ℤ))
        (Finset.mem_univ i)]
    have hcast : (M : ℚ) = ((y i).den : ℚ) *
        ∏ j ∈ Finset.univ.erase i, ((y j).den : ℚ) := by
      rw [hsplit]; push_cast; ring
    have hnum : ((y i).num : ℚ) = ((y i).den : ℚ) * y i := by
      have h := Rat.num_div_den (y i)
      rw [div_eq_iff (by exact_mod_cast (y i).den_nz)] at h
      rw [h]; ring
    rw [castL_apply, Pi.smul_apply, zsmul_eq_mul, hcast]
    push_cast
    rw [hnum]
    ring

/-! ### Spreading out preserves the rank -/

/-- The `ℚ`-span of the rational points of an integral lattice has the same dimension as the
lattice. -/
lemma spread_finrank (L : Submodule ℤ (ι → ℤ)) :
    Module.finrank ℚ (spread L) = Module.finrank ℤ L := by
  have h1 : Module.finrank ℚ (spread L) =
      Module.finrank ℤ ↥(L.map (castL (ι := ι))) :=
    Submodule.finrank_span_eq_finrank ℚ (L.map (castL (ι := ι)))
  have h2 : Module.finrank ℤ ↥(L.map (castL (ι := ι))) = Module.finrank ℤ L := by
    have hinj : Function.Injective ((castL (ι := ι)).comp L.subtype) :=
      castL_injective.comp (fun a b h => Subtype.ext h)
    have hr := LinearMap.finrank_range_of_inj hinj
    rw [show LinearMap.range ((castL (ι := ι)).comp L.subtype) =
        L.map (castL (ι := ι)) from ?_] at hr
    · exact hr
    · ext x
      simp only [LinearMap.mem_range, Submodule.mem_map]
      constructor
      · rintro ⟨v, rfl⟩; exact ⟨↑v, v.2, rfl⟩
      · rintro ⟨v, hv, rfl⟩; exact ⟨⟨v, hv⟩, rfl⟩
  rw [h1, h2]

/-! ### The standard form is nondegenerate -/

lemma stdB_nondegenerate : (stdB (ι := ι)).Nondegenerate := by
  constructor
  · intro x hx
    ext i
    have h := hx (Pi.single i 1)
    rw [stdB_apply] at h
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero] at h
    simpa using h
  · intro y hy
    ext i
    have h := hy (Pi.single i 1)
    rw [stdB_apply] at h
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul] at h
    simpa using h

/-! ### Integral points of a rational subspace span it -/

/-- If `I ⊆ ℚ^ι` is a `ℤ`-submodule meeting every rational line (`hI`), then a rational subspace
`V` is the `ℚ`-span of its integral points relative to `I`. -/
lemma span_restrictScalars_inf (V : Submodule ℚ (ι → ℚ)) (I : Submodule ℤ (ι → ℚ))
    (hI : ∀ y : ι → ℚ, ∃ M : ℤ, M ≠ 0 ∧ M • y ∈ I) :
    Submodule.span ℚ (↑(V.restrictScalars ℤ ⊓ I) : Set (ι → ℚ)) = V := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    intro x hx
    exact hx.1
  · intro y hy
    obtain ⟨M, hM, hMI⟩ := hI y
    have hMsmul : M • y = (M : ℚ) • y := by
      ext i
      rw [Pi.smul_apply, Pi.smul_apply, zsmul_eq_mul, smul_eq_mul]
    have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM
    have hy_eq : y = ((M : ℚ))⁻¹ • (M • y) := by
      rw [hMsmul, inv_smul_smul₀ hMq]
    have hMV : M • y ∈ V.restrictScalars ℤ := by
      rw [hMsmul]
      exact Submodule.smul_mem _ _ hy
    rw [hy_eq]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (show M • y ∈ V.restrictScalars ℤ ⊓ I from ⟨hMV, hMI⟩))

/-! ### The orthogonal lattice spreads out to the orthogonal complement -/

/-- The rational points of `orthLat Λ` span the orthogonal complement of the rational points
of `Λ`, for the standard form on `ℚ^ι`. -/
lemma spread_orthLat_eq_orthogonal (Λ : Submodule ℤ (ι → ℤ)) :
    spread (orthLat Λ) = stdB.orthogonal (spread Λ) := by
  have hAI : (stdB.orthogonal (spread Λ)).restrictScalars ℤ ⊓
        LinearMap.range (castL (ι := ι)) = (orthLat Λ).map (castL (ι := ι)) := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨hyV, hyI⟩
      obtain ⟨z, rfl⟩ := hyI
      refine Submodule.mem_map.mpr ⟨z, ?_, rfl⟩
      rw [mem_orthLat]
      intro x hx
      have hxV : castL x ∈ spread Λ := by
        rw [spread_eq_span_image]
        exact Submodule.subset_span ⟨x, hx, rfl⟩
      have h0 : stdB (castL x) (castL z) = 0 := hyV (castL x) hxV
      rw [stdB_castL] at h0
      have hz : dotI x z = 0 := by exact_mod_cast h0
      rwa [dotI_comm]
    · rintro y ⟨a, ha, rfl⟩
      constructor
      · change castL a ∈ stdB.orthogonal (spread Λ)
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro n hn
        have hle : spread Λ ≤ LinearMap.ker (stdB.flip (castL a)) := by
          rw [spread_eq_span_image, Submodule.span_le]
          rintro x ⟨v, hv, rfl⟩
          show stdB (castL v) (castL a) = 0
          rw [stdB_castL, dotI_comm]
          simp [mem_orthLat.mp ha v hv]
        exact hle hn
      · exact LinearMap.mem_range.mpr ⟨a, rfl⟩
  calc spread (orthLat Λ)
      = Submodule.span ℚ (↑((orthLat Λ).map (castL (ι := ι))) : Set (ι → ℚ)) := rfl
    _ = Submodule.span ℚ (↑((stdB.orthogonal (spread Λ)).restrictScalars ℤ ⊓
          LinearMap.range (castL (ι := ι))) : Set (ι → ℚ)) := by rw [hAI]
    _ = stdB.orthogonal (spread Λ) :=
        span_restrictScalars_inf _ _ castL_denom

/-! ### The rank formula -/

theorem rk_orthLat {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Submodule ℤ (ι → ℤ))
    (h : IsPrimLat Λ) : rk (orthLat Λ) = Fintype.card ι - rk Λ := by
  have h1 : Module.finrank ℚ (spread (orthLat Λ)) = Module.finrank ℤ (orthLat Λ) :=
    spread_finrank (orthLat Λ)
  have h2 : spread (orthLat Λ) = stdB.orthogonal (spread Λ) := spread_orthLat_eq_orthogonal Λ
  have h3 : Module.finrank ℚ (stdB.orthogonal (spread Λ)) =
      Module.finrank ℚ (ι → ℚ) - Module.finrank ℚ (spread Λ) :=
    LinearMap.BilinForm.finrank_orthogonal stdB_nondegenerate (spread Λ)
  have h4 : Module.finrank ℚ (spread Λ) = Module.finrank ℤ Λ := spread_finrank Λ
  have h5 : Module.finrank ℚ (ι → ℚ) = Fintype.card ι := Module.finrank_fintype_fun_eq_card ℚ
  unfold rk
  rw [← h1, h2, h3, h5, h4]

end Work.HP.numaux
