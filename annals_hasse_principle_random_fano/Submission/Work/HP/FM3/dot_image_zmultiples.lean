import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Transf.Basic

/-!
# The image of `z ↦ ⟨v,z⟩` on a lattice is a principal subgroup of `ℤ`

For `v` in the dual lattice of `L`, the set of values `⟨v,z⟩`, `z ∈ L`, is an additive subgroup
of `ℤ` (all values are integers), hence of the form `dℤ` with `d ≥ 1` when nonzero; moreover `d`
is attained.  This is the normalisation that makes `v/d` a primitive dual vector.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.FM3

open Work.HP Work.HP.Transf

variable {ι : Type*} [Fintype ι]

theorem dot_image_zmultiples (L : Submodule ℤ (ι → ℝ)) (v : ι → ℝ)
    (hv : v ∈ dualLat L) (hne : ∃ z ∈ L, dotR v z ≠ 0) :
    ∃ d : ℤ, 0 < d ∧ (∃ w ∈ L, dotR v w = d) ∧
      ∀ z ∈ L, ∃ k : ℤ, dotR v z = k * d := by
  -- the `ℤ`-linear functional `z ↦ ⟨v,z⟩` on `L`
  have hspec : ∀ z : ↥L, ∃ k : ℤ, dotR v (z : ι → ℝ) = (k : ℝ) := fun z => hv.2 z.1 z.2
  let φfun : ↥L → ℤ := fun z => Classical.choose (hspec z)
  have hφ : ∀ z : ↥L, (φfun z : ℝ) = dotR v (z : ι → ℝ) :=
    fun z => (Classical.choose_spec (hspec z)).symm
  have hadd : ∀ a b : ↥L, φfun (a + b) = φfun a + φfun b := by
    intro a b
    refine Int.cast_injective (α := ℝ) ?_
    rw [Int.cast_add, hφ (a + b), hφ a, hφ b, Submodule.coe_add]
    exact dotR_add_right _ _ _
  have hsmul : ∀ (c : ℤ) (a : ↥L), φfun (c • a) = c * φfun a := by
    intro c a
    refine Int.cast_injective (α := ℝ) ?_
    rw [Int.cast_mul, hφ (c • a), hφ a, Submodule.coe_smul,
      ← Int.cast_smul_eq_zsmul ℝ c (a : ι → ℝ), dotR_smul_right]
  let φ : ↥L →ₗ[ℤ] ℤ := { toFun := φfun, map_add' := hadd, map_smul' := hsmul }
  have hφ' : ∀ z : ↥L, (φ z : ℝ) = dotR v (z : ι → ℝ) := hφ
  let I : Ideal ℤ := LinearMap.range φ
  have hmemI : ∀ n : ℤ, n ∈ I ↔ ∃ z : ↥L, φ z = n := fun n => Iff.rfl
  -- `I` is nonzero
  obtain ⟨z0, hz0, hz0ne⟩ := hne
  have hz0I : φ ⟨z0, hz0⟩ ∈ I := ⟨⟨z0, hz0⟩, rfl⟩
  have hne0 : φ ⟨z0, hz0⟩ ≠ 0 := by
    intro h
    refine hz0ne ?_
    have h1 := hφ' ⟨z0, hz0⟩
    rw [h] at h1
    simpa using h1.symm
  have hIne : I ≠ ⊥ := fun h => hne0 (by rw [h] at hz0I; exact (Submodule.mem_bot ℤ).mp hz0I)
  -- generator, made positive
  set g : ℤ := Submodule.IsPrincipal.generator I with hg
  have hgmem : g ∈ I := Submodule.IsPrincipal.generator_mem I
  have hgdvd : ∀ n ∈ I, g ∣ n := fun n hn => (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp hn
  have hgne : g ≠ 0 := by
    intro h
    refine hIne (Submodule.eq_bot_iff I |>.mpr fun n hn => ?_)
    have h1 := hgdvd n hn
    rw [h] at h1
    simpa using h1
  refine ⟨|g|, abs_pos.mpr hgne, ?_, ?_⟩
  · -- attainability
    have hmemabs : |g| ∈ I := by
      rcases le_or_gt 0 g with h | h
      · rwa [abs_of_nonneg h]
      · rw [abs_of_neg h]; exact Submodule.neg_mem _ hgmem
    obtain ⟨z, hz⟩ := (hmemI |g|).mp hmemabs
    exact ⟨(z : ι → ℝ), z.2, by rw [← hφ' z, hz]⟩
  · -- divisibility
    intro z hz
    have h1 : g ∣ φ ⟨z, hz⟩ := hgdvd _ ⟨⟨z, hz⟩, rfl⟩
    have h2 : |g| ∣ φ ⟨z, hz⟩ := (abs_dvd g (φ ⟨z, hz⟩)).mpr h1
    obtain ⟨k, hk⟩ := h2
    refine ⟨k, ?_⟩
    have h3 : (φ ⟨z, hz⟩ : ℝ) = dotR v z := hφ' ⟨z, hz⟩
    rw [← h3, hk]
    push_cast
    ring

end Work.HP.FM3
