import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC.C6

/-- **The multiplication map of a linearly disjoint descent.** Let `F` be an intermediate field of
`K/𝕜`, `L/𝕜` a subextension with `𝕜 → L → K` a tower, `F` and `L` linearly disjoint, the tensor
product `F ⊗[𝕜] L` a field (this holds when `L/𝕜` is algebraic), and `F · L = K`. Then the
multiplication map `F ⊗[𝕜] L → K`, `a ⊗ l ↦ a * l`, is a `𝕜`-algebra isomorphism.

Route: build it with `Algebra.TensorProduct.lift`; it is injective because its source is a field and
its target is nontrivial, and surjective because its image is a `IntermediateField` containing `F`
(through `a ⊗ 1 ↦ a`) and the image of `L` (through `1 ⊗ l ↦ l`), hence contains
`F ⊔ (IsScalarTower.toAlgHom 𝕜 L K).fieldRange = ⊤`.  The two displayed equations are
`Algebra.TensorProduct.lift_tmul`.  (Alternatively Mathlib's
`Subalgebra.LinearDisjoint.mulMapLeftOfSupEqTop` may shorten the work.) -/
theorem exists_tensorAlgEquiv {𝕜 K L : Type} [Field 𝕜] [Field K] [Algebra 𝕜 K]
    [Field L] [Algebra 𝕜 L] [Algebra L K] [IsScalarTower 𝕜 L K]
    (F : IntermediateField 𝕜 K) (hLI : F.LinearDisjoint L)
    (hfield : IsField (TensorProduct 𝕜 ↥F L))
    (hsup : F ⊔ (IsScalarTower.toAlgHom 𝕜 L K).fieldRange = ⊤) :
    ∃ e : TensorProduct 𝕜 ↥F L ≃ₐ[𝕜] K,
      (∀ a : ↥F, e (TensorProduct.tmul 𝕜 a 1) = a) ∧
        (∀ l : L, e (TensorProduct.tmul 𝕜 (1 : ↥F) l) = algebraMap L K l) := by
  -- The linear disjointness hypothesis is not needed below: injectivity is supplied by the
  -- (stronger, and here explicitly assumed) requirement that the tensor product is a field.
  have _ := hLI
  -- Keep the tensor product in scope with the `𝕜`-algebra structure of the statement.
  have hcomm : ∀ (a : ↥F) (l : L),
      Commute (F.val a) (IsScalarTower.toAlgHom 𝕜 L K l) := fun a l => mul_comm _ _
  -- The multiplication map `F ⊗[𝕜] L → K`, `a ⊗ l ↦ a * l`.
  let φ : TensorProduct 𝕜 ↥F L →ₐ[𝕜] K :=
    Algebra.TensorProduct.lift F.val (IsScalarTower.toAlgHom 𝕜 L K) hcomm
  have hφa : ∀ a : ↥F, φ (TensorProduct.tmul 𝕜 a (1 : L)) = (a : K) := by
    intro a
    dsimp only [φ]
    rw [show TensorProduct.tmul 𝕜 a (1 : L) = a ⊗ₜ[𝕜] (1 : L) from rfl]
    rw [Algebra.TensorProduct.lift_tmul]
    simp
  have hφl : ∀ l : L, φ (TensorProduct.tmul 𝕜 (1 : ↥F) l) = algebraMap L K l := by
    intro l
    dsimp only [φ]
    rw [show TensorProduct.tmul 𝕜 (1 : ↥F) l = (1 : ↥F) ⊗ₜ[𝕜] l from rfl]
    rw [Algebra.TensorProduct.lift_tmul]
    simp
  -- The image of `φ` is closed under inverses, i.e. it is a subfield.
  have hinv : ∀ x ∈ φ.range, x⁻¹ ∈ φ.range := by
    intro x hx
    rw [AlgHom.mem_range] at hx ⊢
    obtain ⟨a, rfl⟩ := hx
    by_cases ha : a = 0
    · refine ⟨0, ?_⟩
      rw [ha, map_zero, inv_zero]
    · obtain ⟨b, hb⟩ := hfield.mul_inv_cancel ha
      refine ⟨b, ?_⟩
      have h1 : φ a * φ b = 1 := by rw [← map_mul, hb]; exact φ.map_one'
      exact eq_inv_of_mul_eq_one_right h1
  -- The image, as an intermediate field.
  let H : IntermediateField 𝕜 K := φ.range.toIntermediateField hinv
  have hFH : F ≤ H := by
    intro x hx
    change x ∈ φ.range
    rw [AlgHom.mem_range]
    exact ⟨TensorProduct.tmul 𝕜 ⟨x, hx⟩ (1 : L), hφa ⟨x, hx⟩⟩
  have hGH : (IsScalarTower.toAlgHom 𝕜 L K).fieldRange ≤ H := by
    intro y hy
    change y ∈ φ.range
    rw [AlgHom.mem_fieldRange] at hy
    obtain ⟨l, rfl⟩ := hy
    rw [AlgHom.mem_range]
    exact ⟨TensorProduct.tmul 𝕜 (1 : ↥F) l, hφl l⟩
  have htop : H = ⊤ := le_antisymm le_top (hsup ▸ sup_le hFH hGH)
  have hsub : H.toSubalgebra = ⊤ := by rw [htop]; rfl
  have hrange : φ.range = ⊤ := (toSubalgebra_toIntermediateField φ.range hinv).symm.trans hsub
  have hsurj : Function.Surjective φ := (AlgHom.range_eq_top φ).mp hrange
  -- Injectivity: the source is a field, so the kernel of `φ` is trivial.
  have hinj : Function.Injective φ := by
    intro x y hxy
    by_contra hne
    have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hsub
    have h1 : φ ((x - y) * b) = 1 := by rw [hb]; exact φ.map_one'
    rw [map_mul, map_sub, hxy, sub_self, zero_mul] at h1
    exact one_ne_zero h1.symm
  have hbij : Function.Bijective φ :=
    (Function.bijective_iff_existsUnique φ).mpr fun y => by
      obtain ⟨x, hx⟩ := hsurj y
      exact ⟨x, hx, fun z hz => hinj (hz.trans hx.symm)⟩
  refine ⟨AlgEquiv.ofBijective φ hbij, ?_, ?_⟩
  · intro a
    rw [AlgEquiv.ofBijective_apply]
    exact hφa a
  · intro l
    rw [AlgEquiv.ofBijective_apply]
    exact hφl l

end Work.MotC.C6
