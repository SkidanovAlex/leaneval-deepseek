import Mathlib

namespace Work.CORE3

/-- If `y * x * y⁻¹ = x⁻¹` and `K ≤ C_G(x)`, then `y K y⁻¹ ≤ C_G(x)`: conjugation by `y`
inverts `x`, hence preserves the set of elements commuting with `x` (conjugation by `y` is an
automorphism sending `C_G(x)` to `C_G(x⁻¹) = C_G(x)`).

Explicitly, for `k ∈ K` and `w = y * k * y⁻¹` one has `w * x * w⁻¹ = y * (k * x⁻¹ * k⁻¹) * y⁻¹
= y * x⁻¹ * y⁻¹ = x` because `k` centralizes `x`. -/
theorem map_conj_le_centralizer_of_conj_eq_inv {G : Type} [Group G] {x y : G} {K : Subgroup G}
    (hxy : y * x * y⁻¹ = x⁻¹) (hK : K ≤ Subgroup.centralizer ({x} : Set G)) :
    K.map (MulAut.conj y).toMonoidHom ≤ Subgroup.centralizer ({x} : Set G) := by
  -- `C_G(x⁻¹) = C_G(x)`: an element commuting with `x⁻¹` commutes with `x`.
  have hle : Subgroup.centralizer ({x⁻¹} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    have h := congrArg (fun t => x * t * x) hz
    have h' : x * z = z * x := by simpa [mul_assoc] using h
    exact h'.symm
  -- conjugation by `y` sends `{x}` to `{x⁻¹}`.
  have h3 : ((MulAut.conj y).toMonoidHom) '' ({x} : Set G) = ({x⁻¹} : Set G) := by
    rw [Set.image_singleton, Set.singleton_eq_singleton_iff]
    change MulAut.conj y x = x⁻¹
    rw [MulAut.conj_apply]
    exact hxy
  calc K.map (MulAut.conj y).toMonoidHom
      ≤ (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj y).toMonoidHom :=
        Subgroup.map_mono hK
    _ ≤ Subgroup.centralizer (((MulAut.conj y).toMonoidHom) '' ({x} : Set G)) :=
        Subgroup.map_centralizer_le_centralizer_image _ _
    _ = Subgroup.centralizer ({x⁻¹} : Set G) := by rw [h3]
    _ ≤ Subgroup.centralizer ({x} : Set G) := hle

end Work.CORE3
