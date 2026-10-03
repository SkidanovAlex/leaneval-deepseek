import Mathlib
import Submission.Work.OROneRel.exists_hnn_top_of_normal_vertex

set_option autoImplicit false

namespace Work.OROneRel

/-- **A normal subgroup with quotient `ℤ` realises `G` as an HNN extension.**

If `φ : G →* Multiplicative ℤ` has `φ t = ofAdd 1`, kernel exactly `H`, and `G = ⟨H, t⟩`, then the
conjugation automorphism `h ↦ t h t⁻¹` of `H` makes `G` the HNN extension of `H` with both
associated subgroups equal to the whole base group.

This is the `φ`-form of `Work.OROneRel.exists_hnn_top_of_normal_vertex`: from `H = ker φ` one gets
that `H` is normal and that `t ^ m ∉ H` for `m ≠ 0`, since `φ (t ^ m) = (ofAdd 1) ^ m = ofAdd m`
vanishes only for `m = 0`. -/
theorem hnnKernelForm {G : Type*} [Group G] (H : Subgroup G) (t : G)
    (φ : G →* Multiplicative ℤ) (hφt : φ t = Multiplicative.ofAdd 1)
    (hH : ∀ g : G, g ∈ H ↔ φ g = 1)
    (hgen : Subgroup.closure ((H : Set G) ∪ {t}) = ⊤) :
    ∃ (ψ : (⊤ : Subgroup ↥H) ≃* (⊤ : Subgroup ↥H)),
      Nonempty (HNNExtension ↥H ⊤ ⊤ ψ ≃* G) ∧
      (∀ a : (⊤ : Subgroup ↥H),
        (((ψ a : (⊤ : Subgroup ↥H)) : ↥H) : G) = t * (((a : (⊤ : Subgroup ↥H)) : ↥H) : G) * t⁻¹) := by
  -- `H` is the kernel of `φ`, hence normal.
  have hker : H = φ.ker := by
    ext g
    rw [MonoidHom.mem_ker]
    exact hH g
  have hN : H.Normal := hker ▸ MonoidHom.normal_ker φ
  -- no nonzero power of `t` lies in `H`, because `φ t` generates `Multiplicative ℤ`.
  have ht : ∀ m : ℤ, m ≠ 0 → t ^ m ∉ H := by
    intro m hm hmem
    have h1 : φ (t ^ m) = 1 := (hH (t ^ m)).mp hmem
    rw [map_zpow, hφt] at h1
    have h2 : m = 0 := by
      have := congrArg Multiplicative.toAdd h1
      simpa using this
    exact hm h2
  obtain ⟨ψ, hψ, hiso⟩ :=
    exists_hnn_top_of_normal_vertex H hN t hgen ht
  exact ⟨ψ, hiso, fun a => hψ (a : ↥H)⟩

end Work.OROneRel
