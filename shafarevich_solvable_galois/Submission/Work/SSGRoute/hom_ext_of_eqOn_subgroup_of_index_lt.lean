import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Prime.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- If two group homomorphisms `G →* M` into a commutative group `M` of prime cardinality `l`
agree on a subgroup `H ≤ G` whose index is nonzero and strictly smaller than `l`, then they are
equal. -/
lemma hom_ext_of_eqOn_subgroup_of_index_lt {G M : Type*} [Group G] [CommGroup M]
    (H : Subgroup G) (l : ℕ) (hl : l.Prime) (hcard : Nat.card M = l)
    (hHpos : H.index ≠ 0) (hidx : H.index < l)
    {φ₁ φ₂ : G →* M} (h : ∀ x ∈ H, φ₁ x = φ₂ x) : φ₁ = φ₂ := by
  -- Work with the pointwise quotient `ψ = φ₁ * φ₂⁻¹`, which is a homomorphism since `M` is
  -- commutative.  We show `ψ = 1`.
  set ψ : G →* M := φ₁ * φ₂⁻¹ with hψdef
  -- `ψ` vanishes on `H`, so `H ≤ ker ψ`.
  have hHψ : H ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    show ψ x = 1
    rw [hψdef, MonoidHom.mul_apply, MonoidHom.inv_apply, h x hx, mul_inv_cancel]
  -- The index of any subgroup containing `H` divides the index of `H` and is at most it.
  have hKdvdH : ψ.ker.index ∣ H.index := Subgroup.index_dvd_of_le hHψ
  -- The index of the kernel is the cardinality of the image, which divides `l`.
  have hKdvdL : ψ.ker.index ∣ l := by
    have h2 : Nat.card ↥ψ.range * ψ.range.index = Nat.card M := Subgroup.card_mul_index ψ.range
    rw [Subgroup.index_ker, ← hcard]
    exact ⟨ψ.range.index, h2.symm⟩
  have hKleH : ψ.ker.index ≤ H.index := Nat.le_of_dvd (Nat.pos_of_ne_zero hHpos) hKdvdH
  -- As `l` is prime and `H.index < l`, the index of the kernel must be `1`.
  have hK : ψ.ker.index = 1 := by
    rcases hl.eq_one_or_self_of_dvd ψ.ker.index hKdvdL with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hKleH
      exact absurd hKleH (not_le.mpr hidx)
  have hψ : ψ = 1 := MonoidHom.ker_eq_top_iff.mp (Subgroup.index_eq_one.mp hK)
  apply MonoidHom.ext
  intro g
  have hg : φ₁ g * (φ₂ g)⁻¹ = 1 := by
    have hh := MonoidHom.ext_iff.mp hψ g
    simp only [hψdef, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.one_apply] at hh
    exact hh
  exact mul_inv_eq_one.mp hg

end Work.SSGRoute
