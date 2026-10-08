import Mathlib
import Submission.Work.CORE4.Defs

namespace Work.CORE4.ConjSub

/-- The defining unfolding of `K^g`: `a ∈ K^g ↔ ∃ k ∈ K, g * k * g⁻¹ = a`. -/
theorem mem_conjSub {G : Type} [Group G] {g a : G} {K : Subgroup G} :
    a ∈ Work.GW2.conjSub g K ↔ ∃ k ∈ K, g * k * g⁻¹ = a := by
  rw [Work.GW2.conjSub, Subgroup.mem_map]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

/-- **Conjugation of subgroups is a right action:** `(K^h)^g = K^{gh}` for
`K^g = Work.GW2.conjSub g K = g K g⁻¹`. -/
theorem conjSub_mul {G : Type} [Group G] (g h : G) (K : Subgroup G) :
    Work.GW2.conjSub (g * h) K = Work.GW2.conjSub g (Work.GW2.conjSub h K) := by
  ext a
  simp only [Work.GW2.conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨k, hk, hk'⟩
    exact ⟨h * k * h⁻¹, ⟨k, hk, rfl⟩, by rw [← hk']; group⟩
  · rintro ⟨b, ⟨k, hk, hk'⟩, hb⟩
    exact ⟨k, hk, by rw [← hb, ← hk']; group⟩

end Work.CORE4.ConjSub
