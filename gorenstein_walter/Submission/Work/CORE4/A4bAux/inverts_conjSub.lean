import Mathlib
import Submission.Work.CORE4.Defs

namespace Work.CORE4.A4bAux

/-- If `s` inverts `K` (`s * x * s⁻¹ = x⁻¹` for all `x ∈ K`) and `e` commutes with `s`, then
`s` inverts the conjugate `K^e = e K e⁻¹` of `K` by `e`. -/
theorem inverts_conjSub {G : Type*} [Group G] {s e : G} (h : e * s = s * e) {K : Subgroup G}
    (hinv : Work.GW2.Inverts s K) : Work.GW2.Inverts s (Work.GW2.conjSub e K) := by
  intro y hy
  rw [Work.GW2.conjSub, Subgroup.mem_map] at hy
  obtain ⟨k, hk, hky⟩ := hy
  rw [← hky]
  show s * (e * k * e⁻¹) * s⁻¹ = (e * k * e⁻¹)⁻¹
  calc s * (e * k * e⁻¹) * s⁻¹
      = (s * e) * k * (s * e)⁻¹ := by group
    _ = e * (s * k * s⁻¹) * e⁻¹ := by rw [← h]; group
    _ = e * k⁻¹ * e⁻¹ := by rw [hinv k hk]
    _ = (e * k * e⁻¹)⁻¹ := by group

end Work.CORE4.A4bAux
