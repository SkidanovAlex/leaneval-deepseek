import Submission.Work.ZJB2.Defs

/-!
# GW design 17, item B (ZJB2) — leaf `ivMethod` (T51.IV-alg) — PROVED

Source: Glauberman 1968, p. 1120 step (IV); reused at the end of Theorem 5.2 (p. 1122).
Pure algebra: `V = xWx⁻¹`; `GoodFor S V` at `x` gives `x = c₁ m`, at `x g` gives `x g = d n`; then
`g = (m⁻¹ c₁⁻¹ d m)(m⁻¹ n)` with `m⁻¹ c₁⁻¹ d m ∈ C(m⁻¹Vm) = C(W)`.
-/

namespace Work.ZJB

open Work.GW2 Subgroup

theorem ivMethod (G : Type) [Group G] : IVMethodProp G := by
  intro S Cond hgood W hW ⟨x, hVS, hc⟩ g hg
  set V := W.map (MulAut.conj x).toMonoidHom with hV
  have hmemV : ∀ w ∈ W, x * w * x⁻¹ ∈ V := fun w hw =>
    Subgroup.mem_map.mpr ⟨w, hw, by simp [MulAut.conj_apply]⟩
  have hVinv : ∀ v ∈ V, ∃ w ∈ W, v = x * w * x⁻¹ := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
    exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
  obtain ⟨c₁, m, hc₁, hm, hx⟩ := hgood V hVS hc x (by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := hVinv v hv
    have : x⁻¹ * (x * w * x⁻¹) * x = w := by group
    rw [this]; exact hW hw)
  obtain ⟨d, n, hd, hn, hxg⟩ := hgood V hVS hc (x * g) (by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := hVinv v hv
    have : (x * g)⁻¹ * (x * w * x⁻¹) * (x * g) = g⁻¹ * w * g := by group
    rw [this]; exact hg w hw)
  refine ⟨m⁻¹ * c₁⁻¹ * d * m, m⁻¹ * n, ?_, Subgroup.mul_mem _ (Subgroup.inv_mem _ hm) hn, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hv := hmemV w hw
    have h1 := (Subgroup.mem_centralizer_iff.mp hc₁) _ hv
    have h2 := (Subgroup.mem_centralizer_iff.mp hd) _ hv
    set v := x * w * x⁻¹ with hvdef
    have hw' : w = m⁻¹ * v * m := by
      have : w = x⁻¹ * v * x := by rw [hvdef]; group
      rw [this, hx]
      calc (c₁ * m)⁻¹ * v * (c₁ * m) = m⁻¹ * (c₁⁻¹ * (v * c₁)) * m := by group
        _ = m⁻¹ * (c₁⁻¹ * (c₁ * v)) * m := by rw [h1]
        _ = m⁻¹ * v * m := by group
    have h1' : c₁⁻¹ * v = v * c₁⁻¹ := by
      calc c₁⁻¹ * v = c₁⁻¹ * (v * c₁) * c₁⁻¹ := by group
        _ = c₁⁻¹ * (c₁ * v) * c₁⁻¹ := by rw [h1]
        _ = v * c₁⁻¹ := by group
    have h3 : v * (c₁⁻¹ * d) = (c₁⁻¹ * d) * v := by
      calc v * (c₁⁻¹ * d) = (v * c₁⁻¹) * d := by group
        _ = c₁⁻¹ * v * d := by rw [h1']
        _ = c₁⁻¹ * (v * d) := by group
        _ = c₁⁻¹ * (d * v) := by rw [h2]
        _ = (c₁⁻¹ * d) * v := by group
    rw [hw']
    calc m⁻¹ * v * m * (m⁻¹ * c₁⁻¹ * d * m) = m⁻¹ * (v * (c₁⁻¹ * d)) * m := by group
      _ = m⁻¹ * ((c₁⁻¹ * d) * v) * m := by rw [h3]
      _ = m⁻¹ * c₁⁻¹ * d * m * (m⁻¹ * v * m) := by group
  · calc g = x⁻¹ * (x * g) := by group
      _ = (c₁ * m)⁻¹ * (d * n) := by rw [← hx, ← hxg]
      _ = m⁻¹ * c₁⁻¹ * d * m * (m⁻¹ * n) := by group

end Work.ZJB


