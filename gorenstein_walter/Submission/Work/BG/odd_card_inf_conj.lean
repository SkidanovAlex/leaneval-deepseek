import Mathlib
import Submission.Work.GLUE.Defs

namespace Work.BG

theorem odd_card_inf_conj {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) (G1 : Subgroup G)
    (hH : D.H ≤ G1)
    (hcl : ∀ x y : G, x ∈ G1 → y ∈ G1 → orderOf x = 2 → orderOf y = 2 →
      ∃ g ∈ G1, g * x * g⁻¹ = y)
    {a : G} (ha : a ∉ G1) :
    Odd (Nat.card (G1 ⊓ G1.map (MulAut.conj a).toMonoidHom : Subgroup G)) := by
  rw [← Nat.not_even_iff_odd]
  intro hEven
  -- `t` lies in `H ≤ G1`.
  have htH : D.t ∈ D.H := by
    simp only [Work.GW2.BGData.H, Subgroup.mem_centralizer_singleton_iff]
  have htG1 : D.t ∈ G1 := hH htH
  -- an even-order subgroup contains an involution
  have h2dvd : 2 ∣ Nat.card (G1 ⊓ G1.map (MulAut.conj a).toMonoidHom : Subgroup G) :=
    even_iff_two_dvd.mp hEven
  obtain ⟨x, hxord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(G1 ⊓ G1.map (MulAut.conj a).toMonoidHom)) 2 h2dvd
  have hxmem : (x : G) ∈ G1 ⊓ G1.map (MulAut.conj a).toMonoidHom := x.2
  have hxG1 : (x : G) ∈ G1 := (Subgroup.mem_inf.mp hxmem).1
  have hxmap : (x : G) ∈ G1.map (MulAut.conj a).toMonoidHom := (Subgroup.mem_inf.mp hxmem).2
  have hxordG : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe, hxord]
  -- `a⁻¹ x a ∈ G1`
  obtain ⟨y, hyG1, hyeq⟩ := Subgroup.mem_map.mp hxmap
  have hy2 : a * y * a⁻¹ = (x : G) := by simpa using hyeq
  have hconjmem : a⁻¹ * (x : G) * a ∈ G1 := by
    have h1 : a⁻¹ * (x : G) * a = y := by rw [← hy2]; group
    rw [h1]; exact hyG1
  -- `x` is `G1`-conjugate to `t`
  obtain ⟨g, hgG1, hgeq⟩ := hcl (x : G) D.t hxG1 htG1 hxordG D.t_order
  have hxu : (x : G) = g⁻¹ * D.t * g := by rw [← hgeq]; group
  -- set `u = g a`; then `u⁻¹ t u = a⁻¹ x a ∈ G1`
  set u : G := g * a with hu
  have hmemU : u⁻¹ * D.t * u ∈ G1 := by
    have h1 : u⁻¹ * D.t * u = a⁻¹ * (x : G) * a := by rw [hu, hxu]; group
    rw [h1]; exact hconjmem
  have hordU : orderOf (u⁻¹ * D.t * u) = 2 := by
    have h1 : u⁻¹ * D.t * u = (MulAut.conj (u⁻¹)).toMonoidHom D.t := by
      simp
    rw [h1, orderOf_injective (MulAut.conj (u⁻¹)).toMonoidHom
      (MulAut.conj (u⁻¹)).injective D.t, D.t_order]
  -- both `u⁻¹ t u` and `t` are involutions in `G1`, hence conjugate inside `G1`
  obtain ⟨h, hhG1, hheq⟩ := hcl (u⁻¹ * D.t * u) D.t hmemU htG1 hordU D.t_order
  set w : G := h * u⁻¹ with hw
  have hwconj : w * D.t * w⁻¹ = D.t := by
    have h1 : w * D.t * w⁻¹ = h * (u⁻¹ * D.t * u) * h⁻¹ := by rw [hw]; group
    rw [h1, hheq]
  have hwH : w ∈ D.H := by
    simp only [Work.GW2.BGData.H, Subgroup.mem_centralizer_singleton_iff]
    calc w * D.t = w * D.t * w⁻¹ * w := by group
      _ = D.t * w := by rw [hwconj]
  have hwG1 : w ∈ G1 := hH hwH
  have huinvG1 : u⁻¹ ∈ G1 := by
    have h1 : u⁻¹ = h⁻¹ * w := by rw [hw]; group
    rw [h1]; exact mul_mem (inv_mem hhG1) hwG1
  have huG1 : u ∈ G1 := by simpa using inv_mem huinvG1
  have haG1 : a ∈ G1 := by
    have h1 : a = g⁻¹ * u := by rw [hu]; group
    rw [h1]; exact mul_mem (inv_mem hgG1) huG1
  exact ha haG1

end Work.BG
