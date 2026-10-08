import Mathlib

namespace Work.CORE3.LeFourAux

/-- Auxiliary statement: for one involution `b` (with `b ^ 2 = 1`) satisfying
`b * v * b = h * v⁻¹ * h⁻¹`, `b * v3 * b = v3⁻¹` and `b * v2 * b ∈ V`,
where `v = v2 * v3`, `v2 ^ 2 = 1`, `v3 ∈ U`, `v2 ∈ V`, `U` and `V` commute
elementwise, and `h` centralises `v3`, we get `b * v2 * b = h * v2 * h⁻¹`.

The proof: write `b * v * b = (b * v2 * b) * (b * v3 * b) = (b * v2 * b) * v3⁻¹`
on the left, and
`h * v⁻¹ * h⁻¹ = h * (v3⁻¹ * v2⁻¹) * h⁻¹ = (h * v3⁻¹ * h⁻¹) * (h * v2 * h⁻¹)
= v3⁻¹ * (h * v2 * h⁻¹)` on the right. Hence
`(b * v2 * b) * v3⁻¹ = v3⁻¹ * (h * v2 * h⁻¹)`, so
`h * v2 * h⁻¹ = v3 * (b * v2 * b) * v3⁻¹`. Since `b * v2 * b ∈ V` and `v3 ∈ U`
commute, `v3 * (b * v2 * b) * v3⁻¹ = b * v2 * b`, giving the claim. -/
private lemma key {G : Type} [Group G] {V U : Subgroup G}
    {b h v v2 v3 : G}
    (hcomm : ∀ u ∈ U, ∀ w ∈ V, u * w = w * u)
    (hv3 : v3 ∈ U) (hdecomp : v = v2 * v3)
    (hv22 : v2 * v2 = 1) (hsq : b * b = 1)
    (hA : b * v2 * b ∈ V)
    (hmain : b * v * b = h * v⁻¹ * h⁻¹)
    (hbU : b * v3 * b = v3⁻¹)
    (hhU : h * v3 * h⁻¹ = v3) :
    b * v2 * b = h * v2 * h⁻¹ := by
  have hv2inv : v2⁻¹ = v2 := inv_eq_of_mul_eq_one_right hv22
  have hhinv : h * v3⁻¹ * h⁻¹ = v3⁻¹ := by
    rw [show h * v3⁻¹ * h⁻¹ = (h * v3 * h⁻¹)⁻¹ by group]
    rw [hhU]
  have hL : b * v * b = (b * v2 * b) * (b * v3 * b) := by
    rw [hdecomp]
    calc b * (v2 * v3) * b
        = b * v2 * (b * b) * v3 * b := by rw [hsq]; group
      _ = (b * v2 * b) * (b * v3 * b) := by group
  have hR : h * v⁻¹ * h⁻¹ = v3⁻¹ * (h * v2 * h⁻¹) := by
    rw [hdecomp, mul_inv_rev, hv2inv]
    calc h * (v3⁻¹ * v2) * h⁻¹
        = (h * v3⁻¹ * h⁻¹) * (h * v2 * h⁻¹) := by group
      _ = v3⁻¹ * (h * v2 * h⁻¹) := by rw [hhinv]
  have h1' : (b * v2 * b) * v3⁻¹ = v3⁻¹ * (h * v2 * h⁻¹) := by
    rw [hL, hbU, hR] at hmain
    exact hmain
  have hxy : h * v2 * h⁻¹ = v3 * (b * v2 * b) * v3⁻¹ := by
    calc h * v2 * h⁻¹
        = v3 * (v3⁻¹ * (h * v2 * h⁻¹)) := by group
      _ = v3 * ((b * v2 * b) * v3⁻¹) := by rw [← h1']
      _ = v3 * (b * v2 * b) * v3⁻¹ := by group
  have hc := hcomm v3 hv3 (b * v2 * b) hA
  rw [hxy, hc]
  group

theorem ConjEqOfDecomp {G : Type} [Group G] {V U : Subgroup G}
    {b1 b2 h v v2 v3 : G}
    (hcomm : ∀ u ∈ U, ∀ w ∈ V, u * w = w * u)
    (hv2 : v2 ∈ V) (hv3 : v3 ∈ U) (hdecomp : v = v2 * v3) (hv22 : v2 * v2 = 1)
    (hb1sq : b1 * b1 = 1) (hb2sq : b2 * b2 = 1)
    (hA : b1 * v2 * b1 ∈ V) (hB : b2 * v2 * b2 ∈ V)
    (h1 : b1 * v * b1 = h * v⁻¹ * h⁻¹) (h2 : b2 * v * b2 = h * v⁻¹ * h⁻¹)
    (hb1U : b1 * v3 * b1 = v3⁻¹) (hb2U : b2 * v3 * b2 = v3⁻¹)
    (hhU : h * v3 * h⁻¹ = v3) :
    b1 * v2 * b1 = h * v2 * h⁻¹ ∧ b2 * v2 * b2 = h * v2 * h⁻¹ :=
  ⟨key hcomm hv3 hdecomp hv22 hb1sq hA h1 hb1U hhU,
   key hcomm hv3 hdecomp hv22 hb2sq hB h2 hb2U hhU⟩

end Work.CORE3.LeFourAux
