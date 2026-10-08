import Mathlib
import Submission.Work.ZASS.Leaf9
import Submission.Work.ZASS2.ZassS

namespace Work.ZASS2

theorem zassS_equivariant {G X : Type} [Group G] [MulAction G X] {inf zero : X} {U : Subgroup G}
    (C : Work.GW2.ZassCoords G X inf zero U) {s : G} (hs2 : s * s = 1) (hsz : s • zero = inf)
    (hinv : Work.GW2.Inverts s (Work.Zassenhaus.pairStab G inf zero))
    (hα : ∀ h : Work.Zassenhaus.pairStab G inf zero, C.α h⁻¹ = (C.α h)⁻¹) :
    ∀ a y : C.E, a ≠ 0 → y ≠ 0 → Work.ZASS2.zassS C s (a ^ 2 * y) = Work.ZASS2.zassS C s y / a ^ 2 := by
  intro a y ha hy
  -- `a²` is a nonzero square, so it is `α h` for some `h ∈ H = G_{∞0}`.
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  obtain ⟨h, hh⟩ := (C.α_range (a ^ 2) ha2).mpr ⟨a, by rw [pow_two]⟩
  -- the point `x` of coordinate `y`.
  set x : X := C.Θ.symm (some y) with hxdef
  have hsx : C.Θ (s • x) = some (Work.ZASS2.zassS C s y) := by
    rw [hxdef]; exact Work.ZASS2.zassS_spec C hsz hs2 hy
  -- `h • x` is the point of coordinate `α h * y = a² * y`.
  have hcoord : C.Θ ((h : G) • x) = some (a ^ 2 * y) := by
    rw [C.scale, hxdef, Equiv.apply_symm_apply]
    simp only [hh, Option.map_some]
  have hx_coord : (h : G) • x = C.Θ.symm (some (a ^ 2 * y)) :=
    (Equiv.eq_symm_apply C.Θ).mpr hcoord
  -- `s` inverts `H`, so `s h = h⁻¹ s`, hence `s • (h • x) = h⁻¹ • (s • x)`.
  have hinvh : s * (h : G) * s⁻¹ = (h : G)⁻¹ := hinv (h : G) h.2
  have hmul : s * (h : G) = (h : G)⁻¹ * s := by
    calc s * (h : G) = s * (h : G) * s⁻¹ * s := by group
      _ = (h : G)⁻¹ * s := by rw [hinvh]
  have hsh : s • ((h : G) • x) = (h : G)⁻¹ • (s • x) := by
    rw [← mul_smul, hmul, mul_smul]
  -- the coordinate of `h⁻¹ • (s • x)` is `(α h)⁻¹ * S y = (a²)⁻¹ * S y`.
  have hleft : C.Θ (s • ((h : G) • x)) = some ((a ^ 2)⁻¹ * Work.ZASS2.zassS C s y) := by
    rw [hsh]
    have hcoe : ((h⁻¹ : ↥(Work.Zassenhaus.pairStab G inf zero)) : G) =
        ((h : ↥(Work.Zassenhaus.pairStab G inf zero)) : G)⁻¹ := Subgroup.coe_inv _ h
    have hkey := C.scale (h⁻¹ : ↥(Work.Zassenhaus.pairStab G inf zero)) (s • x)
    rw [hcoe, hsx] at hkey
    rw [hkey]
    simp only [Option.map_some]
    rw [hα h, hh]
  -- the coordinate of `s • (h • x) = s • x_{a²y}` is `S (a² y)`.
  have hright : C.Θ (s • ((h : G) • x)) = some (Work.ZASS2.zassS C s (a ^ 2 * y)) := by
    rw [hx_coord]
    exact Work.ZASS2.zassS_spec C hsz hs2 (mul_ne_zero ha2 hy)
  have hs_eq : Work.ZASS2.zassS C s (a ^ 2 * y) = (a ^ 2)⁻¹ * Work.ZASS2.zassS C s y :=
    Option.some.inj (hright.symm.trans hleft)
  rw [hs_eq, div_eq_mul_inv, mul_comm]

end Work.ZASS2
