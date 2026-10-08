import Mathlib
import Submission.Work.Hering.Config
import Submission.Work.Hering.HardCore.abelian_setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `C_G(V)/V` is the centralizer in `G/V` of the image of the second level

In the abelian configuration of the hard core of Hering's theorem, `V ⊴ G` is elementary abelian
(`hexp`), `C = C_G(V)` is abelian (`hCab`) and the squaring map
`level2 V C = {x ∈ C | x * x ∈ V} → V`, `x ↦ x * x`, is onto (`hsq`).  Then

`C_G(V) · V / V = C_{G/V}(level2 · V / V)`,

i.e. an element `g ∈ G` lies in `C_G(V)` if and only if its image in `G/V` centralizes the image
of the second level.

The two inclusions are:

* `⊆`: both `C` and `level2` sit inside the abelian group `C`, so their images commute in `G/V`;
* `⊇`: if `g ∈ G` commutes modulo `V` with `level2`, then for `x ∈ level2` the element
  `g x g⁻¹ x⁻¹` lies in `V`.  Since `V` is abelian and `x ∈ level2 ≤ C_G(V)`, the square
  `(g x g⁻¹)² = (g x g⁻¹ x⁻¹ · x)² = x²`; by `hsq` every `v ∈ V` is of the shape `x * x`
  with `x ∈ level2`, so `g` fixes `V` pointwise, i.e. `g ∈ C_G(V)`.
-/

set_option autoImplicit false

namespace Work.Hering.HardCore

open LeanEval.GroupTheory.Defs

theorem centralizer_map_level2 {G : Type*} [Group G] [Finite G] (V C : Subgroup G) [V.Normal]
    (hC : C = Subgroup.centralizer ((V : Set G)))
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hexp : ∀ x ∈ V, x * x = 1)
    (hsq : ∀ v ∈ V, ∃ x ∈ level2 V C hC hCab hexp, x * x = v) :
    (C.map (QuotientGroup.mk' V))
      = Subgroup.centralizer (((level2 V C hC hCab hexp).map (QuotientGroup.mk' V) : Set (G ⧸ V))) := by
  classical
  have hVn : V.Normal := inferInstance
  have hVC : V ≤ C := V_le_C V C hC hexp
  refine le_antisymm ?_ ?_
  · -- both `C` and the second level are contained in the abelian group `C`
    intro y hy
    obtain ⟨c, hcC, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨x, hxL, rfl⟩ := Subgroup.mem_map.mp hz
    rw [← map_mul, ← map_mul, hCab c hcC x hxL.1]
  · intro y hy
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective V y
    -- `g` commutes with the second level modulo `V`
    have hkey : ∀ x ∈ level2 V C hC hCab hexp, g * x * g⁻¹ * x⁻¹ ∈ V := by
      intro x hxL
      have hmem : QuotientGroup.mk' V x
          ∈ ((level2 V C hC hCab hexp).map (QuotientGroup.mk' V) : Set (G ⧸ V)) :=
        Subgroup.mem_map_of_mem _ hxL
      have h1 := (Subgroup.mem_centralizer_iff.mp hy) _ hmem
      rw [← map_mul, ← map_mul] at h1
      have h2 : (x * g)⁻¹ * (g * x) ∈ V := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h1
        exact QuotientGroup.eq.mp h1
      -- conjugate this relation into `g * x * g⁻¹ * x⁻¹ ∈ V`
      have h3 : g * (x * ((x * g)⁻¹ * (g * x)) * x⁻¹) * g⁻¹ ∈ V :=
        hVn.conj_mem _ (hVn.conj_mem _ h2 x) g
      rwa [show g * (x * ((x * g)⁻¹ * (g * x)) * x⁻¹) * g⁻¹ = g * x * g⁻¹ * x⁻¹ from by
        group] at h3
    -- hence `g` fixes `V` pointwise, since squaring on the second level is onto `V`
    have hfix : ∀ v ∈ V, g * v * g⁻¹ = v := by
      intro v hv
      obtain ⟨y, hyL, hyv⟩ := hsq v hv
      -- `a = g y g⁻¹ y⁻¹ ∈ V` commutes with `y ∈ C`, and `g y g⁻¹ = a y`
      set a : G := g * y * g⁻¹ * y⁻¹ with ha
      have hay : a ∈ V := by rw [ha]; exact hkey y hyL
      have haC : a ∈ C := hVC hay
      have hyC : y ∈ C := hyL.1
      have haa : a * a = 1 := hexp a hay
      have hyc : y * a = a * y := hCab y hyC a haC
      have hgy : g * y * g⁻¹ = a * y := by rw [ha]; group
      have key : (a * y) * (a * y) = y * y := by
        calc (a * y) * (a * y) = a * (y * a) * y := by group
          _ = a * (a * y) * y := by rw [hyc]
          _ = (a * a) * (y * y) := by group
          _ = y * y := by rw [haa, one_mul]
      calc g * v * g⁻¹ = g * (y * y) * g⁻¹ := by rw [hyv]
        _ = (g * y * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (a * y) * (a * y) := by rw [hgy]
        _ = y * y := key
        _ = v := hyv
    refine Subgroup.mem_map.mpr ⟨g, ?_, rfl⟩
    rw [mem_C_iff V C hC]
    intro v hv
    have h1 : g * v = v * g := by
      calc g * v = (g * v * g⁻¹) * g := by group
        _ = v * g := by rw [hfix v hv]
    exact h1.symm

end Work.Hering.HardCore
