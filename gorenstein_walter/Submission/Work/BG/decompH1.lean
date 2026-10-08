import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.invJCard
import Submission.Work.BG.rem31UinfS0

namespace Work.BG

set_option linter.style.haveILetI false

open Subgroup
open scoped Pointwise

/-- If `A ⊓ B = ⊥`, the product map `A × B → G`, `(a, b) ↦ a * b`, is injective:
from `a * b = a' * b'` we get `a'⁻¹ * a = b' * b⁻¹ ∈ A ⊓ B = ⊥`, hence `a = a'` and
`b = b'`.  (No normality is needed for injectivity.) -/
theorem mul_injective_of_inf_eq_bot {G : Type} [Group G] {A B : Subgroup G}
    (hbot : A ⊓ B = ⊥) :
    Function.Injective (fun p : ↥A × ↥B => (p.1 : G) * (p.2 : G)) := by
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
  simp only at h
  have hkey : (a' : G)⁻¹ * a = b' * b⁻¹ := by
    calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * b⁻¹ := by group
      _ = (a' : G)⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h1 : (a' : G)⁻¹ * a = 1 := by
    have hmem : (a' : G)⁻¹ * a ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      refine ⟨A.mul_mem (A.inv_mem ha') ha, ?_⟩
      rw [hkey]
      exact B.mul_mem hb' (B.inv_mem hb)
    simpa using hmem
  have haa : a' = a := inv_mul_eq_one.mp h1
  have hbb : b' = b := mul_inv_eq_one.mp (by rw [← hkey]; exact h1)
  subst haa
  subst hbb
  exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup in
theorem decompH1 {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) {x : G}
    (hx : x ∈ Work.BG.H1 D) : ∃! p : ↥D.U × ↥D.S0, (p.1 : G) * (p.2 : G) = x := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  -- `H₁ = U ⊔ S₀ = U · S₀` because `S₀` normalizes `U`.
  have hmem : x ∈ (↑D.U : Set G) * (↑D.S0 : Set G) := by
    rw [← Work.BG.coe_U_sup_S0 D]
    exact hx
  obtain ⟨u, hu, s, hs, hus⟩ := hmem
  have hus' : u * s = x := hus
  refine ⟨(⟨u, hu⟩, ⟨s, hs⟩), hus', ?_⟩
  intro y hy
  refine mul_injective_of_inf_eq_bot (Work.BG.rem31UinfS0 D) ?_
  change (y.1 : G) * (y.2 : G) = u * s
  rw [hy, hus']

end Work.BG
