import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.exists_mul_of_mem_sup_of_normal

namespace Work.CORE3

open scoped Pointwise

open Subgroup
open Work.GW2

/-- Design pass 13 §1, D2 (pure group theory).  If `P₂` normalizes `P`, `Y ≤ P ⊔ P₂`,
`Y ∩ P = 1` and `Y ≠ 1`, then `(P ⊔ Y) ∩ P₂ ≠ 1`.

Proof: since `P₂ ≤ N_G(P)`, every element of `P ⊔ P₂` is a product `a * b` with `a ∈ P`,
`b ∈ P₂`; take `y ∈ Y#` and write `y = a * b`; then `b = a⁻¹ * y ∈ (P ⊔ Y) ⊓ P₂`, and if that
intersection were `⊥` then `y = a ∈ P ⊓ Y = ⊥`.  (GAP check: 1.5M instances, 0 failures.) -/
theorem Core13InfNeBot (G : Type) [Group G] {P P2 Y : Subgroup G}
    (hPn : P2 ≤ normalizer (P : Set G)) (hY : Y ≤ P ⊔ P2) (hYP : Y ⊓ P = ⊥) (hYne : Y ≠ ⊥) :
    (P ⊔ Y) ⊓ P2 ≠ ⊥ := by
  -- pick a nontrivial element `y` of `Y`
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hYne
  have hyY : (y : G) ∈ Y := y.2
  have hyG : (y : G) ≠ 1 := fun h => hy1 (Subtype.ext h)
  -- `P₂ ≤ N_G(P)` decomposes the elements of `P ⊔ P₂` as products
  have hy : (y : G) ∈ P ⊔ P2 := hY hyY
  have hy' : (y : G) ∈ (P : Set G) * (P2 : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left P P2 hPn]
    exact hy
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hy'
  -- `b = a⁻¹ y` lies in `P ⊔ Y` and in `P₂`
  have hb_eq : b = a⁻¹ * (y : G) := by rw [← hab, inv_mul_cancel_left]
  have hb_sup : b ∈ P ⊔ Y := by
    rw [hb_eq]
    exact mul_mem (Subgroup.inv_mem _ (Subgroup.mem_sup_left ha)) (Subgroup.mem_sup_right hyY)
  -- and `b ≠ 1`, since `b = 1` would force `y = a ∈ Y ⊓ P = ⊥`
  have hb_ne : b ≠ 1 := by
    intro hb1
    apply hyG
    have hyP : (y : G) ∈ P := by rw [← hab, hb1, mul_one]; exact ha
    have hmem : (y : G) ∈ Y ⊓ P := ⟨hyY, hyP⟩
    rw [hYP] at hmem
    simpa using hmem
  exact Subgroup.ne_bot_iff_exists_ne_one.mpr
    ⟨⟨b, ⟨hb_sup, hb⟩⟩, fun h => hb_ne (Subtype.ext_iff.mp h)⟩

end Work.CORE3
