import Mathlib

namespace Work.Drive

/-- **Quotient maps with the same fibres give a homeomorphism.**  If `q : X → Y` and `f : X → Z` are
both quotient maps and `q x = q y ↔ f x = f y` for all `x y`, then `Y ≃ₜ Z`. -/
theorem quotientMap_fibers {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {q : X → Y} {f : X → Z} (hq : Topology.IsQuotientMap q)
    (hf : Topology.IsQuotientMap f) (h : ∀ x y, q x = q y ↔ f x = f y) : Nonempty (Y ≃ₜ Z) := by
  classical
  -- `g` descends `f` through `q`: pick any preimage under `q` and apply `f`.
  let g : Y → Z := fun y => f (Function.surjInv hq.surjective y)
  -- `k` descends `q` through `f`.
  let k : Z → Y := fun z => q (Function.surjInv hf.surjective z)
  -- Both descents commute with the defining maps, using that they have the same fibres.
  have hgq : ∀ x, g (q x) = f x := by
    intro x
    exact (h _ _).mp (Function.surjInv_eq hq.surjective (q x))
  have hkf : ∀ x, k (f x) = q x := by
    intro x
    exact (h _ _).mpr (Function.surjInv_eq hf.surjective (f x))
  -- `g` and `k` are mutually inverse, since both maps are surjective.
  have hgk : Function.LeftInverse k g := by
    intro y
    obtain ⟨x, rfl⟩ := hq.surjective y
    rw [hgq x, hkf x]
  have hkg : Function.RightInverse k g := by
    intro z
    obtain ⟨x, rfl⟩ := hf.surjective z
    rw [hkf x, hgq x]
  -- Continuity of both descents comes from the quotient property of the other map.
  have hg_cont : Continuous g := by
    rw [hq.continuous_iff]
    change Continuous fun x => g (q x)
    rw [show (fun x => g (q x)) = f from funext hgq]
    exact hf.continuous
  have hk_cont : Continuous k := by
    rw [hf.continuous_iff]
    change Continuous fun x => k (f x)
    rw [show (fun x => k (f x)) = q from funext hkf]
    exact hq.continuous
  exact ⟨⟨Equiv.mk g k hgk hkg, hg_cont, hk_cont⟩⟩

end Work.Drive
