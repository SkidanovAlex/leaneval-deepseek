import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- If `ℳ` is an internal direct sum decomposition of `M` and `f` is a graded map of degree `w`
(i.e. `f (ℳ i) ≤ ℳ (i + w)` for all `i`), then the image of the component `ℳ j` is exactly the
piece of `ℳ (j + w)` that lies in the range of `f`. -/
theorem graded_map_image {ι R M : Type*} [AddCommGroup ι] [DecidableEq ι]
    [Ring R] [AddCommGroup M] [Module R M] (ℳ : ι → Submodule R M)
    (hℳ : DirectSum.IsInternal ℳ) (f : M →ₗ[R] M) (w : ι)
    (hf : ∀ i, (ℳ i).map f ≤ ℳ (i + w)) (j : ι) :
    (ℳ j).map f = ℳ (j + w) ⊓ LinearMap.range f := by
  -- The family `ℳ` is independent and spans `M`; hence `M = ℳ j ⊔ ⨆_{i ≠ j} ℳ i`.
  have hsplit : ℳ j ⊔ (⨆ (i : ι) (_ : i ≠ j), ℳ i) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hℳ.submodule_iSup_eq_top]
    refine iSup_le fun i => ?_
    by_cases hi : i = j
    · subst hi; exact le_sup_left
    · exact (le_iSup₂ (f := fun i (_ : i ≠ j) => ℳ i) i hi).trans le_sup_right
  -- `f` maps the sum of the other components into the sum of the shifted other components.
  have hPQ : (⨆ (i : ι) (_ : i ≠ j), ℳ i).map f ≤
      (⨆ (i : ι) (_ : i ≠ j), ℳ (i + w)) := by
    rw [Submodule.map_iSup]
    refine iSup_le fun i => ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun hi => ?_
    exact (hf i).trans (le_iSup₂ (f := fun i (_ : i ≠ j) => ℳ (i + w)) i hi)
  -- `ℳ (j + w)` is disjoint from the shifted "other" components.
  have hdisj : ℳ (j + w) ⊓ (⨆ (i : ι) (_ : i ≠ j), ℳ (i + w)) = ⊥ := by
    have hbot : ℳ (j + w) ⊓ (⨆ (m : ι) (_ : m ≠ j + w), ℳ m) = ⊥ :=
      disjoint_iff.mp (hℳ.submodule_iSupIndep (j + w))
    rw [← le_bot_iff]
    calc ℳ (j + w) ⊓ (⨆ (i : ι) (_ : i ≠ j), ℳ (i + w))
        ≤ ℳ (j + w) ⊓ (⨆ (m : ι) (_ : m ≠ j + w), ℳ m) :=
          le_inf inf_le_left (inf_le_right.trans (iSup₂_le fun i hi =>
            le_iSup₂ (f := fun m (_ : m ≠ j + w) => ℳ m) (i + w)
              (fun h => hi (add_right_cancel h))))
      _ = ⊥ := hbot
  refine le_antisymm (le_inf (hf j) ?_) ?_
  · -- `(ℳ j).map f ≤ range f`
    calc (ℳ j).map f ≤ (⊤ : Submodule R M).map f := Submodule.map_mono le_top
      _ = LinearMap.range f := Submodule.map_top f
  · -- the interesting inclusion `ℳ (j + w) ⊓ range f ≤ (ℳ j).map f`
    intro y hy
    rw [Submodule.mem_inf, LinearMap.mem_range] at hy
    obtain ⟨hy1, x, hx_eq⟩ := hy
    -- split `x = a + b` with `a ∈ ℳ j` and `b` in the other components
    have hx : x ∈ ℳ j ⊔ (⨆ (i : ι) (_ : i ≠ j), ℳ i) := by rw [hsplit]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    have hfa : f a ∈ ℳ (j + w) := hf j (Submodule.mem_map.mpr ⟨a, ha, rfl⟩)
    have hfb : f b ∈ (⨆ (i : ι) (_ : i ≠ j), ℳ (i + w)) :=
      hPQ (Submodule.mem_map.mpr ⟨b, hb, rfl⟩)
    have hsubeq : y - f a = f b := by
      rw [← hx_eq, ← hab, map_add]
      abel
    have hyfa : y - f a ∈ ℳ (j + w) := Submodule.sub_mem _ hy1 hfa
    -- the difference lies in `ℳ (j + w) ⊓ Q = ⊥`, so it vanishes and `y = f a`
    have hz : y - f a = 0 := by
      have hmem : y - f a ∈ ℳ (j + w) ⊓ (⨆ (i : ι) (_ : i ≠ j), ℳ (i + w)) := by
        rw [Submodule.mem_inf]
        exact ⟨hyfa, by rw [hsubeq]; exact hfb⟩
      rw [hdisj] at hmem
      simpa using hmem
    exact Submodule.mem_map.mpr ⟨a, ha, (sub_eq_zero.mp hz).symm⟩

end Work.BW
