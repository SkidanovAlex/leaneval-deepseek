import Mathlib

open MeasureTheory Set

namespace Work.TMC7Core.Scale

/-- Shifting by `c` and taking fractional parts cannot increase the measure: for a measurable
`B`, the set of `x ∈ [0,1]` with `Int.fract (x + c) ∈ B` has measure at most that of `B`.

The map `y ↦ Int.fract y` cuts out one representative of each integer translate, i.e. the preimage
`Int.fract ⁻¹' B` is invariant under the action of `ℤ ⊂ ℝ` by translation.  Comparing its mass on
the two fundamental domains `Ioc c (c+1)` and `Ioc 0 1` of that action (via
`IsAddFundamentalDomain.measure_set_eq`), translating back by `c` and bounding the boundary terms,
gives the claim. -/
theorem volume_fract_shift (B : Set ℝ) (hB : MeasurableSet B) (hB1 : B ⊆ Set.Icc 0 1) (c : ℝ) :
    MeasureTheory.volume {x : ℝ | x ∈ Set.Icc (0:ℝ) 1 ∧ Int.fract (x + c) ∈ B}
      ≤ MeasureTheory.volume B := by
  have hAmeas : MeasurableSet (Int.fract ⁻¹' B : Set ℝ) := measurable_fract hB
  -- `Int.fract ⁻¹' B` is invariant under integer translations.
  have hinv : ∀ g : AddSubgroup.zmultiples (1:ℝ),
      (fun x : ℝ => g +ᵥ x) ⁻¹' (Int.fract ⁻¹' B) = (Int.fract ⁻¹' B) := by
    intro g
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp g.2
    ext x
    simp only [Set.mem_preimage]
    have hgx : g +ᵥ x = x + (n:ℝ) := by
      rw [AddSubgroup.vadd_def]
      rw [show (↑g : ℝ) = (n:ℝ) by rw [← hn]; simp]
      rw [vadd_eq_add, add_comm]
    simp only [hgx, Int.fract_add_intCast]
  have hfund_c : MeasureTheory.IsAddFundamentalDomain (AddSubgroup.zmultiples (1:ℝ))
      (Set.Ioc c (c + 1)) MeasureTheory.volume :=
    isAddFundamentalDomain_Ioc (T := 1) (by norm_num) c
  have hfund_0 : MeasureTheory.IsAddFundamentalDomain (AddSubgroup.zmultiples (1:ℝ))
      (Set.Ioc (0:ℝ) (0 + 1)) MeasureTheory.volume :=
    isAddFundamentalDomain_Ioc (T := 1) (by norm_num) 0
  -- Mass on any two fundamental domains agrees for the invariant set.
  have hshift : MeasureTheory.volume (Int.fract ⁻¹' B ∩ Set.Ioc c (c + 1))
      = MeasureTheory.volume (Int.fract ⁻¹' B ∩ Set.Ioc (0:ℝ) (0 + 1)) :=
    MeasureTheory.IsAddFundamentalDomain.measure_set_eq hfund_c hfund_0 hAmeas hinv
  -- Translate the target set by `c`.
  have htrans : MeasureTheory.volume {x : ℝ | x ∈ Set.Icc (0:ℝ) 1 ∧ Int.fract (x + c) ∈ B}
      = MeasureTheory.volume (Int.fract ⁻¹' B ∩ Set.Icc c (c + 1)) := by
    have hset : {x : ℝ | x ∈ Set.Icc (0:ℝ) 1 ∧ Int.fract (x + c) ∈ B}
        = (fun x : ℝ => x + c) ⁻¹' (Int.fract ⁻¹' B ∩ Set.Icc c (c + 1)) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_Icc]
      constructor
      · rintro ⟨⟨hx0, hx1⟩, hfx⟩
        exact ⟨hfx, ⟨by linarith, by linarith⟩⟩
      · rintro ⟨hfx, ⟨h0, h1⟩⟩
        exact ⟨⟨by linarith, by linarith⟩, hfx⟩
    rw [hset, MeasureTheory.measure_preimage_add_right]
  -- Replacing `Icc c (c+1)` by `Ioc c (c+1)` only removes the null set `{c}`.
  have hIcc_le : MeasureTheory.volume (Int.fract ⁻¹' B ∩ Set.Icc c (c + 1))
      ≤ MeasureTheory.volume (Int.fract ⁻¹' B ∩ Set.Ioc c (c + 1)) := by
    calc MeasureTheory.volume (Int.fract ⁻¹' B ∩ Set.Icc c (c + 1))
        ≤ MeasureTheory.volume ((Int.fract ⁻¹' B ∩ Set.Ioc c (c + 1)) ∪ ({c} : Set ℝ)) := by
          apply MeasureTheory.measure_mono
          rintro y ⟨hyA, hy0, hy1⟩
          rcases eq_or_lt_of_le hy0 with h | h
          · exact Or.inr (by simp only [Set.mem_singleton_iff]; exact h.symm)
          · exact Or.inl ⟨hyA, h, hy1⟩
      _ ≤ MeasureTheory.volume (Int.fract ⁻¹' B ∩ Set.Ioc c (c + 1))
            + MeasureTheory.volume ({c} : Set ℝ) := MeasureTheory.measure_union_le _ _
      _ = MeasureTheory.volume (Int.fract ⁻¹' B ∩ Set.Ioc c (c + 1)) := by
          rw [MeasureTheory.measure_singleton, add_zero]
  -- On `(0,1]` the condition `Int.fract y ∈ B` forces `y ∈ B`, except possibly `y = 1`.
  have hbound : MeasureTheory.volume (Int.fract ⁻¹' B ∩ Set.Ioc (0:ℝ) (0 + 1))
      ≤ MeasureTheory.volume B := by
    have hsub : Int.fract ⁻¹' B ∩ Set.Ioc (0:ℝ) (0 + 1) ⊆ B ∪ ({1} : Set ℝ) := by
      rintro y ⟨hyA, hy0, hy1⟩
      rcases eq_or_lt_of_le hy1 with h | h
      · right
        simp only [Set.mem_singleton_iff]
        linarith [h]
      · left
        have hy1' : y < 1 := by linarith [h]
        have : Int.fract y = y := Int.fract_eq_self.mpr ⟨le_of_lt hy0, hy1'⟩
        simpa [this] using hyA
    calc MeasureTheory.volume (Int.fract ⁻¹' B ∩ Set.Ioc (0:ℝ) (0 + 1))
        ≤ MeasureTheory.volume (B ∪ ({1}:Set ℝ)) := MeasureTheory.measure_mono hsub
      _ ≤ MeasureTheory.volume B + MeasureTheory.volume ({1}:Set ℝ) :=
          MeasureTheory.measure_union_le _ _
      _ = MeasureTheory.volume B := by rw [MeasureTheory.measure_singleton, add_zero]
  calc MeasureTheory.volume {x : ℝ | x ∈ Set.Icc (0:ℝ) 1 ∧ Int.fract (x + c) ∈ B}
      = MeasureTheory.volume (Int.fract ⁻¹' B ∩ Set.Icc c (c + 1)) := htrans
    _ ≤ MeasureTheory.volume (Int.fract ⁻¹' B ∩ Set.Ioc c (c + 1)) := hIcc_le
    _ = MeasureTheory.volume (Int.fract ⁻¹' B ∩ Set.Ioc (0:ℝ) (0 + 1)) := hshift
    _ ≤ MeasureTheory.volume B := hbound

end Work.TMC7Core.Scale
