import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open NumberField

set_option linter.style.haveILetI false

theorem finplace_ciSup_log_support {L : Type*} [Field L] [NumberField L] {ι : Type*} [Finite ι]
    (x : ι → L) (hne : ∃ i, x i ≠ 0) :
    Function.HasFiniteSupport (fun w : NumberField.FinitePlace L => Real.log (⨆ i, w (x i))) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hne
  haveI : Nonempty ι := ⟨i₀⟩
  -- The (finite) union of the multiplicative supports of `w ↦ w (x i)`, over the indices `i`
  -- with `x i ≠ 0`.
  have hBfin : (⋃ i ∈ {i : ι | x i ≠ 0},
      Function.mulSupport (fun w : NumberField.FinitePlace L => w (x i))).Finite := by
    refine Set.Finite.biUnion (Set.toFinite _) ?_
    intro i hi
    exact NumberField.FinitePlace.hasFiniteMulSupport (by simpa using hi)
  refine hBfin.subset ?_
  intro w hw
  by_contra hmem
  simp only [Function.mem_support] at hw
  -- Off the union, every nonzero `x i` has `w (x i) = 1`.
  have hoff : ∀ i, x i ≠ 0 → w (x i) = 1 := by
    intro i hi
    by_contra hne1
    exact hmem (by
      rw [Set.mem_iUnion₂]
      exact ⟨i, hi, Function.mem_mulSupport.mpr hne1⟩)
  -- Hence the supremum over `i` is exactly `1`.
  have hle1 : ∀ i, w (x i) ≤ 1 := by
    intro i
    by_cases hi : x i = 0
    · rw [hi, map_zero]; norm_num
    · rw [hoff i hi]
  have hbdd : BddAbove (Set.range (fun i : ι => w (x i))) :=
    ⟨1, by rintro _ ⟨i, rfl⟩; exact hle1 i⟩
  have hsup : (⨆ i, w (x i)) = 1 := by
    refine le_antisymm (ciSup_le hle1) ?_
    have h1 := le_ciSup (f := fun i : ι => w (x i)) hbdd i₀
    rwa [hoff i₀ hi₀] at h1
  exact hw (by rw [hsup, Real.log_one])

end Work.BW
