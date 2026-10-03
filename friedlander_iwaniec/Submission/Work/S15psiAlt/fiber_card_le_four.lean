import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.GaussMoebiusCore
import Submission.Commons.NumberTheory.GaussianInt.units_classification

/-!
# The fibre of `normalizedFactors` on `ℤ[i]` has at most four elements

`UniqueFactorizationMonoid.normalizedFactors` is invariant under multiplication by a unit and,
conversely, two nonzero elements have the same normalized factor multiset if and only if they are
associated (Mathlib's `associated_iff_normalizedFactors_eq_normalizedFactors`). Hence, inside a
fixed `Finset W` of nonzero elements, the elements with prescribed normalized factors are all
multiples of one fixed element by a unit. `ℤ[i]` has exactly four units (`±1`, `±i`), so such a
fibre contains at most four elements.
-/

namespace Work.S15psiAlt

open UniqueFactorizationMonoid

/-- The four units of `ℤ[i]`, as an explicit finset. -/
private def unitFinset : Finset GaussianInt :=
  {1, -1, (⟨0, 1⟩ : GaussianInt), (⟨0, -1⟩ : GaussianInt)}

private lemma card_unitFinset : unitFinset.card ≤ 4 := by decide

/-- Every unit of `ℤ[i]` lies in `unitFinset`. -/
private lemma mem_unitFinset {x : GaussianInt} (hx : IsUnit x) : x ∈ unitFinset := by
  have h := (Commons.NumberTheory.GaussianInt.units_classification x).mp hx
  simp only [unitFinset, Finset.mem_insert, Finset.mem_singleton]
  rcases h with rfl | rfl | rfl | rfl <;> simp

theorem fiber_card_le_four (z : GaussianInt) (W : Finset GaussianInt) (hz : z ≠ 0) (hW : ∀ w ∈ W, w ∣ z) (S : Multiset GaussianInt) : (W.filter (fun w => UniqueFactorizationMonoid.normalizedFactors w = S)).card ≤ 4 := by
  classical
  -- Every element of `W` is nonzero, since it divides the nonzero `z`.
  have hne : ∀ w ∈ W, w ≠ 0 := fun w hw => by
    have hwz := hW w hw
    rintro rfl
    obtain ⟨c, hc⟩ := hwz
    exact hz (hc.trans (zero_mul c))
  set T : Finset GaussianInt :=
    W.filter (fun w => UniqueFactorizationMonoid.normalizedFactors w = S) with hT
  rcases eq_or_ne T ∅ with h0 | h0
  · rw [h0]
    norm_num
  · -- Pick a base point `b` in the fibre: every element of the fibre is associated to `b`.
    obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr h0
    obtain ⟨hbW, hbS⟩ := Finset.mem_filter.mp hb
    have hsub : T ⊆ unitFinset.image (fun y => y * b) := by
      intro x hx
      obtain ⟨hxW, hxS⟩ := Finset.mem_filter.mp hx
      have hassoc : Associated x b :=
        (UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors
          (hne x hxW) (hne b hbW)).mpr (hxS.trans hbS.symm)
      obtain ⟨u, hu⟩ := hassoc
      have hxeq : x = (↑u⁻¹ : GaussianInt) * b := by
        calc x = (x * (↑u : GaussianInt)) * (↑u⁻¹ : GaussianInt) := by
              rw [mul_assoc, Units.mul_inv, mul_one]
          _ = b * (↑u⁻¹ : GaussianInt) := by rw [hu]
          _ = (↑u⁻¹ : GaussianInt) * b := mul_comm _ _
      exact Finset.mem_image.mpr ⟨(↑u⁻¹ : GaussianInt), mem_unitFinset (u⁻¹).isUnit, hxeq.symm⟩
    calc T.card ≤ (unitFinset.image (fun y => y * b)).card := Finset.card_le_card hsub
      _ ≤ 4 := le_trans Finset.card_image_le card_unitFinset

end Work.S15psiAlt
