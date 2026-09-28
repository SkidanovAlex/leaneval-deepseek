import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.HP2.grid_count_bounds

namespace Work.HP.HP2

/-- `Work.HP.toR` is injective on integer vectors. -/
lemma toR_injective (m : ℕ) : Function.Injective (Work.HP.toR : (Fin m → ℤ) → (Fin m → ℝ)) := by
  intro v w h
  funext i
  have hi : ((v i : ℤ) : ℝ) = ((w i : ℤ) : ℝ) := congrFun h i
  exact_mod_cast hi

/-- The integer points `v` of the coset `b + W ℤ^m` (i.e. `(W : ℤ) ∣ v i - b i` for all `i`)
whose real image `toR v` lies in `S` are in bijection -- via `toR` -- with the real points of the
coset `b + W ℤ^m` lying in `S`.  Hence the two counting sets have the same `ncard`.

Forward direction: `(W : ℤ) ∣ v i - b i` writes `v i = b i + W * (z i)`, so
`toR v = fun i => (b i : ℝ) + (W : ℝ) * (z i)`.  Backward direction: given
`x = fun i => (b i : ℝ) + (W : ℝ) * (z i)` put `v i := b i + W * z i`.  Injectivity of `toR`
follows from injectivity of `Int.cast` and the finiteness of `Fin m`, so `ncard` of the injective
image of a set equals the `ncard` of the set.  (No positivity of `W` is needed.) -/
lemma ncard_int_coset_eq (m : ℕ) (W : ℕ) (b : Fin m → ℤ) (S : Set (Fin m → ℝ)) :
    ({v : Fin m → ℤ | (∀ i, (W : ℤ) ∣ v i - b i) ∧ Work.HP.toR v ∈ S} : Set (Fin m → ℤ)).ncard
      = ({x : Fin m → ℝ | x ∈ S ∧ ∃ z : Fin m → ℤ,
          x = fun i => (b i : ℝ) + (W : ℝ) * (z i)} : Set (Fin m → ℝ)).ncard := by
  have himg : Work.HP.toR ''
      ({v : Fin m → ℤ | (∀ i, (W : ℤ) ∣ v i - b i) ∧ Work.HP.toR v ∈ S} : Set (Fin m → ℤ))
      = {x : Fin m → ℝ | x ∈ S ∧ ∃ z : Fin m → ℤ,
          x = fun i => (b i : ℝ) + (W : ℝ) * (z i)} := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨hdiv, hvS⟩ := hv
      choose z hz using hdiv
      refine ⟨hvS, z, ?_⟩
      funext i
      simp only [Work.HP.toR]
      have hcast : ((v i - b i : ℤ) : ℝ) = (W : ℝ) * (z i : ℝ) := by
        rw [hz i]; push_cast; ring
      have hv' : (v i : ℝ) = (b i : ℝ) + ((v i - b i : ℤ) : ℝ) := by push_cast; ring
      rw [hv', hcast]
    · rintro ⟨hxS, z, rfl⟩
      refine ⟨fun i => b i + (W : ℤ) * z i, ⟨?_, ?_⟩, ?_⟩
      · intro i
        exact ⟨z i, by ring⟩
      · have h : Work.HP.toR (fun i => b i + (W : ℤ) * z i)
            = fun i => (b i : ℝ) + (W : ℝ) * (z i) := by
          funext i
          simp only [Work.HP.toR]
          push_cast
          ring
        rw [h]
        exact hxS
      · funext i
        simp only [Work.HP.toR]
        push_cast
        ring
  have h := Set.ncard_image_of_injective
    ({v : Fin m → ℤ | (∀ i, (W : ℤ) ∣ v i - b i) ∧ Work.HP.toR v ∈ S} : Set (Fin m → ℤ))
    (toR_injective m)
  rw [← h, himg]

theorem grid_coset_lower (m : ℕ) (hm : 1 ≤ m) (W : ℕ) (hW : 0 < W) (b : Fin m → ℤ)
    (S : Set (Fin m → ℝ)) (hS : IsClosed S) (hSbd : Bornology.IsBounded S)
    (hvol : (MeasureTheory.volume {x : Fin m → ℝ | ∃ y ∈ frontier S,
        Work.HP.rNorm (x - y) ≤ 8 * (m : ℝ) * W}).toReal ≤ (1 / 2) * (MeasureTheory.volume S).toReal) :
    (1 / 2) * (MeasureTheory.volume S).toReal / (W : ℝ) ^ m
      ≤ ({v : Fin m → ℤ | (∀ i, (W : ℤ) ∣ v i - b i) ∧ Work.HP.toR v ∈ S} : Set (Fin m → ℤ)).ncard := by
  classical
  obtain ⟨hcb1, -⟩ := grid_count_bounds m hm W hW b S hS hSbd
  have hWℝ : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hwp : (0 : ℝ) < (W : ℝ) ^ m := pow_pos hWℝ m
  rw [ncard_int_coset_eq]
  have hstep : (1 / 2) * (MeasureTheory.volume S).toReal / (W : ℝ) ^ m
      ≤ ((MeasureTheory.volume S).toReal
          - (MeasureTheory.volume {x : Fin m → ℝ | ∃ y ∈ frontier S,
              Work.HP.rNorm (x - y) ≤ 8 * (m : ℝ) * W}).toReal) / (W : ℝ) ^ m := by
    apply div_le_div_of_nonneg_right _ hwp.le
    linarith
  linarith [hcb1]

end Work.HP.HP2
