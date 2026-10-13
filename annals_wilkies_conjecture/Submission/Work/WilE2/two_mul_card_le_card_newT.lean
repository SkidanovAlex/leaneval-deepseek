import Mathlib
import Submission.Work.WilE2.KhoSphereDefs

namespace Work.WilE2

variable {n s : ℕ}

/-- `khoPt S c` is injective: the last coordinate can be forgotten. -/
theorem khoPt_inj (S : ESys n (s + 1)) (c : ℝ) : Function.Injective (khoPt S c) := by
  intro x y h
  funext i
  have := congrFun h (Fin.castSucc i)
  simpa [khoPt, Fin.snoc_castSucc] using this

/-- `khoPt' S c` is injective: the last coordinate can be forgotten. -/
theorem khoPt'_inj (S : ESys n (s + 1)) (c : ℝ) : Function.Injective (khoPt' S c) := by
  intro x y h
  funext i
  have := congrFun h (Fin.castSucc i)
  simpa [khoPt', Fin.snoc_castSucc] using this

/-- The two lifts of a point with `fT S x < c` are distinct, since the last coordinates
`±√(c - fT S x)` differ as soon as `c - fT S x > 0`. -/
theorem khoPt_ne_khoPt' (S : ESys n (s + 1)) (c : ℝ) {x y : Fin n → ℝ}
    (hx : 0 < c - fT S x) : khoPt S c x ≠ khoPt' S c y := by
  intro h
  have hxy : x = y := by
    funext i
    have := congrFun h (Fin.castSucc i)
    simpa [khoPt, khoPt', Fin.snoc_castSucc] using this
  subst hxy
  have hlast := congrFun h (Fin.last n)
  simp only [khoPt, khoPt', Fin.snoc_last] at hlast
  have hs : Real.sqrt (c - fT S x) = 0 := by linarith
  have := Real.sqrt_pos_of_pos hx
  linarith

theorem two_mul_card_le_card_newT {n s : ℕ} (S : ESys n (s + 1)) (T : Finset (Fin n → ℝ))
    (c : ℝ) (hc : ∀ x ∈ T, 0 < c - fT S x) : 2 * T.card ≤ (newT S T c).card := by
  have hA : (T.image (khoPt S c)).card = T.card :=
    Finset.card_image_of_injective T (khoPt_inj S c)
  have hB : (T.image (khoPt' S c)).card = T.card :=
    Finset.card_image_of_injective T (khoPt'_inj S c)
  have hdisj : Disjoint (T.image (khoPt S c)) (T.image (khoPt' S c)) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    rw [Finset.mem_image] at ha hb
    obtain ⟨x, hxT, rfl⟩ := ha
    obtain ⟨y, hyT, rfl⟩ := hb
    exact khoPt_ne_khoPt' S c (hc x hxT)
  have hunion : (T.image (khoPt S c) ∪ T.image (khoPt' S c)).card
      = (T.image (khoPt S c)).card + (T.image (khoPt' S c)).card :=
    Finset.card_union_of_disjoint hdisj
  have hsub : T.image (khoPt S c) ∪ T.image (khoPt' S c) ⊆ newT S T c := by
    apply Finset.union_subset
    · rw [Finset.image_subset_iff]
      intro x hx
      rw [newT, Finset.mem_biUnion]
      exact ⟨x, hx, by simp⟩
    · rw [Finset.image_subset_iff]
      intro x hx
      rw [newT, Finset.mem_biUnion]
      exact ⟨x, hx, by simp⟩
  have hle := Finset.card_le_card hsub
  rw [hunion, hA, hB] at hle
  omega

end Work.WilE2
