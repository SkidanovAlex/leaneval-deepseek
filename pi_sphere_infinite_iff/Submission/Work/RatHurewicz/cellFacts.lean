import Mathlib
import Submission.Work.RatHurewicz.cellDefs
import Submission.Work.RatHurewicz.rawWeight_eqvGen

/-!
# Elementary facts about the cells of the model

Corollaries of the invariance of `rawWeight` (`Work.RatHurewicz.rawWeight_eqvGen`) that the
cell-by-cell push for `Work.RatHurewicz.compress_to_skeleton` uses: open cells that meet have
supports of the same cardinality, the skeleta are described by `rawWeight`, and a point of
`skel D k` that misses all the open cells of dimension `k` lies in `skel D (k-1)`.
-/

open scoped Topology Simplicial unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ} {D : MData X n x₀}

/-- **Two open cells that meet have supports of the same cardinality.** -/
theorem openCell_card_eq {i j : D.Idx} {S T : Finset (Fin (n + 2))} {z : Model D}
    (hz : z ∈ openCell D i S) (hz' : z ∈ openCell D j T) : S.card = T.card := by
  obtain ⟨x, hx, hxz⟩ := hz
  obtain ⟨y, hy, hyz⟩ := hz'
  have hEq : (Quotient.mk'' (Sum.inl ⟨j, y⟩) : Model D) =
      Quotient.mk'' (Sum.inl ⟨i, x⟩) := by
    rw [hyz, hxz.symm]
  have hrel : Relation.EqvGen (modelRel D) (Sum.inl ⟨j, y⟩) (Sum.inl ⟨i, x⟩) :=
    Quotient.exact hEq
  have hw := rawWeight_eqvGen D hrel
  rw [rawWeight_inl, rawWeight_inl] at hw
  rw [hy, hx] at hw
  exact hw.symm

/-- The description of the `k`-skeleton by `rawWeight`. -/
theorem mem_skel_iff {k : ℕ} {z : Model D} :
    z ∈ skel D k ↔ ∃ a : Raw D, Quotient.mk'' a = z ∧ rawWeight D a ≤ k + 1 := by
  constructor
  · rintro ⟨a, ha, hw⟩
    rcases a with ⟨i, x⟩ | ⟨i, t⟩
    · exact ⟨Sum.inl ⟨i, x⟩, ha, hw⟩
    · exact ⟨Sum.inr ⟨i, t⟩, ha, by show (1:ℕ) ≤ k + 1; omega⟩
  · rintro ⟨a, ha, hw⟩
    rcases a with ⟨i, x⟩ | ⟨i, t⟩
    · exact ⟨Sum.inl ⟨i, x⟩, ha, hw⟩
    · exact ⟨Sum.inr ⟨i, t⟩, ha, trivial⟩

/-- **A point of `skel D k` that misses every open `k`-cell lies in `skel D (k-1)`.** -/
theorem skel_pred_of_not_mem_openCells {k : ℕ} {z : Model D} (hz : z ∈ skel D k)
    (h : ∀ (i : D.Idx) (S : Finset (Fin (n + 2))), S.card = k + 1 → z ∉ openCell D i S) :
    z ∈ skel D (k - 1) := by
  obtain ⟨a, ha, hw⟩ := (mem_skel_iff (D := D)).mp hz
  rcases a with ⟨i, x⟩ | ⟨i, t⟩
  · rw [rawWeight_inl] at hw
    by_cases hc : (ptSupport x).card = k + 1
    · exact absurd ⟨x, rfl, ha⟩ (h i (ptSupport x) hc)
    · have hle : (ptSupport x).card ≤ k := by omega
      refine (mem_skel_iff (D := D)).mpr ⟨Sum.inl ⟨i, x⟩, ha, ?_⟩
      rw [rawWeight_inl]
      omega
  · refine (mem_skel_iff (D := D)).mpr ⟨Sum.inr ⟨i, t⟩, ha, ?_⟩
    show (1 : ℕ) ≤ (k - 1) + 1
    omega

/-- The `k`-skeleton is monotone in `k`. -/
theorem skel_mono {k l : ℕ} (hkl : k ≤ l) : skel D k ⊆ skel D l := by
  intro z hz
  obtain ⟨a, ha, hw⟩ := hz
  rcases a with ⟨i, x⟩ | ⟨i, t⟩
  · exact ⟨Sum.inl ⟨i, x⟩, ha, le_trans hw (by omega)⟩
  · exact ⟨Sum.inr ⟨i, t⟩, ha, trivial⟩

/-- Every point of the model lies in the top skeleton (the pieces are copies of `Δ^{n+1}`). -/
theorem mem_skel_top (z : Model D) : z ∈ skel D (n + 1) := by
  induction z using Quotient.inductionOn with
  | h y =>
    rcases y with ⟨i, x⟩ | ⟨i, t⟩
    · refine ⟨Sum.inl ⟨i, x⟩, rfl, ?_⟩
      exact le_trans (Finset.card_le_univ _) (by simp)
    · exact ⟨Sum.inr ⟨i, t⟩, rfl, trivial⟩

end

end Work.RatHurewicz
