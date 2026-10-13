import Mathlib
import Submission.Work.WilG4c.EngineDefs

namespace Work.WilG4c

open WilkiesDesign

/-- `Fin.init` is a linear projection, hence `C^r`. -/
private theorem finInit_contDiffOn {n r : ℕ} :
    ContDiffOn ℝ r (fun z : Fin (n + 1) → ℝ => Fin.init z) (openCube (n + 1)) := by
  refine contDiffOn_pi.mpr fun i : Fin n => ?_
  have h : (fun z : Fin (n + 1) → ℝ => Fin.init z i) =
      (fun z : Fin (n + 1) → ℝ => z i.castSucc) := rfl
  rw [h]
  exact contDiffOn_apply ℝ ℝ i.castSucc _

private theorem finInit_mapsTo {n : ℕ} :
    Set.MapsTo (fun z : Fin (n + 1) → ℝ => Fin.init z) (openCube (n + 1)) (openCube n) :=
  fun _z hz i => hz i.castSucc

theorem cellChart_contDiffOn {p n r : ℕ}
    (χ ψ : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
    (M W : (Fin p → ℝ) → (Fin n → ℝ) → ℝ) (l : Fin p → ℝ)
    (hχ : ∀ j : Fin n, ContDiffOn ℝ r (fun u : Fin n → ℝ => χ l (ψ l u) j)
      (WilkiesDesign.openCube n))
    (hM : ContDiffOn ℝ r (fun u : Fin n → ℝ => M l (ψ l u)) (WilkiesDesign.openCube n))
    (hW : ContDiffOn ℝ r (fun u : Fin n → ℝ => W l (ψ l u)) (WilkiesDesign.openCube n)) :
    ContDiffOn ℝ r (fun z : Fin (n + 1) → ℝ => Work.WilG4c.cellChart χ M W ψ l z)
      (WilkiesDesign.openCube (n + 1)) := by
  refine contDiffOn_pi.mpr fun j : Fin (n + 1) => ?_
  have hMc : ContDiffOn ℝ r (fun z : Fin (n + 1) → ℝ => M l (ψ l (Fin.init z)))
      (openCube (n + 1)) :=
    ContDiffOn.comp (g := fun u : Fin n → ℝ => M l (ψ l u))
      (f := fun z : Fin (n + 1) → ℝ => Fin.init z) hM finInit_contDiffOn finInit_mapsTo
  have hWc : ContDiffOn ℝ r (fun z : Fin (n + 1) → ℝ => W l (ψ l (Fin.init z)))
      (openCube (n + 1)) :=
    ContDiffOn.comp (g := fun u : Fin n → ℝ => W l (ψ l u))
      (f := fun z : Fin (n + 1) → ℝ => Fin.init z) hW finInit_contDiffOn finInit_mapsTo
  by_cases hj : (j : ℕ) = n
  · have hlast : ∀ z : Fin (n + 1) → ℝ,
        cellChart χ M W ψ l z j =
          M l (ψ l (Fin.init z)) + (z (Fin.last n) - 1 / 2) *
            (2 * W l (ψ l (Fin.init z)) - 1 / 2) := by
      intro z
      simp only [cellChart]
      rw [dite_eq_left hj]
    have hB : ContDiffOn ℝ r
        (fun z : Fin (n + 1) → ℝ => 2 * W l (ψ l (Fin.init z)) - 1 / 2) (openCube (n + 1)) :=
      (contDiffOn_const.mul hWc).sub contDiffOn_const
    have hC : ContDiffOn ℝ r (fun z : Fin (n + 1) → ℝ => z (Fin.last n) - 1 / 2)
        (openCube (n + 1)) :=
      (contDiffOn_apply ℝ ℝ (Fin.last n) _).sub contDiffOn_const
    exact (hMc.add (hC.mul hB)).congr fun z _ => hlast z
  · have hjlt : (j : ℕ) < n := by omega
    have hnotlast : ∀ z : Fin (n + 1) → ℝ,
        cellChart χ M W ψ l z j = χ l (ψ l (Fin.init z)) ⟨(j : ℕ), hjlt⟩ := by
      intro z
      simp only [cellChart]
      rw [dite_eq_right hj]
    exact (ContDiffOn.comp (g := fun u : Fin n → ℝ => χ l (ψ l u) ⟨(j : ℕ), hjlt⟩)
      (f := fun z : Fin (n + 1) → ℝ => Fin.init z)
      (hχ ⟨(j : ℕ), hjlt⟩) finInit_contDiffOn finInit_mapsTo).congr
      fun z _ => hnotlast z

end Work.WilG4c
