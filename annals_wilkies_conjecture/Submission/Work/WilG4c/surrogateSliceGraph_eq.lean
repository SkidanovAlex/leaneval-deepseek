import Mathlib
import Submission.Work.WilG4c.SlicePinnedDefs

namespace Work.WilG4c

theorem surrogateSliceGraph_eq (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)) (M : List (Fin n)) :
    WilkiesDesign.CG.famGraph (fun (l : Fin p → ℝ) (x : Fin 1 → ℝ) =>
        Work.WilkG4c.surrogateSlice p n f γ M l (x 0))
      = {z : Fin (p + 1 + 1) → ℝ |
          (∃ t : ℝ, Fin.snoc (Work.WilkG4c.xPt (fun i : Fin p => (Fin.init z) (Fin.castSucc i))
                ((Fin.init z) (Fin.last p))
                (fun j : Fin n => γ (fun i : Fin p => (Fin.init z) (Fin.castSucc i))
                  ((Fin.init z) (Fin.last p)) j)) t
              ∈ Work.WilkG4c.pinDg p n f M ∧ z (Fin.last (p + 1)) = (t + 2) / 4) ∨
          (Work.WilkG4c.xPt (fun i : Fin p => (Fin.init z) (Fin.castSucc i))
                ((Fin.init z) (Fin.last p))
                (fun j : Fin n => γ (fun i : Fin p => (Fin.init z) (Fin.castSucc i))
                  ((Fin.init z) (Fin.last p)) j)
              ∉ WilkiesDesign.projLast (Work.WilkG4c.pinDg p n f M) ∧
            z (Fin.last (p + 1)) = 1 / 2)} := by
  ext z
  let lz : Fin p → ℝ := fun i => (Fin.init z) (Fin.castSucc i)
  let xz : ℝ := (Fin.init z) (Fin.last p)
  let yz : Fin n → ℝ := fun j => γ lz xz j
  let W : Fin (p + (n + 1)) → ℝ := Work.WilkG4c.xPt lz xz yz
  change (z (Fin.last (p + 1)) = Work.WilkG4c.surrogateSlice p n f γ M lz xz) ↔
    ((∃ t : ℝ, Fin.snoc W t ∈ Work.WilkG4c.pinDg p n f M ∧
        z (Fin.last (p + 1)) = (t + 2) / 4) ∨
      (W ∉ WilkiesDesign.projLast (Work.WilkG4c.pinDg p n f M) ∧
        z (Fin.last (p + 1)) = 1 / 2))
  have hmem : ∀ t : ℝ, Fin.snoc W t ∈ Work.WilkG4c.pinDg p n f M ↔
      ContDiffAt ℝ M.length (Work.WilkG4c.slice (f lz) xz) yz ∧
        t = iteratedFDeriv ℝ M.length (Work.WilkG4c.slice (f lz) xz) yz (fun j => Pi.single (M.get j) 1) := by
    intro t
    rw [Work.WilkG4c.snoc_mem_pinDg]
    dsimp only [W]
    rw [Work.WilkG4c.pinL_xPt, Work.WilkG4c.pinX_xPt, Work.WilkG4c.pinY_xPt]
  have hproj : W ∈ WilkiesDesign.projLast (Work.WilkG4c.pinDg p n f M) ↔
      ContDiffAt ℝ M.length (Work.WilkG4c.slice (f lz) xz) yz := by
    rw [Work.WilkG4c.projLast_pinDg]
    simp only [Set.mem_ofPred_eq]
    dsimp only [W]
    rw [Work.WilkG4c.pinL_xPt, Work.WilkG4c.pinX_xPt, Work.WilkG4c.pinY_xPt]
  by_cases h : ContDiffAt ℝ M.length (Work.WilkG4c.slice (f lz) xz) yz
  · rw [Work.WilkG4c.surrogateSlice_of_mem h]
    have h1 : (∃ t : ℝ, Fin.snoc W t ∈ Work.WilkG4c.pinDg p n f M ∧
          z (Fin.last (p + 1)) = (t + 2) / 4) ↔
        z (Fin.last (p + 1)) =
          (iteratedFDeriv ℝ M.length (Work.WilkG4c.slice (f lz) xz) yz (fun j => Pi.single (M.get j) 1)
            + 2) / 4 := by
      constructor
      · rintro ⟨t, ht, hv⟩
        rw [hmem t] at ht
        exact hv.trans (by rw [ht.2])
      · rintro hv
        exact ⟨_, by rw [hmem]; exact ⟨h, rfl⟩, hv⟩
    have h2 : ¬ (W ∉ WilkiesDesign.projLast (Work.WilkG4c.pinDg p n f M) ∧
          z (Fin.last (p + 1)) = 1 / 2) := by
      rintro ⟨hn, -⟩
      exact hn (hproj.mpr h)
    rw [h1]
    constructor
    · exact Or.inl
    · rintro (hv | hP2)
      · exact hv
      · exact absurd hP2 h2
  · rw [Work.WilkG4c.surrogateSlice_of_not_mem h]
    have h1 : ¬ (∃ t : ℝ, Fin.snoc W t ∈ Work.WilkG4c.pinDg p n f M ∧
          z (Fin.last (p + 1)) = (t + 2) / 4) := by
      rintro ⟨t, ht, -⟩
      rw [hmem t] at ht
      exact h ht.1
    have h2 : (W ∉ WilkiesDesign.projLast (Work.WilkG4c.pinDg p n f M) ∧
          z (Fin.last (p + 1)) = 1 / 2) ↔ z (Fin.last (p + 1)) = 1 / 2 := by
      have hp : W ∉ WilkiesDesign.projLast (Work.WilkG4c.pinDg p n f M) :=
        fun hw => h (hproj.mp hw)
      constructor
      · rintro ⟨-, hv⟩; exact hv
      · intro hv; exact ⟨hp, hv⟩
    rw [h2]
    constructor
    · exact Or.inr
    · rintro (hv | hv)
      · exact absurd hv h1
      · exact hv

end Work.WilG4c
