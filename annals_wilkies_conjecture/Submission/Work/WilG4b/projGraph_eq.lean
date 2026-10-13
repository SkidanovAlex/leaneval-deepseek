import Mathlib
import Submission.Work.WilG4b.Basic
import Submission.Work.WilG4b.projCoords_mem

namespace Work.WilG4b

/-- The graph of `x ↦ γ x i` in `ℝ²` is exactly the projection of the graph of `γ`
(over the coordinates `(x, y) = (z 0, z (Fin.natAdd 1 i))`) onto the two coordinates `0`
and `Fin.natAdd 1 i`. -/
theorem projGraph_eq {n : ℕ} (γ : (Fin 1 → ℝ) → (Fin (n + 2) → ℝ)) (i : Fin (n + 2)) :
    {y : Fin 2 → ℝ | ∃ z : Fin (1 + (n + 2)) → ℝ,
        (∀ j : Fin (n + 2), z (Fin.natAdd 1 j) = γ (fun i => z (Fin.castAdd (n + 2) i)) j) ∧
        y = z ∘ (fun j : Fin 2 => if j = 0 then (0 : Fin (1 + (n + 2))) else Fin.natAdd 1 i)} =
      WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => γ x i) := by
  ext y
  simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    -- the projection of the graph of `γ` lands in the graph of `x ↦ γ x i`
    have he1 : (fun j : Fin 2 => if j = 0 then (0 : Fin (1 + (n + 2))) else Fin.natAdd 1 i) 1
        = Fin.natAdd 1 i := by simp
    have hinit : Fin.init (z ∘ (fun j : Fin 2 =>
          if j = 0 then (0 : Fin (1 + (n + 2))) else Fin.natAdd 1 i))
        = (fun i : Fin 1 => z (Fin.castAdd (n + 2) i)) := by
      funext j
      fin_cases j
      simp only [Fin.init, Function.comp_apply]
      rfl
    change (z ∘ (fun j : Fin 2 =>
        if j = 0 then (0 : Fin (1 + (n + 2))) else Fin.natAdd 1 i)) 1
      = γ (Fin.init (z ∘ (fun j : Fin 2 =>
        if j = 0 then (0 : Fin (1 + (n + 2))) else Fin.natAdd 1 i))) i
    rw [hinit]
    simp only [Function.comp_apply, he1]
    exact hz i
  · intro h
    -- conversely, a point `(y 0, γ (y 0) i)` of the graph of `x ↦ γ x i` lifts to the graph of `γ`
    have h' : y 1 = γ (fun _ : Fin 1 => y 0) i := by
      rw [show Fin.last 1 = (1 : Fin 2) from rfl] at h
      rwa [show Fin.init y = (fun _ : Fin 1 => y 0) from by
        funext j; fin_cases j; rfl] at h
    refine ⟨Fin.append (fun _ : Fin 1 => y 0) (fun j : Fin (n + 2) => γ (fun _ : Fin 1 => y 0) j),
      ?_, ?_⟩
    · intro j
      rw [Fin.append_right]
      congr 1
      funext i; fin_cases i
      simp only [Fin.append_left]
    · funext j
      fin_cases j
      · show y 0 = Fin.append (fun _ : Fin 1 => y 0)
          (fun j => γ (fun _ : Fin 1 => y 0) j)
          (if (0 : Fin 2) = 0 then (0 : Fin (1 + (n + 2))) else Fin.natAdd 1 i)
        rw [ite_eq_left rfl]
        rfl
      · show y 1 = Fin.append (fun _ : Fin 1 => y 0)
          (fun j => γ (fun _ : Fin 1 => y 0) j)
          (if (1 : Fin 2) = 0 then (0 : Fin (1 + (n + 2))) else Fin.natAdd 1 i)
        rw [ite_eq_right (by decide), Fin.append_right]
        exact h'

end Work.WilG4b
