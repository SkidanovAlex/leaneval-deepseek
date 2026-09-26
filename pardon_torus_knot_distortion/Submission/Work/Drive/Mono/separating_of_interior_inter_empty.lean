import Mathlib

namespace Work.Drive.Mono

/-- Separation of two closed convex sets in `ℝ²` whose interiors are disjoint: there is a nonzero
continuous linear functional `f` and a level `c` such that `A` lies in the half space `f ≤ c`, `B`
lies in `f ≥ c`, and the two sets meet only on the level `f = c`.

The separation of the interiors is a direct instance of the Hahn–Banach separation theorem; the
inequality is then extended from `interior B` to `B` by closedness (`closure (interior B) = B` for a
closed convex set with nonempty interior). -/
theorem separating_of_interior_inter_empty {A B : Set (EuclideanSpace ℝ (Fin 2))}
    (hAc : Convex ℝ A) (hAcl : IsClosed A) (hAne : (interior A).Nonempty)
    (hBc : Convex ℝ B) (hBcl : IsClosed B) (hBne : (interior B).Nonempty)
    (hd : Disjoint (interior A) (interior B)) :
    ∃ (f : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧
      A ⊆ {x | f x ≤ c} ∧ B ⊆ {x | f x ≥ c} ∧ A ∩ B ⊆ {x | f x = c} := by
  obtain ⟨f, c, hf0, hA, hB⟩ :=
    geometric_hahn_banach_of_nonempty_interior hAc hBc.interior hd hAne hBne
  -- the inequality `c ≤ f` holds on the interior of `B`; extend it to `B` by closedness
  have hclB : B = closure (interior B) := by
    rw [Convex.closure_interior_eq_closure_of_nonempty_interior hBc hBne, hBcl.closure_eq]
  have hB' : ∀ b ∈ B, c ≤ f b := by
    have hsub : closure (interior B) ⊆ {x : EuclideanSpace ℝ (Fin 2) | c ≤ f x} :=
      closure_minimal (fun x hx => hB x hx) (isClosed_Ici.preimage f.continuous)
    exact fun b hb => hsub (hclB ▸ hb)
  exact ⟨f, c, hf0, hA, hB', fun x hx => le_antisymm (hA x hx.1) (hB' x hx.2)⟩

end Work.Drive.Mono
