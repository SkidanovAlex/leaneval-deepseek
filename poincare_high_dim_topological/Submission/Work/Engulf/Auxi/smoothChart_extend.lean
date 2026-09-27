import Mathlib
import Submission.Work.Engulf.Basic

namespace Work.Engulf.Aux

/-- **`smoothChart_extend`** (Hx2e of `Submission/Work/NOTES_LEAD_poincare_E1fix.md` §1): adding frozen faces `S` on which `f` is globally `ψ`-affine keeps `ψ` a smoothing chart, provided every face inside `L ∪ S` is inside `L` or inside `S`. -/
theorem smoothChart_extend {n p N : ℕ} {M : Type*} [MetricSpace M] {X : Set M} {Γ : PL.Cx N}
    {L S : Set (PL.E N)} {f : PL.E N → M} {ψ : PL.CubeChart n M}
    (hψ : Work.Engulf.SmoothChart p X Γ L f ψ)
    (hsplit : ∀ s ∈ Γ.faces, PL.simp s ⊆ L ∪ S → PL.simp s ⊆ L ∨ PL.simp s ⊆ S)
    (hlin : ∀ s ∈ Γ.faces, PL.simp s ⊆ S → Work.Engulf.LinIn ψ f (PL.simp s)) :
    Work.Engulf.SmoothChart p X Γ (L ∪ S) f ψ := by
  refine ⟨hψ.1, ?_⟩
  intro s hs hsLS y hy hyc
  rcases hsplit s hs hsLS with hsL | hsS
  · exact hψ.2 s hs hsL y hy hyc
  · obtain ⟨A, hA⟩ := hlin s hs hsS
    exact ⟨1, one_pos, A, fun z hz => hA z hz.1⟩

end Work.Engulf.Aux
