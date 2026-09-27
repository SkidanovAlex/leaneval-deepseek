import Submission.Work.PL.Approx.SdSubdiv
import Submission.Work.PL.Approx.pl_approx
import Submission.Work.PL.Approx.pl_approx_of_osc
import Submission.Work.PL.Approx.Near.oscillation_of_mesh
import Submission.Work.PL.Approx.Frozen.pl_approx_frozen_fine

/-!
# `pl_approx` for the actual barycentric subdivision

The PL approximation theorem of this area (`Work.PL.Approx.pl_approx`) is stated for an abstract
`Subdiv`.  This file records the two forms in which the engulfing argument uses it, with the
barycentric subdivision `sdSubdiv` of area A2 substituted:

* `pl_approx_sd` -- `pl_approx` for `sdSubdiv`;
* `pl_approx_sd_of_mesh` -- the form where the subdivision is *given* and only its mesh matters
  (the oscillation hypothesis is derived from uniform continuity of `f` via
  `Near/oscillation_of_mesh`).
-/

open Set Metric

namespace Work.PL.Approx

noncomputable section

variable {N n : ℕ}

/-- `pl_approx` for the barycentric subdivision of area A2. -/
theorem pl_approx_sd (K : PL.Cx N) (hK : K.faces.Finite) (f : PL.E N → PL.E n)
    (hf : ContinuousOn f K.space) (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ1 : β < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, ∃ g : PL.E N → PL.E n, ContinuousOn g K.space ∧
      (∀ x ∈ K.space, dist (g x) (f x) < ε) ∧
      (∀ x ∈ K.space, f x ∉ PL.closedCube β → g x = f x) ∧
      ∀ s ∈ ((sdSubdiv N).iter r K hK).faces, (∃ x ∈ PL.simp s, g x ∈ PL.closedCube α) →
        ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ y ∈ PL.simp s, g y = A y :=
  pl_approx (sdSubdiv N) K hK f hf α β hα hαβ hβ1 ε hε

/-- `pl_approx_of_osc` in the mesh form, for a subdivision `K'` of `K` all of whose simplices have
vertex diameter `< δ`, where `δ` is a modulus of uniform continuity of `f` for the threshold
`min ε ((β - α)/24)`. -/
theorem pl_approx_of_osc_of_mesh (K K' : PL.Cx N) (hK' : K'.faces.Finite) (f : PL.E N → PL.E n)
    (hf : ContinuousOn f K.space) (hsub : PL.Subdivides K' K) (α β : ℝ) (hα : 0 < α)
    (hαβ : α < β) (hβ1 : β < 1) (ε : ℝ) (hε : 0 < ε) {δ : ℝ}
    (hδ : ∀ x ∈ K.space, ∀ y ∈ K.space, dist x y < δ → dist (f x) (f y) < min ε ((β - α) / 24))
    (hmesh : PL.MeshLT K' δ) :
    ∃ g : PL.E N → PL.E n, ContinuousOn g K.space ∧ (∀ x ∈ K.space, dist (g x) (f x) < ε) ∧
      (∀ x ∈ K.space, f x ∉ PL.closedCube β → g x = f x) ∧
      ∀ s ∈ K'.faces, (∃ x ∈ PL.simp s, g x ∈ PL.closedCube α) →
        ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ y ∈ PL.simp s, g y = A y :=
  pl_approx_of_osc K K' hK' f hf hsub α β hα hαβ hβ1 ε hε
    (Near.oscillation_of_mesh K K' hsub f hmesh hδ)

/-- The output of `pl_approx` in `PL.LinOn` form: every subcomplex of the fine subdivision all of
whose faces meet `g ⁻¹' closedCube α` is mapped linearly by `g`. -/
theorem pl_approx_LinOn (S : Subdiv N) (K : PL.Cx N) (hK : K.faces.Finite) (f : PL.E N → PL.E n)
    (hf : ContinuousOn f K.space) (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ1 : β < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, ∃ g : PL.E N → PL.E n, ContinuousOn g K.space ∧
      (∀ x ∈ K.space, dist (g x) (f x) < ε) ∧
      (∀ x ∈ K.space, f x ∉ PL.closedCube β → g x = f x) ∧
      ∀ M : PL.Cx N, PL.IsSub M (S.iter r K hK) →
        (∀ s ∈ M.faces, ∃ x ∈ PL.simp s, g x ∈ PL.closedCube α) → PL.LinOn M g := by
  obtain ⟨r, g, hcont, hnear, hfix, hlin⟩ := pl_approx S K hK f hf α β hα hαβ hβ1 ε hε
  exact ⟨r, g, hcont, hnear, hfix, fun M hM hmeet s hs => hlin s (hM hs) (hmeet s hs)⟩

/-- The output of the frozen variant `pl_approx_frozen_fine` in `PL.LinOn` form. -/
theorem pl_approx_frozen_LinOn (K : PL.Cx N) (hK : K.faces.Finite) (L : PL.Cx N)
    (hLK : PL.IsSub L K) (hLfin : L.faces.Finite) (r : ℕ) (f : PL.E N → PL.E n)
    (hf : ContinuousOn f K.space) (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ1 : β < 1)
    (ε : ℝ) (hε : 0 < ε)
    (hlinL : ∀ ρ ∈ L.faces, (∃ z ∈ PL.simp ρ, f z ∈ PL.closedCube β) →
      ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ z ∈ PL.simp ρ, f z = A z)
    (hosc : ∀ s ∈ ((sdSubdiv N).iter r K hK).faces, ∀ x ∈ PL.simp s, ∀ y ∈ PL.simp s,
      dist (f x) (f y) < min ε ((β - α) / 24)) :
    ∃ g : PL.E N → PL.E n, ContinuousOn g K.space ∧ (∀ x ∈ K.space, dist (g x) (f x) < ε) ∧
      (∀ x ∈ K.space, f x ∉ PL.closedCube β → g x = f x) ∧ (∀ x ∈ L.space, g x = f x) ∧
      ∀ M : PL.Cx N, PL.IsSub M ((sdSubdiv N).iter r K hK) →
        (∀ s ∈ M.faces, ∃ x ∈ PL.simp s, g x ∈ PL.closedCube α) → PL.LinOn M g := by
  obtain ⟨g, hcont, hnear, hfix, hfrozen, hlin⟩ :=
    Frozen.pl_approx_frozen_fine K hK L hLK hLfin r f hf α β hα hαβ hβ1 ε hε hlinL hosc
  exact ⟨g, hcont, hnear, hfix, hfrozen, fun M hM hmeet s hs => hlin s (hM hs) (hmeet s hs)⟩

end

end Work.PL.Approx
