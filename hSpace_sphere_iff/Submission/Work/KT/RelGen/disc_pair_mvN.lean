import Mathlib
import Submission.Work.KT.ExtGen.disc_square
import Submission.Work.KT.Bott.GlueAux

/-!
# `Work.KT.RelGen.disc_pair_mvN`

Gluing of Murray–von Neumann data over the Cartesian square

```
pullAlg2 X --fstProj--> C(X × D, ℂ)
    |                        |
 sndProj                bdryRestrict
    v                        v
C(X × D, ℂ) --bdryRestrict--> C(X × S¹, ℂ)
```

of `Work.KT.ExtGen.disc_square`.  If a pair of matrices `P`, `Q` over `pullAlg2 X` becomes
Murray–von Neumann equivalent over each of the two discs (`bᵢ * aᵢ = P`, `aᵢ * bᵢ = Q` for the two
projections `i = 1, 2`) and the witnessing matrices agree on the boundary circle, then `P` and `Q`
are already Murray–von Neumann equivalent over `pullAlg2 X` — the two witnesses glue entrywise
along the Cartesian square, and the two identities are checked after both projections.

This is the "excision/descent" step of the relative generation argument for
`K₀(C(X × S², ℂ))`: classes that become trivial on each disc, compatibly on the equator, are
trivial on `X × S²`.
-/

namespace Work.KT.RelGen


/-- **Descent of Murray–von Neumann equivalence along the disc square.**  A compatible pair of
Murray–von Neumann data over the two discs glues to Murray–von Neumann data over `pullAlg2 X`. -/
theorem disc_pair_mvN (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {m k : ℕ} (P : Matrix (Fin m) (Fin m) ↥(Work.KT.Fund.pullAlg2 X))
    (Q : Matrix (Fin k) (Fin k) ↥(Work.KT.Fund.pullAlg2 X))
    (a₁ : Matrix (Fin k) (Fin m) C(X × Ball ℂ, ℂ)) (b₁ : Matrix (Fin m) (Fin k) C(X × Ball ℂ, ℂ))
    (a₂ : Matrix (Fin k) (Fin m) C(X × Ball ℂ, ℂ)) (b₂ : Matrix (Fin m) (Fin k) C(X × Ball ℂ, ℂ))
    (h₁ : b₁ * a₁ = P.map (Work.KT.ExtGen.fstProj X)) (h₂ : a₁ * b₁ = Q.map (Work.KT.ExtGen.fstProj X))
    (h₃ : b₂ * a₂ = P.map (Work.KT.ExtGen.sndProj X)) (h₄ : a₂ * b₂ = Q.map (Work.KT.ExtGen.sndProj X))
    (ha : a₁.map (Work.KT.Fund.bdryRestrict X) = a₂.map (Work.KT.Fund.bdryRestrict X))
    (hb : b₁.map (Work.KT.Fund.bdryRestrict X) = b₂.map (Work.KT.Fund.bdryRestrict X)) :
    Work.KT.Mat.MvN (⟨m, P⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
      (⟨k, Q⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) := by
  have hpb := Work.KT.ExtGen.square_patch X
  have hcomm := Work.KT.ExtGen.square_comm X
  -- The two discs share the same boundary values, entrywise.
  have hac : ∀ i j, Work.KT.Fund.bdryRestrict X (a₁ i j) = Work.KT.Fund.bdryRestrict X (a₂ i j) := by
    intro i j
    have h := congrFun (congrFun ha i) j
    simpa [Matrix.map_apply] using h
  have hbc : ∀ i j, Work.KT.Fund.bdryRestrict X (b₁ i j) = Work.KT.Fund.bdryRestrict X (b₂ i j) := by
    intro i j
    have h := congrFun (congrFun hb i) j
    simpa [Matrix.map_apply] using h
  -- Glue the entrance and exit maps along the Cartesian square.
  obtain ⟨A, hA₁, hA₂⟩ := Work.KT.Bott.mat_lift (Work.KT.ExtGen.fstProj X) (Work.KT.ExtGen.sndProj X)
      (Work.KT.Fund.bdryRestrict X) (Work.KT.Fund.bdryRestrict X) hpb a₁ a₂ hac
  obtain ⟨B, hB₁, hB₂⟩ := Work.KT.Bott.mat_lift (Work.KT.ExtGen.fstProj X) (Work.KT.ExtGen.sndProj X)
      (Work.KT.Fund.bdryRestrict X) (Work.KT.Fund.bdryRestrict X) hpb b₁ b₂ hbc
  refine ⟨A, B, ?_, ?_⟩
  · -- `B * A = P`, checked after both projections.
    apply Work.KT.Bott.mat_ext_of_maps (Work.KT.ExtGen.fstProj X) (Work.KT.ExtGen.sndProj X)
      (Work.KT.Fund.bdryRestrict X) (Work.KT.Fund.bdryRestrict X) hcomm hpb
    · rw [Matrix.map_mul, hB₁, hA₁]; exact h₁
    · rw [Matrix.map_mul, hB₂, hA₂]; exact h₃
  · -- `A * B = Q`, checked after both projections.
    apply Work.KT.Bott.mat_ext_of_maps (Work.KT.ExtGen.fstProj X) (Work.KT.ExtGen.sndProj X)
      (Work.KT.Fund.bdryRestrict X) (Work.KT.Fund.bdryRestrict X) hcomm hpb
    · rw [Matrix.map_mul, hA₁, hB₁]; exact h₂
    · rw [Matrix.map_mul, hA₂, hB₂]; exact h₄

end Work.KT.RelGen
