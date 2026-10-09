/-
Copyright (c) 2025. All rights reserved.

# The abstract setting attached to an embedding problem over `ℚ`

This file instantiates `Work.Properness.Setup` (the abstract setting of an embedding problem with
abelian kernel) at

* `H = G_ℚ`, the absolute Galois group of `ℚ`;
* `E = E.G`, the group of the embedding problem;
* `Q = Gal(M.L/ℚ)`, where `M` is a closure model of the embedding problem;
* `π = M.pi : E.G →* Gal(M.L/ℚ)`, the projection of the embedding problem (a surjection);
* `ρ = restrictHom M.L : G_ℚ →* Gal(M.L/ℚ)`, the restriction map (a surjection).

In this dictionary `H_K = ker ρ` is the absolute Galois group of the field cut out by the base
field `M.L`, i.e. `G_L` for the field `L = M.L` of the paper, and a lift `ψ : G_ℚ →* E.G` with
`M.pi ∘ ψ = restrictHom M.L` is exactly a *solution* of the embedding problem (a splitting of the
fibre product `pullback E M`), which is *proper* iff `ψ` is surjective — i.e. iff (by
`Work.AbsoluteGalois.isSolvable_iff_hasSurjectiveLift`) the embedding problem is solvable.

## Main declarations

* `Work.Properness.closureToSetup` — the abstract setting attached to `E` and `M`;
* `Work.Properness.closureToSetup_H`, `_E`, `_Q`, `_π`, `_ρ`, `_A`, `_HK` — the computation rules.
-/
import Mathlib
import Submission.EmbeddingProblem
import Submission.Work.AbsoluteGalois.Basic
import Submission.Work.AbsoluteGalois.ClosureModel
import Submission.Work.AbsoluteGalois.Obstruction
import Submission.Work.AbsoluteGalois.ObstructionLink
import Submission.Work.Properness.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Properness

open scoped Classical

noncomputable section

/-- **The abstract setting attached to an embedding problem over `ℚ` with abelian kernel.**
`H = G_ℚ`, `E = E.G`, `Q = Gal(M.L/ℚ)`, `π = M.pi`, `ρ = restrictHom M.L`. -/
noncomputable def closureToSetup {E : Submission.EmbeddingProblem ℚ} (M : E.ClosureModel)
    (hcomm : ∀ a b : M.pi.ker, a * b = b * a) : Setup where
  H := Field.absoluteGaloisGroup ℚ
  E := E.G
  Q := ↥M.L ≃ₐ[ℚ] ↥M.L
  π := M.pi
  π_surj := M.pi_surjective
  ρ := Work.AbsoluteGalois.restrictHom M.L
  ρ_surj := by
    haveI : Normal ℚ ↥M.L := M.isGalois.to_normal
    exact Work.AbsoluteGalois.restrictHom_surjective M.L
  ker_comm := hcomm

variable {E : Submission.EmbeddingProblem ℚ} (M : E.ClosureModel)
  (hcomm : ∀ a b : M.pi.ker, a * b = b * a)

@[simp] theorem closureToSetup_H : (closureToSetup M hcomm).H = Field.absoluteGaloisGroup ℚ := rfl

@[simp] theorem closureToSetup_E : (closureToSetup M hcomm).E = E.G := rfl

@[simp] theorem closureToSetup_Q : (closureToSetup M hcomm).Q = (↥M.L ≃ₐ[ℚ] ↥M.L) := rfl

@[simp] theorem closureToSetup_π : (closureToSetup M hcomm).π = M.pi := rfl

@[simp] theorem closureToSetup_ρ :
    (closureToSetup M hcomm).ρ = Work.AbsoluteGalois.restrictHom M.L := rfl

end

end Work.Properness
