import Submission.Work.CoreTopology.PieceData
import Submission.Work.CoreTopology.sphere_family

/-!
# Pardon's lemma `doublebubble`

A **double bubble** is a sphere `S` together with a disc `D` glued along its boundary to a
simple loop of `S`; the curve `∂D ⊆ S` divides `S` into two discs, and gluing one of them to
`D` produces two spheres `H₁`, `H₂`, the *halves* of the double bubble.

Pardon's `doublebubble` lemma: if a double bubble has all its intersections with `F`
inessential and

  `#(S ∩ β) + 2·#(D ∩ β) < I(F, β)`,

and if `F ∩ int(S)` contains an essential loop of `F`, then `F ∩ int(H_i)` contains an
essential loop for `i = 1` or `i = 2`.

The proof goes through a `2`-surgery family `S_t` of spheres from `S` to the two halves
(`S_0 = S`, `S_1` the union of the two boundary spheres of the halves, so that
`int(S_1) = int(H₁) ⊔ int(H₂)`, whence `H₁(F ∩ int S_1) → H₁(F)` factors through
`H₁(F ∩ int H₁) ⊕ H₁(F ∩ int H₂)`).  For every `t` the intersection `S_t ∩ F` consists of
inessential curves — by `mustbeinessential`, since `#(S_t ∩ β) ≤ #(S ∩ β) + 2#(D ∩ β) <
I(F,β)` — and the invariant `W t = im(H₁(F ∩ int S_t) → H₁(F))` is `0` or everything, with
each surgery changing it by at most `1`; hence it is constant and `W 1 = ⊤`.

`sphere_family` is the algebraic content of that last sentence; this file packages it in the
geometric vocabulary of pieces of the torus and of "contains an essential loop".
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

/-- **Pardon's Lemma 3, "double bubble" (specialised to a torus).**

`H` records the invariant `H₁(F ∩ U ; ℚ) → H₁(F ; ℚ)` for regions `U ⊆ ℝ³`, `Sint` is the
interior of the original sphere `S`, `H₁`, `H₂` are the interiors of the two halves of the
double bubble, and `W : ℝ → Submodule ℚ A` is the invariant along the surgery family, from
`W 0 = H.hom Sint` to `W 1 = H.hom H₁ ⊔ H.hom H₂`.

If the dichotomy `0 / all` holds for the pieces, the initial piece contains an essential
loop, and the family satisfies the surgery dimension bounds, then one of the two halves
contains an essential loop. -/
theorem double_bubble {P : ParamTorus} {A : Type*} [AddCommGroup A] [Module ℚ A]
    [FiniteDimensional ℚ A] [Nontrivial A]
    (H : HomPieceData P A) (W : ℝ → Submodule ℚ A) (Sint H₁ H₂ : Set R3)
    (hA : 1 < Module.finrank ℚ A)
    (hdich : H.Dichotomy)
    (hSess : H.HasEssentialLoop Sint)
    (hval : ∀ t : ℝ, W t = ⊥ ∨ W t = ⊤)
    (hstep : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε →
      Module.finrank ℚ ↥(W s) ≤ Module.finrank ℚ ↥(W t) + 1 ∧
      Module.finrank ℚ ↥(W t) ≤ Module.finrank ℚ ↥(W s) + 1)
    (hW0 : W 0 = H.hom Sint)
    (hdecomp : W 1 = H.hom H₁ ⊔ H.hom H₂) :
    H.HasEssentialLoop H₁ ∨ H.HasEssentialLoop H₂ := by
  rcases hdich Sint with h | h
  · exact absurd h hSess
  · rcases sphere_family W (H.hom H₁) (H.hom H₂) hA hval hstep (by rw [hW0, h]) hdecomp
        (hdich H₁) (hdich H₂) with h1 | h1
    · exact Or.inl (HomPieceData.HasEssentialLoop.of_hom_eq_top H h1)
    · exact Or.inr (HomPieceData.HasEssentialLoop.of_hom_eq_top H h1)

/-- Variant of `double_bubble` in which the dichotomy is assumed only for the three relevant
pieces (`Sint`, `H₁`, `H₂`) and the family `W`, rather than for every region of `ℝ³`. -/
theorem double_bubble_of_pieces {P : ParamTorus} {A : Type*} [AddCommGroup A] [Module ℚ A]
    [FiniteDimensional ℚ A] [Nontrivial A]
    (H : HomPieceData P A) (W : ℝ → Submodule ℚ A) (Sint H₁ H₂ : Set R3)
    (hA : 1 < Module.finrank ℚ A)
    (hdichS : H.hom Sint = ⊥ ∨ H.hom Sint = ⊤)
    (hSess : H.HasEssentialLoop Sint)
    (hval : ∀ t : ℝ, W t = ⊥ ∨ W t = ⊤)
    (hstep : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t| < ε →
      Module.finrank ℚ ↥(W s) ≤ Module.finrank ℚ ↥(W t) + 1 ∧
      Module.finrank ℚ ↥(W t) ≤ Module.finrank ℚ ↥(W s) + 1)
    (hW0 : W 0 = H.hom Sint)
    (hdecomp : W 1 = H.hom H₁ ⊔ H.hom H₂)
    (hval1 : H.hom H₁ = ⊥ ∨ H.hom H₁ = ⊤) (hval2 : H.hom H₂ = ⊥ ∨ H.hom H₂ = ⊤) :
    H.HasEssentialLoop H₁ ∨ H.HasEssentialLoop H₂ := by
  rcases hdichS with h | h
  · exact absurd h hSess
  · rcases sphere_family W (H.hom H₁) (H.hom H₂) hA hval hstep (by rw [hW0, h]) hdecomp
        hval1 hval2 with h1 | h1
    · exact Or.inl (HomPieceData.HasEssentialLoop.of_hom_eq_top H h1)
    · exact Or.inr (HomPieceData.HasEssentialLoop.of_hom_eq_top H h1)

end

end Work.CoreTopology
