import Mathlib
import Submission.Work.SymQuot.DivOf.Setup
import Submission.Work.SymQuot.Prod.isAffineOpen_piOpen
import Submission.Work.SymQuot.Sym.isIntegral_sym

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# `Γ(Cⁿ, Vⁿ)` is a domain (area SY, the `divOf` construction)

For a curve `C` over a field `K`, an open subscheme `V ⊆ C` and `n : ℕ` we show that the
sections of the `n`-fold power `Cⁿ` over the product open `Vⁿ = piOpen C V n` form an integral
domain.

The point is that the hypothesis is much stronger than needed: `Cⁿ` is an **integral** scheme
(`Work.SymQuot.isIntegral_prod`), so by `IsIntegral.component_integral` the sections over any
*nonempty* open subscheme of `Cⁿ` form a domain.  Nonemptiness of `Vⁿ` follows from
nonemptiness of `V`: the diagonal `C ⟶ Cⁿ` (all coordinates the identity) maps `V` into `Vⁿ`.
In particular the affineness hypothesis `hV` on `V` is not used.
-/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf

/-- **The diagonal** `C ⟶ Cⁿ`: the morphism of `K`-schemes all of whose coordinates are the
identity.  It is `Pi.lift` of the constant family `m ↦ 𝟙 C`. -/
noncomputable def diagOver {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ) :
    C.toOver ⟶ Work.SymQuot.prod C.toOver n :=
  Limits.Pi.lift (fun _ : Fin n => 𝟙 C.toOver)

/-- The `m`-th projection of the diagonal is the identity. -/
theorem diagOver_proj {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ)
    (m : Fin n) : diagOver C n ≫ Work.SymQuot.proj C.toOver n m = 𝟙 C.toOver := by
  rw [Work.SymQuot.proj]
  exact Limits.Pi.lift_comp_π _ m

/-- **The product open `Vⁿ` is nonempty when `V` is**: the diagonal maps any point of `V` into
`Vⁿ`. -/
theorem piOpen_nonempty {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ)
    (V : C.left.Opens) [Nonempty V] : Nonempty (Work.SymQuot.piOpen C.toOver V n) := by
  obtain ⟨x, hx⟩ := ‹Nonempty V›
  refine ⟨⟨(diagOver C n).left x, ?_⟩⟩
  rw [Work.SymQuot.mem_piOpen]
  intro m
  have h : (Work.SymQuot.proj C.toOver n m).left ((diagOver C n).left x) = x := by
    change (diagOver C n ≫ Work.SymQuot.proj C.toOver n m).left x = x
    rw [diagOver_proj]
    rfl
  rw [h]
  exact hx

theorem isDomain_piOpen_sections {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ) (V : C.left.Opens) [Nonempty V] (hV : AlgebraicGeometry.IsAffineOpen V) : IsDomain ((Work.SymQuot.prod C.toOver n).left.presheaf.obj (Opposite.op (Work.SymQuot.piOpen C.toOver V n))) := by
  haveI : IsIntegral (Work.SymQuot.prod C.toOver n).left := Work.SymQuot.isIntegral_prod C n
  haveI : Nonempty (Work.SymQuot.piOpen C.toOver V n) := piOpen_nonempty C n V
  infer_instance

end Work.SymQuot.DivOf
