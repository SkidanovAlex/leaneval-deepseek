import Mathlib
import Submission.Work.Thom.IsoPunct
import Submission.Work.Thom.complexPullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

/-!
# The fibre of a real bundle, and the fibre-generator condition for a Thom class

The two standard definitions of a *Thom class* of a rank-`n` real bundle `Z → B` are

* the **cup-map (iso) definition** — `Work.Thom.ThomClass Z n`, a class `τ ∈ H^n(E,E∖0)` for which
  `x ↦ π^*(x) ⌣ τ` is bijective in every degree (the one used everywhere in this workspace);
* the **fibrewise definition** — a class whose restriction to every *fibre pair*
  `(Z_b, Z_b∖0) ≅ (D^n, S^{n-1})` is a *generator* of `H^n(Z_b, Z_b∖0; ℤ) ≅ ℤ`
  (`Work.ThomBordism.IsFibreGenerator` below, the definition used in the classical texts, e.g.
  Hatcher §4.D, Milnor–Stasheff §10).

This module contains only the *definitions* (the fibre pair of a bundle, the restriction map to a
fibre, and the fibre-generator condition) so that lemmas about them can be stated and proved in
modules that do not import the (still incomplete) main file.

The two halves of the equivalence of the definitions at the *rank* degree are

* `Work.ThomBordism.thomClass_fibreGenerator`: `T : ThomClass Z n` with `n = Z.rank` restricts to
  a generator on every fibre (Hatcher's exercise after 4D.10);
* `Work.ThomBordism.thomClass_of_fibreGenerator`: a class at the rank degree restricting to a
  generator on every fibre is a Thom class (Hatcher's Corollary 4D.9, the Leray–Hirsch direction).
-/

namespace Work.ThomBordism

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}

/-- The **fibre of a real bundle `Z` over `b`**, as a subspace of the total space. -/
def fibre (Z : RealBundle B F ι) (b : B) : Set Z.TotalSpace := {p | p.1 = b}

/-- The **punctured fibre** of `Z` over `b`. -/
def fibrePunct (Z : RealBundle B F ι) (b : B) : Set Z.TotalSpace :=
  {p | p.1 = b ∧ (show F from p.2) ≠ 0}

/-- The inclusion of the fibre of `Z` over `b` into the total space. -/
def fibreIncl (Z : RealBundle B F ι) (b : B) : C(↥(fibre Z b), Z.TotalSpace) :=
  Work.Thom.subtypeMap (fibre Z b)

/-- The punctured part of the fibre, as a subset of the subtype `↥(fibre Z b)`. -/
def fibrePunctSub (Z : RealBundle B F ι) (b : B) : Set ↥(fibre Z b) :=
  (Subtype.val : ↥(fibre Z b) → Z.TotalSpace) ⁻¹' fibrePunct Z b

/-- The membership condition of the fibre inclusion. -/
theorem fibreIncl_mem (Z : RealBundle B F ι) (b : B) :
    ∀ x ∈ fibrePunctSub Z b, fibreIncl Z b x ∈ Work.Thom.zeroComplement Z :=
  fun x hx => hx.2

/-- The **restriction of a class of the Thom pair to a fibre**: the pullback along the inclusion of
the fibre pair `(Z_b, Z_b∖0) → (E, E∖0)`. -/
def fibreRes (Z : RealBundle B F ι) (b : B) (n : ℕ) :
    Work.Thom.OpenThom Z n →ₗ[ℤ]
      Work.Thom.RelCoh ℤ n ↥(fibre Z b) (fibrePunctSub Z b) :=
  (Work.Thom.relCohMap (fibreIncl Z b) (fibrePunctSub Z b) (Work.Thom.zeroComplement Z)
    (fibreIncl_mem Z b) ℤ n).hom

/-- A class of the Thom pair is a **fibre generator** if its restriction to every fibre pair
generates the relative cohomology of that fibre pair. -/
def IsFibreGenerator (Z : RealBundle B F ι) (n : ℕ) (σ : Work.Thom.OpenThom Z n) : Prop :=
  ∀ b : B, Submodule.span ℤ {fibreRes Z b n σ} = ⊤

end

end Work.ThomBordism
