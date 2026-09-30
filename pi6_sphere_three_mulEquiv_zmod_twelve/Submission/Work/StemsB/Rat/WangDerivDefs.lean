import Mathlib
import Submission.Work.StemsB.WangDerivation
import Submission.Work.StemsB.Rat.WangGammaExplicit
import Submission.Work.StemsB.Rat.CollarClutch
import Submission.Work.StemsB.Rat.CollarLambdaOatIso
import Submission.Work.StemsB.Rat.SuspSq
import Submission.Work.StemsB.Rat.CollarCup

/-!
# The collar transgression of the Wang sequence: definitions

This file collects the objects of the derivation argument for
`Work.StemsB.wangSphereDerivation_exists`:

* the collar sets `wangA` (`p ⁻¹' sphLoopOuter b`), `wangA1` (the collar preimage inside `E|_G`)
  and `wangCQ` (the collar inside `↥(sphLoopBig b) × ↥(p ⁻¹' {d_G.1})`), together with the two
  maps of pairs `wangExc` (the inclusion `(E|_G, E|_C) → (E, E|_O)`) and `wangTriv`
  (the trivialisation `Ψ_G` over the inner cube);

* the suspension class `s` and Thom class `τ` of `Work.StemsB.Rat.collarSuspensionClass_sq`, extracted
  with `Classical.choose` (`wangSusS`, `wangSusT`) together with their properties;

* `wangTheta`, the geometric transgression `θ = ρ ∘ Σ ∘ u`: the composite of the pullback `u` along
  the clutching map `λ_G`, the collar transgression coefficient map `Σ` (`Work.StemsB.Rat.collarSigma`)
  and the pullback `ρ` along `λ_O-pt` (`Work.StemsB.Rat.rhoCoh`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.StemsB.Rat

noncomputable section

variable {E : Type} [TopologicalSpace E]

/-- The fibre of `p` over the point `d_G.1` of the inner cube. -/
abbrev wangFY (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b)) : Type := ↥(p ⁻¹' {d_G.1})

/-- The collar inside `↥(sphLoopBig b) × ↥(p ⁻¹' {d_G.1})`. -/
abbrev wangCQ (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b)) :
    Set (↥(sphLoopBig b) × wangFY b p d_G) := sphLoopCollarProd b (wangFY b p d_G)

/-- The collar preimage inside `E|_G = p ⁻¹' sphLoopBig b`. -/
abbrev wangA1 (b : ℕ) (p : C(E, SphModel b)) : Set ↥(p ⁻¹' sphLoopBig b) :=
  {x | (x : E) ∈ p ⁻¹' sphLoopCollar b}

/-- The outer preimage `p ⁻¹' sphLoopOuter b` in the total space. -/
abbrev wangA (b : ℕ) (p : C(E, SphModel b)) : Set E := p ⁻¹' sphLoopOuter b

/-- `E|_G = p ⁻¹' sphLoopBig b`, as a space. -/
abbrev wangEG (b : ℕ) (p : C(E, SphModel b)) : TopCat := TopCat.of ↥(p ⁻¹' sphLoopBig b)

/-- The inclusion `E|_G ↪ E`. -/
def wangExcMap (b : ℕ) (p : C(E, SphModel b)) : C(↥(p ⁻¹' sphLoopBig b), E) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion `E|_G ↪ E` maps the collar preimage into the outer preimage. -/
theorem wangExcMap_mem (b : ℕ) (p : C(E, SphModel b)) :
    ∀ x ∈ wangA1 b p, wangExcMap b p x ∈ wangA b p := by
  intro x hx
  exact hx.1

/-- The trivialisation `Ψ_G` maps the collar product into the collar preimage of `E|_G`. -/
theorem wangTrivMap_mem (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) :
    ∀ q ∈ wangCQ b p d_G, fibTrivΨ p (sphLoopBig b) d_G hT_G q ∈ wangA1 b p := by
  intro q hq
  show (fibTrivΨ p (sphLoopBig b) d_G hT_G q : E) ∈ p ⁻¹' sphLoopCollar b
  exact fibTrivΨ_mem (sphLoopBig b) d_G hT_G q (sphLoopCollar b) hq

/-- **Excision**, as a cohomology map: `H^*(E, E|_O) → H^*(E|_G, E|_C)`. -/
def wangExc (b : ℕ) (p : C(E, SphModel b)) (k : ℕ) :
    (Work.Cohomology.relComplex ℚ (TopCat.of E) (wangA b p)).homology k ⟶
      (Work.Cohomology.relComplex ℚ (wangEG b p) (wangA1 b p)).homology k :=
  HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := wangEG b p)
    (X₂ := TopCat.of E) ℚ (wangA1 b p) (wangA b p)
    (TopCat.ofHom (wangExcMap b p)) (wangExcMap_mem b p)) k

/-- **The trivialisation**, as a cohomology map: `H^*(E|_G, E|_C) → H^*(Q, C_Q)` along `Ψ_G`. -/
def wangTriv (b : ℕ) (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (k : ℕ) :
    (Work.Cohomology.relComplex ℚ (wangEG b p) (wangA1 b p)).homology k ⟶
      (Work.Cohomology.relComplex ℚ
        (TopCat.of (↥(sphLoopBig b) × wangFY b p d_G))
        (wangCQ b p d_G)).homology k :=
  HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap
    (X₁ := TopCat.of (↥(sphLoopBig b) × wangFY b p d_G)) (X₂ := wangEG b p) ℚ
    (wangCQ b p d_G) (wangA1 b p)
    (TopCat.ofHom (fibTrivΨ p (sphLoopBig b) d_G hT_G))
    (wangTrivMap_mem b p d_G hT_G)) k

/-! ## The transgression `θ = ρ ∘ Σ ∘ u` -/

/-- **The geometric Wang transgression** for the sphere model: the composite of the pullback `u`
along the clutching map `λ_G`, the collar transgression `Σ` and the pullback `ρ` along the inverse
clutching map at the shell point.  It has degree `-(b-1)`: `θ_n : H^{n+b}(F) → H^{n+1}(F)`. -/
noncomputable def wangTheta (b : ℕ) (hb : 2 ≤ b) (p : C(E, SphModel b))
    (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (n : ℕ) :
    Work.Cohomology.singularCohomology ℚ (n + b) (wangCohFsp b p) →ₗ[ℚ]
      Work.Cohomology.singularCohomology ℚ (n + 1) (wangCohFsp b p) :=
  ((rhoCoh b (by omega) p d_G hT_G hT_O (n + 1)).hom).comp
    ((collarSigma b (by omega) (Y := wangFY b p d_G)
        (wangSusT b hb (wangFY b p d_G)) (wangSusT_thom b hb (wangFY b p d_G)) n).comp
      ((collarLambdaGCoh b p d_G hT_G hT_O (n + b)).hom))

@[simp] theorem wangTheta_apply (b : ℕ) (hb : 2 ≤ b) (p : C(E, SphModel b))
    (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (n : ℕ)
    (a : Work.Cohomology.singularCohomology ℚ (n + b) (wangCohFsp b p)) :
    wangTheta b hb p d_G hT_G hT_O n a =
      (rhoCoh b (by omega) p d_G hT_G hT_O (n + 1)).hom
        (collarSigma b (by omega) (Y := wangFY b p d_G)
          (wangSusT b hb (wangFY b p d_G)) (wangSusT_thom b hb (wangFY b p d_G)) n
          ((collarLambdaGCoh b p d_G hT_G hT_O (n + b)).hom a)) := rfl

end

end Work.StemsB.Rat
