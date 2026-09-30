import Mathlib
import Submission.Work.Pi6.MSS.serreCohFilt
import Submission.Work.Pi6.MSS.CohFilt
import Submission.Work.Cohomology.cupBilinear
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The Serre cochain filtration as a `CohFilt`

`Work.Pi6.MSS.serreCF 𝕜 p` packages the six clauses proved in
`Submission/Work/Pi6/MSS/serreCohFilt.lean` (monotone, `F^0 = ⊤`, `F^{n+1}C^n = ⊥`, `δ`-stability,
cup compatibility, Leibniz) as the structure `Work.Pi6.MSS.CohFilt 𝕜`:
the filtered cochain complex is the singular cochain complex `C^*(Sing E;𝕜)` with the Serre
cochain filtration `coFilt 𝕜 (sSingP p)` and the Alexander–Whitney cup product.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

namespace Work.Pi6.MSS

noncomputable section

/-- The Alexander–Whitney cup product of cochains of `Sing E` as a curried bilinear map. -/
def serreCup (𝕜 : Type) [CommRing 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (n m : ℕ) :
    Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n →ₗ[𝕜]
      Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) m →ₗ[𝕜]
      Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) (n + m) :=
  LinearMap.mk₂ 𝕜 (fun a b => Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) a b)
    (fun a a' b => (Work.Cohomology.cupBilinear 𝕜 (Work.SSS.sSing E) n m).1 a a' b)
    (fun a a' b => (Work.Cohomology.cupBilinear 𝕜 (Work.SSS.sSing E) n m).2.1 a a' b)
    (fun a b b' => (Work.Cohomology.cupBilinear 𝕜 (Work.SSS.sSing E) n m).2.2.1 a b b')
    (fun a b b' => (Work.Cohomology.cupBilinear 𝕜 (Work.SSS.sSing E) n m).2.2.2 a b b')

/-- The cup product as a curried bilinear map is the Alexander–Whitney cup product. -/
@[simp] theorem serreCup_apply (𝕜 : Type) [CommRing 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (n m : ℕ)
    (a : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n)
    (b : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) m) :
    serreCup 𝕜 p n m a b = Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) a b := by
  simp only [serreCup, LinearMap.mk₂_apply]

/-- **The Serre cochain filtration of `p : E → B` as a `CohFilt`**: the singular cochains of `E`
with coefficients in `𝕜`, filtered by vanishing on the chains over the skeleta of `B`, with the
Alexander–Whitney cup product. -/
def serreCF (𝕜 : Type) [CommRing 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) : CohFilt 𝕜 where
  C := Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing E)
  F := fun s n => coFilt 𝕜 (Work.SSS.sSingP p) s n
  F_mono := fun s n => (serreCohFilt 𝕜 E B p).1 s n
  F_zero := fun n => (serreCohFilt 𝕜 E B p).2.1 n
  F_top := fun n => (serreCohFilt 𝕜 E B p).2.2.1 n
  F_leib := fun s n x hx => by
    have h := (serreCohFilt 𝕜 E B p).2.2.2.1 s n x hx
    simpa only [Work.Cohomology.SSetCochainComplex, CochainComplex.of_d,
      ModuleCat.hom_ofHom, Work.Cohomology.cochainDiffLM_apply] using h
  mul := fun n m => serreCup 𝕜 p n m
  mul_filt := fun s s' n m x y hx hy => by
    simpa only [Work.Cohomology.SSetCochainComplex, serreCup_apply]
      using (serreCohFilt 𝕜 E B p).2.2.2.2.1 s s' n m x y hx hy
  mul_leib := fun n m e₁ e₂ x y => by
    simp only [Work.Cohomology.SSetCochainComplex, serreCup_apply]
    have h := (serreCohFilt 𝕜 E B p).2.2.2.2.2 n m x y
    simpa only [Work.Cohomology.SSetCochainComplex, CochainComplex.of_d, ModuleCat.hom_ofHom,
      Work.Cohomology.cochainDiffLM_apply] using h

@[simp] theorem serreCF_F (𝕜 : Type) [CommRing 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (s n : ℕ) :
    (serreCF 𝕜 E B p).F s n = coFilt 𝕜 (Work.SSS.sSingP p) s n := rfl

@[simp] theorem serreCF_C (𝕜 : Type) [CommRing 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) :
    (serreCF 𝕜 E B p).C = Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing E) := rfl

end

end Work.Pi6.MSS
