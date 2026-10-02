import Mathlib
import Submission.Work.Serre.DiscPair.oldPartDefs
import Submission.Work.Serre.DiscPair.subPairMapQuasiIso
import Submission.Work.Serre.DiscPair.collarDefs
import Submission.Work.Serre.DiscPair.collarHomeoA2
import Submission.Work.Serre.DiscPair.collarSetHomotopyEquiv
import Submission.Work.Serre.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The inclusion `oldA ↪ oldU₀` of the bottom of the collar is a rational homology isomorphism

The target `oldA = A₂ ∩ {λ = 0} = range (cylIncl q)` (inside `↥(cylPairA₂ q)`, where `λ = cylLam q`
is the collar coordinate) is the bottom copy of `X` in the mapping cylinder, and `oldU₀ = A₂ ∩
{λ < 1/2}` is the collar piece.  The inclusion `oldIncl : oldA ↪ oldU₀` is a rational homology
isomorphism: indeed `oldA` is the "bottom" of the collar and `oldU₀` deformation retracts onto it
(the collar flow `λ ↦ 0`).

The proof here avoids an explicit retraction of the quotient: it uses the two known facts about the
collar,

* `Aux.cylCollar : ↥(cylU₀A₂ q) ≃ₜ ↥(cylSet₁ q)` is the collar homeomorphism of
  `collarHomeoA2` (with `cylCollar_mk` giving its value on `cylMk q (inl (x,t))`, `t < 1/2`), and
* `Aux.cylPrHe : ↥(cylU₀A₂ q) ≃ X` is the homotopy equivalence given by the collar projection
  `cylPr = cylSetFst ∘ cylCollar`,

and the elementary observation that inside `↥(cylU₀A₂ q)` the bottom copy is exactly the complement
of `cylU₀U₁A₂ = {λ > 0}` (`cylPairBot_eq_cylU₀A₂InterU₁`), so that under `cylCollar` it is
`X × {0} ⊆ cylSet₁`.  Consequently the composite `cylPr ∘ oldIncl : oldA → X` is a homeomorphism
(with inverse the bottom section `oldPartBot`), hence a rational homology isomorphism; composing
with the rational homology isomorphism `cylPr` and cancelling gives the statement.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.DiscPair

noncomputable section

variable {D : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type}
  {f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)} {X : Type} [TopologicalSpace X]

/-! ## The bottom section of the collar -/

/-- **The bottom copy of `X` in `A₂`**: the section `x ↦ cylIncl q x`, viewed as a point of
`oldA = A₂ ∩ range (cylIncl q)`. -/
def oldPartBot (q : C(X, CylZ D Γ ι f)) : C(X, ↥(oldA q)) where
  toFun x := ⟨⟨cylIncl q x, Or.inr ⟨x, rfl⟩⟩, ⟨x, rfl⟩⟩
  continuous_toFun := Continuous.subtype_mk
    (f := fun x : X => (⟨cylIncl q x, Or.inr ⟨x, rfl⟩⟩ : ↥(cylPairA₂ q)))
    (Continuous.subtype_mk (f := fun x : X => cylIncl q x) ((cylIncl q).continuous)
      (fun x => Or.inr ⟨x, rfl⟩))
    (fun x => ⟨x, rfl⟩)

@[simp] theorem oldPartBot_coe (q : C(X, CylZ D Γ ι f)) (x : X) :
    ((oldPartBot q x : ↥(oldA q)).1 : cyl q) = cylIncl q x := rfl

/-! ## The value of the collar homeomorphism on the bottom copy -/

/-- **The collar homeomorphism on a point whose class is `cylMk q (inl (x,t))`**, with `t < 1/2`.
This is `Aux.cylCollar_mk` with the membership proofs replaced by arbitrary ones (they are
irrelevant). -/
theorem oldPartCollar_apply_mk (q : C(X, CylZ D Γ ι f)) {y : ↥(cylU₀A₂ q)} (x : X)
    (t : unitInterval) (ht : (t : ℝ) < 1/2)
    (hA₂ : Work.Serre.cylMk q (Sum.inl (x, t)) ∈ cylPairA₂ q)
    (hy : y.1 = ⟨Work.Serre.cylMk q (Sum.inl (x, t)), hA₂⟩) :
    Aux.cylCollar q y = ⟨(x, t), ⟨ht, (mem_cylPairA₂_cylMk_inl_iff q x t ht).mp hA₂⟩⟩ := by
  have hyy : y = ⟨⟨Work.Serre.cylMk q (Sum.inl (x, t)), hA₂⟩,
      (mem_cylU₀_cylMk_inl_iff q x t).mpr ht⟩ := Subtype.ext hy
  rw [hyy]
  exact Aux.cylCollar_mk q x t ht hA₂

/-! ## The two round trips of `cylPr ∘ oldIncl` and the bottom section -/

theorem oldPartPr_oldPartBot (q : C(X, CylZ D Γ ι f)) (x : X) :
    Aux.cylPr q (oldIncl q (oldPartBot q x)) = x := by
  have hA₂ : Work.Serre.cylMk q (Sum.inl (x, (0 : unitInterval))) ∈ cylPairA₂ q := Or.inr ⟨x, rfl⟩
  have hmem : (((0 : unitInterval)) : ℝ) < 1/2 := by norm_num
  have hy : (oldIncl q (oldPartBot q x)).1
      = ⟨Work.Serre.cylMk q (Sum.inl (x, (0 : unitInterval))), hA₂⟩ := rfl
  show Aux.cylSetFst q (Aux.cylCollar q (oldIncl q (oldPartBot q x))) = x
  rw [oldPartCollar_apply_mk q x 0 hmem hA₂ hy]
  rfl

theorem oldPartBot_oldPartPr (q : C(X, CylZ D Γ ι f)) (y : ↥(oldA q)) :
    oldPartBot q (Aux.cylPr q (oldIncl q y)) = y := by
  obtain ⟨x, hx⟩ := y.2
  have hA₂ : Work.Serre.cylMk q (Sum.inl (x, (0 : unitInterval))) ∈ cylPairA₂ q := Or.inr ⟨x, rfl⟩
  have hmem : (((0 : unitInterval)) : ℝ) < 1/2 := by norm_num
  have hy : (oldIncl q y).1
      = ⟨Work.Serre.cylMk q (Sum.inl (x, (0 : unitInterval))), hA₂⟩ := by
    refine Subtype.ext ?_
    rw [oldIncl_coe]
    rw [← hx]
    rfl
  show oldPartBot q (Aux.cylSetFst q (Aux.cylCollar q (oldIncl q y))) = y
  rw [oldPartCollar_apply_mk q x 0 hmem hA₂ hy]
  refine Subtype.ext (Subtype.ext ?_)
  exact hx

/-! ## The rational homology isomorphisms -/

/-- The collar projection `cylPr : ↥(cylU₀A₂ q) → X` is a rational homology isomorphism (it is a
homotopy equivalence). -/
theorem oldPart_ratHomologyIso_cylPr (q : C(X, CylZ D Γ ι f)) :
    Work.Serre.IsRatHomologyIso (Aux.cylPr q) := by
  have h := Work.Serre.IsRatHomologyIso.of_homotopyEquiv (Aux.cylPrHe q)
  rwa [Aux.cylPrHe_toFun q] at h

/-- **`cylPr ∘ oldIncl : oldA → X` is a rational homology isomorphism**: it is a homeomorphism,
with inverse the bottom section `oldPartBot`. -/
theorem oldPart_ratHomologyIso_comp (q : C(X, CylZ D Γ ι f)) :
    Work.Serre.IsRatHomologyIso ((Aux.cylPr q).comp (oldIncl q)) := by
  have hleft : (oldPartBot q).comp ((Aux.cylPr q).comp (oldIncl q))
      = ContinuousMap.id ↥(oldA q) :=
    ContinuousMap.ext (fun y => oldPartBot_oldPartPr q y)
  have hright : ((Aux.cylPr q).comp (oldIncl q)).comp (oldPartBot q) = ContinuousMap.id X :=
    ContinuousMap.ext (fun x => oldPartPr_oldPartBot q x)
  have hleft' : ((oldPartBot q).comp ((Aux.cylPr q).comp (oldIncl q))).Homotopic
      (ContinuousMap.id ↥(oldA q)) := by
    rw [hleft]
  have hright' : (((Aux.cylPr q).comp (oldIncl q)).comp (oldPartBot q)).Homotopic
      (ContinuousMap.id X) := by
    rw [hright]
  exact Work.Serre.IsRatHomologyIso.of_homotopyEquiv
    (ContinuousMap.HomotopyEquiv.mk _ _ hleft' hright')

/-- The inclusion `oldA ↪ oldU₀` of the bottom of the collar into the collar is a rational
homology isomorphism.  (`oldA = {x : ↥(cylPairA₂ q) | (x : cyl q) ∈ cylPairBot q}` is the relative
part of the target pair, `oldU₀ = cylU₀A₂ q = {x | λ x < 1/2}` with `λ = cylLam q` the collar
coordinate, and `oldIncl` is the inclusion; all three are in
`Submission.Work.Serre.DiscPair.oldPartDefs`.) -/
theorem oldPartCollarIncl (D : ℕ) {Γ : Type} [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.Serre.DiscPair.CylZ D Γ ι f)) :
    Work.Serre.IsRatHomologyIso
      (Work.Serre.DiscPair.oldIncl (D := D) (Γ := Γ) (ι := ι) (f := f) (X := X) q) := by
  have hcomp := oldPart_ratHomologyIso_comp (X := X) q
  have hp := oldPart_ratHomologyIso_cylPr (X := X) q
  intro n
  have hcomp' : IsIso (Work.Serre.ratHomologyMap (oldIncl q) n
      ≫ Work.Serre.ratHomologyMap (Aux.cylPr q) n) := by
    rw [← Work.Serre.ratHomologyMap_comp (oldIncl q) (Aux.cylPr q) n]
    exact hcomp n
  haveI := hcomp'
  haveI := hp n
  exact IsIso.of_isIso_comp_right (Work.Serre.ratHomologyMap (oldIncl q) n)
    (Work.Serre.ratHomologyMap (Aux.cylPr q) n)

end

end Work.Serre.DiscPair
