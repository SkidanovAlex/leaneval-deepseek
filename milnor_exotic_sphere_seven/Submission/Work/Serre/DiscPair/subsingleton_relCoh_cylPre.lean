import Mathlib
import Submission.Work.Serre.relCohPreimageDefs
import Submission.Work.Serre.C1Cyl
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.relCohMap_homotopic
import Submission.Work.Thom.relCohHomeomorph

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Vanishing of the relative cohomology of the part of a mapping cylinder over a subset

For a continuous map `q : C(X, Γ)` the **mapping cylinder** `cyl q` retracts onto its target copy
`cylInr q : Γ ↪ cyl q` (`Work.Serre.cylRetract`), and the *push-up* homotopy `cylMove q`
(`Submission/Work/Serre/C1Cyl.lean`) exhibits this retraction as a deformation retraction:
`cylMove q (·,0) = id` and `cylMove q (·,1) = cylInr q ∘ cylRetract q`.  Moreover `cylMove q`
does not move the retraction `cylRetract q` (proved here as `cylRetract_cylMove_pre`), so it preserves
every set of the form `cylPre q S = (cylRetract q) ⁻¹' S`.

Consequently, for `S ⊆ V`, the pair

`(cylPre q V, cylPre q S)`

is a pair of subspaces of the mapping cylinder on which `cylMove q` restricts to a homotopy of
pairs from the identity to the map

`cylInr q ∘ cylRetract q : (cylPre q V, cylPre q S) ⟶ (cylPre q V, cylPre q S)`,

which factors through the pair `(V, S)` along the retraction `cylPreRetract q V` and the target
inclusion `cylPreInr q V`.  Hence the identity of `H^k(cylPre q V, cylPre q S; R)` factors through
`H^k(V, S; R)`, and if the latter vanishes then so does the former:

* `Work.Serre.DiscPair.subsingleton_relCoh_of_factors_homotopic` — the abstract statement: if a
  self-map of the pair `(B,A)` which is homotopic (through maps of pairs) to the identity factors
  through a map of pairs `(B,A) → (B',A')`, then the vanishing of `H^k(B',A')` implies that of
  `H^k(B,A)`;
* `Work.Serre.DiscPair.subsingleton_relCoh_cylPre` — the requested vanishing statement.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.DiscPair

noncomputable section

variable {Γ : Type} [TopologicalSpace Γ] {X : Type} [TopologicalSpace X]

/-! ## The push-up homotopy preserves the retraction -/

/-- The push-up homotopy `cylMove` of the mapping cylinder does not move the retraction
`cylRetract`: for the cylinder part both sides are `q` of the source point, and on the target copy
`cylMove` is the identity. -/
-- NOTE (area-owner fix, 2026-09-27): the auxiliary lemma below was named `cylRetract_cylMove`,
-- which clashed with the same-named declaration of `Submission/Work/Serre/DiscPair/collarDefs.lean`
-- (and of `DiscPair/cylRetractPairIso.lean`).  Since `Submission/Work/Serre/All.lean` now reaches
-- both this module (via `DiscPair/thomRVDefs.lean`) and `collarDefs.lean` (via
-- `DiscPair/cylPairCofibre.lean`), the clash made `All.lean` fail to build with
-- `environment already contains 'Work.Serre.DiscPair.cylRetract_cylMove'`.  Nothing outside this
-- file used the name, so it has been renamed here (all four occurrences).
theorem cylRetract_cylMove_pre (q : C(X, Γ)) (y : Work.Serre.cyl q) (s : unitInterval) :
    Work.Serre.cylRetract q (Work.Serre.cylMove q (y, s)) = Work.Serre.cylRetract q y := by
  induction y using Quotient.inductionOn with
  | h z =>
      rcases z with ⟨p, t⟩ | z
      · show Work.Serre.cylRetractFun q (Work.Serre.cylMoveFun q s (Sum.inl (p, t)))
          = Work.Serre.cylRetractFun q (Sum.inl (p, t))
        rfl
      · show Work.Serre.cylRetractFun q (Work.Serre.cylMoveFun q s (Sum.inr z))
          = Work.Serre.cylRetractFun q (Sum.inr z)
        rfl

/-- `cylMove` preserves the part of the mapping cylinder lying over a subset. -/
theorem cylMove_mem_cylPre (q : C(X, Γ)) (V : Set Γ) (s : unitInterval)
    (y : ↥(Work.Serre.cylPre q V)) :
    Work.Serre.cylMove q ((y : Work.Serre.cyl q), s) ∈ Work.Serre.cylPre q V := by
  show Work.Serre.cylRetract q (Work.Serre.cylMove q ((y : Work.Serre.cyl q), s)) ∈ V
  rw [cylRetract_cylMove_pre]
  exact y.2

/-! ## The pair `(cylPre q V, cylPre q S)` and its retraction onto `(V,S)` -/

/-- The retraction of the part of the mapping cylinder over `V` onto `V`. -/
def cylPreRetract (q : C(X, Γ)) (V : Set Γ) : C(↥(Work.Serre.cylPre q V), ↥V) :=
  ⟨fun x => ⟨Work.Serre.cylRetract q x, x.2⟩,
   Continuous.subtype_mk ((Work.Serre.cylRetract q).continuous.comp continuous_subtype_val)
     (fun x => x.2)⟩

/-- The target copy of `V` inside the part of the mapping cylinder over `V`. -/
def cylPreInr (q : C(X, Γ)) (V : Set Γ) : C(↥V, ↥(Work.Serre.cylPre q V)) :=
  ⟨fun γ => ⟨Work.Serre.cylInr q γ, γ.2⟩,
   Continuous.subtype_mk ((Work.Serre.cylInr q).continuous.comp continuous_subtype_val)
     (fun γ => γ.2)⟩

/-- The reindexing map `I × ↥(cylPre q V) → cyl q × I` of the push-up homotopy. -/
def cylPreMoveMap (q : C(X, Γ)) (V : Set Γ) :
    C(unitInterval × ↥(Work.Serre.cylPre q V), Work.Serre.cyl q × unitInterval) :=
  ⟨fun p => ((p.2 : Work.Serre.cyl q), p.1), by fun_prop⟩

/-- **The push-up homotopy, restricted to the part of the mapping cylinder over `V`.**  It is a
homotopy from the identity of `↥(cylPre q V)` to the composite `cylInr q ∘ cylRetract q`, read as a
self-map of `↥(cylPre q V)`. -/
def cylPreHomotopy (q : C(X, Γ)) (V : Set Γ) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(Work.Serre.cylPre q V))
      ((cylPreInr q V).comp (cylPreRetract q V)) where
  toContinuousMap :=
    ⟨fun p => ⟨Work.Serre.cylMove q (cylPreMoveMap q V p), cylMove_mem_cylPre q V p.1 p.2⟩,
     Continuous.subtype_mk
       ((Work.Serre.cylMove q).continuous.comp (cylPreMoveMap q V).continuous)
       (fun p => cylMove_mem_cylPre q V p.1 p.2)⟩
  map_zero_left := fun y => Subtype.ext (Work.Serre.cylMove_zero q (y : Work.Serre.cyl q))
  map_one_left := fun y => Subtype.ext (Work.Serre.cylMove_one q (y : Work.Serre.cyl q))

/-- The value of the restricted push-up homotopy. -/
theorem cylPreHomotopy_apply (q : C(X, Γ)) (V : Set Γ) (t : unitInterval)
    (x : ↥(Work.Serre.cylPre q V)) :
    ((cylPreHomotopy q V (t, x) : ↥(Work.Serre.cylPre q V)) : Work.Serre.cyl q)
      = Work.Serre.cylMove q ((x : Work.Serre.cyl q), t) := rfl

/-! ## The abstract vanishing criterion -/

/-- **Vanishing of relative cohomology along a pair map that factors a homotopy.**

Let `θ : C(P,Q)` and `ι : C(Q,P)` be maps of pairs `(P,A) → (Q,A') → (P,A)`, and suppose that the
identity of `P` is homotopic, through maps of pairs `(P,A) → (P,A)`, to `ι ∘ θ`.  Then the identity
of `H^k(P,A;R)` factors as `θ^* ∘ ι^*` through `H^k(Q,A';R)`, so the vanishing of `H^k(Q,A';R)`
forces that of `H^k(P,A;R)`. -/
theorem subsingleton_relCoh_of_factors_homotopic {P Q : Type} [TopologicalSpace P]
    [TopologicalSpace Q] {A : Set P} {A' : Set Q} (θ : C(P, Q)) (ι : C(Q, P))
    (hθ : ∀ x ∈ A, θ x ∈ A') (hι : ∀ y ∈ A', ι y ∈ A)
    (hH : ∃ H : ContinuousMap.Homotopy (ContinuousMap.id P) (ι.comp θ),
      ∀ t x, x ∈ A → H (t, x) ∈ A)
    (R : Type) [CommRing R] (k : ℕ) (hvan : Subsingleton (Work.Thom.RelCoh R k Q A')) :
    Subsingleton (Work.Thom.RelCoh R k P A) := by
  have hid : ∀ x ∈ A, (ContinuousMap.id P) x ∈ A := fun x hx => hx
  have hgf : ∀ x ∈ A, (ι.comp θ) x ∈ A := fun x hx => hι (θ x) (hθ x hx)
  obtain ⟨H, hH⟩ := hH
  haveI := hvan
  -- the identity of `H^k(P,A)` equals `(ι ∘ θ)^*`
  have h1 : Work.Thom.relCohMap (ContinuousMap.id P) A A hid R k
      = Work.Thom.relCohMap (ι.comp θ) A A hgf R k :=
    Work.Thom.relCohMap_homotopic A A hid hgf H hH R k
  rw [Work.Thom.relCohMap_idA A R k] at h1
  -- the pullback along `θ` is zero, its source being a zero module
  have hz : Work.Thom.relCohMap θ A A' hθ R k = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [Subsingleton.elim x 0]
    simp
  -- and `(ι ∘ θ)^*` factors through that zero map
  have hfac : Work.Thom.relCohMap (ι.comp θ) A A hgf R k
      = CategoryTheory.CategoryStruct.comp (Work.Thom.relCohMap ι A' A hι R k)
          (Work.Thom.relCohMap θ A A' hθ R k) :=
    (Work.Thom.relCohMap_compA A A' A θ ι hθ hι hgf R k).symm
  have hzero : (𝟙 (Work.Thom.RelCoh R k P A)) = 0 := by
    rw [h1, hfac, hz, comp_zero]
  refine ⟨fun a b => ?_⟩
  have ha : a = 0 := by simpa using LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hzero) a
  have hb : b = 0 := by simpa using LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hzero) b
  rw [ha, hb]

end

end Work.Serre.DiscPair

namespace Work.Serre.DiscPair

noncomputable section

variable {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]

/-- **The relative cohomology of the part of the mapping cylinder over `V` vanishes, relative to
the part over `S`, as soon as that of the pair `(V,S)` does.** -/
theorem subsingleton_relCoh_cylPre {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (S V : Set B) (hSV : S ⊆ V) (N : ℕ)
    (hvanV : ∀ j : ℕ, j ≤ N + 2 →
      CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j ↥V {x : ↥V | (x : B) ∈ S}))
    (j : ℕ) (hj : j ≤ N + 2) :
    Subsingleton (Work.Thom.RelCoh ℚ j ↥(Work.Serre.cylPre q V)
      {x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S}) := by
  have hvanish : Subsingleton (Work.Thom.RelCoh ℚ j ↥V {x : ↥V | (x : B) ∈ S}) :=
    ModuleCat.isZero_iff_subsingleton.mp (hvanV j hj)
  refine subsingleton_relCoh_of_factors_homotopic (Q := ↥V)
    (A := {x : ↥(Work.Serre.cylPre q V) | (x : Work.Serre.cyl q) ∈ Work.Serre.cylPre q S})
    (A' := {x : ↥V | (x : B) ∈ S})
    (cylPreRetract q V) (cylPreInr q V) ?_ ?_ ⟨cylPreHomotopy q V, ?_⟩ ℚ j hvanish
  · -- the retraction carries the part over `S` into `S`
    intro x hx
    exact hx
  · -- the target inclusion carries `S` into the part over `S`
    intro y hy
    exact hy
  · -- the push-up homotopy preserves the part of the cylinder over `S`
    intro t x hx
    show Work.Serre.cylRetract q
      ((cylPreHomotopy q V (t, x) : ↥(Work.Serre.cylPre q V)) : Work.Serre.cyl q) ∈ S
    rw [cylPreHomotopy_apply, cylRetract_cylMove_pre]
    exact hx

end

end Work.Serre.DiscPair
