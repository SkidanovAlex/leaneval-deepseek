import Mathlib
import Submission.Work.Serre.C1Cyl

/-!
# The map of mapping cylinders induced by a **square**

`Submission/Work/Serre/thomCylAt_of_homeo.lean` constructs `Work.Serre.cylMap f g φ` for a
*compatible pair* of maps with the **same source** (`φ ∘ f = g`, `f : C(P,X)`, `g : C(P,X')`).
This file removes that restriction: a commutative *square*

```
P  --ψ-->  P'
|          |
f          g
v          v
X  --φ-->  X'          (φ ∘ f = g ∘ ψ)
```

induces a continuous map `cylMapGen f g ψ φ h : C(cyl f, cyl g)` (the identity on the `I`-coordinate
of the cylinder and `ψ`, `φ` on the two copies), together with its two computation rules, the
compatibility with the bottom copies (`cylIncl`) and with the retractions (`cylRetract`).  The
general form is what is needed to compare the mapping cylinder of a fibration `q : C(X,B)` with the
mapping cylinder of its pullback `pullbackSnd q γ` along a path `γ : I → B`:
there `P = X`, `P' = Pullback q γ`, `f = q`, `g = pullbackSnd q γ`, `ψ = pullbackFst`, `φ = γ`.
-/

open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

variable {P P' X X' : Type} [TopologicalSpace P] [TopologicalSpace P']
  [TopologicalSpace X] [TopologicalSpace X']

/-- The map on `(P × I) ⊕ X` underlying the map of mapping cylinders induced by a square
`(ψ, φ)`. -/
def cylRelMapGen (ψ : C(P, P')) (φ : C(X, X')) : (P × unitInterval) ⊕ X → (P' × unitInterval) ⊕ X' :=
  Sum.elim (fun a => (Sum.inl (ψ a.1, a.2) : (P' × unitInterval) ⊕ X')) (fun x => Sum.inr (φ x))

@[simp] theorem cylRelMapGen_inl (ψ : C(P, P')) (φ : C(X, X')) (a : P × unitInterval) :
    cylRelMapGen ψ φ (Sum.inl a : (P × unitInterval) ⊕ X) = Sum.inl (ψ a.1, a.2) := rfl

@[simp] theorem cylRelMapGen_inr (ψ : C(P, P')) (φ : C(X, X')) (x : X) :
    cylRelMapGen ψ φ (Sum.inr x : (P × unitInterval) ⊕ X) = Sum.inr (φ x) := rfl

theorem continuous_cylRelMapGen (ψ : C(P, P')) (φ : C(X, X')) :
    Continuous (cylRelMapGen ψ φ) := by
  show Continuous (Sum.elim (fun a : P × unitInterval => (Sum.inl (ψ a.1, a.2) :
    (P' × unitInterval) ⊕ X')) (fun x => Sum.inr (φ x)))
  refine Continuous.sumElim ?_ (continuous_inr.comp φ.continuous)
  exact continuous_inl.comp (((ψ.continuous.comp continuous_fst).prodMk continuous_snd))

/-- A relation step is carried to a relation step. -/
theorem cylRel_mapGen (f : C(P, X)) (g : C(P', X')) (ψ : C(P, P')) (φ : C(X, X'))
    (h : ∀ p, φ (f p) = g (ψ p)) {a b : (P × unitInterval) ⊕ X} (hab : Work.Serre.cylRel f a b) :
    Work.Serre.cylRel g (cylRelMapGen ψ φ a) (cylRelMapGen ψ φ b) := by
  obtain ⟨p, rfl, rfl⟩ := hab
  exact ⟨ψ p, rfl, by simp only [cylRelMapGen_inr, h p]⟩

/-- The gluing relation of `cyl f` is carried into that of `cyl g`. -/
theorem cylRelMapGen_eqvGen (f : C(P, X)) (g : C(P', X')) (ψ : C(P, P')) (φ : C(X, X'))
    (h : ∀ p, φ (f p) = g (ψ p)) (a b : (P × unitInterval) ⊕ X)
    (hab : Relation.EqvGen (Work.Serre.cylRel f) a b) :
    Relation.EqvGen (Work.Serre.cylRel g) (cylRelMapGen ψ φ a) (cylRelMapGen ψ φ b) := by
  induction hab with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (cylRel_mapGen f g ψ φ h hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- The function underlying the map of mapping cylinders induced by a square. -/
def cylMapGenFun (f : C(P, X)) (g : C(P', X')) (ψ : C(P, P')) (φ : C(X, X'))
    (h : ∀ p, φ (f p) = g (ψ p)) : Work.Serre.cyl f → Work.Serre.cyl g :=
  Quotient.lift (fun a => Quotient.mk'' (cylRelMapGen ψ φ a))
    (fun a b hab => Quotient.sound (cylRelMapGen_eqvGen f g ψ φ h a b hab))

theorem continuous_cylMapGenFun (f : C(P, X)) (g : C(P', X')) (ψ : C(P, P')) (φ : C(X, X'))
    (h : ∀ p, φ (f p) = g (ψ p)) : Continuous (cylMapGenFun f g ψ φ h) := by
  show Continuous (Quotient.lift (fun a => Quotient.mk'' (cylRelMapGen ψ φ a)) _)
  exact Continuous.quotient_lift (continuous_quotient_mk'.comp (continuous_cylRelMapGen ψ φ)) _

/-- **The map of mapping cylinders induced by a commutative square.** -/
def cylMapGen (f : C(P, X)) (g : C(P', X')) (ψ : C(P, P')) (φ : C(X, X'))
    (h : ∀ p, φ (f p) = g (ψ p)) : C(Work.Serre.cyl f, Work.Serre.cyl g) :=
  ⟨cylMapGenFun f g ψ φ h, continuous_cylMapGenFun f g ψ φ h⟩

theorem cylMapGen_apply_inl (f : C(P, X)) (g : C(P', X')) (ψ : C(P, P')) (φ : C(X, X'))
    (h : ∀ p, φ (f p) = g (ψ p)) (a : P × unitInterval) :
    cylMapGen f g ψ φ h (Quotient.mk'' (Sum.inl a)) =
      Quotient.mk'' (Sum.inl (ψ a.1, a.2) : (P' × unitInterval) ⊕ X') := by
  change cylMapGenFun f g ψ φ h (Quotient.mk'' (Sum.inl a)) = _
  simp only [cylMapGenFun, Quotient.lift_mk, cylRelMapGen_inl]

theorem cylMapGen_apply_inr (f : C(P, X)) (g : C(P', X')) (ψ : C(P, P')) (φ : C(X, X'))
    (h : ∀ p, φ (f p) = g (ψ p)) (x : X) :
    cylMapGen f g ψ φ h (Quotient.mk'' (Sum.inr x)) =
      Quotient.mk'' (Sum.inr (φ x) : (P' × unitInterval) ⊕ X') := by
  change cylMapGenFun f g ψ φ h (Quotient.mk'' (Sum.inr x)) = _
  simp only [cylMapGenFun, Quotient.lift_mk, cylRelMapGen_inr]

/-- The induced map of cylinders is compatible with the bottom copies. -/
theorem cylIncl_comp_cylMapGen (f : C(P, X)) (g : C(P', X')) (ψ : C(P, P')) (φ : C(X, X'))
    (h : ∀ p, φ (f p) = g (ψ p)) :
    (cylMapGen f g ψ φ h).comp (Work.Serre.cylIncl f) = (Work.Serre.cylIncl g).comp ψ := by
  ext p
  show cylMapGen f g ψ φ h (Quotient.mk'' (Sum.inl (p, 0) : (P × unitInterval) ⊕ X)) =
    Quotient.mk'' (Sum.inl (ψ p, 0) : (P' × unitInterval) ⊕ X')
  rw [cylMapGen_apply_inl]

/-- The induced map of cylinders is compatible with the retractions. -/
theorem cylRetract_comp_cylMapGen (f : C(P, X)) (g : C(P', X')) (ψ : C(P, P')) (φ : C(X, X'))
    (h : ∀ p, φ (f p) = g (ψ p)) :
    (Work.Serre.cylRetract g).comp (cylMapGen f g ψ φ h) = φ.comp (Work.Serre.cylRetract f) := by
  ext z
  refine Quotient.inductionOn
    (motive := fun y => Work.Serre.cylRetract g (cylMapGen f g ψ φ h y) =
      φ (Work.Serre.cylRetract f y)) z ?_
  intro a
  cases a with
  | inl pt =>
    rw [cylMapGen_apply_inl]
    show g (ψ pt.1) = φ (f pt.1)
    exact (h pt.1).symm
  | inr x =>
    rw [cylMapGen_apply_inr]
    rfl

/-- The induced map of cylinders carries the fibre of the retraction over `t` into the fibre over
`φ t`. -/
theorem cylMapGen_mapsTo_fibre (f : C(P, X)) (g : C(P', X')) (ψ : C(P, P')) (φ : C(X, X'))
    (h : ∀ p, φ (f p) = g (ψ p)) {t : X} {z : Work.Serre.cyl f}
    (hz : Work.Serre.cylRetract f z = t) :
    Work.Serre.cylRetract g (cylMapGen f g ψ φ h z) = φ t := by
  have := DFunLike.congr_fun (cylRetract_comp_cylMapGen f g ψ φ h) z
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply] at this
  rw [this, hz]

/-- The induced map on the bottom copies, as a map `C(P, range (cylIncl g))`. -/
theorem cylMapGen_mapsTo_range (f : C(P, X)) (g : C(P', X')) (ψ : C(P, P')) (φ : C(X, X'))
    (h : ∀ p, φ (f p) = g (ψ p)) {z : Work.Serre.cyl f}
    (hz : z ∈ Set.range (Work.Serre.cylIncl f)) :
    cylMapGen f g ψ φ h z ∈ Set.range (Work.Serre.cylIncl g) := by
  obtain ⟨p, rfl⟩ := hz
  exact ⟨ψ p, (DFunLike.congr_fun (cylIncl_comp_cylMapGen f g ψ φ h) p).symm⟩

end

end Work.StemsB
