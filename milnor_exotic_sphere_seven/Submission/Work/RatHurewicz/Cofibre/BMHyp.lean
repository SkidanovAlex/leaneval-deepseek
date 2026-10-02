import Mathlib
import Submission.Work.RatHurewicz.Cofibre.UShrink
import Submission.Work.RatHurewicz.Cofibre.PiTransfer
import Submission.Work.RatHurewicz.relPiVanishingOfPiInjSurj
import Submission.Work.RatHurewicz.Excision

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Blakers–Massey hypotheses for the cover `(cofibreU ι, cofibreV ι)`

`Work.RatHurewicz.homotopyExcision` is stated for the subspace inclusions `interInclLeft U V` and
`interInclRight U V`.  This file provides (i) the general transport of `RelHomotopyGroup` along a
homeomorphism of the *source* of the map, and (ii) the two hypotheses of the excision theorem in the
form needed for the cover of `cofibre ι`, obtained from `relPiVanishingOfPiInjSurj` and the
`π`-triviality of `↥(cofibreU ι)` (from `cofibreUHomotopyEquiv`) and of `↥(cofibreU ι ∩ cofibreV ι)`
(from the collar `collarHomotopyEquiv`).
-/

open scoped Topology unitInterval
open Work.StemsB

namespace Work.RatHurewicz

noncomputable section

/-- The canonical homeomorphism `↥(B ∩ C) ≃ₜ ↥{z : ↥B | (z : X) ∈ C}`. -/
def interHomeo {X : Type} [TopologicalSpace X] (B C : Set X) :
    ↥(B ∩ C) ≃ₜ ↥{z : ↥B | (z : X) ∈ C} where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun z := ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
  left_inv x := by ext; rfl
  right_inv z := by ext; rfl
  continuous_toFun :=
    Continuous.subtype_mk
      (Continuous.subtype_mk (by fun_prop : Continuous fun x : ↥(B ∩ C) => (x.1 : X))
        (fun x => x.2.1))
      (fun x => x.2.2)
  continuous_invFun :=
    Continuous.subtype_mk
      (by fun_prop : Continuous fun z : ↥{z : ↥B | (z : X) ∈ C} => (z.1.1 : X))
      (fun z => ⟨z.1.2, z.2⟩)

theorem interHomeo_apply {X : Type} [TopologicalSpace X] (B C : Set X) (x : ↥(B ∩ C)) :
    (interHomeo B C x : ↥B) = ⟨x.1, x.2.1⟩ := rfl

/-- The canonical homeomorphism `↥(B ∩ C) ≃ₜ ↥{z : ↥C | (z : X) ∈ B}`, in the *second* variable
(the variant used for `interInclRight`). -/
def interHomeo' {X : Type} [TopologicalSpace X] (B C : Set X) :
    ↥(B ∩ C) ≃ₜ ↥{z : ↥C | (z : X) ∈ B} where
  toFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  invFun z := ⟨z.1.1, ⟨z.2, z.1.2⟩⟩
  left_inv x := by ext; rfl
  right_inv z := by ext; rfl
  continuous_toFun :=
    Continuous.subtype_mk
      (Continuous.subtype_mk (by fun_prop : Continuous fun x : ↥(B ∩ C) => (x.1 : X))
        (fun x => x.2.2))
      (fun x => x.2.1)
  continuous_invFun :=
    Continuous.subtype_mk
      (by fun_prop : Continuous fun z : ↥{z : ↥C | (z : X) ∈ B} => (z.1.1 : X))
      (fun z => ⟨z.2, z.1.2⟩)

theorem interHomeo'_apply {X : Type} [TopologicalSpace X] (B C : Set X) (x : ↥(B ∩ C)) :
    (interHomeo' B C x : ↥C) = ⟨x.1, x.2.2⟩ := rfl

/-- The forward map of `homotopyFibreHomeo`, as a plain function (so that its applications
`β`-reduce). -/
def homotopyFibreHomeoFun {A A' X : Type} [TopologicalSpace A] [TopologicalSpace A']
    [TopologicalSpace X] (g : C(A', X)) (e : A ≃ₜ A') (a : A) :
    homotopyFibre (g.comp ⟨e.toFun, e.continuous⟩) a → homotopyFibre g (e a) := fun p =>
  ⟨(e p.1.1, p.1.2), by
    show (Work.StemsB.evalOne X (g (e a))) p.1.2 = g (e p.1.1)
    exact p.2⟩

/-- The inverse map of `homotopyFibreHomeo`, as a plain function. -/
def homotopyFibreHomeoInvFun {A A' X : Type} [TopologicalSpace A] [TopologicalSpace A']
    [TopologicalSpace X] (g : C(A', X)) (e : A ≃ₜ A') (a : A) :
    homotopyFibre g (e a) → homotopyFibre (g.comp ⟨e.toFun, e.continuous⟩) a := fun q =>
  ⟨(e.symm q.1.1, (q.1.2 : PathSpace X (g (e a)))), by
    show (Work.StemsB.evalOne X (g (e a))) (q.1.2 : PathSpace X (g (e a))) = g (e (e.symm q.1.1))
    rw [e.apply_symm_apply]
    exact q.2⟩

theorem homotopyFibreHomeoInvFun_comp {A A' X : Type} [TopologicalSpace A] [TopologicalSpace A']
    [TopologicalSpace X] (g : C(A', X)) (e : A ≃ₜ A') (a : A)
    (p : homotopyFibre (g.comp ⟨e.toFun, e.continuous⟩) a) :
    homotopyFibreHomeoInvFun g e a (homotopyFibreHomeoFun g e a p) = p := by
  apply Subtype.ext
  exact Prod.ext (e.symm_apply_apply p.1.1) rfl

theorem continuous_homotopyFibreHomeoInvFun {A A' X : Type} [TopologicalSpace A]
    [TopologicalSpace A'] [TopologicalSpace X] (g : C(A', X)) (e : A ≃ₜ A') (a : A) :
    Continuous (homotopyFibreHomeoInvFun g e a) :=
  Continuous.subtype_mk
    (Continuous.prodMk (e.symm.continuous.comp (continuous_fst.comp continuous_subtype_val))
      (continuous_snd.comp continuous_subtype_val))
    (fun q => by
      show (Work.StemsB.evalOne X (g (e a))) (q.1.2 : PathSpace X (g (e a))) = g (e (e.symm q.1.1))
      rw [e.apply_symm_apply]
      exact q.2)

/-- **The homotopy fibres of `g ∘ e` and of `g` are homeomorphic** for a homeomorphism `e` of the
source: the first projection is composed with `e`, and the path is left alone. -/
def homotopyFibreHomeo {A A' X : Type} [TopologicalSpace A] [TopologicalSpace A']
    [TopologicalSpace X] (g : C(A', X)) (e : A ≃ₜ A') (a : A) :
    homotopyFibre (g.comp ⟨e.toFun, e.continuous⟩) a ≃ₜ homotopyFibre g (e a) where
  toFun := homotopyFibreHomeoFun g e a
  invFun := homotopyFibreHomeoInvFun g e a
  left_inv := homotopyFibreHomeoInvFun_comp g e a
  right_inv q := by
    apply Subtype.ext
    exact Prod.ext (e.apply_symm_apply q.1.1) rfl
  continuous_toFun :=
    Continuous.subtype_mk
      (Continuous.prodMk (e.continuous.comp (continuous_fst.comp continuous_subtype_val))
        (continuous_snd.comp continuous_subtype_val))
      (fun p => by
        show (Work.StemsB.evalOne X (g (e a))) p.1.2 = g (e p.1.1)
        exact p.2)
  continuous_invFun := continuous_homotopyFibreHomeoInvFun g e a

/-- **Triviality of a relative homotopy group transports along a homeomorphism of the source.** -/
theorem subsingleton_relPi_of_homeo {A A' X : Type} [TopologicalSpace A] [TopologicalSpace A']
    [TopologicalSpace X] (g : C(A', X)) (e : A ≃ₜ A') (a : A) (n : ℕ)
    (h : Subsingleton (RelHomotopyGroup g (e a) n)) :
    Subsingleton (RelHomotopyGroup (g.comp ⟨e.toFun, e.continuous⟩) a n) := by
  let eC : C(A, A') := ⟨e.toFun, e.continuous⟩
  let fC : C(homotopyFibre (g.comp eC) a, homotopyFibre g (e a)) :=
    ⟨homotopyFibreHomeoFun g e a, by
      have h1 : homotopyFibreHomeoFun g e a = ⇑(homotopyFibreHomeo g e a) :=
        funext (fun p => Subtype.ext rfl)
      rw [h1]
      exact (homotopyFibreHomeo g e a).continuous⟩
  let gC : C(homotopyFibre g (e a), homotopyFibre (g.comp eC) a) :=
    ⟨homotopyFibreHomeoInvFun g e a, continuous_homotopyFibreHomeoInvFun g e a⟩
  have hx : fC (homotopyFibreBasepoint (g.comp eC) a) = homotopyFibreBasepoint g (e a) := by
    apply Subtype.ext
    exact Prod.ext rfl (Subtype.ext rfl)
  have hri : gC.comp fC = ContinuousMap.id (homotopyFibre (g.comp eC) a) := by
    ext p
    exact homotopyFibreHomeoInvFun_comp g e a p
  refine Work.Stems.subsingleton_of_retract (N := Fin n) fC gC hri
    (x := homotopyFibreBasepoint (g.comp eC) a) ?_
  rw [hx]
  exact h

/-- **Triviality of a homotopy group transfers along a homeomorphism.** -/
theorem subsingleton_homotopyGroup_of_homeo {N : Type*} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X)
    (h : Subsingleton (HomotopyGroup N X x)) :
    Subsingleton (HomotopyGroup N Y (e x)) := by
  have h' : Subsingleton (HomotopyGroup N X (e.symm (e x))) := by
    rwa [e.symm_apply_apply x]
  exact Work.Stems.subsingleton_of_retract (N := N) ⟨e.symm, e.symm.continuous⟩
    ⟨e, e.continuous⟩ (by ext y; exact e.apply_symm_apply y) (x := e x) h'

/-- **Blakers–Massey, hypothesis (B)**: the relative homotopy groups of
`(cofibreV ι, cofibreU ι ∩ cofibreV ι)` vanish.

Same construction as hypothesis (A) with the two sets interchanged, using `interHomeo'` (whose
target is the subtype of `↥(cofibreV ι)` cut out by `cofibreU ι`). -/
theorem subsingleton_relPi_interInclRight {E F : Type} [TopologicalSpace E] [TopologicalSpace F]
    (ι : C(F, E)) (J : ℕ) (x₀ : ↥(cofibreU ι ∩ cofibreV ι))
    (hinter : Subsingleton (HomotopyGroup (Fin J) ↥(cofibreU ι ∩ cofibreV ι) x₀))
    (hV : Subsingleton (HomotopyGroup (Fin (J + 1)) ↥(cofibreV ι) ⟨x₀.1, x₀.2.2⟩)) :
    Subsingleton (RelHomotopyGroup (interInclRight (cofibreU ι) (cofibreV ι)) x₀ J) := by
  have hA : Subsingleton (HomotopyGroup (Fin J)
      ↥{z : ↥(cofibreV ι) | (z : cofibre ι) ∈ cofibreU ι}
      ((interHomeo' (cofibreU ι) (cofibreV ι)) x₀)) :=
    subsingleton_homotopyGroup_of_homeo (interHomeo' (cofibreU ι) (cofibreV ι)) x₀ hinter
  have hset : Subsingleton (RelHomotopyGroup
      (setIncl {z : ↥(cofibreV ι) | (z : cofibre ι) ∈ cofibreU ι})
      ((interHomeo' (cofibreU ι) (cofibreV ι)) x₀) J) :=
    relPiVanishingOfPiInjSurj J ((interHomeo' (cofibreU ι) (cofibreV ι)) x₀)
      (fun x y _ => hA.elim x y)
      (fun b => ⟨Classical.arbitrary _, hV.elim _ _⟩)
  have hbridge := subsingleton_relPi_of_homeo
    (g := setIncl {z : ↥(cofibreV ι) | (z : cofibre ι) ∈ cofibreU ι})
    (interHomeo' (cofibreU ι) (cofibreV ι)) x₀ J hset
  convert hbridge using 3
  ext x
  rfl

/-- **Blakers–Massey, hypothesis (A)**: the relative homotopy groups of
`(cofibreU ι, cofibreU ι ∩ cofibreV ι)` vanish up to the index `k-2`.

The inputs are the `π`-trivialities of the two pieces: of the collar
`↥(cofibreU ι ∩ cofibreV ι)` in degree `J` (from `collarHomotopyEquiv` and the connectivity of the
fibre `F`) and of `↥(cofibreU ι)` in degree `J+1` (from `cofibreUHomotopyEquiv` and the connectivity
of `E`).  `relPiVanishingOfPiInjSurj` turns them into the vanishing of the relative group of the
subspace inclusion `setIncl {z : ↥B | (z : cofibre ι) ∈ C}`, and `interHomeo` /
`subsingleton_relPi_of_homeo` identify that inclusion with `interInclLeft B C`. -/
theorem subsingleton_relPi_interInclLeft {E F : Type} [TopologicalSpace E] [TopologicalSpace F]
    (ι : C(F, E)) (J : ℕ) (x₀ : ↥(cofibreU ι ∩ cofibreV ι))
    (hinter : Subsingleton (HomotopyGroup (Fin J) ↥(cofibreU ι ∩ cofibreV ι) x₀))
    (hU : Subsingleton (HomotopyGroup (Fin (J + 1)) ↥(cofibreU ι) ⟨x₀.1, x₀.2.1⟩)) :
    Subsingleton (RelHomotopyGroup (interInclLeft (cofibreU ι) (cofibreV ι)) x₀ J) := by
  have hA : Subsingleton (HomotopyGroup (Fin J)
      ↥{z : ↥(cofibreU ι) | (z : cofibre ι) ∈ cofibreV ι}
      ((interHomeo (cofibreU ι) (cofibreV ι)) x₀)) :=
    subsingleton_homotopyGroup_of_homeo (interHomeo (cofibreU ι) (cofibreV ι)) x₀ hinter
  have hset : Subsingleton (RelHomotopyGroup
      (setIncl {z : ↥(cofibreU ι) | (z : cofibre ι) ∈ cofibreV ι})
      ((interHomeo (cofibreU ι) (cofibreV ι)) x₀) J) :=
    relPiVanishingOfPiInjSurj J ((interHomeo (cofibreU ι) (cofibreV ι)) x₀)
      (fun x y _ => hA.elim x y)
      (fun b => ⟨Classical.arbitrary _, hU.elim _ _⟩)
  have hbridge := subsingleton_relPi_of_homeo
    (g := setIncl {z : ↥(cofibreU ι) | (z : cofibre ι) ∈ cofibreV ι})
    (interHomeo (cofibreU ι) (cofibreV ι)) x₀ J hset
  convert hbridge using 3
  ext x
  rfl

end

end Work.RatHurewicz
