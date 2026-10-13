/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The perfected structure presheaf (node PERF)

For a ring `A` of characteristic `p`, a scheme `X` with `f : X ⟶ Spec A` and a finite affine
cover `U` of `X`, this module builds the *perfected structure presheaf*
`V ↦ Γ(X,V)^{1/p^∞}`, as a presheaf of modules over `W = Γ(X,⊤)^{1/p^∞}`, together with the
natural map `𝒪_X ⟶ 𝒪_X^{1/p^∞}` (at level `0`) of presheaves of `A`-modules.
-/
import Mathlib
import Submission.Work.DSEQP.PerfRing
import Submission.Work.DSF1.Cech.cechComplexFunctor_map_pi
import Submission.Work.DSMap.Map

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped BigOperators

namespace Work.DSEQP

universe u

set_option maxHeartbeats 1000000

/-- The ambient data of the perfected Čech model: a prime `p`, a ring `A` of characteristic `p`,
a scheme `X` with structure morphism `f : X ⟶ Spec A`.  Bundling `f` and the proof that `p = 0`
in `A` makes all the derived objects (`Γ(X,V)^{1/p^∞}`, the perfection `W` of `Γ(X,⊤)`, …)
inferable from a single explicit argument. -/
structure PerfSetup (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) where
  /-- `p` vanishes in `A` (in particular `A` has characteristic `p`). -/
  hA : (p : A) = 0

namespace PerfSetup

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of A)}

/-- The sections of `X` over `V` have characteristic `p`. -/
theorem hpU (S : PerfSetup A p X f) (V : X.Opens) : (p : Γ(X, V)) = 0 := by
  rw [← map_natCast (DSMap.phiU A X f V) p, S.hA, map_zero]

/-- The structure homomorphism `Γ(X,⊤) → Γ(X,V)`. -/
noncomputable def resTop (S : PerfSetup A p X f) (V : X.Opens) : Γ(X, ⊤) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE le_top).op).hom

theorem resTop_comp (S : PerfSetup A p X f) {V V' : X.Opens} (h : V' ≤ V) :
    S.resTop V' =
      ((X.presheaf.map (homOfLE h).op).hom).comp (S.resTop V) := by
  rw [resTop, resTop]
  have h1 : (homOfLE (show V' ≤ ⊤ from le_top) : V' ⟶ ⊤) =
      (homOfLE h : V' ⟶ V) ≫ (homOfLE (show V ≤ ⊤ from le_top) : V ⟶ ⊤) :=
    Subsingleton.elim _ _
  rw [h1, op_comp, Functor.map_comp, CommRingCat.hom_comp]

/-- The perfection of the global sections; the ring `W` of the node `PERF`. -/
noncomputable abbrev W (S : PerfSetup A p X f) : Type u := Perf (Γ(X, ⊤)) p (S.hpU ⊤)

/-- The canonical map `Γ(X,⊤) → W = Γ(X,⊤)^{1/p^∞}`. -/
noncomputable def ψW (S : PerfSetup A p X f) : Γ(X, ⊤) →+* S.W :=
  Perf.of (Γ(X, ⊤)) p (S.hpU ⊤) 0

/-- The perfection of the sections over `V`: the value of the perfected structure presheaf. -/
noncomputable abbrev Psec (S : PerfSetup A p X f) (V : X.Opens) : Type u :=
  Perf (Γ(X, V)) p (S.hpU V)

/-- The structure homomorphism `W → Γ(X,V)^{1/p^∞}`, making the perfection of the sections
over `V` a `W`-module. -/
noncomputable def Wmap (S : PerfSetup A p X f) (V : X.Opens) : S.W →+* S.Psec V :=
  Perf.map (S.hpU ⊤) (S.hpU V) (S.resTop V)

/-- The perfection of the sections over `V` is a `W`-algebra via `W → Γ(X,V)^{1/p^∞}`. -/
noncomputable instance instAlgebraPsec (S : PerfSetup A p X f) (V : X.Opens) :
    Algebra S.W (S.Psec V) :=
  (S.Wmap V).toAlgebra

/-- The value of the perfected structure presheaf at `V`, as a module over `W`. -/
noncomputable abbrev PsecM (S : PerfSetup A p X f) (V : X.Opens) : ModuleCat.{u} S.W :=
  ModuleCat.of S.W (S.Psec V)

/-- The perfection of the sections over `V`, as an `A`-module via `of 0 ∘ φ_U` (this is the
restriction of scalars of `PsecM V` along `ψW ∘ φ`). -/
noncomputable instance instModulePsecA (S : PerfSetup A p X f) (V : X.Opens) :
    Module A (S.Psec V) :=
  Module.compHom _ (S.ψW.comp (DSMap.phi A X f))

theorem Wmap_comp (S : PerfSetup A p X f) {V V' : X.Opens} (h : V' ≤ V) :
    S.Wmap V' = (Perf.map (S.hpU V) (S.hpU V')
      ((X.presheaf.map (homOfLE h).op).hom)).comp (S.Wmap V) := by
  rw [Wmap, Wmap, S.resTop_comp h, Perf.map_comp]

/-- For an arrow `i : V ⟶ V'` of `X.Opensᵒᵖ`, the restriction `Γ(X,V) → Γ(X,V')` is the
restriction attached to the underlying inequality. -/
theorem res_eq (S : PerfSetup A p X f) {V V' : X.Opensᵒᵖ} (i : V ⟶ V') :
    (X.presheaf.map i).hom =
      (X.presheaf.map (homOfLE (leOfHom i.unop)).op).hom := by
  have h : i = (homOfLE (leOfHom i.unop)).op := Subsingleton.elim _ _
  rw [h]

/-- The perfected structure presheaf, as a presheaf of `W`-modules. -/
noncomputable def perfPresheaf (S : PerfSetup A p X f) : X.Opensᵒᵖ ⥤ ModuleCat.{u} S.W where
  obj V := S.PsecM V.unop
  map {V V'} i :=
    ModuleCat.ofHom
      { toFun := fun x => Perf.map (S.hpU V.unop) (S.hpU V'.unop)
          ((X.presheaf.map i).hom) x
        map_add' := fun x y => map_add _ x y
        map_smul' := fun a x => by
          rw [Algebra.smul_def, Algebra.smul_def, map_mul]
          congr 1
          have hW := DFunLike.congr_fun (S.Wmap_comp (leOfHom i.unop)) a
          rw [← S.res_eq i] at hW
          exact hW.symm }
  map_id V := by
    ext x
    show Perf.map (S.hpU V.unop) (S.hpU V.unop)
        ((X.presheaf.map (𝟙 V)).hom) x = x
    have h1 : (X.presheaf.map (𝟙 V)).hom = RingHom.id Γ(X, V.unop) := by
      rw [X.presheaf.map_id]; rfl
    rw [h1]
    exact DFunLike.congr_fun
      (Perf.map_id (R := Γ(X, V.unop)) (p := p) (hp := S.hpU V.unop)) x
  map_comp {V V' V''} i j := by
    ext x
    show Perf.map (S.hpU V.unop) (S.hpU V''.unop) ((X.presheaf.map (i ≫ j)).hom) x =
      Perf.map (S.hpU V'.unop) (S.hpU V''.unop) ((X.presheaf.map j).hom)
        (Perf.map (S.hpU V.unop) (S.hpU V'.unop) ((X.presheaf.map i).hom) x)
    have h2 : (X.presheaf.map (i ≫ j)).hom =
        ((X.presheaf.map j).hom).comp ((X.presheaf.map i).hom) := by
      rw [X.presheaf.map_comp]; rfl
    rw [h2]
    exact DFunLike.congr_fun
      (Perf.map_comp (hp := S.hpU V.unop) (hpS := S.hpU V'.unop) (hpT := S.hpU V''.unop)
        ((X.presheaf.map i).hom) ((X.presheaf.map j).hom)) x

end PerfSetup

end Work.DSEQP
