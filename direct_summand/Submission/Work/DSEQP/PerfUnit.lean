/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The level-`0` map `𝒪_X → 𝒪_X^{1/p^∞}` (node PERF)

The natural transformation from the structure presheaf to the perfected structure presheaf,
at level `0`, as a map of presheaves of `A`-modules for the ring hom `ψW ∘ φ : A → W`.
-/
import Mathlib
import Submission.Work.DSEQP.PerfPresheaf

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped BigOperators

namespace Work.DSEQP

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000

namespace PerfSetup

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of A)}

/-- The `A`-module structure on the values of the perfected structure presheaf (restriction of
scalars along `ψW ∘ φ`); stated in the form in which it is needed by the Čech construction. -/
noncomputable instance instModuleA_obj (S : PerfSetup A p X f) (V : X.Opensᵒᵖ) :
    Module A ↥(S.perfPresheaf.obj V) :=
  Module.compHom (S.Psec V.unop) (S.ψW.comp (DSMap.phi A X f))

/-- The level-`0` map `𝒪_X → 𝒪_X^{1/p^∞}`, as a map of presheaves of `A`-modules. -/
noncomputable def unitNat (S : PerfSetup A p X f) :
    DSMap.cechPresheaf A X f ⟶
      S.perfPresheaf ⋙ ModuleCat.restrictScalars (S.ψW.comp (DSMap.phi A X f)) where
  app V :=
    letI : Algebra A Γ(X, V.unop) := (DSMap.phiU A X f V.unop).toAlgebra
    ModuleCat.ofHom
      { toFun := fun x => Perf.of (Γ(X, V.unop)) p (S.hpU V.unop) 0 x
        map_add' := fun x y => map_add _ x y
        map_smul' := fun a x => by
          show Perf.of (Γ(X, V.unop)) p (S.hpU V.unop) 0
              (DSMap.phiU A X f V.unop a * x) =
            S.Wmap V.unop (S.ψW (DSMap.phi A X f a)) *
              Perf.of (Γ(X, V.unop)) p (S.hpU V.unop) 0 x
          rw [map_mul]
          congr 1
          have hφ : DSMap.phiU A X f V.unop a =
              S.resTop V.unop (DSMap.phi A X f a) := by
            have h2 : DSMap.phiU A X f ⊤ = DSMap.phi A X f := by
              ext b
              show (X.presheaf.map (homOfLE le_top).op).hom (DSMap.phi A X f b) = _
              rw [Subsingleton.elim (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) (𝟙 ⊤), op_id,
                X.presheaf.map_id]
              rfl
            have h1 := DSMap.phiU_res A X f (homOfLE (le_top : V.unop ≤ ⊤)) a
            rw [h2] at h1
            exact h1.symm
          rw [hφ, ← Perf.map_of (hp := S.hpU ⊤) (hpS := S.hpU V.unop)
            (f := S.resTop V.unop) 0 (DSMap.phi A X f a)]
          rfl }
  naturality {V V'} i := by
    letI : Algebra A Γ(X, V.unop) := (DSMap.phiU A X f V.unop).toAlgebra
    letI : Algebra A Γ(X, V'.unop) := (DSMap.phiU A X f V'.unop).toAlgebra
    ext x
    show Perf.of (Γ(X, V'.unop)) p (S.hpU V'.unop) 0 ((X.presheaf.map i).hom x) =
      Perf.map (S.hpU V.unop) (S.hpU V'.unop) ((X.presheaf.map i).hom)
        (Perf.of (Γ(X, V.unop)) p (S.hpU V.unop) 0 x)
    rw [Perf.map_of]

end PerfSetup

end Work.DSEQP
