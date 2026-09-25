/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.Basic

/-!
# The 2-periodic complex of a representation of a finite cyclic group

For a finite cyclic group `G` with chosen generator `g` and a representation `M : Rep k G`,
the sequence

`⋯ ⟶ M --(ρ g - 1)--> M --N--> M --(ρ g - 1)--> M --N--> ⋯`

(where `N = ∑_{h : G} ρ h` is the norm) is a complex.  Its homology in even degrees is the
Tate cohomology `Ĥ⁰` (`= M^G / N M`) and in odd degrees the Tate cohomology `Ĥ¹`
(`= ker N / (ρ g - 1)M`).

We package this as a functor `perF g : Rep k G ⥤ CochainComplex (ModuleCat k) ℕ`
(`perF g` is Mathlib's `Rep.FiniteCyclicGroup.moduleCatCochainComplex`, made functorial), and we
prove that it carries a short exact sequence of representations to a short exact sequence of
cochain complexes.  Because `Rep ℤ G` is not `ConcreteCategory` over `Ab` in a way that lets one
use `forget₂` at `k = ℤ` (a `Module ℤ` diamond), the short exactness is proved for a *variable*
commutative ring `k` and then specialised.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

/-- The 2-periodic cochain complex of `M : Rep k G` with differentials alternating
`ρ(g) - 1` (even degrees) and the norm `N` (odd degrees). -/
noncomputable def perF {k G : Type} [CommRing k] [CommGroup G] [Fintype G] (g : G) :
    Rep k G ⥤ CochainComplex (ModuleCat k) ℕ where
  obj M := Rep.FiniteCyclicGroup.moduleCatCochainComplex M g
  map f := HomologicalComplex.Hom.mk (fun i => Rep.Hom.toModuleCatHom f) (by
    rintro i j hij
    simp only [Rep.FiniteCyclicGroup.moduleCatCochainComplex, HomologicalComplex.alternatingConst]
    rw [dif_pos hij, dif_pos hij]
    by_cases hi : Even i
    · rw [dif_pos hi, dif_pos hi]
      simp only [← Rep.forget₂_moduleCat_map]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      rw [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id,
        Rep.applyAsHom_comm f g]
    · rw [dif_neg hi, dif_neg hi]
      simp only [← Rep.forget₂_moduleCat_map]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      exact Rep.norm_comm f)
  map_id M := by ext i; rfl
  map_comp f g' := by ext i; rfl

instance perF_pz {k G : Type} [CommRing k] [CommGroup G] [Fintype G] (g : G) :
    (perF (k := k) (G := G) g).PreservesZeroMorphisms where
  map_zero X Y := by
    apply HomologicalComplex.Hom.ext
    funext i
    rw [HomologicalComplex.zero_f]
    show Rep.Hom.toModuleCatHom (0 : X ⟶ Y) = 0
    ext x; simp [Rep.Hom.toModuleCatHom]

section Generic
variable {k G : Type} [CommRing k] [CommGroup G] [Fintype G]

/-- The underlying-module short complex of a short exact sequence of representations is short
exact (proved for a variable coefficient ring, then specialised). -/
lemma forgetRep_shortExact (S : ShortComplex (Rep k G)) (hS : S.ShortExact) :
    (S.map (forget₂ (Rep k G) (ModuleCat k))).ShortExact := by
  haveI := hS.mono_f
  haveI := hS.epi_g
  have hm : Mono ((forget₂ (Rep k G) (ModuleCat k)).map S.f) := by
    rw [Rep.forget₂_moduleCat_map]; infer_instance
  have he : Epi ((forget₂ (Rep k G) (ModuleCat k)).map S.g) := by
    rw [Rep.forget₂_moduleCat_map]; infer_instance
  exact ShortComplex.ShortExact.mk'
    ((ShortComplex.exact_map_iff_of_faithful S (forget₂ (Rep k G) (ModuleCat k))).mpr hS.exact) hm he

/-- The periodic complex of a short exact sequence of representations is short exact. -/
lemma perF_shortExact (g : G) (S : ShortComplex (Rep k G)) (hS : S.ShortExact) :
    (S.map (perF g)).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro i
  exact forgetRep_shortExact S hS

end Generic

end NK.GlobalCFTdeep.Herbrand
