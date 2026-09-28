import Mathlib
import Submission.Work.SSS.FibreColDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

namespace Work.SSS.ModelIncl

attribute [-instance] AddCommGroup.toIntModule

open CategoryTheory CategoryTheory.Limits

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-- The inclusion `F_s ⟶ C` is injective on chains, in every degree: it is the degreewise part of
the monomorphism `ξ.incl s`. -/
theorem Cincl_injective (ξ : Filtration C) (s n : ℕ) : Function.Injective (Cincl ξ s n) := by
  have h : Mono (ξ.incl s) := ξ.mono_incl s
  have h2 : Mono ((ξ.incl s).f n) := inferInstance
  exact (ModuleCat.mono_iff_injective _).mp h2

/-- Naturality of `Cincl` with respect to `Finc`: the inclusion into `C` of the image in `F_b` of a
chain of `F_a` is the inclusion of that chain.  This is the degreewise form of `ξ.compat`. -/
theorem Cincl_Finc (ξ : Filtration C) {a b : ℕ} (h : a ≤ b) (n : ℕ)
    (y : (ξ.F.obj a).X n) :
    Cincl ξ b n (Finc ξ a b h n y) = Cincl ξ a n y := by
  have key : (Cincl ξ b n).comp (Finc ξ a b h n) = Cincl ξ a n := by
    have hc : ((ξ.F.map (homOfLE h)).f n ≫ (ξ.incl b).f n) = (ξ.incl a).f n := by
      rw [← HomologicalComplex.comp_f, ξ.compat h]
    have hc2 := congrArg (fun (m : (ξ.F.obj a).X n ⟶ C.X n) => m.hom) hc
    simp only [Cincl, Finc]
    rw [← ModuleCat.hom_comp, hc2]
  exact LinearMap.congr_fun key y

/-- Inside the chains `(F_s/F_{s-1})_n` of the graded piece, the model `Z^s_{s,n}` of the
transgression source is contained in the model `Z²_{s,n}` of the `E²` term: the chains of `F_s`
whose boundary lies in `F_0` are among those whose boundary lifts to `F_{s-2}` (using
`F_0 ⊆ F_{s-2}`, which is why `2 ≤ s` is assumed). -/
theorem Zs_le_Zsq {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) (s n : ℕ) (hs : 2 ≤ s) :
    Zs ξ s n ≤ Zsq ξ s n := by
  rw [Zs, Zsq]
  apply Submodule.map_mono
  intro z hz
  rw [Submodule.mem_comap]
  simp only [Wrel, Submodule.mem_comap] at hz
  rw [mem_Fch] at hz
  obtain ⟨y, hy⟩ := hz
  rw [LinearMap.mem_range]
  refine ⟨Finc ξ 0 (s - 2) (by omega) (n - 1) y, ?_⟩
  apply Cincl_injective ξ s (n - 1)
  rw [Cincl_Finc, Cincl_Finc]
  exact hy

end Work.SSS.ModelIncl
