import Mathlib
import Submission.Work.SSS.ExpTens

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The long exact sequence for `expTens K -` and finiteness of the homology

This file contains the two ingredients of the universal-coefficient argument underlying
`Work.SSS.tensorHomology`:

* `Work.SSS.expTensShort K S` (and `Work.SSS.expTensShort_shortExact`): a short exact sequence of
  `ℤ`-modules `0 → P → Q → M → 0` tensored with a degreewise flat complex `K` is again a short
  exact sequence of complexes;
* `Work.SSS.finite_homology_middle`, `Work.SSS.finite_homology_third`: the resulting long exact
  sequence and the behaviour of finite generation along it.
-/

set_option autoImplicit false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

noncomputable section

/-- If `A ⟶ B ⟶ C` is exact and `A`, `C` are finitely generated `ℤ`-modules, then so is `B`. -/
theorem moduleCat_finite_of_exact {A B C : ModuleCat ℤ} (f : A ⟶ B) (g : B ⟶ C)
    (h : Function.Exact f.hom g.hom) [Module.Finite ℤ A] [Module.Finite ℤ C] :
    Module.Finite ℤ B := by
  have hker : LinearMap.range f.hom = LinearMap.ker g.hom := (LinearMap.exact_iff.mp h).symm
  refine ⟨(⊤ : Submodule ℤ ↥B).fg_of_fg_map_of_fg_inf_ker g.hom ?_ ?_⟩
  · rw [Submodule.map_top]
    exact IsNoetherian.noetherian _
  · rw [top_inf_eq, ← hker, LinearMap.range_eq_map]
    exact Submodule.FG.map f.hom (Module.Finite.fg_top (R := ℤ) (M := ↥A))

variable (K : ChainComplex (ModuleCat ℤ) ℕ)

/-- Applying `expTens K -` to a short complex of `ℤ`-modules. -/
def expTensShort (S : ShortComplex (ModuleCat ℤ)) : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (expTensHom K S.f) (expTensHom K S.g) (by
    apply hom_ext
    intro n
    rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f, expTensHom_f, expTensHom_f]
    simp only [← MonoidalCategory.id_tensorHom]
    rw [MonoidalCategory.tensorHom_comp_tensorHom, S.zero]
    simp)

variable {K}

theorem expTensShort_shortExact (S : ShortComplex (ModuleCat ℤ)) (hS : S.ShortExact)
    (hK : ∀ n, Module.Flat ℤ (K.X n)) : (expTensShort K S).ShortExact := by
  haveI : ∀ n, Module.Flat ℤ (K.X n) := hK
  rw [shortExact_iff_degreewise_shortExact]
  intro n
  set T := (expTensShort K S).map (eval (ModuleCat ℤ) (ComplexShape.down ℕ) n) with hT
  have hf : T.f = K.X n ◁ S.f := rfl
  have hg : T.g = K.X n ◁ S.g := rfl
  have hmono : Mono T.f := by
    rw [hf]
    refine (ModuleCat.mono_iff_injective (K.X n ◁ S.f)).mpr ?_
    change Function.Injective (S.f.hom.lTensor (K.X n))
    exact Module.Flat.lTensor_preserves_injective_linearMap S.f.hom
      ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)
  have hepi : Epi T.g := by
    rw [hg]
    refine (ModuleCat.epi_iff_surjective (K.X n ◁ S.g)).mpr ?_
    change Function.Surjective (S.g.hom.lTensor (K.X n))
    exact LinearMap.lTensor_surjective _
      ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)
  have hex : T.Exact :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mpr (by
      rw [hf, hg]
      change Function.Exact (S.f.hom.lTensor (K.X n)) (S.g.hom.lTensor (K.X n))
      exact Module.Flat.lTensor_exact (K.X n)
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact))
  exact ShortComplex.ShortExact.mk' hex hmono hepi

/-- The long exact sequence in the middle degree: if `H_n(X₁)` and `H_n(X₃)` are finitely
generated, then so is `H_n(X₂)`. -/
theorem finite_homology_middle (S : ShortComplex (ModuleCat ℤ)) (hS : S.ShortExact)
    (hK : ∀ n, Module.Flat ℤ (K.X n)) (n : ℕ)
    (h1 : Module.Finite ℤ ((expTensShort K S).X₁.homology n))
    (h3 : Module.Finite ℤ ((expTensShort K S).X₃.homology n)) :
    Module.Finite ℤ ((expTensShort K S).X₂.homology n) := by
  have hSE := expTensShort_shortExact S hS hK
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (hSE.homology_exact₂ n)
  exact moduleCat_finite_of_exact _ _ hex

/-- The long exact sequence in the third degree: if `H_n(X₂)` and `H_{n-1}(X₁)` are finitely
generated, then so is `H_n(X₃)`. -/
theorem finite_homology_third (S : ShortComplex (ModuleCat ℤ)) (hS : S.ShortExact)
    (hK : ∀ n, Module.Flat ℤ (K.X n)) (n : ℕ) (hn : 1 ≤ n)
    (h2 : Module.Finite ℤ ((expTensShort K S).X₂.homology n))
    (h1 : Module.Finite ℤ ((expTensShort K S).X₁.homology (n - 1))) :
    Module.Finite ℤ ((expTensShort K S).X₃.homology n) := by
  have hSE := expTensShort_shortExact S hS hK
  have hij : (ComplexShape.down ℕ).Rel n (n - 1) := by
    rw [ComplexShape.down_Rel]
    omega
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (hSE.homology_exact₃ n (n - 1) hij)
  exact moduleCat_finite_of_exact _ _ hex

end

end Work.SSS
