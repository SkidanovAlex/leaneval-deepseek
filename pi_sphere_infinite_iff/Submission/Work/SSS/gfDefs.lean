import Mathlib
import Submission.Work.SSS.Packet

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Auxiliary objects for the "graded piece" step of the Serre spectral sequence

This file collects the elementary homological-algebra inputs used to prove
`Work.SSS.gradedField`: the explicit model of `E²_{s,t}` as the homology of the short complex
`E¹_{s+1,t} → E¹_{s,t} → E¹_{s-1,t}` together with the canonical map `H_{s+t}(F_s) → E²_{s,t}`
and the elementwise description of its kernel.
-/

set_option autoImplicit false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-- Transfer of finite generation of the range of a homology map across an equal degree. -/
theorem FGrng {K L : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L) {i j : ℕ} (h : i = j)
    (hf : (LinearMap.range (HomologicalComplex.homologyMap f i).hom).FG) :
    (LinearMap.range (HomologicalComplex.homologyMap f j).hom).FG := by
  subst h; exact hf

/-- The differential of the `E¹` complex in degree `j`. -/
theorem e1c_d (ξ : Filtration C) (t j : ℕ) : (E1Complex ξ t).d (j+1) j = d1 ξ j t :=
  ChainComplex.of_d (fun s => E1 ξ s t) (fun s => d1 ξ s t) j

theorem scf (ξ : Filtration C) (t k : ℕ) :
    ((E1Complex ξ t).sc' (k+2) (k+1) k).f = d1 ξ (k+1) t := by
  show (E1Complex ξ t).d (k+2) (k+1) = _
  exact e1c_d ξ t (k+1)

theorem scg (ξ : Filtration C) (t k : ℕ) :
    ((E1Complex ξ t).sc' (k+2) (k+1) k).g = d1 ξ k t := by
  show (E1Complex ξ t).d (k+1) k = _
  exact e1c_d ξ t k

theorem jFkF (ξ : Filtration C) (s t : ℕ) : jF ξ (s+1) t ≫ kF ξ s t = 0 :=
  ShortComplex.ShortExact.comp_δ (sesF_shortExact ξ s) ((s+1)+t) (s+t)
    (by simp [ComplexShape.down]; omega)

theorem jFd1 (ξ : Filtration C) (k t : ℕ) : jF ξ (k+1) t ≫ d1 ξ k t = 0 := by
  rw [d1, ← Category.assoc, jFkF, zero_comp]

theorem kFincl (ξ : Filtration C) (k t : ℕ) :
    kF ξ (k+1) t ≫ HomologicalComplex.homologyMap (ξ.incl (k+1)) ((k+1)+t) = 0 := by
  have h1 : kF ξ (k+1) t ≫ HomologicalComplex.homologyMap (incF ξ.F (k+1)) ((k+1)+t) = 0 :=
    ShortComplex.ShortExact.δ_comp (sesF_shortExact ξ (k+1)) ((k+1)+1+t) ((k+1)+t)
      (by simp [ComplexShape.down]; omega)
  have h2 : HomologicalComplex.homologyMap (ξ.incl (k+1)) ((k+1)+t) =
      HomologicalComplex.homologyMap (incF ξ.F (k+1)) ((k+1)+t) ≫
      HomologicalComplex.homologyMap (ξ.incl (k+2)) ((k+1)+t) := by
    conv_lhs => rw [show ξ.incl (k+1) = incF ξ.F (k+1) ≫ ξ.incl (k+2) from
      (ξ.compat (Nat.le_succ (k+1))).symm]
    rw [HomologicalComplex.homologyMap_comp]
  rw [h2, ← Category.assoc, h1, zero_comp]

/-- The kernel of `jF ξ (k+1) t` is the image of `H(incF ξ.F k)`. -/
theorem kerjF (ξ : Filtration C) (k t : ℕ) :
    (jF ξ (k+1) t).hom.ker =
      (HomologicalComplex.homologyMap (incF ξ.F k) ((k+1)+t)).hom.range :=
  (((sesF_shortExact ξ k).homology_exact₂ ((k+1)+t)).moduleCat_range_eq_ker).symm

/-- The canonical map `H_{s+t}(F_s) → E²_{s,t}` for `s = k+1`, realised through the short complex
`E¹_{s+1,t} → E¹_{s,t} → E¹_{s-1,t}` computing `E²_{s,t}`. -/
noncomputable def e2MapG (ξ : Filtration C) (k t : ℕ) :
    (ξ.F.obj (k+1)).homology ((k+1) + t) ⟶
      ((E1Complex ξ t).sc' (k+2) (k+1) k).homology :=
  ((E1Complex ξ t).sc' (k+2) (k+1) k).liftCycles (jF ξ (k+1) t)
      (by rw [scg]; exact jFd1 ξ k t) ≫
    ((E1Complex ξ t).sc' (k+2) (k+1) k).homologyπ

/-- In `ModuleCat R`, an element is killed by the projection onto the cokernel of `f` if and only
if it lies in the range of `f`. -/
lemma coker_pi_apply_eq_zero_iff.{v, u} {R : Type u} [Ring R] {X Y : ModuleCat.{v, u} R}
    (f : X ⟶ Y) (y : Y) :
    (cokernel.π f) y = 0 ↔ y ∈ f.hom.range := by
  constructor
  · intro h
    have h2 : Submodule.Quotient.mk (p := f.hom.range) y = 0 := by
      rw [← ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom_apply f y, h, map_zero]
    exact (Submodule.Quotient.mk_eq_zero (f.hom.range)).mp h2
  · intro h
    obtain ⟨m, hm⟩ := h
    rw [← hm]
    exact cokernel.condition_apply f m

/-- An element killed by the projection to the cokernel of `f` lies in the range of `f`. -/
lemma mem_range_of_coker_pi_eq_zero.{v, u} {R : Type u} [Ring R] {X Y : ModuleCat.{v, u} R}
    (f : X ⟶ Y) {y : Y} (h : (cokernel.π f) y = 0) : y ∈ f.hom.range :=
  (coker_pi_apply_eq_zero_iff f y).mp h

/-- If a cycle `φ : A ⟶ S.X₂` of a short complex in `ModuleCat R` maps to zero under the composite
`A → S.cycles → S.homology`, then its value at any element lies in the range of `S.f`. -/
lemma ker_sc_le.{v, u} {R : Type u} [Ring R] (S : ShortComplex (ModuleCat.{v, u} R)) [S.HasHomology]
    {A : ModuleCat.{v, u} R} (φ : A ⟶ S.X₂) (hφ : φ ≫ S.g = 0) (x : A)
    (hx : ((S.liftCycles φ hφ ≫ S.homologyπ).hom) x = 0) :
    (φ.hom) x ∈ (S.f).hom.range := by
  have hA : (((S.liftCycles φ hφ ≫ S.homologyπ) ≫ S.homologyι).hom) x = 0 := by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, hx, map_zero]
  have hB : ((S.liftCycles φ hφ ≫ S.homologyπ) ≫ S.homologyι) = φ ≫ S.pOpcycles := by
    rw [Category.assoc, ShortComplex.homology_π_ι, ← Category.assoc, ShortComplex.liftCycles_i]
  have h1 : ((φ ≫ S.pOpcycles).hom) x = 0 := by rw [← hB]; exact hA
  have h2 : (S.pOpcycles.hom) ((φ.hom) x) = 0 := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h1
  have hcomp : S.pOpcycles ≫ S.opcyclesIsoCokernel.hom = cokernel.π S.f := by
    rw [ShortComplex.opcyclesIsoCokernel_hom]
    exact S.p_descOpcycles _ _
  have h3 : (cokernel.π S.f).hom ((φ.hom) x) = 0 := by
    have hh := congrArg (fun (g : S.X₂ ⟶ cokernel S.f) => g.hom ((φ.hom) x)) hcomp
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, h2, map_zero] at hh
    exact hh.symm
  have h3' : (cokernel.π S.f) ((φ.hom) x) = 0 := by simpa using h3
  exact mem_range_of_coker_pi_eq_zero S.f h3'

end

end Work.SSS
