import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.Thom.ATools
import Submission.Work.Tubular.thomClass_span_top

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The standard Thom generator of `(ℝ^k, ℝ^k∖0)` generates

`Work.ThomBordism.stdThomGen k : H^k(ℝ^k, ℝ^k∖0;ℤ)` is the transport of the Thom class of the
trivial rank-`k` bundle over a point along the trivialisation (see
`Submission/Work/ThomBordism/orientedFibreGen.lean`).  This module proves that it *generates* the
`ℤ`-module `H^k(ℝ^k, ℝ^k∖0;ℤ)` — the only property of it that the fibre comparison of the last mile
of `Work.ThomBordism.thomRational` needs.

The argument:

* `Work.Tubular.thomClass_span_top` — a Thom class generates the relative cohomology of the Thom
  pair of its bundle — applied to the trivial bundle over a point gives `span {τ} = ⊤`, where `τ` is
  the chosen Thom class of that bundle (`Work.Thom.thomClass_trivial_point`);
* the pullback along the *homeomorphism of pairs* `ℝ^k ≅ (trivial bundle).TotalSpace`,
  `v ↦ trivProductHomeo.symm (pt, v)`, is surjective (`relCohMap_compA` applied to the explicit
  mutually inverse pair of maps `trivProductHomeo.symm ∘ (pt, ·)` and
  `p ↦ (trivProductHomeo p).2`, which are inverse to each other because the base is a point);
* `stdThomGen k` is *by definition* the pullback of `τ` along that map, so a surjective `ℤ`-linear
  map carries the generator `τ` to a generator (`Work.Tubular.span_singleton_map_eq_top`).
-/

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

/-- **A generator survives a change of degrees** (the inverse direction of the degree-cast
bookkeeping): if `h ▸ x` generates `M b`, then `x` generates `M a`. -/
theorem span_of_cast_singleton_eq_top {M : ℕ → Type*} [∀ n, AddCommGroup (M n)]
    [∀ n, Module ℤ (M n)] {a b : ℕ} (h : a = b) (x : M a)
    (hx : Submodule.span ℤ ({(h ▸ x)} : Set (M b)) = ⊤) :
    Submodule.span ℤ ({x} : Set (M a)) = ⊤ := by
  cases h
  simpa using hx

theorem stdThomGen_span (k : ℕ) (hk : 1 ≤ k) :
    Submodule.span ℤ ({stdThomGen k hk} : Set (Work.Thom.RelCoh ℤ k
      (EuclideanSpace ℝ (Fin k)) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))))) = ⊤ := by
  classical
  -- the trivial rank-`k` bundle over a point, and its chosen Thom class
  let Z : Work.TangentClasses.RealBundle PUnit (EuclideanSpace ℝ (Fin k)) PUnit :=
    Work.TangentClasses.RealBundle.trivial PUnit (EuclideanSpace ℝ (Fin k)) PUnit
  let T : Work.Thom.ThomClass Z k :=
    Classical.choice (Work.Thom.thomClass_trivial_point k hk PUnit)
  -- the two mutually inverse maps of pairs
  let MAP : C(EuclideanSpace ℝ (Fin k), Z.TotalSpace) :=
    ((↑(Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit).symm :
        C(PUnit × EuclideanSpace ℝ (Fin k),
          (Work.TangentClasses.RealBundle.trivial PUnit (EuclideanSpace ℝ (Fin k))
            PUnit).TotalSpace)).comp
      ⟨fun v : EuclideanSpace ℝ (Fin k) => (PUnit.unit, v),
        continuous_const.prodMk continuous_id⟩)
  let Ψ : C(Z.TotalSpace, EuclideanSpace ℝ (Fin k)) :=
    ⟨fun p => (Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit p).2,
      continuous_snd.comp
        (Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit).continuous⟩
  -- the membership datum of `MAP` is *literally* the one occurring in the definition of `stdThomGen`
  let PF : ∀ v ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))), MAP v ∈ Work.Thom.zeroComplement Z :=
    fun v hv => by
      change (Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit).symm
        (PUnit.unit, v) ∈ Work.Thom.zeroComplement
          (Work.TangentClasses.RealBundle.trivial PUnit (EuclideanSpace ℝ (Fin k)) PUnit)
      rw [Work.Thom.mem_zeroComplement]
      intro h0
      have h1 : (Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit
          ((Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit).symm
            (PUnit.unit, v))).2 = v :=
        congrArg Prod.snd (Homeomorph.apply_symm_apply _ _)
      have h2 : (show EuclideanSpace ℝ (Fin k) from
          ((Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit).symm
            (PUnit.unit, v)).2)
          = (Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit
              ((Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit).symm
                (PUnit.unit, v))).2 := by
        rw [Work.Thom.trivProductHomeo_apply]
      rw [h2, h1] at h0
      exact hv h0
  -- `stdThomGen` is the pullback of `T.τ` along `MAP`
  have hstd : stdThomGen k hk
      = (Work.Thom.relCohMap MAP ({0}ᶜ) (Work.Thom.zeroComplement Z) PF ℤ k).hom T.τ := rfl
  -- the two maps are inverse to one another
  have hΨsnd : ∀ p : Z.TotalSpace,
      (Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit p).2
        = (show EuclideanSpace ℝ (Fin k) from p.2) := fun p => by
    rw [Work.Thom.trivProductHomeo_apply]
  have hΨMAP : ∀ v : EuclideanSpace ℝ (Fin k), Ψ (MAP v) = v := by
    intro v
    have h1 : (Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit) (MAP v)
        = (PUnit.unit, v) := by
      rw [show MAP v = (Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit).symm
        (PUnit.unit, v) from rfl]
      exact Homeomorph.apply_symm_apply _ _
    show (Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit (MAP v)).2 = v
    rw [h1]
  have hMAPΨ : ∀ p : Z.TotalSpace, MAP (Ψ p) = p := by
    intro p
    show (Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit).symm
        (PUnit.unit, (Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit p).2) = p
    rw [Homeomorph.symm_apply_eq]
  -- the membership data of the two maps of pairs
  have hg : ∀ y ∈ Work.Thom.zeroComplement Z,
      Ψ y ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))) := by
    intro y hy
    rw [Work.Thom.mem_zeroComplement] at hy
    rw [Set.mem_compl_singleton_iff]
    exact fun h0 => hy (hΨsnd y ▸ h0)
  have hgf : ∀ x ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))),
      (Ψ.comp MAP) x ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))) := by
    intro x hx
    rw [ContinuousMap.comp_apply, hΨMAP x]
    exact hx
  have hgf' : ∀ y ∈ Work.Thom.zeroComplement Z,
      (MAP.comp Ψ) y ∈ Work.Thom.zeroComplement Z := by
    intro y hy
    rw [ContinuousMap.comp_apply, hMAPΨ y]
    exact hy
  -- the two composites are the identities
  have hcomp_id : Ψ.comp MAP = ContinuousMap.id (EuclideanSpace ℝ (Fin k)) :=
    ContinuousMap.ext hΨMAP
  have hcomp_id' : MAP.comp Ψ = ContinuousMap.id Z.TotalSpace :=
    ContinuousMap.ext hMAPΨ
  have hcompA : Work.Thom.relCohMap Ψ (Work.Thom.zeroComplement Z)
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))) hg ℤ k
      ≫ Work.Thom.relCohMap MAP ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k)))
          (Work.Thom.zeroComplement Z) PF ℤ k
      = 𝟙 (Work.Thom.RelCoh ℤ k (EuclideanSpace ℝ (Fin k))
          ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k)))) := by
    rw [Work.Thom.relCohMap_compA (A := ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))))
      (B := Work.Thom.zeroComplement Z) (C := ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))))
      MAP Ψ PF hg hgf ℤ k]
    exact (Work.Thom.relCohMap_congrA (A := ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))))
      (B := ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k)))) hcomp_id hgf
      (fun _ hx => hx) ℤ k).trans (Work.Thom.relCohMap_idA ({0}ᶜ) ℤ k)
  have hcompB : Work.Thom.relCohMap MAP ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k)))
        (Work.Thom.zeroComplement Z) PF ℤ k
      ≫ Work.Thom.relCohMap Ψ (Work.Thom.zeroComplement Z)
          ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))) hg ℤ k
      = 𝟙 (Work.Thom.RelCoh ℤ k Z.TotalSpace (Work.Thom.zeroComplement Z)) := by
    rw [Work.Thom.relCohMap_compA (A := Work.Thom.zeroComplement Z)
      (B := ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k)))) (C := Work.Thom.zeroComplement Z)
      Ψ MAP hg PF hgf' ℤ k]
    exact (Work.Thom.relCohMap_congrA (A := Work.Thom.zeroComplement Z)
      (B := Work.Thom.zeroComplement Z) hcomp_id' hgf' (fun _ hy => hy) ℤ k).trans
      (Work.Thom.relCohMap_idA (Work.Thom.zeroComplement Z) ℤ k)
  -- hence the pullback along `MAP` is surjective
  have hsurj : Function.Surjective
      (Work.Thom.relCohMap MAP ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k)))
        (Work.Thom.zeroComplement Z) PF ℤ k).hom := by
    have hlin : (Work.Thom.relCohMap MAP ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k)))
          (Work.Thom.zeroComplement Z) PF ℤ k).hom.comp
        (Work.Thom.relCohMap Ψ (Work.Thom.zeroComplement Z)
          ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))) hg ℤ k).hom = LinearMap.id := by
      have h := congrArg ModuleCat.Hom.hom hcompA
      rwa [ModuleCat.hom_comp, ModuleCat.hom_id] at h
    exact fun y => ⟨(Work.Thom.relCohMap Ψ (Work.Thom.zeroComplement Z)
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))) hg ℤ k).hom y, LinearMap.congr_fun hlin y⟩
  -- `T.τ` generates the relative cohomology of the Thom pair
  have hspanτ : Submodule.span ℤ ({T.τ} : Set (Work.Thom.OpenThom Z k)) = ⊤ :=
    span_of_cast_singleton_eq_top (M := fun n => Work.Thom.OpenThom Z n)
      (Nat.zero_add k).symm T.τ (Work.Tubular.thomClass_span_top Z k T)
  rw [hstd]
  exact Work.Tubular.span_singleton_map_eq_top
    ((Work.Thom.relCohMap MAP ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k)))
      (Work.Thom.zeroComplement Z) PF ℤ k).hom) hsurj T.τ hspanτ

end Work.ThomBordism
