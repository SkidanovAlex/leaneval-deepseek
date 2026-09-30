/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# COV′ from a `Γ`-stable covering over a finite Galois extension

The covering `COV′` of §3.5 asks for a finite Galois extension `k'/k` and finitely many centres
whose `Γ = Gal(k'/k)`-orbits cover every degree-zero class over every `k`-algebra receiving
`k'`.  This file shows that *all the Galois bookkeeping is free*: from a covering over `k'`
which is already stable under the conjugation action of `Γ`, the structure `GalCharts` is built
with index set `Γ × ι₀`, centres `E (σ, i) = Spec.map σ ≫ E₀ i` and `act σ (τ, i) = (σ * τ, i)`.

**Convention (important).**  The lead's notes write the compatibility of the Γ-action on the
centres as `E (act σ i) = (E i).map σ.symm`.  That convention is *inconsistent* with `act` being
a group homomorphism: the map `σ ↦ (E ↦ (E).map σ.symm)` is an **anti**-homomorphism, so with
`σ.symm` the axiom would force `(σ₁σ₂)` and `(σ₂σ₁)` to act in the same way on the centres,
which can hold only if `k' ≃ₐ[k] k'` is abelian.  `GalCharts.E_act` (in `Cover.lean`) uses the
correct convention `E (act σ i) = (E i).map σ`; the orbit of a centre — all that area `DS`
consumes — is the same set with either convention.
-/
import Submission.Work.Charts.Cover

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open scoped Classical MonoidalCategory

namespace Work.Charts

open Work.CurveBasics
open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K]

/-- **COV′ from a `Γ`-stable covering over `k'`.**  Given a finite Galois extension `k'/k`, a
chart datum `d` over `k`, finitely many `k'`-points `E₀` of `Sym^g C` and the covering property
that every class over every `k`-algebra `F` receiving `k'` is contained in the chart of a *whole
orbit* of conjugates of one of the `E₀ i`, the Galois-equivariant covering `GalCharts` exists.

The centres of the resulting `GalCharts` are indexed by `Γ × ι₀` and are the conjugates
`Spec.map σ ≫ E₀ i` of the given ones, with the Galois action `act σ (τ, i) = (σ * τ, i)`. -/
theorem galCharts_of_orbit_cover {C : Curve K} [Work.SpecLin.DivBase C] (R : RochData C)
    [Work.SpecLin.SymGeom C R.g] {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
    (k' : Type u) [Field k'] [Algebra K k'] [IsGalois K k'] [FiniteDimensional K k']
    (d : BNData C R) {ι₀ : Type u} [Fintype ι₀] (E₀ : ι₀ → FPt (Sym C R.g) k')
    (hcover : ∀ {F : Type u} [Field F] [Algebra K F] (ε : k' →ₐ[K] F) (c : Pic0 C F),
      ∃ i : ι₀, ∀ τ : k' ≃ₐ[K] k',
        InChart d (RPt.map (ε.comp τ.toAlgHom) (E₀ i)) c) :
    Nonempty (GalCharts C R P0) := by
  let actH : (k' ≃ₐ[K] k') →* Equiv.Perm ((k' ≃ₐ[K] k') × ι₀) :=
    MonoidHom.mk' (fun σ =>
      { toFun := fun p => (σ * p.1, p.2)
        invFun := fun p => (σ.symm * p.1, p.2)
        left_inv := by
          intro p
          refine Prod.ext ?_ rfl
          show (σ.symm * σ) * p.1 = p.1
          rw [show σ.symm * σ = 1 from inv_mul_cancel σ, one_mul]
        right_inv := by
          intro p
          refine Prod.ext ?_ rfl
          show (σ * σ.symm) * p.1 = p.1
          rw [show σ * σ.symm = 1 from mul_inv_cancel σ, one_mul] }) (by
      intro σ₁ σ₂
      apply Equiv.ext
      intro p
      exact Prod.ext (mul_assoc _ _ _) rfl)
  let Idx : Type u := (k' ≃ₐ[K] k') × ι₀
  let EH : Idx → FPt (Sym C R.g) k' := fun p => RPt.map p.1.toAlgHom (E₀ p.2)
  have heact : ∀ (σ : k' ≃ₐ[K] k') (i : Idx), EH (actH σ i) = RPt.map σ.toAlgHom (EH i) := by
    intro σ i
    obtain ⟨τ, j⟩ := i
    show RPt.map (σ * τ).toAlgHom (E₀ j) = RPt.map σ.toAlgHom (RPt.map τ.toAlgHom (E₀ j))
    rw [show RPt.map σ.toAlgHom (RPt.map τ.toAlgHom (E₀ j))
        = RPt.map (σ.toAlgHom.comp τ.toAlgHom) (E₀ j) from
      (RPt.map_comp (K := K) τ.toAlgHom σ.toAlgHom (E₀ j)).symm]
    congr 1
  have hocov : ∀ {F : Type u} [Field F] [Algebra K F] (ε : k' →ₐ[K] F) (c : Pic0 C F),
      ∃ i : Idx, ∀ σ : k' ≃ₐ[K] k', InChart d (RPt.map ε (EH (actH σ i))) c := by
    intro F _ _ ε c
    obtain ⟨i₀, hi₀⟩ := hcover ε c
    refine ⟨(1, i₀), ?_⟩
    intro σ
    have h := hi₀ σ
    show InChart d (RPt.map ε (RPt.map (σ * 1).toAlgHom (E₀ i₀))) c
    rw [mul_one]
    rw [show RPt.map ε (RPt.map σ.toAlgHom (E₀ i₀))
        = RPt.map (ε.comp σ.toAlgHom) (E₀ i₀) from
      (RPt.map_comp (K := K) σ.toAlgHom ε (E₀ i₀)).symm]
    exact h
  exact ⟨GalCharts.mk k' d Idx EH actH heact hocov⟩

/-- **Area `CH`, named input: COV′.**  For every chart datum over `k` there exist a finite
Galois extension `k'/k`, finitely many `k'`-points of `Sym^g C` and the `Γ`-stable covering
property of `galCharts_of_orbit_cover`.

This is step 6 of §3.5, in the form in which the Galois bookkeeping has been removed; it
replaces the coarse input `HasGalCharts` of `Cover.lean`. -/
class OrbitCover (K : Type u) [Field K] : Prop where
  /-- the `Γ`-stable covering over a finite Galois extension -/
  exists_orbit_cover : ∀ {C : Curve K} [Work.SpecLin.DivBase C] (R : RochData C)
    [Work.SpecLin.SymGeom C R.g] (d : BNData C R),
    ∃ (k' : Type u) (h₁ : Field k') (h₂ : Algebra K k') (h₃ : IsGalois K k')
      (h₄ : FiniteDimensional K k'), letI := h₁; letI := h₂; letI := h₃; letI := h₄
      ∃ (ι₀ : Type u) (h₅ : Fintype ι₀) (E₀ : ι₀ → FPt (Sym C R.g) k'), letI := h₅
        ∀ {F : Type u} [Field F] [Algebra K F] (ε : k' →ₐ[K] F) (c : Pic0 C F),
          ∃ i : ι₀, ∀ τ : k' ≃ₐ[K] k',
            InChart d (RPt.map (ε.comp τ.toAlgHom) (E₀ i)) c

/-- **COV′** from the named input `OrbitCover`. -/
theorem exists_galCharts_of_orbitCover [OrbitCover K] {C : Curve K} [Work.SpecLin.DivBase C]
    (R : RochData C) [Work.SpecLin.SymGeom C R.g] {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
    (d : BNData C R) : Nonempty (GalCharts C R P0) := by
  obtain ⟨k', h₁, h₂, h₃, h₄, ι₀, h₅, E₀, hcov⟩ :=
    OrbitCover.exists_orbit_cover (C := C) R d
  letI := h₁; letI := h₂; letI := h₃; letI := h₄; letI := h₅
  exact galCharts_of_orbit_cover R k' d E₀ hcov

end

end Work.Charts
