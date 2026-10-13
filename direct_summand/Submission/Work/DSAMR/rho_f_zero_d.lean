import Mathlib
import Submission.Work.DSAMR.Defs

namespace Work.DSAMR

universe u

/-- **The composite `ρ⁰ ∘ d⁻¹` vanishes.**

In the frozen hypothesis of `DSMap.Mix2.modSplit_of_almostAcyc`, `ρ` is a chain map
`P → K.extend embeddingUpNat` into a complex which is strictly supported in degrees `≥ 0`, so
`K'.X (-1)` is a zero object.  The chain-map condition at `(-1, 0)` therefore gives
`ρ⁰ ((P.d (-1) 0) y) = (K'.d (-1) 0) (ρ⁻¹ y) = 0`.  This is what the AMR endgame needs in order to
apply the homotopy relation at `x := (P.d (-1) 0) y` and conclude `t ∘ d⁻¹ = 0`.

Hints.  Use `HomologicalComplex.Hom.comm'` at `(-1) 0` (the shape is `ComplexShape.up ℤ`, so
`Rel (-1) 0` holds), in the element form `ρ.f (i+1) (d^i x) = d^i (ρ.f i x)`; then
`HomologicalComplex.isZero_extend_X` with `ComplexShape.embeddingUpNat` at `i' = -1` (as
`embeddingUpNat.f n = (n : ℤ) ≥ 0` for `n : ℕ`) gives that `K'.X (-1)` is a zero object, and any
morphism out of a zero object is `0` (`Limits.IsZero.eq_zero_of_source`). -/
theorem rho_f_zero_d {A W : Type u} [CommRing A] [CommRing W] (ψ : A →+* W)
    (K : CochainComplex (ModuleCat.{u} W) ℕ) (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (ρ : P ⟶ ((ModuleCat.restrictScalars ψ).mapHomologicalComplex _).obj
      (K.extend ComplexShape.embeddingUpNat)) :
    ∀ y : P.X (-1),
      ((ρ.f 0) ((P.d (-1) 0).hom y) : (K.extend ComplexShape.embeddingUpNat).X 0) = 0 := by
  intro y
  -- `K' = K.extend embeddingUpNat` is strictly supported in degrees `≥ 0`, so `K'.X (-1)` is zero.
  have hzero : (K.extend ComplexShape.embeddingUpNat).d (-1) 0 = 0 :=
    (K.isZero_extend_X ComplexShape.embeddingUpNat (-1) (by
      intro n
      simp [ComplexShape.embeddingUpNat_f])).eq_zero_of_src _
  -- The chain-map condition at `(-1, 0)`.
  have hcomm := ρ.comm' (-1) 0 (ComplexShape.up_mk (-1) 0 (by norm_num))
  have h1 := congrArg (fun f => f.hom y) hcomm
  simp only [ModuleCat.comp_apply] at h1
  rw [← h1, CategoryTheory.Functor.mapHomologicalComplex_obj_d,
    ModuleCat.restrictScalars.map_apply, hzero]
  rfl

end Work.DSAMR
