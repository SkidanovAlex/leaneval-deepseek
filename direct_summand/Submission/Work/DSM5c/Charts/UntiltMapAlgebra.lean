import Submission.Work.DSM5c.Charts

/-!
# DSM5c — `untiltOf.map` is `W`-linear: the presheaf compatibility for `D_S`

`Work.DSM5c.untiltOf` (`Submission/Work/DSM5c/Charts.lean`) carries two natural structures:

* a `W`-algebra structure `untiltOf.algebraMap` (characterised by `untiltOf.algebraMap_fontaineTheta`),
* functoriality in the tilt side `R`, `untiltOf.map` (characterised by `untiltOf.map_apply`).

For the chart presheaf `Dp = S ↦ untiltOf R_S φ_S` of the frozen node `DSMap.Mix2.area_M5c` the two
have to be **compatible**, i.e. `untiltOf.map` must be `W`-linear.  This file proves that:

`untiltOf.map φ φ' ψ h (untiltOf.algebraMap θ φ w) = untiltOf.algebraMap θ' φ' w`

for any `w : W`, where `θ` (resp. `θ'`) is the surjectivity of Fontaine's theta map used to build the
`W`-structure.  The proof is two characteristic computations plus `wittVector_map_comp` (the `𝕎`
composition law, also proved in `Charts.lean`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.DSM5c

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a

section Compat

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W]

/-- **`untiltOf.map` preserves the `W`-algebra structure.** -/
theorem untiltOf.map_algebraMap
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    {R R' : Type a} [CommRing R] [CommRing R']
    (φ : PreTilt W p →+* R) (φ' : PreTilt W p →+* R') (ψ : R →+* R') (h : ψ.comp φ = φ')
    (w : W) :
    untiltOf.map (p := p) (W := W) (R := R) (R' := R') φ φ' ψ h
        (untiltOf.algebraMap (p := p) (W := W) hθ φ w) =
      untiltOf.algebraMap (p := p) (W := W) hθ φ' w := by
  obtain ⟨x, rfl⟩ := hθ w
  rw [untiltOf.algebraMap_fontaineTheta, untiltOf.map_apply,
    untiltOf.algebraMap_fontaineTheta]
  congr 1
  rw [← RingHom.comp_apply, wittVector_map_comp (p := p) φ ψ, h]

end Compat

end Work.DSM5c
