import Mathlib.RepresentationTheory.Coinduced
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.HassePrinciple.OrbitCoindSection
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.HassePrinciple

open NK.GlobalCFT

/-- **The orbit component of the idèle localisation (free side): Shapiro's map splits.**

Let `Γ = Gal(L/K)`, let `w : Place L`, let `Γ_w = MulAction.stabilizer (L ≃ₐ[K] L) w` be the
decomposition group of `w`, and let `O = placeOrbit K L w` be the `Γ`-orbit of `w`.

`NK.HassePrinciple.orbitCoindMapA K L w : A_O ⟶ Coind_{Γ_w}^{Γ} L_wˣ` is the `Γ`-map from the
idèles supported on `O` (an idèle is supported on `O` when it is `1` outside `O`) to the coinduced
module, defined as the adjunction transpose of "evaluate at `w`".  On elements it is
`t(x)(γ) = (γ • x) w`.

Mathematically `t` is the Shapiro isomorphism `∏_{v ∈ O} L_vˣ ≅ Coind_{Γ_w}^{Γ} L_wˣ`, so the
claim below says in particular that `t` is a split monomorphism, i.e. has a left inverse `s` (a
`Γ`-map with `s ∘ t = id`).

Suggested construction of `s`: for `f` in the coinduced module and `v ∈ O`, choose
`γ : Γ` with `γ • v = w` (such `γ` exists because `v` lies in the orbit of `w`; use
`Classical.choose` on `∃ γ, γ • v = w`), and set `(s f) v := actVal γ⁻¹ w (f γ)` — transported
along `γ⁻¹ • w = v` — and `(s f) v := 1` for `v ∉ O`.  The consistency of the choice of `γ` is
exactly the equivariance condition `f (σ * γ) = σ • f γ` (`σ ∈ Γ_w`) of the coinduced module, and
the retraction identity reduces, at each `γ`, to
`(γ • s f) w = actVal γ (γ⁻¹ • w) ((s f) (γ⁻¹ • w)) = f γ`. -/
theorem orbitCoindMapA_split {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : NK.GlobalCFT.Place L) :
    ∃ s : Rep.coind (MulAction.stabilizer (L ≃ₐ[K] L) w).subtype
            (NK.HassePrinciple.localUnitsRep K L w) ⟶
          NK.HassePrinciple.supportedRep K L (NK.HassePrinciple.orbitStable K L w),
      CategoryTheory.CategoryStruct.comp (NK.HassePrinciple.orbitCoindMapA K L w) s =
        CategoryTheory.CategoryStruct.id
          (NK.HassePrinciple.supportedRep K L (NK.HassePrinciple.orbitStable K L w)) :=
  ⟨NK.HassePrinciple.coindSectionHom w,
    NK.HassePrinciple.orbitCoindMapA_comp_coindSectionHom w⟩

end NK.HassePrinciple
