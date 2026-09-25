import Mathlib
import Submission.Work.CFTLib.fiveTerm_setup

/-!
# The transgression identity of the five-term inflation–restriction sequence

Let `π : G' →* G` be a surjective homomorphism of groups, `N = ker π`, and let
`t ∈ Work.CFTLib.invCharSubmodule p N` be a `G'`-invariant additive character of `N`
(the model of `H¹(N,𝔽_p)^{G'}`).  Fix a set-theoretic section `σ = sectionOf π hπ` of `π`,
put `η g = σ(π g)⁻¹ * g ∈ N`, and let `factor π hπ x y = σ x * σ y * σ(x y)⁻¹ ∈ N`.

The transgression `Work.CFTLib.candFun π hπ t` is the `2`-cochain of `G` given by
`(x,y) ↦ -t(factor π hπ x y)`, and `Work.CFTLib.auxFun π hπ t` is the `1`-cochain of `G'`
given by `g ↦ t(η g)`.  The content of this file is the *transgression identity*

`precomp₂ π (candFun π hπ t) = d₁₂ (auxFun π hπ t)`,

i.e. for all `x y : G'`,

`-t(factor π hπ (π x) (π y)) = auxFun y - auxFun (x * y) + auxFun x`,

which exhibits the inflation of the transgression as a coboundary.  It is the rearrangement of
the cocycle identity `auxFun (x * y) = t(factor (π x) (π y)) + auxFun x + auxFun y`
(proved independently as `Work.CFTLib.fiveTerm_auxFun_mul`).

The mathematical core is the group identity in `N`
`η(x * y) = (σ(xy)⁻¹ · factor(πx,πy) · σ(xy)) * (σ(πy)⁻¹ · η x · σ(πy)) * η y`,
which is purely group-theoretic, combined with the conjugation-invariance of `t` (the defining
property of `invCharSubmodule`) and its additivity.
-/

open CategoryTheory Representation groupCohomology
open scoped Classical

namespace Work.CFTLib

noncomputable section

variable {p : ℕ} {G G' : Type} [Group G] [Group G']

/-- The canonical element `σ(π g)⁻¹ * g` of `ker π`, where `σ = sectionOf π hπ`. -/
private def transSecKer (π : G' →* G) (hπ : Function.Surjective π) (g : G') : π.ker :=
  ⟨(sectionOf π hπ (π g))⁻¹ * g, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, sectionOf_spec]
    simp⟩

/-- `auxFun` is `t` evaluated at the canonical element `transSecKer`. -/
private lemma transAuxFun_eq (π : G' →* G) (hπ : Function.Surjective π)
    (t : invCharSubmodule p π.ker) (g : G') :
    auxFun π hπ t g = t.1 (Additive.ofMul (transSecKer π hπ g)) := rfl

/-- The coercion of `transSecKer` to `G'`. -/
private lemma transSecKer_coe (π : G' →* G) (hπ : Function.Surjective π) (g : G') :
    (transSecKer π hπ g : G') = (sectionOf π hπ (π g))⁻¹ * g := rfl

/-- `g⁻¹ * n * g` again lies in the normal subgroup `ker π`. -/
private lemma transConj_mem (π : G' →* G) (g : G') (n : π.ker) :
    g⁻¹ * (n : G') * g ∈ π.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, n.2]
  group

/-- An invariant character is unchanged by conjugation (the defining property of
`invCharSubmodule`). -/
private lemma transTau_conj (π : G' →* G)
    (t : invCharSubmodule p π.ker) (g : G') (n : π.ker) :
    t.1 (Additive.ofMul (⟨g⁻¹ * (n : G') * g, transConj_mem π g n⟩ : π.ker))
      = t.1 (Additive.ofMul n) := by
  simpa using t.2 g n

/-- Additivity of an invariant character on a product of two elements. -/
private lemma transTau_mul (π : G' →* G) (t : invCharSubmodule p π.ker) (a b : π.ker) :
    t.1 (Additive.ofMul (a * b)) = t.1 (Additive.ofMul a) + t.1 (Additive.ofMul b) := by
  rw [show Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b from rfl, map_add]

/-- **The key group identity.**  In `N = ker π`,
`η(x * y) = (σ(xy)⁻¹ · factor(πx,πy) · σ(xy)) * (σ(πy)⁻¹ · η x · σ(πy)) * η y`,
where `η g = σ(π g)⁻¹ * g` and `factor` is the usual `2`-cocycle of a section. -/
private theorem transSecKer_mul (π : G' →* G) (hπ : Function.Surjective π) (x y : G') :
    transSecKer π hπ (x * y) =
      (⟨(sectionOf π hπ (π (x * y)))⁻¹ * (factor π hπ (π x) (π y) : G')
          * sectionOf π hπ (π (x * y)),
        transConj_mem π (sectionOf π hπ (π (x * y))) (factor π hπ (π x) (π y))⟩ : π.ker) *
      (⟨(sectionOf π hπ (π y))⁻¹ * (transSecKer π hπ x : G') * sectionOf π hπ (π y),
        transConj_mem π (sectionOf π hπ (π y)) (transSecKer π hπ x)⟩ : π.ker) *
      transSecKer π hπ y := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, transSecKer_coe, factor_coe, map_mul]
  group

end

/-- **The transgression identity.**  The inflation `precomp₂ π` of the transgression
`candFun π hπ t` is the coboundary `d₁₂` of the `1`-cochain `auxFun π hπ t`. -/
theorem fiveTerm_precomp_candFun_eq {p : ℕ} [Fact p.Prime] {G G' : Type} [Group G] [Group G']
    (π : G' →* G) (hπ : Function.Surjective π) (t : Work.CFTLib.invCharSubmodule p π.ker) :
    Work.CFTLib.precomp₂ π (Work.CFTLib.candFun π hπ t) =
      Work.CFTLib.d12 p G' (Work.CFTLib.auxFun π hπ t) := by
  funext xy
  obtain ⟨x, y⟩ := xy
  rw [precomp₂_apply, candFun_apply, d12, groupCohomology.d₁₂_hom_apply]
  simp only [Representation.trivial_apply]
  simp only [transAuxFun_eq]
  have hT : t.1 (Additive.ofMul (transSecKer π hπ (x * y))) =
      t.1 (Additive.ofMul (factor π hπ (π x) (π y))) +
        t.1 (Additive.ofMul (transSecKer π hπ x)) +
        t.1 (Additive.ofMul (transSecKer π hπ y)) := by
    rw [transSecKer_mul]
    rw [transTau_mul, transTau_mul]
    rw [transTau_conj, transTau_conj]
  rw [hT]
  abel

end Work.CFTLib
