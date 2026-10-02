import Mathlib
import Submission.Work.Transgression.Kunneth
import Submission.Work.Agree.kunnethInj
import Submission.Work.Transgression.Rank
import Submission.Work.Cohomology.sphereCohomologyTop

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The Künneth *span* statement for `S³ × S³`

This is the last step of `Work.Transgression.KunnethInj` (`Submission/Work/Transgression/Kunneth.lean`),
the `S³ × S³` input of the Mayer–Vietoris transgression: **a class in `H³(S³ × S³;ℤ)` killed by
both factor restrictions `sect₁^*`, `sect₂^*` is zero.**

The two *easy* halves are already in the workspace:

* `sect₁^* ∘ prj₁^* = id`, `sect₂^* ∘ prj₂^* = id` (`Work.Transgression.sect₁_comp_prj₁`,
  `sect₂_comp_prj₂`), so `prj₁^*`, `prj₂^*` are split *injections* and `sect₁^*`, `sect₂^*` are
  split *surjections* onto the two summands of the span;
* `sect₁^* ∘ prj₂^* = 0`, `sect₂^* ∘ prj₁^* = 0` (`Work.Agree.sect₁_prj₂_zero`,
  `sect₂_prj₁_zero` in `Submission/Work/Agree/kunnethInj.lean`), via the constant map
  `prj₂ ∘ sect₁ = const N`.

What is left is the *rank*: `H³(S³ × S³;ℤ)` is free of rank `2`
(`Work.Transgression.Sph33Rank`, proved in `Rank.lean` from
`Work.Cohomology.homology_prod_sphere`), so the split injections `prj₁^*`, `prj₂^*` already span.
Feeding an explicit pair `T : ℤ² → H³(S³ × S³;ℤ)`, `S : H³(S³ × S³;ℤ) → ℤ²` of mutually
inverse-to-the-left maps into `Work.Transgression.bijective_of_comp_eq_id_of_iso_two` does it.

## Contents

* `Work.Agree.span_eq_bot` — the abstract `ℤ`-module lemma: if `A' ∘ A = id`, `B' ∘ B = id`,
  `A' ∘ B = B' ∘ A = 0`, `N ≅ ℤ` and `M ≅ ℤ²`, then `x` with `A' x = B' x = 0` is `0`.
* `Work.Agree.cohH3S33` — `H³(S³ × S³;ℤ) ≅ ℤ²` in the `S33` model (transport of `Sph33Rank`
  along the homeomorphism `S³ × S³ ≅ ↥(S33)` given by `s3Homeo` and `sphereSet_eq'`).
* `Work.Agree.cohH3S3s` — `H³(S³;ℤ) ≅ ℤ` in the `S3s` model.
* `Work.Agree.kunnethSpan` — the requested statement.

The instance trap (see the note at the end of `kunnethInj.lean`) is avoided by building the two
maps `T' : ℤ × ℤ → M`, `S' : M → ℤ × ℤ` with `LinearMap.fst`/`LinearMap.snd`/`LinearMap.prod`
and the `ℤ × ℤ` form of `ℤ²` (`LinearEquiv.finTwoArrow`), never using `smulRight`.
-/

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-- The compatibility of the four structural maps of the two factor embeddings. -/
theorem span_eq_bot {M N : Type} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (A B : N →ₗ[ℤ] M) (A' B' : M →ₗ[ℤ] N)
    (hAA : A'.comp A = LinearMap.id) (hAB : A'.comp B = 0)
    (hBA : B'.comp A = 0) (hBB : B'.comp B = LinearMap.id)
    (eM : M ≃ₗ[ℤ] ℤ × ℤ) (eN : N ≃ₗ[ℤ] ℤ) :
    ∀ x : M, A' x = 0 → B' x = 0 → x = 0 := by
  let T' : ℤ × ℤ →ₗ[ℤ] M :=
    (A.comp eN.symm.toLinearMap).comp (LinearMap.fst ℤ ℤ ℤ) +
      (B.comp eN.symm.toLinearMap).comp (LinearMap.snd ℤ ℤ ℤ)
  let S' : M →ₗ[ℤ] ℤ × ℤ :=
    (eN.toLinearMap.comp A').prod (eN.toLinearMap.comp B')
  have hA : ∀ a b : ℤ, A' (A (eN.symm a) + B (eN.symm b)) = eN.symm a := by
    intro a b
    rw [map_add, ← LinearMap.comp_apply, hAA, ← LinearMap.comp_apply, hAB]
    simp
  have hB : ∀ a b : ℤ, B' (A (eN.symm a) + B (eN.symm b)) = eN.symm b := by
    intro a b
    rw [map_add, ← LinearMap.comp_apply, hBA, ← LinearMap.comp_apply, hBB]
    simp
  have hcomp : ∀ a b : ℤ, S' (T' (a, b)) = (a, b) := by
    intro a b
    have hT : T' (a, b) = A (eN.symm a) + B (eN.symm b) := rfl
    have hS : S' (A (eN.symm a) + B (eN.symm b))
        = (eN (A' (A (eN.symm a) + B (eN.symm b))),
           eN (B' (A (eN.symm a) + B (eN.symm b)))) := rfl
    rw [hT, hS, hA a b, hB a b, eN.apply_symm_apply, eN.apply_symm_apply]
  have hST' : S'.comp T' = LinearMap.id := by
    apply LinearMap.ext
    intro c
    obtain ⟨a, b⟩ := c
    exact hcomp a b
  let f2 := LinearEquiv.finTwoArrow ℤ ℤ
  let T : (Fin 2 → ℤ) →ₗ[ℤ] M := T'.comp f2.toLinearMap
  let S : M →ₗ[ℤ] (Fin 2 → ℤ) := f2.symm.toLinearMap.comp S'
  have hST : S.comp T = LinearMap.id := by
    apply LinearMap.ext
    intro c
    change f2.symm (S' (T' (f2 c))) = c
    rw [show S' (T' (f2 c)) = f2 c from hcomp (f2 c).1 (f2 c).2, f2.symm_apply_apply]
  have hbij : Function.Bijective T :=
    Work.Transgression.bijective_of_comp_eq_id_of_iso_two T S hST (eM.trans f2.symm)
  have hSinj : Function.Injective S := by
    intro a b hab
    obtain ⟨za, hza⟩ := hbij.surjective a
    obtain ⟨zb, hzb⟩ := hbij.surjective b
    have h1 : S (T za) = za := LinearMap.congr_fun hST za
    have h2 : S (T zb) = zb := LinearMap.congr_fun hST zb
    have hz : za = zb := by rw [← h1, ← h2, hza, hzb, hab]
    rw [← hza, ← hzb, hz]
  intro x hx1 hx2
  have hSx : S x = 0 := by
    have hSx' : S' x = 0 := by
      have h : S' x = (eN (A' x), eN (B' x)) := rfl
      rw [h, hx1, hx2]
      simp
    change f2.symm (S' x) = 0
    rw [hSx']
    simp
  exact hSinj (by rw [hSx, map_zero])

/-- **`H³(S³ × S³;ℤ) ≅ ℤ²`** in the model `S33 = S³ × S³` of the transgression, obtained by
transporting `Work.Transgression.Sph33Rank` (quaternionic model) along
`s3Homeo × s3Homeo`. -/
theorem cohH3S33 : Nonempty (↥(Work.Thom.Coh ℤ 3 ↥(Work.Transgression.S33)) ≃ₗ[ℤ] ℤ × ℤ) := by
  obtain ⟨e⟩ := Work.Transgression.Sph33Rank
  obtain ⟨e2⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    ((Work.CharacteristicClasses.s3Homeo.trans
        (Homeomorph.setCongr (Work.Cohomology.sphereSet_eq' 4))).prodCongr
      (Work.CharacteristicClasses.s3Homeo.trans
        (Homeomorph.setCongr (Work.Cohomology.sphereSet_eq' 4)))).toHomotopyEquiv 3
  exact ⟨e2.toLinearEquiv.symm.trans (e.trans (LinearEquiv.finTwoArrow ℤ ℤ))⟩

/-- **`H³(S³;ℤ) ≅ ℤ`** in the model `S3s = S³` of the transgression. -/
theorem cohH3S3s : Nonempty (↥(Work.Thom.Coh ℤ 3 ↥(Work.Transgression.S3s)) ≃ₗ[ℤ] ℤ) := by
  obtain ⟨e⟩ := Work.Cohomology.sphereCohomologyTop 3 (by norm_num)
  obtain ⟨e2⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    (Homeomorph.setCongr (Work.Cohomology.sphereSet_eq' 4)).toHomotopyEquiv 3
  exact ⟨e2.toLinearEquiv.symm.trans e.toLinearEquiv⟩

/-- **Künneth injectivity (the span statement) for `S³ × S³`**: the two factor restrictions
`sect₁^*`, `sect₂^*` jointly kill only the zero class of `H³(S³ × S³;ℤ)`.

Equivalently, `H³(S³ × S³;ℤ)` is the direct sum of the images of `prj₁^*` and `prj₂^*`; the rank
computation `H³(S³ × S³;ℤ) ≅ ℤ²` (`Work.Agree.cohH3S33`) together with the four pairings
`Work.Transgression.sect₁_comp_prj₁`, `sect₂_comp_prj₂` and `Work.Agree.sect₁_prj₂_zero`,
`sect₂_prj₁_zero` gives it. -/
theorem kunnethSpan (x : ↥(Work.Thom.Coh ℤ 3 ↥(Work.Transgression.S33)))
    (h1 : (Work.TangentClasses.HMap Work.Transgression.sect₁ 3).hom x = 0)
    (h2 : (Work.TangentClasses.HMap Work.Transgression.sect₂ 3).hom x = 0) : x = 0 := by
  obtain ⟨eM⟩ := cohH3S33
  obtain ⟨eN⟩ := cohH3S3s
  exact span_eq_bot (A := (Work.TangentClasses.HMap Work.Transgression.prj₁ 3).hom)
    (B := (Work.TangentClasses.HMap Work.Transgression.prj₂ 3).hom)
    (A' := (Work.TangentClasses.HMap Work.Transgression.sect₁ 3).hom)
    (B' := (Work.TangentClasses.HMap Work.Transgression.sect₂ 3).hom)
    Work.Transgression.sect₁_comp_prj₁ sect₁_prj₂_zero
    sect₂_prj₁_zero Work.Transgression.sect₂_comp_prj₂ eM eN x h1 h2

end

end Work.Agree
