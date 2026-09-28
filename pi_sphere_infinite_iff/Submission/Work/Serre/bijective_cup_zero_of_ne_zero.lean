import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.Serre.ratCoh_ratH_iso_rat
import Submission.Work.Serre.cohMap_oneH
import Submission.Work.StemsB.Rat.collarSuspClassAuxRat

/-!
# Cupping with a non-zero relative class is bijective in degree `0`

`Work.Serre.cyl p` is the mapping cylinder of `p : C(E,B)` and `cylIncl p` its bottom copy; the
pair `(cyl p, range (cylIncl p))` is the geometric model of the "fibre pair" of `p`.  The mixed
cup product `mixedCupC ℚ A 0 (r+1)` composed with the pullback along the retraction
`cylRetract p : cyl p → B` is the linear map

  `H⁰(B;ℚ) --(cylRetract p)^*--> H⁰(cyl p;ℚ) -- ⌣ U --> H^{r+1}(cyl p, range (cylIncl p);ℚ)`.

If the target is a line (a `ThomCylAt`-type requirement, here the hypothesis `hlin`) and `U ≠ 0`,
this map is bijective:  a non-zero linear map between `ℚ`-lines is an isomorphism, and the map is
non-zero because it sends the unit class `1 = (cylRetract p)^* 1` to `U` itself
(`mixedCupC_oneH_zeroQ`).  The source is a line because `B` is path connected — it is the
continuous image of the path connected `cyl p` under the surjective retraction `cylRetract p`.

## Main results

* `Work.Serre.bijective_of_linearEquiv_rat` — a non-zero `ℚ`-linear map between `ℚ`-lines is
  bijective (a self-contained replacement for `isIso_ofHom_of_linearEquiv_rat`, in the `Function`
  form needed here).
* `Work.Serre.bijective_cup_zero_of_ne_zero` — the requested statement.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **A non-zero `ℚ`-linear map between two `ℚ`-lines is bijective.**  After transporting along
`e₁` and `e₂` we may assume `φ : ℚ →ₗ[ℚ] ℚ`; every such map is multiplication by `φ 1`, which is
non-zero because `φ ≠ 0`, and multiplication by a non-zero rational is bijective. -/
theorem bijective_of_linearEquiv_rat {V W : Type} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (e₁ : V ≃ₗ[ℚ] ℚ) (e₂ : W ≃ₗ[ℚ] ℚ) (φ : V →ₗ[ℚ] W)
    (hφ : φ ≠ 0) : Function.Bijective φ := by
  set ψ : ℚ →ₗ[ℚ] ℚ := e₂.toLinearMap.comp (φ.comp e₁.symm.toLinearMap) with hψ
  have hform : ∀ x : ℚ, ψ x = x * ψ 1 := fun x => by
    have key : ψ (x • (1 : ℚ)) = x • ψ 1 := map_smul ψ x 1
    simpa using key
  have hψ1 : ψ 1 ≠ 0 := by
    intro h1
    refine hφ (LinearMap.ext fun v => ?_)
    have h2 : ψ (e₁ v) = e₂ (φ v) := by
      show e₂ (φ (e₁.symm (e₁ v))) = e₂ (φ v)
      rw [e₁.symm_apply_apply]
    have h3 : ψ (e₁ v) = 0 := by rw [hform, h1, mul_zero]
    rw [h2] at h3
    exact e₂.injective (by simpa using h3)
  have hψbij : Function.Bijective ψ := by
    constructor
    · intro x y hxy
      have h4 : x * ψ 1 = y * ψ 1 := by rw [← hform x, ← hform y, hxy]
      exact mul_right_cancel₀ hψ1 h4
    · intro w
      refine ⟨w * (ψ 1)⁻¹, ?_⟩
      rw [hform, mul_assoc, inv_mul_cancel₀ hψ1, mul_one]
  constructor
  · intro x y hxy
    have h5 : ψ (e₁ x) = ψ (e₁ y) := by
      have hx : ψ (e₁ x) = e₂ (φ x) := by
        show e₂ (φ (e₁.symm (e₁ x))) = e₂ (φ x)
        rw [e₁.symm_apply_apply]
      have hy : ψ (e₁ y) = e₂ (φ y) := by
        show e₂ (φ (e₁.symm (e₁ y))) = e₂ (φ y)
        rw [e₁.symm_apply_apply]
      rw [hx, hy, hxy]
    exact e₁.injective (hψbij.1 h5)
  · intro w
    obtain ⟨q, hq⟩ := hψbij.2 (e₂ w)
    refine ⟨e₁.symm q, ?_⟩
    apply e₂.injective
    have h6 : e₂ (φ (e₁.symm q)) = ψ q := rfl
    rw [h6]
    exact hq

/-- **Cupping with a non-zero relative class is bijective.**  With `U ∈ H^{r+1}(cyl p, A;ℚ)`
non-zero, `A = range (cylIncl p)`, the map
`H⁰(B;ℚ) → H^{r+1}(cyl p, A;ℚ)`, `x ↦ (cylRetract p)^* x ⌣ U` is bijective, provided the target is
a line. -/
theorem bijective_cup_zero_of_ne_zero (r : ℕ)
    {B : Type} [TopologicalSpace B] {E : Type} [TopologicalSpace E] (p : C(E, B))
    [PathConnectedSpace (Work.Serre.cyl p)]
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl p) (Set.range (Work.Serre.cylIncl p)))
    (hU : U ≠ 0)
    (hlin : Nonempty (Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl p)
      (Set.range (Work.Serre.cylIncl p)) ≅ ModuleCat.of ℚ ℚ)) :
    Function.Bijective (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl p)) 0 (r + 1)).flip U) ∘ₗ
      (Work.Thom.CohMap (Work.Serre.cylRetract p) ℚ 0).hom) := by
  classical
  -- `B` is path connected: it is the continuous image of the path connected `cyl p` under the
  -- surjective retraction `cylRetract p`.
  have hsurj : Function.Surjective (Work.Serre.cylRetract p) :=
    fun x => ⟨Work.Serre.cylInr p x, rfl⟩
  haveI hBpc : PathConnectedSpace B :=
    hsurj.pathConnectedSpace (Work.Serre.cylRetract p).continuous
  -- the target in the degree in which the map lands is a line
  have hline0 : Nonempty (Work.Thom.RelCoh ℚ (0 + (r + 1)) (Work.Serre.cyl p)
      (Set.range (Work.Serre.cylIncl p)) ≅ ModuleCat.of ℚ ℚ) := by
    obtain ⟨e⟩ := hlin
    exact ⟨eqToIso (congrArg (fun n => Work.Thom.RelCoh ℚ n (Work.Serre.cyl p)
      (Set.range (Work.Serre.cylIncl p))) (Nat.zero_add (r + 1))) ≪≫ e⟩
  -- the source `H⁰(B;ℚ)` is a line
  have hsource : Nonempty (Work.Thom.Coh ℚ 0 B ≅ ModuleCat.of ℚ ℚ) :=
    (Work.Serre.ratCoh_ratH_iso_rat (TopCat.of B) 0).mpr
      (Work.Serre.ratH_zero_of_pathConnected B)
  -- the map is non-zero: it sends the unit class to `U ≠ 0`
  have hf : (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl p)) 0 (r + 1)).flip U) ∘ₗ
      (Work.Thom.CohMap (Work.Serre.cylRetract p) ℚ 0).hom) ≠ 0 := by
    intro h0
    have cast_ne : ∀ {a b : ℕ} (h : a = b) (x : Work.Thom.RelCoh ℚ a (Work.Serre.cyl p)
        (Set.range (Work.Serre.cylIncl p))), x ≠ 0 → (h ▸ x) ≠ 0 := by
      intro a b h x hx
      cases h
      exact hx
    have hh0 : ((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl p)) 0 (r + 1)).flip U)
        ((Work.Thom.CohMap (Work.Serre.cylRetract p) ℚ 0).hom
          (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of B)))) = 0 :=
      LinearMap.congr_fun h0 _
    rw [Work.Serre.cohMap_oneH ℚ (Work.Serre.cylRetract p)] at hh0
    have hh1 : (Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl p)) 0 (r + 1))
        (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of (Work.Serre.cyl p)))) U = 0 := hh0
    rw [Work.StemsB.Rat.mixedCupC_oneH_zeroQ (Set.range (Work.Serre.cylIncl p)) (r + 1) U]
      at hh1
    exact cast_ne (Nat.zero_add (r + 1)).symm U hU hh1
  exact bijective_of_linearEquiv_rat (Classical.choice hsource).toLinearEquiv
    (Classical.choice hline0).toLinearEquiv _ hf

end

end Work.Serre
