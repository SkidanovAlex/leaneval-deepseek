import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.Pair
import Submission.Work.Thom.MixedCup
import Submission.Work.Cohomology.relCupHNatural
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Sph3Disc.pairDelta_mixedCup_general

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-!
# The suspension step of the Thom isomorphism for trivial bundles

This module proves the abstract algebraic-topological input of the induction that constructs the
Thom class of the trivial bundle of rank `n` over an arbitrary base from the rank-`(n-1)` one.

The situation is a chain of subsets `A₁ ⊆ A ⊆ X`.  Write

* `ρ : H^*(X) → H^*(A)` for the restriction (the pullback along `A ↪ X`), and
* `res : H^*(A) → H^*(A₁)` for the restriction to the smaller subspace.

**Hypotheses.** `ρ` is injective and the composite `res ∘ ρ : H^*(X) → H^*(A₁)` is bijective.  The
geometric situation is: `X` is the disc bundle of a trivial bundle, `A` its sphere bundle and `A₁`
a subspace of the sphere bundle which is a deformation retract of `X`.

**The two conclusions.**

* `suspensionStep_bijective`: the composite `δ ∘ relToAbs : H^n(A,A₁) → H^{n+1}(X,A)` of the
  forgetful map of the pair `(A,A₁)` with the connecting homomorphism `δ` of the pair `(X,A)` is
  bijective — the *suspension isomorphism* relating the Thom pair of rank `n` to the pair
  `(A,A₁)`.
* `suspensionStep_cup`: it satisfies the Leibniz rule with respect to the module structure over the
  absolute cohomology of `X`, which is what makes the *Thom map* (and not merely an abstract
  isomorphism of groups) pass through the suspension.

The point of the hypotheses is the decomposition `H^*(A) = im ρ ⊕ ker res`: the connecting
homomorphism `δ` is surjective with kernel `im ρ`, so it restricts to an isomorphism
`ker res ≅ H^{∗+1}(X,A)`, while `relToAbs : H^n(A,A₁) ≅ ker res`.
-/

namespace Work.Thom

open CategoryTheory

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The subset of the subspace `A` cut out by the subset `A₁ ⊆ X`: this is the subset `A₁` in the
form in which the relative cohomology of the pair of subtypes is phrased. -/
def subSubset (A₁ A : Set X) : Set A := {q | (q : X) ∈ A₁}

@[simp] theorem mem_subSubset {A₁ A : Set X} (q : A) : q ∈ subSubset A₁ A ↔ (q : X) ∈ A₁ :=
  Iff.rfl

variable (A₁ A : Set X) (hA₁A : A₁ ⊆ A)

/-- **The suspension isomorphism.**  For `n ≥ 0`, the composite
`δ ∘ relToAbs : H^{n+1}(A,A₁) → H^{n+2}(X,A)` is bijective. -/
theorem suspensionStep_bijective (n : ℕ)
    (hρ : ∀ m, Function.Injective (CohMap (subtypeMap A) ℤ m).hom)
    (hres : ∀ m, Function.Bijective
      (((CohMap (subtypeMap (subSubset A₁ A)) ℤ m).hom).comp
        ((CohMap (subtypeMap A) ℤ m).hom))) :
    Function.Bijective
      (((pairδC A (n + 1)).hom).comp ((relToAbs ℤ (subSubset A₁ A) (n + 1)).hom)) := by
  classical
  set ρ : ∀ m, Coh ℤ m X ⟶ Coh ℤ m A := fun m => CohMap (subtypeMap A) ℤ m with hρdef
  set res : ∀ m, Coh ℤ m A ⟶ Coh ℤ m (subSubset A₁ A) :=
    fun m => CohMap (subtypeMap (subSubset A₁ A)) ℤ m with hresdef
  have hres_surj : ∀ m, Function.Surjective (res m).hom := by
    intro m y
    obtain ⟨x, hx⟩ := (hres m).2 y
    exact ⟨(ρ m).hom x, hx⟩
  -- `im ρ` meets `ker res` trivially
  have hdisj : ∀ m, ∀ y, y ∈ (ρ m).hom.range → y ∈ (res m).hom.ker → y = 0 := by
    intro m y hy hyk
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    have h0 : (res m).hom ((ρ m).hom x) = 0 := hyk
    have hinj : Function.Injective (((res m).hom).comp ((ρ m).hom)) := (hres m).1
    have hx0 : x = 0 := hinj (by simp only [LinearMap.comp_apply, h0, map_zero])
    rw [hx0, map_zero]
  -- `H^m(A) = im ρ + ker res` in every degree
  have hsum : ∀ m, (ρ m).hom.range ⊔ (res m).hom.ker = ⊤ := by
    intro m
    rw [Submodule.eq_top_iff']
    intro y
    obtain ⟨x, hx⟩ : ∃ x, (res m).hom ((ρ m).hom x) = (res m).hom y :=
      (hres m).2 ((res m).hom y)
    rw [Submodule.mem_sup]
    refine ⟨(ρ m).hom x, LinearMap.mem_range.mpr ⟨x, rfl⟩, y - (ρ m).hom x, ?_, by abel⟩
    rw [LinearMap.mem_ker, map_sub, hx, sub_self]
  -- the connecting homomorphism of `(X,A)` is surjective with kernel `im ρ`
  have hδ_ker : (pairδC A (n + 1)).hom.ker = (ρ (n + 1)).hom.range := by
    have h := ShortComplex.Exact.moduleCat_range_eq_ker (pairExact₃ A (n + 1))
    rw [← h]
  have hδ_surj : Function.Surjective (pairδC A (n + 1)).hom := by
    have hrel0 : (relToAbs ℤ A (n + 2)).hom = 0 := by
      refine LinearMap.range_eq_bot.mp ?_
      have h := ShortComplex.Exact.moduleCat_range_eq_ker (pairExact₂ A (n + 2))
      rw [h]
      exact LinearMap.ker_eq_bot.mpr (hρ (n + 2))
    have h := ShortComplex.Exact.moduleCat_range_eq_ker (pairExact₁ A (n + 1))
    rw [hrel0, LinearMap.ker_zero, LinearMap.range_eq_top] at h
    exact h
  -- `relToAbs` for the pair `(A,A₁)` is injective with image `ker res`
  have hrel_range : (relToAbs ℤ (subSubset A₁ A) (n + 1)).hom.range = (res (n + 1)).hom.ker := by
    have h := ShortComplex.Exact.moduleCat_range_eq_ker (pairExact₂ (subSubset A₁ A) (n + 1))
    rw [h]
  have hrel_inj : Function.Injective (relToAbs ℤ (subSubset A₁ A) (n + 1)).hom := by
    have hzero : (pairδC (subSubset A₁ A) n).hom = 0 := by
      rw [← LinearMap.ker_eq_top]
      have h := ShortComplex.Exact.moduleCat_range_eq_ker (pairExact₃ (subSubset A₁ A) n)
      rw [← h, LinearMap.range_eq_top]
      exact hres_surj n
    have h := ShortComplex.Exact.moduleCat_range_eq_ker (pairExact₁ (subSubset A₁ A) n)
    rw [← LinearMap.ker_eq_bot, ← h, hzero, LinearMap.range_zero]
  constructor
  · rintro z z' hzz'
    have hzz'' : (pairδC A (n + 1)).hom ((relToAbs ℤ (subSubset A₁ A) (n + 1)).hom z)
        = (pairδC A (n + 1)).hom ((relToAbs ℤ (subSubset A₁ A) (n + 1)).hom z') := hzz'
    have hk : (relToAbs ℤ (subSubset A₁ A) (n + 1)).hom z
        - (relToAbs ℤ (subSubset A₁ A) (n + 1)).hom z' ∈ (pairδC A (n + 1)).hom.ker := by
      rw [LinearMap.mem_ker, map_sub, hzz'', sub_self]
    rw [hδ_ker] at hk
    have hk2 : (relToAbs ℤ (subSubset A₁ A) (n + 1)).hom z
        - (relToAbs ℤ (subSubset A₁ A) (n + 1)).hom z' ∈ (res (n + 1)).hom.ker := by
      rw [← hrel_range]
      exact Submodule.sub_mem _ (LinearMap.mem_range.mpr ⟨z, rfl⟩)
        (LinearMap.mem_range.mpr ⟨z', rfl⟩)
    exact hrel_inj (sub_eq_zero.mp (hdisj (n + 1) _ hk hk2))
  · intro w
    have hw : w ∈ (pairδC A (n + 1)).hom.range := LinearMap.mem_range.mpr (hδ_surj w)
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hw
    have hu' : u ∈ (ρ (n + 1)).hom.range ⊔ (res (n + 1)).hom.ker := by
      rw [hsum]; exact Submodule.mem_top
    obtain ⟨p, hp, v, hv, hpv⟩ := Submodule.mem_sup.mp hu'
    have hδp : (pairδC A (n + 1)).hom p = 0 := by
      have : p ∈ (pairδC A (n + 1)).hom.ker := by rw [hδ_ker]; exact hp
      exact this
    have hv' : v ∈ (relToAbs ℤ (subSubset A₁ A) (n + 1)).hom.range := by
      rw [hrel_range]; exact hv
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hv'
    refine ⟨z, ?_⟩
    have hv_eq : v = u - p := by rw [← hpv]; abel
    rw [LinearMap.comp_apply, hz, hv_eq, map_sub, hδp, sub_zero, hu]

/-- **The suspension isomorphism is compatible with the module structure**: for `x ∈ H^m(X)` and
`z ∈ H^{n+1}(A,A₁)`,
`(δ ∘ relToAbs)(x|_A ⌣ z) = (-1)^m · x ⌣ (δ ∘ relToAbs)(z)`. -/
theorem suspensionStep_cup (m n : ℕ) (x : Coh ℤ m X)
    (z : RelCoh ℤ (n + 1) A (subSubset A₁ A)) :
    ((pairδC A (m + (n + 1))).hom)
        (((relToAbs ℤ (subSubset A₁ A) (m + (n + 1))).hom)
          (((mixedCupC ℤ (subSubset A₁ A) m (n + 1))
            ((CohMap (subtypeMap A) ℤ m).hom x)) z))
      = ((-1 : ℤ) ^ m) •
        (((mixedCupC ℤ A m (n + 2)) x)
          (((pairδC A (n + 1)).hom) (((relToAbs ℤ (subSubset A₁ A) (n + 1)).hom) z))) := by
  have h1 := congrArg (fun w => ((pairδC A (m + (n + 1))).hom) w)
    (mixedCup_relToAbs (X := A) (subSubset A₁ A) m (n + 1) ((CohMap (subtypeMap A) ℤ m).hom x) z)
  have h2 := Work.Sph3Disc.pairDelta_mixedCup_general (TopCat.of X) A m (n + 1) x
    ((relToAbs ℤ (subSubset A₁ A) (n + 1)).hom z)
  rw [h1]
  exact h2

end

end Work.Thom
