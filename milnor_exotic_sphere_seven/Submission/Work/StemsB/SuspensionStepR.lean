import Mathlib
import Submission.Work.Thom.SuspensionStep
import Submission.Work.StemsB.ThomRatShim
import Submission.Work.StemsB.pairDelta_mixedCup_general_R

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The suspension step of the model Thom induction, over an arbitrary coefficient ring

`Submission/Work/Thom/SuspensionStep.lean` proves, over `ℤ`, the abstract algebraic-topological
input of the induction that constructs the Thom class of the trivial bundle of rank `n` from the
rank-`(n-1)` one:

* `suspensionStep_bijective` — under the hypotheses "the restriction `H^*(X) → H^*(A)` is injective"
  and "the composite `H^*(X) → H^*(A) → H^*(A₁)` is bijective", the composite
  `δ ∘ relToAbs : H^n(A,A₁) → H^{n+1}(X,A)` of the forgetful map of the pair `(A,A₁)` with the
  connecting homomorphism of `(X,A)` is bijective;
* `suspensionStep_cup` — it satisfies the Leibniz rule with respect to the module structure over
  the absolute cohomology of `X`.

Both proofs use only coefficient-generic ingredients, so this file is the same proof over an
arbitrary commutative ring `R` — which is what the rational (`ℚ`) model Thom class needs.
-/

namespace Work.StemsB

open CategoryTheory

noncomputable section

variable {X : Type} [TopologicalSpace X]

variable (R : Type) [CommRing R]

variable (A₁ A : Set X) (hA₁A : A₁ ⊆ A)

/-- **The suspension isomorphism, over `R`.**  For `n ≥ 0`, the composite
`δ ∘ relToAbs : H^{n+1}(A,A₁) → H^{n+2}(X,A)` is bijective. -/
theorem suspensionStep_bijective_R (n : ℕ)
    (hρ : ∀ m, Function.Injective (Work.Thom.CohMap (Work.Thom.subtypeMap A) R m).hom)
    (hres : ∀ m, Function.Bijective
      (((Work.Thom.CohMap (Work.Thom.subtypeMap (Work.Thom.subSubset A₁ A)) R m).hom).comp
        ((Work.Thom.CohMap (Work.Thom.subtypeMap A) R m).hom))) :
    Function.Bijective
      (((pairδCR R A (n + 1)).hom).comp
        ((Work.Thom.relToAbs R (Work.Thom.subSubset A₁ A) (n + 1)).hom)) := by
  classical
  set ρ : ∀ m, Work.Thom.Coh R m X ⟶ Work.Thom.Coh R m A :=
    fun m => Work.Thom.CohMap (Work.Thom.subtypeMap A) R m with hρdef
  set res : ∀ m, Work.Thom.Coh R m A ⟶ Work.Thom.Coh R m (Work.Thom.subSubset A₁ A) :=
    fun m => Work.Thom.CohMap (Work.Thom.subtypeMap (Work.Thom.subSubset A₁ A)) R m with hresdef
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
  have hδ_ker : (pairδCR R A (n + 1)).hom.ker = (ρ (n + 1)).hom.range := by
    exact pairKer₃R R A (n + 1)
  have hδ_surj : Function.Surjective (pairδCR R A (n + 1)).hom := by
    have hrel0 : (Work.Thom.relToAbs R A (n + 2)).hom = 0 := by
      refine LinearMap.range_eq_bot.mp ?_
      rw [pairKer₂R R A (n + 2)]
      exact LinearMap.ker_eq_bot.mpr (hρ (n + 2))
    have h := pairKer₁R R A (n + 1)
    rw [hrel0, LinearMap.ker_zero, LinearMap.range_eq_top] at h
    exact h
  -- `relToAbs` for the pair `(A,A₁)` is injective with image `ker res`
  have hrel_range : (Work.Thom.relToAbs R (Work.Thom.subSubset A₁ A) (n + 1)).hom.range
      = (res (n + 1)).hom.ker := by
    exact pairKer₂R R (Work.Thom.subSubset A₁ A) (n + 1)
  have hrel_inj : Function.Injective
      (Work.Thom.relToAbs R (Work.Thom.subSubset A₁ A) (n + 1)).hom := by
    have hzero : (pairδCR R (Work.Thom.subSubset A₁ A) n).hom = 0 := by
      rw [← LinearMap.ker_eq_top]
      rw [pairKer₃R R (Work.Thom.subSubset A₁ A) n, LinearMap.range_eq_top]
      exact hres_surj n
    have h := pairKer₁R R (Work.Thom.subSubset A₁ A) n
    rw [← LinearMap.ker_eq_bot, ← h, hzero, LinearMap.range_zero]
  constructor
  · rintro z z' hzz'
    have hzz'' : (pairδCR R A (n + 1)).hom
          ((Work.Thom.relToAbs R (Work.Thom.subSubset A₁ A) (n + 1)).hom z)
        = (pairδCR R A (n + 1)).hom
          ((Work.Thom.relToAbs R (Work.Thom.subSubset A₁ A) (n + 1)).hom z') := hzz'
    have hk : (Work.Thom.relToAbs R (Work.Thom.subSubset A₁ A) (n + 1)).hom z
        - (Work.Thom.relToAbs R (Work.Thom.subSubset A₁ A) (n + 1)).hom z'
          ∈ (pairδCR R A (n + 1)).hom.ker := by
      rw [LinearMap.mem_ker, map_sub, hzz'', sub_self]
    rw [hδ_ker] at hk
    have hk2 : (Work.Thom.relToAbs R (Work.Thom.subSubset A₁ A) (n + 1)).hom z
        - (Work.Thom.relToAbs R (Work.Thom.subSubset A₁ A) (n + 1)).hom z'
          ∈ (res (n + 1)).hom.ker := by
      rw [← hrel_range]
      exact Submodule.sub_mem _ (LinearMap.mem_range.mpr ⟨z, rfl⟩)
        (LinearMap.mem_range.mpr ⟨z', rfl⟩)
    exact hrel_inj (sub_eq_zero.mp (hdisj (n + 1) _ hk hk2))
  · intro w
    have hw : w ∈ (pairδCR R A (n + 1)).hom.range := LinearMap.mem_range.mpr (hδ_surj w)
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hw
    have hu' : u ∈ (ρ (n + 1)).hom.range ⊔ (res (n + 1)).hom.ker := by
      rw [hsum]; exact Submodule.mem_top
    obtain ⟨p, hp, v, hv, hpv⟩ := Submodule.mem_sup.mp hu'
    have hδp : (pairδCR R A (n + 1)).hom p = 0 := by
      have : p ∈ (pairδCR R A (n + 1)).hom.ker := by rw [hδ_ker]; exact hp
      exact this
    have hv' : v ∈ (Work.Thom.relToAbs R (Work.Thom.subSubset A₁ A) (n + 1)).hom.range := by
      rw [hrel_range]; exact hv
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hv'
    refine ⟨z, ?_⟩
    have hv_eq : v = u - p := by rw [← hpv]; abel
    rw [LinearMap.comp_apply, hz, hv_eq, map_sub, hδp, sub_zero, hu]

/-- **The suspension isomorphism is compatible with the module structure**, over `R`: for
`x ∈ H^m(X)` and `z ∈ H^{n+1}(A,A₁)`,
`(δ ∘ relToAbs)(x|_A ⌣ z) = (-1)^m · x ⌣ (δ ∘ relToAbs)(z)`. -/
theorem suspensionStep_cup_R (m n : ℕ) (x : Work.Thom.Coh R m X)
    (z : Work.Thom.RelCoh R (n + 1) A (Work.Thom.subSubset A₁ A)) :
    ((pairδCR R A (m + (n + 1))).hom)
        (((Work.Thom.relToAbs R (Work.Thom.subSubset A₁ A) (m + (n + 1))).hom)
          (((Work.Thom.mixedCupC R (Work.Thom.subSubset A₁ A) m (n + 1))
            ((Work.Thom.CohMap (Work.Thom.subtypeMap A) R m).hom x)) z))
      = ((-1 : R) ^ m) •
        (((Work.Thom.mixedCupC R A m (n + 2)) x)
          (((pairδCR R A (n + 1)).hom)
            (((Work.Thom.relToAbs R (Work.Thom.subSubset A₁ A) (n + 1)).hom) z))) := by
  have h1 := congrArg (fun w => ((pairδCR R A (m + (n + 1))).hom) w)
    (mixedCup_relToAbs_R R (X := A) (Work.Thom.subSubset A₁ A) m (n + 1)
      ((Work.Thom.CohMap (Work.Thom.subtypeMap A) R m).hom x) z)
  have h2 := pairDelta_mixedCup_general_R R (TopCat.of X) A m (n + 1) x
    ((Work.Thom.relToAbs R (Work.Thom.subSubset A₁ A) (n + 1)).hom z)
  rw [h1]
  exact h2

/-- **The Leibniz rule of the suspension isomorphism**, over `R`, in the degree convention
`H^n(A,A₁) → H^{n+1}(X,A)`. -/
theorem suspensionStep_cup'_R (m n : ℕ) (x : Work.Thom.Coh R m X)
    (z : Work.Thom.RelCoh R n A (Work.Thom.subSubset A₁ A)) :
    ((pairδCR R A (m + n)).hom)
        (((Work.Thom.relToAbs R (Work.Thom.subSubset A₁ A) (m + n)).hom)
          (((Work.Thom.mixedCupC R (Work.Thom.subSubset A₁ A) m n)
            ((Work.Thom.CohMap (Work.Thom.subtypeMap A) R m).hom x)) z))
      = ((-1 : R) ^ m) •
        (((Work.Thom.mixedCupC R A m (n + 1)) x)
          (((pairδCR R A n).hom)
            (((Work.Thom.relToAbs R (Work.Thom.subSubset A₁ A) n).hom) z))) := by
  have h1 := congrArg (fun w => ((pairδCR R A (m + n)).hom) w)
    (mixedCup_relToAbs_R R (X := A) (Work.Thom.subSubset A₁ A) m n
      ((Work.Thom.CohMap (Work.Thom.subtypeMap A) R m).hom x) z)
  have h2 := pairDelta_mixedCup_general_R R (TopCat.of X) A m n x
    ((Work.Thom.relToAbs R (Work.Thom.subSubset A₁ A) n).hom z)
  rw [h1]
  exact h2

end

end Work.StemsB
