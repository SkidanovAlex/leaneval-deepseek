import Mathlib
import Submission.Work.MotT.Defs

set_option linter.unusedVariables false -- v435-speed

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false

/-!
# Extending a `K`-isomorphism of linearly disjoint `K`-forms to the ambient field

This file proves `Work.MotT.extend_algEquiv_of_linearDisjoint` (T4, step 1 of the T-twist route
to Lin–Shinder, *Motivic invariants of birational maps*, Ann. of Math. **199** (2024)).

The mathematical content is the following.  Let `K → L → Ω` be a tower of fields and let
`F₁, F₂ ⊆ Ω` be intermediate fields of `Ω/K` which are linearly disjoint from `L` over `K` and
whose compositum with `L` is all of `Ω`.  Then `Ω` is the field of fractions of `F_i ⊗[K] L`
(the multiplication map `F_i ⊗[K] L → Ω` is injective by linear disjointness, and its image
generates `Ω` as a field because `F_i · L = Ω`).  Hence a `K`-algebra isomorphism `θ : F₁ ≃ₐ[K] F₂`
yields a `K`-algebra isomorphism `θ ⊗ id` of the fraction fields, i.e. an automorphism `Θ` of `Ω`,
which fixes `L` pointwise and restricts to `θ` on `F₁`.

Note that in the application the second factor `L` (an algebraic closure `K̄`) is algebraic over
`K`, so `F ⊗[K] L` *is* `Ω` and one could work with `Subalgebra.LinearDisjoint.mulMapLeftOfSupEqTop`
directly (as `Work.MotC.exists_algEquiv_fixedField` does).  The statement here carries no
algebraicity hypothesis, so we use the fraction ring of `F ⊗[K] L` instead: the auxiliary lemma
`Work.MotT.exists_fractionRing_algEquiv_of_linearDisjoint` below shows that the structural map
`F ⊗[K] L → Ω` extends to an isomorphism out of `FractionRing (F ⊗[K] L)`, the surjectivity coming
from `F ⊔ (L : Ω) = ⊤` and the injectivity from `L`-linear disjointness.

## Main results

* `Work.MotT.exists_fractionRing_algEquiv_of_linearDisjoint`: `Ω` as a fraction ring of `F ⊗[K] L`.
* `Work.MotT.extend_algEquiv_of_linearDisjoint`: the extension statement.
-/

namespace Work.MotT

open IntermediateField

noncomputable section

variable {K L Ω : Type} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]

/-- **`Ω` is a fraction field of `F ⊗[K] L`.**  Let `F ⊆ Ω` be an intermediate field of `Ω/K` which
is linearly disjoint from `L` over `K` and whose compositum with (the image of) `L` is all of `Ω`.
Then the structural `K`-algebra map `F ⊗[K] L → Ω`, `a ⊗ b ↦ a * b`, exhibits `Ω` as the fraction
field of `F ⊗[K] L`: it extends to a `K`-algebra isomorphism
`FractionRing (F ⊗[K] L) ≃ₐ[K] Ω`, which sends `a ⊗ 1` to `a` and `1 ⊗ b` to `b`.

The element `B` is the image of `L` in `Ω` (a `K`-subalgebra of `Ω`), and `hB` records this; the
hypothesis `hLI` is `F.LinearDisjoint L` unfolded at the level of subalgebras. -/
theorem exists_fractionRing_algEquiv_of_linearDisjoint (F : IntermediateField K Ω)
    (B : Subalgebra K Ω) (hB : B = (IsScalarTower.toAlgHom K L Ω).range)
    (hLI : F.toSubalgebra.LinearDisjoint B)
    (hsup : F ⊔ (IsScalarTower.toAlgHom K L Ω).fieldRange = ⊤) :
    ∃ Ψ : FractionRing (TensorProduct K F.toSubalgebra B) ≃ₐ[K] Ω,
      ∀ a : F.toSubalgebra, ∀ b : B,
        Ψ (algebraMap _ _ (a ⊗ₜ[K] b)) = (a : Ω) * (b : Ω) := by
  haveI : IsDomain (TensorProduct K F.toSubalgebra B) := Subalgebra.LinearDisjoint.isDomain hLI
  -- the injective structural map `F ⊗[K] B → Ω`
  let g : TensorProduct K F.toSubalgebra B →ₐ[K] Ω := Subalgebra.mulMap F.toSubalgebra B
  have hg : Function.Injective g := Subalgebra.linearDisjoint_iff_injective.mp hLI
  -- its extension to the fraction ring of `F ⊗[K] B`
  let ψ : FractionRing (TensorProduct K F.toSubalgebra B) →ₐ[K] Ω := IsFractionRing.liftAlgHom hg
  have key : ∀ x : TensorProduct K F.toSubalgebra B,
      (ψ : FractionRing (TensorProduct K F.toSubalgebra B) → Ω)
        (algebraMap (TensorProduct K F.toSubalgebra B)
          (FractionRing (TensorProduct K F.toSubalgebra B)) x)
        = (g : TensorProduct K F.toSubalgebra B → Ω) x := by
    intro x
    rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
    rfl
  have hmem : ∀ (a : F.toSubalgebra) (b : B),
      (ψ : FractionRing (TensorProduct K F.toSubalgebra B) → Ω)
        (algebraMap (TensorProduct K F.toSubalgebra B)
          (FractionRing (TensorProduct K F.toSubalgebra B)) (a ⊗ₜ[K] b))
        = (a : Ω) * (b : Ω) := by
    intro a b
    rw [key]
    simp only [g, Subalgebra.mulMap_tmul]
  -- the image of `ψ` contains `F` and the image of `L`; hence, their compositum being `Ω`, it is
  -- everything
  have hF_le : F ≤ ψ.fieldRange := by
    intro x hx
    refine AlgHom.mem_fieldRange.mpr ⟨algebraMap _ _
      ((⟨x, hx⟩ : F.toSubalgebra) ⊗ₜ[K] (1 : B)), ?_⟩
    rw [hmem]; simp
  have hB_le : (IsScalarTower.toAlgHom K L Ω).fieldRange ≤ ψ.fieldRange := by
    intro x hx
    rw [AlgHom.mem_fieldRange] at hx
    obtain ⟨l, hl⟩ := hx
    have hxB : x ∈ B := by rw [hB]; exact ⟨l, hl⟩
    refine AlgHom.mem_fieldRange.mpr ⟨algebraMap _ _
      ((1 : F.toSubalgebra) ⊗ₜ[K] (⟨x, hxB⟩ : B)), ?_⟩
    rw [hmem]; simp
  have hsurj : Function.Surjective ψ := by
    rw [← AlgHom.fieldRange_eq_top]
    apply top_le_iff.mp
    rw [← hsup]
    exact sup_le hF_le hB_le
  have hinj : Function.Injective ψ := fun x y h => RingHom.injective ψ.toRingHom h
  exact ⟨AlgEquiv.ofBijective ψ ⟨hinj, hsurj⟩, fun a b => hmem a b⟩

/-- **Extension of a `K`-isomorphism to `L`.** Let `F₁, F₂ ⊆ Ω` be intermediate fields of a
tower `K → L → Ω`, both linearly disjoint from `L` over `K` and both satisfying `F ⊔ L = ⊤`
(so `F ⊗_K L ≅ Ω` for each). Then every `K`-algebra isomorphism `F₁ ≃ₐ[K] F₂` extends to an
`L`-algebra automorphism of `Ω`. This is the field-theoretic step (T4, step 1) of
`Work.MotT.twist_iso_pointK`: `θ : F_{h₁} ≃ₐ[K] F_{h₂}` extends to `Θ ∈ Aut_{K̄}(K̄(E))`, to which
the automorphism classification `Work.MotT.AutRigid` (node C2 / `MotC2.aut_functionField`) applies.

Route: `F ⊗_K L ≅ Ω` from linear disjointness (injectivity) + `F ⊔ L = ⊤` (surjectivity); the
`K`-algebra isomorphism `θ ⊗ id` is then an `L`-algebra automorphism of `Ω`, and its restriction to
`F₁ ⊆ F₁ ⊗_K L` is `θ`.  Mathlib has `Subalgebra.LinearDisjoint.mulMapLeftOfSupEqTop`. -/
theorem extend_algEquiv_of_linearDisjoint {K L Ω : Type} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    (F₁ F₂ : IntermediateField K Ω)
    (hLI₁ : F₁.LinearDisjoint L) (hLI₂ : F₂.LinearDisjoint L)
    (hsup₁ : F₁ ⊔ (IsScalarTower.toAlgHom K L Ω).fieldRange = ⊤)
    (hsup₂ : F₂ ⊔ (IsScalarTower.toAlgHom K L Ω).fieldRange = ⊤)
    (θ : F₁ ≃ₐ[K] F₂) :
    ∃ Θ : Ω ≃ₐ[L] Ω, ∀ x : F₁, Θ (x : Ω) = (θ x : Ω) := by
  set B : Subalgebra K Ω := (IsScalarTower.toAlgHom K L Ω).range with hB
  -- both `F₁` and `F₂` are the fraction field description of `Ω`
  obtain ⟨Ψ₁, hΨ₁⟩ := exists_fractionRing_algEquiv_of_linearDisjoint F₁ B hB hLI₁ hsup₁
  obtain ⟨Ψ₂, hΨ₂⟩ := exists_fractionRing_algEquiv_of_linearDisjoint F₂ B hB hLI₂ hsup₂
  let θ' : F₁.toSubalgebra ≃ₐ[K] F₂.toSubalgebra := θ
  -- `θ ⊗ id` and the induced isomorphism of fraction rings
  let τ : TensorProduct K F₁.toSubalgebra B ≃ₐ[K] TensorProduct K F₂.toSubalgebra B :=
    Algebra.TensorProduct.congr θ' (AlgEquiv.refl : B ≃ₐ[K] B)
  let ρ : FractionRing (TensorProduct K F₁.toSubalgebra B) ≃ₐ[K]
      FractionRing (TensorProduct K F₂.toSubalgebra B) := IsFractionRing.algEquivOfAlgEquiv τ
  -- the induced automorphism of `Ω`
  let Θ₀ : Ω ≃ₐ[K] Ω := Ψ₁.symm.trans (ρ.trans Ψ₂)
  have hτ : ∀ (a : F₁.toSubalgebra) (b : B), τ (a ⊗ₜ[K] b) = θ' a ⊗ₜ[K] b := by
    intro a b
    simp only [τ, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    rfl
  -- `Θ₀` restricts to `θ` on `F₁`
  have key1 : ∀ x : F₁, Θ₀ (x : Ω) = (θ x : Ω) := by
    intro x
    have hsym : Ψ₁.symm (x : Ω) =
        algebraMap _ _ ((⟨(x : Ω), x.2⟩ : F₁.toSubalgebra) ⊗ₜ[K] (1 : B)) := by
      rw [AlgEquiv.symm_apply_eq, hΨ₁]
      simp
    have hρ : ρ (algebraMap _ _ ((⟨(x : Ω), x.2⟩ : F₁.toSubalgebra) ⊗ₜ[K] (1 : B)))
        = algebraMap _ _ (θ' ⟨(x : Ω), x.2⟩ ⊗ₜ[K] (1 : B)) := by
      rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap, hτ]
    have hΨ₂' : Ψ₂ (algebraMap _ _ (θ' ⟨(x : Ω), x.2⟩ ⊗ₜ[K] (1 : B))) = (θ x : Ω) := by
      rw [hΨ₂]
      simp [θ']
    show Ψ₂ (ρ (Ψ₁.symm (x : Ω))) = (θ x : Ω)
    rw [hsym, hρ, hΨ₂']
  -- `Θ₀` fixes `L` pointwise
  have key2 : ∀ l : L, Θ₀ (algebraMap L Ω l) = algebraMap L Ω l := by
    intro l
    have hmemB : algebraMap L Ω l ∈ B := by rw [hB]; exact ⟨l, rfl⟩
    have hsym : Ψ₁.symm (algebraMap L Ω l) =
        algebraMap _ _ ((1 : F₁.toSubalgebra) ⊗ₜ[K] (⟨algebraMap L Ω l, hmemB⟩ : B)) := by
      rw [AlgEquiv.symm_apply_eq, hΨ₁]
      simp
    have hρ : ρ (algebraMap _ _ ((1 : F₁.toSubalgebra) ⊗ₜ[K] (⟨algebraMap L Ω l, hmemB⟩ : B)))
        = algebraMap _ _ ((1 : F₂.toSubalgebra) ⊗ₜ[K] (⟨algebraMap L Ω l, hmemB⟩ : B)) := by
      rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap, hτ]
      congr 1
      simp
    have hΨ₂' : Ψ₂ (algebraMap _ _
        ((1 : F₂.toSubalgebra) ⊗ₜ[K] (⟨algebraMap L Ω l, hmemB⟩ : B))) = algebraMap L Ω l := by
      rw [hΨ₂]; simp
    show Ψ₂ (ρ (Ψ₁.symm (algebraMap L Ω l))) = algebraMap L Ω l
    rw [hsym, hρ, hΨ₂']
  refine ⟨AlgEquiv.ofRingEquiv (f := Θ₀.toRingEquiv) (fun l => key2 l), fun x => ?_⟩
  simp only [AlgEquiv.ofRingEquiv_apply]
  exact key1 x

end

end Work.MotT
