import Mathlib
import Submission.Work.ThomBordism.absThomComparePhi
import Submission.Work.Thom.ATools
import Submission.Work.Cohomology.relCupHNatural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Naturality of the canonical Thom comparison `ThetaZ`

For a real bundle `Z` over a compact Hausdorff base with finite dimensional fibre and a norm-like
function `N` on it, `Work.ThomBordism.ThetaZ Z N hn` is the canonical comparison
`H^n(Z⁺) ≅ H^n(Z, Z∖0)` between the cohomology of the one-point compactification (the Thom space)
and the relative cohomology of the Thom pair, built in `Submission/Work/ThomBordism/absThomCompare*.lean`
as

  `ThetaZ Z N hn := compPullZ Z N n ∘ relCohOfAbsZ Z N hn`,

the composite of the inverse of the forgetful map `relToAbs : H^n(Z⁺, A) → H^n(Z⁺)`
(with `A = (Z∖0) ∪ {∞}`) with the excision-plus-homeomorphism pullback `compPullZ`.

This file proves that it is **natural**: a map of bundles `g : Z' → Z` whose one-point
compactification `J : Z'⁺ → Z⁺` is compatible (`J (some p) = some (g p)`, `J ∞ = ∞`) satisfies

  `ThetaZ Z' N' hn (J^* u) = g^* (ThetaZ Z N hn u)`,

which is the statement of `Work.ThomBordism.thetaZNatural`.

The content is formal: `relToAbs` is natural (`Work.Thom.relCohMap_relToAbs`) and bijective on
`(Z⁺, A)` because `A` is contractible (`Work.ThomBordism.absNZRelToAbsBijective`,
`Work.ThomBordism.absContractible`), so `relCohOfAbsZ` is natural; and `compPullZ` — the excision
and the homeomorphism of pairs `(Z, Z∖0) ≅ ({∞}ᶜ, {∞}ᶜ ∩ A)` — is the pullback along
`some : Z → Z⁺`, hence natural by `Work.Thom.relCohMap_compA`.

### Main results

* `Work.ThomBordism.someMap` — the continuous map `some : Z → Z⁺`;
* `Work.ThomBordism.someMap_eq` — `infZIncl ∘ (someHomeoZ) = some` (the excision inclusion
  followed by the homeomorphism is `some`);
* `Work.ThomBordism.compPullZ_eq_comp` — `compPullZ Z N n` is the composite of the pullbacks along
  `infZIncl` and `someHomeoZ`;
* `Work.ThomBordism.compPullZ_eq` — `compPullZ Z N n` is the pullback along `someMap Z`;
* `Work.ThomBordism.compPullZ_natural` — naturality of `compPullZ`;
* `Work.ThomBordism.relCohOfAbsZ_natural` — naturality of `relCohOfAbsZ`;
* `Work.ThomBordism.thetaZNatural` — the target.
-/

open CategoryTheory Limits
open Work.TangentClasses
open scoped Topology

namespace Work.ThomBordism

open Work.Cohomology

noncomputable section

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}
variable {B' : Type} [TopologicalSpace B'] [CompactSpace B'] [T2Space B']
variable {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F'] {ι' : Type}

/-! ## The map `some : Z → Z⁺` -/

/-- The canonical inclusion of a space into its one-point compactification, as a bundled continuous
map. -/
def someMap (Z : RealBundle B F ι) : C(Z.TotalSpace, OnePoint Z.TotalSpace) :=
  ⟨OnePoint.some, OnePoint.continuous_coe⟩

@[simp] theorem someMap_apply (Z : RealBundle B F ι) (p : Z.TotalSpace) :
    someMap Z p = OnePoint.some p := rfl

/-- **The excision inclusion followed by the homeomorphism `Z ≅ {∞}ᶜ` is `some`**: the definitional
identity behind `compPullZ`. -/
theorem someMap_eq (Z : RealBundle B F ι) :
    (infZIncl Z).comp (someHomeoZ Z : C(Z.TotalSpace, ↥(infZ Z))) = someMap Z := by
  ext z
  exact someHomeoZ_apply Z z

/-- The membership condition of the pair map `(Z, Z∖0) → (Z⁺, A)` given by `some`. -/
theorem someMap_mem (Z : RealBundle B F ι) :
    ∀ p ∈ Work.Thom.zeroComplement Z, someMap Z p ∈ absNZ Z := fun p hp => by
  show OnePoint.some p ∈ absNZ Z
  exact (some_mem_absNZ Z p).mpr hp

/-! ## `compPullZ` is the pullback along `some` -/

/-- **`compPullZ` is the composite of the pullbacks along `infZIncl` and `someHomeoZ`** (the
definition, exposed as an identity of linear maps). -/
theorem compPullZ_eq_comp (Z : RealBundle B F ι) (N : NormLike Z) (n : ℕ) :
    compPullZ Z N n = (CategoryTheory.CategoryStruct.comp
      (Work.Thom.relCohMap (infZIncl Z) (excSubZ Z) (absNZ Z) (fun _ hy => hy) ℤ n)
      (Work.Thom.relCohMap (someHomeoZ Z) (Work.Thom.zeroComplement Z) (excSubZ Z)
        (fun x hx => (some_mem_excSubZ Z x).mp hx) ℤ n)).hom := by
  apply LinearMap.ext
  intro β
  rfl

/-- **`compPullZ Z N n` is the pullback along `some : Z → Z⁺`** (the excision of `∞` and the
homeomorphism of pairs `(Z, Z∖0) ≅ ({∞}ᶜ, {∞}ᶜ ∩ A)` collapse to it). -/
theorem compPullZ_eq (Z : RealBundle B F ι) (N : NormLike Z) (n : ℕ) :
    compPullZ Z N n =
      (Work.Thom.relCohMap (someMap Z) (Work.Thom.zeroComplement Z) (absNZ Z)
        (someMap_mem Z) ℤ n).hom := by
  rw [compPullZ_eq_comp Z N n]
  have hmem : ∀ x ∈ Work.Thom.zeroComplement Z, someHomeoZ Z x ∈ excSubZ Z :=
    fun x hx => (some_mem_excSubZ Z x).mp hx
  have hg : ∀ y ∈ excSubZ Z, infZIncl Z y ∈ absNZ Z := fun _ hy => hy
  have hgf : ∀ x ∈ Work.Thom.zeroComplement Z, infZIncl Z (someHomeoZ Z x) ∈ absNZ Z :=
    fun x hx => hg _ (hmem x hx)
  have hcomp := Work.Thom.relCohMap_compA (Work.Thom.zeroComplement Z) (excSubZ Z) (absNZ Z)
    (someHomeoZ Z) (infZIncl Z) hmem hg hgf ℤ n
  rw [← Work.Thom.relCohMap_congrA (Work.Thom.zeroComplement Z) (absNZ Z) (someMap_eq Z) hgf
    (someMap_mem Z) ℤ n]
  exact congrArg ModuleCat.Hom.hom hcomp

/-! ## Naturality of `compPullZ` -/

/-- **Naturality of `compPullZ`** under a map of bundles `g : Z' → Z` whose one-point
compactification `J` sends `some p` to `some (g p)`. -/
theorem compPullZ_natural (Z : RealBundle B F ι) (Z' : RealBundle B' F' ι')
    (NZ : NormLike Z) (NZ' : NormLike Z') {n : ℕ} (g : C(Z'.TotalSpace, Z.TotalSpace))
    (hg : ∀ p : Z'.TotalSpace, p ∈ Work.Thom.zeroComplement Z' → g p ∈ Work.Thom.zeroComplement Z)
    (J : C(OnePoint Z'.TotalSpace, OnePoint Z.TotalSpace))
    (hJ : ∀ p : Z'.TotalSpace, J (OnePoint.some p) = OnePoint.some (g p))
    (hJA : ∀ p ∈ absNZ Z', J p ∈ absNZ Z)
    (β : Work.Thom.RelCoh ℤ n (OnePoint Z.TotalSpace) (absNZ Z)) :
    (Work.Thom.relCohMap g (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z) hg ℤ n).hom
        (compPullZ Z NZ n β)
      = compPullZ Z' NZ' n
          ((Work.Thom.relCohMap J (absNZ Z') (absNZ Z) hJA ℤ n).hom β) := by
  rw [compPullZ_eq Z NZ n, compPullZ_eq Z' NZ' n]
  -- both sides as composites of pullbacks
  have hL : (Work.Thom.relCohMap g (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z)
        hg ℤ n).hom
      ((Work.Thom.relCohMap (someMap Z) (Work.Thom.zeroComplement Z) (absNZ Z)
        (someMap_mem Z) ℤ n).hom β)
      = (CategoryTheory.CategoryStruct.comp
          (Work.Thom.relCohMap (someMap Z) (Work.Thom.zeroComplement Z) (absNZ Z)
            (someMap_mem Z) ℤ n)
          (Work.Thom.relCohMap g (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z)
            hg ℤ n)).hom β := rfl
  have hR : (CategoryTheory.CategoryStruct.comp
      (Work.Thom.relCohMap J (absNZ Z') (absNZ Z) hJA ℤ n)
      (Work.Thom.relCohMap (someMap Z') (Work.Thom.zeroComplement Z') (absNZ Z')
        (someMap_mem Z') ℤ n)).hom β
      = (Work.Thom.relCohMap (someMap Z') (Work.Thom.zeroComplement Z') (absNZ Z')
        (someMap_mem Z') ℤ n).hom
          ((Work.Thom.relCohMap J (absNZ Z') (absNZ Z) hJA ℤ n).hom β) := rfl
  rw [hL, ← hR]
  have hgf1 : ∀ x ∈ Work.Thom.zeroComplement Z', someMap Z (g x) ∈ absNZ Z :=
    fun x hx => someMap_mem Z _ (hg x hx)
  have hcomp1 := Work.Thom.relCohMap_compA (Work.Thom.zeroComplement Z')
    (Work.Thom.zeroComplement Z) (absNZ Z) g (someMap Z) hg (someMap_mem Z) hgf1 ℤ n
  rw [congrArg ModuleCat.Hom.hom hcomp1]
  have hgf2 : ∀ x ∈ Work.Thom.zeroComplement Z', J (someMap Z' x) ∈ absNZ Z :=
    fun x hx => hJA _ (someMap_mem Z' x hx)
  have hcomp2 := Work.Thom.relCohMap_compA (Work.Thom.zeroComplement Z') (absNZ Z') (absNZ Z)
    (someMap Z') J (someMap_mem Z') hJA hgf2 ℤ n
  rw [congrArg ModuleCat.Hom.hom hcomp2]
  have hJs : J.comp (someMap Z') = (someMap Z).comp g := by
    ext z
    show J (OnePoint.some z) = OnePoint.some (g z)
    exact hJ z
  rw [show Work.Thom.relCohMap (J.comp (someMap Z')) (Work.Thom.zeroComplement Z') (absNZ Z)
        hgf2 ℤ n
      = Work.Thom.relCohMap ((someMap Z).comp g) (Work.Thom.zeroComplement Z') (absNZ Z)
        hgf1 ℤ n
      from Work.Thom.relCohMap_congrA _ _ hJs hgf2 hgf1 ℤ n]

/-! ## Naturality of `relCohOfAbsZ` -/

/-- **Naturality of `relCohOfAbsZ`**, the inverse of the forgetful map `relToAbs` on `(Z⁺, A)`:
`relToAbs` is natural and bijective (`Work.ThomBordism.absNZRelToAbsBijective`), so its inverse is
natural as well. -/
theorem relCohOfAbsZ_natural (Z : RealBundle B F ι) (Z' : RealBundle B' F' ι')
    (NZ : NormLike Z) (NZ' : NormLike Z') {n : ℕ} (hn : 2 ≤ n)
    (J : C(OnePoint Z'.TotalSpace, OnePoint Z.TotalSpace))
    (hJA : ∀ p ∈ absNZ Z', J p ∈ absNZ Z)
    (u : Work.Thom.Coh ℤ n (OnePoint Z.TotalSpace)) :
    (Work.Thom.relCohMap J (absNZ Z') (absNZ Z) hJA ℤ n).hom (relCohOfAbsZ Z NZ hn u)
      = relCohOfAbsZ Z' NZ' hn ((Work.Thom.CohMap J ℤ n).hom u) := by
  refine (absNZRelToAbsBijective Z' (absContractible Z' NZ') hn).1 ?_
  have h1 : (Work.Thom.relToAbs ℤ (absNZ Z') n).hom
        ((Work.Thom.relCohMap J (absNZ Z') (absNZ Z) hJA ℤ n).hom (relCohOfAbsZ Z NZ hn u))
      = (Work.Thom.CohMap J ℤ n).hom u := by
    have h := congrArg (fun (φ : Work.Thom.RelCoh ℤ n (OnePoint Z.TotalSpace) (absNZ Z) ⟶
        Work.Thom.Coh ℤ n (OnePoint Z'.TotalSpace)) => φ.hom (relCohOfAbsZ Z NZ hn u))
      (Work.Thom.relCohMap_relToAbs J (absNZ Z') (absNZ Z) hJA ℤ n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h, relToAbs_relCohOfAbsZ]
  have h2 : (Work.Thom.relToAbs ℤ (absNZ Z') n).hom
        (relCohOfAbsZ Z' NZ' hn ((Work.Thom.CohMap J ℤ n).hom u))
      = (Work.Thom.CohMap J ℤ n).hom u :=
    relToAbs_relCohOfAbsZ Z' NZ' hn ((Work.Thom.CohMap J ℤ n).hom u)
  exact h1.trans h2.symm

/-! ## The target -/

/-- **Naturality of the canonical comparison `ThetaZ`**: for a map of real bundles `g : Z' → Z`
(over compact Hausdorff bases, finite dimensional fibres, with norm-like functions) whose one-point
compactification `J` sends `some p` to `some (g p)` and `∞` to `∞`, the comparison
`H^n(Z⁺) ≅ H^n(Z, Z∖0)` is natural. -/
theorem thetaZNatural {B B' : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
    [TopologicalSpace B'] [CompactSpace B'] [T2Space B']
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
    {ι ι' : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (Z' : Work.TangentClasses.RealBundle B' F' ι')
    (NZ : Work.ThomBordism.NormLike Z) (NZ' : Work.ThomBordism.NormLike Z') {n : ℕ} (hn : 2 ≤ n)
    (g : C(Z'.TotalSpace, Z.TotalSpace))
    (hg : ∀ p : Z'.TotalSpace, p ∈ Work.Thom.zeroComplement Z' →
      g p ∈ Work.Thom.zeroComplement Z)
    (J : C(OnePoint Z'.TotalSpace, OnePoint Z.TotalSpace))
    (hJ : ∀ p : Z'.TotalSpace, J (OnePoint.some p) = OnePoint.some (g p))
    (hJinf : J OnePoint.infty = OnePoint.infty)
    (u : Work.Thom.Coh ℤ n (OnePoint Z.TotalSpace)) :
    Work.ThomBordism.ThetaZ Z' NZ' hn ((Work.Thom.CohMap J ℤ n).hom u)
      = (Work.Thom.relCohMap g (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z) hg
          ℤ n).hom (Work.ThomBordism.ThetaZ Z NZ hn u) := by
  have hJA : ∀ x ∈ absNZ Z', J x ∈ absNZ Z := by
    intro x hx
    by_cases hx' : x = OnePoint.infty
    · subst hx'
      rw [hJinf]
      exact infty_mem_absNZ Z
    · obtain ⟨p, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hx'
      rw [some_mem_absNZ] at hx
      rw [hJ p]
      exact someMap_mem Z (g p) (hg p hx)
  have h4 := compPullZ_natural Z Z' NZ NZ' g hg J hJ hJA
    (β := relCohOfAbsZ Z NZ hn u)
  have h5 := relCohOfAbsZ_natural Z Z' NZ NZ' hn J hJA u
  calc Work.ThomBordism.ThetaZ Z' NZ' hn ((Work.Thom.CohMap J ℤ n).hom u)
      = compPullZ Z' NZ' n
          ((relCohOfAbsZ Z' NZ' hn) ((Work.Thom.CohMap J ℤ n).hom u)) := rfl
    _ = compPullZ Z' NZ' n
          ((Work.Thom.relCohMap J (absNZ Z') (absNZ Z) hJA ℤ n).hom
            ((relCohOfAbsZ Z NZ hn) u)) := by rw [h5]
    _ = (Work.Thom.relCohMap g (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z)
          hg ℤ n).hom (compPullZ Z NZ n ((relCohOfAbsZ Z NZ hn) u)) := h4.symm
    _ = (Work.Thom.relCohMap g (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z)
          hg ℤ n).hom (Work.ThomBordism.ThetaZ Z NZ hn u) := rfl

end

end Work.ThomBordism
