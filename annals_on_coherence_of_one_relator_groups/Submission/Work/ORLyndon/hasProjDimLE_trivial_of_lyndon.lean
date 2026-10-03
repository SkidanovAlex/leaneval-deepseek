import Mathlib
import Submission.Work.ORLyndon.Lyndon
import Submission.Work.ORLyndon.ProjDim
import Submission.Work.ORLyndon.lyndonDelta_range_eq_augIdeal
import Submission.Work.ORLyndon.lyndon_exact_relationModuleMap
import Submission.Work.ORLyndon.relationModuleMap_injective
import Submission.Work.ORLyndon.projective_quotient_span_of_pow_eq_one
import Submission.Work.ORLyndon.HasProjDimLE_of_linearEquiv

/-!
# The trivial module of a one-relator group algebra has projective dimension `≤ 2`

Let `X` be a set, `K` a field of characteristic zero, `r = u ^ l ∈ F(X)` a relator whose root `u`
is not a proper power, and `G = ⟨X | r⟩` the associated one-relator group
(`Work.ORLyndon.OneRelatorGroup`).  Assuming Lyndon's identity theorem
(`Work.ORLyndon.LyndonIdentity`) we show that the trivial left `K[G]`-module
`K[G] / I_{K[G]}` (the quotient by the augmentation ideal) admits a projective resolution of length
at most `2`, i.e. `Work.ORLyndon.HasProjDimLE K[G] (K[G]/I) 2`.

The argument is the Lyndon resolution of the one-relator presentation

`0 → K[G] ⊗_{K⟨u⟩} K → K[G]^X --δ--> K[G] --ε--> K → 0`,

whose middle homology `coker θ = K[G]^X / ker δ` is the relation module `K[G]/K[G](u-1)`.  Since
`u ^ l = 1` with `(l : K) ≠ 0`, that relation module is projective (Maschke), and:
* the syzygy `ker δ` is isomorphic to the relation module, hence projective,
* `range δ = I_{K[G]}` is a quotient of the free module `K[G]^X` by a projective module, so
  `HasProjDimLE K[G] I_{K[G]} 1`,
* `K[G]/I_{K[G]}` is a quotient of the free module `K[G]` by `I_{K[G]}`, so
  `HasProjDimLE K[G] (K[G]/I_{K[G]}) 2`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

theorem hasProjDimLE_trivial_of_lyndon {X : Type*} [DecidableEq X] {K : Type*} [Field K] [CharZero K]
    {r u : FreeGroup X} {l : ℕ} (h : Work.ORLyndon.LyndonIdentity K X r u l) :
    Work.ORLyndon.HasProjDimLE (MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r))
      (MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r) ⧸
        Work.ORLyndon.augIdeal K (Work.ORLyndon.OneRelatorGroup r)) 2 := by
  have hpow : (Work.ORLyndon.presentRho r u) ^ l = 1 := by
    rw [← map_pow, h.hpow, Work.ORLyndon.presentRho_relator]
  have hl : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr h.hpos.ne'
  -- The relation module is projective, since `u` has finite order invertible in `K`.
  have hproj : Module.Projective (MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r))
      (Work.ORLyndon.relationModule K r u) :=
    Work.ORLyndon.projective_quotient_span_of_pow_eq_one (Work.ORLyndon.presentRho r u) l hpow hl
  have hpdRel : Work.ORLyndon.HasProjDimLE (MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r))
      (Work.ORLyndon.relationModule K r u) 0 := hproj
  -- Hence the syzygy `ker δ` of the Lyndon resolution is projective.
  have hpdKer : Work.ORLyndon.HasProjDimLE (MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r))
      (LinearMap.ker (Work.ORLyndon.lyndonDelta (K := K) r)) 0 :=
    Work.ORLyndon.HasProjDimLE_of_linearEquiv
      ((LinearEquiv.ofInjective (Work.ORLyndon.relationModuleMap K r u l h)
          (Work.ORLyndon.relationModuleMap_injective h)).trans
        (LinearEquiv.ofEq _ _ (Work.ORLyndon.lyndon_exact_relationModuleMap h)))
      hpdRel
  -- The augmentation ideal is the range of `δ`, so its projective dimension is `≤ 1`.
  have hpdAug : Work.ORLyndon.HasProjDimLE (MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r))
      (Work.ORLyndon.augIdeal K (Work.ORLyndon.OneRelatorGroup r)) 1 := by
    have hrange := Work.ORLyndon.lyndonDelta_range_eq_augIdeal (K := K) r
    let f : (X →₀ MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r)) →ₗ[
        MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r)]
        (Work.ORLyndon.augIdeal K (Work.ORLyndon.OneRelatorGroup r)) :=
      LinearMap.codRestrict _ (Work.ORLyndon.lyndonDelta (K := K) r) (fun a => by
        rw [← hrange]
        exact ⟨a, rfl⟩)
    have hkerf : LinearMap.ker f = LinearMap.ker (Work.ORLyndon.lyndonDelta (K := K) r) :=
      LinearMap.ker_codRestrict _ _ _
    refine ⟨_, inferInstance, inferInstance, Module.Projective.of_free, f, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      obtain ⟨b, hb⟩ : ∃ b, Work.ORLyndon.lyndonDelta (K := K) r b = y := by
        have hy' : y ∈ Work.ORLyndon.augIdeal K (Work.ORLyndon.OneRelatorGroup r) := hy
        rw [← hrange] at hy'
        exact hy'
      exact ⟨b, Subtype.ext hb⟩
    · show Work.ORLyndon.HasProjDimLE _ (LinearMap.ker f) 0
      rw [hkerf]
      exact hpdKer
  -- Finally the trivial module is a quotient of the free module `K[G]` by the augmentation ideal.
  refine ⟨MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r), inferInstance, inferInstance,
    Module.Projective.of_free,
    Submodule.mkQ (Work.ORLyndon.augIdeal K (Work.ORLyndon.OneRelatorGroup r)),
    Submodule.mkQ_surjective _, ?_⟩
  show Work.ORLyndon.HasProjDimLE _
    (LinearMap.ker (Submodule.mkQ (Work.ORLyndon.augIdeal K (Work.ORLyndon.OneRelatorGroup r)))) 1
  rw [Submodule.ker_mkQ]
  exact hpdAug

end Work.ORLyndon
