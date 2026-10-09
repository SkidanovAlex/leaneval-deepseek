import Mathlib
import Submission.NK.GlobalCFT.Place

import Submission.NK.HassePrinciple.localRingEquiv_localAlgebraMapUnits_of_restrict
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
import Submission.NK.HassePrinciple.IdeleCocycle
import Submission.NK.HassePrinciple.liesOver_smul_of_restrict
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.NUV2.LC.LocalLevelSystem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1000000

/-!
# The local level map `v`

For a tower `F ⊆ L ⊆ M` of number fields (with `M/F`, `L/F` finite Galois) and finite places
`q' | q` (i.e. `q'.asIdeal.LiesOver q.asIdeal`), the local level map

`v : H²(Γ_q(L), L_qˣ) ⟶ H²(Γ_{q'}(M), M_{q'}ˣ)`

is the composite of the restriction of the local groups
`Γ_{q'}(M) = stabilizer Gal(M/F) q' →* stabilizer Gal(L/F) q = Γ_q(L)`
(an element of `Gal(M/F)` fixing `q'` restricts to an element of `Gal(L/F)` fixing `q`) with the
local coefficient map `(L_q)ˣ →* (M_{q'})ˣ` of `NK.NUV2.LC.exists_localUnitsMap`.

It is the map that appears in the level square `(G1)` of
`Submission/Work/NUV2/LC/NOTES_hasse_open_level.md`: the coarse localisation at a deeper level is the
image of the shallower one under `v`.

## This file

* `stabilizer_restrict_smul_eq` — the group-theoretic half: a `σ : Gal(M/F)` fixing the place
  `ofFinite q'` restricts to an automorphism of `L` fixing `ofFinite q`.  (Uses `Place.LiesOver`
  and `NK.HassePrinciple.liesOver_smul_of_restrict`, plus the uniqueness of the place of `L`
  below a fixed finite place of `M`, which is `LiesOver`'s definition read through `liesOver_iff`.)
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace NK.NUV2.LC

open NK.GlobalCFT

variable {F L M : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra F L] [Algebra F M] [Algebra L M] [IsScalarTower F L M]
  [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional F M] [IsGalois F M]

/-- **Uniqueness of the place below a finite place.**  A finite place of `L` lying below a fixed
finite place of `M` is determined by it: this is `Place.LiesOver`'s definition read through
`Place.liesOver_iff`, since `q'.asIdeal.LiesOver Q.asIdeal` says that `Q.asIdeal` is the contraction
of `q'.asIdeal` to `L`. -/
theorem liesOver_ofFinite_unique
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    {v₁ v₂ : NK.GlobalCFT.Place L}
    (h₁ : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') v₁)
    (h₂ : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') v₂) :
    v₁ = v₂ := by
  rw [NK.GlobalCFT.Place.liesOver_iff] at h₁ h₂
  rcases h₁ with ⟨w₁, v₁', hw₁, -, -⟩ | ⟨q₁, Q₁, hq₁, hv₁, hqQ₁⟩
  · exact absurd hw₁ (by simp)
  rcases h₂ with ⟨w₂, v₂', hw₂, -, -⟩ | ⟨q₂, Q₂, hq₂, hv₂, hqQ₂⟩
  · exact absurd hw₂ (by simp)
  have e₁ : q₁ = q' := by cases hq₁; rfl
  have e₂ : q₂ = q' := by cases hq₂; rfl
  have hid : Q₁.asIdeal = Q₂.asIdeal := by
    have h₁ := hqQ₁.over
    have h₂ := hqQ₂.over
    rw [e₁] at h₁
    rw [e₂] at h₂
    exact h₁.trans h₂.symm
  have hQ : Q₁ = Q₂ := by
    cases Q₁
    cases Q₂
    simp_all
  rw [hv₁, hv₂, hQ]

/-- **The group-theoretic half of the local level map `v`.**  An element `σ` of `Gal(M/F)` fixing
the finite place `q'` of `M` restricts to an element of `Gal(L/F)` fixing the finite place `q` of
`L` below it. -/
theorem stabilizer_restrict_smul_eq
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (hq : q.asIdeal = q'.asIdeal.comap
      (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M)))
    (σ : Gal(M/F))
    (hσ : σ • (NK.GlobalCFT.Place.ofFinite q') = NK.GlobalCFT.Place.ofFinite q') :
    ((AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ) •
        (NK.GlobalCFT.Place.ofFinite q) = NK.GlobalCFT.Place.ofFinite q := by
  have hLies : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
      (NK.GlobalCFT.Place.ofFinite q) :=
    NK.GlobalCFT.Place.liesOver_ofFinite
      (K := L) (L := M) (Ideal.LiesOver.mk (by rw [hq]))
  have hLies' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
      (((AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ) •
        (NK.GlobalCFT.Place.ofFinite q)) := by
    have h := NK.HassePrinciple.liesOver_smul_of_restrict (K := F) (F := L) (L := M) σ
      ((AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ)
      (fun y => AlgEquiv.restrictNormal_commutes (E := L) σ y) hLies
    rwa [hσ] at h
  exact liesOver_ofFinite_unique q' hLies' hLies

/-! ## The equivariance of the local units map under the local automorphisms -/

section Equivariance

/-- The completion map of the tower on the image of `L`. -/
private lemma adicCompletionMap_algebraMap
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (hq : q.asIdeal = q'.asIdeal.comap
      (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M))) (f : L) :
    Commons.RingTheory.Henselian.adicCompletionMap q q' (Ideal.LiesOver.mk (by rw [hq]))
        (algebraMap L (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q)) f) =
      algebraMap M (NK.GlobalCFT.Place.localField M (NK.GlobalCFT.Place.ofFinite q'))
        (algebraMap L M f) := by
  show Commons.RingTheory.Henselian.adicCompletionMap q q' (Ideal.LiesOver.mk (by rw [hq]))
    (f : q.adicCompletion L) = _
  rw [Commons.RingTheory.Henselian.adicCompletionMap_apply]
  rfl

/-- **The ring-level naturality of the completion maps for the tower.**  For `σ : Gal(M/F)` fixing
the finite place `q'` of `M` (and hence, by `stabilizer_restrict_smul_eq`, restricting to an
`A : Gal(L/F)` fixing `q`), the completion map `q.adicCompletion L →+* q'.adicCompletion M` of the
tower intertwines the two local automorphisms. -/
theorem adicCompletionMap_localAut
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (hq : q.asIdeal = q'.asIdeal.comap
      (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M)))
    (σ : Gal(M/F))
    (hσ : σ • (NK.GlobalCFT.Place.ofFinite q') = NK.GlobalCFT.Place.ofFinite q') :
    ∀ x : q.adicCompletion L,
      Commons.RingTheory.Henselian.adicCompletionMap q q' (Ideal.LiesOver.mk (by rw [hq]))
          (NK.HassePrinciple.localAut (K := F) (NK.GlobalCFT.Place.ofFinite q)
            ⟨(AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ,
              stabilizer_restrict_smul_eq q q' hq σ hσ⟩ x) =
        NK.HassePrinciple.localAut (K := F) (NK.GlobalCFT.Place.ofFinite q')
            ⟨σ, by rw [MulAction.mem_stabilizer_iff]; exact hσ⟩
          (Commons.RingTheory.Henselian.adicCompletionMap q q' (Ideal.LiesOver.mk (by rw [hq])) x) := by
  intro x
  set A : Gal(L/F) := (AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ with hA
  have hAstab : A • (NK.GlobalCFT.Place.ofFinite q) = NK.GlobalCFT.Place.ofFinite q :=
    stabilizer_restrict_smul_eq q q' hq σ hσ
  set σs : MulAction.stabilizer Gal(M/F) (NK.GlobalCFT.Place.ofFinite q') :=
    ⟨σ, by rw [MulAction.mem_stabilizer_iff]; exact hσ⟩ with hσs
  set As : MulAction.stabilizer Gal(L/F) (NK.GlobalCFT.Place.ofFinite q) :=
    ⟨A, by rw [MulAction.mem_stabilizer_iff]; exact hAstab⟩ with hAs
  have key : (fun y : q.adicCompletion L =>
      Commons.RingTheory.Henselian.adicCompletionMap q q' (Ideal.LiesOver.mk (by rw [hq]))
        (NK.HassePrinciple.localAut (K := F) (NK.GlobalCFT.Place.ofFinite q) As y)) =
      fun y => NK.HassePrinciple.localAut (K := F) (NK.GlobalCFT.Place.ofFinite q') σs
        (Commons.RingTheory.Henselian.adicCompletionMap q q' (Ideal.LiesOver.mk (by rw [hq])) y) := by
    refine DenseRange.equalizer (f := algebraMap L (q.adicCompletion L)) ?_ ?_ ?_ ?_
    · exact NK.GlobalCFT.Galois.denseRange_algebraMap_localField
        (NK.GlobalCFT.Place.ofFinite q)
    · exact (Commons.RingTheory.Henselian.adicCompletionMap_continuous q q'
        (Ideal.LiesOver.mk (by rw [hq]))).comp
        (NK.HassePrinciple.localAut_continuous (K := F) (NK.GlobalCFT.Place.ofFinite q) As)
    · exact (NK.HassePrinciple.localAut_continuous (K := F) (NK.GlobalCFT.Place.ofFinite q') σs).comp
        (Commons.RingTheory.Henselian.adicCompletionMap_continuous q q'
          (Ideal.LiesOver.mk (by rw [hq])))
    · funext y
      simp only [Function.comp_apply]
      rw [NK.HassePrinciple.localAut_algebraMap (K := F) (NK.GlobalCFT.Place.ofFinite q) As y]
      rw [adicCompletionMap_algebraMap q q' hq (((As : Gal(L/F))) y),
        adicCompletionMap_algebraMap q q' hq y,
        NK.HassePrinciple.localAut_algebraMap (K := F) (NK.GlobalCFT.Place.ofFinite q') σs]
      rw [show (((As : Gal(L/F))) : L ≃ₐ[F] L) = σ.restrictNormal L from
        (show (((As : Gal(L/F))) : L ≃ₐ[F] L) =
            (AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ from rfl).trans rfl]
      exact congrArg (algebraMap M (NK.GlobalCFT.Place.localField M
        (NK.GlobalCFT.Place.ofFinite q')))
        (AlgEquiv.restrictNormal_commutes (E := L) σ y)
  exact congrFun key x

end Equivariance

/-! ## The local level map `v`, and the statements `(G1)` and `(G2)` -/

section LevelMap

variable (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
  (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
  (hq : q.asIdeal = q'.asIdeal.comap
      (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M)))

/-- **The group map of `v`**: the restriction of the local decomposition group at `q'` to the one
at `q` (`stabilizer_restrict_smul_eq`). -/
noncomputable def localStabilizerMap :
    MulAction.stabilizer Gal(M/F) (NK.GlobalCFT.Place.ofFinite q') →*
      MulAction.stabilizer Gal(L/F) (NK.GlobalCFT.Place.ofFinite q) where
  toFun σ :=
    ⟨(AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) σ.1, by
      rw [MulAction.mem_stabilizer_iff]
      exact stabilizer_restrict_smul_eq q q' hq σ.1
        (MulAction.mem_stabilizer_iff.mp σ.2)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' σ τ := Subtype.ext (map_mul _ σ.1 τ.1)

/-- The units map of the tower as a `CoeffInt`-linear map between the local unit groups. -/
noncomputable def localUnitsLinearMap :
    Additive (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q))ˣ →ₗ[
        NK.HassePrinciple.CoeffInt]
      Additive (NK.GlobalCFT.Place.localField M (NK.GlobalCFT.Place.ofFinite q'))ˣ :=
  { toFun := ⇑(Units.map (Commons.RingTheory.Henselian.adicCompletionMap q q'
        (Ideal.LiesOver.mk (by rw [hq]))).toMonoidHom).toAdditive
    map_add' := fun x y => map_add (Units.map (Commons.RingTheory.Henselian.adicCompletionMap q q'
        (Ideal.LiesOver.mk (by rw [hq]))).toMonoidHom).toAdditive x y
    map_smul' := fun n x => by
      obtain ⟨z⟩ := n
      exact AddMonoidHom.map_zsmul (Units.map (Commons.RingTheory.Henselian.adicCompletionMap q q'
        (Ideal.LiesOver.mk (by rw [hq]))).toMonoidHom).toAdditive z x }

end LevelMap

end NK.NUV2.LC
