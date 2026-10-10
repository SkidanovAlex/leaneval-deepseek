import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero

namespace NK.GlobalCFTdeep

open NK.GlobalCFT


/-- **The local norm group contains the `[L_q : K_Q]`-th powers.**

For a finite extension `L / K` of number fields and places `q | Q`, the norm of an element of the
base field is its degree-th power (`Algebra.norm_algebraMap`), so
`(K_Qˣ)^[L_q:K_Q] ⊆ N_{L_q/K_Q}(L_qˣ)`.

This is the elementary local input that makes the norm index of a finite extension of number
fields finite: at the (finitely many) ramified places the norm group contains a power subgroup,
and at all other places the extension is unramified, so the norm is surjective on units. -/
theorem pow_finrank_mem_localNormFinite {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      (Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toAlgebra
    ∀ a : (Q.adicCompletion K)ˣ,
      a ^ Module.finrank (Q.adicCompletion K) (q.adicCompletion L) ∈
        (NK.GlobalCFT.Place.localNormFinite q Q hq).range := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    (Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toAlgebra
  intro a
  refine ⟨Units.map ((algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom) a, ?_⟩
  rw [NK.GlobalCFT.Place.localNormFinite]
  apply Units.ext
  simp only [Units.coe_map]
  simpa using Algebra.norm_algebraMap (R := Q.adicCompletion K) (S := q.adicCompletion L)
    (x := (a : Q.adicCompletion K))

/-- **The group-theoretic core of the tower inequality**, conditional on the finiteness of the
norm index of the *upper* extension `L / K'`.

With `f := IdeleClassGroup.normClassHom K K' : C[K'] →* C[K]`,
`A := Idele.normClassSubgroup K L`, `B := Idele.normClassSubgroup K K'` and
`A' := Idele.normClassSubgroup K' L`, transitivity of the norm
(`NormGroup.globalCFT_normClassHom_trans`) gives `A = A'.map f` and `B = ⊤.map f = f.range`, hence
`A ≤ B`.  Then

* `A.index = A.relIndex B * B.index` (`Subgroup.relIndex_mul_index`),
* `A.relIndex B = (A'.map f).relIndex (⊤.map f) = (A' ⊔ f.ker).relIndex ⊤ = (A' ⊔ f.ker).index`
  (`Subgroup.relIndex_map_map`, `Subgroup.relIndex_top_right`),
* and `(A' ⊔ f.ker).index ≤ A'.index` because `A' ≤ A' ⊔ f.ker` and `A'` has finite index
  (`Subgroup.index_antitone`).

This is the only place where the finiteness of the index of `A'` is used: with `Nat.card`-based
indices the inequality `(A' ⊔ f.ker).index ≤ A'.index` fails for a general subgroup inclusion
`A' ≤ A' ⊔ f.ker` when `A'.index = 0` (e.g. `A' = {0} × ℤ ≤ ℤ × ℤ = A' ⊔ f.ker` with
`f.ker = ℤ × {0}`: `A'.index = 0` but `(A' ⊔ f.ker).index = 1`), so the finiteness of the norm
index of `L / K'` is an essential hypothesis of the group-theoretic argument. -/
theorem index_normClassSubgroup_le_mul_index_of_finiteIndex {K K' L : Type} [Field K]
    [NumberField K] [Field K'] [NumberField K'] [Field L] [NumberField L]
    [Algebra K K'] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
    [FiniteDimensional K K'] [FiniteDimensional K' L] [FiniteDimensional K L]
    (hfin : (Idele.normClassSubgroup K' L).FiniteIndex) :
    (Idele.normClassSubgroup K L).index ≤
      (Idele.normClassSubgroup K K').index * (Idele.normClassSubgroup K' L).index := by
  haveI : (Idele.normClassSubgroup K' L).FiniteIndex := hfin
  have hcomp : IdeleClassGroup.normClassHom K L =
      (IdeleClassGroup.normClassHom K K').comp (IdeleClassGroup.normClassHom K' L) :=
    MonoidHom.ext fun q => (NormGroup.globalCFT_normClassHom_trans q).symm
  have hA : Idele.normClassSubgroup K L =
      (Idele.normClassSubgroup K' L).map (IdeleClassGroup.normClassHom K K') := by
    rw [Idele.normClassSubgroup_eq_range (K := K) (L := L),
      Idele.normClassSubgroup_eq_range (K := K') (L := L), hcomp, MonoidHom.range_comp]
  have hB : Idele.normClassSubgroup K K' =
      (⊤ : Subgroup (IdeleClassGroup K')).map (IdeleClassGroup.normClassHom K K') := by
    rw [Idele.normClassSubgroup_eq_range (K := K) (L := K'), MonoidHom.range_eq_map]
  have hle : Idele.normClassSubgroup K L ≤ Idele.normClassSubgroup K K' := by
    rw [hA, hB]
    exact Subgroup.map_mono le_top
  have hrel : (Idele.normClassSubgroup K L).relIndex (Idele.normClassSubgroup K K') ≤
      (Idele.normClassSubgroup K' L).index := by
    rw [hA, hB, Subgroup.relIndex_map_map (IdeleClassGroup.normClassHom K K')]
    simp only [top_sup_eq, Subgroup.relIndex_top_right]
    exact Subgroup.index_antitone le_sup_left
  calc (Idele.normClassSubgroup K L).index
      = (Idele.normClassSubgroup K L).relIndex (Idele.normClassSubgroup K K') *
        (Idele.normClassSubgroup K K').index := (Subgroup.relIndex_mul_index hle).symm
    _ ≤ (Idele.normClassSubgroup K' L).index * (Idele.normClassSubgroup K K').index :=
        Nat.mul_le_mul_right _ hrel
    _ = (Idele.normClassSubgroup K K').index * (Idele.normClassSubgroup K' L).index :=
        Nat.mul_comm _ _

/-- **Tower inequality for norm class subgroups.** For a tower `K ⊆ K' ⊆ L` of number fields
(no Galois-ness or normality assumptions), the index of the norm class subgroup of `L/K` is
bounded by the product of the two indices of the intermediate extensions.

Proof sketch (group-theoretic only): put `f := IdeleClassGroup.normClassHom K K' : C[K'] →* C[K]`
and `A := normClassSubgroup K L`, `B := normClassSubgroup K K'`, `A' := normClassSubgroup K' L`.
By transitivity of the norm (`NormGroup.globalCFT_normClassHom_trans`) one has
`A = A'.map f` and `B = ⊤.map f = f.range`, so `A ≤ B`.  Then
`A.index = A.relIndex B * B.index` (`Subgroup.relIndex_mul_index`), and
`A.relIndex B = (A'.map f).relIndex (⊤.map f) = (A' ⊔ f.ker).relIndex (⊤ ⊔ f.ker)` by
`Subgroup.relIndex_map_map`, which is `(A' ⊔ f.ker).index`.  Since `A' ≤ A' ⊔ f.ker`, the
conclusion follows either from `Subgroup.index_dvd_of_le` (careful: `Nat.card`-based indices
vanish on infinite quotients; the surjection
`C[K'] ⧸ A' ↠ (A' ⊔ f.ker) ⧸ A'` plus `Nat.card_le_card_of_surjective` is a safe alternative). -/
theorem index_normClassSubgroup_le_mul_index {K K' L : Type} [Field K] [NumberField K]
    [Field K'] [NumberField K'] [Field L] [NumberField L]
    [Algebra K K'] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
    [FiniteDimensional K K'] [FiniteDimensional K' L] [FiniteDimensional K L] :
    (NK.GlobalCFT.Idele.normClassSubgroup K L).index ≤
      (NK.GlobalCFT.Idele.normClassSubgroup K K').index *
        (NK.GlobalCFT.Idele.normClassSubgroup K' L).index :=
  index_normClassSubgroup_le_mul_index_of_finiteIndex
    (Subgroup.finiteIndex_iff.mpr (normClassSubgroup_index_ne_zero (K := K') (L := L)))

end NK.GlobalCFTdeep
