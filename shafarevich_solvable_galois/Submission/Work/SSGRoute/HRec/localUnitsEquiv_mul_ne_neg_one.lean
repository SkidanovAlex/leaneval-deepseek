import Mathlib
import Submission.Work.sha2_hasse.exists_norm_witness_infinitePlace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean positivity computation

At an *infinite* place `v` of a finite Galois extension `L/k` of number fields, a nontrivial
element `σ` of the decomposition group of `v` acts on the local field `L_v = ℂ` by complex
conjugation; hence `z * (σ • z) ≠ -1` for every local unit `z`, because `z * conj z = |z|² ≥ 0`.

This is the local faithfulness of the Kummer coefficient map `μ₂ ↪ L_vˣ` at an archimedean place:
it is what makes the Kummer pushforward of the level cup class nonzero exactly at the archimedean
places where the cup class is nonzero (see `Work.SSGRoute.HRec.cupKummer_archMatchK`).
-/

open NumberField

noncomputable section

namespace Work.SSGRoute.HRec

theorem localUnitsEquiv_mul_ne_neg_one {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (v : NumberField.InfinitePlace L)
    (σ : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite v)) (hσ : σ ≠ 1)
    (z : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite v))ˣ) :
    z * NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
        (NK.GlobalCFT.Place.ofInfinite v) σ z ≠ -1 := by
  classical
  set γ : L ≃ₐ[k] L := (σ : L ≃ₐ[k] L) with hγ
  have hγσ : γ = (σ : L ≃ₐ[k] L) := hγ
  have hσ' : γ ≠ 1 := by
    rw [hγσ]
    exact fun h => hσ (Subtype.ext h)
  -- `γ` lies in the stabiliser of the infinite place `v` itself
  have hmem : γ ∈ MulAction.stabilizer (L ≃ₐ[k] L) v := by
    rw [hγσ, MulAction.mem_stabilizer_iff]
    have h := MulAction.mem_stabilizer_iff.mp σ.2
    rwa [NK.GlobalCFT.Place.smul_ofInfinite, NK.GlobalCFT.Place.ofInfinite_inj] at h
  -- hence `v` is not real: a real place is unramified and has trivial stabiliser
  have hcomplex : v.IsComplex := by
    rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
    intro hreal
    have hunr : NumberField.InfinitePlace.IsUnramified k v :=
      NumberField.InfinitePlace.isUnramified_iff.mpr (Or.inl hreal)
    have hbot : MulAction.stabilizer (L ≃ₐ[k] L) v = ⊥ :=
      NumberField.InfinitePlace.IsUnramified.stabilizer_eq_bot (k := k) hunr
    rw [hbot] at hmem
    exact hσ' (Subgroup.mem_bot.mp hmem)
  -- `γ` acts by complex conjugation with respect to the embedding `v.embedding`
  have hconj : NumberField.ComplexEmbedding.IsConj (k := k) v.embedding γ := by
    have hkey : γ ∈ MulAction.stabilizer (L ≃ₐ[k] L)
        (NumberField.InfinitePlace.mk v.embedding) := by
      rw [NumberField.InfinitePlace.mk_embedding v]
      exact hmem
    have h := (NumberField.InfinitePlace.mem_stabilizer_mk_iff (k := k) v.embedding γ).mp hkey
    rcases h with h1 | h2
    · exact absurd h1 hσ'
    · exact h2
  -- the local action of `σ` is the complex conjugation under the identification with `ℂ`
  have hloc : ∀ y : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite v),
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hcomplex
          (NK.HassePrinciple.localAutHom (K := k) (L := L)
            (NK.GlobalCFT.Place.ofInfinite v) σ y) =
        starRingEnd ℂ
          (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hcomplex y) :=
    Work.sha2_hasse.localAutHom_ringEquivComplex (K := k) (L := L) v hcomplex σ
      (fun x => by
        rw [hγσ] at hconj
        exact hconj.eq x)
  intro h
  set e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hcomplex
    with he
  -- the value of `σ • z` in `ℂ` is the complex conjugate of the value of `z`
  have hval : e (((NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
        (NK.GlobalCFT.Place.ofInfinite v) σ z :
        (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite v))ˣ) :
        NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite v))) =
      starRingEnd ℂ (e (z : NK.GlobalCFT.Place.localField L
        (NK.GlobalCFT.Place.ofInfinite v))) := by
    rw [NK.HassePrinciple.coe_localUnitsEquiv]
    exact hloc _
  have h1 : e (z : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite v)) *
      starRingEnd ℂ (e (z : NK.GlobalCFT.Place.localField L
        (NK.GlobalCFT.Place.ofInfinite v))) = -1 := by
    -- transport the unit equation to `ℂˣ` with `Units.map e`
    have h2 : Units.map e.toMonoidHom (z * NK.HassePrinciple.localUnitsEquiv (K := k)
          (L := L) (NK.GlobalCFT.Place.ofInfinite v) σ z) =
        Units.map e.toMonoidHom (-1 :
          (NK.GlobalCFT.Place.localField L
            (NK.GlobalCFT.Place.ofInfinite v))ˣ) := congrArg _ h
    rw [map_mul] at h2
    have h3 : e (z : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite v)) *
        e (((NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
          (NK.GlobalCFT.Place.ofInfinite v) σ z :
          (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite v))ˣ) :
          NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite v))) = -1 := by
      have h4 : (((z * NK.HassePrinciple.localUnitsEquiv (K := k) (L := L)
          (NK.GlobalCFT.Place.ofInfinite v) σ z :
          (NK.GlobalCFT.Place.localField L
            (NK.GlobalCFT.Place.ofInfinite v))ˣ) :
          NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite v))) =
          ((-1 : (NK.GlobalCFT.Place.localField L
            (NK.GlobalCFT.Place.ofInfinite v))ˣ) :
          NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite v)) :=
        congrArg _ h
      rw [_root_.Units.val_mul, _root_.Units.val_neg, _root_.Units.val_one] at h4
      have h5 := congrArg e h4
      rw [map_mul, map_neg, map_one] at h5
      exact h5
    rw [hval] at h3
    exact h3
  have hnorm : ((Complex.normSq (e (z : NK.GlobalCFT.Place.localField L
      (NK.GlobalCFT.Place.ofInfinite v))) : ℝ) : ℂ) = -1 := by
    rw [← Complex.mul_conj, ← Complex.star_def]
    exact h1
  have hreal : Complex.normSq (e (z : NK.GlobalCFT.Place.localField L
      (NK.GlobalCFT.Place.ofInfinite v))) = -1 := by
    exact_mod_cast hnorm
  have hnonneg := Complex.normSq_nonneg (e (z : NK.GlobalCFT.Place.localField L
    (NK.GlobalCFT.Place.ofInfinite v)))
  linarith

end Work.SSGRoute.HRec
