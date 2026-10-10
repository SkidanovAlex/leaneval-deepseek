import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.Work.SSGRoute.CFTSide.classField_exists_of_index
import Submission.Work.SSGRoute.ZDataMup.onePlace_mem_normImage_of_mem_sup_abelian
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.CycLevel

open scoped NumberField
open NumberField IsDedekindDomain

/-- **The local degree is the index of the local norm group.**

For a finite Galois extension `L/k` of number fields (abelian, i.e. commutative Galois group), a
finite place `Q` of `k` and a place `w` of `L` above `Q`: the cardinality of the stabiliser of `w`
in `Gal(L/k)` equals the index in `k_Qˣ` of the local norm subgroup at `Q`.

Both sides are the local degree `e·f = [L_w : k_Q]`: the stabiliser is the decomposition group of
`w` (order `e·f`), and by the local norm index theorem `[k_Qˣ : N_{L_w/k_Q}L_wˣ] = [L_w : k_Q]`,
while the local norm subgroups of the various `w | Q` coincide because `Gal(L/k)` is abelian. -/
theorem card_stabilizer_eq_of_localNormSubgroup_index {k : Type} [Field k] [NumberField k]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    {L : Type} [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L]
    [IsGalois k L] [IsMulCommutative (L ≃ₐ[k] L)]
    (w : NK.GlobalCFT.Place L)
    (hw : NK.GlobalCFT.Place.LiesOver w (NK.GlobalCFT.Place.ofFinite Q)) :
    Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w) =
      (NK.CFTLib.IdeleHasse.localNormSubgroup (K := k) (L := L)
        (NK.GlobalCFT.Place.ofFinite Q)).index := by
  cases w with
  | inl w' =>
      -- an archimedean place never lies over a nonarchimedean one
      have hf : NK.GlobalCFT.Place.IsFinite (NK.GlobalCFT.Place.ofInfinite w') :=
        (NK.GlobalCFT.Place.isFinite_of_liesOver hw).mpr (by simp)
      exact absurd hf (by simp)
  | inr q =>
      -- the place of `k` below the finite place `q` is `Q`
      obtain ⟨Q', hQ, hqQ⟩ : ∃ Q' : IsDedekindDomain.HeightOneSpectrum
            (NumberField.RingOfIntegers k),
          NK.GlobalCFT.Place.ofFinite Q = NK.GlobalCFT.Place.ofFinite Q' ∧
            q.asIdeal.LiesOver Q'.asIdeal := by
        rcases hw with ⟨w', v', h1, h2, -⟩ | ⟨q', Q'', h1, h2, h3⟩
        · exact absurd h1 (by simp)
        · rw [NK.GlobalCFT.Place.ofFinite_inj] at h1
          subst h1
          exact ⟨Q'', h2, h3⟩
      rw [NK.GlobalCFT.Place.ofFinite_inj] at hQ
      subst hQ
      -- ## The left-hand side is the order of the decomposition group, `e·f`
      have hcard : Nat.card
          (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q)) =
          Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) *
            Q.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L) := by
        have hstab : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q) =
            Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := k) q := by
          ext σ
          rw [MulAction.mem_stabilizer_iff,
            NK.GlobalCFT.Inclusion.globalCFT_mem_decompositionSubgroup_iff,
            NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj]
        rw [hstab]
        exact Commons.NumberTheory.NumberField.Completion.card_decompositionSubgroup Q q hqQ
      -- ## The right-hand side is the index of the local norm group, `e·f`
      have hidx : (NK.CFTLib.IdeleHasse.localNormSubgroup (K := k) (L := L)
          (NK.GlobalCFT.Place.ofFinite Q)).index =
          Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) *
            Q.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L) := by
        -- the local field `L_q` as a `k_Q`-algebra, with the instance used by the local CFT API
        letI hAlg : Algebra (Q.adicCompletion k) (q.adicCompletion L) :=
          Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q q hqQ
        -- the local Galois group is commutative: it is the (commutative) global decomposition group
        have hcomm : ∀ a b : (q.adicCompletion L) ≃ₐ[Q.adicCompletion k] (q.adicCompletion L),
            a * b = b * a := by
          intro a b
          let e := Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
            (K := k) (L := L) Q q hqQ
          have hinner : e.symm a * e.symm b = e.symm b * e.symm a := by
            refine Subtype.ext ?_
            exact mul_comm' _ _
          exact e.symm.injective (by rw [map_mul, map_mul]; exact hinner)
        -- the local norm subgroup is the norm group of the local extension
        have hnorm : NK.CFTLib.IdeleHasse.localNormSubgroup (K := k) (L := L)
            (NK.GlobalCFT.Place.ofFinite Q) =
            NK.LocalReciprocity.normGroup (Q.adicCompletion k) (q.adicCompletion L) :=
          Work.SSGRoute.ZDataMup.localNormSubgroup_ofFinite_eq_normGroup Q q hqQ
        rw [hnorm]
        -- local norm index theorem, then the local degree is `e·f`
        exact (NK.LocalReciprocity.index_normGroup_eq_finrank Q q hcomm).trans
          (Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ef' Q q hqQ)
      rw [hcard, hidx]

end Work.SSGRoute.CycLevel
