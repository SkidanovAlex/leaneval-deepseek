import Mathlib
import Submission.Work.SSGRoute.CycLevel.LevelData
import Submission.Work.SSGRoute.CycLevel.GrunwaldImports
import Submission.Work.SSGRoute.CFTSide.classField_exists_of_index
import Submission.Work.SSGRoute.CycLevel.grunwald_odd_single_place
import Submission.Work.SSGRoute.PTW.mem_pthPower_of_all_open_index_p_subgroups
import Submission.Work.SSGRoute.CycLevel.localNormSubgroup_eq_preimage_normClass
import Submission.Work.SSGRoute.CycLevel.levelData_of_abstract_level
import Submission.Work.SSGRoute.CycLevel.card_stabilizer_eq_of_localNormSubgroup_index
import Submission.Work.SSGRoute.CycLevel.index_comap_onePlace_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.CycLevel

/-- **The odd Grünwald step at a single place, open-subgroup form.**

For a number field `k`, a finite place `v₀` and an odd prime `q` there is an *open* subgroup
`V ≤ C_k` of index `q` such that some one-place idèle class at `v₀` lies outside `V`: concretely,
the class of the uniformiser at `v₀` does.  Equivalently, `C_k ⧸ V` is cyclic of order `q` and the
image of the local group `k_{v₀}ˣ` in it is non-trivial.

This is the `S = {v₀}` case of Grünwald's result for odd `q`.  It is deduced here from the
class-field-theoretic form `grunwald_odd_single_place` by the `p`-power criterion in the idèle class
group: the class of the local uniformiser is not a `q`-th power in `C_k`
(`not_pow_onePlace_of_not_pow`), so it fails to lie in some open index-`q` subgroup
(`Work.SSGRoute.PTW.mem_pthPower_of_all_open_index_p_subgroups`). -/
theorem grunwald_open_unifUnit (k : Type) [Field k] [NumberField k]
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (q : ℕ) (hq : q.Prime) (hq2 : 2 < q) :
    ∃ V : Subgroup (NK.GlobalCFT.IdeleClassGroup k),
      V.FiniteIndex ∧ IsOpen (V : Set (NK.GlobalCFT.IdeleClassGroup k)) ∧ V.index = q ∧
        ∃ x : (NK.GlobalCFT.Place.localField k (NK.GlobalCFT.Place.ofFinite v₀))ˣ,
          NK.GlobalCFT.IdeleClassGroup.mk k
            (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite v₀) x) ∉ V := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hnot : ¬ ∃ y : NK.GlobalCFT.IdeleClassGroup k,
      y ^ q = NK.GlobalCFT.IdeleClassGroup.mk k
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite v₀)
          (NK.GlobalCFT.IdeleClassGroup.unifUnit k v₀)) :=
    not_pow_onePlace_of_not_pow k v₀ q hq hq2 (NK.GlobalCFT.IdeleClassGroup.unifUnit k v₀)
      (unifUnit_not_pow k v₀ q hq hq2)
  by_contra hcon
  obtain ⟨y, hy⟩ := Work.SSGRoute.PTW.mem_pthPower_of_all_open_index_p_subgroups k q
    (NK.GlobalCFT.IdeleClassGroup.mk k
      (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite v₀)
        (NK.GlobalCFT.IdeleClassGroup.unifUnit k v₀)))
    (fun V h1 h2 h3 => by
      by_contra hmem
      exact hcon ⟨V, h1, h2, h3,
        ⟨NK.GlobalCFT.IdeleClassGroup.unifUnit k v₀, hmem⟩⟩)
  exact hnot ⟨y, hy⟩

/-- **The odd Grünwald step at a single place, prime level.**

For a number field `k`, an odd prime `q` and *any* finite place `v₀` there is a cyclic level of
`q`-power degree with `v₀` of full local degree and `q^1` dividing the order. -/
theorem prime_level_single_place (k : Type) [Field k] [NumberField k]
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (q : ℕ) (hq : q.Prime) (hq2 : 2 < q) :
    Nonempty (LevelData k q 1 v₀) := by
  classical
  -- ## Step 1: the odd Grünwald step at `v₀`, in subgroup form
  obtain ⟨V, hVfin, hVopen, hVidx, x, hx⟩ := grunwald_open_unifUnit k v₀ q hq hq2
  -- ## Step 2: the existence theorem of class field theory produces the level over `k`
  obtain ⟨L, hFL, hNL, hAL, hfdL, hGalL, hNormL, hrankL⟩ :=
    Work.SSGRoute.CFTSide.classField_exists_of_index (K := k) q hq.pos V hVfin hVopen hVidx
  letI : Field L := hFL
  letI : NumberField L := hNL
  letI : Algebra k L := hAL
  letI : FiniteDimensional k L := hfdL
  haveI : IsGalois k L := hGalL
  -- `Gal(L/k)` has `q` elements, hence is cyclic of order `q`
  have hNcard : Nat.card (L ≃ₐ[k] L) = q := by
    rw [IsGalois.card_aut_eq_finrank k L, hrankL]
  haveI : Fact q.Prime := ⟨hq⟩
  have hcyc : IsCyclic (L ≃ₐ[k] L) := isCyclic_of_prime_card hNcard
  letI : CommGroup (L ≃ₐ[k] L) := IsCyclic.commGroup
  haveI : IsMulCommutative (L ≃ₐ[k] L) := IsMulCommutative.mk ⟨fun a b => mul_comm a b⟩
  -- ## Step 3: `v₀` has full local degree in `L/k`
  have hloc : ∀ w : NK.GlobalCFT.Place L,
      NK.GlobalCFT.Place.LiesOver w (NK.GlobalCFT.Place.ofFinite v₀) →
        Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w) = Nat.card (L ≃ₐ[k] L) := by
    intro w hw
    -- the stabiliser has the cardinality of the local norm index
    rw [card_stabilizer_eq_of_localNormSubgroup_index v₀ w hw, hNcard]
    -- the local norm subgroup is the preimage of `V` under the one-place map
    have hsub : NK.CFTLib.IdeleHasse.localNormSubgroup (K := k) (L := L)
          (NK.GlobalCFT.Place.ofFinite v₀) =
        Subgroup.comap ((NK.GlobalCFT.IdeleClassGroup.mk k).comp
          (NK.CFTLib.IdeleHasse.onePlaceHom (NK.GlobalCFT.Place.ofFinite v₀))) V := by
      refine SetLike.ext fun a => ?_
      rw [hNormL.symm, Subgroup.mem_comap]
      exact (localNormSubgroup_eq_preimage_normClass (L := L) v₀ a).symm
    rw [hsub]
    -- the index of that preimage is `q` since the local image escapes `V`
    exact index_comap_onePlace_eq k v₀ q hq V hVidx x hx
  -- ## Step 4: package the abstract level into a subfield of `AlgebraicClosure k`
  exact levelData_of_abstract_level k v₀ q L hcyc ⟨1, by rw [hNcard, pow_one]⟩
    (by rw [hNcard]) hloc

end Work.SSGRoute.CycLevel
