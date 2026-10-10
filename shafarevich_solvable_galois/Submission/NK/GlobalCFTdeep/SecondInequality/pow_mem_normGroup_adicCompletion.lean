import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois_coe
import Submission.NK.LocalReciprocity.index_normGroup_eq_finrank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `p`-th powers of local units are local norms

Let `L / K` be a finite Galois extension of number fields whose Galois group has prime order `p`.
For a finite place `Q` of `K` and a place `q` of `L` above `Q`, the local extension
`L_q / K_Q` of the `q`-adic completion over the `Q`-adic completion is Galois with Galois group
isomorphic to the decomposition subgroup `D_q ≤ Gal(L/K)`; in particular `Gal(L_q/K_Q)` is
cyclic of order dividing `p`, hence commutative.  The norm index theorem of local class field
theory (the abelian case, `NK.LocalReciprocity.index_normGroup_eq_finrank`) then gives

  `[(K_Q)ˣ : N_{L_q/K_Q} (L_q)ˣ] = [L_q : K_Q]`,

and `[L_q : K_Q] = #D_q` divides `#Gal(L/K) = p`.  Hence the quotient of the local units by the
norm group has order dividing `p`, so every `p`-th power of a local unit is a norm.

This is the local input of the second inequality of global class field theory in the case of a
cyclic extension of prime degree.
-/

namespace NK.GlobalCFTdeep.SecondInequality

theorem pow_mem_normGroup_adicCompletion {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] {p : ℕ} (hp : p.Prime) (hcard : Nat.card (L ≃ₐ[K] L) = p) (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) [hq : q.asIdeal.LiesOver Q.asIdeal] (x : (Q.adicCompletion K)ˣ) : x ^ p ∈ NK.LocalReciprocity.normGroup (Q.adicCompletion K) (q.adicCompletion L) := by
  -- the local extension `L_q / K_Q` is finite and Galois
  haveI hfin : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Submission.NeukirchUchida.Local.isGalois_adicCompletion Q q hq
  -- the global Galois group has prime order, hence is cyclic, hence commutative
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hcyc : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_card_dvd_prime (p := p) (hcard.symm ▸ dvd_rfl)
  have hcommGal : ∀ a b : L ≃ₐ[K] L, a * b = b * a :=
    fun a b => hcyc.isMulCommutative.is_comm.comm a b
  -- the decomposition group is identified with the local Galois group, so the latter is
  -- commutative as well
  have hcomm : ∀ a b : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      a * b = b * a := by
    intro a b
    let e : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q ≃*
        (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
      Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois Q q hq
    have hD : ∀ δ ε : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q,
        δ * ε = ε * δ := fun δ ε => Subtype.ext (hcommGal (δ : L ≃ₐ[K] L) (ε : L ≃ₐ[K] L))
    calc a * b = e (e.symm a * e.symm b) := by
          rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      _ = e (e.symm b * e.symm a) := by rw [hD]
      _ = b * a := by
          rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  -- local norm index theorem (abelian case): the index is the local degree
  have hidx := NK.LocalReciprocity.index_normGroup_eq_finrank (K := K) (L := L) Q q hcomm
  -- the local degree is the order of the decomposition group, which divides `p`
  have hcard_loc : Nat.card (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      = Nat.card (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q) :=
    (Nat.card_congr (Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
      Q q hq).toEquiv).symm
  have hfin_loc : Nat.card (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      = Module.finrank (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_finrank Q q hq
  have hdvd : (NK.LocalReciprocity.normGroup (Q.adicCompletion K) (q.adicCompletion L)).index ∣ p := by
    rw [hidx, ← hfin_loc, hcard_loc, ← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  -- every `index`-th power is a norm, and `index ∣ p`
  have hpow : x ^ (NK.LocalReciprocity.normGroup (Q.adicCompletion K) (q.adicCompletion L)).index ∈
      NK.LocalReciprocity.normGroup (Q.adicCompletion K) (q.adicCompletion L) :=
    Subgroup.pow_index_mem _ x
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, pow_mul]
  exact pow_mem hpow k

end NK.GlobalCFTdeep.SecondInequality
