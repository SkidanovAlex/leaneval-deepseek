/-
# BMAX — `O^p(H·E) ≤ O^p(H)·E` when `H` centralizes `E`

Bender 1970 §1.7 repeatedly uses that, for a subgroup `H` lying in the centralizer of a
subgroup `E`, the `p`-residual of the join `H ⊔ E` is controlled by the `p`-residual of `H`
alone:

  `O^p(H ⊔ E) ≤ O^p(H) ⊔ E`.

Since `H ≤ C_G(E) ≤ N_G(E)` the join is the set product `H · E` (`coe_mul_of_left_le_normalizer_right`),
and the two factors commute elementwise.  So a `p'`-element `x = h·e` of `H · E` can be handled
by the standard "Jordan decomposition" trick: some `p`-power of `h` is a `p'`-element, hence lies in
`O^p(H)`; then `x ^ p^n = h ^ p^n · e ^ p^n ∈ O^p(H) ⊔ E`, and because `p ∤ orderOf x` the
exponent `p ^ n` is coprime to `orderOf x`, so `x` itself is a power of `x ^ p^n`
(`exists_pow_eq_self_of_coprime`) and therefore lies in `O^p(H) ⊔ E`.

`O^p(H ⊔ E)` is the closure of the `p'`-elements of `H ⊔ E`, so `closure_le` finishes the job.

The only ingredient imported from elsewhere is `exists_pow_not_dvd_orderOf` (some `p`-power of
any element of a finite group has `p'`-order), which is the elementary `ordProj`/`ordCompl`
computation of `Submission/Work/BMAX/fstarIn_le_pResidualIn_of_notMem_primesOf.lean`.
-/
import Mathlib
import Submission.Work.BMAX.D17Defs
import Submission.Work.BMAX.fstarIn_le_pResidualIn_of_notMem_primesOf

namespace Work.BMAX

open Subgroup
open Pointwise

/-- If `x ^ k ∈ N` and `k` is coprime to `orderOf x`, then `x ∈ N`: indeed `x` is a power of
`x ^ k` in this case (`exists_pow_eq_self_of_coprime`). -/
theorem mem_of_pow_mem_of_coprime_orderOf {G : Type*} [Group G] {N : Subgroup G} {x : G} {k : ℕ}
    (hk : x ^ k ∈ N) (hcop : k.Coprime (orderOf x)) : x ∈ N := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact N.pow_mem hk m

theorem pResidualIn_sup_le_of_le_centralizer {G : Type} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (H E : Subgroup G)
    (hcomm : H ≤ Subgroup.centralizer (E : Set G)) :
    Work.BMAX.pResidualIn p (H ⊔ E) ≤ Work.BMAX.pResidualIn p H ⊔ E := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxK, hxo⟩
  -- `H ⊔ E = H · E` because `H ≤ C_G(E) ≤ N_G(E)`
  have hnorm : H ≤ Subgroup.normalizer (E : Set G) :=
    le_trans hcomm (Subgroup.centralizer_le_normalizer (E : Set G))
  have hxmem : x ∈ (H : Set G) * (E : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right H E hnorm]
    exact hxK
  obtain ⟨h, hh, e, he, rfl⟩ := hxmem
  -- some `p`-power of `h` is a `p'`-element of `H`
  obtain ⟨n, hn⟩ := Work.BMAX.exists_pow_not_dvd_orderOf p hp h
  have hhp : h ^ (p ^ n) ∈ Work.BMAX.pResidualIn p H :=
    Work.BMAX.pResidualIn.subset_closure (H.pow_mem hh (p ^ n)) hn
  -- `h` and `e` commute, so `(h * e) ^ p^n = h ^ p^n * e ^ p^n ∈ O^p(H) ⊔ E`
  have hce : Commute h e := ((Subgroup.mem_centralizer_iff.mp (hcomm hh)) e he).symm
  have hxpow : (h * e) ^ (p ^ n) ∈ Work.BMAX.pResidualIn p H ⊔ E := by
    rw [hce.mul_pow]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hhp)
      (Subgroup.mem_sup_right (E.pow_mem he (p ^ n)))
  -- `p ^ n` is coprime to `orderOf (h * e)`, so `h * e` is a power of its `p ^ n`-th power
  exact mem_of_pow_mem_of_coprime_orderOf hxpow ((hp.coprime_iff_not_dvd.mpr hxo).pow_left n)

end Work.BMAX
