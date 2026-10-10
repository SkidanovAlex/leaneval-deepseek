import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Topology.Algebra.ProperAction.Basic
import Submission.Work.SSGRoute.PTW.CompactAbelianExponentP
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Divisibility of a compact connected abelian topological group

A compact Hausdorff connected abelian topological group is divisible: for every `p ≠ 0` and every
`x` there is `y` with `y ^ p = x`.

The proof reduces to prime exponents.  For a prime `q`, put `N := (powMonoidHom q).range = qG`
and `Q := G ⧸ N`; then `Q` is a compact Hausdorff abelian group of exponent `q`.  If `x ∉ N` the
separation theorem `exists_open_index_p_notMem_of_compact_abelian_exponent_p` yields an open
subgroup `U ≤ Q` of index `q` with `x̄ ∉ U`; pulling back along the quotient map gives an open
subgroup of `G` of index `q` avoiding `x`.  But an open subgroup is clopen, hence contains the
connected component of the identity (`IsClopen.connectedComponent_subset`), so it is all of `G`
because `G` is connected — contradiction.  So `x ∈ qG`.

An arbitrary nonzero exponent is then handled by stripping one prime factor at a time.
-/

namespace Work.SSGRoute.PTW

set_option linter.style.haveILetI false

theorem compact_connected_abelian_pow_surjective (G : Type*) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [ConnectedSpace G] (p : ℕ) (hp : p ≠ 0)
    (x : G) : ∃ y : G, y ^ p = x := by
  -- Step 1: the statement for prime exponents.
  have prime_case : ∀ (q : ℕ), Nat.Prime q → ∀ x : G, ∃ y : G, y ^ q = x := by
    intro q hq x
    by_contra hcon
    have hcon' : ∀ y : G, y ^ q ≠ x := fun y hy => hcon ⟨y, hy⟩
    haveI : Fact (Nat.Prime q) := ⟨hq⟩
    set N : Subgroup G := (powMonoidHom q).range with hN
    have hpc : Continuous (⇑(powMonoidHom q) : G → G) := by
      have hfun : (⇑(powMonoidHom q) : G → G) = fun g : G => g ^ q := by
        funext g; exact powMonoidHom_apply q g
      rw [hfun]; exact continuous_id.pow q
    have hNclosed : IsClosed (N : Set G) := by
      rw [hN, MonoidHom.coe_range]
      exact (isCompact_range hpc).isClosed
    haveI : IsClosed (N : Set G) := hNclosed
    haveI : T2Space (G ⧸ N) := inferInstance
    have hexp : ∀ z : G ⧸ N, z ^ q = 1 := by
      intro z
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N z
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact MonoidHom.mem_range.mpr ⟨g, (powMonoidHom_apply q g).symm⟩
    have hxN : (QuotientGroup.mk' N) x ≠ 1 := by
      intro h
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      rw [hN] at h
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp h
      exact hcon' y (by rw [← hy, powMonoidHom_apply])
    obtain ⟨U, hUopen, hUindex, hUx⟩ :=
      exists_open_index_p_notMem_of_compact_abelian_exponent_p (G ⧸ N) q hexp
        ((QuotientGroup.mk' N) x) hxN
    refine hUx ?_
    have hVopen : IsOpen ((U.comap (QuotientGroup.mk' N) : Subgroup G) : Set G) :=
      hUopen.preimage QuotientGroup.continuous_mk
    have hle : Subgroup.connectedComponentOfOne G ≤ U.comap (QuotientGroup.mk' N) :=
      fun _ hx => (IsClopen.connectedComponent_subset
        ⟨Subgroup.isClosed_of_isOpen (U.comap (QuotientGroup.mk' N)) hVopen, hVopen⟩
        (U.comap (QuotientGroup.mk' N)).one_mem) hx
    have hxcc : x ∈ Subgroup.connectedComponentOfOne G := by
      change x ∈ connectedComponent (1 : G)
      rw [PreconnectedSpace.connectedComponent_eq_univ (1 : G)]
      exact Set.mem_univ x
    exact hle hxcc
  -- Step 2: strip a prime factor and use strong induction on the exponent.
  have key : ∀ n : ℕ, n ≠ 0 → ∀ x : G, ∃ y : G, y ^ n = x := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn x
      rcases eq_or_ne n 1 with h1 | hne1
      · subst h1
        exact ⟨x, pow_one x⟩
      · obtain ⟨q, hq, hqdiv⟩ := Nat.exists_prime_and_dvd hne1
        obtain ⟨z, hz⟩ := prime_case q hq x
        set m : ℕ := n / q with hm
        have hqm : q * m = n := by rw [hm, Nat.mul_div_cancel' hqdiv]
        have hm_lt : m < n := by
          rw [hm]
          exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) hq.one_lt
        have hm_ne : m ≠ 0 := fun h0 => by
          rw [h0, mul_zero] at hqm
          exact hn hqm.symm
        obtain ⟨w, hw⟩ := ih m hm_lt hm_ne z
        refine ⟨w, ?_⟩
        rw [show n = m * q from by rw [← hqm, mul_comm], pow_mul, hw, hz]
  exact key p hp x

end Work.SSGRoute.PTW
