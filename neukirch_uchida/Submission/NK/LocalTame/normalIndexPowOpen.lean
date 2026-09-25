import Mathlib
import Submission.NK.LocalTame.lFrattini_isOpen
import Submission.NK.LocalTame.normalIndexPrimeOpen_of_openNormal
import Submission.NK.LocalTame.exists_normal_le_index_prime

/-!
# Normal subgroups of `ℓ`-power index in a compact group are open

Let `G` be a compact Hausdorff topological group and `ℓ` a prime, and suppose that every
*normal* subgroup of `G` of index `ℓ` is open (`hopen`).  Then every normal subgroup of `G`
whose index is a power of `ℓ` is open.

## Strategy

Strong induction on the exponent `k` of `N.index = ℓ ^ k`.

* `k = 0`: the index is `1`, so `N = ⊤` is open.
* `k ≥ 1`: choose (via `NK.LocalTame.exists_normal_le_index_prime`) a normal subgroup
  `M` with `N ≤ M` and `[G : M] = ℓ`; it is open by `hopen`.  The descent step
  `NK.LocalTame.normalIndexPrimeOpen_of_openNormal` shows that *every* normal subgroup of
  `M` of index `ℓ` is open in `M` — this is where the `ℓ`-Frattini of `M` is shown to have
  finite index (Baire category, `NK.LocalTame.IndexRedo`).  Since `[M : N] = ℓ ^ (k-1)`,
  the induction hypothesis applied inside the compact Hausdorff group `M` gives that `N` is
  open in `M`, and `M` is open in `G`, so `N` is open in `G`.

This shows that the hypothesis "every normal subgroup of index `ℓ` is open" bootstraps to all
`ℓ`-power indices.  (It is genuinely needed: for a general compact Hausdorff group a
finite-index subgroup need not be open, as `∏ ℤ/ℓ` shows.)
-/

namespace NK.LocalTame

open Subgroup

/-- The strong-induction form of `normalIndexPowOpen`, universally quantified over the group so
that the induction hypothesis can be applied to open subgroups. -/
theorem normalIndexPowOpen_aux (k : ℕ) :
    ∀ {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
      [T2Space G] {ℓ : ℕ}, ℓ.Prime →
      (∀ H : Subgroup G, H.index = ℓ → H.Normal → IsOpen (H : Set G)) →
      ∀ N : Subgroup G, N.Normal → N.index = ℓ ^ k → IsOpen (N : Set G) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro G _ _ _ _ _ ℓ hℓ hopen N hN hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- index one: `N = ⊤`
      subst hk0
      rw [pow_zero] at hk
      rw [Subgroup.index_eq_one.mp hk]
      exact isOpen_univ
    · -- a normal subgroup `M` with `N ≤ M` and `[G : M] = ℓ`
      obtain ⟨M, hNM, hMN, hMi⟩ := exists_normal_le_index_prime hℓ N hN hk hkpos
      haveI hMn : M.Normal := hMN
      haveI hNn : N.Normal := hN
      have hMo : IsOpen (M : Set G) := hopen M hMi hMN
      haveI hMc : CompactSpace M :=
        isCompact_iff_compactSpace.mp (M.isClosed_of_isOpen hMo).isCompact
      -- every normal subgroup of `M` of index `ℓ` is open in `M`
      have hopenM : ∀ P : Subgroup M, P.index = ℓ → P.Normal → IsOpen (P : Set M) :=
        fun P hP hPN => normalIndexPrimeOpen_of_openNormal hℓ hopen M hMN hMo hMi P hPN hP
      have hlt : k - 1 < k := Nat.sub_lt hkpos (by norm_num)
      -- the index of `N` in `M`
      have hidx : (N.subgroupOf M).index = ℓ ^ (k - 1) := by
        have hrel : (N.subgroupOf M).index * M.index = N.index := Subgroup.relIndex_mul_index hNM
        rw [hMi, hk] at hrel
        have hpow : ℓ ^ (k - 1) * ℓ = ℓ ^ k := by
          rw [← pow_succ]
          congr 1
          omega
        exact Nat.mul_right_cancel hℓ.pos (by rw [hrel, hpow])
      -- induction hypothesis inside `M`
      have hopenN : IsOpen (N.subgroupOf M : Set M) :=
        ih (k - 1) hlt (ℓ := ℓ) hℓ hopenM (N.subgroupOf M) inferInstance hidx
      -- transport openness from the open subgroup `M` back to `G`
      have hind : Topology.IsInducing (Subtype.val : M → G) := ⟨rfl⟩
      have heq : (Subtype.val : M → G) ⁻¹' (N : Set G) = ((N.subgroupOf M : Subgroup M) : Set M) := by
        ext m
        simp [Subgroup.mem_subgroupOf]
      have hpre : IsOpen ((Subtype.val : M → G) ⁻¹' (N : Set G)) := by rw [heq]; exact hopenN
      obtain ⟨V, hVopen, hVeq⟩ := (Topology.IsInducing.isOpen_iff hind).mp hpre
      have hN_eq : (N : Set G) = V ∩ (M : Set G) := by
        ext g
        constructor
        · intro hg
          refine ⟨?_, hNM hg⟩
          have hmem : (⟨g, hNM hg⟩ : M) ∈ (Subtype.val : M → G) ⁻¹' (N : Set G) := hg
          rw [← hVeq] at hmem
          exact hmem
        · rintro ⟨hgV, hgM⟩
          have hmem : (⟨g, hgM⟩ : M) ∈ (Subtype.val : M → G) ⁻¹' V := hgV
          rw [hVeq] at hmem
          exact hmem
      rw [hN_eq]
      exact hVopen.inter hMo

/-- **Normal subgroups of `ℓ`-power index are open.**

Let `G` be a compact Hausdorff topological group and `ℓ` a prime, and suppose that every
*normal* subgroup of `G` of index `ℓ` is open.  Then every normal subgroup of `G` of
`ℓ`-power index is open. -/
theorem normalIndexPowOpen {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hopen : ∀ H : Subgroup G, H.index = ℓ → H.Normal → IsOpen (H : Set G))
    (N : Subgroup G) (hN : N.Normal) (k : ℕ) (hk : N.index = ℓ ^ k) : IsOpen (N : Set G) :=
  normalIndexPowOpen_aux k hℓ hopen N hN hk

end NK.LocalTame
