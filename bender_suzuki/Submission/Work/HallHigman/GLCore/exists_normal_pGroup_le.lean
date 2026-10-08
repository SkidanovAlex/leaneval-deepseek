import Mathlib
import Submission.Work.HallHigman.Basic
import Submission.Work.HallHigman.piCore_isPiNat
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman.GLCore

/-- A subgroup `M ≤ K` disjoint from a normal subgroup `H` has order dividing the index of
`H ⊓ K` in `K` (equivalently, of `H.subgroupOf K` in `K`): the canonical map
`M → K ⧸ (H.subgroupOf K)` is injective because its kernel is `M ⊓ H = ⊥`. -/
theorem card_dvd_index_of_inf_eq_bot {G : Type*} [Group G] {H K M : Subgroup G} [H.Normal]
    (hMK : M ≤ K) (hbot : M ⊓ H = ⊥) : Nat.card ↥M ∣ ((H.subgroupOf K)).index := by
  haveI : (H.subgroupOf K).Normal := Subgroup.Normal.comap (inferInstance : H.Normal) K.subtype
  let φ : ↥M →* (↥K ⧸ (H.subgroupOf K)) :=
    (QuotientGroup.mk' (H.subgroupOf K)).comp (Subgroup.inclusion hMK)
  have hker : φ.ker = ⊥ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hx
      have hxH : (x : G) ∈ H := by
        have h1 : (Subgroup.inclusion hMK x : ↥K) ∈ H.subgroupOf K := by
          rw [← QuotientGroup.ker_mk' (H.subgroupOf K), MonoidHom.mem_ker]
          exact hx
        rwa [Subgroup.mem_subgroupOf] at h1
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact ⟨x.2, hxH⟩
      exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
    · intro hx
      rw [hx, map_one]
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  have hcard : Nat.card ↥M = Nat.card ↥φ.range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [Subgroup.index_eq_card, hcard]
  exact Subgroup.card_subgroup_dvd_card φ.range

/-- In a finite `p`-solvable group with trivial `p'`-core, every nontrivial normal subgroup
contains a nontrivial normal `p`-subgroup (item L15a of the GL-core design).

Walk up a `p`-solvable series `1 = f 0 ≤ … ≤ f n = G` (factors of `p`-power or `p'`-index) to
the first index `i` with `f i ⊓ N ≠ ⊥`; then `M = f i ⊓ N` is normal, nontrivial, lies in `N`,
and `M ⊓ f (i-1) = ⊥`, so `|M|` divides the index of `f (i-1)` in `f i`.  If that index is
prime to `p` then `M` is a nontrivial normal `p'`-subgroup, forcing `M ≤ O_{p'}(G) = ⊥`, a
contradiction; hence `M` has `p`-power order. -/
lemma exists_normal_pGroup_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hps : Work.HallHigman.IsPSolvable p G) (h : Work.HallHigman.opCore p G = ⊥)
    {N : Subgroup G} (hN : N.Normal) (hNne : N ≠ ⊥) :
    ∃ M : Subgroup G, M.Normal ∧ M ≤ N ∧ M ≠ ⊥ ∧
      Work.HallHigman.IsPiNat (· = p) (Nat.card ↥M) := by
  classical
  obtain ⟨n, f, hf0, hfn, hfnorm, hfac⟩ := hps
  -- the indices at which the series meets `N` nontrivially
  let S : Finset (Fin (n + 1)) := Finset.univ.filter fun j => f j ⊓ N ≠ ⊥
  have hSne : S.Nonempty := ⟨Fin.last n, by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [hfn, top_inf_eq]
    exact hNne⟩
  let i : Fin (n + 1) := S.min' hSne
  have hiS : f i ⊓ N ≠ ⊥ := by
    have hmem : i ∈ S := Finset.min'_mem S hSne
    exact (Finset.mem_filter.mp hmem).2
  have himin : ∀ j : Fin (n + 1), j < i → f j ⊓ N = ⊥ := by
    intro j hj
    by_contra hc
    have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hc⟩
    exact absurd (show i ≤ j from Finset.min'_le S j hjS) (not_le.mpr hj)
  -- `i` is not the first index, because `f 0 = ⊥`
  have hi0 : i ≠ 0 := by
    intro h0
    refine hiS ?_
    rw [h0, show f (0 : Fin (n + 1)) = ⊥ from hf0]
    simp
  have hival : 0 < i.val := by
    have hpos : (0 : Fin (n + 1)) < i := Fin.pos_iff_ne_zero.mpr hi0
    simpa using (Fin.lt_def.mp hpos)
  -- the previous index
  let i' : Fin n := i.pred hi0
  have hi'succ : i'.succ = i := Fin.succ_pred i hi0
  have hi'val : (i'.val : ℕ) = i.val - 1 := Fin.val_pred i hi0
  have hcast_lt : i'.castSucc < i := by
    rw [Fin.lt_def, Fin.val_castSucc, hi'val]
    omega
  have hjbot : f i'.castSucc ⊓ N = ⊥ := himin i'.castSucc hcast_lt
  have hfac' := hfac i'
  rw [hi'succ] at hfac'
  -- `M = f i ⊓ N` is disjoint from the previous term, so its order divides the factor index
  have hNinf : (f i ⊓ N).Normal := by
    haveI := hfnorm i
    haveI := hN
    infer_instance
  have hdvd : Nat.card ↥(f i ⊓ N) ∣ ((f i'.castSucc).subgroupOf (f i)).index := by
    haveI : (f i'.castSucc).Normal := hfnorm i'.castSucc
    refine card_dvd_index_of_inf_eq_bot (H := f i'.castSucc) (K := f i) (M := f i ⊓ N)
      inf_le_left ?_
    have hsub : ((f i ⊓ N) ⊓ f i'.castSucc) ≤ f i'.castSucc ⊓ N :=
      fun x hx => ⟨hx.2, hx.1.2⟩
    exact le_antisymm (le_trans hsub (le_of_eq hjbot)) bot_le
  rcases hfac' with hND | ⟨k, hk⟩
  · -- a `p'`-factor would give a nontrivial normal `p'`-subgroup, contradicting `O_{p'}(G) = ⊥`
    have hpdvd : ¬ p ∣ Nat.card ↥(f i ⊓ N) := fun hd => hND (hd.trans hdvd)
    have hpi : Work.HallHigman.IsPiNat (· ≠ p) (Nat.card ↥(f i ⊓ N)) := by
      intro q hq hqn hqp
      exact hpdvd (hqp ▸ hqn)
    have hle := Work.HallHigman.le_opCore hNinf hpi
    rw [h] at hle
    exact absurd (le_antisymm hle bot_le) hiS
  · -- a `p`-power factor forces `|M|` to be a `p`-power
    refine ⟨f i ⊓ N, hNinf, inf_le_right, hiS, ?_⟩
    intro q hq hqn
    exact (Nat.prime_dvd_prime_iff_eq hq Fact.out).mp
      (hq.dvd_of_dvd_pow (hqn.trans (hk ▸ hdvd)))

end Work.HallHigman.GLCore
