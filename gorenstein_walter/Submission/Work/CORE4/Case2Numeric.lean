import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2Parity
import Submission.Work.CORE4.Case2KB0
import Submission.Work.CORE4.Case2CHs
import Submission.Work.CORE4.Case2Fill
import Submission.Work.CORE4.Case2BGData
import Submission.Work.CORE4.Case2NormalizerP
import Submission.Work.CORE4.Case2KmulS0
import Submission.Work.CORE4.Case2PrePlusOfCentralizer
import Submission.Work.CORE4.Case2PrePlusOfCommutator
import Submission.Work.CORE4.Case2NotInvNormal
import Submission.Work.CORE4.Case2PrePlusOfCtx
import Submission.Work.CORE4.Case2S0_comm_U
import Submission.Work.CORE4.Case2SixEmbed
import Submission.Work.CORE4.Case2Seven
import Submission.Work.CORE4.SevenX.piFU_le_pi_K0F
import Submission.Work.CORE4.SevenX.piF_le_pi_K0_of_witness
import Submission.Work.CORE4.Case2SevenCentralizer
import Submission.Work.CORE4.Case2SevenRemainingOfCtx
import Submission.Work.CORE4.Case2K1_ne_bot
import Submission.Work.CORE4.S0CentUO2
import Submission.Work.CORE4.Case2Eight
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.Case2EightP0LeP1
import Submission.Work.CORE4.Case2EightP1Le
import Submission.Work.CORE4.Case2EightDisjOfCtx

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## The state of the proof of `Case2Numeric`

The target is assembled by `Case2Numeric_of_layer` from three inputs, and every other conjunct is
proved here:

* `Case2SevenFacts B h.D` — Bender's §4 (7) for the *given* setup; leaf `Work.CORE4.Case2Seven`
  (`Work.GW2.Case2SevenImpl`), needing `Case2 B` (`Case2Ctx.toCase2`), `Case2Ctx6 B`
  (`Case2Ctx.toCtx6`) and `Case2PrePlus B h.D`.
* `Case2EightAll B h.D` — Bender's §4 (8) objects and inequalities; leaf
  `Work.CORE4.Case2Eight` (`Work.GW2.Case2EightImpl`), with the same hypotheses plus (7).
* `¬ Case2InvNormal B h.D` — Bender's exceptional case of (8) is excluded; proved as
  `Work.CORE4.Case2NotInvNormal` from `S₀ ≤ C_G(U)` (`S₀ = C_S(U)`, Bender p. 227), which is
  `Work.GW2.Case2S0_comm_U`.

The identity `k = |K|·|S₀|` of §4 (9) is `Work.CORE4.Case2KmulS0` (proved), and Bender's (1),(2)
(`Case2PrePlus B h.D`) follow for the given setup from `S₀ ≤ C_G(U)` by
`Case2PrePlus_of_S0` (this file) together with `Case2Ctx.sylowIndex`,
`Case2PrePlusOfCommutator` / `Case2PrePlusOfCentralizer` and the two glue lemmas
`Case2Data.commutator_S0_le_K`, `Case2Data.B0_le_centralizer_S`. -/

/-! ## Auxiliary facts about the §4 configuration, used by the assembly of `Case2Numeric`

These are the conjuncts of the target whose proofs do *not* need the §4 (6)–(9) input: the
`Case2`-data needed to invoke the design-9 leaves, the Sylow/`H ≰ M` bookkeeping, and the purely
numerical consequences of `k = |K| · |S₀|`, `p ∣ |K|`, `p₀ ≤ p₁ ≤ p+1`. -/

/-- **The involution `s` is not in the cyclic index-two subgroup `S₀`.**

If `s ∈ S₀`, then `s = B.t`: both have order `2` and lie in the cyclic group `S₀`, which has a
unique subgroup of order `2`, so `⟨s⟩ = ⟨t⟩` and `s ∈ ⟨t⟩ = {1, t}`.  But `U ≤ H = C_G(t)`, so
`t` centralizes `U ⊇ U ⊓ M`, whence every element of `K = I_{U⊓M}(s) = I_{U⊓M}(t)` satisfies
`x = x⁻¹`; as `U` has odd order this forces `x = 1`, i.e. `K = ⊥`.  That contradicts `K ≠ ⊥`
(`Work.CORE4.Case2K1_ne_bot`). -/
theorem Case2Data.s_notMem_S0 (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (hbc : Work.GW2.BenderCtx G) (h : Work.GW2.Case2Ctx B) : h.D.s ∉ B.S0 := by
  intro hs
  haveI : IsCyclic ↥B.S0 := B.S0_cyclic
  have hle_s : Subgroup.zpowers h.D.s ≤ B.S0 := Subgroup.zpowers_le.mpr hs
  have hle_t : Subgroup.zpowers B.t ≤ B.S0 := Subgroup.zpowers_le.mpr B.t_mem
  have hcard_s : Nat.card ↥(Subgroup.zpowers h.D.s) = 2 := by
    rw [Nat.card_zpowers]; exact h.D.s_order
  have hcard_t : Nat.card ↥(Subgroup.zpowers B.t) = 2 := by
    rw [Nat.card_zpowers]; exact B.t_order
  have heq : (Subgroup.zpowers h.D.s).subgroupOf B.S0 =
      (Subgroup.zpowers B.t).subgroupOf B.S0 := by
    refine IsCyclic.subgroup_eq_iff_card_eq.mpr ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle_s).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle_t).toEquiv, hcard_s, hcard_t]
  have heq' : Subgroup.zpowers h.D.s = Subgroup.zpowers B.t := by
    have hmap := congrArg (Subgroup.map (B.S0).subtype) heq
    rwa [Subgroup.map_subgroupOf_eq_of_le hle_s, Subgroup.map_subgroupOf_eq_of_le hle_t] at hmap
  -- `t` centralizes `U` (as `U ≤ H = C_G(t)`), hence so does every element of `⟨t⟩ ∋ s`
  have htC : B.t ∈ Subgroup.centralizer ((B.U : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact ((Subgroup.mem_centralizer_iff.mp (B.U_le_H hu)) B.t (Set.mem_singleton B.t)).symm
  have hsC : h.D.s ∈ Subgroup.centralizer ((B.U : Subgroup G) : Set G) := by
    refine Subgroup.zpowers_le.mpr htC ?_
    rw [← heq']; exact Subgroup.mem_zpowers _
  have hKbot : h.D.K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxinv : x ∈ Work.GW2.invSet (B.U ⊓ h.D.M) h.D.s := by
      rw [← h.D.K_def]; exact hx
    obtain ⟨-, hinv⟩ := hxinv
    have hxU : x ∈ B.U := (Subgroup.mem_inf.mp ((h.D.K_le B) hx)).1
    have hfix : h.D.s * x * h.D.s⁻¹ = x := by
      have hc := (Subgroup.mem_centralizer_iff.mp hsC) x hxU
      rw [hc.symm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hfix] at hinv
    -- `x = x⁻¹` with `x` of odd order
    have hx2 : x * x = 1 := by
      nth_rewrite 2 [hinv]
      exact mul_inv_cancel x
    have hx1 : orderOf x ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact hx2
    have hodd : Odd (orderOf x) :=
      Odd.of_dvd_nat B.U_odd (Subgroup.orderOf_dvd_natCard B.U hxU)
    rcases (Nat.dvd_prime Nat.prime_two).mp hx1 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · rw [h1] at hodd; exact absurd hodd (by decide)
  have hne := Work.CORE4.Case2K1_ne_bot I hbc h
  rw [hKbot] at hne
  simpa using hne

/-- **Bender §4 (1)/(2), the `S₀`-half.**  If `S₀ ≤ C_G(U)` (Bender p. 227: `S₀ = C_S(U)`),
then `S₀` centralizes `B₀` (as `B₀ ≤ U`) and `B₀` centralizes `s` (by definition), while
`S = S₀ ⊔ ⟨s⟩` because `s ∉ S₀` (`Case2Data.s_notMem_S0`) and `S₀` has index two in `S`; hence
`B₀ ≤ C_G(S)`.  With `Case2PrePlusOfCentralizer` this gives Bender's (2) `B₀ = C_{U⊓M}(S ∩ E)`. -/
theorem Case2Data.B0_le_centralizer_S (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (hbc : Work.GW2.BenderCtx G) (h : Work.GW2.Case2Ctx B)
    (hS0 : B.S0 ≤ Subgroup.centralizer ((B.U : Subgroup G) : Set G)) :
    h.D.B0 ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G) := by
  have hsS : h.D.s ∈ (B.S : Subgroup G) := (Subgroup.mem_inf.mp h.D.s_mem).1
  have hsup : B.S0 ⊔ Subgroup.zpowers h.D.s = (B.S : Subgroup G) := by
    refine le_antisymm (sup_le B.S0_le (Subgroup.zpowers_le.mpr hsS)) ?_
    rw [← Subgroup.relIndex_eq_one]
    have hmul := Subgroup.relIndex_mul_relIndex (H := B.S0)
      (K := B.S0 ⊔ Subgroup.zpowers h.D.s) (L := (B.S : Subgroup G)) le_sup_left
      (sup_le B.S0_le (Subgroup.zpowers_le.mpr hsS))
    rw [B.S0_index] at hmul
    have hdvd : (B.S0 ⊔ Subgroup.zpowers h.D.s).relIndex (B.S : Subgroup G) ∣ 2 :=
      ⟨B.S0.relIndex (B.S0 ⊔ Subgroup.zpowers h.D.s), by rw [mul_comm]; exact hmul.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hmul
      have h2 : B.S0.relIndex (B.S0 ⊔ Subgroup.zpowers h.D.s) = 1 := by omega
      rw [Subgroup.relIndex_eq_one] at h2
      exact Case2Data.s_notMem_S0 I hbc h (h2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
  have hB0U : h.D.B0 ≤ B.U := le_trans (h.D.B0_le B) inf_le_left
  have hS0' : B.S0 ≤ Subgroup.centralizer (h.D.B0 : Set G) :=
    le_trans hS0 (Subgroup.centralizer_le (fun x hx => hB0U hx))
  have hs' : Subgroup.zpowers h.D.s ≤ Subgroup.centralizer (h.D.B0 : Set G) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hc := (Subgroup.mem_inf.mp (by rw [← h.D.B0_def]; exact hy)).2
    exact Subgroup.mem_centralizer_singleton_iff.mp hc
  have hSle : (B.S : Subgroup G) ≤ Subgroup.centralizer (h.D.B0 : Set G) := by
    rw [← hsup]
    exact sup_le hS0' hs'
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  exact fun σ hσ => (Subgroup.mem_centralizer_iff.mp (hSle hσ) y hy).symm

/-- **Bender §4 (1), the `S₀`-half.**  If `S₀ ≤ C_G(U)`, then `[S₀, U ⊓ M] = 1 ≤ K`, which is the
hypothesis of `Case2PrePlusOfCommutator`: with it, Bender's (1) `K = [S ∩ E, U ∩ M]` follows. -/
theorem Case2Data.commutator_S0_le_K (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (hbc : Work.GW2.BenderCtx G) (h : Work.GW2.Case2Ctx B)
    (hS0 : B.S0 ≤ Subgroup.centralizer ((B.U : Subgroup G) : Set G)) :
    ⁅B.S0, B.U ⊓ h.D.M⁆ ≤ h.D.K := by
  have hbot : ⁅B.S0, B.U ⊓ h.D.M⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact le_trans hS0 (Subgroup.centralizer_le (fun x hx => (Subgroup.mem_inf.mp hx).1))
  rw [hbot]
  exact bot_le

/-- **Bender §4, the Sylow choice.** `S ⊓ M ∈ Syl₂(M)`: §4 (9) (`Case2Ctx.nine`) records
`S ≤ E(M) ≤ M`, so `S ⊓ M = S` and `S` — a Sylow 2-subgroup of `G` — is a Sylow 2-subgroup of
`M`.  Hence `2 ∤ |M : S|`, which is the first conjunct of the design-pass-9 layer `Case2PrePlus`.

Proof: `Subgroup.relIndex_mul_card` gives `|S : M| · |S| = |M|`; multiplying by `M.index` and
comparing with `S.index · |S| = |G|` (twice `Subgroup.index_mul_card`) and cancelling `|S| ≠ 0`
identifies `(S).relIndex M` with `S.index / M.index`; by `Sylow.not_dvd_index` the index
`S.index = |G : S|` is not divisible by `2`. -/
theorem Case2Ctx.sylowIndex (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) :
    ¬ 2 ∣ (((B.S : Subgroup G) ⊓ h.D.M)).relIndex h.D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [inf_eq_left.mpr h.S_le_M]
  have h1 : (B.S : Subgroup G).relIndex h.D.M * Nat.card ↥(B.S : Subgroup G) =
      Nat.card ↥h.D.M := by
    have hh := Subgroup.relIndex_mul_card (B.S : Subgroup G) h.D.M
    rwa [inf_eq_left.mpr h.S_le_M] at hh
  have h2 := Subgroup.index_mul_card h.D.M
  have h3 := Subgroup.index_mul_card (B.S : Subgroup G)
  have hmul : h.D.M.index * ((B.S : Subgroup G).relIndex h.D.M *
        Nat.card ↥(B.S : Subgroup G)) =
      (B.S : Subgroup G).index * Nat.card ↥(B.S : Subgroup G) := by
    rw [h1, h2, h3]
  have hkey : h.D.M.index * (B.S : Subgroup G).relIndex h.D.M =
      (B.S : Subgroup G).index :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [mul_assoc]; exact hmul)
  intro hcon
  obtain ⟨d, hd⟩ := hcon
  refine Sylow.not_dvd_index B.S ⟨h.D.M.index * d, ?_⟩
  rw [← hkey, hd]
  ring

/-- `Case2 B` follows from the §4 configuration: the fields of `Case2Data` are exactly the data
required by `Case2` (the coatom `M`, `t ∈ E(M)`, and `X ≠ ⊥` with `X ≤ F(U)`, `N_G(X) ≤ M`). -/
theorem Case2Ctx.toCase2 {B : Work.GW2.BenderSetup G} (h : Work.GW2.Case2Ctx B) :
    Work.GW2.Case2 B :=
  ⟨h.D.M, h.D.M_coatom, h.D.t_mem, h.D.X, h.D.X_ne, h.D.X_le, h.D.NX_le⟩

/-- `Case2Ctx6 B` follows from `Case2Ctx B` (forget §4 (7)–(9)). -/
def Case2Ctx.toCtx6 {B : Work.GW2.BenderSetup G} (h : Work.GW2.Case2Ctx B) :
    Work.GW2.Case2Ctx6 B :=
  ⟨h.D, h.pre, h.F_ti, h.F_cyclic⟩

/-- `U ⊄ M`: if `U ≤ M`, then `H = U · S ≤ M` because `S ≤ E(M) ≤ M` (here `S ≤ E(M)` is §4 (9),
a field of `Case2Ctx`), contradicting §4 (1) (`¬ H ≤ M`).  Bender uses this to see `3 ≤ p₀`. -/
theorem Case2Num_not_U_le_M (I : Work.GW2.C4Inputs) (B : Work.GW2.BenderSetup G)
    (h : Work.GW2.Case2Ctx B) : ¬ B.U ≤ h.D.M := by
  intro hUM
  exact Work.GW2.Case2Pre.not_H_le B h.D h.pre
    ((Work.GW2.Case2Ctx.H_eq_U_sup_S I h).trans_le (sup_le hUM h.S_le_M))

/-- `2 * p ≤ k` if `k = |K| · |S₀|` and `p ∣ |K|`: `p ≤ |K|`, and `|S₀| ≥ 2` because `t ∈ S₀` is
an involution. -/
theorem Case2Num_two_p_le_k (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    {k p : ℕ} (hk : k = Nat.card ↥h.D.K * Nat.card ↥B.S0)
    (hp : p ∣ Nat.card ↥h.D.K) : 2 * p ≤ k := by
  have hpK : p ≤ Nat.card ↥h.D.K := Nat.le_of_dvd Nat.card_pos hp
  have hS0 : 2 ≤ Nat.card ↥B.S0 := by
    refine Nat.le_of_dvd Nat.card_pos ?_
    have h := Subgroup.orderOf_dvd_natCard B.S0 B.t_mem
    rwa [B.t_order] at h
  rw [hk]
  calc 2 * p ≤ 2 * Nat.card ↥h.D.K := by omega
    _ = Nat.card ↥h.D.K * 2 := by ring
    _ ≤ Nat.card ↥h.D.K * Nat.card ↥B.S0 := Nat.mul_le_mul_left _ hS0

/-- `p₀ ≤ p`: from `p₀ ≤ p₁ ≤ p + 1` together with `p₀` odd and `p` odd (`p + 1` is even, so the
inequality `p₀ ≤ p + 1` is strict for odd `p₀`). -/
theorem Case2Num_p0_le_p {p0 p1 p : ℕ} (h01 : p0 ≤ p1) (h1 : p1 ≤ p + 1)
    (hodd : Odd p0) (hpodd : Odd p) : p0 ≤ p := by
  obtain ⟨a, ha⟩ := hodd
  obtain ⟨b, hb⟩ := hpodd
  omega

/-- `1 ≤ u` for `u = |U : N_U(A)|`: relative indices of subgroups are positive. -/
theorem Case2Num_one_le_relIndex (B : Work.GW2.BenderSetup G) (A : Subgroup G) :
    1 ≤ (B.U ⊓ Subgroup.normalizer (A : Set G)).relIndex B.U := by
  have h := Subgroup.relIndex_mul_card (B.U ⊓ Subgroup.normalizer (A : Set G)) (B.U)
  have hpos : 0 < Nat.card ↥(B.U : Subgroup G) := Nat.card_pos
  by_contra hcon
  rw [Nat.not_le] at hcon
  have hzero : (B.U ⊓ Subgroup.normalizer (A : Set G)).relIndex B.U = 0 := by omega
  rw [hzero, Nat.zero_mul] at h
  omega

/-- §4 (10), the index identity `|H : H ⊓ M| = u · p₀`.

For `u = |U : N_U(A)| = (U ⊓ N(A)).relIndex U` and
`p₀ = |N_U(A) : N_U(P)| = (U ⊓ N(P)).relIndex (U ⊓ N(A))`, relative-index multiplicativity
(`Subgroup.relIndex_mul_relIndex`) applied to `N_U(P) ≤ N_U(A) ≤ U` gives
`p₀ · u = |U : N_U(P)|`, and `N_U(P) = U ⊓ M` (Bender §4 (5), the workspace lemma
`Case2NormalizerP`) together with `Work.GW2.Case2Ctx.relIndex_H_inter_M`
(`|H : H ⊓ M| = |U : U ⊓ M|`) identifies the right-hand side with `|H : H ⊓ M|`. -/
theorem Case2Num_MH_relIndex (I : Work.GW2.C4Inputs) (B : Work.GW2.BenderSetup G)
    (h : Work.GW2.Case2Ctx B) (P A : Subgroup G)
    (hP : B.U ⊓ Subgroup.normalizer (P : Set G) = B.U ⊓ h.D.M)
    (hPA : B.U ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (A : Set G)) :
    (h.D.M ⊓ B.H).relIndex B.H =
      (B.U ⊓ Subgroup.normalizer (A : Set G)).relIndex B.U *
      (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex
        (B.U ⊓ Subgroup.normalizer (A : Set G)) := by
  have hkey := Subgroup.relIndex_mul_relIndex
    (H := B.U ⊓ Subgroup.normalizer (P : Set G))
    (K := B.U ⊓ Subgroup.normalizer (A : Set G)) (L := B.U)
    (le_inf inf_le_left hPA) inf_le_left
  have hkey' : (B.U ⊓ Subgroup.normalizer (A : Set G)).relIndex B.U *
      (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex
        (B.U ⊓ Subgroup.normalizer (A : Set G)) =
      (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex B.U := by
    have hcomm : (B.U ⊓ Subgroup.normalizer (A : Set G)).relIndex B.U *
        (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex
          (B.U ⊓ Subgroup.normalizer (A : Set G)) =
        (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex
            (B.U ⊓ Subgroup.normalizer (A : Set G)) *
          (B.U ⊓ Subgroup.normalizer (A : Set G)).relIndex B.U := Nat.mul_comm _ _
    rw [hcomm, hkey]
  have h1 : (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex B.U =
      (B.U ⊓ h.D.M).relIndex B.U := by rw [hP]
  rw [hkey', h1]
  exact Work.GW2.Case2Ctx.relIndex_H_inter_M I h

/-- **Bender's §4 (1)–(2) for the given setup `B`.**

Given `S₀ ≤ C_G(U)` (Bender p. 227: `S₀ = C_S(U)`), the three conjuncts of the design-pass-9 layer
`Case2PrePlus B h.D` follow from the proved pieces:

* the Sylow condition `¬ 2 ∣ |M : S ⊓ M|` is `Case2Ctx.sylowIndex` (§4 (9) gives `S ≤ E(M) ≤ M`);
* Bender's (1) `K = [S ⊓ E(M), U ⊓ M]` is `Case2PrePlusOfCommutator`, applied with
  `Case2Data.commutator_S0_le_K`;
* Bender's (2) `B₀ = (U ⊓ M) ⊓ C_G(S ⊓ E(M))` is `Case2PrePlusOfCentralizer`, applied with
  `Case2Data.B0_le_centralizer_S`. -/
theorem Case2PrePlus_of_S0 (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (hbc : Work.GW2.BenderCtx G) (h : Work.GW2.Case2Ctx B)
    (hS0 : B.S0 ≤ Subgroup.centralizer ((B.U : Subgroup G) : Set G)) :
    Work.GW2.Case2PrePlus B h.D :=
  ⟨Case2Ctx.sylowIndex B h,
   Work.CORE4.Case2PrePlusOfCommutator G I hbc B h
     (Case2Data.commutator_S0_le_K I hbc h hS0),
   Work.CORE4.Case2PrePlusOfCentralizer G I hbc B h
     (Case2Data.B0_le_centralizer_S I hbc h hS0)⟩

/-! ## §4 (8): the `F(U) ≤ M` case of `u = 1`

The two facts recorded here are the parts of Bender's §4 (8) inequality `u ≤ p` that do *not* use
the position of `A` in `Q := Ω₁(Z₂(O_p(U)))`:

* if `F(U) ≤ M` then `A = Ω₁(F(U))` (`A_eq_omega1_fittingIn_of_le_M`) is `U`-invariant
  (`conjSub_omega1_fittingIn_eq`), so `N_U(A) = U` and `u = 1`;
* `A ≤ U ⊓ M` (so `U ⊓ M ≤ N_U(A)`), which together with `A ⊴ F(U)` gives
  `(U ⊓ M) ⊔ F(U) ≤ N_U(A)`, hence `u ≤ |U : (U ⊓ M) ⊔ F(U)|` — Bender's (8) *first* half, which
  is `1` when `F(U) ⊄ M` (because then `F(U)·M = G` forces `(U ⊓ M) ≤ F(U)·(U ⊓ M) = U`). -/

/-- `A ≤ U ⊓ M`: `A ≤ F ⊔ K₀` with `F ≤ U ⊓ M` and `K₀ ≤ K ≤ U ⊓ M`. -/
theorem A_le_UinfM_c4 (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (p : ℕ) (P A : Subgroup G) (hObj : Work.GW2.Case2EightObj h.D p P A) :
    A ≤ B.U ⊓ h.D.M :=
  hObj.2.2.2.1.trans
    (sup_le (Work.GW2.Case2Data.F_le_UinfM B h.D) (Work.GW2.Case2Data.K_le B h.D))

/-- **If `F(U) ≤ M` then `N_U(A) = U`, i.e. `u = 1`.**  Then `A = Ω₁(F(U))`, which is
`U`-invariant. -/
theorem Case2EightU_eq_one_of_fitting_le_M (I : Work.GW2.C4Inputs)
    (hbc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card ↥P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A)
    (hFM : Work.GW2.fittingIn B.U ≤ h.D.M) :
    Work.GW2.Case2EightU B A = 1 := by
  have hAeq : A = omega1 p (Work.GW2.fittingIn B.U) :=
    A_eq_omega1_fittingIn_of_le_M I hbc B h p P A hp hPF hPcard hObj hFM
  have hUle : B.U ≤ Subgroup.normalizer (A : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show Work.GW2.conjSub u A = A
    rw [hAeq]
    exact conjSub_omega1_fittingIn_eq B p hu
  rw [Work.GW2.Case2EightU, inf_eq_left.mpr hUle, Subgroup.relIndex_self]

/-- **Assembly of `Case2Numeric`.**  From Bender's §4 (7) layer (`Case2SevenFacts`), the §4 (8)
objects and inequalities (`Case2EightAll`), and the exclusion of Bender's exceptional case of (8)
(`¬ Case2InvNormal`, proved from `S₀ ≤ C_U(S)` via Lemma 2.8), the target `Case2Numeric` follows.
The identity `k = |K| · |S₀|` of §4 (9) is the proved lemma `Work.CORE4.Case2KmulS0`; this
lemma isolates the *assembly* (parity data of `Case2Parity`, the order-`p` subgroup `P ≤ F` of
`Case2Fill`, the `(p,p)`-subgroup `A` of `Case2EightAll`, and the arithmetic `2p ≤ k`, `p₀ ≤ p`),
which needs no further §4 input. -/
theorem Case2Numeric_of_layer (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (hSeven : Work.GW2.Case2SevenFacts B h.D)
    (hEight : Work.GW2.Case2EightAll B h.D)
    (hInv : ¬ Work.GW2.Case2InvNormal B h.D) :
    ∃ (q k k' p : ℕ) (P A : Subgroup G) (u p0 p1 : ℕ),
      Odd q ∧ 7 ≤ q ∧ Even k ∧ Odd k' ∧
      ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) ∧
      (h.D.M ⊓ B.H).relIndex h.D.M = q * k' ∧
      k = Nat.card ↥h.D.K * Nat.card ↥B.S0 ∧ p ∣ Nat.card ↥h.D.K ∧
      p.Prime ∧ P ≤ h.D.F ∧ Nat.card ↥P = p ∧
      A ≤ h.D.F ⊔ h.D.K ∧ Nat.card ↥A = p ^ 2 ∧ (∀ x ∈ A, x ^ p = 1) ∧ P ≤ A ∧
      (∀ B' : Subgroup G, B' ≤ h.D.F ⊔ h.D.K → Nat.card ↥B' = p ^ 2 →
          (∀ x ∈ B', x ^ p = 1) → B' = A) ∧
      u = (B.U ⊓ Subgroup.normalizer (A : Set G)).relIndex B.U ∧
      p0 = (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex
             (B.U ⊓ Subgroup.normalizer (A : Set G)) ∧
      p1 = {X : Subgroup G | X ≤ A ∧ ∃ g : G, X = Work.GW2.conjSub g P}.ncard ∧
      (h.D.M ⊓ B.H).relIndex B.H = u * p0 ∧
      3 ≤ p0 ∧ Odd p0 ∧ p0 ≤ p1 ∧ p1 ≤ p + 1 ∧ p0 ≤ p ∧ 2 * p ≤ k ∧ 1 ≤ u ∧ u ≤ p := by
  classical
  -- §4 (10): the parity data with `|M : M ⊓ H| = q k'`.
  obtain ⟨q, k, k', hqodd, hq7, hkeven, hk'odd, hcases, hrelMH⟩ :=
    Work.CORE4.Case2Parity G I hbc B h
  -- §4 (5): `p := |F|.minFac` and `P ≤ F` of order `p` (Cauchy in the finite cyclic group `F`).
  obtain ⟨hpprime, -, P, hPF, hPcard⟩ := Work.CORE4.Case2Fill G B h
  -- §4 (8): Bender's objects, for this `p` and `P`.
  obtain ⟨A, hObj, hFacts⟩ := hEight (Nat.card ↥h.D.F).minFac P hpprime hPF hPcard
  obtain ⟨hpprime', hPF', hPcard', hAle, hAcard, hAexp, hPAsub, hAuniq⟩ := hObj
  obtain ⟨hpK0, -, hNP, hNPA, hp0odd, hp0p1, hp1p, hp0p, -, hdisj⟩ := hFacts
  -- `p ∣ |K|`: `p ∣ |K₀|` and `K₀ ≤ K`.
  have hpK : (Nat.card ↥h.D.F).minFac ∣ Nat.card ↥h.D.K :=
    dvd_trans hpK0 (Subgroup.card_dvd_of_le inf_le_right)
  -- §4 (9): the identity `k = |K| · |S₀|` (Bender p. 227, proved as `Case2KmulS0`).
  have hkK : k = Nat.card ↥h.D.K * Nat.card ↥B.S0 :=
    Work.CORE4.Case2KmulS0 G I hbc B h q k k' hqodd hq7 hcases hrelMH
  -- Bender's exceptional case of (8) is excluded, so `u ≤ p` and (with `U ⊄ M`) `3 ≤ p₀`.
  have hup : Work.GW2.Case2EightU B A ≤ (Nat.card ↥h.D.F).minFac := by
    rcases hdisj with hcase | hcase
    · exact absurd hcase hInv
    · exact hcase.1
  have hp03 : 3 ≤ Work.GW2.Case2EightP0 B P A := by
    rcases hdisj with hcase | hcase
    · exact absurd hcase hInv
    · exact hcase.2.2 (Case2Num_not_U_le_M I B h)
  refine ⟨q, k, k', (Nat.card ↥h.D.F).minFac, P, A, Work.GW2.Case2EightU B A,
    Work.GW2.Case2EightP0 B P A, Work.GW2.Case2EightP1 P A, hqodd, hq7, hkeven, hk'odd,
    hcases, hrelMH, hkK, hpK, hpprime', hPF', hPcard', hAle, hAcard, hAexp, hPAsub, hAuniq,
    rfl, rfl, rfl, ?_, hp03, hp0odd, hp0p1, hp1p, hp0p,
    Case2Num_two_p_le_k B h hkK hpK, Case2Num_one_le_relIndex B A, hup⟩
  -- `|H : H ⊓ M| = u · p₀` (§4 (10)).
  simpa only [Work.GW2.Case2EightU, Work.GW2.Case2EightP0] using
    Case2Num_MH_relIndex I B h P A hNP hNPA

/-- **Bender's §4 (7) facts for the given `Case2Ctx`, assembled from the proved pieces.**

Conjunct 2 (`π(K₀) = π(F(U))`) is `conj2_iff_piF` (the equivalence with `π(F) ⊆ π(K₀)`) plus
Bender's (6)-witness from `Submission.Work.CORE4.Case2SixEmbed`; conjunct 6
(`π⁅S ⊓ M, B₀⁆ ⊆ π`) is immediate from Bender's (2) (`Case2PrePlusOfCtx`), since
`B₀ ≤ C_G(S ⊓ E(M)) = C_G(S ⊓ M)` makes the commutator trivial.  The remaining conjuncts are the
two delegated inputs `hC` (the centralizer conjunct) and `hRem`. -/
theorem Case2SevenFacts_of_pieces (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (hbc : Work.GW2.BenderCtx G) (h : Work.GW2.Case2Ctx B)
    (hRem : Work.GW2.pCoreIn 2 (B.H ⊓ h.D.M) = Work.GW2.pCoreIn 2 B.H ∧
            Work.GW2.primesOf (Work.GW2.Case2Data.K0 h.D) ⊆ B.piFU ∧
            Work.GW2.primesOf h.D.K ⊆ B.piFU ∧
            Work.GW2.primesOf (Work.GW2.fittingIn h.D.M) ⊆ B.piFU) :
    Work.GW2.Case2SevenFacts B h.D := by
  have hpre : Work.GW2.Case2PrePlus B h.D := Work.CORE4.Case2PrePlusOfCtx G I hbc B h
  -- the centralizer conjunct, proved as `Work.CORE4.Case2SevenCentralizer`
  have hC : Work.GW2.primesOf (B.U ⊓ Subgroup.centralizer
      (((Work.GW2.Case2Data.K0 h.D ⊔ h.D.F : Subgroup G)) : Set G)) = B.piFU :=
    Work.CORE4.Case2SevenCentralizer I G hbc B (Case2Ctx.toCtx6 h) (Case2Ctx.toCase2 h) hpre
  -- (2): `π(F(U)) = π(K₀ ⊔ F)`
  have hFU : B.piFU = Work.GW2.primesOf (Work.GW2.Case2Data.K0 h.D ⊔ h.D.F) := by
    refine le_antisymm ?_ ?_
    · exact Work.CORE4.SevenX.piFU_le_pi_K0F I G hbc B (Case2Ctx.toCase2 h) h.D h.pre
    · intro p hp
      rw [Work.GW2.primesOf] at hp
      change p ∈ (Nat.card ↥(Work.GW2.fittingIn B.U)).primeFactors
      exact Nat.primeFactors_mono (Subgroup.card_dvd_of_le
        (sup_le (inf_le_left : Work.GW2.Case2Data.K0 h.D ≤ Work.GW2.fittingIn B.U)
          h.D.F_le_fitting)) (Nat.card_pos.ne') hp
  -- Bender's (6): the witness, and hence `π(F) ⊆ π(K₀)`
  have hwit : ∃ g : G, g ∉ h.D.M ∧
      Work.GW2.conjSub g h.D.F ≤ Work.GW2.fittingIn B.U ⊓ h.D.M :=
    Work.CORE4.exists_witness_of_case2ctx6 I hbc B (Case2Ctx.toCtx6 h)
  have hKF : Work.GW2.primesOf h.D.F ⊆ Work.GW2.primesOf (Work.GW2.Case2Data.K0 h.D) :=
    Work.CORE4.SevenX.piF_le_pi_K0_of_witness I G hbc B (Case2Ctx.toCase2 h)
      (Case2Ctx.toCtx6 h) hpre hwit
  have hK0 : Work.GW2.primesOf (Work.GW2.Case2Data.K0 h.D) = B.piFU :=
    (Work.CORE4.conj2_iff_piF I hbc B h.D h.pre hFU).mpr hKF
  -- (6): Bender's (2) makes `⁅S ⊓ M, B₀⁆ = 1`
  obtain ⟨_, _, _, _, _, _, hSE⟩ := h.nine
  have hB0 : h.D.B0 ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G) := by
    rw [hpre.2.2]
    refine inf_le_right.trans (Subgroup.centralizer_le ?_)
    exact le_inf le_rfl hSE
  have h6 : Work.GW2.primesOf ⁅(B.S : Subgroup G) ⊓ h.D.M, h.D.B0⁆ ⊆ B.piFU := by
    have hbot : ⁅(B.S : Subgroup G) ⊓ h.D.M, h.D.B0⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      refine Subgroup.le_centralizer_iff.mp ?_
      exact hB0.trans (Subgroup.centralizer_le (fun x hx => (Subgroup.mem_inf.mp hx).1))
    rw [hbot]
    intro p hp
    rw [Work.GW2.primesOf, Subgroup.card_bot, Nat.primeFactors_one] at hp
    exact absurd hp (by simp)
  exact ⟨hRem.1, hK0, hC, hRem.2.2.1, hRem.2.2.2, h6⟩

/-- **The target from Bender's §4 (7) and (8) facts for the given `Case2Ctx`.**

Everything else is proved in this workspace: Bender's §4 (1)–(2) for the *given* setup is
`Work.CORE4.Case2PrePlusOfCtx`; `S₀ ≤ C_G(U)` (Bender p. 227, `S₀ = C_S(U)`) is
`Work.CORE4.Case2S0_comm_U`; the exclusion of Bender's exceptional case of (8) is
`Work.CORE4.Case2NotInvNormal`; the identity `k = |K|·|S₀|` of §4 (9) is `Work.CORE4.Case2KmulS0`;
and the arithmetic is `Case2Ctx.sylowIndex` plus the `Case2Num_*` lemmas below.

Note the inputs are taken at the `Case2Ctx` level rather than through the design-pass-9 leaves
`Case2SevenImpl`/`Case2EightImpl` (which are stated over `Case2Ctx6 B`): the first conjunct of
§4 (7), `O₂(H ⊓ M) = O₂(H)`, needs `S ≤ M`, which comes from §4 (9), i.e. from `Case2Ctx.nine`
(`Work.GW2.Case2Ctx.S_le_M`) and not from `Case2Ctx6`. -/
theorem Case2Numeric_of_leaves (I : Work.GW2.C4Inputs)
    (hEight : ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B), Work.GW2.Case2EightAll B h.D) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ∃ (q k k' p : ℕ) (P A : Subgroup G) (u p0 p1 : ℕ),
          Odd q ∧ 7 ≤ q ∧ Even k ∧ Odd k' ∧
          ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) ∧
          (h.D.M ⊓ B.H).relIndex h.D.M = q * k' ∧
          k = Nat.card ↥h.D.K * Nat.card ↥B.S0 ∧ p ∣ Nat.card ↥h.D.K ∧
          p.Prime ∧ P ≤ h.D.F ∧ Nat.card ↥P = p ∧
          A ≤ h.D.F ⊔ h.D.K ∧ Nat.card ↥A = p ^ 2 ∧ (∀ x ∈ A, x ^ p = 1) ∧ P ≤ A ∧
          (∀ B' : Subgroup G, B' ≤ h.D.F ⊔ h.D.K → Nat.card ↥B' = p ^ 2 →
              (∀ x ∈ B', x ^ p = 1) → B' = A) ∧
          u = (B.U ⊓ Subgroup.normalizer (A : Set G)).relIndex B.U ∧
          p0 = (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex
                 (B.U ⊓ Subgroup.normalizer (A : Set G)) ∧
          p1 = {X : Subgroup G | X ≤ A ∧ ∃ g : G, X = Work.GW2.conjSub g P}.ncard ∧
          (h.D.M ⊓ B.H).relIndex B.H = u * p0 ∧
          3 ≤ p0 ∧ Odd p0 ∧ p0 ≤ p1 ∧ p1 ≤ p + 1 ∧ p0 ≤ p ∧ 2 * p ≤ k ∧ 1 ≤ u ∧ u ≤ p := by
  intro G _ _ hbc B h
  have hpre : Work.GW2.Case2PrePlus B h.D := Work.CORE4.Case2PrePlusOfCtx G I hbc B h
  -- §4 (7): `Case2SevenCentralizer` (conjunct 3) and `Case2SevenRemainingOfCtx` (the rest)
  have h7 : Work.GW2.Case2SevenFacts B h.D :=
    Case2SevenFacts_of_pieces I hbc h
      (Work.CORE4.Case2SevenRemainingOfCtx I G hbc B h
        (Work.CORE4.Case2SevenCentralizer I G hbc B (Case2Ctx.toCtx6 h) (Case2Ctx.toCase2 h)
          hpre))
  have h8 : Work.GW2.Case2EightAll B h.D := hEight G hbc B h
  -- `S₀ ≤ C_G(U)`: Bender p. 227 (`S₀ = C_S(U)`)
  have hs0 : B.S0 ≤ Subgroup.centralizer ((B.U : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (Work.CORE4.Case2S0_comm_U I hbc (Case2Ctx.toCase2 h) h hpre h7)
  have hinv : ¬ Work.GW2.Case2InvNormal B h.D := Work.CORE4.Case2NotInvNormal G I hbc B h hs0
  exact Case2Numeric_of_layer I hbc B h h7 h8 hinv

/-! ## §4 (8) at the `Case2Ctx` level: the target from the two §4 (8) inequalities

The whole §4 (8) layer of Bender (p. 225–226) enters the target through exactly two facts about
the objects `p`, `P ≤ F` (of order `p`) and `A ≤ F ⊔ K` (of type `(p,p)`, containing `P`):

* `u = |U : N_U(A)| ≤ p` (Bender's display (8)), and
* `A ⊴ F(U)` (Bender's display (8), "unless `I_U(s) ⊴ Ĥ`"),

for the *specific* prime `p = (|F|).minFac` and `P` of order `p` in `F` (the only choice the
target needs).  Everything else is already proved in this workspace:

* the objects exist (`Case2EightObjExists`, from §4 (6) + (7));
* `p ∣ |K|` (`prime_dvd_card_K_c4`, from §4 (7));
* `N_U(P) = U ⊓ M` (`Case2Eight_NU`) and `N_U(P) ≤ N_G(A)` (`Case2Eight_le_normalizer_A`);
* `p₀` odd (`Case2Eight_odd_p0`), `p₀ ≤ p₁ ≤ p+1` (`Case2EightP0LeP1`, `Case2EightP1Le`),
  hence `p₀ ≤ p` (`Case2Eight_p0_le_p`);
* `3 ≤ p₀` from `A ⊴ F(U)` and `U ⊄ M` (`three_le_p0_of_not_invNormal`, whose only non-elementary
  inputs are exactly those two);
* `k = |K| · |S₀|` (`Case2KmulS0`) and the parity data (`Case2Parity`);
* `|H : H ⊓ M| = u · p₀` (`Case2Num_MH_relIndex`);
* Bender's exceptional case `Case2InvNormal` is excluded (`not_Case2InvNormal_of_ctx`). -/
theorem Case2Numeric_of_eight (I : Work.GW2.C4Inputs)
    (hLeaf : ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ¬ Work.GW2.Case2InvNormal B h.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
          Work.GW2.Case2EightObj h.D p P A →
          (Work.GW2.Case2EightU B A ≤ p ∧
            (A.subgroupOf (Work.GW2.fittingIn B.U)).Normal)) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ∃ (q k k' p : ℕ) (P A : Subgroup G) (u p0 p1 : ℕ),
          Odd q ∧ 7 ≤ q ∧ Even k ∧ Odd k' ∧
          ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) ∧
          (h.D.M ⊓ B.H).relIndex h.D.M = q * k' ∧
          k = Nat.card ↥h.D.K * Nat.card ↥B.S0 ∧ p ∣ Nat.card ↥h.D.K ∧
          p.Prime ∧ P ≤ h.D.F ∧ Nat.card ↥P = p ∧
          A ≤ h.D.F ⊔ h.D.K ∧ Nat.card ↥A = p ^ 2 ∧ (∀ x ∈ A, x ^ p = 1) ∧ P ≤ A ∧
          (∀ B' : Subgroup G, B' ≤ h.D.F ⊔ h.D.K → Nat.card ↥B' = p ^ 2 →
              (∀ x ∈ B', x ^ p = 1) → B' = A) ∧
          u = (B.U ⊓ Subgroup.normalizer (A : Set G)).relIndex B.U ∧
          p0 = (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex
                 (B.U ⊓ Subgroup.normalizer (A : Set G)) ∧
          p1 = {X : Subgroup G | X ≤ A ∧ ∃ g : G, X = Work.GW2.conjSub g P}.ncard ∧
          (h.D.M ⊓ B.H).relIndex B.H = u * p0 ∧
          3 ≤ p0 ∧ Odd p0 ∧ p0 ≤ p1 ∧ p1 ≤ p + 1 ∧ p0 ≤ p ∧ 2 * p ≤ k ∧ 1 ≤ u ∧ u ≤ p := by
  classical
  intro G _ _ hbc B h
  have hInv : ¬ Work.GW2.Case2InvNormal B h.D := Work.CORE4.not_Case2InvNormal_of_ctx I hbc h
  have hpre : Work.GW2.Case2PrePlus B h.D := Work.CORE4.Case2PrePlusOfCtx G I hbc B h
  -- §4 (7) for this setup
  have h7 : Work.GW2.Case2SevenFacts B h.D :=
    Case2SevenFacts_of_pieces I hbc h
      (Work.CORE4.Case2SevenRemainingOfCtx I G hbc B h
        (Work.CORE4.Case2SevenCentralizer I G hbc B (Case2Ctx.toCtx6 h) (Case2Ctx.toCase2 h)
          hpre))
  -- §4 (10): the parity data with `|M : M ⊓ H| = q k'`.
  obtain ⟨q, k, k', hqodd, hq7, hkeven, hk'odd, hcases, hrelMH⟩ :=
    Work.CORE4.Case2Parity G I hbc B h
  -- §4 (8): `p := |F|.minFac` and `P ≤ F` of order `p`.
  obtain ⟨hpprime, -, P, hPF, hPcard⟩ := Work.CORE4.Case2Fill G B h
  -- §4 (8), objects: the unique `(p,p)`-subgroup `A ≤ F ⊔ K` containing `P`.
  obtain ⟨A, hObj⟩ := Work.CORE4.Case2EightObjExists I G hbc B (Case2Ctx.toCase2 h)
    (Case2Ctx.toCtx6 h) hpre h7 (Nat.card ↥h.D.F).minFac P hpprime hPF hPcard
  obtain ⟨hpprime', hPF', hPcard', hAle, hAcard, hAexp, hPAsub, hAuniq⟩ := hObj
  -- clear hObj by re-stating it: the leaf below takes the object as a single hypothesis
  have hObj' : Work.GW2.Case2EightObj h.D (Nat.card ↥h.D.F).minFac P A :=
    ⟨hpprime', hPF', hPcard', hAle, hAcard, hAexp, hPAsub, hAuniq⟩
  -- §4 (8), the two inequalities
  obtain ⟨hup, hAn⟩ :=
    hLeaf G hbc B h hInv (Nat.card ↥h.D.F).minFac P A hpprime hPF hPcard hObj'
  -- elementary §4 (8): `N_U(P) = U ⊓ M`, `N_U(P) ≤ N_G(A)`, odd `p₀`, `p₀ ≤ p₁ ≤ p + 1`
  have hpne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hPcard
    have hp2 : 2 ≤ (Nat.card ↥h.D.F).minFac := hpprime.two_le
    omega
  have hNU : B.U ⊓ Subgroup.normalizer (P : Set G) = B.U ⊓ h.D.M :=
    Work.CORE4.Case2Eight_NU B (Case2Ctx.toCtx6 h) P hPF hpne
  have hNPA : B.U ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (A : Set G) := by
    rw [hNU]
    exact Work.CORE4.Case2Eight_le_normalizer_A I B (Case2Ctx.toCtx6 h)
      (Nat.card ↥h.D.F).minFac P A hObj'
  have hp0odd : Odd (Work.GW2.Case2EightP0 B P A) :=
    Work.CORE4.Case2Eight_odd_p0 B (Nat.card ↥h.D.F).minFac P A hNPA
  have h6a : Work.GW2.Case2EightP0 B P A ≤ Work.GW2.Case2EightP1 P A :=
    Work.CORE4.Case2EightP0LeP1 B (Nat.card ↥h.D.F).minFac P A hPAsub hNPA
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x :=
    Work.CORE4.Case2Eight_A_comm I B (Case2Ctx.toCtx6 h) A hAle
  have h6b : Work.GW2.Case2EightP1 P A ≤ (Nat.card ↥h.D.F).minFac + 1 :=
    Work.CORE4.Case2EightP1Le (Nat.card ↥h.D.F).minFac P A hpprime hPAsub hAcard hAexp hAcomm
      hPcard
  -- `p` is odd (`p ∣ |F| ∣ |U|` and `U` has odd order), hence `p₀ ≤ p`
  have hpodd : Odd (Nat.card ↥h.D.F).minFac := by
    have h1 : (Nat.card ↥h.D.F).minFac ∣ Nat.card ↥h.D.F := by
      rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
    exact Odd.of_dvd_nat B.U_odd (h1.trans (Subgroup.card_dvd_of_le (h.D.F_le_U B)))
  have hp0p : Work.GW2.Case2EightP0 B P A ≤ (Nat.card ↥h.D.F).minFac :=
    Work.CORE4.Case2Eight_p0_le_p B (Nat.card ↥h.D.F).minFac P A hp0odd h6a h6b hpodd
  -- `p ∣ |K|` (§4 (7) gives `π(K) = π(F(U)) ∋ p`)
  have hpK : (Nat.card ↥h.D.F).minFac ∣ Nat.card ↥h.D.K := by
    have h1 : (Nat.card ↥h.D.F).minFac ∣ Nat.card ↥h.D.F := by
      rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
    exact Work.CORE4.prime_dvd_card_K_c4 B h.D h7 hpprime h1
  -- §4 (9): `k = |K| · |S₀|`
  have hkK : k = Nat.card ↥h.D.K * Nat.card ↥B.S0 :=
    Work.CORE4.Case2KmulS0 G I hbc B h q k k' hqodd hq7 hcases hrelMH
  -- §4 (8): `3 ≤ p₀` (from `A ⊴ F(U)` and `U ⊄ M`)
  have hp03 : 3 ≤ Work.GW2.Case2EightP0 B P A :=
    Work.CORE4.three_le_p0_of_not_invNormal I hbc B h (Nat.card ↥h.D.F).minFac P A hpprime hPF
      hPcard hObj' hInv hAn
  refine ⟨q, k, k', (Nat.card ↥h.D.F).minFac, P, A, Work.GW2.Case2EightU B A,
    Work.GW2.Case2EightP0 B P A, Work.GW2.Case2EightP1 P A, hqodd, hq7, hkeven, hk'odd,
    hcases, hrelMH, hkK, hpK, hpprime', hPF', hPcard', hAle, hAcard, hAexp, hPAsub, hAuniq,
    rfl, rfl, rfl, ?_, hp03, hp0odd, h6a, h6b, hp0p,
    Case2Num_two_p_le_k B h hkK hpK, Case2Num_one_le_relIndex B A, hup⟩
  -- `|H : H ⊓ M| = u · p₀` (§4 (10)).
  simpa only [Work.GW2.Case2EightU, Work.GW2.Case2EightP0] using
    Case2Num_MH_relIndex I B h P A hNU hNPA

/-- Bender 1981, §4 (7)–(8) and the objects of p. 225: the numbers `q, k, k', p`, the subgroups
`P ≤ F` (of order `p`), `A ≤ F·K` (the unique subgroup of type `(p,p)`, containing `P`) and the
numbers `u = |U : N_U(A)|`, `p₀ = |N_U(A) : N_U(P)|`, `p₁ = #{conjugates of P in A}`, with all
the inequalities Bender derives there (`3 ≤ p₀`, `p₀` odd, `p₀ ≤ p₁ ≤ p+1`, `p₀ ≤ p`, `2p ≤ k`,
`1 ≤ u ≤ p`), together with the parity data of §4 (10), the identity `k = |K|·|S₀|`, `p ∣ |K|`
and `|H : H ⊓ M| = u·p₀` (`N_U(P) = U ⊓ M`). -/
theorem Case2Numeric :
    ∀ (G : Type) [Group G] [Finite G] (I : Work.GW2.C4Inputs), Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ∃ (q k k' p : ℕ) (P A : Subgroup G) (u p0 p1 : ℕ),
          Odd q ∧ 7 ≤ q ∧ Even k ∧ Odd k' ∧
          ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) ∧
          (h.D.M ⊓ B.H).relIndex h.D.M = q * k' ∧
          k = Nat.card ↥h.D.K * Nat.card ↥B.S0 ∧ p ∣ Nat.card ↥h.D.K ∧
          p.Prime ∧ P ≤ h.D.F ∧ Nat.card ↥P = p ∧
          A ≤ h.D.F ⊔ h.D.K ∧ Nat.card ↥A = p ^ 2 ∧ (∀ x ∈ A, x ^ p = 1) ∧ P ≤ A ∧
          (∀ B' : Subgroup G, B' ≤ h.D.F ⊔ h.D.K → Nat.card ↥B' = p ^ 2 →
              (∀ x ∈ B', x ^ p = 1) → B' = A) ∧
          u = (B.U ⊓ Subgroup.normalizer (A : Set G)).relIndex B.U ∧
          p0 = (B.U ⊓ Subgroup.normalizer (P : Set G)).relIndex
                 (B.U ⊓ Subgroup.normalizer (A : Set G)) ∧
          p1 = {X : Subgroup G | X ≤ A ∧ ∃ g : G, X = Work.GW2.conjSub g P}.ncard ∧
          (h.D.M ⊓ B.H).relIndex B.H = u * p0 ∧
          3 ≤ p0 ∧ Odd p0 ∧ p0 ≤ p1 ∧ p1 ≤ p + 1 ∧ p0 ≤ p ∧ 2 * p ≤ k ∧ 1 ≤ u ∧ u ≤ p := by sorry

end Work.CORE4
