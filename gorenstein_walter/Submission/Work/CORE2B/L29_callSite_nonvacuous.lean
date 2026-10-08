import Mathlib
import Submission.Work.CORE2B.L29CallSite
import Submission.Work.CORE2B.t_central_in_S
import Submission.Work.CORE2B.oddCore_odd
import Submission.Work.CORE2B.sylow_not_cyclic_of_sub

namespace Work.CORE2B

open Subgroup
open scoped commutatorElement

/-! ## Elementary group-theoretic helpers used below

These are the pieces of the argument that have nothing to do with Bender's notation. -/

/-- A subgroup of order `4` all of whose elements are involutions is not cyclic. -/
theorem not_isCyclic_of_card_four {G : Type*} [Group G] (V : Subgroup G)
    (hcard : Nat.card ↥V = 4) (hexp : ∀ v ∈ V, v ^ 2 = 1) : ¬ IsCyclic V := by
  intro hcyc
  haveI := hcyc
  obtain ⟨v, hv⟩ := IsCyclic.exists_generator (α := ↥V)
  have htop : Subgroup.zpowers v = ⊤ := by
    ext x; exact ⟨fun _ => trivial, fun _ => hv x⟩
  have hord : orderOf v = 4 := by
    rw [← Nat.card_zpowers (a := v), htop, Subgroup.card_top, hcard]
  have h2 : (v : G) * (v : G) = 1 := by
    have := hexp (v : G) v.2
    rwa [sq] at this
  have h3 : orderOf (v : G) = orderOf v :=
    orderOf_injective (Subgroup.subtype V) Subtype.val_injective v
  have hdvd : orderOf (v : G) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact h2)
  have hle : orderOf (v : G) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- For a four-group `V ≤ N`, the relative subgroup `V.subgroupOf N` is a non-cyclic `2`-group. -/
theorem subgroupOf_four_not_cyclic {G : Type} [Group G] [Finite G] (V N : Subgroup G)
    (hV : Work.GW2.IsFourGroup V) (h : V ≤ N) :
    IsPGroup 2 ↥(V.subgroupOf N) ∧ ¬ IsCyclic ↥(V.subgroupOf N) := by
  obtain ⟨hcard, hsq⟩ := hV
  have hcard' : Nat.card ↥(V.subgroupOf N) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]
    exact hcard
  have hexp : ∀ v ∈ V.subgroupOf N, v ^ 2 = 1 := by
    intro v hv
    apply Subtype.ext
    simpa [pow_two] using hsq (v : G) hv
  refine ⟨?_, not_isCyclic_of_card_four _ hcard' hexp⟩
  have h22 : Nat.card ↥(V.subgroupOf N) = 2 ^ 2 := by rw [hcard']; norm_num
  exact IsPGroup.of_card h22

/-- A non-trivial commutator `⁅H,K⁆` has a cyclic witness in `H`: there is `s ∈ H` with
`⁅⟨s⟩,K⁆ ≠ ⊥`. -/
theorem commutator_zpowers_ne_bot {G : Type} [Group G]
    (H K : Subgroup G) (h : ⁅H, K⁆ ≠ ⊥) :
    ∃ s ∈ H, ⁅Subgroup.zpowers s, K⁆ ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  exact h (bot_unique ((Subgroup.commutator_le).mpr (fun g₁ hg₁ g₂ hg₂ => by
    have h1 : ⁅g₁, g₂⁆ ∈ ⁅Subgroup.zpowers g₁, K⁆ := by
      rw [Subgroup.commutator_def]
      exact Subgroup.subset_closure ⟨g₁, Subgroup.mem_zpowers g₁, g₂, hg₂, rfl⟩
    rw [hcon g₁ hg₁] at h1
    simpa using h1)))

/-- The size clause of Bender's Lemma 2.7 at a call site with `S ≤ N`. -/
theorem eight_le_or_eq_four {G : Type} [Group G] [Finite G] (S N V : Subgroup G)
    (hS : IsPGroup 2 ↥S) (hSN : S ≤ N) (hV : Work.GW2.IsFourGroup V) (hVS : V ≤ S) :
    8 ≤ Nat.card (S ⊓ N : Subgroup G) ∨ Nat.card S = 4 := by
  obtain ⟨hcardV, -⟩ := hV
  have hinf : S ⊓ N = S := inf_eq_left.mpr hSN
  have h4 : 4 ≤ Nat.card ↥S := by
    have hd : Nat.card ↥V ∣ Nat.card ↥S := Subgroup.card_dvd_of_le hVS
    rw [hcardV] at hd
    exact Nat.le_of_dvd Nat.card_pos hd
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hS
  have h4' : 4 ≤ 2 ^ n := by rw [← hn]; exact h4
  by_cases hn2 : n ≤ 2
  · right
    rw [hn]
    have hle : 2 ^ n ≤ 4 := by
      calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
        _ = 4 := by norm_num
    omega
  · left
    rw [hinf, hn]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ## The call-site lemma -/

/-- At the call sites of Bender 1981, Lemma 2.9 (where `N` is a maximal subgroup with `Ĥ ⇝ N`,
`¬N ≤ Ĥ`, `S ≤ N`) the hypothesis `hyp` of `L29Hyp` is **satisfied non-vacuously**: there are
`s ∈ S` and `1 ≠ X ≤ U` with `X = [⟨s⟩,X]` — the antecedent of `hyp`, so that `hyp` may be applied
to it and yields `t ∈ O₂(N_G(X))`.

Route.  (i) `S ≤ C_G(t)` (`Work.CORE2B.t_central_in_S`) and `U = O(C_G(t))` is normal in `C_G(t)`,
so `S ≤ N_G(U)`; in particular `s ∈ S` normalises `U` for every `s ∈ S`.  (ii) Lemma 2.7 (`h27`)
applied to `N` (its hypotheses are the call-site data: `N ≠ ⊤`, `Ĥ ⇝ N`, `¬N ≤ Ĥ`, `t ∈ N`,
`t ∉ E(N)` from `V ∩ E(N) = ⊥` and `t ∈ V`, all Sylow 2-subgroups of `N` non-cyclic because
`V ≅ 2² ≤ N` is a non-cyclic 2-subgroup, and the size clause because `S ≤ N` gives `S ⊓ N = S`
while `4 = |V| ≤ |S|` is a power of 2) gives `¬ [S,U] ≤ F(U)`, hence `[S,U] ≠ ⊥`; since `[S,U]`
is the join of the `[⟨s⟩,U]`, some `s ∈ S` has `[⟨s⟩,U] ≠ ⊥`.  (iii) For that `s`,
`X := [⟨s⟩,U] ≤ U` (as `s` normalises `U`) and `X = [⟨s⟩,X]` by `T.c11i` (coprime action of the
2-group `⟨s⟩` on the odd group `U`). -/
theorem L29_callSite_nonvacuous {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp)
    (hctx : Work.GW2.BenderCtx G) (h27 : Work.GW2.Lemma27Prop) (B : Work.GW2.BenderSetup G)
    (V N : Subgroup G) (h : Work.CORE2B.L29CallSite B V N)
    (h2 : V ⊓ Work.GW2.layerIn N = ⊥) :
    ∃ s ∈ (B.S : Subgroup G), ∃ X : Subgroup G,
      X ≤ B.U ∧ X ≠ ⊥ ∧ ⁅Subgroup.zpowers s, X⁆ = X := by
  classical
  -- `t ≠ 1`
  have ht_ne_one : B.t ≠ 1 := by
    intro h1
    have hord := B.t_order
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  -- (i) `S ≤ C_G(t) = H` and `U ⊴ H`, hence `S ≤ N_G(U)`.
  have hSH : (B.S : Subgroup G) ≤ B.H := by
    intro x hx
    show x ∈ Subgroup.centralizer ({B.t} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (t_central_in_S B x hx).symm
  have hHNU : B.H ≤ Subgroup.normalizer (B.U : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg u hu
    have hu' : u ∈ (Work.GW2.oddCore ↥B.H).map B.H.subtype := hu
    rw [Subgroup.mem_map] at hu'
    obtain ⟨k, hk, rfl⟩ := hu'
    have hconj : (⟨g, hg⟩ : ↥B.H) * k * (⟨g, hg⟩ : ↥B.H)⁻¹ ∈ Work.GW2.oddCore ↥B.H :=
      (Work.GW2.oddCore_normal ↥B.H).conj_mem k hk ⟨g, hg⟩
    exact Subgroup.mem_map_of_mem B.H.subtype hconj
  have hSNU : (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) := hSH.trans hHNU
  -- (ii) Bender's Lemma 2.7 applied to `N`.
  have htN : B.t ∈ N := h.hyp.V_le_N h.hyp.t_mem
  have ht_not_layer : B.t ∉ Work.GW2.layerIn N := by
    intro ht
    have hmem : B.t ∈ V ⊓ Work.GW2.layerIn N := ⟨h.hyp.t_mem, ht⟩
    rw [h2] at hmem
    exact ht_ne_one (Subgroup.mem_bot.mp hmem)
  have hsyl : ∀ P : Sylow 2 N, ¬ IsCyclic P := by
    intro P
    obtain ⟨hP2, hPnc⟩ := subgroupOf_four_not_cyclic V N h.hyp.four h.hyp.V_le_N
    exact sylow_not_cyclic_of_sub (V.subgroupOf N) hP2 hPnc P
  have hsize : 8 ≤ Nat.card ((B.S : Subgroup G) ⊓ N : Subgroup G) ∨
      Nat.card (B.S : Subgroup G) = 4 ∨ B.t ∈ Work.GW2.twoResidualIn N := by
    have hS2 : IsPGroup 2 ↥(B.S : Subgroup G) := Sylow.isPGroup' B.S
    rcases eight_le_or_eq_four (B.S : Subgroup G) N V hS2 h.S_le_N h.hyp.four h.hyp.V_le_S with
      h8 | h4
    · exact Or.inl h8
    · exact Or.inr (Or.inl h4)
  have h27res := h27 G hFT hctx B N h.hyp.N_ne_top h.rel h.not_le htN ht_not_layer hsyl hsize
  have hsu : ⁅(B.S : Subgroup G), B.U⁆ ≠ ⊥ :=
    fun hbot => h27res.2.1 (by rw [hbot]; exact bot_le)
  -- (iii) Some `s ∈ S` has `⁅⟨s⟩,U⁆ ≠ ⊥`; for it the coprime action of `⟨s⟩` on the odd group
  -- `U` gives `⁅⟨s⟩,⁅⟨s⟩,U⁆⁆ = ⁅⟨s⟩,U⁆`.
  obtain ⟨s, hsS, hsX⟩ := commutator_zpowers_ne_bot (B.S : Subgroup G) B.U hsu
  have hzn : Subgroup.zpowers s ≤ Subgroup.normalizer (B.U : Set G) :=
    (Subgroup.zpowers_le.mpr hsS).trans hSNU
  have hcop : Nat.Coprime 2 (Nat.card B.U) := by
    rw [Nat.coprime_two_left]
    have hcard : Nat.card ↥B.U = Nat.card ↥(Work.GW2.oddCore ↥B.H) := by
      show Nat.card ↥((Work.GW2.oddCore ↥B.H).map B.H.subtype)
        = Nat.card ↥(Work.GW2.oddCore ↥B.H)
      exact Subgroup.card_map_of_injective Subtype.val_injective
    rw [hcard]
    exact oddCore_odd
  have hP2 : IsPGroup 2 ↥(Subgroup.zpowers s) :=
    IsPGroup.to_le (Sylow.isPGroup' B.S) (Subgroup.zpowers_le.mpr hsS)
  refine ⟨s, hsS, ⁅Subgroup.zpowers s, B.U⁆, ?_, hsX, ?_⟩
  · rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have h1 : g₁ * g₂ * g₁⁻¹ ∈ B.U := (Subgroup.le_normalizer_iff.mp hzn) g₁ hg₁ g₂ hg₂
    rw [commutatorElement_def]
    exact B.U.mul_mem h1 (B.U.inv_mem hg₂)
  · exact (T.c11i G 2 (Subgroup.zpowers s) B.U hP2 hcop hzn).1

end Work.CORE2B

