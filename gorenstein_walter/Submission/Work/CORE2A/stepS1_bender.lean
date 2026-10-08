import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.stepEDefs
import Submission.Work.CORE2A.pCoreIn_conjSub
import Submission.Work.CORE2A.dihOrCycSylow_subgroup
import Submission.Work.CORE2A.thm26_aux
import Submission.Work.CORE2A.bender26c_key
import Submission.Work.CORE2A.bender26c_stepE

/-!
# GW design pass 21 — Theorem 2.6 step 3 as Bender actually argues it (p. 220 last line – p. 221)

Bender's text (page image, J. Algebra 70 (1981) pp. 220–221; `H = C_G(t)`, **not** `Ĥ`):

> By minimality of `P`, 1.1.i, and 1.1.iv applied with `K = O_p(H)P`,
>     `P = [t,P]`  and  `P = N_P(O_p(H)) = C_P(O_p(H))`.
> … `1 ≠ P₀ := [t, C_P(s)] ⊆ C_G(s) = H^g ⊆ Ĥ^g`. …
> Lying in `O_p(H^g) = O_p(H)^g`, `P₀` centralizes `P^g`.

So the two facts are
* (L1)  `P ≤ C_G(O_p(C_G(t)))`                      — minimality + three-subgroup lemma;
* (L2)  `P₀ = ⁅⟨t⟩, P ⊓ C_G(s)⁆ ≤ O_p(C_G(s))`       — 1.10.i in the D-group `C_G(s)`,
        with the involution `t ∈ C_G(s)` (not `s`);
and `O_p(C_G(s)) = O_p(C_G(t))^g` is centralized by `P^g`.  No abelianness of any `O_p(M)`,
and no `E(M) = 1`, is used.  The printed `O_p(Ĥ^g)` in the OCR / previous notes was a misreading
of `O_p(H^g)`.
-/

namespace Work.GW21

open Subgroup Work.GW2

/-! ## L1a. In a `p`-group, `⁅P, Q⁆ = P` forces `P = 1` -/

theorem pgroup_eq_bot_of_commutator_eq {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P Q : Subgroup G} (hP : IsPGroup p P) (hQ : IsPGroup p Q)
    (hQN : Q ≤ normalizer (P : Set G)) (h : ⁅P, Q⁆ = P) : P = ⊥ := by
  set K : Subgroup G := P ⊔ Q with hK
  have hKp : IsPGroup p K := IsPGroup.to_sup_of_normal_left' hP hQ hQN
  have : Group.IsNilpotent ↥K := hKp.isNilpotent
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries (S := K)).mp inferInstance
  have hstep : ∀ m, P ≤ K.lowerCentralSeries m := by
    intro m
    induction m with
    | zero => exact le_sup_left
    | succ m ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      calc P = ⁅P, Q⁆ := h.symm
        _ ≤ ⁅K.lowerCentralSeries m, K⁆ := Subgroup.commutator_mono ih le_sup_right
  exact le_bot_iff.mp (hn ▸ hstep n)

/-! ## L1. `P` centralizes `O_p(C_G(t))` (Bender p. 220, last display) -/

theorem P_le_centralizer_pCoreIn_H (T : Work.GW2.LocalToolkit) {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (P : Subgroup G)
    (hP : IsPGroup p P) (hHN : B.H ≤ Subgroup.normalizer (P : Set G))
    (hmin : ∀ Q : Subgroup G, Q < P → IsPGroup p Q → B.H ≤ Subgroup.normalizer (Q : Set G) →
      Q ≤ Subgroup.centralizer ({B.t} : Set G))
    (hnot : ¬ P ≤ Subgroup.centralizer ({B.t} : Set G)) :
    P ≤ Subgroup.centralizer ((Work.GW2.pCoreIn p B.H : Subgroup G) : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  set Q : Subgroup G := Work.GW2.pCoreIn p B.H with hQdef
  have hQH : Q ≤ B.H := Subgroup.map_subtype_le _
  have hQp : IsPGroup p Q := Work.CORE2A.pCoreIn_isPGroup_gen p B.H
  have hQN : Q ≤ normalizer (P : Set G) := hQH.trans hHN
  have hHQ : B.H ≤ normalizer (Q : Set G) := Work.CORE2A.le_normalizer_pCoreIn B.H p
  set C : Subgroup G := ⁅P, Q⁆ with hCdef
  have hCP : C ≤ P := by
    rw [hCdef, Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hQN
  have hCH : B.H ≤ normalizer (C : Set G) := by
    intro h hh
    have h1 : h ∈ normalizer (P : Set G) := hHN hh
    have h2 : h ∈ normalizer (Q : Set G) := hHQ hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    rw [hCdef, Subgroup.map_commutator, h1, h2]
  have hPeq : ⁅Subgroup.zpowers B.t, P⁆ = P :=
    Work.CORE2A.b26c_commutator_eq T B p hp hp2 P hP hHN hmin hnot
  -- `[P,Q] = 1`
  have hbot : C = ⊥ := by
    by_cases hlt : C = P
    · exfalso
      have : P = ⊥ := pgroup_eq_bot_of_commutator_eq hP hQp hQN hlt
      exact hnot (by rw [this]; exact bot_le)
    · have hCt : C ≤ centralizer ({B.t} : Set G) :=
        hmin C (lt_of_le_of_ne hCP hlt) (hP.to_le hCP) hCH
      -- three-subgroup lemma with `⟨t⟩, P, Q`
      have h1 : ⁅⁅P, Q⁆, Subgroup.zpowers B.t⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨k, rfl⟩ := (Subgroup.mem_zpowers_iff (G := G)).mp hy
        have hc : Commute x B.t :=
          ((Subgroup.mem_centralizer_iff.mp (hCt hx)) B.t (Set.mem_singleton _)).symm
        exact (hc.zpow_right k).eq.symm
      have h2 : ⁅⁅Q, Subgroup.zpowers B.t⁆, P⁆ = ⊥ := by
        have : ⁅Q, Subgroup.zpowers B.t⁆ = ⊥ := by
          rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
          refine (Subgroup.zpowers_le (G := G)).mpr ?_
          rw [Subgroup.mem_centralizer_iff]
          intro q hq
          exact ((Subgroup.mem_centralizer_iff.mp (hQH hq)) B.t (Set.mem_singleton _)).symm
        rw [this, Subgroup.commutator_bot_left]
      have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
      rwa [hPeq] at h3
  rw [hCdef, Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
  exact hbot

/-! ## L2. `P₀ ≤ O_p(C_G(s))` (1.10.i in `C_G(s)` with the involution `t`) -/

theorem stepP1sub_le_pCoreIn_centralizer (T : Work.GW2.LocalToolkit)
    (hFT : Work.GW2.FeitThompsonProp) (G : Type) [Group G] [Finite G]
    (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (P : Subgroup G) (hP : IsPGroup p P)
    (hHN : B.H ≤ Subgroup.normalizer (P : Set G))
    (V : Subgroup G) (hV4 : Work.GW2.IsFourGroup V) (htV : B.t ∈ V)
    (g : G) (s : G) (hs : s = g * B.t * g⁻¹) (hsV : s ∈ V) :
    Work.CORE2A.stepP1sub B P s ≤
      Work.GW2.pCoreIn p (Subgroup.centralizer ({s} : Set G)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set K : Subgroup G := Subgroup.centralizer ({s} : Set G) with hK
  -- `t ∈ C_G(s)`: `V` has exponent 2, hence is abelian
  have hts : B.t * s = s * B.t := by
    have h1 : (B.t * s) ^ 2 = 1 := hV4.2 _ (V.mul_mem htV hsV)
    have h2 : B.t ^ 2 = 1 := hV4.2 _ htV
    have h3 : s ^ 2 = 1 := hV4.2 _ hsV
    have e1 : B.t⁻¹ = B.t := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h2)
    have e2 : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h3)
    have e3 : (B.t * s)⁻¹ = B.t * s := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h1)
    rw [mul_inv_rev, e1, e2] at e3
    exact e3.symm
  have htK : B.t ∈ K := by
    rw [hK, Subgroup.mem_centralizer_singleton_iff]
    exact hts
  -- `C_G(s) ≤ Ĥ^g ≠ ⊤`
  have hKle : K ≤ Work.GW2.conjSub g B.Hhat := by
    intro x hx
    rw [Work.CORE2A.mem_conjSub_iff]
    have hxs : s * x = x * s := (Subgroup.mem_centralizer_iff.mp hx) s (by simp)
    have hct : g⁻¹ * x * g ∈ Subgroup.centralizer ({B.t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have : g * B.t * g⁻¹ * x = x * (g * B.t * g⁻¹) := by rw [← hs]; exact hxs
      calc g⁻¹ * x * g * B.t = g⁻¹ * (x * (g * B.t * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * B.t * g⁻¹ * x) * g := by rw [this]
        _ = B.t * (g⁻¹ * x * g) := by group
    exact B.H_le_Hhat hct
  have hKne : K ≠ ⊤ := by
    intro htop
    have h1 : Work.GW2.conjSub g B.Hhat = ⊤ := top_le_iff.mp (htop ▸ hKle)
    have h2 : Work.GW2.conjSub g⁻¹ (Work.GW2.conjSub g B.Hhat) = ⊤ := by
      rw [h1, Work.CORE2A.conjSub_top]
    rw [Work.CORE2A.conjSub_inv_conjSub] at h2
    exact B.Hhat_coatom.ne_top h2
  have hD : Work.GW2.DihOrCycSylow ↥K := Work.CORE2A.dihOrCycSylow_subgroup hctx.sylow K
  have hDG : IsDGroup ↥K :=
    hctx.ih ↥K (Work.CORE2A.card_lt_card_of_ne_top hKne) hD
  have hP' : IsPGroup p ((P ⊓ K).subgroupOf K) :=
    (hP.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right : P ⊓ K ≤ K)).symm
  set t' : ↥K := ⟨B.t, htK⟩ with ht'def
  have ht'2 : orderOf t' = 2 := by
    rw [ht'def, Subgroup.orderOf_mk]
    exact B.t_order
  have hcen : Subgroup.centralizer ({t'} : Set ↥K) ≤
      Subgroup.normalizer ((P ⊓ K).subgroupOf K : Set ↥K) := by
    intro x hx
    have hxct : (x : G) ∈ Subgroup.centralizer ({B.t} : Set G) := by
      have h1 : t' * x = x * t' := (Subgroup.mem_centralizer_iff.mp hx) t' (by simp)
      have h3 := congrArg (Subtype.val) h1
      simp only [ht'def, Subgroup.coe_mul] at h3
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact h3.symm
    have hxN : (x : G) ∈ Subgroup.normalizer (P : Set G) := hHN hxct
    rw [Subgroup.mem_normalizer_iff] at hxN ⊢
    intro y
    constructor
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      rw [Subgroup.mem_subgroupOf]
      refine ⟨?_, ?_⟩
      · exact (hxN (y : G)).mp hy.1
      · change (x : G) * (y : G) * (x : G)⁻¹ ∈ K
        exact K.mul_mem (K.mul_mem x.2 hy.2) (K.inv_mem x.2)
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      rw [Subgroup.mem_subgroupOf]
      refine ⟨?_, ?_⟩
      · exact (hxN (y : G)).mpr hy.1
      · change (y : G) ∈ K
        exact y.2
  have hkey := T.d110i ↥K hFT hD hDG t' ht'2 p hp2 ((P ⊓ K).subgroupOf K) hP' hcen
  have hmap := Subgroup.map_mono (f := K.subtype) hkey
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (inf_le_right : P ⊓ K ≤ K),
      MonoidHom.map_zpowers] at hmap
  rw [Work.CORE2A.stepP1sub_def,
    Subgroup.commutator_comm (Subgroup.zpowers B.t) (P ⊓ Subgroup.centralizer ({s} : Set G))]
  simpa [Work.GW2.pCoreIn, hK] using hmap

/-! ## L3. `C_G(t^g) = C_G(t)^g` -/

theorem centralizer_conj_eq_conjSub {G : Type} [Group G] (g t : G) :
    Subgroup.centralizer ({g * t * g⁻¹} : Set G) =
      Work.GW2.conjSub g (Subgroup.centralizer ({t} : Set G)) := by
  ext x
  rw [Work.CORE2A.mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [h]
      _ = t * (g⁻¹ * x * g) := by group
  · intro h
    calc x * (g * t * g⁻¹) = g * ((g⁻¹ * x * g) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = g * t * g⁻¹ * x := by group

/-! ## Assembly: `StepS1Prop` (Bender: "Lying in `O_p(H^g) = O_p(H)^g`, `P₀` centralizes `P^g`") -/

theorem stepS1Prop_bender : Work.CORE2A.StepS1Prop := by
  intro T h21 h23 h24 h25 G _ _ hFT hctx B p hp hp2 P hPp hPH hmin hnot M hM hNPM V hV4 hVS htV
    g hgN hgM s hs hsV hbig
  -- (L1) conjugated: `P^g ≤ C_G(O_p(C_G(t))^g)`
  have hL1 := P_le_centralizer_pCoreIn_H T B p hp hp2 P hPp hPH hmin hnot
  -- (L2): `P₀ ≤ O_p(C_G(s)) = O_p(C_G(t))^g`
  have hL2 := stepP1sub_le_pCoreIn_centralizer T hFT G hctx B p hp hp2 P hPp hPH V hV4 htV g s
    hs hsV
  rw [hs, centralizer_conj_eq_conjSub, Work.CORE2A.pCoreIn_conjSub] at hL2
  rw [← hs] at hL2
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  intro x hx
  rw [Work.CORE2A.mem_conjSub_iff] at hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' := hL2 hy
  rw [Work.CORE2A.mem_conjSub_iff] at hy'
  have hc := (Subgroup.mem_centralizer_iff.mp (hL1 hx)) _ hy'
  -- hc : (g⁻¹ y g) (g⁻¹ x g) = (g⁻¹ x g) (g⁻¹ y g)
  have := congrArg (fun z => g * z * g⁻¹) hc
  simp only [mul_assoc, mul_inv_cancel_left] at this
  simpa [mul_assoc] using this

end Work.GW21
