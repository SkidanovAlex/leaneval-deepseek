import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.DoubleTransitivity.App2.app2_1
import Submission.Work.DoubleTransitivity.App2.app2_2
import Submission.Work.DoubleTransitivity.App2.app2_4
import Submission.Work.DoubleTransitivity.App2.app2_5

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

/-! ## Two elementary Sylow lemmas used below -/

/-- Being a `p`-Sylow subgroup of `D` only depends on the order of `D` (for a fixed `p`-subgroup
`P ≤ D`). -/
theorem app2_6_isSylowSubgroupOf_of_card_eq {G : Type} [Group G] [Finite G] {p : ℕ}
    {P D D' : Subgroup G} (h : Work.DoubleTransitivity.IsSylowSubgroupOf p P D') (hP : P ≤ D)
    (hcard : Nat.card ↥D = Nat.card ↥D') : Work.DoubleTransitivity.IsSylowSubgroupOf p P D := by
  refine ⟨hP, h.2.1, ?_⟩
  have e1 : Nat.card ↥(P.subgroupOf D) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv
  have e2 : Nat.card ↥(P.subgroupOf D') = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.1).toEquiv
  have h1 := Subgroup.card_mul_index (P.subgroupOf D)
  have h2 := Subgroup.card_mul_index (P.subgroupOf D')
  rw [e1] at h1
  rw [e2, ← hcard] at h2
  have hin : (P.subgroupOf D).index = (P.subgroupOf D').index :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  rw [hin]; exact h.2.2

/-- If a `p`-subgroup `P` of `D` is not a `p`-Sylow subgroup of `D`, then some `p`-subgroup of
`D` strictly contains it. -/
theorem app2_6_exists_pSubgroup_lt_of_dvd_index {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {P D : Subgroup G} (hPp : IsPGroup p P) (hPD : P ≤ D)
    (h : p ∣ (P.subgroupOf D).index) :
    ∃ Q : Subgroup G, Q ≤ D ∧ IsPGroup p Q ∧ P < Q := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Qd, hQd⟩ := IsPGroup.exists_le_sylow
    (hPp.comap_of_injective D.subtype Subtype.coe_injective :
      IsPGroup p ↥(P.subgroupOf D))
  have hQdne : (Qd : Subgroup ↥D) ≠ P.subgroupOf D := by
    intro heq
    have h2 := Sylow.not_dvd_index Qd
    rw [heq] at h2
    exact h2 h
  refine ⟨(Qd : Subgroup ↥D).map D.subtype, Subgroup.map_subtype_le _,
    Qd.isPGroup'.map D.subtype, ?_⟩
  have hle : P ≤ (Qd : Subgroup ↥D).map D.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hPD]
    exact Subgroup.map_mono hQd
  refine lt_of_le_of_ne hle fun heq => hQdne ?_
  have h2 : (P.subgroupOf D).map D.subtype = (Qd : Subgroup ↥D).map D.subtype :=
    (Subgroup.map_subgroupOf_eq_of_le hPD).trans heq
  have h3 := congrArg (Subgroup.comap D.subtype) h2
  rw [Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective,
      Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective] at h3
  exact h3.symm

/-! ## Appendix II (6) in the abstract setting `X` acting on `E` -/

/-- **Peterfalvi I, Appendix II (6)**, abstract form: `X` is a finite group acting on a finite
set `E`, `P ≤ X_a` is a `p`-subgroup maximal among the `p`-subgroups of the point stabiliser
`X_a` with at least `3` fixed points.  Then `P` is maximal among *all* `p`-subgroups of `X`
with at least `3` fixed points, and `N_X(P)` acts `2`-transitively on the fixed-point set `E_P`.

The proof is the source's (p. 205): if `P` is a `p`-Sylow of the two-point stabiliser `X_a ⊓ X_b`
(with `b ∈ E_P \ {a}`) then App. II (5) (`app2_5`) gives the `2`-transitivity of `N_X(P)` on
`E_P`.  Otherwise, for each `c ∈ E_P \ {a}` a `p`-Sylow of `N_X(P) ⊓ X_a ⊓ X_c` strictly
contains `P` (since `P` is not a `p`-Sylow of `X_a ⊓ X_c`), hence has exactly the two fixed
points `a, c`; and a `p`-Sylow of `N_X(P) ⊓ X_c ⊓ X_d` for distinct `c, d ∈ E_P \ {a}` is not
contained in `X_a`, so `N_X(P)` does not fix `a`.  App. II (3) (`app2_3`), applied to the action
of `N_X(P)` on `E_P`, then gives `2`-transitivity.  Part (i) is the standard consequence: a
`p`-subgroup `R ≥ P` fixing three points is conjugate by an element of `N_X(P)` into `X_a`, and
maximality of `P` in `X_a` forces `R = P`. -/
theorem app2_6_abstract {X E : Type} [Group X] [MulAction X E] [Finite X] [Fintype E]
    {p : ℕ} (hp : p.Prime) {a : E}
    (h2 : MulAction.IsMultiplyPretransitive X E 2)
    {P : Subgroup X} (hP : IsPGroup p P) (hPa : P ≤ MulAction.stabilizer X a)
    (hbig : 3 ≤ (Work.DoubleTransitivity.fixedBySub (E := E) P).ncard)
    (hmax : ∀ Q : Subgroup X, P ≤ Q → Q ≤ MulAction.stabilizer X a → IsPGroup p Q →
      3 ≤ (Work.DoubleTransitivity.fixedBySub (E := E) Q).ncard → Q = P) :
    (∀ R : Subgroup X, P ≤ R → IsPGroup p R →
      3 ≤ (Work.DoubleTransitivity.fixedBySub (E := E) R).ncard → R = P) ∧
      Work.DoubleTransitivity.IsTwoTransitiveOnSub (Subgroup.normalizer (P : Set X))
        (Work.DoubleTransitivity.fixedBySub (E := E) P) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set EP : Set E := Work.DoubleTransitivity.fixedBySub (E := E) P with hEPdef
  set N : Subgroup X := Subgroup.normalizer (P : Set X) with hNdef
  have haEP : a ∈ EP := hPa
  have hEPbig : 3 ≤ EP.ncard := hbig
  have h2p : ∀ {u v u' v' : E}, u ≠ v → u' ≠ v' → ∃ g : X, g • u = u' ∧ g • v = v' :=
    fun huv huv' => (MulAction.is_two_pretransitive_iff.mp h2) huv huv'
  obtain ⟨b₀, hb₀EP, hb₀ne⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < EP.ncard) a
  -- two distinct points of `EP \ {a}`
  have h2diff : 2 ≤ (EP \ {a}).ncard := by
    have hsub : EP ⊆ insert a (EP \ {a}) := by
      intro x hx
      by_cases h : x = a
      · exact Set.mem_insert_iff.mpr (Or.inl h)
      · exact Set.mem_insert_iff.mpr (Or.inr ⟨hx, h⟩)
    have h1 := Set.ncard_le_ncard hsub
    have h2' := Set.ncard_insert_le a (EP \ {a})
    omega
  obtain ⟨c₀, hc₀, hc₀ne⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < (EP \ {a}).ncard) a
  have hc₀EP : c₀ ∈ EP := hc₀.1
  have hc₀ne_a : c₀ ≠ a := hc₀.2
  have hne2 : ((EP \ {a}) \ {c₀}).Nonempty := by
    rw [← Set.ncard_pos]
    have h1 := Set.ncard_sdiff_singleton_add_one hc₀
    omega
  obtain ⟨d₀, hd₀⟩ := hne2
  have hd₀EP : d₀ ∈ EP := hd₀.1.1
  have hd₀ne_a : d₀ ≠ a := hd₀.1.2
  have hd₀ne_c : d₀ ≠ c₀ := hd₀.2
  -- two-point stabilisers of pairs in `EP` all have the same order
  have hcard_stab : ∀ {u v : E}, u ≠ v →
      Nat.card ↥(MulAction.stabilizer X u ⊓ MulAction.stabilizer X v)
        = Nat.card ↥(MulAction.stabilizer X a ⊓ MulAction.stabilizer X b₀) := by
    intro u v huv
    obtain ⟨g, hgu, hgv⟩ := h2p hb₀ne.symm huv
    have hconj : conj g (MulAction.stabilizer X a ⊓ MulAction.stabilizer X b₀)
        = MulAction.stabilizer X u ⊓ MulAction.stabilizer X v := by
      rw [conj_inf, ← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj g a,
        ← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj g b₀, hgu, hgv]
    rw [← hconj]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hle_of_mem : ∀ c : E, c ∈ EP → P ≤ MulAction.stabilizer X c :=
    fun c hc x hx => MulAction.mem_stabilizer_iff.mpr
      ((Work.DoubleTransitivity.mem_fixedBySub.mp hc) x hx)
  have hPab : P ≤ MulAction.stabilizer X a ⊓ MulAction.stabilizer X b₀ :=
    fun x hx => ⟨hPa hx, hle_of_mem b₀ hb₀EP hx⟩
  have h2t : Work.DoubleTransitivity.IsTwoTransitiveOnSub N EP := by
    by_cases hcase1 : Work.DoubleTransitivity.IsSylowSubgroupOf p P
        (MulAction.stabilizer X a ⊓ MulAction.stabilizer X b₀)
    · have ht := Work.DoubleTransitivity.App2.app2_5 (p := p) hb₀ne.symm h2 hcase1
      rwa [hNdef, hEPdef]
    · -- `P` is not a `p`-Sylow of the two-point stabiliser
      have hcase2 : p ∣ (P.subgroupOf (MulAction.stabilizer X a
          ⊓ MulAction.stabilizer X b₀)).index := by
        by_contra hcon
        exact hcase1 ⟨hPab, hP, hcon⟩
      have hdvd : ∀ {u v : E}, u ∈ EP → v ∈ EP → u ≠ v →
          p ∣ (P.subgroupOf (MulAction.stabilizer X u ⊓ MulAction.stabilizer X v)).index := by
        intro u v hu hv huv
        by_contra hcon
        have hsyl : Work.DoubleTransitivity.IsSylowSubgroupOf p P
            (MulAction.stabilizer X u ⊓ MulAction.stabilizer X v) :=
          ⟨fun x hx => ⟨hle_of_mem u hu hx, hle_of_mem v hv hx⟩, hP, hcon⟩
        exact hcase1 (app2_6_isSylowSubgroupOf_of_card_eq hsyl hPab (hcard_stab huv).symm)
      -- a `p`-subgroup of `X_a` strictly above `P` has fewer than three fixed points
      have hfix_lt : ∀ R : Subgroup X, R ≤ MulAction.stabilizer X a → IsPGroup p R → P < R →
          (Work.DoubleTransitivity.fixedBySub (E := E) R).ncard < 3 := by
        intro R hRa hRg hlt
        by_contra hcon
        exact hlt.ne' (hmax R hlt.le hRa hRg (by omega))
      -- for `c ∈ EP \ {a}`: a `p`-subgroup of `N` with fixed point set `{a, c}`
      have hRc : ∀ c ∈ EP, c ≠ a → ∃ R : Subgroup X, R ≤ N ∧ IsPGroup p R ∧ P < R ∧
          (Work.DoubleTransitivity.fixedBySub (E := E) R) = {a, c} := by
        intro c hcEP hca
        have hdac : P ≤ MulAction.stabilizer X a ⊓ MulAction.stabilizer X c :=
          fun x hx => ⟨hPa hx, hle_of_mem c hcEP hx⟩
        obtain ⟨Q₀, hQ₀le, hQ₀g, hQ₀lt⟩ := app2_6_exists_pSubgroup_lt_of_dvd_index hp hP hdac
          (hdvd haEP hcEP (fun h => hca h.symm))
        have hQ₀a : Q₀ ≤ MulAction.stabilizer X a := le_trans hQ₀le inf_le_left
        have hlt : P < Q₀ ⊓ N := Work.Coprime.lt_inf_normalizer_of_lt hQ₀g hQ₀lt
        refine ⟨Q₀ ⊓ N, by rw [hNdef]; exact inf_le_right, hQ₀g.to_inf_left, hlt, ?_⟩
        have hle_a : Q₀ ⊓ N ≤ MulAction.stabilizer X a := le_trans inf_le_left hQ₀a
        have hlt3 := hfix_lt (Q₀ ⊓ N) hle_a hQ₀g.to_inf_left hlt
        have hsub : ({a, c} : Set E) ⊆
            (Work.DoubleTransitivity.fixedBySub (E := E) (Q₀ ⊓ N)) := by
          intro x hx
          rcases hx with h | h
          · rw [h, Work.DoubleTransitivity.mem_fixedBySub]
            exact fun m hm => MulAction.mem_stabilizer_iff.mp (hle_a hm)
          · rw [h, Work.DoubleTransitivity.mem_fixedBySub]
            exact fun m hm =>
              MulAction.mem_stabilizer_iff.mp (le_trans inf_le_left (le_trans hQ₀le inf_le_right) hm)
        have h2' : (Work.DoubleTransitivity.fixedBySub (E := E) (Q₀ ⊓ N)).ncard ≤
            ({a, c} : Set E).ncard := by
          rw [Set.ncard_pair hca.symm]
          omega
        exact (Set.eq_of_subset_of_ncard_le hsub h2').symm
      -- `N` does not fix `a`
      have hNfix : ∃ n ∈ N, n • a ≠ a := by
        have hdcd : P ≤ MulAction.stabilizer X c₀ ⊓ MulAction.stabilizer X d₀ :=
          fun x hx => ⟨hle_of_mem c₀ hc₀EP hx, hle_of_mem d₀ hd₀EP hx⟩
        obtain ⟨Q₀, hQ₀le, hQ₀g, hQ₀lt⟩ := app2_6_exists_pSubgroup_lt_of_dvd_index hp hP hdcd
          (hdvd hc₀EP hd₀EP (fun h => hd₀ne_c h.symm))
        have hRlt : P < Q₀ ⊓ N := Work.Coprime.lt_inf_normalizer_of_lt hQ₀g hQ₀lt
        have hRle_cd : Q₀ ⊓ N ≤ MulAction.stabilizer X c₀ ⊓ MulAction.stabilizer X d₀ :=
          le_trans inf_le_left hQ₀le
        by_contra hcon
        push_neg at hcon
        have hRa : Q₀ ⊓ N ≤ MulAction.stabilizer X a := by
          intro r hr
          exact MulAction.mem_stabilizer_iff.mpr (hcon r hr.2)
        have hR3 : 3 ≤ (Work.DoubleTransitivity.fixedBySub (E := E) (Q₀ ⊓ N)).ncard := by
          have hsub : ({a, c₀, d₀} : Set E) ⊆
              (Work.DoubleTransitivity.fixedBySub (E := E) (Q₀ ⊓ N)) := by
            intro x hx
            rcases hx with h | h | h
            · rw [h, Work.DoubleTransitivity.mem_fixedBySub]
              exact fun m hm => MulAction.mem_stabilizer_iff.mp (hRa hm)
            · rw [h, Work.DoubleTransitivity.mem_fixedBySub]
              exact fun m hm => MulAction.mem_stabilizer_iff.mp ((le_trans hRle_cd inf_le_left) hm)
            · rw [h, Work.DoubleTransitivity.mem_fixedBySub]
              exact fun m hm => MulAction.mem_stabilizer_iff.mp ((le_trans hRle_cd inf_le_right) hm)
          have hpair : ({a, c₀, d₀} : Set E).ncard = 3 := by
            rw [Set.ncard_eq_three]
            exact ⟨a, c₀, d₀, hc₀ne_a.symm, hd₀ne_a.symm, hd₀ne_c.symm, rfl⟩
          rw [← hpair]
          exact Set.ncard_le_ncard hsub
        exact hRlt.ne' (hmax (Q₀ ⊓ N) hRlt.le hRa hQ₀g.to_inf_left hR3)
      -- App. II (3) applied to `N` acting on `EP`
      have hNsmul : ∀ (n : X), n ∈ N → ∀ x ∈ EP, n • x ∈ EP :=
        fun n hn x hx => Work.DoubleTransitivity.App2.smul_mem_fixedBySub_of_mem_normalizer hn hx
      let actN : MulAction ↥N ↥EP :=
        { smul := fun m x => ⟨(m : X) • (x : E), hNsmul (m : X) m.2 (x : E) x.2⟩
          one_smul := fun x => Subtype.ext (one_smul X (x : E))
          mul_smul := fun m₁ m₂ x => Subtype.ext (mul_smul (m₁ : X) (m₂ : X) (x : E)) }
      letI := actN
      have h30 : ∀ c ∈ ({⟨a, haEP⟩}ᶜ : Set ↥EP), ∃ P' : Subgroup ↥N, IsPGroup p P' ∧
          (Work.DoubleTransitivity.fixedBySub P' : Set ↥EP) = {⟨a, haEP⟩, c} := by
        intro c hc
        rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hc
        obtain ⟨R, hRleN, hRg, _hRlt, hRfix⟩ := hRc (c : E) c.2 (fun h => hc (Subtype.ext h))
        refine ⟨R.subgroupOf N, hRg.comap_of_injective N.subtype Subtype.coe_injective, ?_⟩
        ext z
        rw [Work.DoubleTransitivity.mem_fixedBySub]
        constructor
        · intro hz
          have hz' : (z : E) ∈ (Work.DoubleTransitivity.fixedBySub (E := E) R) := by
            intro r hr
            exact congrArg (fun y : ↥EP => (y : E))
              (hz ⟨r, hRleN hr⟩ (Subgroup.mem_subgroupOf.mpr hr))
          rw [hRfix] at hz'
          rcases hz' with h | h
          · exact Or.inl (Subtype.ext h)
          · exact Or.inr (Subtype.ext h)
        · intro hz
          rcases hz with h | h
          · rw [h]
            intro m hm
            apply Subtype.ext
            exact (Work.DoubleTransitivity.mem_fixedBySub.mp
              (by rw [hRfix]; exact Or.inl rfl)) (m : X) (Subgroup.mem_subgroupOf.mp hm)
          · rw [h]
            intro m hm
            apply Subtype.ext
            exact (Work.DoubleTransitivity.mem_fixedBySub.mp
              (by rw [hRfix]; exact Or.inr rfl)) (m : X) (Subgroup.mem_subgroupOf.mp hm)
      have h30fix : ¬ ∀ x : ↥N, x • (⟨a, haEP⟩ : ↥EP) = ⟨a, haEP⟩ := by
        intro hcon
        obtain ⟨n, hnN, hna⟩ := hNfix
        exact hna (congrArg (fun y : ↥EP => (y : E)) (hcon ⟨n, hnN⟩))
      have h3t := Work.DoubleTransitivity.App2.app2_3 (X := ↥N) (E := ↥EP) (p := p) h30 h30fix
      intro c hc d hd hcd c' hc' d' hd' hcd'
      have hne1 : (⟨c, hc⟩ : ↥EP) ≠ ⟨d, hd⟩ := fun h => hcd (Subtype.ext_iff.mp h)
      have hne2 : (⟨c', hc'⟩ : ↥EP) ≠ ⟨d', hd'⟩ := fun h => hcd' (Subtype.ext_iff.mp h)
      obtain ⟨m, hm1, hm2⟩ := (MulAction.is_two_pretransitive_iff.mp h3t) hne1 hne2
      exact ⟨(m : X), m.2, congrArg (fun y : ↥EP => (y : E)) hm1,
        congrArg (fun y : ↥EP => (y : E)) hm2⟩
  refine ⟨?_, h2t⟩
  -- Part (i)
  intro R hPR hRg hR3
  have hRsub : (Work.DoubleTransitivity.fixedBySub (E := E) R) ⊆ EP := by
    rw [hEPdef]
    exact Work.DoubleTransitivity.fixedBySub_antitone hPR
  have hneR : (Work.DoubleTransitivity.fixedBySub (E := E) R).Nonempty := by
    rw [← Set.ncard_pos]
    omega
  obtain ⟨c, hcR⟩ := hneR
  have hcEP : c ∈ EP := hRsub hcR
  obtain ⟨n, hnN, hna⟩ := h2t.isTransitiveOnSub a haEP c hcEP
  have hRfixc : R ≤ MulAction.stabilizer X c :=
    fun r hr => MulAction.mem_stabilizer_iff.mpr
      ((Work.DoubleTransitivity.mem_fixedBySub.mp hcR) r hr)
  have hnR : conj n⁻¹ R ≤ MulAction.stabilizer X a := by
    have hconj : conj n⁻¹ (MulAction.stabilizer X c) = MulAction.stabilizer X a := by
      rw [(Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj n⁻¹ c).symm]
      congr 1
      rw [← hna, inv_smul_smul]
    exact le_trans (Subgroup.map_mono hRfixc) (le_of_eq hconj)
  have hnP : conj n P = P := Subgroup.mem_normalizer_iff_map_conj_eq.mp hnN
  have hnP' : conj n⁻¹ P = P := by
    conv_lhs => rw [← hnP]
    rw [← conj_mul, inv_mul_cancel, conj_one]
  have hPn : P ≤ conj n⁻¹ R := by
    rw [← hnP']
    exact Subgroup.map_mono hPR
  have hcard : 3 ≤ (Work.DoubleTransitivity.fixedBySub (E := E) (conj n⁻¹ R)).ncard := by
    rw [Work.DoubleTransitivity.App2.app2_3_fixedBySub_map_conj R n⁻¹, Set.ncard_smul_set]
    exact hR3
  have hle : conj n⁻¹ R = P := hmax (conj n⁻¹ R) hPn hnR (hRg.map _) hcard
  have h1 : conj n (conj n⁻¹ R) = conj n P := by rw [hle]
  rwa [← conj_mul, mul_inv_cancel, conj_one, hnP] at h1

/-- **Peterfalvi I, Appendix II (6)** (import `Submission.Work.ThreePoints.Omega`, `Submission.Work.DoubleTransitivity.Action`, `Submission.Work.DoubleTransitivity.App2.app2_1/app2_2/app2_4/app2_5`): let `G` be a finite group acting 2-transitively on `Ω = G ⧸ H` (`IsTwoTransitiveOn H = MulAction.IsMultiplyPretransitive G (G ⧸ H) 2`), let `p` be a prime and `Q ≤ H` a `p`-subgroup which is *maximal among the `p`-subgroups of `H` with at least three fixed points*.  Then (i) `Q` is maximal among the `p`-subgroups of `G` with at least three fixed points, and (ii) the normaliser `N_G(Q)` acts 2-transitively on the set of fixed points of `Q`.

This is the source's App. II (6) verbatim (`REFS/peterfalvi_I_app1_4.md` p. 205: "Let `P` be a maximal element of the set of `p`-subgroups of `H` fixing at least 3 points. Then `P` is maximal in the set of `p`-subgroups of `X` fixing at least 3 points, and `N_X(P)` is 2-transitive on `E_P`").  Source proof (p. 205): let `a, b ∈ E_P` be distinct; split on whether `P` is a `p`-Sylow of the two-point stabiliser `X_a ⊓ X_b` — in that case apply App. II (5) (`Work.DoubleTransitivity.App2.app2_5`, already proved) to `P`, otherwise apply App. II (3) (`app2_3`) to `N_X(P)` to get a Sylow `p`-subgroup `R` of `X_a ⊓ X_b` with `P ≤ R` and `P = R ⊓ N_X(P)`, then (5) again.  Part (i) follows from the maximality of `Q` in `H` together with the fact that any `R ≥ Q` fixing three points satisfies `R ≤ Stab ω` for each of those points. -/
theorem app2_6_uniform {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (h2 : Submission.Blueprint.IsTwoTransitiveOn H) {p : ℕ} (hp : p.Prime) {Q : Subgroup G}
    (hQH : Q ≤ H) (hQp : IsPGroup p Q) (hQ3 : 3 ≤ (Submission.Blueprint.fixedPts H Q).ncard)
    (hQmax : ∀ R : Subgroup G, Q ≤ R → R ≤ H → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts H R).ncard → R = Q) :
    (∀ R : Subgroup G, Q ≤ R → IsPGroup p R → 3 ≤ (Submission.Blueprint.fixedPts H R).ncard →
        R = Q) ∧
      Work.DoubleTransitivity.IsTwoTransitiveOnSub (Subgroup.normalizer (Q : Set G))
        (Submission.Blueprint.fixedPts H Q) := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hstab : MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) = H := by
    rw [Work.ThreePoints.stabilizer_mk H 1, Work.ThreePoints.conj_one]
  have hpa : Q ≤ MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) := by
    rw [hstab]; exact hQH
  have hbig : 3 ≤ (Work.DoubleTransitivity.fixedBySub (E := G ⧸ H) Q).ncard := hQ3
  have hmax' : ∀ R : Subgroup G, Q ≤ R →
      R ≤ MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) → IsPGroup p R →
      3 ≤ (Work.DoubleTransitivity.fixedBySub (E := G ⧸ H) R).ncard → R = Q := by
    intro R hQR hRa hRp hR3
    exact hQmax R hQR (by rw [← hstab]; exact hRa) hRp hR3
  obtain ⟨hpart1, hpart2⟩ := app2_6_abstract (X := G) (E := G ⧸ H) (p := p)
    (a := (QuotientGroup.mk (1 : G) : G ⧸ H)) (P := Q) hp h2 hQp hpa hbig hmax'
  exact ⟨hpart1, hpart2⟩

end Work.ThreePoints
