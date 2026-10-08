import Submission.Work.ZJB2.Defs
import Submission.Work.ZJB.ZJBPropPrime

/-!
# gorenstein_walter, ZJB2 — the assemblies (no `sorry`)

Copied from the lead's design pass 17 (`Submission/Work/_design_gw/Core17B_Assembly.lean`,
namespace `GW2.C17B`), where all of it is proved.

* `cpPaper_of_goodFor` — subsets ⟸ subgroups (proved here);
* `thm51_of_leaves` — Theorem 5.1 under hypothesis (a): step (I) (design 11) + (II) + (III) +
  the (IV) method;
* `thm52_of_leaves` — Theorem 5.2 for `K = Z(J(·))`, hypotheses (a) at every subquotient,
  (b) at every proper subgroup and at `G/O_p(G)`;
* `theoremB_of_leaves` — the induction on `|X|` over the D-class (p. 1125);
* `zjbProp'_of_leaves`, `zjbProp'_of_leaves_pstable` — the deliverable `ZJBProp'`.
-/

namespace Work.ZJB

open Work.GW2
open Subgroup

/-- Subsets ⟸ subgroups: `(C_p)` for `S` follows from `GoodFor S W` for all subgroups `W ≤ S`
(the remark after `(C_p*)` on p. 1116: `C(V) = C(⟨V⟩)`). -/
theorem cpPaper_of_goodFor {G : Type} [Group G] (S : Subgroup G)
    (h : ∀ W : Subgroup G, W ≤ S → GoodFor S W) : ControlsStrongFusionPaper S (ZJ S) := by
  intro W _ hWS g hg
  set U : Subgroup G := Subgroup.closure W with hU
  have hUS : U ≤ S := (Subgroup.closure_le _).mpr hWS
  have hUmap : U.map (MulAut.conj g⁻¹).toMonoidHom ≤ S := by
    rw [hU, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨w, hw, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hg w hw
  have hUg : ∀ u ∈ U, g⁻¹ * u * g ∈ S := by
    intro u hu
    have := hUmap (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
  obtain ⟨c, n, hc, hn, hgn⟩ := h U hUS g hUg
  exact ⟨c, n, (Subgroup.centralizer_le Subgroup.subset_closure) hc, hn, hgn⟩

/-- **Theorem 5.1** (hypothesis (a)) from step (I) (design 11), (II), (III) and the (IV)
method. -/
theorem thm51_of_leaves {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (s1 : Step1Prop p G) (l51 : CpStarInOfCpInProp p G) (s2 : Step2Prop p G)
    (s3 : Step3Prop p G) (iv : IVMethodProp G) (ex : CondExists51Prop p G) (hA : HypA p G) :
    SatisfiesCpPaper p G := by
  intro S
  have hZ := s2 S (s1 hA S)
  have hstar := l51 _ (hA S (ZS (S : Subgroup G)) le_rfl inf_le_right)
  apply cpPaper_of_goodFor
  intro W hW
  exact iv S (fun V => IsSylowIn p (centralizer (V : Set G) ⊓ S) (centralizer (V : Set G)))
    (fun V hV hc => s3 S hZ hstar V hV hc) W hW (ex S W hW)

/-- **(5.4)+(5.5)**: `G = C(P)·N(Z(J(S)))` when hypothesis (a) holds. -/
theorem eq_centralizer_mul_normalizer {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (g2 : SylowInInfNormalProp p G) (g3 : IsSylowInOfLeProp p G) (frat : FrattiniInProp p G)
    (nrf : NormRFactorProp p G) (mrc : MRCentralizesProp p G) (hA : SubquotA p G)
    (S : Sylow p G) (g : G) :
    ∃ c ∈ centralizer (pCore p G : Set G),
      ∃ n ∈ normalizer (ZJ (S : Subgroup G) : Set G), g = c * n := by
  set P := pCore p G with hPdef
  have hPS : P ≤ S := pCore_le_sylow S
  set L : Subgroup G := P ⊔ centralizer (P : Set G) with hL
  have hLN : (⊤ : Subgroup G) ≤ normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
  have hR : IsSylowIn p (Rsub p G S) L := by
    have h := g2 S ⊤ L (g3 S ⊤ le_top) le_top hLN
    rwa [inf_comm] at h
  obtain ⟨l, hl, n, hn, rfl⟩ := frat ⊤ L (Rsub p G S) le_top hLN hR g (Subgroup.mem_top g)
  rw [hL, sup_comm, Subgroup.mem_sup_of_normal_left] at hl
  obtain ⟨b, hb, a, ha, rfl⟩ := hl
  have haR : a ∈ Rsub p G S := ⟨Subgroup.mem_sup_left ha, hPS ha⟩
  have han : a * n ∈ normalizer (Rsub p G S : Set G) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer haR) (Subgroup.mem_inf.mp hn).2
  obtain ⟨m, hm, k, hk, hmk⟩ := nrf hA S (a * n) han
  refine ⟨b * m, Subgroup.mul_mem _ hb (mrc S hm), k, hk, ?_⟩
  rw [mul_assoc, hmk, mul_assoc]

/-- **Theorem 5.2** for `K = Z(J(·))` (pp. 1121–1122): hypothesis (a) at every subquotient,
(b) at every proper subgroup (as `CpIn`) and at `G/O_p(G)`. -/
theorem thm52_of_leaves {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (l51 : CpStarInOfCpInProp p G) (g2 : SylowInInfNormalProp p G) (g3 : IsSylowInOfLeProp p G)
    (iv : IVMethodProp G) (frat : FrattiniInProp p G) (nrf : NormRFactorProp p G)
    (mrc : MRCentralizesProp p G) (lt52 : Case52ProperProp p G) (modp : ModPStepProp p G)
    (ppc : PPrimeCentralizesProp p G) (fac : FactorPPrimeProp p G)
    (nrm : CbarNormalizesProp p G) (ex : CondExists52Prop p G)
    (hA : SubquotA p G) (hBsub : ∀ M : Subgroup G, M ≠ ⊤ → CpIn p M)
    (hBq : SatisfiesCpPaper p (G ⧸ pCore p G)) : SatisfiesCpPaper p G := by
  intro S
  set P := pCore p G with hPdef
  have hGCN := eq_centralizer_mul_normalizer g2 g3 frat nrf mrc hA S
  by_cases hC : centralizer (P : Set G) ⊔ (S : Subgroup G) = ⊤
  · -- the case `G = C(P) S`
    have hGCS : ∀ g : G, ∃ c ∈ centralizer (P : Set G), ∃ s ∈ (S : Subgroup G), g = c * s := by
      intro g
      have hg : g ∈ centralizer (P : Set G) ⊔ (S : Subgroup G) := hC ▸ Subgroup.mem_top g
      obtain ⟨c, hc, s, hs, hcs⟩ := Subgroup.mem_sup_of_normal_left.mp hg
      exact ⟨c, hc, s, hs, hcs.symm⟩
    apply cpPaper_of_goodFor
    intro W hW
    refine iv S (fun V => V ≤ P ∨ IsSylowIn p (Cbar P V ⊓ S) (Cbar P V)) ?_ W hW (ex S W hW)
    intro V hV hc g hg
    by_cases hVP : V ≤ P
    · obtain ⟨c, hc', s, hs, rfl⟩ := hGCS g
      exact ⟨c, s, Subgroup.centralizer_le hVP hc', le_normalizer_ZJ _ hs, rfl⟩
    · have hSyl := hc.resolve_left hVP
      obtain ⟨y, hy, n, hn, rfl⟩ := modp hBsub hBq S V hV hVP g hg
      obtain ⟨l, hl, q, hq, rfl⟩ :=
        fac (Cbar P V) (centralizer ((V ⊔ P : Subgroup G) : Set G) ⊓ Cbar P V) (Cbar P V ⊓ S)
          inf_le_right (nrm V) (fun y hy hco => ⟨ppc S hGCS V hV y hy hco, hy⟩) hSyl y hy
      refine ⟨l, q * n, ?_, ?_, by rw [mul_assoc]⟩
      · exact Subgroup.centralizer_le (le_sup_left : V ≤ V ⊔ P) (Subgroup.mem_inf.mp hl).1
      · exact Subgroup.mul_mem _ (le_normalizer_ZJ _ (Subgroup.mem_inf.mp hq).2) hn
  · exact lt52 S hGCN (l51 _ (hBsub _ hC))

/-- **Theorem B** (p. 1125) over the D-class, by strong induction on `|X|`. -/
theorem theoremB_of_leaves (L : Leaves) (hZA : ZJAProp) (hH : DihOrCycHeredProp) :
    ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], p ≠ 2 → DihOrCycSylow X →
      SatisfiesCpPaper p X := by
  intro X _ _ p _ hp hX
  suffices h : ∀ n : ℕ, ∀ (X : Type) [Group X] [Finite X], Nat.card X = n → DihOrCycSylow X →
      SatisfiesCpPaper p X from h _ X rfl hX
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ hn hX
  have hsub : ∀ M : Subgroup X, M ≠ ⊤ → CpIn p M := fun M hM =>
    L.br X p M (ih _ (hn ▸ Subgroup.card_lt_card_of_ne_top hM) ↥M rfl ((hH X hX).1 M))
  intro S
  by_cases hS : (S : Subgroup X) = ⊥
  · exact L.bot X p S hS
  by_cases hP : pCore p X = ⊥
  · exact thm51_of_leaves (L.step1 X p) (L.l51 X p) (L.step2 X p) (L.step3 X p) (L.ivAlg X)
      (L.ex51 X p) (L.hypA X p hP hsub ⟨S, hS⟩) S
  · have hlt : Nat.card (X ⧸ pCore p X) < n := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore p X)
      have h2 : 1 < Nat.card (pCore p X) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hP
      have h3 : 0 < Nat.card (X ⧸ pCore p X) := Nat.card_pos
      rw [← hn, h1]
      exact lt_mul_of_one_lt_right h3 h2
    have hq : SatisfiesCpPaper p (X ⧸ pCore p X) :=
      ih _ hlt (X ⧸ pCore p X) rfl ((hH X hX).2 (pCore p X))
    have hAq : SubquotA p X := fun Y Lq _ hc Q =>
      zj_normal_of_subquotient hZA hH hX p hp Y Lq hc Q
    exact thm52_of_leaves (L.l51 X p) (L.g2 X p) (L.g3 X p) (L.ivAlg X) (L.frat X p) (L.nrf X p)
      (L.mrc X p) (L.lt52 X p) (L.modp X p) (L.ppc X p) (L.fac X p) (L.nrm X p) (L.ex52 X p)
      hAq hsub hq S

/-- **The deliverable** `ZJBProp'` from the leaves, `ZJAProp` and `DihOrCycHeredProp`. -/
theorem zjbProp'_of_leaves (L : Leaves) (hZA : ZJAProp) (hH : DihOrCycHeredProp) :
    ZJBProp' :=
  zjbProp'_of_satisfiesCpPaper fun X _ _ p _ hp hD => theoremB_of_leaves L hZA hH X p hp hD

/-- The same with `ZJAProp` supplied by GLUE (`Work.GW2.zjA`) from `PStableProp`. -/
theorem zjbProp'_of_leaves_pstable (L : Leaves) (hPS : PStableProp)
    (hH : DihOrCycHeredProp) : ZJBProp' :=
  zjbProp'_of_leaves L (zjA hPS) hH

end Work.ZJB
