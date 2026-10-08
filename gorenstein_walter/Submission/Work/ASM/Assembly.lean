import Submission.Work.ASM.Basic
import Submission.Work.ASM.CyclicSylow
import Submission.Work.ASM.oddCore_odd
import Submission.Work.ASM.dihedral_sylow_cyclic_index_two
import Submission.Work.ASM.PGL_exists_normal_subgroup
import Submission.Work.ASM.PSL_even_card

/-!
# ASM: the top-level assembly of the Gorenstein–Walter proof

This is the area `ASM` of the blueprint (`NOTES_LEAD_gw_blueprint2.md`, §2): the assembly that
turns the other areas' `Prop`s into the challenge statement.

* `gw_of_DGroupTheorem`        : `DGroupTheoremProp` ⇒ the challenge statement;
* `dGroupTheorem_of_steps`     : `NonSimpleStepProp` + `SimpleStepProp` ⇒ `DGroupTheoremProp`
                                (strong induction on `|G|`);
* `simpleStep_of_bender`       : `Thm210Prop` + `Case1FalseProp` + `Case2FalseProp` ⇒
                                `SimpleStepProp` (Bender's contradiction);
* `gorenstein_walter_of_areas` : the assembled challenge statement.

Everything is stated in the vocabulary `Work.GW2` of `Submission.Work.ASM.Defs`, which is a
verbatim copy of the `Prop`s of `_design_gw/Contracts2.lean`.
-/

open scoped MatrixGroups Pointwise
open Subgroup

namespace Work.GW2

open Work.ASM

/-! ## `O(G) = ⊥` for a simple group of even order -/

/-- In a simple group of even order the largest normal odd-order subgroup is trivial.  (For
`O(G) ⊴ G` is `⊥` or `⊤` by simplicity, and `⊤` is impossible because `O(G)` has odd order.) -/
theorem oddCore_eq_bot_of_even {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (heven : Even (Nat.card G)) : oddCore G = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (oddCore G) with h | h
  · exact h
  · exfalso
    have hc : Nat.card (oddCore G) = Nat.card G := by rw [h]; exact Subgroup.card_top
    exact (Nat.not_even_iff_odd.mpr (oddCore_odd G)) (hc ▸ heven)

/-! ## Elementary transports -/

/-- `Q ≃* ↥L` for a subgroup `L` of `Q` that is everything. -/
noncomputable def topSubgroupEquiv {Q : Type*} [Group Q] (L : Subgroup Q) (h : L = ⊤) :
    Q ≃* ↥L :=
  (Subgroup.topEquiv (G := Q)).symm.trans (MulEquiv.subgroupCongr h).symm

/-- `A₇` has even order. -/
theorem even_card_of_mulEquiv_a7 {G : Type*} [Group G]
    (h : Nonempty (G ≃* alternatingGroup (Fin 7))) : Even (Nat.card G) := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card]
  norm_num

/-- `PSL(2, q)` has even order for odd `q ≥ 5`. -/
theorem even_card_of_mulEquiv_PSL {G : Type*} [Group G] (p k : ℕ) [Fact p.Prime] (hp : Odd p)
    (hq : 5 ≤ p ^ k)
    (h : Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) :
    Even (Nat.card G) := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact PSL_even_card p k hp hq

/-- The challenge conclusion forces even order. -/
theorem even_card_of_gwConclusion {G : Type*} [Group G] (h : GWConclusion G) :
    Even (Nat.card G) := by
  rcases h with hA7 | ⟨p, k, _hpp, hpodd, hq, hPSL⟩
  · exact even_card_of_mulEquiv_a7 hA7
  · exact even_card_of_mulEquiv_PSL p k hpodd hq hPSL

/-! ## `PGL(2, q)` is not simple -/

/-- A finite simple group is not isomorphic to `PGL(2, q)` for odd `q ≥ 5`. -/
theorem false_of_mulEquiv_PGL {G : Type} [Group G] [IsSimpleGroup G] (p k : ℕ) [Fact p.Prime]
    (hp : Odd p) (hq : 5 ≤ p ^ k)
    (h : Nonempty (G ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k))) : False := by
  obtain ⟨N, hNn, hNbot, hNtop⟩ := PGL_exists_normal_subgroup p k hp hq
  obtain ⟨e⟩ := h
  have hMn : (N.map e.symm.toMonoidHom).Normal :=
    Subgroup.Normal.map hNn _ e.symm.toEquiv.surjective
  have hMbot : (N.map e.symm.toMonoidHom) ≠ ⊥ := fun hbot =>
    hNbot ((Subgroup.map_eq_bot_iff_of_injective N e.symm.toEquiv.injective).mp hbot)
  have hMtop : (N.map e.symm.toMonoidHom) ≠ ⊤ := by
    intro htop
    apply hNtop
    have h1 : (N.map e.symm.toMonoidHom).map e.toMonoidHom = N := by
      rw [Subgroup.map_map]
      have h2 : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
        ext x
        simp
      rw [h2, Subgroup.map_id]
    rw [htop, Subgroup.map_top_of_surjective _ e.toEquiv.surjective] at h1
    exact h1.symm
  rcases hMn.eq_bot_or_eq_top with h' | h'
  · exact hMbot h'
  · exact hMtop h'

/-! ## The `DShape` alternatives for a simple non-abelian group -/

/-- For a simple non-abelian `G` of even order with `O(G) = ⊥`, `DShape (G ⧸ O(G))` is the
challenge conclusion. -/
theorem gwConclusion_of_dShape {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (heven : Even (Nat.card G)) (hodd : oddCore G = ⊥)
    (h : DShape (G ⧸ oddCore G)) : GWConclusion G := by
  rcases h with hpg | ⟨V, hVn, hV4, _hVc⟩ | hA7 | ⟨L, hLn, hLodd, p, k, hpp, hpodd, hq, hXY⟩
  · exact (false_of_isPGroup_oddCore_quotient hnonab hodd hpg).elim
  · exact (false_of_fourGroup_oddCore_quotient hnonab hodd V hVn hV4).elim
  · obtain ⟨f⟩ := hA7
    exact Or.inl ⟨(quotientOddCoreEquiv hodd).symm.trans f⟩
  · have hLtop : L = ⊤ := by
      rcases normal_eq_bot_or_top_of_quotient (oddCore G) L hLn with hbot | htop
      · exfalso
        have hcard : Nat.card (G ⧸ oddCore G) = Nat.card G :=
          Nat.card_congr (quotientOddCoreEquiv hodd).toEquiv
        have hidx : L.index = Nat.card G := by rw [hbot, Subgroup.index_bot, hcard]
        rw [hidx] at hLodd
        exact (Nat.not_even_iff_odd.mpr hLodd) heven
      · exact htop
    rcases hXY with hPSL | hPGL
    · obtain ⟨f⟩ := hPSL
      exact Or.inr ⟨p, k, hpp, hpodd, hq,
        ⟨(quotientOddCoreEquiv hodd).symm.trans ((topSubgroupEquiv L hLtop).trans f)⟩⟩
    · obtain ⟨f⟩ := hPGL
      exact (false_of_mulEquiv_PGL p k hpodd hq
        ⟨(quotientOddCoreEquiv hodd).symm.trans ((topSubgroupEquiv L hLtop).trans f)⟩).elim

/-- The challenge conclusion makes `G` a D-group (for simple non-abelian `G` of even order). -/
theorem isDGroup_of_gwConclusion {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (heven : Even (Nat.card G)) (h : GWConclusion G) : IsDGroup G := by
  have hodd : oddCore G = ⊥ := oddCore_eq_bot_of_even heven
  rcases h with hA7 | ⟨p, k, hpp, hpodd, hq, hPSL⟩
  · obtain ⟨f⟩ := hA7
    exact Or.inr (Or.inr (Or.inl ⟨(quotientOddCoreEquiv hodd).trans f⟩))
  · obtain ⟨f⟩ := hPSL
    refine Or.inr (Or.inr (Or.inr ⟨⊤, inferInstance, ?_, p, k, hpp, hpodd, hq,
      Or.inl (Nonempty.intro ?_)⟩))
    · rw [Subgroup.index_top]
      exact ⟨0, rfl⟩
    · exact (Subgroup.topEquiv (G := G ⧸ oddCore G)).trans
        ((quotientOddCoreEquiv hodd).trans f)

/-! ## The three pieces of the assembly -/

/-- ASM: the challenge statement from `DGroupTheoremProp`. -/
theorem gw_of_DGroupTheorem (h : DGroupTheoremProp) (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G)
    (hdih : ∃ n : ℕ, Nonempty ((P : Subgroup G) ≃* DihedralGroup n)) : GWConclusion G := by
  obtain ⟨n, hn⟩ := hdih
  have hdih' : DihOrCycSylow G := dihOrCycSylow_of_dihedral P hn
  have hD : IsDGroup G := h G hdih'
  have heven : Even (Nat.card G) := even_card_of_dihedral_sylow P hn
  exact gwConclusion_of_dShape hnonab heven (oddCore_eq_bot_of_even heven) hD

/-- ASM: strong induction on `|G|`. -/
theorem dGroupTheorem_of_steps (hN : NonSimpleStepProp) (hS : SimpleStepProp) :
    DGroupTheoremProp := by
  have hmain : ∀ n, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n →
      DihOrCycSylow G → IsDGroup G := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G _ _ hcard hdih
      have hsmall : SmallerDGroups G := fun X _ _ hlt hX =>
        ih (Nat.card X) (by omega) X rfl hX
      by_cases hs : IsSimpleGroup G ∧ ∃ a b : G, a * b ≠ b * a
      · obtain ⟨hsimple, hnonab⟩ := hs
        have : IsSimpleGroup G := hsimple
        have hGW : GWConclusion G := hS G hsimple hnonab hdih hsmall
        exact isDGroup_of_gwConclusion (even_card_of_gwConclusion hGW) hGW
      · exact hN G hdih hsmall hs
  intro G _ _ hdih
  exact hmain (Nat.card G) G rfl hdih

/-- ASM: Bender's contradiction.  A minimal counterexample `G` has a dihedral Sylow
2-subgroup (cyclic Sylow 2-subgroups are excluded by `false_of_cyclic_sylow_two`); from it we
build the Bender setup `S, S₀, t, Ĥ` and apply Bender's Theorem 2.10 and the two eliminations. -/
theorem simpleStep_of_bender (hFT : FeitThompsonProp) (h210 : Thm210Prop)
    (h1 : Case1FalseProp) (h2 : Case2FalseProp) : SimpleStepProp := by
  intro G _ _ hsimple hnonab hdih ih
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hconcl
  have hctx : BenderCtx G :=
    { simple := hsimple
      nonab := hnonab
      sylow := hdih
      ih := ih
      notA7 := ⟨fun h => hconcl (Or.inl ⟨h⟩)⟩
      notPSL := fun p k hpp hpodd hq =>
        ⟨fun h => hconcl (Or.inr ⟨p, k, hpp, hpodd, hq, ⟨h⟩⟩)⟩ }
  obtain ⟨S⟩ : Nonempty (Sylow 2 G) := Sylow.nonempty
  rcases hdih S with hcyc | ⟨n, hn⟩
  · exact (false_of_cyclic_sylow_two hnonab hFT S hcyc).elim
  · obtain ⟨e⟩ := hn
    by_cases hcycS : IsCyclic ↥(S : Subgroup G)
    · exact (false_of_cyclic_sylow_two hnonab hFT S hcycS).elim
    · obtain ⟨S0, t, hS0le, hS0cyc, hS0idx, htmem, htord⟩ :=
        dihedral_sylow_cyclic_index_two S hcycS e
      have ht_ne_one : t ≠ 1 := by
        intro h1'
        rw [h1', orderOf_one] at htord
        exact absurd htord (by norm_num)
      have hCt_ne_top : centralizer ({t} : Set G) ≠ ⊤ := by
        intro htop
        have hmem : t ∈ Subgroup.center G := by
          refine Subgroup.mem_center_iff.mpr fun g => ?_
          have hg : g ∈ centralizer ({t} : Set G) := by rw [htop]; trivial
          exact ((Subgroup.mem_centralizer_iff.mp hg) t (by simp)).symm
        have hne : Subgroup.center G ≠ ⊥ := fun hbot =>
          ht_ne_one (by
            have : t ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact hmem
            rwa [Subgroup.mem_bot] at this)
        have htop' : Subgroup.center G = ⊤ := by
          rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h' | h'
          · exact absurd h' hne
          · exact h'
        obtain ⟨a, b, hab⟩ := hnonab
        refine hab ?_
        have ha : a ∈ Subgroup.center G := by rw [htop']; trivial
        exact ((Subgroup.mem_center_iff.mp ha) b).symm
      obtain ⟨Hhat, hHhatcoatom, hHhatge⟩ :=
        exists_coatom_ge_of_ne_top (centralizer ({t} : Set G)) hCt_ne_top
      let B : BenderSetup G :=
        { S := S
          S0 := S0
          t := t
          Hhat := Hhat
          S0_le := hS0le
          S0_cyclic := hS0cyc
          S0_index := hS0idx
          t_mem := htmem
          t_order := htord
          Hhat_coatom := hHhatcoatom
          H_le_Hhat := hHhatge }
      rcases h210 G hFT hctx B with hc1 | hc2
      · exact (h1 G hFT hctx B hc1).elim
      · exact (h2 G hFT hctx B hc2).elim

/-! ## The assembled challenge statement -/

/-- The assembled challenge statement from the areas' `Prop`s. -/
theorem gorenstein_walter_of_areas (hN : NonSimpleStepProp) (hS : SimpleStepProp)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G) (hdih : ∃ n : ℕ, Nonempty ((P : Subgroup G) ≃* DihedralGroup n)) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    ∃ p k : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
      Nonempty (G ≃* PSL(2, GaloisField p k)) :=
  gw_of_DGroupTheorem (dGroupTheorem_of_steps hN hS) G hnonab P hdih

/-- The same, in the shape of `GW2.gorenstein_walter_of_areas` of the contracts: the toolkit
supplies Feit–Thompson, and the CORE areas supply Theorem 2.10 and the two eliminations. -/
theorem gorenstein_walter_of_toolkit (T : LocalToolkit) (hN : NonSimpleStepProp)
    (h210 : Thm210Prop) (h1 : Case1FalseProp) (h2 : Case2FalseProp) (G : Type) [Group G]
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (P : Sylow 2 G)
    (hdih : ∃ n : ℕ, Nonempty ((P : Subgroup G) ≃* DihedralGroup n)) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    ∃ p k : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
      Nonempty (G ≃* PSL(2, GaloisField p k)) :=
  gorenstein_walter_of_areas hN (simpleStep_of_bender T.ft h210 h1 h2) G hnonab P hdih

end Work.GW2
