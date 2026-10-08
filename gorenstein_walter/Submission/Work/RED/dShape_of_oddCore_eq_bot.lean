import Mathlib
import Submission.Work.RED.Basic
import Submission.Work.ASM.PGL_exists_normal_subgroup

/-!
# RED: `DShape G` when `O(G) = 1` and `G` is not a nonabelian simple group

This is the case-B2 analysis of blueprint §4 (see `NOTES_RED.md`): the non-simple step of the
Gorenstein–Walter / Bender theorem reduced to the case `O(G) = O_{2'}(G) = 1`.

Given a dihedral Sylow `2`-subgroup `P ≃* DihedralGroup n` (`n ≥ 2`), the induction hypothesis
`SmallerDGroups G`, and the fact that `G` is not a nonabelian simple group, we show that `G` has
one of the four shapes recorded in `Work.RED.GW2.DShape`:

* `G` is a `2`-group (this covers the "central involution" case);
* `G` contains a self-centralizing normal Klein four-group;
* `G ≅ A₇`;
* `G` has a normal subgroup of odd index isomorphic to `PSL(2,q)` or `PGL(2,q)`.

The mathematics follows the case analysis of `NOTES_RED.md` §4, consuming the `RedFacts` bundle
and the Props `CentralizerSplitProp`, `AutL2Prop`, `AutA7Prop` supplied by the neighbouring areas.
-/

open scoped MatrixGroups

namespace Work.RED

open Subgroup

/-- Two involutions whose product is an involution commute. -/
private theorem mul_comm_of_sq_eq_one_aux {G : Type*} [Group G] {x y : G}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : (x * y) ^ 2 = 1) : x * y = y * x := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hy)
  have h1 : x * y = (x * y)⁻¹ := by
    have h2 : (x * y) * (x * y) = 1 := by simpa [pow_two] using hxy
    exact (inv_eq_of_mul_eq_one_left h2).symm
  rw [h1, mul_inv_rev, hx', hy']

theorem dShape_of_oddCore_eq_bot (F : Work.RED.GW2.RedFacts)
    (hfus : Work.RED.GW2.InvolutionFusionProp) (hsplit : Work.RED.GW2.CentralizerSplitProp)
    (hautL2 : Work.RED.GW2.AutL2Prop) (hautA7 : Work.RED.GW2.AutA7Prop)
    {G : Type} [Group G] [Finite G] (hdih : Work.RED.GW2.DihOrCycSylow G)
    (hsmall : Work.RED.GW2.SmallerDGroups G) (hO : Work.RED.GW2.oddCore G = ⊥)
    (hnotsimple : ¬ (IsSimpleGroup G ∧ ∃ a b : G, a * b ≠ b * a))
    {n : ℕ} [NeZero n] {P : Sylow 2 G} (e : ↥(P : Subgroup G) ≃* DihedralGroup n) (hn : 2 ≤ n) :
    Work.RED.GW2.DShape G := by
  classical
  by_cases hnt : Nontrivial G
  swap
  · -- `G` trivial
    haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hnt
    exact Or.inl (IsPGroup.of_subsingleton 2 G)
  haveI := hnt
  -- `P = ⊤` gives `IsPGroup 2 G`
  have key_top (htop : (P : Subgroup G) = ⊤) : Work.RED.GW2.DShape G := by
    have hsurj : Function.Surjective ((P : Subgroup G).subtype : ↥(P : Subgroup G) → G) := by
      intro g
      exact ⟨⟨g, htop ▸ Subgroup.mem_top g⟩, rfl⟩
    let ePG : ↥(P : Subgroup G) ≃* G :=
      MulEquiv.ofBijective ((P : Subgroup G).subtype)
        ⟨(P : Subgroup G).subtype_injective, hsurj⟩
    exact Or.inl (P.isPGroup'.of_equiv ePG)
  by_cases hsimple : IsSimpleGroup G
  · -- `G` simple: `hnotsimple` forces `G` commutative, so `P ⊴ G` is `⊥` or `⊤`.
    have hcomm : ∀ a b : G, a * b = b * a := by
      by_contra hcon
      push_neg at hcon
      exact hnotsimple ⟨hsimple, hcon⟩
    haveI : IsMulCommutative G := IsMulCommutative.of_comm hcomm
    have hPnorm : (P : Subgroup G).Normal := Subgroup.normal_of_isMulCommutative _
    rcases Subgroup.Normal.eq_bot_or_eq_top (P : Subgroup G) with hbot | htop
    · -- `P = ⊥` contradicts `P ≃* DihedralGroup n` with `n ≥ 2`
      exfalso
      have h1 : Nat.card ↥(P : Subgroup G) = 1 := by rw [hbot]; exact Subgroup.card_bot
      have h2 : Nat.card ↥(P : Subgroup G) = 2 * n := by
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      omega
    · exact key_top htop
  · -- `G` not simple
    obtain ⟨N, hN⟩ := F.min.exists_minimal G
    have hNne_top : N ≠ ⊤ := by
      intro htop
      apply hsimple
      refine IsSimpleGroup.mk (fun M hM => ?_)
      rcases eq_or_ne M ⊥ with h | h
      · exact Or.inl h
      · exact Or.inr (top_le_iff.mp (htop ▸ hN.2.2 M hM h (by rw [htop]; exact le_top)))
    by_cases hNab : IsMulCommutative N
    · -- ############################################################
      -- ## Case A: `N` abelian
      -- ############################################################
      obtain ⟨p, hp, hexp⟩ := F.min.abelian_elementary G N hN hNab
      by_cases hp2 : p = 2
      · subst hp2
        -- `N` is elementary abelian of exponent `2`
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hNpg : IsPGroup 2 ↥N := by
          rw [isPGroup_iff_orderOf_dvd_pow]
          intro x
          refine ⟨1, ?_⟩
          rw [pow_one, orderOf_dvd_iff_pow_eq_one]
          apply Subtype.ext
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          exact hexp (x : G) x.2
        haveI hNnormal : N.Normal := hN.normal
        have hNP : N ≤ (P : Subgroup G) := IsPGroup.le_sylow_of_normal hNpg P
        -- rank bound: `|N| ≤ 4`
        have hcardle : Nat.card ↥N ≤ 4 := by
          let f : ↥N →* DihedralGroup n := e.toMonoidHom.comp (Subgroup.inclusion hNP)
          have hfinj : Function.Injective f :=
            e.injective.comp (Subgroup.inclusion_injective hNP)
          let E : Subgroup (DihedralGroup n) := (⊤ : Subgroup ↥N).map f
          have hEcard : Nat.card E = Nat.card ↥N := by
            dsimp only [E]
            rw [Subgroup.card_map_of_injective hfinj]
            simp
          have hE2 : ∀ x ∈ E, x ^ 2 = 1 := by
            intro x hx
            dsimp only [E] at hx
            rw [Subgroup.mem_map] at hx
            obtain ⟨v, -, rfl⟩ := hx
            have hv2 : v ^ 2 = 1 := by
              apply Subtype.ext
              rw [Subgroup.coe_pow, Subgroup.coe_one]
              exact hexp (v : G) v.2
            rw [← map_pow, hv2, map_one]
          have h4 := F.dih.elementary_abelian_card_le_four n E hE2
          rw [hEcard] at h4
          exact h4
        have hcardge : 2 ≤ Nat.card ↥N := by
          have h1 : 1 < Nat.card ↥N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hN.ne_bot
          omega
        have hcases : Nat.card ↥N = 2 ∨ Nat.card ↥N = 4 := by
          obtain ⟨kk, hkk⟩ := (IsPGroup.iff_card).mp hNpg
          have hle : kk ≤ 2 := by
            have h : 2 ^ kk ≤ 4 := hkk ▸ hcardle
            have h' : 2 ^ kk ≤ 2 ^ 2 := by norm_num at h ⊢; exact h
            exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h'
          have hge : 1 ≤ kk := by
            by_contra hcon
            have h0 : kk = 0 := by omega
            have h1 : Nat.card ↥N = 1 := by rw [hkk, h0, pow_zero]
            omega
          rw [hkk]
          interval_cases kk <;> simp
        rcases hcases with hN2 | hN4
        · -- `|N| = 2`: the involution of `N` is central, `C(t) = ⊤`, so `P = ⊤`.
          have hcle : N ≤ Subgroup.center G := F.cent2 N hN.normal hN2
          haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN.ne_bot
          obtain ⟨x, hx1⟩ := exists_ne (1 : ↥N)
          have hxG1 : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
          have hxP : (x : G) ∈ (P : Subgroup G) := hNP x.2
          have hxcenter : (x : G) ∈ Subgroup.center G := hcle x.2
          have hx2 : orderOf (x : G) = 2 :=
            orderOf_eq_prime (hexp (x : G) x.2) hxG1
          have hxcomm : ∀ y ∈ (P : Subgroup G), y * (x : G) = (x : G) * y :=
            fun y _ => Subgroup.mem_center_iff.mp hxcenter y
          have hsplit' := hsplit G P n hn ⟨e⟩ (x : G) hxP hx2 hxcomm
          have hctop : Subgroup.centralizer ({(x : G)} : Set G) = ⊤ := by
            rw [eq_top_iff]
            intro y _
            rw [Subgroup.mem_centralizer_iff]
            intro z hz
            rw [Set.mem_singleton_iff] at hz
            subst hz
            exact (Subgroup.mem_center_iff.mp hxcenter y).symm
          have hOI : Work.RED.GW2.oddCoreIn (⊤ : Subgroup G) = ⊥ := by
            apply le_bot_iff.mp
            rw [← hO]
            exact F.odd.le_of_normal G ⊤ inferInstance
          rw [hctop, hOI] at hsplit'
          exact key_top (by simpa using hsplit')
        · -- `|N| = 4`: `N` is a normal four-group, self-centralizing.
          have hIs4 : Work.RED.GW2.IsFourGroup N := ⟨hN4, fun v hv => hexp v hv⟩
          exact Or.inr (Or.inl ⟨N, hN.normal, hIs4, F.fourNorm hN.normal hIs4 hO e hn⟩)
      · -- `p` odd: `N` is a normal odd-order subgroup, hence `N ≤ O(G) = ⊥`.
        exfalso
        have hpodd : Odd p := hp.odd_of_ne_two hp2
        haveI : Fact (Nat.Prime p) := ⟨hp⟩
        have hNpg : IsPGroup p ↥N := by
          rw [isPGroup_iff_orderOf_dvd_pow]
          intro x
          refine ⟨1, ?_⟩
          rw [pow_one, orderOf_dvd_iff_pow_eq_one]
          apply Subtype.ext
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          exact hexp (x : G) x.2
        have hOdd : Odd (Nat.card ↥N) := by
          obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hNpg
          rw [hm]
          exact hpodd.pow
        have hle := F.odd.le_oddCore G N hN.normal hOdd
        rw [hO] at hle
        exact hN.ne_bot (le_bot_iff.mp hle)
    · -- ############################################################
      -- ## Case B: `N` nonabelian
      -- ############################################################
      obtain ⟨K, hK⟩ := F.min.exists_minimalIn G N hN.ne_bot
      have hKnab : ¬ IsMulCommutative K := F.min.nonabelian_of_minimalNormalIn G N K hN hK hNab
      have hKnotSol : ¬ Group.IsSolvable ↥K := F.notSol hN hK hKnab
      have hOK : Work.RED.GW2.oddCore ↥K = ⊥ := F.oddCoreK hN hK hKnotSol
      have hdihK : Work.RED.GW2.DihOrCycSylow ↥K := F.dcs K hdih
      obtain ⟨V, hV4⟩ := F.v4 ↥K hdihK hOK hKnotSol
      -- the four-group `V ≤ K`, viewed in `G`
      let V' : Subgroup G := V.map K.subtype
      have hV'le : V' ≤ K := Subgroup.map_subtype_le V
      have hV'4 : Work.RED.GW2.IsFourGroup V' := by
        refine ⟨?_, ?_⟩
        · change Nat.card (V.map K.subtype) = 4
          rw [Subgroup.card_map_of_injective K.subtype_injective, hV4.1]
        · intro x hx
          rw [Subgroup.mem_map] at hx
          obtain ⟨v, hv, rfl⟩ := hx
          change (K.subtype v) ^ 2 = 1
          rw [← map_pow, hV4.2 v hv, map_one]
      -- `K = N`
      have hKN : K = N := F.eqOfContained N K hN hK ⟨V', hV'le, hV'4⟩ e hn
      rw [hKN] at hK hKnotSol hOK hV'le
      haveI : IsSimpleGroup ↥N := F.min.isSimpleGroup_of_minimalNormalIn_self G N hK
      have hNnotSol : ¬ Group.IsSolvable ↥N := hKnotSol
      have hON : Work.RED.GW2.oddCore ↥N = ⊥ := hOK
      -- the centre of the simple nonabelian `N` is trivial
      have hcenterN : Subgroup.center ↥N = ⊥ := by
        haveI : (Subgroup.center ↥N).Normal := inferInstance
        rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center ↥N) with h | h
        · exact h
        · exfalso
          apply hNab
          refine IsMulCommutative.of_comm (fun a b => ?_)
          have ha : a ∈ Subgroup.center ↥N := by rw [h]; trivial
          exact (Subgroup.mem_center_iff.mp ha b).symm
      -- `C_G(N) = ⊥`
      have hCodd : Odd (Nat.card (Subgroup.centralizer (N : Set G))) :=
        F.cent4 N hN.normal hcenterN e hn ⟨V', hV'le, hV'4⟩
      have hCbot : Subgroup.centralizer (N : Set G) = ⊥ := by
        haveI : N.Normal := hN.normal
        haveI : (Subgroup.centralizer (N : Set G)).Normal := inferInstance
        have hle : Subgroup.centralizer (N : Set G) ≤ Work.RED.GW2.oddCore G :=
          F.odd.le_oddCore G _ inferInstance hCodd
        rw [hO] at hle
        exact le_bot_iff.mp hle
      -- `|N| < |G|`
      have hcardN : Nat.card ↥N < Nat.card G := by
        rw [← Subgroup.index_mul_card (H := N)]
        exact lt_mul_of_one_lt_left Nat.card_pos (Subgroup.one_lt_index_of_ne_top hNne_top)
      have hdihN : Work.RED.GW2.DihOrCycSylow ↥N := F.dcs N hdih
      have hDShapeN : Work.RED.GW2.DShape ↥N := by
        have h1 : Work.RED.GW2.DShape (↥N ⧸ Work.RED.GW2.oddCore ↥N) :=
          hsmall ↥N hcardN hdihN
        have h2 : Work.RED.GW2.DShape (↥N ⧸ (⊥ : Subgroup ↥N)) :=
          Work.RED.GW2.DShape.of_mulEquiv h1 (QuotientGroup.quotientMulEquivOfEq hON)
        exact (Work.RED.GW2.DShape.quotientBot_iff ↥N).mp h2
      rcases hDShapeN with h2grp | ⟨V2, hV2n, hV24, hV2c⟩ | ⟨e7⟩ | ⟨L, hLn, hLi, p, k, hp, hodd, h5, hL⟩
      · -- clause 1: a `2`-group is solvable, contradicting the non-solvability of `N`
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hsol : Group.IsSolvable ↥N := by
          haveI : Group.IsNilpotent ↥N := h2grp.isNilpotent
          exact IsNilpotent.to_isSolvable
        exact absurd hsol hNnotSol
      · -- clause 2: a normal four-group in a simple nonabelian `N` is everything, so `N` is abelian
        haveI : V2.Normal := hV2n
        rcases Subgroup.Normal.eq_bot_or_eq_top V2 with h | h
        · exact absurd h ((Subgroup.nontrivial_iff_ne_bot V2).mp hV24.nontrivial)
        · exfalso
          apply hNab
          refine IsMulCommutative.of_comm (fun a b => ?_)
          have ha : a ^ 2 = 1 := hV24.2 a (by rw [h]; exact Subgroup.mem_top a)
          have hb : b ^ 2 = 1 := hV24.2 b (by rw [h]; exact Subgroup.mem_top b)
          have hab : (a * b) ^ 2 = 1 := hV24.2 (a * b) (by rw [h]; exact Subgroup.mem_top _)
          exact mul_comm_of_sq_eq_one_aux ha hb hab
      · -- clause 3: `N ≅ A₇` forces `N = ⊤`, contradicting `N ≠ ⊤`
        have htop : N = ⊤ := hautA7 G N hN.normal e7 hCbot hdih
        exact absurd htop hNne_top
      · -- clause 4
        haveI : Fact p.Prime := hp
        -- `L ⊴ N` is `⊥` or `⊤`; `⊥` is excluded because its index `|N|` is even
        have hLtop : L = ⊤ := by
          haveI : L.Normal := hLn
          rcases Subgroup.Normal.eq_bot_or_eq_top L with h | h
          · exfalso
            have hidx : L.index = Nat.card ↥N := by rw [h, Subgroup.index_bot]
            rw [hidx] at hLi
            have h4dvd : 4 ∣ Nat.card ↥N := by
              rw [← hV'4.1]
              exact Subgroup.card_dvd_of_le hV'le
            have heven : Even (Nat.card ↥N) :=
              even_iff_two_dvd.mpr (dvd_trans (by norm_num : 2 ∣ 4) h4dvd)
            exact (Nat.not_odd_iff_even.mpr heven) hLi
          · exact h
        rcases hL with ⟨hLPSL⟩ | ⟨hLPGL⟩
        · -- `N ≅ PSL(2,q)`: AutL2Prop supplies the normal subgroup of odd index
          rw [hLtop] at hLPSL
          obtain ⟨gPSL⟩ := hLPSL
          have hNPSL : Nonempty
              (↥N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
            ⟨(Subgroup.topEquiv (G := ↥N)).symm.trans gPSL⟩
          obtain ⟨M, hMn, -, hMi, hM⟩ := hautL2 G N p k hodd h5 hN.normal hNPSL hCbot hdih
          exact Or.inr (Or.inr (Or.inr ⟨M, hMn, hMi, p, k, hp, hodd, h5, hM⟩))
        · -- `N ≅ PGL(2,q)`: impossible, `PGL(2,q)` is not simple
          rw [hLtop] at hLPGL
          obtain ⟨gPGL⟩ := hLPGL
          have hPGL : ↥N ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k) :=
            (Subgroup.topEquiv (G := ↥N)).symm.trans gPGL
          obtain ⟨N', hN'n, hN'ne, hN'top⟩ := Work.ASM.PGL_exists_normal_subgroup p k hodd h5
          haveI : (N'.comap hPGL.toMonoidHom).Normal := hN'n.comap hPGL.toMonoidHom
          have hN''bot : N'.comap hPGL.toMonoidHom ≠ ⊥ := by
            intro hb
            apply hN'ne
            rw [← Subgroup.map_comap_eq_self_of_surjective (f := hPGL.toMonoidHom)
              hPGL.surjective N', hb, Subgroup.map_bot]
          have hN''top : N'.comap hPGL.toMonoidHom ≠ ⊤ := by
            intro ht
            apply hN'top
            rw [← Subgroup.map_comap_eq_self_of_surjective (f := hPGL.toMonoidHom)
              hPGL.surjective N', ht, Subgroup.map_top_of_surjective _ hPGL.surjective]
          rcases Subgroup.Normal.eq_bot_or_eq_top (N'.comap hPGL.toMonoidHom) with hh | hh
          · exact absurd hh hN''bot
          · exact absurd hh hN''top

end Work.RED
