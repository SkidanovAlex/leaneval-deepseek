import Mathlib
import Submission.Work.CORE2B.Defs
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.isQuasisimple_four_dvd
import Submission.Work.CORE2B.dihedral_center_of_large_subgroup
import Submission.Work.CORE2B.sylow_central_of_large_inter
import Submission.Work.CORE2B.L27_step1
import Submission.Work.CORE2B.L29_sylow_piece

/-!
# CORE2B — Bender 1981, Lemma 2.9, `D₁₆` case (iv), at the leaf's hypotheses

The leaf `Work.CORE2B.L29_case_iv_leaf`: given Bender's context `hctx`, a setup `B`, a four-group
`V ≤ B.S` contained in `N`, the hypothesis `V ⊓ E(N) = ⊥`, and a normal quasisimple subgroup
`E ◁ ↥N`, we derive a contradiction.

Route (worked out here; no solubility of `N` is used):

* `E ≠ ⊥` (its central quotient is simple), hence `4 ∣ |E|` by
  `Work.CORE2B.isQuasisimple_four_dvd`;
* `E ≤ E(↥N)` since `E` is normal and quasisimple in `↥N`, so the image
  `E.map N.subtype` lies in `layerIn N` and `V ⊓ E.map N.subtype = ⊥` by `h2`;
* a Sylow `2`-subgroup `Q` of `↥N` contains `V.subgroupOf N`; `Work.CORE2B.sylow_inf_dvd`
  gives `4 ∣ |Q ⊓ E|`, so the `2`-subgroup `T := Q.map N.subtype ≤ G` contains `V` and meets
  `E.map N.subtype` in at least `4` elements;
* `T` lies in a Sylow `2`-subgroup `S'` of `G`, and inside the cyclic-or-dihedral `S'` two
  subgroups of order `≥ 4` meet nontrivially (the unique involution of a cyclic index-two
  subgroup), contradiction.
-/

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- A quasisimple subgroup is nontrivial (its central quotient is a nontrivial group). -/
private theorem isQuasisimple_ne_bot {X : Type} [Group X] (E : Subgroup X)
    (h : Work.GW2.IsQuasisimple E) : E ≠ ⊥ := by
  rintro hbot
  have hsub : ∀ x : ↥E, (x : X) = 1 := fun x => Subgroup.mem_bot.mp (hbot ▸ x.2)
  haveI : Subsingleton ↥E := ⟨fun x y => Subtype.ext (by rw [hsub x, hsub y])⟩
  haveI : Nontrivial (↥E ⧸ Subgroup.center ↥E) := h.2.toNontrivial
  exact not_subsingleton (↥E ⧸ Subgroup.center ↥E) inferInstance

/-- **Two `2`-subgroups of order `≥ 4` of a cyclic-or-dihedral Sylow `2`-subgroup meet
nontrivially.**  In such a `2`-group both subgroups contain the unique involution of a cyclic
subgroup of index two: in the dihedral case `S ≅ DihedralGroup n` (`n = 2` forces `|S| = 4` and
`Q₁ = Q₂ = S`; for `n ≥ 4` use `Work.CORE2B.dih_helper` and
`Work.CORE2B.cyclic_index_two_center_mem`), in the cyclic case the unique involution of the
cyclic `2`-group. -/
private theorem inf_ne_bot_of_le_sylow {G : Type} [Group G] [Finite G]
    (hsy : ∀ P : Sylow 2 G, IsCyclic (P : Subgroup G) ∨
      ∃ n : ℕ, Nonempty ((P : Subgroup G) ≃* DihedralGroup n))
    (S : Sylow 2 G) (Q₁ Q₂ : Subgroup G) (h₁ : Q₁ ≤ (S : Subgroup G))
    (h₂ : Q₂ ≤ (S : Subgroup G)) (hc₁ : 4 ≤ Nat.card ↥Q₁) (hc₂ : 4 ≤ Nat.card ↥Q₂) :
    ∃ z : G, z ≠ 1 ∧ z ∈ Q₁ ∧ z ∈ Q₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ₁2 : IsPGroup 2 ↥Q₁ := (S.isPGroup').to_le h₁
  have hQ₂2 : IsPGroup 2 ↥Q₂ := (S.isPGroup').to_le h₂
  have h2dvd₁ : 2 ∣ Nat.card ↥Q₁ := by
    rcases hQ₁2.card_eq_or_dvd with h | h
    · omega
    · exact h
  have h2dvd₂ : 2 ∣ Nat.card ↥Q₂ := by
    rcases hQ₂2.card_eq_or_dvd with h | h
    · omega
    · exact h
  rcases hsy S with hcyc | ⟨n, ⟨e⟩⟩
  · -- ## `S` is cyclic: both `Qᵢ` contain the unique involution of `S`
    haveI : IsCyclic ↥(S : Subgroup G) := hcyc
    obtain ⟨u₁, hu₁⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd₁
    obtain ⟨u₂, hu₂⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd₂
    have hu₁' : orderOf (u₁ : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu₁
    have hu₂' : orderOf (u₂ : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu₂
    have hne₁ : (u₁ : G) ≠ 1 := by
      rintro h1
      rw [h1, orderOf_one] at hu₁'
      exact absurd hu₁' (by norm_num)
    have hord₁ : orderOf (⟨(u₁ : G), h₁ u₁.2⟩ : ↥(S : Subgroup G)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact hu₁'
    have hord₂ : orderOf (⟨(u₂ : G), h₂ u₂.2⟩ : ↥(S : Subgroup G)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact hu₂'
    have heq : (⟨(u₁ : G), h₁ u₁.2⟩ : ↥(S : Subgroup G)) = ⟨(u₂ : G), h₂ u₂.2⟩ :=
      unique_involution_of_cyclic hord₁ hord₂
    have hval : (u₁ : G) = (u₂ : G) :=
      congrArg (fun x : ↥(S : Subgroup G) => (x : G)) heq
    exact ⟨(u₁ : G), hne₁, u₁.2, by rw [hval]; exact u₂.2⟩
  · -- ## `S ≅ DihedralGroup n`
    have hcardS : Nat.card ↥(S : Subgroup G) = 2 * n := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    by_cases hn2 : n = 2
    · -- `|S| = 4`, so `Q₁ = Q₂ = S`
      have hcardS4 : Nat.card ↥(S : Subgroup G) = 4 := by rw [hcardS, hn2]
      have hQ₁S : Q₁ = (S : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge h₁ (by rw [hcardS4]; exact hc₁)
      have hQ₂S : Q₂ = (S : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge h₂ (by rw [hcardS4]; exact hc₂)
      obtain ⟨u₁, hu₁⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd₁
      have hu₁' : orderOf (u₁ : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu₁
      have hne₁ : (u₁ : G) ≠ 1 := by
        rintro h1
        rw [h1, orderOf_one] at hu₁'
        exact absurd hu₁' (by norm_num)
      exact ⟨(u₁ : G), hne₁, u₁.2, by rw [hQ₂S, ← hQ₁S]; exact u₁.2⟩
    · -- `4 ≤ n`: `dih_helper` produces the cyclic index-two subgroup and its involution
      have h4n : 4 ≤ n := by
        obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
        have h2n : 2 * n = 2 ^ k := by rw [← hcardS, hk]
        have h4S : 4 ≤ 2 ^ k := by
          have h : 4 ≤ Nat.card ↥(S : Subgroup G) :=
            le_trans hc₁ (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le h₁))
          rwa [hcardS, h2n] at h
        have hk2 : 2 ≤ k := by
          have h : 2 ^ 2 ≤ 2 ^ k := by simpa using h4S
          exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp h
        have hn : n = 2 ^ (k - 1) := by
          have h3 : 2 * n = 2 * 2 ^ (k - 1) := by
            rw [h2n, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
          exact Nat.mul_left_cancel (by norm_num) h3
        have h2k1 : 2 ≤ k - 1 := by
          rcases Nat.lt_or_ge (k - 1) 2 with h | h
          · exfalso
            have hk1 : k - 1 = 1 := by omega
            exact hn2 (by rw [hn, hk1, pow_one])
          · exact h
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) h2k1
          _ = n := hn.symm
      obtain ⟨T0, τ, hT0le, hT0cyc, hT0idx, hτT0, hτ2, hτuniq⟩ := dih_helper h4n e
      refine ⟨τ, (fun h1 => by rw [h1, orderOf_one] at hτ2; exact absurd hτ2 (by norm_num)), ?_, ?_⟩
      · exact cyclic_index_two_center_mem (S := (S : Subgroup G)) (S0 := T0) S.isPGroup'
          hT0le hT0cyc hT0idx hτT0 hτ2 hτuniq Q₁ h₁ hc₁
      · exact cyclic_index_two_center_mem (S := (S : Subgroup G)) (S0 := T0) S.isPGroup'
          hT0le hT0cyc hT0idx hτT0 hτ2 hτuniq Q₂ h₂ hc₂

/-- Bender 1981 Lemma 2.9, D16 case (iv) at the leaf's hypotheses.  Route (no solubility of `N`
needed): `4 ∣ |E|` by `isQuasisimple_four_dvd` (`E ≠ ⊥` as `E` is quasisimple); `E ≤ layer N`
as `E` is normal quasisimple in `↥N`, so `V ⊓ E = ⊥` by `h2` and `V ⊓ E` is `⊥` for two
subgroups of a common Sylow of `G`: take a Sylow 2-subgroup `Q` of `E ⊔ V` containing `V`;
then `Q ⊓ E` is a Sylow 2-subgroup of `E`, of order `≥ 4`, and `Q ≤ S'` for a Sylow `S'` of
`G`; `S'` is cyclic or dihedral and is a 2-group, so `V` and `Q ⊓ E` (order `≥ 4`) both
contain the central involution of `S'`, contradiction. -/
theorem L29_case_iv_leaf {G : Type} [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (V N : Subgroup G) (h : Work.CORE2B.L29Hyp B V N)
    (h2 : V ⊓ Work.GW2.layerIn N = ⊥) (E : Subgroup ↥N) [E.Normal]
    (hEqs : Work.GW2.IsQuasisimple E) : False := by
  classical
  -- ## Step 1: `E` has order divisible by `4`
  have hEne : E ≠ ⊥ := isQuasisimple_ne_bot E hEqs
  have h4E : 4 ∣ Nat.card E := isQuasisimple_four_dvd E hEqs hEne
  -- ## Step 2: the image `E.map N.subtype` lies in `layerIn N`, hence `V ⊓ E.map N.subtype = ⊥`
  have hEle : E ≤ Work.GW2.layer ↥N := le_sSup ⟨inferInstance, hEqs⟩
  have hE'le : E.map N.subtype ≤ Work.GW2.layerIn N := by
    rw [Work.GW2.layerIn]
    exact Subgroup.map_mono hEle
  have hdisj : V ⊓ E.map N.subtype = ⊥ := by
    have hle : V ⊓ E.map N.subtype ≤ V ⊓ Work.GW2.layerIn N := inf_le_inf_left V hE'le
    rw [h2] at hle
    exact le_bot_iff.mp hle
  -- ## Step 3: a `2`-subgroup of `G` containing `V` and meeting `E.map N.subtype` in order `≥ 4`
  have hVH4 : Nat.card ↥(V.subgroupOf N) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.V_le_N).toEquiv, h.four.1]
  obtain ⟨T0, hT02, hVT0, hT0card⟩ :=
    L29_sylow_piece (N := ↥N) (A := E) (V := V.subgroupOf N) h4E hVH4
  set T : Subgroup G := T0.map N.subtype with hTdef
  have hT2 : IsPGroup 2 T := hT02.map N.subtype
  have hVT : V ≤ T := by
    intro v hv
    rw [hTdef, Subgroup.mem_map]
    exact ⟨⟨v, h.V_le_N hv⟩, hVT0 (Subgroup.mem_subgroupOf.mpr hv), rfl⟩
  have hTcard : 4 ≤ Nat.card ↥(T ⊓ E.map N.subtype) := by
    have hTinf : T ⊓ E.map N.subtype = (T0 ⊓ E).map N.subtype := by
      rw [hTdef, ← Subgroup.map_inf T0 E N.subtype N.subtype_injective]
    rw [hTinf, Subgroup.card_map_of_injective N.subtype_injective]
    exact hT0card
  -- ## Step 4: `T` lies in a Sylow `2`-subgroup `S'` of `G`
  obtain ⟨S', hTS'⟩ := IsPGroup.exists_le_sylow hT2
  -- ## Step 5: two subgroups of order `≥ 4` of the cyclic-or-dihedral Sylow `S'` meet
  obtain ⟨z, hz1, hzV, hzTE⟩ :=
    inf_ne_bot_of_le_sylow hctx.sylow S' V (T ⊓ E.map N.subtype) (hVT.trans hTS')
      (inf_le_left.trans hTS') h.four.1.ge hTcard
  -- ## Step 6: contradiction with `V ⊓ E.map N.subtype = ⊥`
  have hmem : z ∈ V ⊓ E.map N.subtype := ⟨hzV, hzTE.2⟩
  rw [hdisj] at hmem
  exact hz1 (Subgroup.mem_bot.mp hmem)

end Work.CORE2B
