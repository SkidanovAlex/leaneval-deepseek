import Mathlib
import Submission.Work.ZJB.Step1.Defs
import Submission.Work.ZJB2.Step1.dltProp
import Submission.Work.ZJB2.Step1.sylowOfNormalizerProp
import Submission.Work.ZJB2.Step1.zsLeZJProp
import Submission.Work.ZJB2.Step1.thompsonJEqOfLeProp
import Submission.Work.ZJB2.Step1.cardSylowInProp
import Submission.Work.ZJB2.Step1.exists_isSylowIn_of_le
import Submission.Work.ZJB2.Step1.dMemProp

namespace Work.ZJB2.Step1

/-!
# ZJB2, step (I), leaf I.4 (`ExistsT1Prop`): a Sylow subgroup `T₁` of `N(D)` beating `D`

Glauberman 1968, Theorem 5.1, step (I), (5.1)+(5.3) (pp. 1117–1118).  Let `S` be a Sylow
`p`-subgroup of `G`, `S₁` a *bad* Sylow `p`-subgroup in the sense of `MaxBad S S₁`, and

`D = Dsub S S₁ = N_G(J(S)) ∩ S₁`,   `J = J(S)`.

Because `S₁` is bad, `S₁ ⊄ N_G(J)` (leaf I.1, `dltProp`), so `D ⊊ S₁`.  Consequently

`|D| < |S₁| = p^{ν_p(|G|)} = |S| = p^{ν_p(|N_G(J)|)}`,

i.e. `D` is a `p`-subgroup of `N_G(J)` which is *not* Sylow there: it lies in a strictly larger
Sylow `p`-subgroup `T` of `N_G(J)`.  In the `p`-group `T` the subgroup `D` is properly contained
in its normalizer `Q := N_G(D) ∩ T`, which is a `p`-subgroup of `N_G(J) ∩ N_G(D)` strictly
containing `D`.  Extending `Q` to a Sylow `p`-subgroup `T₁` of `N_G(D)` gives

`|D| < |Q| ≤ |N_G(J) ∩ T₁|`,

which is the assertion of `ExistsT1Prop`.

The mathematical content beyond the Sylow counting is the normalizer condition for `p`-groups
(`lt_normalizer_inf_of_isPGroup` below); the counting uses leaf F2 (`cardSylowInProp`).
-/

open Subgroup

/-- `S` is a Sylow `p`-subgroup of `N_G(J(S))`: it is a `p`-subgroup (it is one of `G`) and it is
maximal as such, because any `p`-subgroup of `G` containing the Sylow `p`-subgroup `S` equals
`S`. -/
theorem isSylowIn_sylow_normalizer_thompsonJ {G : Type*} [Group G] {p : ℕ} (S : Sylow p G) :
    Work.ZJB.IsSylowIn p (S : Subgroup G)
      (Subgroup.normalizer (Work.GW2.thompsonJ (S : Subgroup G) : Set G)) := by
  refine ⟨sylow_le_normalizer_thompsonJ S, S.isPGroup', ?_⟩
  intro Q hSQ _ hQp
  exact S.is_maximal' hQp hSQ

/-- A proper subgroup `D` of a `p`-group `T` is a proper subgroup of its normalizer inside `T`:
a finite `p`-group is nilpotent, hence satisfies the normalizer condition. -/
theorem lt_normalizer_inf_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {D T : Subgroup G} (hT : IsPGroup p T) (hDT : D < T) :
    D < Subgroup.normalizer (D : Set G) ⊓ T := by
  classical
  have hNC : NormalizerCondition ↥T :=
    @Group.normalizerCondition_of_isNilpotent ↥T _ hT.isNilpotent
  have hD_le : D ≤ T := le_of_lt hDT
  have hsub_lt_top : D.subgroupOf T < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact (ne_of_lt hDT) (le_antisymm hD_le htop)
  have hlt := hNC (D.subgroupOf T) hsub_lt_top
  obtain ⟨t, ht_norm, ht_not⟩ := IsConcreteLE.exists_of_lt hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hD_le, Subgroup.mem_subgroupOf] at ht_norm
  rw [Subgroup.mem_subgroupOf] at ht_not
  refine lt_of_le_of_ne (le_inf Subgroup.le_normalizer hD_le) ?_
  intro heq
  apply ht_not
  have hmem : (t : G) ∈ Subgroup.normalizer (D : Set G) ⊓ T := ⟨ht_norm, t.2⟩
  rw [← heq] at hmem
  exact hmem

/-- **I.4 (5.1)+(5.3).**  For a bad Sylow `p`-subgroup `S₁` there is a Sylow `p`-subgroup `T₁` of
`N_G(D)`, `D = Dsub S S₁`, containing `D` with `|D| < |N_G(J(S)) ∩ T₁|`. -/
theorem existsT1Prop {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] : Work.ZJB.ExistsT1Prop p G := by
  intro S S₁ hbad
  set NJ : Subgroup G := Subgroup.normalizer (Work.GW2.thompsonJ (S : Subgroup G) : Set G)
    with hNJ
  -- `D` is the intersection `N_G(J) ∩ S₁`
  have hDdef : Work.ZJB.Dsub S S₁ = NJ ⊓ (S₁ : Subgroup G) := rfl
  have hD_le_NJ : Work.ZJB.Dsub S S₁ ≤ NJ := hDdef.le.trans inf_le_left
  have hD_le_S1 : Work.ZJB.Dsub S S₁ ≤ (S₁ : Subgroup G) := hDdef.le.trans inf_le_right
  have hDp : IsPGroup p (Work.ZJB.Dsub S S₁) := S₁.isPGroup'.to_le hD_le_S1
  -- `D ≠ S₁`, since `S₁ ≤ N_G(J)` would contradict leaf I.1 (`dltProp`)
  have hD_lt_S1 : Work.ZJB.Dsub S S₁ < (S₁ : Subgroup G) := by
    refine lt_of_le_of_ne hD_le_S1 ?_
    intro hEq
    have hS1_le_NJ : (S₁ : Subgroup G) ≤ NJ := hEq ▸ hD_le_NJ
    exact (dltProp S S₁ hbad.1 hbad.2.1) (hS1_le_NJ.trans (le_of_eq hNJ))
  -- `S` is a Sylow `p`-subgroup of `N_G(J)`
  have hS_syl : Work.ZJB.IsSylowIn p (S : Subgroup G) NJ :=
    isSylowIn_sylow_normalizer_thompsonJ (p := p) S
  -- `D` is not a Sylow `p`-subgroup of `N_G(J)`, so it lies in a strictly larger one `T`
  obtain ⟨T, hT_syl, hDT_le⟩ :=
    exists_isSylowIn_of_le (p := p) (M := NJ) (A := Work.ZJB.Dsub S S₁) hD_le_NJ hDp
  have hcard1 : Nat.card ↥(Work.ZJB.Dsub S S₁) < Nat.card ↥(S₁ : Subgroup G) :=
    Subgroup.card_lt_of_lt hD_lt_S1
  have hcard2 : Nat.card ↥(S₁ : Subgroup G) = p ^ (Nat.card G).factorization p := by
    simpa using Sylow.card_eq_multiplicity (p := p) S₁
  have hcard3 : Nat.card ↥(S : Subgroup G) = p ^ (Nat.card G).factorization p := by
    simpa using Sylow.card_eq_multiplicity (p := p) S
  have hcard4 : Nat.card ↥(S : Subgroup G) = p ^ (Nat.card ↥NJ).factorization p := by
    simpa [Work.ZJB.nuP] using cardSylowInProp (p := p) (G := G) (S : Subgroup G) NJ hS_syl
  have hcard5 : Nat.card ↥T = p ^ (Nat.card ↥NJ).factorization p := by
    simpa [Work.ZJB.nuP] using cardSylowInProp (p := p) (G := G) T NJ hT_syl
  have hcardD_T : Nat.card ↥(Work.ZJB.Dsub S S₁) < Nat.card ↥T :=
    calc Nat.card ↥(Work.ZJB.Dsub S S₁) < Nat.card ↥(S₁ : Subgroup G) := hcard1
      _ = p ^ (Nat.card G).factorization p := hcard2
      _ = Nat.card ↥(S : Subgroup G) := hcard3.symm
      _ = p ^ (Nat.card ↥NJ).factorization p := hcard4
      _ = Nat.card ↥T := hcard5.symm
  have hDT_lt : Work.ZJB.Dsub S S₁ < T := by
    refine lt_of_le_of_ne hDT_le ?_
    rintro hEq
    rw [hEq] at hcardD_T
    exact absurd hcardD_T (lt_irrefl _)
  -- inside the `p`-group `T`, the normalizer of `D` is strictly larger than `D`
  have hTp : IsPGroup p T := hT_syl.2.1
  have hQgt : Work.ZJB.Dsub S S₁ <
      Subgroup.normalizer (Work.ZJB.Dsub S S₁ : Set G) ⊓ T :=
    lt_normalizer_inf_of_isPGroup (p := p) hTp hDT_lt
  have hT_le_NJ : T ≤ NJ := hT_syl.1
  -- extend `Q = N_G(D) ∩ T` to a Sylow `p`-subgroup `T₁` of `N_G(D)`
  obtain ⟨T₁, hT₁_syl, hQT₁⟩ :=
    exists_isSylowIn_of_le (p := p)
      (M := Subgroup.normalizer (Work.ZJB.Dsub S S₁ : Set G))
      (A := Subgroup.normalizer (Work.ZJB.Dsub S S₁ : Set G) ⊓ T)
      inf_le_left (hTp.to_le inf_le_right)
  refine ⟨T₁, hT₁_syl, (le_inf Subgroup.le_normalizer hDT_le).trans hQT₁, ?_⟩
  have hQ_le_inf : Subgroup.normalizer (Work.ZJB.Dsub S S₁ : Set G) ⊓ T ≤ NJ ⊓ T₁ :=
    le_inf (inf_le_right.trans hT_le_NJ) hQT₁
  exact lt_of_lt_of_le (Subgroup.card_lt_of_lt hQgt) (Subgroup.card_le_of_le hQ_le_inf)

end Work.ZJB2.Step1
