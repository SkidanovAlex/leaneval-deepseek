import Mathlib
import Submission.Work.PSU3.StageB.Step1
import Submission.Work.ThmF.Setup
import Submission.Work.ThreePoints.Basic
import Submission.Work.Reductions.OddResidual

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

-- Note (proof-level only; the statement below is unchanged): the requester's original import list
-- included `Submission.Work.PSU3.StageB.centralizer_oddResidual_isPSU3_v2`.  That import is *not*
-- needed here — this file uses neither `inf_center_centralizerOddResidual_eq_bot` nor
-- `centralizer_oddResidual_isPSU3_v2` (the latter is still `hole`-ed) — and it pulls in the whole
-- `Work.Higman`/`Work.HallHigman` development (~1700 modules), an order of magnitude more than the
-- proof below needs.  Consumers that *do* want those two lemmas should import that module directly.
-- Everything used below is available from the five imports above.

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.PSU3.StageB

/-
# Step 4 bookkeeping (ii): `|U_Y| = |C_Q(P)|` (Peterfalvi II.7.4(1))

`F := U = O^{2'}(C_G(P))` (`Work.PSU3.StageB.centralizerOddResidual P`), `S` a Sylow
`2`-subgroup of `F ⊓ H` (data produced by `ChIIFourProp` P3 with `X = P`: `hSp` says it is a
`2`-group and `hSidx` that its index in `F ⊓ H` is odd), and `φ : ↥F →* Y` a surjection with
`φ.ker = Z(F)` (so `Y = F/Z(F)`).  Then the image of `S` in `Y` — the unipotent radical `U_Y` of
the Borel `B_Y = (H ⊓ F)/(H ⊓ F ⊓ Z(F))` of `Y` — has the same order as the fixed-point subgroup
`C_Q(P) = Q ⊓ C_G(P)`:

    Nat.card ↥((S.subgroupOf F).map φ) = Nat.card ↥(Q ⊓ C_G(P)).

Route:
* `(S.subgroupOf F).map φ` has order `|S| / |S ⊓ Z(F)|` (kernel of the restriction of `φ`), and
  `S ⊓ Z(F) = ⊥` by `Work.PSU3.StageB.inf_center_centralizerOddResidual_eq_bot` (in
  `Submission.Work.PSU3.StageB.centralizer_oddResidual_isPSU3_v2`, needs `S ≤ Q` and `Z(F) ≤ P`,
  the latter being `Work.PSU3.StageB.centralizerOddResidual_center_le_P`); so `|U_Y| = |S|`.
* `S = Q ⊓ C_G(P)`: `S ≤ Q` (a `2`-subgroup of `H` lies in `Q`, since `|H : Q| = |D|` is odd —
  `Work.ThmF.split_odd_card_twoPoint` or the odd-index argument used in
  `Submission.Work.PSU3.StageA.lemma2c`) and `S ≤ F ≤ C_G(P)`, so `S ≤ C := Q ⊓ C_G(P)`;
  conversely `C` is a `2`-subgroup of `F ⊓ H` (its elements are `2`-elements of `Q ≤ H` and of
  `C_G(P)`, hence lie in `O^{2'}(C_G(P)) = F`), so `|C|` divides `|S|` because `S` is a Sylow
  `2`-subgroup of `F ⊓ H`; hence `S = C` by `S ≤ C` and `|C| ∣ |S|`.

Both steps are carried out below, with the last step (`ker` of the restriction of `φ` to
`S.subgroupOf F`) obtained directly from the hypothesis `hZS` (`S ⊓ Z(F) = ⊥`), rather than from
the source's `Z(U) ⊆ P`: the two inputs `S ≤ Q` and `Z(F) ⊆ P` that the docstring above lists are
exactly what is needed to turn `hZS` into `(S.subgroupOf F) ⊓ φ.ker = ⊥`.

⚠ No hypothesis is dropped: the statement is proved *as requested*.  Note that `hPV`, `hPp` and
the surjectivity of `φ` are not used (the equality of *orders* of the image and `C_Q(P)` only
needs injectivity of `φ` on `S.subgroupOf F`).
-/

/-! ## Elementary `2`-group lemmas (local copies of the standard facts) -/

/-- An element of `2`-power order lies in `O^{2'}` (`oddResidual`). -/
private theorem mem_oddResidual_of_pow_two_eq_one {L : Type} [Group L] [Finite L] {x : L}
    {k : ℕ} (hx : x ^ 2 ^ k = 1) : x ∈ Submission.Blueprint.oddResidual L := by
  induction k generalizing x with
  | zero =>
      rw [pow_zero, pow_one] at hx
      rw [hx]
      exact Subgroup.one_mem _
  | succ k ih =>
      have h2 : (x * x) ^ 2 ^ k = 1 := by
        rw [← pow_two, ← pow_mul, ← pow_succ', hx]
      exact Work.Reductions.mem_oddResidual_of_mul_self_mem (ih h2)

/-- An element of `2`-power order lies in every normal subgroup of odd index. -/
private theorem mem_of_pow_two_eq_one_of_normal_odd_index {G : Type} [Group G] [Finite G]
    {N : Subgroup G} [hN : N.Normal] (hodd : Odd N.index) {x : G} {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : x ∈ N := by
  have h1 : orderOf (QuotientGroup.mk' N x) ∣ 2 ^ k := by
    rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, hx, map_one]
  have h2 : orderOf (QuotientGroup.mk' N x) ∣ N.index := by
    rw [Subgroup.index_eq_card]; exact orderOf_dvd_natCard _
  obtain ⟨j, -, hje⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h3 : 2 ^ j ∣ N.index := hje ▸ h2
  have hj0 : j = 0 := by
    by_contra hj
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have h2dvd : 2 ∣ N.index := by
      refine dvd_trans ?_ h3
      rw [hs, pow_succ]; exact dvd_mul_left 2 _
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)
  have hone : orderOf (QuotientGroup.mk' N x) = 1 := by rw [hje, hj0, pow_zero]
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp hone)

/-- An element of `C ≤ G` whose order is a power of `2` lies in the image of `O^{2'}(C)` in `G`. -/
private theorem mem_map_oddResidual_of_pow_two_eq_one {G : Type} [Group G] [Finite G]
    {C : Subgroup G} {x : G} (hx : x ∈ C) {k : ℕ} (h : x ^ 2 ^ k = 1) :
    x ∈ (Submission.Blueprint.oddResidual ↥C).map C.subtype := by
  refine Subgroup.mem_map.mpr ⟨(⟨x, hx⟩ : ↥C), ?_, rfl⟩
  exact mem_oddResidual_of_pow_two_eq_one (x := (⟨x, hx⟩ : ↥C)) (k := k) (by
    apply Subtype.ext
    simpa using h)

/-- `O^{2'}(C_G(P))` (as a subgroup of `G`) is contained in `C_G(P)`. -/
private theorem centralizerOddResidual_le_centralizer {G : Type} [Group G] {P : Subgroup G} :
    centralizerOddResidual P ≤ Subgroup.centralizer (P : Set G) := by
  simp only [centralizerOddResidual]
  exact Subgroup.map_subtype_le _

/-! ## The main theorem -/

theorem card_map_sylow_eq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) {P : Subgroup G}
    (hPV : P ≤ Submission.Blueprint.centD H t) (hPp : (Nat.card P).Prime)
    {S : Subgroup G} (hSp : IsPGroup 2 S)
    (hSFH : S ≤ Work.PSU3.StageB.centralizerOddResidual P ⊓ H)
    (hSidx : ¬ 2 ∣ (S.subgroupOf (Work.PSU3.StageB.centralizerOddResidual P ⊓ H)).index)
    {Y : Type} [Group Y] [Finite Y] {φ : ↥(Work.PSU3.StageB.centralizerOddResidual P) →* Y}
    (hker : φ.ker = Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P))
    (hZS : S ⊓ (Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P)).map
        (Work.PSU3.StageB.centralizerOddResidual P).subtype = ⊥) :
    Nat.card ↥((S.subgroupOf (Work.PSU3.StageB.centralizerOddResidual P)).map φ)
      = Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G)) := by
  classical
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := hS.split
  have hSF : S ≤ centralizerOddResidual P := hSFH.trans inf_le_left
  have hF_le_Gc : centralizerOddResidual P ≤ Subgroup.centralizer (P : Set G) :=
    centralizerOddResidual_le_centralizer

  -- ## Step 1. `(S.subgroupOf F) ⊓ φ.ker = ⊥`, hence `φ` is injective on `S.subgroupOf F`
  have hker_bot : (S.subgroupOf (centralizerOddResidual P)) ⊓ φ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxS, hxk⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_bot]
    have hxG : ((x : ↥(centralizerOddResidual P)) : G) ∈ S :=
      Subgroup.mem_subgroupOf.mp hxS
    have hxZ : ((x : ↥(centralizerOddResidual P)) : G) ∈
        (Subgroup.center ↥(centralizerOddResidual P)).map
          (centralizerOddResidual P).subtype := by
      rw [hker] at hxk
      exact Subgroup.mem_map.mpr ⟨x, hxk, rfl⟩
    have hxbot : ((x : ↥(centralizerOddResidual P)) : G) ∈
        S ⊓ (Subgroup.center ↥(centralizerOddResidual P)).map
          (centralizerOddResidual P).subtype := Subgroup.mem_inf.mpr ⟨hxG, hxZ⟩
    rw [hZS, Subgroup.mem_bot] at hxbot
    exact Subtype.ext hxbot

  have hinj : Function.Injective
      (fun a : ↥(S.subgroupOf (centralizerOddResidual P)) => φ a) := by
    intro a b hab
    have hmem1 : ((a : ↥(centralizerOddResidual P)))⁻¹ *
        ((b : ↥(centralizerOddResidual P))) ∈ (S.subgroupOf (centralizerOddResidual P)) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ a.2) b.2
    have hmem2 : ((a : ↥(centralizerOddResidual P)))⁻¹ *
        ((b : ↥(centralizerOddResidual P))) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have hab' : φ ((a : ↥(centralizerOddResidual P))) =
          φ ((b : ↥(centralizerOddResidual P))) := hab
      rw [map_mul, map_inv, hab', inv_mul_cancel]
    have hmem : ((a : ↥(centralizerOddResidual P)))⁻¹ *
        ((b : ↥(centralizerOddResidual P))) ∈
        (S.subgroupOf (centralizerOddResidual P)) ⊓ φ.ker :=
      Subgroup.mem_inf.mpr ⟨hmem1, hmem2⟩
    rw [hker_bot, Subgroup.mem_bot] at hmem
    have hb_eq : (b : ↥(centralizerOddResidual P)) = (a : ↥(centralizerOddResidual P)) := by
      have h := congrArg (fun z => (a : ↥(centralizerOddResidual P)) * z) hmem
      rw [mul_one] at h
      rw [← h]; group
    exact Subtype.ext hb_eq.symm

  have hcard1 : Nat.card ↥((S.subgroupOf (centralizerOddResidual P)).map φ)
      = Nat.card ↥(S.subgroupOf (centralizerOddResidual P)) := by
    let ψ : ↥(S.subgroupOf (centralizerOddResidual P)) →* Y :=
      φ.comp (S.subgroupOf (centralizerOddResidual P)).subtype
    have hψinj : Function.Injective ψ := fun a b h => hinj h
    have hrange : (S.subgroupOf (centralizerOddResidual P)).map φ = ψ.range := by
      ext y
      constructor
      · intro hy
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
        exact ⟨⟨a, ha⟩, rfl⟩
      · rintro ⟨a, ha⟩
        exact Subgroup.mem_map.mpr ⟨(a : ↥(centralizerOddResidual P)), a.2, ha⟩
    calc Nat.card ↥((S.subgroupOf (centralizerOddResidual P)).map φ)
        = Nat.card ↥(ψ.range) := by rw [hrange]
      _ = Nat.card ↥(Subgroup.map ψ ⊤) := by rw [MonoidHom.range_eq_map]
      _ = Nat.card ↥(⊤ : Subgroup ↥(S.subgroupOf (centralizerOddResidual P))) :=
            Subgroup.card_map_of_injective hψinj
      _ = Nat.card ↥(S.subgroupOf (centralizerOddResidual P)) := Subgroup.card_top
  have hcard2 : Nat.card ↥(S.subgroupOf (centralizerOddResidual P)) = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSF).toEquiv

  -- ## Step 2. `S = Q ⊓ C_G(P)`
  -- ### 2a. `|H : Q| = |D|` is odd
  have hQHindex : (Q.subgroupOf H).index = Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
    have hcard := Subgroup.card_mul_index (Q.subgroupOf H)
    have h1 : Nat.card ↥(Q.subgroupOf H) = Nat.card ↥Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsplit.le).toEquiv
    rw [h1, Work.ThmF.split_card_H hsplit] at hcard
    exact Nat.mul_left_cancel Nat.card_pos hcard
  -- ### 2b. every `2`-element of `H` lies in `Q`, so `S ≤ Q`
  have hS_le_Q : S ≤ Q := by
    intro x hx
    obtain ⟨n, hn⟩ := hSp (⟨x, hx⟩ : ↥S)
    have hxn : (⟨x, (hSFH hx).2⟩ : ↥H) ^ 2 ^ n = 1 := by
      apply Subtype.ext
      have := congrArg (fun g : ↥S => (g : G)) hn
      simpa using this
    refine Subgroup.mem_subgroupOf.mp (mem_of_pow_two_eq_one_of_normal_odd_index
      (N := Q.subgroupOf H) (hN := Work.ThmF.split_Q_normal_in_H hsplit) ?_ hxn)
    rw [hQHindex]
    exact Work.ThmF.split_odd_card_twoPoint hsplit
  -- ### 2c. `C := Q ⊓ C_G(P)` is a `2`-subgroup of `F ⊓ H`
  have hC_le_F : Q ⊓ Subgroup.centralizer (P : Set G) ≤ centralizerOddResidual P := by
    intro x hx
    obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨n, hn⟩ := hS.two (⟨x, hxQ⟩ : ↥Q)
    have hpow : x ^ 2 ^ n = 1 := by
      have := congrArg (fun g : ↥Q => (g : G)) hn
      simpa using this
    have hmem := mem_map_oddResidual_of_pow_two_eq_one
      (C := Subgroup.centralizer (P : Set G)) hxC hpow
    simpa only [centralizerOddResidual] using hmem
  have hS_le_C : S ≤ Q ⊓ Subgroup.centralizer (P : Set G) :=
    le_inf hS_le_Q (hSF.trans hF_le_Gc)
  have hC_le_FH : Q ⊓ Subgroup.centralizer (P : Set G) ≤ centralizerOddResidual P ⊓ H :=
    le_inf hC_le_F (inf_le_left.trans hsplit.le)
  have hC2 : IsPGroup 2 ↥(Q ⊓ Subgroup.centralizer (P : Set G)) := by
    intro x
    obtain ⟨n, hn⟩ := hS.two (⟨(x : G), x.2.1⟩ : ↥Q)
    refine ⟨n, ?_⟩
    apply Subtype.ext
    have := congrArg (fun g : ↥Q => (g : G)) hn
    simpa using this
  -- ### 2d. the Sylow argument
  have hS_eq_C : S = Q ⊓ Subgroup.centralizer (P : Set G) := by
    have hcardSS : Nat.card ↥(S.subgroupOf (centralizerOddResidual P ⊓ H)) = Nat.card ↥S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSFH).toEquiv
    have hcardFH : Nat.card ↥(centralizerOddResidual P ⊓ H)
        = Nat.card ↥S * (S.subgroupOf (centralizerOddResidual P ⊓ H)).index := by
      rw [← Subgroup.card_mul_index (S.subgroupOf (centralizerOddResidual P ⊓ H)), hcardSS]
    have hodd_idx : Odd (S.subgroupOf (centralizerOddResidual P ⊓ H)).index :=
      Nat.not_even_iff_odd.mp (fun h => hSidx (even_iff_two_dvd.mp h))
    obtain ⟨j, hj⟩ := hC2.exists_card_eq
    obtain ⟨k, hk⟩ := hSp.exists_card_eq
    have hdvd : 2 ^ j ∣ (S.subgroupOf (centralizerOddResidual P ⊓ H)).index * Nat.card ↥S := by
      have h1 : Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G)) ∣
          Nat.card ↥S * (S.subgroupOf (centralizerOddResidual P ⊓ H)).index := by
        rw [← hcardFH]
        exact Subgroup.card_dvd_of_le hC_le_FH
      rwa [hj, mul_comm] at h1
    have hcop : Nat.Coprime (2 ^ j) (S.subgroupOf (centralizerOddResidual P ⊓ H)).index :=
      (Nat.coprime_two_right.mpr hodd_idx).symm.pow_left j
    have hdvdS : 2 ^ j ∣ Nat.card ↥S := hcop.dvd_of_dvd_mul_left hdvd
    have hle : Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G)) ≤ Nat.card ↥S := by
      rw [hk] at hdvdS
      rw [hj, hk]
      exact Nat.le_of_dvd (by positivity) hdvdS
    exact Subgroup.eq_of_le_of_card_ge hS_le_C hle

  -- ## Step 3. Assembly
  rw [hcard1, hcard2, hS_eq_C]

end Work.PSU3.StageB
