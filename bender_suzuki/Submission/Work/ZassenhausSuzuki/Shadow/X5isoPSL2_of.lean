import Submission.Work.ZassenhausSuzuki.SzSetting
import Mathlib
import Submission.Work.ThmF.ChV12.Lemma5Defs
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ZassenhausSuzuki.Shadow.L5Struct
import Submission.Work.ZassenhausSuzuki.Shadow.X5RankOneAux
import Submission.Work.ZassenhausSuzuki.Shadow.L5Aux
import Submission.Work.ZassenhausSuzuki.Shadow.X5_rankOne_of
import Submission.Work.ThmF.ChV12.isZassenhaus_of_centD_eq_bot
import Submission.Work.ZassenhausPSL2.ZData.psl2_coords
import Submission.Work.ZassenhausPSL2.ZData.card_Q_eq
import Submission.Work.ZassenhausPSL2.Feit.card_excl
import Submission.Work.ZassenhausPSL2.FeitCln.card_excl_eq_one
import Submission.Work.ZassenhausPSL2.Model.psl2_datum
import Submission.Work.RankOneUniqueness.recognize

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi II, Ch. V §2 Lemma 5 (c): `⟨Q₀, K, t⟩ ≅ PSL(2, 2ⁿ)`

The identification `X = ⟨Q₀, K, t⟩ ≅ PSL(2, 2ⁿ)`, `q = |Q₀| = 2ⁿ`, in the form conditional on
the two areas `FeitThompsonProp` and `ChIIFourProp`:

* `ChIIFourProp` gives (Ch. II §4) that the involutions of `H` commute, so `Q₀ = Q₀sub H` is an
  elementary abelian `2`-group (`Q0sub_elementary`), and (through its Ch. II §4 Prop. 3 clause,
  or through Peterfalvi II App. X and `FeitThompsonProp`) that `K = J(D,t) = Ksub H t` is a
  **subgroup** (`L5prop2`);
* inside `X = ⟨Q₀,K,t⟩` the datum `(B, Q₀, t)` with `B = Q₀sub H ⊔ Ksub H t` is a split
  rank-one datum and `X` is simple (`X5_rankOne_of`), and `V = C_{B ∩ Bᵗ}(t) = 1`
  (`centD_bor_eq_bot` below), so `B` is a Zassenhaus subgroup
  (`isZassenhaus_of_centD_eq_bot`);
* `ZassenhausPSL2`'s machinery (`Feit.card_excl`, `FeitCln.card_excl_eq_one`,
  `ZData.card_Q_eq`, `ZData.psl2_coords`, `Model.psl2_datum`, `RankOneUniqueness.recognize`)
  then coordinatises `Q₀` by `Multiplicative (GF(2ⁿ))` with `f` = inversion and recognises `X`
  as `PSL(2, 2ⁿ)`.

The conclusion `Nat.card ↥(Q0sub H) = 2 ^ n` for the *same* `n` is read off from the
coordinatisation `e : ↥(Q₀sub H).subgroupOf X ≃* Multiplicative (GF(2ⁿ))`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open Classical LeanEval.GroupTheory.Defs

namespace Work.ZassenhausSuzuki.Shadow.ChV12
open Submission.Blueprint

open Work.ThmF.ChV12
variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

/-- **`V = 1` inside `X = ⟨Q₀,K,t⟩`.**  The Borel `B = Q₀sub H ⊔ Ksub H t` of `X` is the
point stabiliser of a point of `X ⧸ B`, `B ∩ Bᵗ = Ksub H t` (`L5.X5`), and `t` inverts every
element of `Ksub H t` (because `Ksub H t = Kset H t`); hence the two-point stabiliser of `B`
contains no element centralising `t`: `C_{B ∩ Bᵗ}(t) = 1`. -/
theorem centD_bor_eq_bot (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    (h : Work.ZassenhausSuzuki.SzHyp H Q t s) :
    centD ((Work.ZassenhausSuzuki.Shadow.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t))
      (Work.ThmF.Lemma5.tX H t) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [centD, Subgroup.mem_inf] at hx
  obtain ⟨hx1, hx2⟩ := hx
  -- `x` lies in `Ksub H t`
  have hxK : x ∈ (Work.ThmF.Ksub H t).subgroupOf (Work.ThmF.Lemma5.X5 H t) := by
    rw [← Work.ZassenhausSuzuki.Shadow.L5.twoPoint_bor_subgroupOf h]
    exact hx1
  have hxKg : ((x : ↥(Work.ThmF.Lemma5.X5 H t)) : G) ∈ Work.ThmF.Ksub H t :=
    Subgroup.mem_subgroupOf.mp hxK
  have hxKset : ((x : ↥(Work.ThmF.Lemma5.X5 H t)) : G) ∈ Work.ThmF.Kset H t := by
    rw [← hKsub]; exact hxKg
  set xx : G := ((x : ↥(Work.ThmF.Lemma5.X5 H t)) : G) with hxx
  have htinvt : t * xx * t⁻¹ = xx⁻¹ := (Work.ThmF.mem_Kset_iff.mp hxKset).2
  -- `x` commutes with `tX`
  have hcent : Work.ThmF.Lemma5.tX H t * x = x * Work.ThmF.Lemma5.tX H t :=
    (Subgroup.mem_centralizer_iff.mp hx2) (Work.ThmF.Lemma5.tX H t) rfl
  have hcommG : xx * t = t * xx := by
    have h'' := congrArg (fun y : ↥(Work.ThmF.Lemma5.X5 H t) => (y : G)) hcent
    have h1 : ((Work.ThmF.Lemma5.tX H t * x : ↥(Work.ThmF.Lemma5.X5 H t)) : G)
        = t * ((x : ↥(Work.ThmF.Lemma5.X5 H t)) : G) := rfl
    have h2 : ((x * Work.ThmF.Lemma5.tX H t : ↥(Work.ThmF.Lemma5.X5 H t)) : G)
        = ((x : ↥(Work.ThmF.Lemma5.X5 H t)) : G) * t := rfl
    rw [h1, h2] at h''
    exact h''.symm
  have htt : t * t = 1 := by
    have h1 : t ^ 2 = 1 := by simpa [h.split.invol] using pow_orderOf_eq_one t
    simpa [pow_two] using h1
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  -- hence `t xx t = xx`, so `xx⁻¹ = xx` and `xx ^ 2 = 1`
  have hconj : t * xx * t = xx := by
    calc t * xx * t = (t * xx) * t := by rw [mul_assoc]
      _ = (xx * t) * t := by rw [hcommG]
      _ = xx * (t * t) := by rw [mul_assoc]
      _ = xx := by rw [htt, mul_one]
  have hsq : xx * xx = 1 := by
    have h2 : xx⁻¹ = xx := by rw [← htinvt, hti, hconj]
    calc xx * xx = xx * xx⁻¹ := by rw [h2]
      _ = 1 := mul_inv_cancel xx
  -- but `xx` lies in `D = twoPoint H t`, of odd order, so `xx = 1`
  have hx2p : xx ∈ twoPoint H t := Work.ThmF.Ksub_le_twoPoint (H := H) t hxKg
  have hdvd : orderOf xx ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hsq)
  have hodd : Odd (orderOf xx) :=
    Odd.of_dvd_nat (Work.ThmF.split_odd_card_twoPoint h.split)
      (Subgroup.orderOf_dvd_natCard (twoPoint H t) hx2p)
  have hone : orderOf xx = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact h1
    · rw [h1] at hodd
      exact absurd hodd (Nat.not_odd_iff_even.mpr even_two)
  have hxx1 : xx = 1 := orderOf_eq_one_iff.mp hone
  exact Subtype.ext hxx1

theorem X5isoPSL2_of {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (h : Work.ZassenhausSuzuki.SzHyp H Q t s) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n ∧
      Nonempty (↥(Work.ThmF.Lemma5.X5 H t) ≃* LeanEval.GroupTheory.Defs.PSL2Model n) := by
  classical
  -- `ChIIFourProp`: the involutions of `H` commute, so `Q₀ = Q₀sub H` is elementary abelian
  have hcomm := Work.ZassenhausSuzuki.SzHyp.hcomm h
  -- `K = J(D,t)` is the subgroup `Ksub H t` (Ch. V §1 Prop. 2, via App. X and `hFT`)
  have hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t :=
    (Work.ZassenhausSuzuki.SzHyp.Ksub_eq_Kset h)
  -- inside `X = ⟨Q₀,K,t⟩`: `X` is simple and `(B, Q₀, t)` is a split rank-one datum
  obtain ⟨hsimple, hsplit, -⟩ := X5_rankOne_of h
  haveI : IsSimpleGroup ↥(Work.ThmF.Lemma5.X5 H t) := hsimple
  haveI : Fintype ↥(Work.ThmF.Lemma5.X5 H t) := Fintype.ofFinite _
  have h2 : IsPGroup 2 ↥((Work.ThmF.Q0sub H).subgroupOf (Work.ThmF.Lemma5.X5 H t)) :=
    Work.ZassenhausSuzuki.Shadow.L5.isPGroup_two_Q0sub_sub (H := H) hcomm
  have hab : IsAbelianSubgroup
      ((Work.ThmF.Q0sub H).subgroupOf (Work.ThmF.Lemma5.X5 H t)) :=
    Work.ZassenhausSuzuki.Shadow.L5.isAbelianSubgroup_Q0sub_sub (H := H) hcomm
  -- `V = 1` in `X`, so the Borel is a Zassenhaus subgroup
  have hcentD := centD_bor_eq_bot hKsub h
  have hz : IsZassenhaus
      ((Work.ZassenhausSuzuki.Shadow.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) :=
    isZassenhaus_of_centD_eq_bot hsplit h2 hcentD
  -- Feit's count gives `|Q₀| = |D| + 1`
  have hcz := Work.ZassenhausPSL2.FeitCln.card_excl_eq_one hsplit hz h2 hab
  have hmul := Work.ZassenhausPSL2.Feit.card_excl hsplit hz h2 hab
  have hcard := Work.ZassenhausPSL2.ZData.card_Q_eq hcz hmul
  -- field coordinates: `Q₀ ≃* Multiplicative (GF(2ⁿ))`, the `f`-relation being inversion
  obtain ⟨n, hn, e, hf⟩ := Work.ZassenhausPSL2.ZData.psl2_coords hsplit hz h2 hab hcard
  refine ⟨n, hn, ?_, ?_⟩
  · rw [← Work.ZassenhausSuzuki.Shadow.L5.card_subgroupOf_Q0sub (H := H)]
    exact (Nat.card_congr e.toEquiv).trans
      (Work.ZassenhausSuzuki.Shadow.L5.card_multiplicative_galoisField n (by omega))
  · obtain ⟨M⟩ := Work.ZassenhausPSL2.Model.psl2_datum n hn
    exact Work.RankOneUniqueness.recognize Work.RankOneUniqueness.rankOneQUniqueness
      hsplit M e hf

end Work.ZassenhausSuzuki.Shadow.ChV12
