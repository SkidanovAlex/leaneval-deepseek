import Mathlib
import Submission.Work.ThmF.ChV12.JFormClosedFin
import Submission.Work.ThmF.ChV12.L5bridge
import Submission.Work.PSU3.StageA.not_caseA
import Submission.Work.PSU3.StageA.centD_ne_bot
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ThmF.ChV12.JformReduction
import Submission.Work.ThmF.Bender.DTransitiveInv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The FT-free route to case a) of Ch. VI §1, from `TransitiveLinearSolvable`

* `L5cruxProp_of_JFormClosedFin` is the bridge of
  `Submission/Work/ThmF/ChV12/L5bridge.lean` with the classical closure statement replaced by its
  finite form `JFormClosedFin`;
* `L5cruxProp_of_transitiveLinearSolvable` composes it with
  `JFormClosedFin_of_transitiveLinearSolvable`;
* `not_caseA_of_transitiveLinearSolvable` eliminates case a) of the Ch. VI §1 trichotomy;
* `isSolvable_twoPoint_of_W_eq_bot_of_transitiveLinearSolvable` supplies the solvability of
  `D = twoPoint H t` that Ch. V §1 Prop. 2 (Peterfalvi's Appendix X route) consumes, in the branch
  `W = ⊥` where `D` acts faithfully and transitively on `Q₀ ∖ {1}`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.ThmF.ChV12

open Submission.Blueprint

theorem L5cruxProp_of_JFormClosedFin (h : JFormClosedFin) : L5cruxProp := by
  intro G _ _ H Q t s hC4 hyp hQ
  by_cases hX : Work.ThmF.Lemma5.X5 H t = ⊤
  · refine Or.inr ?_
    by_contra hV
    have hDK : twoPoint H t = Work.ThmF.Ksub H t :=
      X5_eq_top_imp_twoPoint_eq_Ksub hC4 hyp hX
    have hCent : twoPoint H t ⊓
        Subgroup.centralizer (Work.ThmF.Q0sub H : Set G) = ⊥ :=
      X5_eq_top_imp_centD_ne_bot_imp_centralizer_eq_bot hC4 hyp hX hV
    have hcomm := Work.ThmF.L5.involutions_commute hyp.sit hC4 hyp.split
    have hA2 : ∀ x ∈ Work.ThmF.Q0sub H, x * x = 1 := by
      intro x hx
      have hxQ0 : x ∈ Work.ThmF.Q0 H := (Work.ThmF.L5.mem_Q0sub_iff hC4 hyp x).mp hx
      rcases Work.ThmF.mem_Q0_iff.mp hxQ0 with ⟨-, hord⟩ | rfl
      · have h2 : x ^ 2 = 1 := by
          have := pow_orderOf_eq_one x
          rwa [hord] at this
        simpa [pow_two] using h2
      · simp
    have hAc : ∀ x ∈ Work.ThmF.Q0sub H, ∀ y ∈ Work.ThmF.Q0sub H, x * y = y * x := by
      intro x hx y hy
      have hxI : x ∈ Work.ThmF.Q0 H := (Work.ThmF.L5.mem_Q0sub_iff hC4 hyp x).mp hx
      have hyI : y ∈ Work.ThmF.Q0 H := (Work.ThmF.L5.mem_Q0sub_iff hC4 hyp y).mp hy
      rcases Work.ThmF.mem_Q0_iff.mp hxI with hx' | rfl
      · rcases Work.ThmF.mem_Q0_iff.mp hyI with hy' | rfl
        · exact hcomm x hx' y hy'
        · simp
      · simp
    have hDN : twoPoint H t ≤ Subgroup.normalizer (Work.ThmF.Q0sub H : Set G) := by
      rw [hDK]; exact Work.ThmF.L5.Ksub_le_normalizer_Q0sub hC4 hyp
    have hodd : Odd (Nat.card ↥(twoPoint H t)) := by
      rw [hDK]; exact L5oddKsub hyp
    have ht2 : t * t = 1 := Work.ThmF.L5.ht_mul_self hyp
    have htN : t ∈ Subgroup.normalizer ((twoPoint H t) : Set G) :=
      Work.ThmF.normalizes_twoPoint_of_data (Work.ThmF.IsSplitRankOne.toData hyp.split)
    have htrans : ∀ a ∈ Work.ThmF.Q0sub H, a ≠ 1 → ∀ b ∈ Work.ThmF.Q0sub H, b ≠ 1 →
        ∃! j : G, (j ∈ twoPoint H t ∧ t * j * t⁻¹ = j⁻¹) ∧ j * a * j⁻¹ = b := by
      intro a ha ha1 b hb hb1
      have haI : a ∈ involutions (H : Set G) := by
        have h0 := (Work.ThmF.L5.mem_Q0sub_iff hC4 hyp a).mp ha
        rcases Work.ThmF.mem_Q0_iff.mp h0 with h' | h'
        · exact h'
        · exact absurd h' ha1
      have hbI : b ∈ involutions (H : Set G) := by
        have h0 := (Work.ThmF.L5.mem_Q0sub_iff hC4 hyp b).mp hb
        rcases Work.ThmF.mem_Q0_iff.mp h0 with h' | h'
        · exact h'
        · exact absurd h' hb1
      obtain ⟨k, hk, huniq⟩ := Work.ThmF.L5.Kset_regular hyp.split a haI b hbI
      refine ⟨k, ⟨?_, hk.2⟩, ?_⟩
      · exact hk.1
      · intro y hy
        exact huniq y ⟨hy.1, hy.2⟩
    have hcl := h G (Work.ThmF.Q0sub H) (twoPoint H t) t
      hA2 hAc hDN hodd ht2 htN htrans hCent
    -- the inverted set is a subgroup of `twoPoint H t`, and it generates it
    let Jset : Set G := {j : G | j ∈ twoPoint H t ∧ t * j * t⁻¹ = j⁻¹}
    have h1J : (1 : G) ∈ Jset := ⟨(twoPoint H t).one_mem, by simp⟩
    have hmulJ : ∀ x ∈ Jset, ∀ y ∈ Jset, x * y ∈ Jset := by
      intro x hx y hy
      exact ⟨(twoPoint H t).mul_mem hx.1 hy.1, hcl x hx.1 hx.2 y hy.1 hy.2⟩
    have hinvJ : ∀ x ∈ Jset, x⁻¹ ∈ Jset := by
      intro x hx
      refine ⟨(twoPoint H t).inv_mem hx.1, ?_⟩
      have h' : t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
      rw [h', hx.2, inv_inv]
    have hKsubJ : ∀ x ∈ Work.ThmF.Ksub H t, x ∈ Jset := by
      intro x hx
      refine Subgroup.closure_induction (k := Work.ThmF.Kset H t) (p := fun y _ => y ∈ Jset)
        ?_ ?_ ?_ ?_ hx
      · intro y hy
        exact hy
      · exact h1J
      · intro y z hy hz ihy ihz
        exact hmulJ y ihy z ihz
      · intro y hy ihy
        exact hinvJ y ihy
    have hJeq : Jset = (twoPoint H t : Set G) := by
      refine Set.Subset.antisymm (fun x hx => hx.1) ?_
      intro x hx
      exact hKsubJ x (by rw [← hDK]; exact hx)
    have hbot : centD H t = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro d hd
      obtain ⟨hdD, hdC⟩ := Subgroup.mem_inf.mp hd
      have hinv : t * d * t⁻¹ = d⁻¹ := by
        have hdJ : d ∈ Jset := by rw [hJeq]; exact hdD
        exact hdJ.2
      have hfix : t * d * t⁻¹ = d := by
        have h' := (Subgroup.mem_centralizer_iff.mp hdC) t (Set.mem_singleton t)
        have htd : t * d = d * t := by first | exact h' | exact h'.symm
        rw [htd, mul_assoc, mul_inv_cancel, mul_one]
      have h3 : d = d⁻¹ := by
        calc d = t * d * t⁻¹ := hfix.symm
          _ = d⁻¹ := hinv
      have hdd : d * d = 1 := by
        have h5 : d * d = d * d⁻¹ := congrArg (fun z => d * z) h3
        rw [h5, mul_inv_cancel]
      have hdd' : (⟨d, hdD⟩ : ↥(twoPoint H t)) * ⟨d, hdD⟩ = 1 := by
        ext
        simpa using hdd
      have h2' : orderOf (⟨d, hdD⟩ : ↥(twoPoint H t)) ∣ 2 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hdd')
      have hN' : orderOf (⟨d, hdD⟩ : ↥(twoPoint H t)) ∣
          Nat.card ↥(twoPoint H t) := orderOf_dvd_natCard _
      have hoddord : Odd (orderOf (⟨d, hdD⟩ : ↥(twoPoint H t))) := hodd.of_dvd_nat hN'
      rcases (Nat.dvd_prime Nat.prime_two).mp h2' with h1 | h1
      · exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
      · obtain ⟨k, hk⟩ := hoddord
        omega
    exact hV hbot
  · exact Or.inl hX

theorem L5cruxProp_of_transitiveLinearSolvable (h : TransitiveLinearSolvable) : L5cruxProp :=
  L5cruxProp_of_JFormClosedFin (JFormClosedFin_of_transitiveLinearSolvable h)

end Work.ThmF.ChV12

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- **Case a) of Ch. VI §1 is impossible, given `L5cruxProp`.**  Reproof of
`Work.PSU3.StageA.notCaseA_of_sharpInvertingClosed` taking the crux directly. -/
theorem not_caseA_of_L5cruxProp {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hcrux : Work.ThmF.ChV12.L5cruxProp)
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    {s : G} (hs : s ∈ Q) (hs2 : orderOf s = 2) (hst : t * s * t = s * t * s) :
    (Q : Set G) ≠ Work.ThmF.Q0sub H := by
  intro hQ
  have hQ' : Q = Work.ThmF.Q0sub H := Subgroup.ext (fun x => Set.ext_iff.mp hQ x)
  rcases hcrux hC4 (notCaseA_hyp5 hS hs hs2 hst) hQ' with hX5 | hV
  · exact absurd (notCaseA_X5_eq_top hS hs hs2 hst hQ) hX5
  · exact Work.PSU3.StageA.centD_ne_bot hS hV

/-- **Case a) of Ch. VI §1, from `TransitiveLinearSolvable`.** -/
theorem not_caseA_of_transitiveLinearSolvable {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t : G} (hTLS : Work.ThmF.ChV12.TransitiveLinearSolvable)
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    {s : G} (hs : s ∈ Q) (hs2 : orderOf s = 2) (hst : t * s * t = s * t * s) :
    (Q : Set G) ≠ Work.ThmF.Q0sub H :=
  not_caseA_of_L5cruxProp (Work.ThmF.ChV12.L5cruxProp_of_transitiveLinearSolvable hTLS)
    hS hC4 hs hs2 hst

/-- **`D = twoPoint H t` is solvable in the branch `W = ⊥`**, from `TransitiveLinearSolvable`.

In that branch (Ch. II §4 Prop. 4) `D` acts faithfully on `Q₀ = Q0sub H` — the kernel is
`D ⊓ C_G(Q₀) ≤ D ⊓ C_G(Inv H) = W = ⊥` — and `D` is transitive on `Q₀ ∖ {1}` (`Q₀ ∖ {1} =
Inv H` and `D` is transitive on `Inv H`, `DTransitiveInv`).  Odd order and `TransitiveLinearSolvable`
give solvability. -/
theorem isSolvable_twoPoint_of_W_eq_bot_of_transitiveLinearSolvable {G : Type} [Group G]
    [Finite G] {H Q : Subgroup G} {t : G}
    (hTLS : Work.ThmF.ChV12.TransitiveLinearSolvable)
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hW : Work.ThmF.W H t = ⊥) :
    Group.IsSolvable ↥(Submission.Blueprint.twoPoint H t) := by
  have hcomm := Work.ThmF.L5.involutions_commute hS.situation hC4 hS.split
  obtain ⟨hQ0sq, hQ0comm, hQ0norm, hQ0inv⟩ := Work.ThmF.ChV12.Q0sub_elementary H hcomm
  have hDN : Submission.Blueprint.twoPoint H t ≤
      Subgroup.normalizer (Work.ThmF.Q0sub H : Set G) := by
    intro d hd
    have hdH : d ∈ H := Work.RankOneUniqueness.twoPoint_le_left H t hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hQ0norm d hdH x hx
    · intro hx
      have h := hQ0norm d⁻¹ (H.inv_mem hdH) (d * x * d⁻¹) hx
      rwa [show d⁻¹ * (d * x * d⁻¹) * d⁻¹⁻¹ = x by group] at h
  have hWbot : Submission.Blueprint.twoPoint H t ⊓
      Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G)) = ⊥ := by
    have hP4 := (hC4 G hS.situation H hS.split.stronglyEmbedded t hS.split.invol
      hS.split.not_mem).2.2.2.2.1
    rw [show Work.ThmF.W H t = Submission.Blueprint.twoPoint H t ⊓
      Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G)) from by
        simpa only [Work.ThmF.W, Work.ThmF.Kset] using hP4] at hW
    exact hW
  have hkerbot : Submission.Blueprint.twoPoint H t ⊓
      Subgroup.centralizer (Work.ThmF.Q0sub H : Set G) = ⊥ := by
    refine le_bot_iff.mp (le_trans ?_ (le_of_eq hWbot))
    exact inf_le_inf_left _ (Subgroup.centralizer_le (fun x hx =>
      Work.ThmF.Q0_le_Q0sub H (Work.ThmF.involutions_subset_Q0 H hx)))
  refine hTLS (fun x : ↥(Work.ThmF.Q0sub H) => Subtype.ext (by simpa using hQ0sq (x : G) x.2))
    (fun x y : ↥(Work.ThmF.Q0sub H) => Subtype.ext (by
      simpa using hQ0comm (x : G) x.2 (y : G) y.2))
    (Work.ThmF.split_odd_card_twoPoint hS.split)
    (Work.ThmF.ChV12.jAct (Work.ThmF.Q0sub H) (Submission.Blueprint.twoPoint H t) hDN) ?_ ?_
  · -- faithfulness
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hcent : ((x : ↥(Submission.Blueprint.twoPoint H t)) : G) ∈
        Subgroup.centralizer (Work.ThmF.Q0sub H : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h := congrArg (fun f : MulAut ↥(Work.ThmF.Q0sub H) =>
        ((f ⟨a, ha⟩ : ↥(Work.ThmF.Q0sub H)) : G)) hx
      simp only [MulAut.one_apply, Work.ThmF.ChV12.jAct_coe, Subgroup.coe_mk] at h
      calc a * ((x : ↥(Submission.Blueprint.twoPoint H t)) : G)
          = (((x : ↥(Submission.Blueprint.twoPoint H t)) : G) * a *
              ((x : ↥(Submission.Blueprint.twoPoint H t)) : G)⁻¹) *
              ((x : ↥(Submission.Blueprint.twoPoint H t)) : G) := by rw [h]
        _ = ((x : ↥(Submission.Blueprint.twoPoint H t)) : G) * a := by group
    have hmem : ((x : ↥(Submission.Blueprint.twoPoint H t)) : G) ∈
        Submission.Blueprint.twoPoint H t ⊓
          Subgroup.centralizer (Work.ThmF.Q0sub H : Set G) := ⟨x.2, hcent⟩
    rw [hkerbot, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  · -- transitivity
    intro a b ha hb
    have haG : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    have hbG : (b : G) ≠ 1 := fun h => hb (Subtype.ext h)
    have ha' : (a : G) ∈ Submission.Blueprint.involutions (H : Set G) := hQ0inv (a : G) a.2 haG
    have hb' : (b : G) ∈ Submission.Blueprint.involutions (H : Set G) := hQ0inv (b : G) b.2 hbG
    obtain ⟨d, hd, hdab⟩ :=
      Work.ThmF.Bender.DTransitiveInv hS.split.stronglyEmbedded hS.split.invol hS.split.not_mem
        (a : G) ha' (b : G) hb'
    exact ⟨⟨d, hd⟩, by ext; rw [Work.ThmF.ChV12.jAct_coe]; exact hdab⟩

end Work.PSU3.StageA
