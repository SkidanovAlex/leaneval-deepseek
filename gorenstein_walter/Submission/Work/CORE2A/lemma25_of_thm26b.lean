import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.conj_BenderSetup
import Submission.Work.CORE2A.fstar_ne_bot
import Submission.Work.BMAX.FstarSamePrime
import Submission.Work.ASM.oddCore_odd

/-!
# GW design pass 22: Bender 1981 Lemma 2.5 from Lemma 2.3 (BMAX form), 2.4 and Thm 2.6 step 2

Source check (page image p. 219): Lemma 2.3's standing hypothesis is `Ĥ ⇝ M`, NOT `Ĥ ◁ M`
(the OCR renders `⇝` as "4"/"d").  In 2.5, Bender gets `F*(Ĥ^g) ≤ Ĥ` "and in particular
`Ĥ^g ⇝ Ĥ`" -- the witness is `X = 1`.  So `Lemma23Prop` (BMAX) is exactly what is needed.
The only extra input is `E(Ĥ^g) ≤ Ĥ`, which we take from `Thm26bProp` (`E(Ĥ) = 1`, proved by
`thm26b_v14` without Lemma 2.5).
-/

open Subgroup Work.GW2

namespace Work.CORE2A

/-! Copied from `CORE4/FittingInConj.lean` (its `CORE4.Defs` import clashes with `ASM.Defs`). -/
theorem fitting_map_le {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (Work.GW2.fitting A).map e.toMonoidHom ≤ Work.GW2.fitting B := by
  haveI : (Subgroup.map e.toMonoidHom
      ((sSup {N : Subgroup A | N.Normal ∧ Group.IsNilpotent N}).normalCore)).Normal :=
    (Subgroup.normalCore_normal _).map e.toMonoidHom e.surjective
  have hmain : Subgroup.map e.toMonoidHom
        ((sSup {N : Subgroup A | N.Normal ∧ Group.IsNilpotent N}).normalCore)
      ≤ sSup {N : Subgroup B | N.Normal ∧ Group.IsNilpotent N} := by
    refine le_trans (Subgroup.map_mono (f := e.toMonoidHom) (Subgroup.normalCore_le _)) ?_
    rw [Subgroup.map_le_iff_le_comap, sSup_le_iff]
    intro N hN
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨hN.1.map e.toMonoidHom e.surjective, ?_⟩
    haveI : Group.IsNilpotent ↥N := hN.2
    exact Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective N e.toMonoidHom e.injective)
  show (Subgroup.map e.toMonoidHom
      ((sSup {N : Subgroup A | N.Normal ∧ Group.IsNilpotent N}).normalCore)) ≤ Work.GW2.fitting B
  rw [Work.GW2.fitting]
  exact Subgroup.normal_le_normalCore.mpr hmain

theorem fitting_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (Work.GW2.fitting A).map e.toMonoidHom = Work.GW2.fitting B := by
  refine le_antisymm (fitting_map_le e) ?_
  have h := Subgroup.map_mono (f := e.toMonoidHom) (fitting_map_le e.symm)
  have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id B := by ext x; simp
  rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h

theorem FittingInConj {G : Type} [Group G] (A : Subgroup G) (φ : G ≃* G) :
    Work.GW2.fittingIn (A.map φ.toMonoidHom) = (Work.GW2.fittingIn A).map φ.toMonoidHom := by
  unfold Work.GW2.fittingIn
  rw [← fitting_map_mulEquiv (Subgroup.equivMapOfInjective A φ.toMonoidHom φ.injective)]
  rw [Subgroup.map_map]
  have hcomp : (A.map φ.toMonoidHom).subtype.comp
      (Subgroup.equivMapOfInjective A φ.toMonoidHom φ.injective).toMonoidHom
      = φ.toMonoidHom.comp A.subtype := by ext x; rfl
  rw [hcomp, ← Subgroup.map_map]

/-- **Bridge.** `F*(A) ≤ B` gives `A ⇝ B` (witness `X = 1`). -/
theorem bRel_of_fstarIn_le {G : Type*} [Group G] {A B : Subgroup G} (h : fstarIn A ≤ B) :
    BRel A B :=
  ⟨⊥, bot_le, inf_le_right.trans h⟩

/-- Iterated commutators of a subgroup, inside the ambient group. -/
def dser {X : Type*} [Group X] (O : Subgroup X) : ℕ → Subgroup X
  | 0 => O
  | n + 1 => ⁅dser O n, dser O n⁆

theorem dser_eq_map {X : Type*} [Group X] (O : Subgroup X) (n : ℕ) :
    dser O n = (derivedSeries O n).map O.subtype := by
  induction n with
  | zero => show O = _; rw [derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  | succ n ih => rw [dser, derivedSeries_succ, Subgroup.map_commutator, ih]

theorem dser_normal {X : Type*} [Group X] (O : Subgroup X) [O.Normal] (n : ℕ) :
    (dser O n).Normal := by
  induction n with
  | zero => simpa [dser]
  | succ n ih => haveI := ih; rw [dser]; exact Subgroup.commutator_normal _ _

theorem dser_le {X : Type*} [Group X] (O : Subgroup X) (n : ℕ) : dser O n ≤ O := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [dser, Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact ih (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb))

/-- **`O(K) ≠ 1` excludes `F*(K)` a 2-group** (via FT: a nontrivial solvable normal odd
subgroup contains a nontrivial abelian normal subgroup, which lies in `F(K)`). -/
theorem not_isPGroup_two_fstarIn (hFT : FeitThompsonProp) {G : Type} [Group G] [Finite G]
    {K : Subgroup G} (hO : oddCoreIn K ≠ ⊥) : ¬ IsPGroup 2 (fstarIn K) := by
  intro h2
  set O : Subgroup K := oddCore K with hOdef
  have hOne : O ≠ ⊥ := by
    intro hb; apply hO; rw [oddCoreIn, ← hOdef, hb, Subgroup.map_bot]
  have hOodd : Odd (Nat.card O) := Work.ASM.oddCore_odd K
  have hsol : Group.IsSolvable O := hFT O hOodd
  obtain ⟨m, hm⟩ := (Group.isSolvable_def O).mp hsol
  have hex : ∃ n, dser O n = ⊥ := ⟨m, by rw [dser_eq_map, hm, Subgroup.map_bot]⟩
  classical
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0; have := Nat.find_spec hex; rw [h0] at this; exact hOne this
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := Nat.exists_eq_succ_of_ne_zero hn0
  set A : Subgroup K := dser O k
  have hAne : A ≠ ⊥ := Nat.find_min hex (by omega)
  have hAA : ⁅A, A⁆ = ⊥ := by have := Nat.find_spec hex; rwa [hk] at this
  haveI : A.Normal := dser_normal O k
  haveI : IsMulCommutative A := ⟨⟨fun a b => by
    have h1 := Subgroup.commutator_mem_commutator a.2 b.2
    rw [hAA, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact Subtype.ext h1⟩⟩
  haveI : Group.IsNilpotent A := inferInstance
  have hAF : A ≤ fitting K := Work.CORE2A.le_fitting_of_normal_isNilpotent
  have h2K : IsPGroup 2 (fstar K) :=
    h2.of_equiv (Subgroup.equivMapOfInjective _ _ K.subtype_injective).symm
  have h2A : IsPGroup 2 A := h2K.to_le (hAF.trans le_sup_left)
  have hAodd : Odd (Nat.card A) :=
    Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le (dser_le O k))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp h2A
  have hj0 : j = 0 := by
    by_contra hj0
    rw [hj] at hAodd
    exact (Nat.not_even_iff_odd.mpr hAodd) ((Nat.even_pow' hj0).mpr even_two)
  apply hAne
  rw [← Subgroup.card_eq_one, hj, hj0, pow_zero]

/-- **Bender 1981, Lemma 2.5**, from `Lemma23Prop` (BMAX), `Lemma24Prop`, `Thm26bProp`. -/
theorem lemma25_of_thm26b (h23 : Lemma23Prop) (h24 : Lemma24Prop) (h26b : Thm26bProp) :
    Lemma25Prop := by
  intro G _ _ hFT hctx B g hO hrel
  set M := conjSub g B.Hhat with hMdef
  obtain ⟨B', -, -, -, hB'⟩ := Work.CORE2A.conj_BenderSetup B g
  have hLH : layerIn B.Hhat = ⊥ := h26b G hFT hctx B
  have hLM : layerIn M = ⊥ := by rw [hMdef, ← hB']; exact h26b G hFT hctx B'
  have hFH := Work.BMAX.fstarIn_eq_fittingIn_of_layerIn_eq_bot hLH
  have hFM := Work.BMAX.fstarIn_eq_fittingIn_of_layerIn_eq_bot hLM
  have hFconj : fittingIn M = (fittingIn B.Hhat).map (MulAut.conj g).toMonoidHom :=
    FittingInConj B.Hhat (MulAut.conj g)
  have hcard : Nat.card (fittingIn M) = Nat.card (fittingIn B.Hhat) := by
    rw [hFconj]; exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hcoat : IsCoatom M := Work.CORE2A.BenderConj.isCoatom_conjSub B.Hhat_coatom g
  by_cases hp : ∃ p : ℕ, p.Prime ∧ IsPGroup p (fstarIn B.Hhat)
  · obtain ⟨p, hpp, hpH⟩ := hp
    have hp2 : p ≠ 2 := by
      rintro rfl; exact not_isPGroup_two_fstarIn hFT hO hpH
    have hpM : IsPGroup p (fstarIn M) := by
      rw [hFM, hFconj]; rw [hFH] at hpH; exact hpH.map _
    exact (h24 G hFT hctx B M hcoat hrel p hpp hp2 hpH hpM).symm
  · have h3 := h23 G hFT hctx B M hcoat.1 hrel
    have hpi : fittingPiIn B.pi M = fittingIn M := by
      apply Work.BMAX.fittingPiIn_eq_fittingIn_of_primeFactors_subset
      intro q hq
      show q ∈ (Nat.card (fittingIn B.Hhat)).primeFactors
      rw [← hcard, fittingIn, Subgroup.card_map_of_injective M.subtype_injective]
      exact hq
    have hle : fstarIn M ≤ B.Hhat := by rw [hFM, ← hpi]; exact h3.1 hp
    rcases h3.2.2 hcoat (bRel_of_fstarIn_le hle) with h | ⟨p, hpp, hpH, -⟩
    · exact h.symm
    · exact absurd ⟨p, hpp, hpH⟩ hp

end Work.CORE2A

#print axioms Work.CORE2A.lemma25_of_thm26b
