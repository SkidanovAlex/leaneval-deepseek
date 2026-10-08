import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.CommutingPairsAux
import Submission.Work.CORE3.CosetInvCountAPI

/-!
# `Work.CORE3.CommutingPairsEqCosetSum`

Bender 1981 §3 (8): the number of pairs of commuting involutions `(z, s)` with `z ∉ Ĥ` and
`s ∈ Ĥ` equals the sum, over the nontrivial cosets of `Ĥ`, of the number of ordered pairs of
distinct commuting involutions of that coset.

The proof is a single bijection, the "shear" `σ(z, s) = (z, z * s)` (`Work.CORE3.pairShear`),
which carries `Work.CORE3.commutingPairsOutsideHat B` onto
`Work.CORE3.commutingPairsSameCoset B`:

* `z * s` is an involution of the same coset as `z` lying outside `Ĥ`;
* conversely, for a pair `(z, z')` of distinct commuting involutions outside `Ĥ` in a common
  coset, `s = z⁻¹ * z' ∈ Ĥ` is an involution commuting with `z`.

The right-hand side is then the coset decomposition of `commutingPairsSameCoset B`: the pairs
in a nontrivial coset are exactly the ordered pairs of distinct commuting involutions counted by
`Work.CORE3.cosetPairCount`.
-/

namespace Work.CORE3

open Work.GW2

variable {G : Type} [Group G] [Finite G]

/-- A set-builder `ncard` in a finite type is a `Finset.filter`-cardinality. -/
private lemma ncard_eq_filter_card {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] :
    ({x : α | p x} : Set α).ncard = (Finset.univ.filter p).card := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

/-- A twice-filtered `card` is the `ncard` of the corresponding conjunction set. -/
private lemma filter_card_eq_ncard {α : Type} [Fintype α] (T U : α → Prop)
    [DecidablePred T] [DecidablePred U] :
    ((Finset.univ.filter T).filter U).card = ({a : α | T a ∧ U a} : Set α).ncard := by
  rw [Finset.filter_filter]
  exact (ncard_eq_filter_card (fun a => T a ∧ U a)).symm

/-- The shear `(z, s) ↦ (z, z * s)` is injective. -/
theorem pairShear_injective : Function.Injective (pairShear : G × G → G × G) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [pairShear, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  subst h1
  exact Prod.ext rfl (mul_left_cancel h2)

/-- The shear `(z, s) ↦ (z, z * s)` carries the pairs `(z, s)` of commuting involutions with
`z ∉ Ĥ` and `s ∈ Ĥ` onto the pairs of distinct commuting involutions outside `Ĥ` lying in a
common coset. -/
theorem pairShear_image_commutingPairsOutsideHat (B : BenderSetup G) :
    pairShear '' (commutingPairsOutsideHat B) = commutingPairsSameCoset B := by
  ext p
  obtain ⟨p1, p2⟩ := p
  change (p1, p2) ∈ pairShear '' commutingPairsOutsideHat B ↔
    (p1, p2) ∈ commutingPairsSameCoset B
  rw [Set.mem_image, commutingPairsSameCoset]
  constructor
  · rintro ⟨q, hq, hqp⟩
    obtain ⟨q1, q2⟩ := q
    rw [commutingPairsOutsideHat, Set.mem_ofPred_eq] at hq
    obtain ⟨hqz, hqs, hqcomm⟩ := hq
    rw [mem_involsOutsideHat] at hqz
    rw [mem_involsInHat] at hqs
    obtain ⟨hq1ord, hq1not⟩ := hqz
    obtain ⟨hq2mem, hq2ord⟩ := hqs
    simp only [pairShear, Prod.mk.injEq] at hqp
    obtain ⟨h1, h2⟩ := hqp
    subst h1
    subst h2
    have hq1sq : q1 * q1 = 1 := ((orderOf_eq_two_iff_mul_self q1).mp hq1ord).1
    have hq2sq : q2 * q2 = 1 := ((orderOf_eq_two_iff_mul_self q2).mp hq2ord).1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [QuotientGroup.eq]
      rw [show q1⁻¹ * (q1 * q2) = q2 from by group]
      exact hq2mem
    · intro hc
      have hq2eq : q2 = 1 := by
        have hh : q1 * q2 = q1 * 1 := by rw [mul_one]; exact hc.symm
        exact mul_left_cancel hh
      exact ((orderOf_eq_two_iff_mul_self q2).mp hq2ord).2 hq2eq
    · rw [show (q1 * q2) * q1 = q1 * (q2 * q1) by group, hqcomm]
    · exact mem_involsOutsideHat.mpr ⟨hq1ord, hq1not⟩
    · rw [mem_involsOutsideHat]
      refine ⟨?_, ?_⟩
      · refine (orderOf_eq_two_iff_mul_self (q1 * q2)).mpr ⟨?_, ?_⟩
        · rw [show (q1 * q2) * (q1 * q2) = (q1 * q1) * (q2 * q2) by
              rw [show (q1 * q2) * (q1 * q2) = q1 * (q2 * q1) * q2 by group, ← hqcomm]
              group]
          rw [hq1sq, hq2sq, mul_one]
        · intro hc
          have hq1eq : q1 = q2 := by
            calc q1 = q1 * 1 := (mul_one q1).symm
              _ = q1 * (q2 * q2) := by rw [hq2sq, mul_one]
              _ = (q1 * q2) * q2 := by group
              _ = 1 * q2 := by rw [hc]
              _ = q2 := one_mul q2
          exact hq1not (hq1eq.symm ▸ hq2mem)
      · intro hc
        have hq1mem : q1 ∈ B.Hhat := by
          have h2 : q1 = (q1 * q2) * q2 := by rw [mul_assoc, hq2sq, mul_one]
          rw [h2]
          exact B.Hhat.mul_mem hc hq2mem
        exact hq1not hq1mem
  · intro hp
    obtain ⟨hp_mk, hp_ne, hp_comm, hp1, hp2⟩ := hp
    have hp_comm' : p1 * p2 = p2 * p1 := hp_comm
    rw [mem_involsOutsideHat] at hp1 hp2
    have hp1sq : p1 * p1 = 1 := ((orderOf_eq_two_iff_mul_self p1).mp hp1.1).1
    have hp2sq : p2 * p2 = 1 := ((orderOf_eq_two_iff_mul_self p2).mp hp2.1).1
    have hp1inv : p1⁻¹ = p1 := inv_eq_of_mul_eq_one_right hp1sq
    refine ⟨(p1, p1⁻¹ * p2), ?_, ?_⟩
    · rw [commutingPairsOutsideHat, Set.mem_ofPred_eq]
      refine ⟨mem_involsOutsideHat.mpr ⟨hp1.1, hp1.2⟩, ?_, ?_⟩
      · rw [mem_involsInHat]
        refine ⟨QuotientGroup.eq.mp hp_mk, ?_⟩
        refine (orderOf_eq_two_iff_mul_self (p1⁻¹ * p2)).mpr ⟨?_, ?_⟩
        · rw [show p1⁻¹ * p2 = p1 * p2 by rw [hp1inv]]
          rw [show (p1 * p2) * (p1 * p2) = (p1 * p1) * (p2 * p2) by
              rw [show (p1 * p2) * (p1 * p2) = p1 * (p2 * p1) * p2 by group, ← hp_comm]
              group]
          rw [hp1sq, hp2sq, mul_one]
        · intro hc
          have hq1eq : p1 = p2 := by
            have hc' : p1 * p2 = 1 := by rw [← hp1inv]; exact hc
            calc p1 = p1 * 1 := (mul_one p1).symm
              _ = p1 * (p2 * p2) := by rw [hp2sq, mul_one]
              _ = (p1 * p2) * p2 := by group
              _ = 1 * p2 := by rw [hc']
              _ = p2 := one_mul p2
          exact hp_ne hq1eq
      · have hL : p1 * (p1⁻¹ * p2) = p2 := by rw [hp1inv, ← mul_assoc, hp1sq, one_mul]
        have hR : (p1⁻¹ * p2) * p1 = p2 := by
          rw [hp1inv, mul_assoc, ← hp_comm', ← mul_assoc, hp1sq, one_mul]
        rw [hL, hR]
    · simp only [pairShear]
      rw [show p1 * (p1⁻¹ * p2) = p2 by group]

/-- **The coset decomposition.**  The pairs of distinct commuting involutions outside `Ĥ` lying
in a common coset of `Ĥ` are counted by summing `Work.CORE3.cosetPairCount` over the nontrivial
cosets. -/
theorem commutingPairsSameCoset_ncard_eq_sum (B : BenderSetup G)
    [Fintype (G ⧸ B.Hhat)] [DecidableEq (G ⧸ B.Hhat)] :
    (commutingPairsSameCoset B).ncard =
      ∑ c ∈ Finset.univ.filter (fun c : G ⧸ B.Hhat => c ≠ ((1 : G) : G ⧸ B.Hhat)),
        cosetPairCount B.Hhat (Quotient.out c) := by
  classical
  haveI : Fintype (G × G) := Fintype.ofFinite _
  have h1 : (commutingPairsSameCoset B).ncard
      = (Finset.univ.filter (fun p : G × G => p ∈ commutingPairsSameCoset B)).card :=
    ncard_eq_filter_card (fun p : G × G => p ∈ commutingPairsSameCoset B)
  rw [h1]
  rw [Finset.card_eq_sum_card_fiberwise
        (f := fun p : G × G => (QuotientGroup.mk p.1 : G ⧸ B.Hhat))
        (t := Finset.univ.filter (fun c : G ⧸ B.Hhat => c ≠ ((1 : G) : G ⧸ B.Hhat)))
        ?hm]
  · refine Finset.sum_congr rfl ?_
    intro c hc
    have hcne : c ≠ ((1 : G) : G ⧸ B.Hhat) := (Finset.mem_filter.mp hc).2
    rw [filter_card_eq_ncard (fun p : G × G => p ∈ commutingPairsSameCoset B)
          (fun p : G × G => (QuotientGroup.mk p.1 : G ⧸ B.Hhat) = c)]
    have hset : ({p : G × G | p ∈ commutingPairsSameCoset B ∧
          (QuotientGroup.mk p.1 : G ⧸ B.Hhat) = c} : Set (G × G))
        = {p : G × G | p.1 ∈ cosetInvolSet B.Hhat (Quotient.out c) ∧
            p.2 ∈ cosetInvolSet B.Hhat (Quotient.out c) ∧ p.1 ≠ p.2 ∧
            p.1 * p.2 = p.2 * p.1} := by
      ext p
      simp only [Set.mem_ofPred_eq, mem_cosetInvolSet]
      constructor
      · rintro ⟨hp, hcmk⟩
        rw [commutingPairsSameCoset, Set.mem_ofPred_eq] at hp
        obtain ⟨hmk, hne, hcomm, hx, hy⟩ := hp
        rw [mem_involsOutsideHat] at hx hy
        exact ⟨⟨hx.1, (mk_eq_iff_leftRel B.Hhat c p.1).mp hcmk⟩,
          ⟨hy.1, (mk_eq_iff_leftRel B.Hhat c p.2).mp (hmk ▸ hcmk)⟩, hne, hcomm⟩
      · rintro ⟨⟨hx2, hxc⟩, ⟨hy2, hyc⟩, hne, hcomm⟩
        have hxmk : (QuotientGroup.mk p.1 : G ⧸ B.Hhat) = c :=
          (mk_eq_iff_leftRel B.Hhat c p.1).mpr hxc
        have hymk : (QuotientGroup.mk p.2 : G ⧸ B.Hhat) = c :=
          (mk_eq_iff_leftRel B.Hhat c p.2).mpr hyc
        refine ⟨?_, hxmk⟩
        rw [commutingPairsSameCoset, Set.mem_ofPred_eq]
        exact ⟨by rw [hxmk, hymk], hne, hcomm,
          ⟨hx2, fun hmem => hcne (hxmk ▸ (mk_eq_one_iff B.Hhat p.1).mpr hmem)⟩,
          ⟨hy2, fun hmem => hcne (hymk ▸ (mk_eq_one_iff B.Hhat p.2).mpr hmem)⟩⟩
    rw [hset]
    rfl
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [commutingPairsSameCoset, Set.mem_ofPred_eq] at hp
    obtain ⟨-, -, -, hp1, -⟩ := hp
    rw [mem_involsOutsideHat] at hp1
    intro h
    exact hp1.2 ((mk_eq_one_iff B.Hhat p.1).mp h)

theorem CommutingPairsEqCosetSum (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    [Fintype (G ⧸ B.Hhat)] [DecidableEq (G ⧸ B.Hhat)] :
    (Work.CORE3.commutingPairsOutsideHat B).ncard =
      ∑ c ∈ Finset.univ.filter (fun c : G ⧸ B.Hhat => c ≠ ((1 : G) : G ⧸ B.Hhat)),
        Work.CORE3.cosetPairCount B.Hhat (Quotient.out c) := by
  have h1 : (Work.CORE3.commutingPairsOutsideHat B).ncard
      = (Work.CORE3.commutingPairsSameCoset B).ncard := by
    rw [← Set.ncard_image_of_injective (f := pairShear) (commutingPairsOutsideHat B)
            pairShear_injective,
      pairShear_image_commutingPairsOutsideHat B]
  rw [h1]
  exact commutingPairsSameCoset_ncard_eq_sum B

end Work.CORE3
