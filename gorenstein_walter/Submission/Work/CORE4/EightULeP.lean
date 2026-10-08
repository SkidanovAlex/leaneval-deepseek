import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.EightAeqOmega
import Submission.Work.CORE4.ConjSubOrbitNcard
import Submission.Work.CORE4.ncard_subgroups_prime_cube
import Submission.Work.CORE4.E2Z2le
import Submission.Work.CORE4.EightAnormalPcore_of_Qpos

namespace Work.CORE4

open Work.GW2 Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## Auxiliary: `Z(Q)` is invariant under anything normalising `Q`

`centerIn Q` is the centre of `Q` viewed in the ambient group.  Since it is characteristic in
`Q`, every element of a normaliser of `Q` normalises it as well. -/

/-- `Z(Q)` (viewed in `G`) is invariant under anything normalising `Q`. -/
theorem conjSub_centerIn_eq {Q : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    Work.GW2.conjSub g (centerIn Q) = centerIn Q := by
  have hQ : Work.GW2.conjSub g Q = Q := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hmem : ∀ z : G, z ∈ Q ↔ (MulAut.conj g) z ∈ Q := by
    intro z
    constructor
    · intro hz; rw [← hQ]; exact Subgroup.mem_map_of_mem _ hz
    · intro hz
      have hg' : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) := (Subgroup.normalizer _).inv_mem hg
      have hQ' : Work.GW2.conjSub g⁻¹ Q = Q :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hg'
      have h2 : (MulAut.conj g⁻¹) ((MulAut.conj g) z) ∈ Work.GW2.conjSub g⁻¹ Q :=
        Subgroup.mem_map_of_mem _ hz
      rw [hQ'] at h2
      simpa [MulAut.conj_apply, mul_assoc] using h2
  rw [Work.GW2.conjSub]
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    obtain ⟨hyQ, hyc⟩ := mem_centerIn_iff.mp hy
    rw [← hyx]
    rw [mem_centerIn_iff]
    refine ⟨(hmem y).mp hyQ, ?_⟩
    intro z hz
    have hzQ : (MulAut.conj g⁻¹) z ∈ Q := (hmem ((MulAut.conj g⁻¹) z)).mpr (by
      have hgg : (MulAut.conj g) ((MulAut.conj g⁻¹) z) = z := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [hgg]; exact hz)
    have h := hyc ((MulAut.conj g⁻¹) z) hzQ
    calc (MulAut.conj g) y * z = (MulAut.conj g) (y * (MulAut.conj g⁻¹) z) := by
          simp [MulAut.conj_apply, mul_assoc]
      _ = (MulAut.conj g) ((MulAut.conj g⁻¹) z * y) := by rw [h]
      _ = z * (MulAut.conj g) y := by simp [MulAut.conj_apply, mul_assoc]
  · intro x hx
    obtain ⟨hxQ, hxc⟩ := mem_centerIn_iff.mp hx
    refine Subgroup.mem_map.mpr ⟨(MulAut.conj g⁻¹) x, ?_, ?_⟩
    · rw [mem_centerIn_iff]
      refine ⟨(hmem ((MulAut.conj g⁻¹) x)).mpr (by
        have hgg : (MulAut.conj g) ((MulAut.conj g⁻¹) x) = x := by
          simp [MulAut.conj_apply, mul_assoc]
        rw [hgg]; exact hxQ), ?_⟩
      intro z hz
      have hzQ : (MulAut.conj g) z ∈ Q := (hmem z).mp hz
      have h := hxc ((MulAut.conj g) z) hzQ
      calc (MulAut.conj g⁻¹) x * z = (MulAut.conj g⁻¹) (x * (MulAut.conj g) z) := by
            simp [MulAut.conj_apply, mul_assoc]
        _ = (MulAut.conj g⁻¹) ((MulAut.conj g) z * x) := by rw [h]
        _ = z * (MulAut.conj g⁻¹) x := by simp [MulAut.conj_apply, mul_assoc]
    · simp [MulAut.conj_apply, mul_assoc]

/-! ## Case 2 of the §4 (8) trichotomy: the orbit count `u ≤ p`

Bender 1981, §4 (8), p. 226: put `Q := Ω₁(Z₂(O_p(U)))`.  In the second case of the trichotomy,
`Z(Q) < A < Q` with `|Q : A| = p`.  The `U`-conjugates of `A` are then among the (at most)
`p + 1` subgroups of `Q` of order `p ^ 2` containing the `U`-invariant subgroup `Z(Q)`, while
`u = |U : N_U(A)|` is odd; hence `u ≤ p`. -/

/-- **Bender 1981, §4 (8), case 2 (p. 226)**: if `A` is a `(p,p)`-subgroup (`|A| = p²`,
exponent `p`) of a subgroup `Q ≤ U` of exponent `p` with `Q` normalised by `U`, `Z(Q) < A`
and `|Q : A| = p`, then `u = |U : N_U(A)| ≤ p`. -/
theorem eightU_le_p_of_case2 (B : Work.GW2.BenderSetup G) {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    {A Q : Subgroup G} (hQN : B.U ≤ Subgroup.normalizer (Q : Set G))
    (hAQ : A ≤ Q) (hZlt : centerIn Q < A)
    (hAcard : Nat.card ↥A = p ^ 2) (hidx : A.relIndex Q = p)
    (hQexp : ∀ x ∈ Q, x ^ p = 1) :
    Work.GW2.Case2EightU B A ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `|Q| = p ^ 3`
  have hAQ' : A ⊓ Q = A := inf_eq_left.mpr hAQ
  have hcardQ : Nat.card ↥Q = p ^ 3 := by
    have h := Subgroup.relIndex_mul_card A Q
    rw [hAQ', hAcard, hidx] at h
    rw [← h]; ring
  -- `Q` is nontrivial, hence `Z(Q) ≠ ⊥`
  have hQnt : Nontrivial ↥Q := by
    refine (Subgroup.nontrivial_iff_ne_bot Q).mpr ?_
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardQ
    have h2 : 2 ≤ p := hp.two_le
    nlinarith [hcardQ]
  haveI := hQnt
  have hQP : IsPGroup p ↥Q := by
    rw [IsPGroup.iff_card]
    exact ⟨3, hcardQ⟩
  have hZbot : (Subgroup.center ↥Q) ≠ ⊥ := by
    haveI : Group.IsNilpotent ↥Q := hQP.isNilpotent
    exact Group.IsNilpotent.center_ne_bot ↥Q
  have hZne : centerIn Q ≠ ⊥ := by
    intro hb
    apply hZbot
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ centerIn Q := Subgroup.mem_map_of_mem Q.subtype hx
    rw [hb] at hx'
    exact Subtype.ext (Subgroup.mem_bot.mp hx')
  -- `|Z(Q)| = p`
  have hZle : centerIn Q ≤ A := le_of_lt hZlt
  have hZdiv : Nat.card ↥(centerIn Q) ∣ p ^ 2 := by
    rw [← hAcard]; exact Subgroup.card_dvd_of_le hZle
  have hZlt2 : Nat.card ↥(centerIn Q) ≠ p ^ 2 := by
    intro h
    refine (ne_of_lt hZlt) (Subgroup.eq_of_le_of_card_ge hZle ?_)
    rw [h, hAcard]
  have hZcard : Nat.card ↥(centerIn Q) = p := by
    rcases (Nat.dvd_prime_pow hp).mp hZdiv with ⟨k, hk, hkeq⟩
    have hk1 : Nat.card ↥(centerIn Q) ≠ 1 := by
      intro h1
      exact hZne (Subgroup.card_eq_one.mp h1)
    have hk01 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk01 with rfl | rfl | rfl
    · rw [pow_zero] at hkeq; exact absurd hkeq hk1
    · rwa [pow_one] at hkeq
    · exact absurd hkeq hZlt2
  -- the count of subgroups of `Q` of order `p²` containing `Z(Q)`
  have hcount : {H : Subgroup G | H ≤ Q ∧ Nat.card ↥H = p ^ 2 ∧ centerIn Q ≤ H}.ncard
      = p + 1 :=
    ncard_subgroups_prime_cube p hp Q hQexp hcardQ hZcard
  -- every `U`-conjugate of `A` is such a subgroup
  have hsub : {X : Subgroup G | ∃ h : G, h ∈ B.U ∧ X = Work.GW2.conjSub h A} ⊆
      {H : Subgroup G | H ≤ Q ∧ Nat.card ↥H = p ^ 2 ∧ centerIn Q ≤ H} := by
    rintro X ⟨h, hh, rfl⟩
    have hhN : h ∈ Subgroup.normalizer (Q : Set G) := hQN hh
    have hQc : Work.GW2.conjSub h Q = Q := Subgroup.mem_normalizer_iff_map_conj_eq.mp hhN
    refine ⟨?_, ?_, ?_⟩
    · calc Work.GW2.conjSub h A ≤ Work.GW2.conjSub h Q := Subgroup.map_mono hAQ
        _ = Q := hQc
    · rw [Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj h).injective, hAcard]
    · rw [← conjSub_centerIn_eq hhN]
      exact Subgroup.map_mono hZle
  have hle : Work.GW2.Case2EightU B A ≤ p + 1 := by
    show (B.U ⊓ Subgroup.normalizer (A : Set G)).relIndex B.U ≤ p + 1
    rw [← ConjSubOrbitNcard B.U A]
    exact (Set.ncard_le_ncard hsub).trans_eq hcount
  -- `u` is odd
  have hoddU : Odd (Work.GW2.Case2EightU B A) :=
    Odd.of_dvd_nat B.U_odd
      (Subgroup.relIndex_dvd_card (B.U ⊓ Subgroup.normalizer (A : Set G)) B.U)
  have hp1even : Even (p + 1) := by
    obtain ⟨k, hk⟩ := hpodd
    exact ⟨k + 1, by omega⟩
  have hne : Work.GW2.Case2EightU B A ≠ p + 1 := by
    intro h
    rw [h] at hoddU
    exact (Nat.not_even_iff_odd.mpr hoddU) hp1even
  omega

theorem EightULeP (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ¬ Work.GW2.Case2InvNormal B h.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
          Work.GW2.Case2EightObj h.D p P A →
          Work.GW2.Case2EightU B A ≤ p := by sorry

end Work.CORE4
