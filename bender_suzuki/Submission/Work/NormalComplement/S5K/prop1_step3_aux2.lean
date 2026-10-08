/-
# `Submission.Work.NormalComplement.S5K.prop1_step3_aux2`

Auxiliary lemmas for the proof of Peterfalvi I Ch. III §4 Prop. 1, step 3:

* `card_dvd_card_of_fixedPointFree` — a finite group acting with trivial stabilisers on a finite
  set has order dividing the cardinality of the set;
* `fpf_on_P1modP` — the fixed-point-freeness of `C_A(P)` on `P₁/P` (formula (∗)).
-/
import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.S5K.prop1_step3_defs
import Submission.Work.NormalComplement.S5K.Defs
import Submission.Work.NormalComplement.S5K.prop1_step3_aux
import Submission.Work.NormalComplement.p3Normal_of_chIIFourP3Subnormal
import Submission.Work.NormalComplement.card_sup_mul_card_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1600000
open Classical
open Submission.Blueprint
open LeanEval.GroupTheory.Defs

namespace Work.NormalComplement.S5K

/-! ## Counting orbits of a fixed-point-free action -/

/-- **A finite group acting on a finite set with trivial stabilisers has order dividing the
cardinality of the set.**  Every orbit has `Nat.card R` elements. -/
lemma card_dvd_card_of_fixedPointFree {R Y : Type*} [Group R] [Finite R] [MulAction R Y]
    [Finite Y] (hfpf : ∀ u : R, u ≠ 1 → ∀ y : Y, u • y = y → False) :
    Nat.card R ∣ Nat.card Y := by
  classical
  haveI : Fintype R := Fintype.ofFinite _
  haveI : Fintype Y := Fintype.ofFinite _
  haveI : Fintype (MulAction.orbitRel.Quotient R Y) := Fintype.ofFinite _
  have hdecomp : Nat.card Y = ∑ ω : MulAction.orbitRel.Quotient R Y,
      Nat.card ↥(MulAction.orbit R ω.out) := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits R Y)]
    exact Nat.card_sigma
  have horb : ∀ ω : MulAction.orbitRel.Quotient R Y,
      Nat.card ↥(MulAction.orbit R ω.out) = Nat.card R := by
    intro ω
    have hstab : MulAction.stabilizer R ω.out = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro u hu
      by_contra hne
      rw [MulAction.mem_stabilizer_iff] at hu
      exact hfpf u hne ω.out hu
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group R ω.out
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
    rw [hstab, Subgroup.card_bot, mul_one] at h
    exact h
  have hsum : Nat.card Y = Nat.card R * Fintype.card (MulAction.orbitRel.Quotient R Y) := by
    rw [hdecomp, Finset.sum_congr rfl (fun ω _ => horb ω), Finset.sum_const, Finset.card_univ,
      smul_eq_mul, mul_comm]
  exact ⟨_, hsum⟩

/-! ## Formula (∗) and the fixed-point-freeness on `P₁/P` -/

variable {G : Type} [Group G] [Finite G]
variable {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}

/-- **Peterfalvi I Ch. III §4 Prop. 1, step 3: fixed-point-freeness of `C_A(P)` on `P₁/P`.**
Let `h : Setup45A G H t W p P A` with `P` a `p`-Sylow of `twoPoint H t`, let
`u ∈ C_A(P) = A ⊓ C_G(P)` with `u ≠ 1`, and let `Q` be a `p`-subgroup of `H ⊓ N_G(⟨u⟩)`
containing `P`.  Then `Q = P`.

This is the group-theoretic content of `C_H(U) ∩ P₁ = P` for `1 ≠ U ≤ R`: it says that every
`p`-element of `H` centralising `u` lies in `P`.  The proof uses formula (∗) in the form
`H ⊓ N_G(U) = S ⊔ M` with `S` a `2`-group and `M = twoPoint H t ⊓ N_G(U)`
(`P3NormalProp`), `S ⊓ M = ⊥`, and `M ≤ N_G(S)`; since `P` is a Sylow `p`-subgroup of
`twoPoint H t` and `P ≤ M ≤ twoPoint H t`, one has `Nat.card ↥M = p * d` with `p ∤ d`, so
`Nat.card ↥(S ⊔ M) = 2 ^ a * p * d` and any `p`-subgroup of it containing `P` is `P`. -/
theorem fpf_on_P1modP (hFT : Submission.Blueprint.FeitThompsonProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A)
    (hPsyl : Work.NormalComplement.IsSylowIn p P (Submission.Blueprint.twoPoint H t))
    {u : G} (hu : u ∈ A ⊓ Subgroup.centralizer (P : Set G)) (hu1 : u ≠ 1)
    {Q : Subgroup G}
    (hQle : Q ≤ H ⊓ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G))
    (hQp : IsPGroup p Q) (hPQ : P ≤ Q) : Q = P := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  set U : Subgroup G := Subgroup.zpowers u with hU
  have hUne : U ≠ ⊥ := by
    rw [hU]
    intro hb
    exact hu1 (Subgroup.zpowers_eq_bot.mp hb)
  have hUA : U ≤ A ⊓ Subgroup.centralizer (P : Set G) := by
    rw [hU]; exact Subgroup.zpowers_le.mpr hu
  have hUleV : U ≤ centD H t := (hUA.trans inf_le_left).trans h.A_le
  have hPU : P ≤ Subgroup.centralizer (U : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hUA.trans inf_le_right hx) q hq).symm
  -- an element `k ∈ C_K(A)`, `k ≠ 1`
  have hk : ∃ k ∈ Design.CK H t A, k ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hsub : Design.CK H t A ⊆ ({1} : Set G) := fun x hx => by simpa using hcon x hx
    have hle : (Design.CK H t A).ncard ≤ 1 := by
      have h2 := Set.ncard_le_ncard hsub (Set.finite_singleton (1 : G))
      simpa using h2
    rw [h.A_CK] at hle
    have hpow : 4 ≤ 2 ^ p := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) h.prime.two_le
    omega
  obtain ⟨k, hkCK, hk1⟩ := hk
  have hkNU : k ∈ Subgroup.normalizer (U : Set G) := by
    have h1 : k ∈ Subgroup.centralizer (U : Set G) :=
      Subgroup.centralizer_le (fun x hx => (hUA.trans inf_le_left) hx) hkCK.2
    exact Subgroup.centralizer_le_normalizer (U : Set G) h1
  -- formula (∗) with `X = Y = U`
  obtain ⟨-, S, hSp, _hSF, _hSH, hSN, hSD, hSsup⟩ :=
    (p3Normal_of_chIIFourP3Subnormal hP3) G h.sit H h.se t h.invol h.notMem
      U U hUleV hUne le_rfl (show U ≤ Subgroup.normalizer (U : Set G) from Subgroup.le_normalizer) ⟨k, hkCK.1, hk1, hkNU⟩
  set M : Subgroup G := twoPoint H t ⊓ Subgroup.normalizer (U : Set G) with hM
  have hQle' : Q ≤ S ⊔ M := hSsup.symm ▸ hQle
  -- `P ≤ M`
  have hPleM : P ≤ M := le_inf (h.P_le.trans (inf_le_right.trans inf_le_left))
    (hPU.trans (Subgroup.centralizer_le_normalizer (U : Set G)))
  have hMleD : M ≤ twoPoint H t := inf_le_left
  -- `P` is still a Sylow `p`-subgroup of `M`
  have hnotdvd : ¬ p ∣ P.relIndex M := by
    have hpD : ¬ p ∣ P.relIndex (twoPoint H t) := hPsyl.2.2
    have h1 : P.relIndex M * M.relIndex (twoPoint H t) = P.relIndex (twoPoint H t) :=
      Subgroup.relIndex_mul_relIndex P M (twoPoint H t) hPleM hMleD
    intro hd
    exact hpD (h1 ▸ dvd_mul_of_dvd_left hd _)
  have hMcard : Nat.card ↥M = p * P.relIndex M := by
    rw [← Work.NormalComplement.relIndex_mul_card_of_le' hPleM, h.P_card, mul_comm]
  -- `S ⊓ M = ⊥` and `|S ⊔ M| = |S| * |M|`
  have hSMdisj : S ⊓ M = ⊥ := by
    have hle : S ⊓ M ≤ S ⊓ twoPoint H t :=
      le_inf inf_le_left (inf_le_right.trans inf_le_left)
    rw [hSD] at hle
    exact le_antisymm hle bot_le
  have hMN : M ≤ Subgroup.normalizer (S : Set G) :=
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans hSN
  have hcardSM : Nat.card ↥(S ⊔ M) = Nat.card ↥S * Nat.card ↥M := by
    have h1 := Work.NormalComplement.card_sup_mul_card_inf (H := S) (K := M) hMN
    rw [hSMdisj, Subgroup.card_bot, mul_one] at h1
    exact h1
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2) (G := ↥S)).mp hSp
  have hpodd : p ≠ 2 := by
    intro hp2
    have hodd : Odd p := h.P_card ▸
      Odd.of_dvd_nat (h.se.2.2 t h.notMem)
        (Subgroup.card_dvd_of_le (h.P_le.trans (inf_le_right.trans inf_le_left)))
    rw [hp2] at hodd
    exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr dvd_rfl)) hodd
  have hnot2 : ¬ p ∣ 2 ^ a := by
    intro hd
    have h1 : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow h.prime hd
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h2 | h2
    · exact h.prime.ne_one h2
    · exact hpodd h2
  have hQdvd : Nat.card ↥Q ∣ 2 ^ a * (p * P.relIndex M) := by
    have h1 : Nat.card ↥Q ∣ Nat.card ↥(S ⊔ M) := Subgroup.card_dvd_of_le hQle'
    rwa [hcardSM, ha, hMcard] at h1
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := p) (G := ↥Q)).mp hQp
  have hjle : j ≤ 1 := by
    by_contra hj2
    push_neg at hj2
    have h2' : p ^ 2 ∣ 2 ^ a * (p * P.relIndex M) :=
      (pow_dvd_pow p (by omega : 2 ≤ j)).trans (hj ▸ hQdvd)
    have h2 : p * p ∣ 2 ^ a * (p * P.relIndex M) := by rwa [pow_two] at h2'
    obtain ⟨c, hc⟩ := h2
    have hm : ¬ p ∣ 2 ^ a * P.relIndex M :=
      fun hd => (Nat.Prime.dvd_mul h.prime).mp hd |>.elim hnot2 hnotdvd
    refine hm ⟨c, ?_⟩
    have h4 : (2 ^ a * P.relIndex M) * p = (p * c) * p := by
      have h5 : 2 ^ a * P.relIndex M * p = 2 ^ a * (p * P.relIndex M) := by ring
      rw [h5, hc]; ring
    exact Nat.mul_right_cancel h.prime.pos h4
  have hge : 1 ≤ j := by
    have h1 : p ≤ p ^ j := by
      have h2 : Nat.card ↥P ≤ Nat.card ↥Q := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hPQ)
      rwa [hj, h.P_card] at h2
    by_contra hcon
    push_neg at hcon
    have h3 : j = 0 := by omega
    rw [h3, pow_zero] at h1
    have := h.prime.two_le
    omega
  have hQcard : Nat.card ↥Q = p := by rw [hj, show j = 1 from by omega, pow_one]
  exact (Subgroup.eq_of_le_of_card_ge hPQ (le_of_eq (by rw [hQcard, h.P_card]))).symm

end Work.NormalComplement.S5K
