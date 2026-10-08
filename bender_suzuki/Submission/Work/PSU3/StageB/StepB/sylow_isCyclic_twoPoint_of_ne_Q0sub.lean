import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageA.caseC_W_semireg
import Submission.Work.PSU3.StageA.coarseFrame_defs
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ThmF.ChV12.conj_action_data
import Submission.Work.ThmF.ChV12.prop1c
import Submission.Work.ThmF.Prove.S3.fpf_isCyclic
import Submission.Work.ZassenhausSuzuki.exists_conjAction
import Submission.Work.PSU3.StageB.StepB.exists_fpf_action_quotient
import Submission.Work.Frobenius.Complement.sylow_isCyclic_of_odd
import Submission.Work.Frobenius.Complement.isPGroup_abelian_fpf_isCyclic
import Submission.Work.Frobenius.Complement.isPGroup_isCyclic_of_no_basicGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `D = twoPoint H t` has cyclic Sylow subgroups once `Q₀ ≠ Q` (Peterfalvi II, Ch. VII §2)

This module holds the part of

  `Work.PSU3.StageB.StepB.sylow_isCyclic_twoPoint_of_fpf`

that *is* provable from `PSU3Hyp`-type hypotheses as stated, namely the **corrected** statement
`Work.PSU3.StageB.StepB.sylow_isCyclic_twoPoint_of_ne_Q0sub`, which carries the extra hypothesis
`¬ Q ≤ Q0sub H` (Peterfalvi's cases (b)/(c) of Ch. VI §1 rather than case (a)).

The intended argument (Peterfalvi II, Ch. VII §2, Prop. p. 274; design node `P4`) is:

* `D = twoPoint H t` has odd order (`Work.ThmF.split_odd_card_twoPoint`);
* `DFpfBar H Q t` says that `D` acts fixed-point-freely on `(Q/Q₀)^#`, `Q₀ = Q0sub H = ⟨Inv H⟩`,
  so it acts fixed-point-freely on the group `Q/(Q₀ ⊓ Q)`;
* by `¬ Q ≤ Q0sub H` that group is nontrivial, so `D` is the complement of a Frobenius group with
  nontrivial kernel: its odd Sylow subgroups are cyclic (FT 3.16 (ii)) and the Sylow `2`-subgroup
  is trivial.

The gap in the statement without `¬ Q ≤ Q0sub H` is discussed in the sibling file
`Submission/Work/PSU3/StageB/StepB/sylow_isCyclic_twoPoint_of_fpf.lean`: `DFpfBar` is vacuous
when `Q ≤ Q0sub H`, and excluding that case is Peterfalvi's *Réduction* (Ch. VI §3), which in
this workspace needs `ChIIFourProp` plus `FeitThompsonProp` applied to the odd-order group `D`
(see `Work.PSU3.StageA.not_caseA_of_solvable`, `Work.ThmF.ChV12.L5prop2_caseWbot`).

Also recorded here, and used below:

* `involution_mem_centerOf_of_split` — every involution of `Q` is central in `Q`
  (Peterfalvi II Ch. V §1 Prop. 1 (c) *without* `ChIIFourProp`: `D` is transitive on
  `Inv H = Inv Q`, and automorphisms preserve centrality);
* `Q0sub_le_centerOf_of_split` — consequently `Q₀ ≤ Z(Q)`.

Nothing here is used by the (still open) statement itself.
-/

namespace Work.PSU3.StageB.StepB

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- **Frobenius complements of odd order have cyclic odd Sylow subgroups** (FT 3.16 (ii)).
If a finite group `A` acts on a nontrivial finite group `E` by automorphisms, fixed-point-freely,
and `(|A|, |E|) = 1`, then every `ℓ`-subgroup of `A` for an odd prime `ℓ` is cyclic. -/
theorem isPGroup_isCyclic_of_fpf_mulAut {A E : Type*} [Group A] [Finite A] [Group E] [Finite E]
    [Nontrivial E] (ρ : A →* MulAut E) (hcop : (Nat.card A).Coprime (Nat.card E))
    (hfpf : ∀ a : A, a ≠ 1 → ∀ e : E, ρ a e = e → e = 1)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {L : Subgroup A} (hL : IsPGroup ℓ L) :
    IsCyclic ↥L := by
  letI : MulDistribMulAction A E :=
    { smul := fun a e => ρ a e
      one_smul := fun e => by show ρ 1 e = e; rw [map_one]; rfl
      mul_smul := fun a b e => by show ρ (a * b) e = ρ a (ρ b e); rw [map_mul]; rfl
      smul_one := fun a => by show ρ a 1 = 1; rw [map_one]
      smul_mul := fun a x y => by
        show ρ a (x * y) = ρ a x * ρ a y
        rw [map_mul] }
  exact Work.ThmF.Prove.S3.fpf_isCyclic hcop (fun a ha e he => hfpf a ha e he) hℓ hℓ2 hL

/-- **Every involution of `Q` is central in `Q`** (Peterfalvi II Ch. V §1 Prop. 1 (c)).

The proof here needs no case hypothesis: `D = twoPoint H t` is transitive on
`Inv H = Inv Q` (Peterfalvi I Ch. I §2 Prop. 2 (b), `Work.ThmF.Bender.DTransitiveInv`), and
automorphisms preserve centrality, so every involution of `Q` is conjugate under `D` to a
*central* involution of the nontrivial `2`-group `Q`. -/
theorem involution_mem_centerOf_of_split (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (h2 : IsPGroup 2 Q) :
    ∀ u ∈ involutions (Q : Set G), u ∈ Work.ThmF.centerOf Q := by
  have hoddD : Odd (Nat.card ↥(twoPoint H t)) := Work.ThmF.split_odd_card_twoPoint hsplit
  -- `Q` has even order, so its centre contains an involution
  have hQeven : Even (Nat.card ↥Q) := by
    have h1 : Even (Nat.card ↥Q * Nat.card ↥(twoPoint H t)) := by
      rw [← Work.ThmF.split_card_H hsplit]
      exact Work.ThmF.split_even_card_H hsplit
    rw [Nat.even_mul] at h1
    exact h1.resolve_right (Nat.not_even_iff_odd.mpr hoddD)
  obtain ⟨z, hzQ, hz2, hzcent⟩ :=
    Work.ThmF.ChV12.exists_involution_mem_centerOf Q h2.isNilpotent hQeven
  -- the involutions of `H` are exactly those of `Q`
  have hInv : involutions (H : Set G) = involutions (Q : Set G) := by
    ext u
    exact ⟨fun hu => ⟨Work.PSU3.StageA.inv_mem_Q hsplit u hu, hu.2⟩,
      fun hu => ⟨hsplit.le hu.1, hu.2⟩⟩
  -- `D` is transitive on `Inv Q`
  have htrans : ∀ a ∈ involutions (Q : Set G), ∃ d ∈ twoPoint H t, d * a * d⁻¹ = z := by
    intro a ha
    exact Work.ThmF.Bender.DTransitiveInv hsplit.stronglyEmbedded hsplit.invol hsplit.not_mem
      a (by rw [hInv]; exact ha) z (by rw [hInv]; exact ⟨hzQ, hz2⟩)
  intro u hu
  obtain ⟨d, hdD, hd⟩ := htrans u hu
  have hdH : d ∈ H := (Subgroup.mem_inf.mp hdD).1
  have hdq : ∀ q ∈ Q, d * q * d⁻¹ ∈ Q := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp (hsplit.normal hdH) q).mp hq
  have hu_eq : u = d⁻¹ * z * d := by rw [← hd]; group
  refine (Work.ThmF.mem_centerOf (Q := Q)).mpr ⟨hu.1, fun q hq => ?_⟩
  calc u * q = d⁻¹ * z * d * q := by rw [hu_eq]
    _ = d⁻¹ * (z * (d * q * d⁻¹)) * d := by group
    _ = d⁻¹ * ((d * q * d⁻¹) * z) * d := by rw [hzcent (d * q * d⁻¹) (hdq q hq)]
    _ = q * u := by rw [hu_eq]; group

/-- `Q₀ = ⟨Inv H⟩ ≤ Z(Q)`: the involutions of `H` are central in `Q`. -/
theorem Q0sub_le_centerOf_of_split (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (h2 : IsPGroup 2 Q) : Work.ThmF.Q0sub H ≤ Work.ThmF.centerOf Q := by
  have hcent := involution_mem_centerOf_of_split (H := H) (Q := Q) hsplit h2
  rw [Work.ThmF.Q0sub]
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  rcases Work.ThmF.mem_Q0_iff.mp hx with ⟨hxH, hx2⟩ | rfl
  · exact hcent x ⟨Work.PSU3.StageA.inv_mem_Q hsplit x ⟨hxH, hx2⟩, hx2⟩
  · exact (Work.ThmF.centerOf Q).one_mem

/-- **The corrected statement.**  With the extra hypothesis `¬ Q ≤ Q0sub H` (i.e. `Q ≠ Q0sub H`,
Peterfalvi's cases (b)/(c) rather than case (a) of Ch. VI §1), `DFpfBar` makes `D = twoPoint H t`
act fixed-point-freely on the *nontrivial* group `Q/Q₀`, so `D` is a Frobenius complement of odd
order and all its Sylow subgroups are cyclic. -/
theorem sylow_isCyclic_twoPoint_of_ne_Q0sub (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (h2 : IsPGroup 2 Q) (hfpf : Work.PSU3.DFpfBar H Q t) (hne : ¬ Q ≤ Work.ThmF.Q0sub H)
    (p : ℕ) (hp : p.Prime) (P : Sylow p ↥(twoPoint H t)) : IsCyclic ↥P := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hoddD : Odd (Nat.card ↥(twoPoint H t)) := Work.ThmF.split_odd_card_twoPoint hsplit
  -- `Q₀ ∩ Q` is normal in `Q`
  have hQ0norm : Q ≤ Subgroup.normalizer (Work.ThmF.Q0sub H : Set G) :=
    hsplit.le.trans (Work.ThmF.ChV12.H_le_normalizer_Q0sub H)
  haveI hK : ((Work.ThmF.Q0sub H).subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Work.PSU3.StageA.Q0sub_le_Q hsplit)).mpr
      hQ0norm
  -- the quotient `Q/Q₀` is nontrivial and of `2`-power order
  haveI hnt : Nontrivial (↥Q ⧸ (Work.ThmF.Q0sub H).subgroupOf Q) := by
    by_contra htriv
    rw [not_nontrivial_iff_subsingleton] at htriv
    refine hne fun x hx => ?_
    have h1 : QuotientGroup.mk' ((Work.ThmF.Q0sub H).subgroupOf Q) (⟨x, hx⟩ : ↥Q) = 1 :=
      Subsingleton.elim _ _
    have h2 : (⟨x, hx⟩ : ↥Q) ∈ (Work.ThmF.Q0sub H).subgroupOf Q := by
      have hmem : (⟨x, hx⟩ : ↥Q) ∈
          (QuotientGroup.mk' ((Work.ThmF.Q0sub H).subgroupOf Q)).ker :=
        MonoidHom.mem_ker.mpr h1
      rwa [QuotientGroup.ker_mk'] at hmem
    rwa [Subgroup.mem_subgroupOf] at h2
  have hcop : (Nat.card ↥(twoPoint H t)).Coprime
      (Nat.card (↥Q ⧸ (Work.ThmF.Q0sub H).subgroupOf Q)) := by
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    have hdvd : Nat.card (↥Q ⧸ (Work.ThmF.Q0sub H).subgroupOf Q) ∣ 2 ^ k := by
      rw [← hk]
      exact Subgroup.card_quotient_dvd_card _
    exact (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hoddD)).coprime_dvd_right hdvd
  obtain ⟨ρ, hfpfρ⟩ := Work.PSU3.StageB.StepB.exists_fpf_action_quotient hsplit hfpf
  by_cases hp2 : p = 2
  · subst hp2
    -- a Sylow `2`-subgroup of the odd-order group `D` is trivial
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    have hk' : Nat.card ↥P = 2 ^ k := hk
    have hdvd : Nat.card ↥P ∣ Nat.card ↥(twoPoint H t) :=
      Subgroup.card_subgroup_dvd_card (P : Subgroup ↥(twoPoint H t))
    have hk0 : k = 0 := by
      by_contra hk0
      have h2dvd : 2 ∣ Nat.card ↥P := by
        rw [hk']
        exact dvd_pow_self 2 hk0
      exact (Nat.not_even_iff_odd.mpr (hoddD.of_dvd_nat hdvd)) (even_iff_two_dvd.mpr h2dvd)
    have hcard1 : Nat.card ↥P = 1 := by rw [hk', hk0, pow_zero]
    haveI : Subsingleton ↥P := Finite.card_le_one_iff_subsingleton.mp (le_of_eq hcard1)
    exact isCyclic_of_subsingleton
  · have hL : IsPGroup p ↥(P : Subgroup ↥(twoPoint H t)) := P.isPGroup'
    exact isPGroup_isCyclic_of_fpf_mulAut (ℓ := p) ρ hcop hfpfρ hp hp2 hL

end Work.PSU3.StageB.StepB
