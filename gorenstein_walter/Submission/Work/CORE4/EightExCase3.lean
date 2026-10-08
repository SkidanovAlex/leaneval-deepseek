/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4)

# Case 3 of the §4 (8) trichotomy — report of the prover

This file records the analysis of the requested leaf `Work.CORE4.EightExCase3` and one verified
piece of it (the reduction `invSet_commute_of_inverts`).  **The requested statement, as written,
is not derivable from its hypotheses** — see the detailed report at the end of this header and in
`EightExCase3_finding` below.  The statement itself is left untouched.

## What the statement asks

    Case2InvNormal B C.D  =  ∃ I : Subgroup G, (I : Set G) = invSet B.U D.s ∧
                                            I ≤ B.Hhat ∧ (I.subgroupOf B.Hhat).Normal

with `invSet B.U D.s = {x ∈ B.U | s x s⁻¹ = x⁻¹}`, `s = D.s`.  So the statement demands that the
*set* `I_U(s) = invSet B.U D.s` be the underlying set of a subgroup of `G`, contained in `Ĥ` and
normal in `Ĥ`; in particular `I_U(s)` must be closed under multiplication.

## Why the hypothesis list does not deliver this

* The design's justification is a misreading.  `Submission/Work/_design_gw/Core9.lean` (copied
  verbatim into `CORE4/Defs.lean` §9) writes, immediately above `Case2InvNormal`:
  *"Bender's exceptional clause in (8): `I_U(s) ⊲ Ĥ`.  By Coprime15 (`I.toolkit.c15`), `I_U(s)`
  is a subgroup."*  But `Work.GW2.Coprime15Prop` (`Submission/Work/ASM/Defs.lean` §4) ends with
  the **conditional** statement
  `∀ I : Subgroup G, (I : Set G) = invSet X s → IsMulCommutative I ∧ (I.subgroupOf X).Normal ∧
  I ≤ fittingIn X`
  (see also `Work.COPR.coprime15_sub`): it says what an inversion subgroup is *provided it exists*
  — it never produces one.  So no Coprime15 clause supplies this leaf's `I`.  (The design lead
  also flagged the case-3 argument as not re-derived: `NOTES_LEAD_gw_design9.md`, "Not verified".)
* The two hypotheses about `Q := Qsub p B` that the statement supplies — `¬ IsCyclic Q` and
  `s` inverts every element of `Q` — do **not** make `I_U(s)` closed, even together with the
  group-theoretic facts about `Q` that this area has verified (see the probe
  `CORE4/_eec2_probe.lean`: `Q ≤ O_p(U)`, `O_p(U) ≤ U`, `U ≤ N_G(O_p(U))`, `U ≤ N_G(Q)`,
  `[Q, O_p(U)] ≤ Z(Q)`).  Counterexample: let `p = 3`, let `Q₀ = C_3 × C_3`, let
  `R = ⟨a,b | a^5 = b^5 = 1, [a,b] = z central of order 5⟩` be the extraspecial group of order
  `5³` and exponent `5`, put `U := Q₀ × R`, and let `s` be the automorphism of `U` of order two
  inverting `Q₀`, inverting `a,b` and fixing `z`.  Then `U` has odd order,
  `O_3(U) = Q₀`, `Z₂(Q₀) = Q₀` (abelian) and `Ω₁(Q₀) = Q₀`, so
  `Qsub 3 B = Q₀` is non-cyclic and inverted by `s`, yet
  `I_U(s) = Q₀ × I_R(σ_R)` where `σ_R` is the restriction to `R`, and with
  `I_R(σ_R) = {a^i b^j z^k | 2k + ij ≡ 0 mod 5}` (order `5²`) this set is not closed:
  `(a^i b^j z^k)(a^{i'} b^{j'} z^{k'})` has the right form only if `i'j ≡ ij' (mod 5)`, which is
  false for `i = j' = 1`, `i' = j = 0`.  (Equivalently: the projection of the subgroup generated
  by `I_U(s)` onto `R` is strictly larger than `I_R(σ_R)`.)  Hence the *only* hypotheses of the
  statement that mention `I_U(s)`'s closure data cannot suffice.
* What the hypotheses *do* give is the following verified reduction (`invSet_commute_of_inverts`):
  every `x ∈ I_U(s)` centralizes `Q`, i.e. `I_U(s) ⊆ C_U(Q)`, whence `I_U(s) = I_{C_U(Q)}(s)`.
  Consequently the statement is *equivalent* to `C_U(Q) ∩ C_U(s) = ⊥` (equivalently, by Bender
  1.5 / `Work.BMAX.InvolutionInverts`, to `C_U(Q) ⊆ I_U(s)`), i.e. to Bender's case-3 assertion
  "`s` inverts `C_U(Q)`".  Bender justifies that assertion on p. 226 by
  "`Q ⊄ M` implies `C_U(Q) ∩ F = 1`", i.e. it uses §4's (5) `C_U(s) = B₀` — a fact about the
  actual configuration (derived from the structure of `E(M) ≅ A₇` or `L₂(q)`) that is **not**
  among this leaf's hypotheses: `Case2Ctx6` gives only §4 (1)–(6), and it constrains `C_U(s)`
  only *inside* `M` (`B₀ = (B.U ⊓ D.M) ⊓ C_G(s)`), nothing outside.  In this very area the
  analogous non-derivable facts had to be isolated as explicit hypotheses
  (`CORE4/Case2PrePlusOfCentralizer.lean`, `CORE4/Case2PrePlusOfCommutator.lean`).

## Suggested restatement (the leaf becomes provable)

Add the missing group-theoretic input to the hypothesis list, e.g.

    (hCl : ∀ y ∈ B.U ⊓ Subgroup.centralizer (Work.CORE4.Qsub p B : Set G),
             C.D.s * y * C.D.s⁻¹ = y⁻¹)              -- "s inverts C_U(Q)"

(or `hC1 : ∀ y ∈ C_U(Q), D.s * y * D.s⁻¹ = y⁻¹`, equivalently `C_U(Q) ⊓ C_U(s) = ⊥`).  With it,
`invSet_commute_of_inverts` (below) gives `I_U(s) = C_U(Q)`, and `I := C_U(Q)` is a subgroup with
`(I : Set G) = invSet B.U D.s`, `I ≤ B.U ≤ B.Hhat` and `(I.subgroupOf B.Hhat).Normal` (as `Q` is
characteristic in `U ⊴ Ĥ`).  Alternatively, replace the conclusion by Bender's printed (8), a
disjunction `Case2InvNormal B C.D ∨ (Case2EightU B A ≤ p ∧ A ⊴ F(U) ∧ …)`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.Case2CountSetup

namespace Work.CORE4

open Work.GW2 Subgroup

/-- **The reduction of the case-3 leaf (verified).**  If an involution `s` inverts every element
of a subgroup `Q ≤ U` of odd order that is normal in `U`, then every element of
`I_U(s) = invSet U s` centralizes `Q`.

Route: for `x ∈ I_U(s)` and `q ∈ Q`, `x` normalizes `Q`, so `x q x⁻¹ ∈ Q` and
`s (x q x⁻¹) s⁻¹` may be computed in two ways:
`s x q x⁻¹ s⁻¹ = (s x s⁻¹)(s q s⁻¹)(s x⁻¹ s⁻¹) = x⁻¹ q⁻¹ x` and `= (x q x⁻¹)⁻¹ = x q⁻¹ x⁻¹`.
Hence `x⁻¹ q⁻¹ x = x q⁻¹ x⁻¹`, i.e. `x² q x⁻² = q`: `x²` centralizes `Q`.  Since `orderOf x` is
odd (it divides `|U|`) and `x` is therefore a power of `x²` (`⟨x²⟩ = ⟨x⟩` by the order formula),
`x` itself centralizes `Q`. -/
theorem invSet_commute_of_inverts {G : Type} [Group G] [Finite G] {U Q : Subgroup G} {s x : G}
    (hodd : Odd (Nat.card U)) (hQU : Q ≤ U) (hQn : (Q.subgroupOf U).Normal)
    (hinv : ∀ q ∈ Q, s * q * s⁻¹ = q⁻¹)
    (hxU : x ∈ U) (hx : x ∈ Work.GW2.invSet U s) :
    ∀ q ∈ Q, x * q = q * x := by
  have hUleN : U ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQU).mp hQn
  have hsx : s * x * s⁻¹ = x⁻¹ := hx.2
  have hsx' : s * x⁻¹ * s⁻¹ = x := by
    have h : (s * x * s⁻¹)⁻¹ = s * x⁻¹ * s⁻¹ := by group
    rw [hsx, inv_inv] at h
    exact h.symm
  intro q hq
  have hxq : x * q * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hUleN hxU) q).mp hq
  -- the two computations of `s * (x q x⁻¹) * s⁻¹`
  have hkey : x⁻¹ * q⁻¹ * x = x * q⁻¹ * x⁻¹ := by
    have h1 : s * (x * q * x⁻¹) * s⁻¹ = (x * q * x⁻¹)⁻¹ := hinv _ hxq
    have h2 : s * (x * q * x⁻¹) * s⁻¹ = x⁻¹ * q⁻¹ * x := by
      rw [show s * (x * q * x⁻¹) * s⁻¹
            = (s * x * s⁻¹) * (s * q * s⁻¹) * (s * x⁻¹ * s⁻¹) by group,
          hsx, hinv q hq, hsx']
    rw [h1] at h2
    rw [← h2]
    group
  -- `x²` commutes with `q`
  have hcomm : Commute q (x * x) := by
    have h3 : q⁻¹ * (x * x) = (x * x) * q⁻¹ :=
      calc q⁻¹ * (x * x) = x * (x⁻¹ * q⁻¹ * x) * x := by group
        _ = x * (x * q⁻¹ * x⁻¹) * x := by rw [hkey]
        _ = (x * x) * q⁻¹ := by group
    have h4 : Commute q⁻¹ (x * x) := h3
    simpa using h4.inv_left
  -- `orderOf x` is odd, so `⟨x⟩ = ⟨x²⟩` and `x` is a power of `x²`
  have hoddx : Odd (orderOf x) :=
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard U hxU)
  have hmem : x ∈ Subgroup.zpowers (x * x) := by
    have hcard : Nat.card ↥(Subgroup.zpowers (x * x)) = Nat.card ↥(Subgroup.zpowers x) := by
      rw [Nat.card_zpowers, Nat.card_zpowers,
        show x * x = x ^ 2 by rw [pow_two], orderOf_pow]
      have hg : (orderOf x).gcd 2 = 1 := by
        rw [Nat.gcd_comm]
        exact (Nat.coprime_two_left.mpr hoddx).gcd_eq_one
      rw [hg, Nat.div_one]
    have hle : Subgroup.zpowers (x * x) ≤ Subgroup.zpowers x :=
      Subgroup.zpowers_le.mpr (Subgroup.mul_mem _ (Subgroup.mem_zpowers x) (Subgroup.mem_zpowers x))
    have heq : Subgroup.zpowers (x * x) = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
    rw [heq]
    exact Subgroup.mem_zpowers x
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [← hk]
  exact (hcomm.zpow_right k).eq.symm

/-- **Finding (for the requester).**  The statement of `EightExCase3` is not derivable from the
hypotheses it names; see the module header for the full report: the design's justification
(`Core9.lean`: "By Coprime15, `I_U(s)` is a subgroup") is a misreading of `Coprime15Prop`, whose
third conjunct is conditioned on the existence of that subgroup, and the two hypotheses about
`Qsub p B` (non-cyclicity and inversion by `s`) do not imply that `invSet B.U D.s` is closed —
a counterexample is given in the header.  The verified reduction `invSet_commute_of_inverts`
shows that the leaf is equivalent to the missing assertion `C_U(Qsub p B) ⊓ C_U(D.s) = ⊥`. -/
def EightExCase3_finding : Prop := True

/-- Bender 1981, §4 (8), case 3 of the `Q := Ω₁(Z₂(O_p(U)))` trichotomy: if `s` inverts every element of the non-cyclic `Q` (so that `Q ⊄ M`), then `I_U(s)` is a normal subgroup of `Ĥ`, i.e. `Case2InvNormal B C.D`. -/
theorem EightExCase3 (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case2 B → ∀ C : Work.GW2.Case2Ctx6 B, Work.GW2.Case2PrePlus B C.D →
        Work.GW2.Case2SevenFacts B C.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj C.D p P A →
          ¬ IsCyclic ↥(Work.CORE4.Qsub p B) →
          (∀ x ∈ Work.CORE4.Qsub p B, C.D.s * x * C.D.s⁻¹ = x⁻¹) →
          Work.GW2.Case2InvNormal B C.D := by sorry

end Work.CORE4
