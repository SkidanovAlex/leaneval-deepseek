/-
Copyright (c) 2024. All rights reserved.

# Killing `⟨D, x⟩` when `x² ∈ Ω₁(P)` and `[x, D] ⊆ Ω₁(P)`

`P` a Suzuki 2-group, `D ≤ P` normal with `Ω₁(P) ≤ D`, `D² ⊆ Ω₁(P)`, `[D,D] ⊆ Ω₁(P)` and
`|D| = |Ω₁(P)|³`.  If `x ∉ D` with `x² ∈ Ω₁(P)` and `[x,D] ⊆ Ω₁(P)`, then `M := D ⊔ ⟨x⟩`
satisfies `M² ⊆ Ω₁(P)`, `[M,M] ⊆ Ω₁(P)` and `Ω₁(P) ≤ M`, so
`Work.Higman.H8.card_le_cube_of_sq_le_omega1` gives `|M| ≤ |Ω₁(P)|³`; but `D < M` shows
`|M| > |D| = |Ω₁(P)|³`.  Contradiction.

Mathlib writes `⁅a,b⁆ = a * b * a⁻¹ * b⁻¹`; the identities used are
* `x * d = ⁅x,d⁆ * (d * x)` (pure group identity),
* `(d * x)² = ⁅x,d⁆ * d² * x²` (from the previous one and centrality of `⁅x,d⁆ ∈ Ω₁(P)`),
* `⁅p*q, r⁆ = p * ⁅q,r⁆ * p⁻¹ * ⁅p,r⁆`, `⁅p, q*r⁆ = ⁅p,q⁆ * q * ⁅p,r⁆ * q⁻¹`,
together with `Ω₁(P) ≤ Z(P)` (`IsSuzuki2Grp.omega1_le_center`).
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.H8.cw_cube_bound
import Submission.Work.Higman.H8.mem_sup_zpowers_or

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.style.longLine false

namespace Work.Higman.H8

open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

/-- **`⟨D, x⟩` violates Chevalley–Warning.** -/
theorem false_of_sq_mem_and_comm_le {D : Subgroup P}
    (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hNA : Work.Higman.omega1 P ≤ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hAD : A ≤ D) (hDn : D.Normal)
    (hD2 : Work.Higman.powSub D 2 ≤ Work.Higman.omega1 P)
    (hDd : ∀ a ∈ D, ∀ b ∈ D, a * b * a⁻¹ * b⁻¹ ∈ Work.Higman.omega1 P)
    (hDcard : Nat.card ↥D = (Nat.card ↥(Work.Higman.omega1 P)) ^ 3)
    {x : P} (hxD : x ∉ D) (hx2O : x ^ 2 ∈ Work.Higman.omega1 P)
    (hxcomm : ∀ d ∈ D, x * d * x⁻¹ * d⁻¹ ∈ Work.Higman.omega1 P) :
    False := by
  classical
  haveI : D.Normal := hDn
  have hO : Work.Higman.omega1 P ≤ Subgroup.center P := h.omega1_le_center
  have hxxO : x * x ∈ Work.Higman.omega1 P := by rw [← pow_two]; exact hx2O
  have hx2D : x * x ∈ D := hAD (hNA hxxO)
  -- raw commutators written as brackets
  have h_DD : ∀ a ∈ D, ∀ b ∈ D, ⁅a, b⁆ ∈ Work.Higman.omega1 P := by
    intro a ha b hb
    rw [commutatorElement_def]
    exact hDd a ha b hb
  have h_Dx : ∀ a ∈ D, ⁅a, x⁆ ∈ Work.Higman.omega1 P := by
    intro a ha
    rw [commutatorElement_def]
    have h1 : a * x * a⁻¹ * x⁻¹ = (x * a * x⁻¹ * a⁻¹)⁻¹ := by group
    rw [h1]
    exact Subgroup.inv_mem _ (hxcomm a ha)
  have h_xD : ∀ b ∈ D, ⁅x, b⁆ ∈ Work.Higman.omega1 P := by
    intro b hb
    rw [commutatorElement_def]
    exact hxcomm b hb
  -- elements of `Ω₁(P)` are fixed by conjugation
  have hfix : ∀ c ∈ Work.Higman.omega1 P, ∀ g : P, g⁻¹ * c * g = c := by
    intro c hc g
    have hcc : c ∈ Subgroup.center P := hO hc
    rw [show g⁻¹ * c * g = g⁻¹ * (c * g) by group,
      (Subgroup.mem_center_iff.mp hcc g).symm]
    group
  have hconj : ∀ c ∈ Work.Higman.omega1 P, ∀ g : P, g * c * g⁻¹ ∈ Work.Higman.omega1 P := by
    intro c hc g
    have h1 : g * c * g⁻¹ = (g⁻¹)⁻¹ * c * (g⁻¹) := by group
    rw [h1, hfix c hc g⁻¹]
    exact hc
  -- square of `d * x`
  have hdxsq : ∀ d ∈ D, (d * x) * (d * x) = (x * d * x⁻¹ * d⁻¹) * (d * d) * (x * x) := by
    intro d hd
    have hc : x * d * x⁻¹ * d⁻¹ ∈ Work.Higman.omega1 P := hxcomm d hd
    have hcc : x * d * x⁻¹ * d⁻¹ ∈ Subgroup.center P := hO hc
    have hcm : d * (x * d * x⁻¹ * d⁻¹) = (x * d * x⁻¹ * d⁻¹) * d :=
      Subgroup.mem_center_iff.mp hcc d
    have hxd : x * d = (x * d * x⁻¹ * d⁻¹) * (d * x) := by group
    calc (d * x) * (d * x) = d * (x * d) * x := by group
      _ = d * ((x * d * x⁻¹ * d⁻¹) * (d * x)) * x := by nth_rewrite 1 [hxd]; rfl
      _ = (x * d * x⁻¹ * d⁻¹) * (d * d) * (x * x) := by
            have e1 : d * ((x * d * x⁻¹ * d⁻¹) * (d * x)) * x
                = (d * (x * d * x⁻¹ * d⁻¹)) * d * x * x := by group
            have e2 : (d * (x * d * x⁻¹ * d⁻¹)) * d * x * x
                = (x * d * x⁻¹ * d⁻¹) * (d * d) * (x * x) := by
              rw [hcm]
              group
            exact e1.trans e2
  let M : Subgroup P := D ⊔ Subgroup.zpowers x
  have hDM : D ≤ M := le_sup_left
  have hxM : x ∈ M := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hZM : Work.Higman.omega1 P ≤ M := (hNA.trans hAD).trans hDM
  -- `M² ⊆ Ω₁(P)`
  have hM2 : Work.Higman.powSub M 2 ≤ Work.Higman.omega1 P := by
    rw [Work.Higman.powSub, Subgroup.closure_le]
    rintro y ⟨a, ha, rfl⟩
    rcases mem_sup_zpowers_or hDn hx2D a ha with had | ⟨d, hd, rfl⟩
    · exact hD2 (Work.Higman.pow_mem_powSub had)
    · rw [pow_two, hdxsq d hd]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hxcomm d hd)
        (by simpa [pow_two] using hD2 (Work.Higman.pow_mem_powSub (n := 2) hd))) hxxO
  -- `[M,M] ⊆ Ω₁(P)`
  have hMd : ⁅M, M⁆ ≤ Work.Higman.omega1 P := by
    have hid1 : ∀ p q r : P, ⁅p * q, r⁆ = p * ⁅q, r⁆ * p⁻¹ * ⁅p, r⁆ := by
      intro p q r; rw [commutatorElement_def]; group
    have hid2 : ∀ p q r : P, ⁅p, q * r⁆ = ⁅p, q⁆ * q * ⁅p, r⁆ * q⁻¹ := by
      intro p q r; rw [commutatorElement_def]; group
    have hstep2 : ∀ p q r : P, ⁅p, q⁆ ∈ Work.Higman.omega1 P →
        ⁅p, r⁆ ∈ Work.Higman.omega1 P → ⁅p, q * r⁆ ∈ Work.Higman.omega1 P := by
      intro p q r h1 h3
      have hcm : ⁅p, q⁆ * q = q * ⁅p, q⁆ := (Subgroup.mem_center_iff.mp (hO h1) q).symm
      rw [hid2 p q r,
        show ⁅p, q⁆ * q * ⁅p, r⁆ * q⁻¹ = q * (⁅p, q⁆ * ⁅p, r⁆) * q⁻¹ by rw [hcm]; group]
      exact hconj _ (Subgroup.mul_mem _ h1 h3) q
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rcases mem_sup_zpowers_or hDn hx2D a ha with haD | ⟨d, hd, rfl⟩
    · rcases mem_sup_zpowers_or hDn hx2D b hb with hbD | ⟨e, he, rfl⟩
      · exact h_DD a haD b hbD
      · exact hstep2 a e x (h_DD a haD e he) (h_Dx a haD)
    · rcases mem_sup_zpowers_or hDn hx2D b hb with hbD | ⟨e, he, rfl⟩
      · rw [hid1 d x b]
        exact Subgroup.mul_mem _ (hconj _ (h_xD b hbD) d) (h_DD d hd b hbD)
      · rw [hid1 d x (e * x)]
        have h20 : ⁅d, e * x⁆ ∈ Work.Higman.omega1 P :=
          hstep2 d e x (h_DD d hd e he) (h_Dx d hd)
        have h21 : ⁅x, e * x⁆ ∈ Work.Higman.omega1 P := by
          refine hstep2 x e x (h_xD e he) ?_
          rw [show ⁅x, x⁆ = 1 by rw [commutatorElement_def]; group]
          exact (Work.Higman.omega1 P).one_mem
        exact Subgroup.mul_mem _ (hconj _ h21 d) h20
  -- Chevalley--Warning versus `|D| = q³ < |M|`
  have hCW : Nat.card ↥M ≤ (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 :=
    card_le_cube_of_sq_le_omega1 h hZM hM2 hMd
  have hlt : D < M := lt_of_le_of_ne hDM (fun hEq => hxD (hEq ▸ hxM))
  have hcardlt : Nat.card ↥D < Nat.card ↥M := by
    haveI : Fintype ↥D := Fintype.ofFinite _
    haveI : Fintype ↥M := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    refine Fintype.card_lt_of_injective_not_surjective (Subgroup.inclusion hDM)
      (Subgroup.inclusion_injective hDM) ?_
    intro hsurj
    obtain ⟨y, hy⟩ := hsurj ⟨x, hxM⟩
    have hy' : (y : P) = x := congrArg (fun t : ↥M => (t : P)) hy
    exact hxD (hy' ▸ y.2)
  omega

end Work.Higman.H8
