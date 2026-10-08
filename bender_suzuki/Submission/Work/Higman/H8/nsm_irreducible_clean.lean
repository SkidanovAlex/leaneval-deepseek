import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.HS.core_mul
import Submission.Work.Higman.MSA.l8_card_le
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.equivariant_bihom_trivial
import Submission.Work.Higman.H8.Clean.NsdCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The irreducible case of the `C₄` exclusion, in clean form

This file reproduces `Work.Higman.NSM.irreducible` (Higman, *Suzuki 2-groups* (1963), Lemma 8
with `C = ⊤`) without importing any of `no_square_derived`, `no_square_of_maximal`,
`H8.c4_exclusion`, `H8.c4_exclusion_sq`.  The supporting development (`aux_*`, `nsd_*`,
`L1_iso_field_exp`, `nsd_core`, ...) is reproduced in `Submission/Work/Higman/H8/Clean/`,
under the namespace `Work.Higman.H8.Clean`, so that it never depends on the modules forbidden
by the non-circularity requirement of the proof of `|P| ≤ |Ω₁(P)|³`.

See `Work.Higman.NSM.irreducible` for the mathematical discussion: the irreducible hypothesis
turns into "every element outside `A` fails to centralise `A`"; the two layers `P ⧸ A` and
`Ω₁(P)` are identified with a common finite field on which `ξ` acts by `lam`, resp. `mu`; and
the eigenvalue bookkeeping of Higman's Lemma 6 (packaged as `nsd_core`) gives a contradiction.
-/

open scoped commutatorElement

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.Higman.H8

open Work.Higman.H8.Clean

/-- The `C₄` exclusion, irreducible case (Higman 1963, Lemma 8 with `C = ⊤`): no Suzuki
2-group has a `ξ`-invariant abelian normal subgroup `A` of exponent `4` with `Ω₁(P) ≤ A`,
`[P,P] = A`, all squares in `A`, `A⁴ = 1`, `A² = Ω₁(P)`, `|A| = |Ω₁(P)|²` and `P ⧸ A`
irreducible as an `𝔽₂[ξ]`-module. -/
theorem nsm_irreducible_clean {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hirr : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D = A ∨ D = ⊤) : False := by
  classical
  have hAn : A.Normal := nsd_normal hGs
  haveI : A.Normal := hAn
  -- ## the centraliser of `A`
  have hAleD : A ≤ Subgroup.centralizer (A : Set P) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hAab b hb a ha
  have hDinv : (Subgroup.centralizer (A : Set P)).map (h.xi : MulAut P).toMonoidHom
      = Subgroup.centralizer (A : Set P) := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩ a ha
      rw [Subgroup.mem_centralizer_iff] at hy
      have ha' : ((h.xi : MulAut P)⁻¹) a ∈ A := symm_mem_of_map_eq (h.xi : MulAut P) hAxi ha
      have h1 : ((h.xi : MulAut P)⁻¹) a * y = y * ((h.xi : MulAut P)⁻¹) a := hy _ ha'
      calc a * h.xi y = h.xi (((h.xi : MulAut P)⁻¹) a) * h.xi y := by simp
        _ = h.xi (((h.xi : MulAut P)⁻¹) a * y) := by rw [map_mul]
        _ = h.xi (y * ((h.xi : MulAut P)⁻¹) a) := by rw [h1]
        _ = h.xi y * a := by rw [map_mul]; simp
    · intro hx
      refine ⟨((h.xi : MulAut P)⁻¹) x, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro a ha
      have ha' : (h.xi : MulAut P) a ∈ A := by
        rw [← hAxi]
        exact Subgroup.mem_map_of_mem _ ha
      have h1 : h.xi a * x = x * h.xi a := hx _ ha'
      have h2 := congrArg (fun t : P => ((h.xi : MulAut P)⁻¹) t) h1
      simpa using h2
  -- ## every element outside `A` fails to centralise `A`
  have hcent : ∀ u : P, u ∉ A → ∃ a ∈ A, ⁅u, a⁆ ≠ 1 := by
    rcases hirr (Subgroup.centralizer (A : Set P)) inferInstance hDinv hAleD with hDA | hDtop
    · intro u hu
      by_contra hcon
      push Not at hcon
      have huD : u ∈ Subgroup.centralizer (A : Set P) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact (commutatorElement_eq_one_iff_mul_comm.mp (hcon a ha)).symm
      rw [hDA] at huD
      exact hu huD
    · intro u hu
      exfalso
      have hAZ : A ≤ Subgroup.center P := (Subgroup.centralizer_eq_top_iff_subset).mp hDtop
      have hZc : Subgroup.center P = omega1 P := center_eq_omega1_new h
      have hAle2 : A ≤ powSub A 2 := by
        rw [htop]
        intro a ha
        rw [← hZc]
        exact hAZ ha
      have hAeq : A = powSub A 2 := le_antisymm hAle2 (powSub_le (n := 2) (by norm_num))
      have hcard2 : Nat.card ↥(omega1 P) = (Nat.card ↥(omega1 P)) ^ 2 := by
        have h1 : Nat.card ↥A = Nat.card ↥(omega1 P) := by rw [hAeq, htop]
        rw [← h1, h1] at hcard
        exact hcard
      nlinarith [hcard2, h.omega1_card_ge_four]
  -- ## the two fields
  have hAne : A ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥A = 1 := by rw [hbot]; simp
    rw [h1] at hcard
    have h4 : 4 ≤ Nat.card ↥(omega1 P) := h.omega1_card_ge_four
    nlinarith [hcard, h4]
  obtain ⟨nZ, FZ, hFZf, hFZft, hFZd, hFZc, mu, hFZcard, hnZ, hmuord, hmu0, ζZ,
    hζZadd, hζZeq⟩ := omega1_iso_field h
  have hZcard : Nat.card ↥(omega1 P) = 2 ^ nZ := by
    rw [← Nat.card_congr ζZ, Nat.card_eq_fintype_card, hFZcard]
  obtain ⟨FV, hFVf, hFVft, hFVd, hFVc, lamV, hFVcard, hnV, hlamVord, hlamV0, ζV,
    hζVadd, hζVeq⟩ :=
    L1_iso_field_exp h hAxi hAab hNA hGs hsq hA4 htop hcard hirr nZ hZcard
  have hcFVZ : Fintype.card FV = Fintype.card FZ := by rw [hFVcard, hFZcard]
  let σ : FV ≃+* FZ := FiniteField.ringEquivOfCardEq hcFVZ
  set lam : FZ := σ lamV with hlamdef
  have hlamord : orderOf lam = 2 ^ nZ - 1 := by
    rw [hlamdef]
    have key : orderOf ((σ : FV →* FZ) lamV) = orderOf lamV :=
      orderOf_injective (σ : FV →* FZ) σ.injective lamV
    have h1 : orderOf (σ lamV) = orderOf ((σ : FV →* FZ) lamV) := rfl
    rw [h1, key, hlamVord]
  let ζV' : FZ ≃ (P ⧸ A) := σ.symm.toEquiv.trans ζV
  have hζV'add : ∀ x y : FZ, ζV' (x + y) = ζV' x * ζV' y := by
    intro x y
    show ζV (σ.symm (x + y)) = ζV (σ.symm x) * ζV (σ.symm y)
    rw [map_add, hζVadd]
  have hζV'eq : ∀ x : FZ, ∀ u : P, (u : P ⧸ A) = ζV' x →
      ζV' (lam * x) = (h.xi u : P ⧸ A) := by
    intro x u hu
    show ζV (σ.symm (lam * x)) = (h.xi u : P ⧸ A)
    have h1 : σ.symm (lam * x) = lamV * σ.symm x := by
      rw [hlamdef, map_mul, σ.symm_apply_apply]
    rw [h1]
    exact hζVeq (σ.symm x) u hu
  exact nsd_core h hAxi hAab hNA hGs hsq hA4 htop hcard hcent hnZ hFZcard hZcard
    lam mu hlamord hmuord ζV' hζV'add hζV'eq ζZ hζZadd hζZeq

end Work.Higman.H8
