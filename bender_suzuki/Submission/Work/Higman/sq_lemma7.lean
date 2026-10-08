/-
Copyright (c) 2024. All rights reserved.

# Higman (1963), Lemma 7 — own proof

> **LEMMA 7.** Let `A` be a normal abelian `ξ`-subgroup of a Suzuki 2-group `P`, and `C` a normal
> `ξ`-subgroup covering `A`. If `A = Φ(C)` but `C' ≤ A²`, then `C` is abelian.

The proof uses a single pairing `(x, y) ↦ ⁅x,y⁆ ^ (2 ^ (e-1-s))`, which lands in
`A ⊓ Ω₁(P)` (a copy of `Ω₁(P)`) because `[A,C]` and `[C',C]` both lie in `(C')²`
(`Work.Higman.higman_lemma7_comm_le`).  Well definedness and biadditivity of that pairing
(modulo `A` in each variable) are elementary commutator calculus; it is alternating and
`ξ`-equivariant by construction, so Gorenstein–Thompson
(`Work.Higman.MSA.eq_one_of_alt_of_target_iso`, since `ξ` acts transitively on `Ω₁(P) ∖ {1}`)
forces it to vanish.  Hence `C' ≤ (C')²`, and since `C' = A ^ (2 ^ s)` is a non-trivial
homocyclic group this forces `C' = ⊥`.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.higman_lemma7_comm_le
import Submission.Work.Higman.higman_lemma7_phi2
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.MSA.endgame
import Submission.Work.Higman.sq_basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open scoped commutatorElement

namespace Work.Higman

/-- `⁅x, y * z⁆ = ⁅x,y⁆ * (y * ⁅x,z⁆ * y⁻¹)`. -/
theorem sq_comm_mul_right_eq {G : Type*} [Group G] (x y z : G) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
  have h1 : ⁅y * z, x⁆ = y * ⁅z, x⁆ * y⁻¹ * ⁅y, x⁆ :=
    commutatorElement_mul_left_eq_conj_mul y z x
  have h2 : ⁅x, y * z⁆ = (⁅y * z, x⁆)⁻¹ := (commutatorElement_inv (y * z) x).symm
  rw [h2, h1]
  simp only [mul_inv_rev, inv_inv, commutatorElement_inv]
  group

/-- **The layers of a homocyclic abelian subgroup.**  Let `A` be a `ξ`-invariant abelian normal
subgroup of a Suzuki 2-group, of exponent `2 ^ e` (attained).  Then for `i ≤ e - 1` and
`x ∈ A ^ (2 ^ i)` one has `x ∈ A ^ (2 ^ (i + 1))` if and only if `x ^ (2 ^ (e - i - 1)) = 1`. -/
theorem sq_layer_aux {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P)
    {A : Subgroup P} (hA : IsXiAbelNormal h A) {e : ℕ} (he : 1 ≤ e)
    (h1 : ∀ x ∈ A, x ^ 2 ^ e = 1) (hbd : ∃ a ∈ A, orderOf a = 2 ^ e)
    {i : ℕ} (hi : i ≤ e - 1) :
    ∀ x ∈ powSub A (2 ^ i), x ∈ powSub A (2 ^ (i + 1)) ↔ x ^ 2 ^ (e - i - 1) = 1 := by
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  have hBi : IsXiAbelNormal h (powSub A (2 ^ i)) := by
    induction i with
    | zero => simpa [powSub_one_eq] using hA
    | succ k ih =>
        have h2 := MSA.isXiAbelNormal_powSub_two (ih (by omega))
        rwa [show powSub (powSub A (2 ^ k)) 2 = powSub A (2 ^ (k + 1)) from by
          rw [powSub_powSub hAb, ← pow_succ]] at h2
  obtain ⟨e_i, h1i, h2i, hkeyi⟩ := mem_powSub_two_iff h hBi
  -- the exponent of `powSub A (2 ^ i)` divides `2 ^ (e - i)`
  have hexp_le : e_i ≤ e - i := by
    obtain ⟨a', ha', hord⟩ := h2i
    have ha'e : (a' : P) ^ 2 ^ (e - i) = 1 := by
      obtain ⟨z, hz, hza⟩ := (mem_powSub_iff hAb).mp ha'
      rw [← hza, ← pow_mul]
      have hmul : (2 : ℕ) ^ i * 2 ^ (e - i) = 2 ^ e := by
        rw [← pow_add]; congr 1; omega
      rw [hmul]; exact h1 z hz
    have hdiv : orderOf (a' : P) ∣ 2 ^ (e - i) := orderOf_dvd_iff_pow_eq_one.mpr ha'e
    rw [hord] at hdiv
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdiv
  -- conversely `2 ^ (e - i)` divides the exponent of `powSub A (2 ^ i)`
  have hexp_eq : e_i = e - i := by
    obtain ⟨a₀, ha₀, hord₀⟩ := hbd
    have hmem : a₀ ^ 2 ^ i ∈ powSub A (2 ^ i) := pow_mem_powSub ha₀
    have hx1 : (a₀ ^ 2 ^ i) ^ 2 ^ (e - i) = 1 := by
      rw [← pow_mul, show 2 ^ i * 2 ^ (e - i) = 2 ^ e from by rw [← pow_add]; congr 1; omega]
      exact h1 a₀ ha₀
    have hx2 : (a₀ ^ 2 ^ i) ^ 2 ^ (e - i - 1) ≠ 1 := by
      intro hcon
      have h2 : a₀ ^ 2 ^ (e - 1) = 1 := by
        rw [← hcon, ← pow_mul]
        congr 1
        rw [← pow_add]
        congr 1
        omega
      have hdvd : 2 ^ e ∣ 2 ^ (e - 1) := by
        rw [← hord₀]; exact orderOf_dvd_iff_pow_eq_one.mpr h2
      have hle := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
      omega
    have hdvd_symm : 2 ^ (e - i) ∣ orderOf (a₀ ^ 2 ^ i) := by
      obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        (orderOf_dvd_iff_pow_eq_one.mpr hx1)
      have hj' : orderOf (a₀ ^ 2 ^ i) = 2 ^ j := hj
      by_contra hnd
      have hlt : j < e - i := by
        by_contra hcon
        exact hnd (by rw [hj']; exact Nat.pow_dvd_pow 2 (by omega))
      have hji : j ≤ e - i - 1 := by omega
      have hdvd2 : orderOf (a₀ ^ 2 ^ i) ∣ 2 ^ (e - i - 1) := by
        rw [hj']; exact Nat.pow_dvd_pow 2 hji
      exact hx2 (orderOf_dvd_iff_pow_eq_one.mp hdvd2)
    have hdvd3 : orderOf (a₀ ^ 2 ^ i) ∣ 2 ^ e_i := orderOf_dvd_iff_pow_eq_one.mpr (h1i _ hmem)
    have hle2 : e - i ≤ e_i :=
      (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
        ((Nat.dvd_antisymm hdvd_symm (orderOf_dvd_iff_pow_eq_one.mpr hx1)).symm ▸ hdvd3)
    omega
  intro x hx
  have hpow2 : powSub (powSub A (2 ^ i)) 2 = powSub A (2 ^ (i + 1)) := by
    rw [powSub_powSub hAb, ← pow_succ]
  constructor
  · -- `x ∈ A ^ (2 ^ (i+1))` gives `x ^ (2 ^ (e-i-1)) = 1` directly
    intro hx2
    have hx2' : x ∈ powSub (powSub A (2 ^ i)) 2 := by rw [← hpow2] at hx2; exact hx2
    obtain ⟨w, hw, hwx⟩ := (mem_powSub_iff (powSub_comm hAb (2 ^ i))).mp hx2'
    obtain ⟨z, hz, hzw⟩ := (mem_powSub_iff hAb).mp hw
    rw [← hwx, ← hzw, ← pow_mul, ← pow_mul]
    have hmul : 2 ^ i * (2 * 2 ^ (e - i - 1)) = 2 ^ e := by
      rw [← pow_succ', ← pow_add]
      congr 1
      omega
    rw [hmul]
    exact h1 z hz
  · -- conversely use the `2`-layer dichotomy for `A ^ (2 ^ i)`
    intro hval
    have hx2' : x ∈ powSub (powSub A (2 ^ i)) 2 := by
      rw [hkeyi x hx, hexp_eq]
      exact hval
    rwa [hpow2] at hx2'

/-- **Higman (1963), Lemma 7** (Suzuki form, own proof).
`A` a `ξ`-invariant abelian normal subgroup of a Suzuki 2-group `P`, `C > A` a normal
`ξ`-invariant subgroup with `C/A` a minimal normal `ξ`-section, `Φ(C) = A` and `C' ≤ A²`.
Then `C` is abelian. -/
theorem sq_lemma7 {P : Type} [Group P] [Finite P]
    (h : IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hPhi : powSub C 2 ⊔ ⁅C, C⁆ = A)
    (hCd : ⁅C, C⁆ ≤ powSub A 2) :
    ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
  classical
  rcases eq_or_ne A ⊥ with hA0 | hAne
  · intro x hx y hy
    refine commutatorElement_eq_one_iff_mul_comm.mp ?_
    have h1 : ⁅x, y⁆ ∈ powSub A 2 := hCd (Subgroup.commutator_mem_commutator hx hy)
    rw [hA0] at h1
    exact Subgroup.mem_bot.mp (powSub_le (by norm_num : 0 < 2) h1)
  · have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
    have hAn : A.Normal := hA.normal
    have hOm : omega1 P ≤ A := sq_omega1_le_of_isXiAbelNormal_ne_bot h hA hAne
    have hDA : ⁅C, C⁆ ≤ A := by rw [← hPhi]; exact le_sup_right
    haveI hCnI : C.Normal := hCn
    have hCdinv : (⁅C, C⁆).map (h.xi : MulAut P).toMonoidHom = ⁅C, C⁆ := by
      rw [Subgroup.map_commutator, hCinv]
    obtain ⟨e, h1e, hcarde, htop, hsub⟩ := homogeneous_structure h hAb hA.map_eq
    obtain ⟨s, hs⟩ := hsub ⁅C, C⁆ hDA hCdinv
    have hZeq : A ⊓ omega1 P = omega1 P := inf_eq_right.mpr hOm
    have hq4 : 4 ≤ Nat.card ↥(A ⊓ omega1 P) := by
      rw [hZeq]; exact h.omega1_card_ge_four
    have hqpos : 0 < Nat.card ↥(A ⊓ omega1 P) := by omega
    have he1 : 1 ≤ e := by
      by_contra hcon
      have h0 : e = 0 := by omega
      have h1 : Nat.card ↥A = 1 := by
        have hh := hcarde 0 (Nat.zero_le e)
        rw [show (2 : ℕ) ^ 0 = 1 from by norm_num, powSub_one_eq] at hh
        simpa [h0] using hh
      exact hAne (Subgroup.card_eq_one.mp h1)
    have hcard0 : Nat.card ↥A = (Nat.card ↥(A ⊓ omega1 P)) ^ e := by
      have hh := hcarde 0 (Nat.zero_le e)
      rwa [show (2 : ℕ) ^ 0 = 1 from by norm_num, powSub_one_eq] at hh
    -- an element of `A` of order `2 ^ e`
    have hbd : ∃ a ∈ A, orderOf a = 2 ^ e := by
      obtain ⟨e'', h1'', h2'', hcard''⟩ := higman_lemma1 h hAb hA.map_eq
      obtain ⟨a, ha, hord⟩ := h2''
      refine ⟨a, ha, ?_⟩
      have hq : (Nat.card ↥(A ⊓ omega1 P)) ^ e'' = (Nat.card ↥(A ⊓ omega1 P)) ^ e := by
        rw [← hcard'']; exact hcard0
      have hee : e'' = e :=
        Nat.pow_right_injective (by omega : 2 ≤ Nat.card ↥(A ⊓ omega1 P)) hq
      rw [hord, hee]
    rcases eq_or_ne ⁅C, C⁆ ⊥ with hD0 | hDne
    · intro x hx y hy
      refine commutatorElement_eq_one_iff_mul_comm.mp ?_
      have h1 : ⁅x, y⁆ ∈ (⊥ : Subgroup P) := by
        rw [← hD0]; exact Subgroup.commutator_mem_commutator hx hy
      simpa using h1
    · exfalso
      -- ## `s ≥ 1` and `s ≤ e - 1`
      have hs1 : 1 ≤ s := by
        by_contra hcon
        have h0 : s = 0 := by omega
        have hDAeq : ⁅C, C⁆ = A := by
          rw [hs, h0, show (2 : ℕ) ^ 0 = 1 from by norm_num, powSub_one_eq]
        have hAle : A ≤ powSub A 2 := hDAeq ▸ hCd
        have hle : Nat.card ↥A ≤ Nat.card ↥(powSub A 2) :=
          Nat.card_le_card_of_injective (Subgroup.inclusion hAle)
            (Subgroup.inclusion_injective hAle)
        have hc1 : Nat.card ↥(powSub A 2) = (Nat.card ↥(A ⊓ omega1 P)) ^ (e - 1) :=
          hcarde 1 he1
        have hineq : (Nat.card ↥(A ⊓ omega1 P)) ^ e
            ≤ (Nat.card ↥(A ⊓ omega1 P)) ^ (e - 1) := by
          rw [← hcard0, ← hc1]
          exact hle
        rw [show e = (e - 1) + 1 from by omega, pow_succ] at hineq
        have honemul : (Nat.card ↥(A ⊓ omega1 P)) ^ (e - 1) * 1
            = (Nat.card ↥(A ⊓ omega1 P)) ^ (e - 1) := mul_one _
        have hfin : Nat.card ↥(A ⊓ omega1 P) ≤ 1 :=
          Nat.le_of_mul_le_mul_left (by rw [honemul]; exact hineq) (pow_pos hqpos (e - 1))
        omega
      have hse : s ≤ e - 1 := by
        by_contra hcon
        push Not at hcon
        have hge : e ≤ s := by omega
        have hbot : powSub A (2 ^ s) = ⊥ :=
          le_bot_iff.mp ((powSub_le_of_dvd hAb (Nat.pow_dvd_pow 2 hge)).trans
            (le_of_eq (powSub_eq_bot_of_exp hAb le_rfl h1e)))
        exact hDne (hs.trans hbot)
      -- ## the structural inputs
      obtain ⟨hAC2, hD2C⟩ := higman_lemma7_comm_le h hA hCn hAC hPhi hCd hs1 hse h1e hs
      have hlayer : ∀ x ∈ powSub A (2 ^ s),
          x ∈ powSub A (2 ^ (s + 1)) ↔ x ^ 2 ^ (e - s - 1) = 1 :=
        sq_layer_aux h hA he1 h1e hbd hse
      have hkey : ∀ y ∈ A, y ∈ powSub A 2 ↔ y ^ 2 ^ (e - 1) = 1 := by
        intro y hy
        have h0 := sq_layer_aux h hA he1 h1e hbd (i := 0) (by omega)
        have hy' : y ∈ powSub A (2 ^ 0) := by simpa [powSub_one_eq] using hy
        simpa using h0 y hy'
      obtain ⟨phi1, phi2mem, phi3, phi4, phi5⟩ :=
        higman_lemma7_phi2 h hA hCn hCinv hAC hCA hcover hPhi hCd hAne he1 h1e hkey htop
      -- ## `C' = A ^ (2 ^ s)` and the two elementary facts about `(C')²`
      have hDs2 : powSub ⁅C, C⁆ 2 = powSub A (2 ^ (s + 1)) := by
        rw [hs, powSub_powSub hAb (2 ^ s) 2, ← pow_succ]
      have hDab : ∀ u ∈ ⁅C, C⁆, ∀ v ∈ ⁅C, C⁆, u * v = v * u :=
        fun u hu v hv => hAb u (hDA hu) v (hDA hv)
      have hD2conj : ∀ d ∈ powSub ⁅C, C⁆ 2, ∀ g : P, g * d * g⁻¹ ∈ powSub ⁅C, C⁆ 2 := by
        intro d hd g
        obtain ⟨u, hu, rfl⟩ := (mem_powSub_iff hDab).mp hd
        refine (mem_powSub_iff hDab).mpr ⟨g * u * g⁻¹, ?_, ?_⟩
        · exact (Subgroup.commutator_normal C C).conj_mem u hu g
        · rw [show (g * u * g⁻¹) ^ 2 = g * u ^ 2 * g⁻¹ from by rw [pow_two, pow_two]; group]
      -- ## the facts about `v ↦ v ^ (2 ^ (e-1-s))` on `C'`
      have psi1 : ∀ v ∈ ⁅C, C⁆, v ^ 2 ^ (e - 1 - s) ∈ A ⊓ omega1 P := by
        intro v hv
        have hv' : v ∈ powSub A (2 ^ s) := by rw [← hs]; exact hv
        refine Subgroup.mem_inf.mpr ⟨Subgroup.pow_mem A (hDA hv) _, ?_⟩
        refine h.mem_omega1.mpr ?_
        obtain ⟨a, ha, hav⟩ := (mem_powSub_iff hAb).mp hv'
        rw [← hav, ← pow_mul, ← pow_mul]
        have hmul : 2 ^ s * (2 ^ (e - 1 - s) * 2) = 2 ^ e := by
          rw [← pow_succ, ← pow_add]
          congr 1
          omega
        rw [hmul]
        exact h1e a ha
      have psi3 : ∀ v ∈ ⁅C, C⁆, v ^ 2 ^ (e - 1 - s) = 1 ↔ v ∈ powSub ⁅C, C⁆ 2 := by
        intro v hv
        have hv' : v ∈ powSub A (2 ^ s) := by rw [← hs]; exact hv
        have hlv : v ∈ powSub A (2 ^ (s + 1)) ↔ v ^ 2 ^ (e - s - 1) = 1 := hlayer v hv'
        rw [hDs2, hlv]
        have heq : 2 ^ (e - s - 1) = 2 ^ (e - 1 - s) := by congr 1; omega
        rw [heq]
      have hpowinv : ∀ v ∈ ⁅C, C⁆, ∀ w ∈ ⁅C, C⁆,
          v * w⁻¹ ∈ powSub ⁅C, C⁆ 2 → v ^ 2 ^ (e - 1 - s) = w ^ 2 ^ (e - 1 - s) := by
        intro v hv w hw hrel
        have hv' : v * w⁻¹ ∈ ⁅C, C⁆ := (⁅C, C⁆).mul_mem hv ((⁅C, C⁆).inv_mem hw)
        have hcomm : Commute (v * w⁻¹) w := hDab _ hv' _ hw
        calc v ^ 2 ^ (e - 1 - s) = ((v * w⁻¹) * w) ^ 2 ^ (e - 1 - s) := by
              rw [show (v * w⁻¹) * w = v from by group]
          _ = (v * w⁻¹) ^ 2 ^ (e - 1 - s) * w ^ 2 ^ (e - 1 - s) := Commute.mul_pow hcomm _
          _ = 1 * w ^ 2 ^ (e - 1 - s) := by rw [(psi3 (v * w⁻¹) hv').mpr hrel]
          _ = w ^ 2 ^ (e - 1 - s) := one_mul _
      have psi2 : ∀ u ∈ ⁅C, C⁆, ∀ v ∈ ⁅C, C⁆,
          (u * v) ^ 2 ^ (e - 1 - s) = u ^ 2 ^ (e - 1 - s) * v ^ 2 ^ (e - 1 - s) := by
        intro u hu v hv
        exact Commute.mul_pow (hDab _ hu _ hv) _
      -- ## the four commutator computations
      have hI1 : ∀ x ∈ C, ∀ a ∈ A, ∀ y ∈ C,
          ⁅x * a, y⁆ ^ 2 ^ (e - 1 - s) = ⁅x, y⁆ ^ 2 ^ (e - 1 - s) := by
        intro x hx a ha y hy
        have hrel : ⁅x * a, y⁆ * ⁅x, y⁆⁻¹ ∈ powSub ⁅C, C⁆ 2 := by
          have heq : ⁅x * a, y⁆ * ⁅x, y⁆⁻¹ = x * ⁅a, y⁆ * x⁻¹ := by
            rw [commutatorElement_mul_left_eq_conj_mul]; group
          rw [heq]
          exact hD2conj _ (hAC2 (Subgroup.commutator_mem_commutator ha hy)) x
        exact hpowinv _ (Subgroup.commutator_mem_commutator (C.mul_mem hx (hAC ha)) hy)
          _ (Subgroup.commutator_mem_commutator hx hy) hrel
      have hI2 : ∀ x ∈ C, ∀ y ∈ C, ∀ b ∈ A,
          ⁅x, y * b⁆ ^ 2 ^ (e - 1 - s) = ⁅x, y⁆ ^ 2 ^ (e - 1 - s) := by
        intro x hx y hy b hb
        have hrel : ⁅x, y * b⁆ * ⁅x, y⁆⁻¹ ∈ powSub ⁅C, C⁆ 2 := by
          have hmid : y * ⁅x, b⁆ * y⁻¹ ∈ powSub ⁅C, C⁆ 2 := by
            have hmem : ⁅x, b⁆ ∈ ⁅C, A⁆ := Subgroup.commutator_mem_commutator hx hb
            rw [Subgroup.commutator_comm] at hmem
            exact hD2conj _ (hAC2 hmem) y
          have heq : ⁅x, y * b⁆ * ⁅x, y⁆⁻¹
              = ⁅x, y⁆ * (y * ⁅x, b⁆ * y⁻¹) * ⁅x, y⁆⁻¹ := by
            rw [sq_comm_mul_right_eq]
          rw [heq]
          exact hD2conj _ hmid ⁅x, y⁆
        exact hpowinv _ (Subgroup.commutator_mem_commutator hx (C.mul_mem hy (hAC hb)))
          _ (Subgroup.commutator_mem_commutator hx hy) hrel
      have hB1 : ∀ x ∈ C, ∀ x' ∈ C, ∀ y ∈ C,
          ⁅x * x', y⁆ ^ 2 ^ (e - 1 - s)
            = ⁅x, y⁆ ^ 2 ^ (e - 1 - s) * ⁅x', y⁆ ^ 2 ^ (e - 1 - s) := by
        intro x hx x' hx' y hy
        have hd : ⁅x', y⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hx' hy
        have he : ⁅x, y⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hx hy
        have hrel : ⁅x * x', y⁆ * (⁅x, y⁆ * ⁅x', y⁆)⁻¹ ∈ powSub ⁅C, C⁆ 2 := by
          have hsplit : x * ⁅x', y⁆ * x⁻¹ = ⁅x, ⁅x', y⁆⁆ * ⁅x', y⁆ := by
            rw [commutatorElement_def]; group
          have heq : ⁅x * x', y⁆ * (⁅x, y⁆ * ⁅x', y⁆)⁻¹
              = ⁅x, ⁅x', y⁆⁆ * (⁅x', y⁆ * ⁅x, y⁆ * ⁅x', y⁆⁻¹ * ⁅x, y⁆⁻¹) := by
            rw [commutatorElement_mul_left_eq_conj_mul, hsplit]; group
          rw [heq]
          refine (powSub ⁅C, C⁆ 2).mul_mem ?_ ?_
          · have hmem : ⁅x, ⁅x', y⁆⁆ ∈ ⁅C, ⁅C, C⁆⁆ :=
              Subgroup.commutator_mem_commutator hx hd
            rw [Subgroup.commutator_comm] at hmem
            exact hD2C hmem
          · have hinn : ⁅x', y⁆ * ⁅x, y⁆ * ⁅x', y⁆⁻¹ * ⁅x, y⁆⁻¹ = ⁅⁅x', y⁆, ⁅x, y⁆⁆ := by
              rw [commutatorElement_def]; group
            rw [hinn]
            refine hD2C ?_
            have hmem : ⁅⁅x', y⁆, ⁅x, y⁆⁆ ∈ ⁅⁅C, C⁆, ⁅C, C⁆⁆ :=
              Subgroup.commutator_mem_commutator hd he
            exact (Subgroup.commutator_mono le_rfl (hDA.trans hAC)) hmem
        calc ⁅x * x', y⁆ ^ 2 ^ (e - 1 - s)
            = (⁅x, y⁆ * ⁅x', y⁆) ^ 2 ^ (e - 1 - s) :=
              hpowinv _ (Subgroup.commutator_mem_commutator (C.mul_mem hx hx') hy)
                _ ((⁅C, C⁆).mul_mem he hd) hrel
          _ = ⁅x, y⁆ ^ 2 ^ (e - 1 - s) * ⁅x', y⁆ ^ 2 ^ (e - 1 - s) :=
              Commute.mul_pow (hDab _ he _ hd) _
      have hB2 : ∀ x ∈ C, ∀ y ∈ C, ∀ y' ∈ C,
          ⁅x, y * y'⁆ ^ 2 ^ (e - 1 - s)
            = ⁅x, y⁆ ^ 2 ^ (e - 1 - s) * ⁅x, y'⁆ ^ 2 ^ (e - 1 - s) := by
        intro x hx y hy y' hy'
        have he : ⁅x, y⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hx hy
        have hd : ⁅x, y'⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hx hy'
        have hrel : ⁅x, y * y'⁆ * (⁅x, y⁆ * ⁅x, y'⁆)⁻¹ ∈ powSub ⁅C, C⁆ 2 := by
          have hinner : y * ⁅x, y'⁆ * y⁻¹ * ⁅x, y'⁆⁻¹ = ⁅y, ⁅x, y'⁆⁆ := by
            rw [commutatorElement_def]; group
          have heq : ⁅x, y * y'⁆ * (⁅x, y⁆ * ⁅x, y'⁆)⁻¹
              = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹ * ⁅x, y'⁆⁻¹) * ⁅x, y⁆⁻¹ := by
            rw [sq_comm_mul_right_eq]; group
          rw [heq, hinner]
          refine hD2conj _ ?_ ⁅x, y⁆
          have hmem : ⁅y, ⁅x, y'⁆⁆ ∈ ⁅C, ⁅C, C⁆⁆ :=
            Subgroup.commutator_mem_commutator hy hd
          rw [Subgroup.commutator_comm] at hmem
          exact hD2C hmem
        calc ⁅x, y * y'⁆ ^ 2 ^ (e - 1 - s)
            = (⁅x, y⁆ * ⁅x, y'⁆) ^ 2 ^ (e - 1 - s) :=
              hpowinv _ (Subgroup.commutator_mem_commutator hx (C.mul_mem hy hy'))
                _ ((⁅C, C⁆).mul_mem he hd) hrel
          _ = ⁅x, y⁆ ^ 2 ^ (e - 1 - s) * ⁅x, y'⁆ ^ 2 ^ (e - 1 - s) :=
              Commute.mul_pow (hDab _ he _ hd) _
      have hE : ∀ x ∈ C, ∀ y ∈ C,
          ⁅h.xi x, h.xi y⁆ ^ 2 ^ (e - 1 - s) = h.xi (⁅x, y⁆ ^ 2 ^ (e - 1 - s)) := by
        intro x hx y hy
        have h1 : ⁅h.xi x, h.xi y⁆ = h.xi ⁅x, y⁆ :=
          (map_commutatorElement (h.xi : MulAut P).toMonoidHom x y).symm
        rw [h1, map_pow]
      -- ## the pairing on `Ω₁(P)`
      have hxiC : ∀ y ∈ C, h.xi y ∈ C := by
        intro y hy
        have hmem := Subgroup.mem_map_of_mem (f := (h.xi : MulAut P).toMonoidHom) hy
        rwa [hCinv] at hmem
      let ρ : ↥(omega1 P) → P := fun u =>
        Classical.choose (phi3 (u : P) (Subgroup.mem_inf.mpr ⟨hOm u.2, u.2⟩))
      have hρC : ∀ u : ↥(omega1 P), ρ u ∈ C := fun u =>
        (Classical.choose_spec (phi3 (u : P) (Subgroup.mem_inf.mpr ⟨hOm u.2, u.2⟩))).1
      have hρpow : ∀ u : ↥(omega1 P), ρ u ^ 2 ^ e = (u : P) := fun u =>
        (Classical.choose_spec (phi3 (u : P) (Subgroup.mem_inf.mpr ⟨hOm u.2, u.2⟩))).2
      have hinvpow : ∀ x ∈ C, (x⁻¹) ^ 2 ^ e = (x ^ 2 ^ e)⁻¹ := by
        intro x hx
        have h1 := phi1 x⁻¹ (C.inv_mem hx) x hx
        rw [inv_mul_cancel, one_pow] at h1
        exact (inv_eq_of_mul_eq_one_left h1.symm).symm
      letI hCommΩ : CommGroup ↥(omega1 P) :=
        { (inferInstance : Group ↥(omega1 P)) with
          mul_comm := fun x y => Subtype.ext (h.omega1_comm x.2 y.2) }
      letI hMulΩ : Mul ↥(omega1 P) := hCommΩ.toMul
      letI hOneΩ : One ↥(omega1 P) := hCommΩ.toOne
      have hcoe_mul : ∀ x y : ↥(omega1 P),
          ((x * y : ↥(omega1 P)) : P) = (x : P) * (y : P) := by
        rintro ⟨x, hx⟩ ⟨y, hy⟩
        rfl
      have hcoe_one : ((1 : ↥(omega1 P)) : P) = 1 := rfl
      let cpair : ↥(omega1 P) → ↥(omega1 P) → ↥(omega1 P) := fun u v =>
        ⟨⁅ρ u, ρ v⁆ ^ 2 ^ (e - 1 - s),
          (inf_le_right : A ⊓ omega1 P ≤ omega1 P)
            (psi1 ⁅ρ u, ρ v⁆ (Subgroup.commutator_mem_commutator (hρC u) (hρC v)))⟩
      have hcpair_val : ∀ u v : ↥(omega1 P),
          ((cpair u v : ↥(omega1 P)) : P) = ⁅ρ u, ρ v⁆ ^ 2 ^ (e - 1 - s) := fun u v => rfl
      -- ## the `ξ`-action on `Ω₁(P)` with the instances introduced above
      let xiF : ↥(omega1 P) → ↥(omega1 P) := fun u => ⟨h.xi (u : P), by
        have hmem : h.xi (u : P) ∈ (omega1 P).map (h.xi : MulAut P).toMonoidHom :=
          Subgroup.mem_map_of_mem (f := (h.xi : MulAut P).toMonoidHom) u.2
        rwa [map_xi_omega1 h] at hmem⟩
      have hxiF_coe : ∀ u : ↥(omega1 P), ((xiF u : ↥(omega1 P)) : P) = h.xi (u : P) :=
        fun u => rfl
      have hxiF_inv : ∀ u : ↥(omega1 P), xiF ⟨(h.xi : MulAut P).symm (u : P), by
          have hmem : (u : P) ∈ (omega1 P).map (h.xi : MulAut P).toMonoidHom := by
            rw [map_xi_omega1 h]; exact u.2
          obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmem
          have hys : (h.xi : MulAut P).symm (u : P) = y := by
            rw [← hyeq]; simp
          rw [hys]; exact hy⟩ = u := by
        intro u
        apply Subtype.ext
        show h.xi ((h.xi : MulAut P).symm (u : P)) = (u : P)
        simp
      have hxiF_mul : ∀ u v : ↥(omega1 P), xiF (u * v) = xiF u * xiF v := by
        intro u v
        apply Subtype.ext
        show ((xiF (u * v) : ↥(omega1 P)) : P) = ((xiF u * xiF v : ↥(omega1 P)) : P)
        rw [hxiF_coe, hcoe_mul (xiF u) (xiF v), hxiF_coe, hxiF_coe, hcoe_mul u v]
        simp
      let ξΩ : MulAut ↥(omega1 P) :=
        { toFun := xiF
          invFun := fun u => ⟨(h.xi : MulAut P).symm (u : P), by
            have hmem : (u : P) ∈ (omega1 P).map (h.xi : MulAut P).toMonoidHom := by
              rw [map_xi_omega1 h]; exact u.2
            obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmem
            have hys : (h.xi : MulAut P).symm (u : P) = y := by
              rw [← hyeq]; simp
            rw [hys]; exact hy⟩
          left_inv := fun u => by
            apply Subtype.ext
            show (h.xi : MulAut P).symm ((xiF u : ↥(omega1 P)) : P) = (u : P)
            rw [hxiF_coe]
            simp
          right_inv := fun u => hxiF_inv u
          map_mul' := hxiF_mul }
      have hxiΩ_fun : ∀ a : ↥(omega1 P), ξΩ a = sq_xiOmega1 h a := by
        intro a
        apply Subtype.ext
        rfl
      have hxiΩ_pow : ∀ k : ℕ, ξΩ ^ k = sq_xiOmega1 h ^ k := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
            rw [pow_succ, ih, pow_succ,
              show ξΩ = sq_xiOmega1 h from MulEquiv.ext hxiΩ_fun]
      have hxiΩ_eq : ∀ (k : ℕ) (a : ↥(omega1 P)),
          ((ξΩ ^ k) a : P) = ((sq_xiOmega1 h ^ k) a : P) := by
        intro k a
        rw [hxiΩ_pow k]
      have htransΩ : ∀ a b : ↥(omega1 P), a ≠ 1 → b ≠ 1 → ∃ k : ℕ, ((ξΩ ^ k) a) = b := by
        intro a b ha hb
        obtain ⟨k, hk⟩ := sq_trans_omega1 h a b ha hb
        exact ⟨k, by rw [hxiΩ_pow k]; exact hk⟩
      have htransΩ : ∀ a b : ↥(omega1 P), a ≠ 1 → b ≠ 1 → ∃ k : ℕ, ((ξΩ ^ k) a) = b := by
        intro a b ha hb
        obtain ⟨k, hk⟩ := sq_trans_omega1 h a b ha hb
        refine ⟨k, Subtype.ext ?_⟩
        rw [hxiΩ_eq k a]
        exact congrArg Subtype.val hk
      -- ## `ρ (u * v) * (ρ u * ρ v)⁻¹ ∈ A` and the analogous `ξ`-statement
      have hρmul : ∀ u v : ↥(omega1 P), ρ (u * v) * (ρ u * ρ v)⁻¹ ∈ A := by
        intro u v
        have hmem : ρ (u * v) * (ρ u * ρ v)⁻¹ ∈ C :=
          C.mul_mem (hρC _) (C.inv_mem (C.mul_mem (hρC u) (hρC v)))
        refine (phi4 _ hmem).mp ?_
        rw [phi1 _ (hρC _) _ (C.inv_mem (C.mul_mem (hρC u) (hρC v)))]
        rw [hinvpow _ (C.mul_mem (hρC u) (hρC v))]
        rw [phi1 _ (hρC u) _ (hρC v)]
        rw [hρpow, hρpow, hρpow]
        rw [hcoe_mul]
        simp
      have hρxi : ∀ u : ↥(omega1 P), ρ (ξΩ u) * (h.xi (ρ u))⁻¹ ∈ A := by
        intro u
        have hxiu : h.xi (ρ u) ∈ C := hxiC _ (hρC u)
        have hmem : ρ (ξΩ u) * (h.xi (ρ u))⁻¹ ∈ C :=
          C.mul_mem (hρC _) (C.inv_mem hxiu)
        refine (phi4 _ hmem).mp ?_
        rw [phi1 _ (hρC _) _ (C.inv_mem hxiu), hinvpow _ hxiu]
        have h1 : ((ξΩ u : ↥(omega1 P)) : P) = h.xi (u : P) := rfl
        rw [hρpow, h1]
        rw [phi5 (ρ u) (hρC u), hρpow]
        simp
      -- ### Gorenstein–Thompson hypotheses
      have h2c : ∀ a : ↥(omega1 P), a * a = 1 := fun a => by
        apply Subtype.ext
        rw [hcoe_mul, hcoe_one]
        simpa [pow_two] using h.mem_omega1.mp a.2
      have hmulc : ∀ a b d : ↥(omega1 P), cpair (a * b) d = cpair a d * cpair b d := by
        intro a b d
        have ha' : (ρ a * ρ b)⁻¹ * ρ (a * b) ∈ A := by
          have hh := sq_conj_mem hAn (hρmul a b) (g := ρ a * ρ b)
          simpa [mul_assoc] using hh
        have hstep : ⁅ρ (a * b), ρ d⁆ ^ 2 ^ (e - 1 - s)
            = ⁅ρ a * ρ b, ρ d⁆ ^ 2 ^ (e - 1 - s) := by
          have heq : ρ (a * b) = (ρ a * ρ b) * ((ρ a * ρ b)⁻¹ * ρ (a * b)) := by group
          rw [heq, hI1 (ρ a * ρ b) (C.mul_mem (hρC a) (hρC b)) _ ha' (ρ d) (hρC d)]
        apply Subtype.ext
        simp only [hcpair_val, hcoe_mul]
        rw [hstep, hB1 (ρ a) (hρC a) (ρ b) (hρC b) (ρ d) (hρC d)]
      have hmulc' : ∀ a b d : ↥(omega1 P), cpair a (b * d) = cpair a b * cpair a d := by
        intro a b d
        have hb' : (ρ b * ρ d)⁻¹ * ρ (b * d) ∈ A := by
          have hh := sq_conj_mem hAn (hρmul b d) (g := ρ b * ρ d)
          simpa [mul_assoc] using hh
        have hstep : ⁅ρ a, ρ (b * d)⁆ ^ 2 ^ (e - 1 - s)
            = ⁅ρ a, ρ b * ρ d⁆ ^ 2 ^ (e - 1 - s) := by
          have heq : ρ (b * d) = (ρ b * ρ d) * ((ρ b * ρ d)⁻¹ * ρ (b * d)) := by group
          rw [heq, hI2 (ρ a) (hρC a) (ρ b * ρ d) (C.mul_mem (hρC b) (hρC d))
            ((ρ b * ρ d)⁻¹ * ρ (b * d)) hb']
        apply Subtype.ext
        simp only [hcpair_val, hcoe_mul]
        rw [hstep, hB2 (ρ a) (hρC a) (ρ b) (hρC b) (ρ d) (hρC d)]
      have haltc : ∀ a : ↥(omega1 P), cpair a a = 1 := by
        intro a
        apply Subtype.ext
        simp only [hcpair_val, hcoe_one, commutatorElement_self, one_pow]
      have heqc : ∀ a b : ↥(omega1 P),
          cpair (ξΩ a) (ξΩ b) = ξΩ (cpair a b) := by
        intro a b
        have hra : (h.xi (ρ a))⁻¹ * ρ (ξΩ a) ∈ A := by
          have hh := sq_conj_mem hAn (hρxi a) (g := h.xi (ρ a))
          simpa [mul_assoc] using hh
        have hrb : (h.xi (ρ b))⁻¹ * ρ (ξΩ b) ∈ A := by
          have hh := sq_conj_mem hAn (hρxi b) (g := h.xi (ρ b))
          simpa [mul_assoc] using hh
        have hstep1 : ⁅ρ (ξΩ a), ρ (ξΩ b)⁆ ^ 2 ^ (e - 1 - s)
            = ⁅h.xi (ρ a), h.xi (ρ b)⁆ ^ 2 ^ (e - 1 - s) := by
          have e1 : ρ (ξΩ a)
              = h.xi (ρ a) * ((h.xi (ρ a))⁻¹ * ρ (ξΩ a)) := by group
          have e2 : ρ (ξΩ b)
              = h.xi (ρ b) * ((h.xi (ρ b))⁻¹ * ρ (ξΩ b)) := by group
          rw [e1, hI1 (h.xi (ρ a)) (hxiC _ (hρC a)) _ hra _ (hρC _)]
          rw [e2, hI2 (h.xi (ρ a)) (hxiC _ (hρC a)) (h.xi (ρ b)) (hxiC _ (hρC b))
            ((h.xi (ρ b))⁻¹ * ρ (ξΩ b)) hrb]
        apply Subtype.ext
        simp only [hcpair_val, hcoe_mul]
        rw [hstep1]
        show ⁅h.xi (ρ a), h.xi (ρ b)⁆ ^ 2 ^ (e - 1 - s) = h.xi (↑(cpair a b))
        rw [hcpair_val]
        exact hE (ρ a) (hρC a) (ρ b) (hρC b)
      -- ### Gorenstein–Thompson
      have htriv : ∀ a b : ↥(omega1 P), cpair a b = 1 :=
        MSA.eq_one_of_alt_of_target_iso h2c ξΩ ξΩ
          htransΩ cpair hmulc hmulc' haltc heqc (MulEquiv.refl _) (fun _ => rfl)
      -- ## conclusion: `C' ⊆ (C')²`
      have hρrel : ∀ x ∈ C, ∀ hxΩ : x ^ 2 ^ e ∈ omega1 P,
          ρ ⟨x ^ 2 ^ e, hxΩ⟩ * x⁻¹ ∈ A := by
        intro x hx hxΩ
        have hmem : ρ ⟨x ^ 2 ^ e, hxΩ⟩ * x⁻¹ ∈ C := C.mul_mem (hρC _) (C.inv_mem hx)
        refine (phi4 _ hmem).mp ?_
        rw [phi1 _ (hρC _) _ (C.inv_mem hx), hinvpow _ hx, hρpow]
        simp
      have hall : ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ^ 2 ^ (e - 1 - s) = 1 := by
        intro x hx y hy
        have hxΩ : x ^ 2 ^ e ∈ omega1 P := (Subgroup.mem_inf.mp (phi2mem x hx)).2
        have hyΩ : y ^ 2 ^ e ∈ omega1 P := (Subgroup.mem_inf.mp (phi2mem y hy)).2
        have htv := htriv ⟨x ^ 2 ^ e, hxΩ⟩ ⟨y ^ 2 ^ e, hyΩ⟩
        have ha' : (ρ ⟨x ^ 2 ^ e, hxΩ⟩)⁻¹ * x ∈ A := by
          have h1 : x⁻¹ * ρ ⟨x ^ 2 ^ e, hxΩ⟩ ∈ A := by
            have hh := sq_conj_mem hAn (hρrel x hx hxΩ) (g := x)
            simpa [mul_assoc] using hh
          have h2 : (x⁻¹ * ρ ⟨x ^ 2 ^ e, hxΩ⟩)⁻¹ ∈ A := A.inv_mem h1
          simpa [mul_inv_rev] using h2
        have hb' : (ρ ⟨y ^ 2 ^ e, hyΩ⟩)⁻¹ * y ∈ A := by
          have h1 : y⁻¹ * ρ ⟨y ^ 2 ^ e, hyΩ⟩ ∈ A := by
            have hh := sq_conj_mem hAn (hρrel y hy hyΩ) (g := y)
            simpa [mul_assoc] using hh
          have h2 : (y⁻¹ * ρ ⟨y ^ 2 ^ e, hyΩ⟩)⁻¹ ∈ A := A.inv_mem h1
          simpa [mul_inv_rev] using h2
        have e1 : x = ρ ⟨x ^ 2 ^ e, hxΩ⟩ * ((ρ ⟨x ^ 2 ^ e, hxΩ⟩)⁻¹ * x) := by group
        have e2 : y = ρ ⟨y ^ 2 ^ e, hyΩ⟩ * ((ρ ⟨y ^ 2 ^ e, hyΩ⟩)⁻¹ * y) := by group
        have hval : ((cpair ⟨x ^ 2 ^ e, hxΩ⟩ ⟨y ^ 2 ^ e, hyΩ⟩ : ↥(omega1 P)) : P)
            = ⁅x, y⁆ ^ 2 ^ (e - 1 - s) := by
          rw [hcpair_val]
          conv_rhs => rw [e1]
          rw [hI1 (ρ ⟨x ^ 2 ^ e, hxΩ⟩) (hρC _) ((ρ ⟨x ^ 2 ^ e, hxΩ⟩)⁻¹ * x) ha'
            y hy]
          conv_rhs => rw [e2]
          rw [hI2 (ρ ⟨x ^ 2 ^ e, hxΩ⟩) (hρC _) (ρ ⟨y ^ 2 ^ e, hyΩ⟩) (hρC _)
            ((ρ ⟨y ^ 2 ^ e, hyΩ⟩)⁻¹ * y) hb']
        have h1 : (cpair ⟨x ^ 2 ^ e, hxΩ⟩ ⟨y ^ 2 ^ e, hyΩ⟩ : ↥(omega1 P)) = 1 := htv
        calc ⁅x, y⁆ ^ 2 ^ (e - 1 - s)
            = ((cpair ⟨x ^ 2 ^ e, hxΩ⟩ ⟨y ^ 2 ^ e, hyΩ⟩ : ↥(omega1 P)) : P) := hval.symm
          _ = ((1 : ↥(omega1 P)) : P) := by rw [h1]
          _ = 1 := hcoe_one
      have hDle : ⁅C, C⁆ ≤ powSub ⁅C, C⁆ 2 := by
        rw [Subgroup.commutator_def]
        refine (Subgroup.closure_le (powSub ⁅C, C⁆ 2)).mpr ?_
        rintro z ⟨x, hx, y, hy, rfl⟩
        exact (psi3 ⁅x, y⁆ (Subgroup.commutator_mem_commutator hx hy)).mp (hall x hx y hy)
      -- ## the cardinality contradiction
      have hD2eq : powSub ⁅C, C⁆ 2 = ⁅C, C⁆ :=
        le_antisymm (powSub_le (by norm_num)) hDle
      have hcard_eq : Nat.card ↥(powSub A (2 ^ s)) = Nat.card ↥(powSub A (2 ^ (s + 1))) := by
        have h2 : powSub A (2 ^ s) = ⁅C, C⁆ := hs.symm
        have h3 : ⁅C, C⁆ = powSub ⁅C, C⁆ 2 := hD2eq.symm
        rw [h2, h3, hDs2]
      have hcs : Nat.card ↥(powSub A (2 ^ s)) = (Nat.card ↥(A ⊓ omega1 P)) ^ (e - s) :=
        hcarde s (by omega)
      have hcs1 : Nat.card ↥(powSub A (2 ^ (s + 1)))
          = (Nat.card ↥(A ⊓ omega1 P)) ^ (e - s - 1) := by
        have h := hcarde (s + 1) (by omega)
        rwa [show e - (s + 1) = e - s - 1 from by omega] at h
      rw [hcs, hcs1] at hcard_eq
      have hineq : (Nat.card ↥(A ⊓ omega1 P)) ^ (e - s)
          ≤ (Nat.card ↥(A ⊓ omega1 P)) ^ (e - s - 1) := le_of_eq hcard_eq
      rw [show e - s = (e - s - 1) + 1 from by omega, pow_succ] at hineq
      have honemul : (Nat.card ↥(A ⊓ omega1 P)) ^ (e - s - 1) * 1
          = (Nat.card ↥(A ⊓ omega1 P)) ^ (e - s - 1) := mul_one _
      have hfin : Nat.card ↥(A ⊓ omega1 P) ≤ 1 :=
        Nat.le_of_mul_le_mul_left (by rw [honemul]; exact hineq) (pow_pos hqpos (e - s - 1))
      omega

end Work.Higman
