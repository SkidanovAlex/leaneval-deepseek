/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area DSTR)

# `Work.DSTR.coreOddStep` — the "odd core" step of Bender 1.10(i)

Statement (unchanged below): if `K ⊴ X` has odd order, `t` an involution, `p ≠ 2` a prime,
`P ≤ K` a `p`-subgroup inverted by `t` and normalised by `C_X(t)`, then `P ≤ O_p(K)`.

## Mathematical plan (developed in this file)

Write `F = F(K)` for the Fitting subgroup and let `D ⊴ F` be `t`- and `P`-invariant with
`C_F(t) ⊆ D`.  Then, in the quotient `F ⧸ D`:

* the automorphism `τ` induced by `t` is involutive and fixed-point-free
  (`C_F(t) ⊆ D` plus coprime fixed points on cosets, Glauberman's lemma);
* hence `τ` is inversion of `F ⧸ D`;
* for `y ∈ P` the induced automorphism `ξ` satisfies `τ ξ τ⁻¹ = ξ⁻¹` (as `t` inverts `y`) and has
  odd order, so `ξ = ξ⁻¹`, `ξ² = 1`, `ξ = 1`;
* hence `[P, F] ⊆ D`.

The automorphism-level and quotient-level forms of this argument are proved in this file:

* `mulAut_eq_inv_of_fixedPointFree`, `eq_one_of_mulAut_of_inverted`;
* `quotMulAut`, `trickCoset`.

## The two remaining steps

1. **`endgame`**: instantiate `trickCoset` for `F = F(K)` and `D = (C_F(P))^F` (the `F`-normal
   closure of `C_F(P)`), obtaining `[P, F] ⊆ D`.  The hypothesis `C_F(t) ⊆ C_F(P)` is available
   once the reduction below has been carried out.
2. **Final contradiction**: from `[P,F] ⊆ (C_F(P))^F` conclude `P ≤ O_p(K)`.  This is the open
   point.  Caution: the naive strengthening `[P,F] ⊆ (C_F(P))^F → [P,F] = 1` is false in general
   (`F = Z₃²`, `P` of order `3` acting as a transvection: `[P,F] = C_F(P)` is a line), so the
   hypothesis `C_F(t) ⊆ C_F(P)` — equivalently `t` inverting `P` with `C_F(t) ⊆ C_F(P)` — must be
   used.  In the reduced situation the target is `P = 1` (since `O_p(K) = 1`).

## Reduction to the reduced situation (`O_p(K) = 1`, `K = N ⋊ P`, `|P| = p`, `C_K(t) ⊆ C_K(P)`)

Strong induction on `|K|`:

* if `O_p(K) ≠ 1`, pass to `K/O_p(K)`.  The hypotheses carry over: `[P,t] = P` via
  `Subgroup.map_commutator`/`map_zpowers'`, and `C_{X/Y}(tY) ⊆ N_{X/Y}(PY/Y)` via
  `Work.DSTR.centralizer_quotient_le` together with `Work.DSTR.map_normalizer_le` (both in
  `Submission/Work/DSTR/d110iOdd.lean`).  Finally `O_p(K/O_p(K)) = 1`
  (`OddOrder.Isaacs.Ch04.opCore_quotient_opCore_eq_bot` bridged by
  `Work.CORE2A.pCore_eq_opCore`).
* otherwise replace `K` by `⟨P^K⟩` (the induction applies, and `O_p(⟨P^K⟩) ≤ O_p(K)`).
* then `K = ⟨P^K⟩`, `O_p(K) = 1`.  Take `N ⊴ K` maximal normal and `t`-invariant; applying the
  induction to `N` and to `PN` forces `K = PN`, `P ∩ N = 1`, and `K/N ≅ P` is a chief factor
  carrying the trivial `K`-action, so `K/N ≅ Z_p` and `P = ⟨x⟩` with `x^p = 1`.
* in `K = N ⋊ ⟨x⟩` one computes `N_K(⟨x⟩) = C_N(σ)·⟨x⟩ = C_K(x)` (`σ = conj_x`), so `hN` gives
  `C_K(t) ⊆ C_K(P)`, whence `C_F(t) ⊆ C_F(P)`.
-/
import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.DSTR.invTrickAbelian
import Submission.Work.DSTR.invTrickSolvable
import Submission.Work.DSTR.centralizerQuotientNormalizer
import Submission.Work.DSTR.fittingSelfCentralizing
import Submission.Work.CORE2A.thm26_aux
import Submission.OddOrder.FeitThompson
import Submission.OddOrder.BG.Ch3_MaximalSubgroups.S10_HallStructureCore

namespace Work.DSTR

open Subgroup

open scoped commutatorElement

/-! ## The inversion trick at the level of automorphisms -/

/-- An involutive fixed-point-free automorphism of a finite group is the inversion map. -/
theorem mulAut_eq_inv_of_fixedPointFree {M : Type*} [Group M] [Finite M] (τ : MulAut M)
    (hfp : MonoidHom.FixedPointFree τ) (hτ2 : τ * τ = 1) :
    ∀ m : M, τ m = m⁻¹ := by
  have hinv : Function.Involutive (τ : M → M) := by
    intro m
    have h : (τ * τ) m = (1 : MulAut M) m := by rw [hτ2]
    simpa [MulAut.mul_apply] using h
  have h := MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hfp hinv
  exact fun m => congrFun h m

/-- **The inversion trick.**  Let `τ, ξ` be automorphisms of a finite group `M` with `τ` an
involutive fixed-point-free automorphism and `τ ξ τ⁻¹ = ξ⁻¹`.  If `ξ` has odd order then
`ξ = 1`. -/
theorem eq_one_of_mulAut_of_inverted {M : Type*} [Group M] [Finite M] (τ ξ : MulAut M)
    (hfp : MonoidHom.FixedPointFree τ) (hτ2 : τ * τ = 1)
    (hconj : τ * ξ * τ⁻¹ = ξ⁻¹) (hodd : Odd (orderOf ξ)) : ξ = 1 := by
  have hτinv : ∀ m : M, (τ : M → M) m = m⁻¹ := mulAut_eq_inv_of_fixedPointFree τ hfp hτ2
  have hτinveq : τ⁻¹ = τ := by
    have h1 : τ⁻¹ * (τ * τ) = τ⁻¹ * 1 := by rw [hτ2]
    rw [← mul_assoc, inv_mul_cancel, one_mul, mul_one] at h1
    exact h1.symm
  have hτinv' : ∀ m : M, ((τ⁻¹ : MulAut M) : M → M) m = m⁻¹ := by
    intro m; rw [hτinveq]; exact hτinv m
  have h_eq : ∀ m : M, (ξ : M → M) m = ((ξ⁻¹ : MulAut M) : M → M) m := by
    intro m
    have h := congrArg (fun f : MulAut M => f m) hconj
    simp only [MulAut.mul_apply] at h
    rw [hτinv', hτinv] at h
    have h2 : ((ξ : M → M) (m⁻¹))⁻¹ = (ξ : M → M) m := by rw [map_inv]; simp
    rw [h2] at h
    exact h
  have hsq : ξ ^ 2 = 1 := by
    ext m
    have h1 : (ξ : M → M) ((ξ : M → M) m) = ((ξ⁻¹ : MulAut M) : M → M) ((ξ : M → M) m) :=
      h_eq ((ξ : M → M) m)
    have h2 : ((ξ⁻¹ : MulAut M) : M → M) ((ξ : M → M) m) = m := by simp
    rw [pow_two]
    simp only [MulAut.mul_apply]
    exact h1.trans h2
  have hdvd : orderOf ξ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
  have hle : orderOf ξ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < orderOf ξ := orderOf_pos ξ
  obtain ⟨k, hk⟩ := hodd
  have : orderOf ξ = 1 := by omega
  exact orderOf_eq_one_iff.mp this

/-! ## The same trick modulo a normal subgroup -/

variable {F : Type*} [Group F] {D : Subgroup F} [D.Normal]

/-- The automorphism of `F ⧸ D` induced by an automorphism `τ` of `F` preserving `D`. -/
def quotMulAut (τ : MulAut F) (hτ : ∀ x : F, x ∈ D ↔ τ x ∈ D) : MulAut (F ⧸ D) :=
  QuotientGroup.congr D D (τ : F ≃* F) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact (hτ y).mp hy
    · intro hx
      exact ⟨τ⁻¹ x, (hτ (τ⁻¹ x)).mpr (by simpa using hx), by simp⟩)

theorem quotMulAut_apply (τ : MulAut F) (hτ : ∀ x : F, x ∈ D ↔ τ x ∈ D) (x : F) :
    quotMulAut τ hτ (QuotientGroup.mk' D x) = QuotientGroup.mk' D (τ x) :=
  QuotientGroup.congr_apply D D (τ : F ≃* F) _ x

theorem quotMulAut_inv_apply (τ : MulAut F) (hτ : ∀ x : F, x ∈ D ↔ τ x ∈ D) (x : F) :
    (quotMulAut τ hτ)⁻¹ (QuotientGroup.mk' D x) = QuotientGroup.mk' D (τ⁻¹ x) := by
  have h1 : quotMulAut τ hτ (QuotientGroup.mk' D (τ⁻¹ x)) = QuotientGroup.mk' D x := by
    rw [quotMulAut_apply]
    simp
  rw [← h1]
  exact MulAut.inv_apply_self (F ⧸ D) (quotMulAut τ hτ) _

theorem quotMulAut_pow_apply (τ : MulAut F) (hτ : ∀ x : F, x ∈ D ↔ τ x ∈ D) (n : ℕ) (x : F) :
    (quotMulAut τ hτ ^ n) (QuotientGroup.mk' D x) = QuotientGroup.mk' D ((τ ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, quotMulAut_apply, pow_succ', MulAut.mul_apply]

/-- **Coset form of the inversion trick.**  Let `τ, ξ` be automorphisms of a finite group `F`
preserving a normal subgroup `D`, with `τ` an involution acting fixed-point-freely on `F ⧸ D`
(`τ x * x⁻¹ ∈ D → x ∈ D`), `ξ` of odd order, and `τ ξ τ⁻¹ ≡ ξ⁻¹` modulo `D`.  Then `ξ` acts
trivially on `F ⧸ D`. -/
theorem trickCoset (τ ξ : MulAut F) [Finite F]
    (hτ : ∀ x : F, x ∈ D ↔ τ x ∈ D) (hξ : ∀ x : F, x ∈ D ↔ ξ x ∈ D)
    (hτ2 : τ * τ = 1) (hfp : ∀ x : F, τ x * x⁻¹ ∈ D → x ∈ D)
    (hodd : Odd (orderOf ξ))
    (hconj : ∀ x : F, (τ * ξ * τ⁻¹) x * (ξ⁻¹ x)⁻¹ ∈ D) :
    ∀ x : F, ξ x * x⁻¹ ∈ D := by
  set τq := quotMulAut τ hτ with hτq
  set ξq := quotMulAut ξ hξ with hξq
  have hτq2 : τq * τq = 1 := by
    rw [show τq * τq = τq ^ 2 by rw [pow_two]]
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D q
    rw [hτq, quotMulAut_pow_apply]
    have h2 : (τ ^ 2) x = x := by
      have := congrArg (fun f : MulAut F => f x) hτ2
      simpa [pow_two, MulAut.mul_apply] using this
    rw [h2]
    rfl
  have hfpq : MonoidHom.FixedPointFree τq := by
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D q
    rw [hτq, quotMulAut_apply] at hq
    have hmem : τ x * x⁻¹ ∈ D := by
      have h1 := QuotientGroup.eq_iff_div_mem.mp hq
      simpa [div_eq_mul_inv] using h1
    have hxD : x ∈ D := hfp x hmem
    simpa using (QuotientGroup.eq_one_iff x).mpr hxD
  have hconjq : τq * ξq * τq⁻¹ = ξq⁻¹ := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D q
    have hL : (τq * ξq * τq⁻¹) (QuotientGroup.mk' D x) =
        QuotientGroup.mk' D ((τ * ξ * τ⁻¹) x) := by
      rw [hτq, hξq, MulAut.mul_apply, MulAut.mul_apply, quotMulAut_inv_apply, quotMulAut_apply,
        quotMulAut_apply]
      rfl
    have hR : (ξq⁻¹) (QuotientGroup.mk' D x) = QuotientGroup.mk' D (ξ⁻¹ x) := by
      rw [hξq, quotMulAut_inv_apply]
    rw [hL, hR]
    have h := hconj x
    rw [show ((τ * ξ * τ⁻¹) x * (ξ⁻¹ x)⁻¹) = (τ * ξ * τ⁻¹) x / (ξ⁻¹ x) from
      (div_eq_mul_inv _ _).symm, ← QuotientGroup.eq_iff_div_mem] at h
    simpa using h
  have hoddq : Odd (orderOf ξq) := by
    have hpow : ξq ^ orderOf ξ = 1 := by
      ext q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D q
      rw [hξq, quotMulAut_pow_apply, pow_orderOf_eq_one]
      simp
    have hdvd : orderOf ξq ∣ orderOf ξ := orderOf_dvd_iff_pow_eq_one.mpr hpow
    exact Odd.of_dvd_nat hodd hdvd
  have hξq1 : ξq = 1 := eq_one_of_mulAut_of_inverted τq ξq hfpq hτq2 hconjq hoddq
  intro x
  have h := congrArg (fun f : MulAut (F ⧸ D) => f (QuotientGroup.mk' D x)) hξq1
  simp only [MulAut.one_apply] at h
  rw [hξq, quotMulAut_apply] at h
  have h1 := QuotientGroup.eq_iff_div_mem.mp h
  simpa [div_eq_mul_inv] using h1

/-! ## The endgame: `[P, F] ⊆ D` -/

/-- The order of an element of a `p`-group is a power of `p`, hence odd for `p ≠ 2`. -/
theorem odd_orderOf_of_mem_isPGroup {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) {P : Subgroup X} (hP : IsPGroup p P) {y : X} (hy : y ∈ P) :
    Odd (orderOf y) := by
  have h1 : IsPGroup p (Subgroup.zpowers y) := hP.to_le (Subgroup.zpowers_le.mpr hy)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h1
  rw [Nat.card_zpowers] at hn
  rw [hn]
  exact Odd.pow ((Fact.out : p.Prime).odd_of_ne_two hp)

/-- **The endgame of the odd-core step.**  Let `F ⊴ X` be a finite normal subgroup, `D ⊴ F` a
`t`- and `P`-invariant normal subgroup of `F` containing the `t`-fixed points of `F`, and let the
`p`-subgroup `P` (with `p ≠ 2`) be inverted by `t`.  Then `[P, F] ⊆ D`. -/
theorem commutator_le_of_inverted {X : Type} [Group X] [Finite X] {F : Subgroup X} [F.Normal]
    {D : Subgroup F} [D.Normal] {t : X} (ht : orderOf t = 2) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {P : Subgroup X} (hP : IsPGroup p P)
    (hDt : ∀ x : F, MulAut.conjNormal t x ∈ D ↔ x ∈ D)
    (hDP : ∀ y ∈ P, ∀ x : F, MulAut.conjNormal y x ∈ D ↔ x ∈ D)
    (hinv : ∀ y ∈ P, t * y * t⁻¹ = y⁻¹)
    (hFPF : ∀ x : F, MulAut.conjNormal t x * x⁻¹ ∈ D → x ∈ D) :
    ∀ y ∈ P, ∀ x : F, MulAut.conjNormal y x * x⁻¹ ∈ D := by
  intro y hy
  set φ : X →* MulAut ↥F := MulAut.conjNormal with hφ
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    simpa [pow_two] using h
  have hα2 : φ t * φ t = 1 := by
    rw [← map_mul, ht2, map_one]
  have hβodd : Odd (orderOf (φ y)) := by
    have hpow : (φ y) ^ (orderOf y) = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hdvd : orderOf (φ y) ∣ orderOf y := orderOf_dvd_iff_pow_eq_one.mpr hpow
    exact Odd.of_dvd_nat (odd_orderOf_of_mem_isPGroup hp hP hy) hdvd
  have hconj : ∀ x : ↥F, (φ t * φ y * (φ t)⁻¹) x * (((φ y)⁻¹) x)⁻¹ ∈ D := by
    intro x
    have h3 : φ t * φ y * (φ t)⁻¹ = φ (t * y * t⁻¹) := by
      rw [← map_inv, ← map_mul, ← map_mul]
    rw [h3, ← map_inv, hinv y hy]
    simp
  have hmain := trickCoset (φ t) (φ y) (by
      intro x
      have := hDt x
      rw [hφ] at this
      exact this.symm) (by
      intro x
      have := hDP y hy x
      rw [hφ] at this
      exact this.symm) hα2
    (by
      intro x
      have := hFPF x
      rw [hφ] at this
      simpa using this) hβodd hconj
  intro x
  have := hmain x
  rw [hφ] at this
  simpa using this

/-! ## The reduced case `O_p(K) = 1` -/

section ReducedCore

variable {X : Type} [Group X] [Finite X]

/-- `t` inverts `⁅x,t⁆` when `t * t = 1`. -/
theorem conj_commutatorElement_eq_inv {t x : X} (ht2 : t * t = 1) :
    t * ⁅x, t⁆ * t⁻¹ = ⁅x, t⁆⁻¹ := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have h1 : t * ⁅x, t⁆ * t⁻¹ = (t * x * t) * x⁻¹ := by
    rw [commutatorElement_def, ht']
    calc t * (x * t * x⁻¹ * t) * t = t * (x * t * x⁻¹) * (t * t) := by group
      _ = t * (x * t * x⁻¹) * 1 := by rw [ht2]
      _ = (t * x * t) * x⁻¹ := by group
  have h2 : ⁅x, t⁆⁻¹ = (t * x * t) * x⁻¹ := by
    rw [commutatorElement_def]
    simp only [mul_inv_rev, inv_inv]
    rw [ht']
    group
  rw [h1, h2]

/-- An element `x` inverted by `t` (odd order, coprime to `|F|`) whose `t`-fixed points in the
normal subgroup `F` are `x`-fixed, centralises `F`. -/
theorem centralizes_of_inverted {F : Subgroup X} [F.Normal] (hFsolv : Group.IsSolvable ↥F)
    (hFodd : Odd (Nat.card ↥F)) {t x : X} (ht : orderOf t = 2) (hxodd : Odd (orderOf x))
    (hcop : Nat.Coprime (orderOf x) (Nat.card ↥F)) (htx : t * x * t⁻¹ = x⁻¹)
    (hfix : ∀ f : F, MulAut.conjNormal t f = f → MulAut.conjNormal x f = f) :
    x ∈ Subgroup.centralizer (F : Set X) := by
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht, pow_two] at h
    exact h
  have hξ1 : MulAut.conjNormal (H := F) x = 1 := by
    refine invTrickSolvable hFsolv hFodd (τ := MulAut.conjNormal (H := F) t)
      (ξ := MulAut.conjNormal (H := F) x) ?_ ?_ ?_ ?_ hfix
    · rw [← map_mul, ht2, map_one]
    · exact Nat.Coprime.coprime_dvd_left
        (orderOf_map_dvd (MulAut.conjNormal (H := F) : X →* MulAut ↥F) x) hcop
    · exact Odd.of_dvd_nat hxodd (orderOf_map_dvd (MulAut.conjNormal (H := F) : X →* MulAut ↥F) x)
    · have h3 : MulAut.conjNormal (H := F) t * MulAut.conjNormal (H := F) x *
          (MulAut.conjNormal (H := F) t)⁻¹ = MulAut.conjNormal (H := F) (t * x * t⁻¹) := by
        rw [← map_inv, ← map_mul, ← map_mul]
      rw [h3, htx, map_inv]
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h := congrArg (fun (e : MulAut ↥F) => ((e ⟨y, hy⟩ : ↥F) : X)) hξ1
  simp only [MulAut.one_apply, Subgroup.coe_one] at h
  rw [MulAut.conjNormal_apply (H := F)] at h
  have h2 : x * y = y * x := by
    have h3 : x * y * x⁻¹ = y := h
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [h3]
  exact h2.symm

/-- **The reduced case of the odd core step** (`O_p(K) = ⊥`): then `P = ⊥`. -/
theorem coreOddReducedEngine {K : Subgroup X} [K.Normal] (hKodd : Odd (Nat.card K))
    {t : X} (ht : orderOf t = 2) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {P : Subgroup X}
    (hP : IsPGroup p P) (hPK : P ≤ K)
    (hN : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (P : Set X))
    (hcomm : ⁅P, Subgroup.zpowers t⁆ = P)
    (hcore : Work.GW2.pCore p ↥K = ⊥) : P = ⊥ := by
  classical
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht, pow_two] at h
    exact h
  have htN : t ∈ Subgroup.normalizer (P : Set X) :=
    hN (by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy])
  -- the Fitting subgroup of `K`, viewed in `X`
  set F : Subgroup X := Work.GW2.fittingIn K with hFdef
  have hleFK : F ≤ K := Subgroup.map_subtype_le _
  haveI hchar : (Work.GW2.fitting ↥K).Characteristic := by
    rw [Work.CORE2A.fitting_eq_isaacsFitting]
    exact OddOrder.Isaacs.Ch01.fitting.characteristic ↥K
  haveI hFnorm : F.Normal := by
    rw [hFdef, Work.GW2.fittingIn]
    exact ConjAct.normal_of_characteristic_of_normal
  have hFodd : Odd (Nat.card ↥F) := hKodd.of_dvd_nat (Subgroup.card_dvd_of_le hleFK)
  -- `F` has no nontrivial `p`-subgroups, because those lie in `O_p(K) = ⊥`
  have hNoP : ∀ W : Subgroup X, W ≤ F → IsPGroup p W → W = ⊥ := by
    intro W hW hWp
    have hWK : W ≤ K := hW.trans hleFK
    have hW'' : W.subgroupOf K ≤ Work.GW2.fitting ↥K := by
      intro y hy
      rw [Subgroup.mem_subgroupOf] at hy
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (hW hy)
      have hzy' : z = y := Subtype.ext hzy
      rwa [hzy'] at hz
    have hW' : W.subgroupOf K ≤ OddOrder.Isaacs.Ch01.fitting ↥K := by
      rwa [Work.CORE2A.fitting_eq_isaacsFitting] at hW''
    have hWp' : IsPGroup p ↥(W.subgroupOf K) :=
      hWp.of_injective (Subgroup.subgroupOfEquivOfLe hWK).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hWK).injective
    have hstep := OddOrder.BG.Ch3.S10.pSubgroup_le_opCore_of_le_fitting (G := ↥K) hWp' hW'
    rw [Work.CORE2A.pCore_eq_opCore] at hcore
    have hbot : W.subgroupOf K = ⊥ := le_bot_iff.mp (hcore ▸ hstep)
    rw [eq_bot_iff]
    intro x hx
    have hxK : x ∈ K := hWK hx
    have hx' : (⟨x, hxK⟩ : ↥K) ∈ W.subgroupOf K := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    rw [hbot] at hx'
    simpa using hx'
  have hPF : P ⊓ F = ⊥ := hNoP (P ⊓ F) inf_le_right (hP.to_le inf_le_left)
  have hFcop : Nat.Coprime p (Nat.card ↥F) := by
    haveI : Fintype ↥F := Fintype.ofFinite _
    by_contra h
    have hdvd : p ∣ Fintype.card ↥F := by
      have h' := (Nat.Prime.dvd_iff_not_coprime (Fact.out : p.Prime)).mpr h
      simpa only [Nat.card_eq_fintype_card] using h'
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p hdvd
    have hzple : Subgroup.zpowers (x : X) ≤ F := by
      refine Subgroup.zpowers_le.mpr ?_
      exact x.2
    have hzpp : IsPGroup p ↥(Subgroup.zpowers (x : X)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_coe x, hx, pow_one]
    have hbot := hNoP (Subgroup.zpowers (x : X)) hzple hzpp
    have hx1 : (x : X) = 1 := Subgroup.zpowers_eq_bot.mp hbot
    have : orderOf (x : X) = 1 := by rw [hx1, orderOf_one]
    rw [Subgroup.orderOf_coe x, hx] at this
    exact (Fact.out : p.Prime).ne_one this
  -- `t`-fixed points of `F` centralise `P`
  have hFixP : ∀ c : F, MulAut.conjNormal t c = c → ∀ y ∈ P, y * c = c * y := by
    intro c hc y hy
    have hct : t * (c : X) * t⁻¹ = (c : X) := by
      have h : ((MulAut.conjNormal t c : ↥F) : X) = ((c : ↥F) : X) := by rw [hc]
      have h2 : ((MulAut.conjNormal t c : ↥F) : X) = t * (c : X) * t⁻¹ :=
        MulAut.conjNormal_apply (H := F) t c
      rw [h2] at h
      exact h
    have hct' : t * (c : X) = (c : X) * t := by
      calc t * (c : X) = (t * (c : X) * t⁻¹) * t := by group
        _ = (c : X) * t := by rw [hct]
    have hcC : (c : X) ∈ Subgroup.centralizer ({t} : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hct'
    have hcN : (c : X) ∈ Subgroup.normalizer (P : Set X) := hN hcC
    have hmemP : y⁻¹ * (c : X)⁻¹ * y * (c : X) ∈ P := by
      have h2 : (c : X)⁻¹ * y * (c : X) ∈ P := by
        simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcN) y).mp hy
      simpa [mul_assoc] using P.mul_mem (P.inv_mem hy) h2
    have hmemF : y⁻¹ * (c : X)⁻¹ * y * (c : X) ∈ F := by
      have h1 : y⁻¹ * (c : X)⁻¹ * y ∈ F := by
        have := hFnorm.conj_mem ((c : X)⁻¹) (F.inv_mem c.2) y⁻¹
        simpa [mul_assoc] using this
      exact F.mul_mem h1 c.2
    have hone : y⁻¹ * (c : X)⁻¹ * y * (c : X) = 1 := by
      have : y⁻¹ * (c : X)⁻¹ * y * (c : X) ∈ P ⊓ F := ⟨hmemP, hmemF⟩
      rw [hPF] at this
      simpa using this
    have hyc : y * (c : X) = (c : X) * y := by
      have h2 : y⁻¹ * (c : X)⁻¹ * y = (c : X)⁻¹ := by
        have h4 : y⁻¹ * (c : X)⁻¹ * y * (c : X) = 1 := hone
        calc y⁻¹ * (c : X)⁻¹ * y = y⁻¹ * (c : X)⁻¹ * y * (c : X) * (c : X)⁻¹ := by group
          _ = 1 * (c : X)⁻¹ := by rw [h4]
          _ = (c : X)⁻¹ := by group
      have h3 : y⁻¹ * (c : X) * y = (c : X) := by
        have := congrArg Inv.inv h2
        simpa [mul_assoc] using this
      calc y * (c : X) = y * (y⁻¹ * (c : X) * y) := by rw [h3]
        _ = (c : X) * y := by group
    exact hyc
  -- `P` is generated by the elements it inverts
  have hCenF : P ≤ Subgroup.centralizer (F : Set X) := by
    rw [← hcomm, Subgroup.commutator_le]
    intro x hx y hy
    -- `zpowers t = {1, t}` since `orderOf t = 2`
    have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have hycase : y = 1 ∨ y = t := by
      have hS : Subgroup.zpowers t ≤
          ({ carrier := ({1, t} : Set X)
             mul_mem' := by rintro a b (rfl | rfl) (rfl | rfl) <;> simp [ht2]
             one_mem' := by simp
             inv_mem' := by rintro a (rfl | rfl) <;> simp [ht'] } : Subgroup X) :=
        Subgroup.zpowers_le.mpr (by simp)
      have := hS hy
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    rcases hycase with h1 | h1
    · rw [h1, commutatorElement_one_right]
      exact Subgroup.one_mem _
    · rw [h1]
      have hgP : ⁅x, t⁆ ∈ P := by
        have h1 : ⁅x, t⁆ = x * (t * x⁻¹ * t⁻¹) := by
          rw [commutatorElement_def]
          group
        have h2 : t * x⁻¹ * t⁻¹ ∈ P :=
          (Subgroup.mem_normalizer_iff.mp htN x⁻¹).mp (P.inv_mem hx)
        rw [h1]
        exact P.mul_mem hx h2
      have hgt : t * ⁅x, t⁆ * t⁻¹ = ⁅x, t⁆⁻¹ := conj_commutatorElement_eq_inv ht2
      have hgodd : Odd (orderOf ⁅x, t⁆) := odd_orderOf_of_mem_isPGroup hp hP hgP
      have hgcop : Nat.Coprime (orderOf ⁅x, t⁆) (Nat.card ↥F) := by
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
        have hdvd : orderOf ⁅x, t⁆ ∣ p ^ k := by
          rw [← Nat.card_zpowers, ← hk]
          exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hgP)
        exact Nat.Coprime.coprime_dvd_left hdvd (hFcop.pow_left k)
      exact centralizes_of_inverted (OddOrder.feitThompson hFodd) hFodd ht hgodd hgcop hgt
        (fun f hf => by
          have hyf : ⁅x, t⁆ * (f : X) = (f : X) * ⁅x, t⁆ := hFixP f hf ⁅x, t⁆ hgP
          refine Subtype.ext ?_
          rw [show (((MulAut.conjNormal ⁅x, t⁆) f : ↥F) : X) =
              ⁅x, t⁆ * (f : X) * ⁅x, t⁆⁻¹ from MulAut.conjNormal_apply (H := F) ⁅x, t⁆ f]
          rw [show ⁅x, t⁆ * (f : X) * ⁅x, t⁆⁻¹ = (f : X) from by rw [hyf]; group])
  -- Bender 1.2 and the end
  have hFsolvK : Group.IsSolvable ↥K := OddOrder.feitThompson hKodd
  have hBender : Subgroup.centralizer ((Work.GW2.fitting ↥K : Subgroup ↥K) : Set ↥K) ≤
      Work.GW2.fitting ↥K := fittingSelfCentralizing ↥K hFsolvK
  have hPK2 : P ≤ F := by
    intro y hy
    have hycen : (⟨y, hPK hy⟩ : ↥K) ∈
        Subgroup.centralizer ((Work.GW2.fitting ↥K : Subgroup ↥K) : Set ↥K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzF : ((z : ↥K) : X) ∈ F := by
        rw [hFdef, Work.GW2.fittingIn]
        exact Subgroup.mem_map_of_mem K.subtype hz
      have hzy := hCenF hy ((z : ↥K) : X) hzF
      refine Subtype.ext ?_
      show ((z : ↥K) : X) * y = y * ((z : ↥K) : X)
      exact hzy
    rw [hFdef, Work.GW2.fittingIn]
    exact Subgroup.mem_map_of_mem K.subtype (hBender hycen)
  rw [eq_bot_iff]
  intro y hy
  have hmem : y ∈ P ⊓ F := ⟨hy, hPK2 hy⟩
  rw [hPF] at hmem
  simpa using hmem

end ReducedCore

/-! ## The target -/

section Target

variable {X : Type} [Group X] [Finite X]

/-- The image of a cyclic subgroup is the cyclic subgroup generated by the image.
(Mathlib has no `Subgroup.map_zpowers`.) -/
theorem map_zpowers' {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
    (Subgroup.zpowers g).map f = Subgroup.zpowers (f g) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Subgroup.mem_map_of_mem f (Subgroup.subset_closure (by simp))

/-- Strong-induction form of the odd-core step.  The reduced case (`O_p(K) = ⊥`) is
`coreOddReducedEngine`; the quotient case is reduced to the induction hypothesis. -/
private theorem coreOddStep_aux : ∀ (n : ℕ) {X : Type} [Group X] [Finite X]
    {K : Subgroup X} [K.Normal], Nat.card K = n → Odd (Nat.card K) →
    ∀ {t : X}, orderOf t = 2 → ∀ {p : ℕ} [Fact p.Prime], p ≠ 2 →
    ∀ {P : Subgroup X}, IsPGroup p P → P ≤ K →
    Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (P : Set X) →
    ⁅P, Subgroup.zpowers t⁆ = P → P ≤ Work.GW2.pCoreIn p K := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X _ _ K _ hcard hKodd t ht p _ hp P hP hPK hN hcomm
    have ht2 : t * t = 1 := by
      have h := pow_orderOf_eq_one t
      rw [ht, pow_two] at h
      exact h
    by_cases hcore : Work.GW2.pCore p ↥K = ⊥
    · have hbot : P = ⊥ := coreOddReducedEngine hKodd ht hp hP hPK hN hcomm hcore
      rw [hbot, Work.GW2.pCoreIn, hcore, Subgroup.map_bot]
    · -- `O_p(K) ≠ 1`: pass to `K / O_p(K)`
      set Z : Subgroup X := Work.GW2.pCoreIn p K with hZdef
      have hZK : Z ≤ K := Subgroup.map_subtype_le _
      have hZne : Z ≠ ⊥ := by
        intro hbot
        apply hcore
        rw [eq_bot_iff]
        intro x hx
        have hxZ : K.subtype x ∈ Z := by
          rw [hZdef, Work.GW2.pCoreIn]
          exact Subgroup.mem_map_of_mem K.subtype hx
        rw [hbot] at hxZ
        simpa using hxZ
      have hZpg : IsPGroup p ↥Z := by
        rw [hZdef, Work.GW2.pCoreIn, Work.CORE2A.pCore_eq_opCore]
        exact (OddOrder.Isaacs.Ch01.opCore_isPGroup p ↥K).map K.subtype
      have hZodd : Odd (Nat.card ↥Z) := by
        obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hZpg
        rw [hm]
        exact Odd.pow ((Fact.out : p.Prime).odd_of_ne_two hp)
      haveI hZnorm : Z.Normal := by
        rw [hZdef]
        haveI hchar : (Work.GW2.pCore p ↥K).Characteristic := by
          rw [Work.CORE2A.pCore_eq_opCore]
          exact OddOrder.Isaacs.Ch01.opCore.characteristic p ↥K
        exact ConjAct.normal_of_characteristic_of_normal
      set π : X →* X ⧸ Z := QuotientGroup.mk' Z with hπ
      -- `t ∉ Z`, so `π t` is an involution
      have htZ : t ∉ Z := by
        intro htmem
        have h2 : 2 ∣ Nat.card ↥Z := by
          have hsub : Subgroup.zpowers t ≤ Z := Subgroup.zpowers_le.mpr htmem
          have hcd := Subgroup.card_dvd_of_le hsub
          rwa [Nat.card_zpowers, ht] at hcd
        exact (Nat.not_even_iff_odd.mpr hZodd) (even_iff_two_dvd.mpr h2)
      have htb : orderOf (π t) = 2 := by
        refine orderOf_eq_prime ?_ ?_
        · rw [← map_pow, show t ^ 2 = 1 by rw [pow_two]; exact ht2, map_one]
        · intro hcon
          exact htZ ((QuotientGroup.eq_one_iff t).mp (by rw [hπ] at hcon; exact hcon))
      -- the quotient datum is strictly smaller
      have hKbodd : Odd (Nat.card ↥(K.map π)) := hKodd.of_dvd_nat (Subgroup.card_map_dvd K π)
      have hlt : Nat.card ↥(K.map π) < Nat.card ↥K := by
        have hker' : (π.comp K.subtype).ker = Z.subgroupOf K := by
          ext y
          rw [MonoidHom.mem_ker]
          exact QuotientGroup.eq_one_iff (y : X)
        have hrange' : (π.comp K.subtype).range = K.map π := by
          ext z
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact Subgroup.mem_map_of_mem π y.2
          · rintro ⟨w, hw, rfl⟩
            exact ⟨⟨w, hw⟩, rfl⟩
        have hcard' := Subgroup.card_ker_mul_card_range (π.comp K.subtype)
        rw [hrange', hker'] at hcard'
        have hZ2 : 2 ≤ Nat.card ↥(Z.subgroupOf K) := by
          have hcardZ : Nat.card ↥(Z.subgroupOf K) = Nat.card ↥Z :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv
          haveI : Fintype ↥Z := Fintype.ofFinite _
          haveI : Nontrivial ↥Z := (Subgroup.nontrivial_iff_ne_bot Z).mpr hZne
          have h1 : 1 < Nat.card ↥Z := by
            have := Fintype.one_lt_card (α := ↥Z)
            simpa using this
          omega
        have hb1 : 0 < Nat.card ↥(K.map π) := Nat.card_pos
        have hstep : Nat.card ↥(K.map π) <
            Nat.card ↥(Z.subgroupOf K) * Nat.card ↥(K.map π) := by
          calc Nat.card ↥(K.map π) = 1 * Nat.card ↥(K.map π) := (one_mul _).symm
            _ < Nat.card ↥(Z.subgroupOf K) * Nat.card ↥(K.map π) :=
                Nat.mul_lt_mul_of_pos_right (by omega) hb1
        have hfin : Nat.card ↥(K.map π) < Nat.card ↥K := by
          rw [← hcard']
          exact hstep
        exact hfin
      -- the hypotheses transport to the quotient
      have hNb : Subgroup.centralizer ({π t} : Set (X ⧸ Z)) ≤
          Subgroup.normalizer ((P.map π : Subgroup (X ⧸ Z)) : Set (X ⧸ Z)) :=
        centralizerQuotientNormalizer hZodd ht hN
      have hcommb : ⁅P.map π, Subgroup.zpowers (π t)⁆ = P.map π := by
        rw [← map_zpowers' π t, ← Subgroup.map_commutator, hcomm]
      have hIH := ih (Nat.card ↥(K.map π)) (by rw [← hcard]; exact hlt) (K := K.map π) rfl hKbodd htb hp
        (hP.map π) (Subgroup.map_mono hPK) hNb hcommb
      -- the preimage of `O_p(K/Z)` is a normal `p`-subgroup of `K` containing `P`
      set N : Subgroup X := (Work.GW2.pCoreIn p (K.map π)).comap π with hNdef
      have hPN : P ≤ N := by
        intro y hy
        rw [hNdef]
        exact hIH (Subgroup.mem_map_of_mem π hy)
      have hNnormal : N.Normal := by
        haveI hchar : (Work.GW2.pCore p ↥(K.map π)).Characteristic := by
          rw [Work.CORE2A.pCore_eq_opCore]
          exact OddOrder.Isaacs.Ch01.opCore.characteristic p ↥(K.map π)
        haveI hHnorm : (Work.GW2.pCoreIn p (K.map π)).Normal := by
          rw [Work.GW2.pCoreIn]
          exact ConjAct.normal_of_characteristic_of_normal
        rw [hNdef]
        exact hHnorm.comap π
      have hNK : N.subgroupOf K ≤ Work.GW2.pCore p ↥K := by
        have hZleN : Z ≤ N := by
          intro z hz
          rw [hNdef]
          show π z ∈ Work.GW2.pCoreIn p (K.map π)
          rw [show π z = 1 from (QuotientGroup.eq_one_iff z).mpr hz]
          exact Subgroup.one_mem _
        -- `N` is a `p`-group: both `Z` and `N/Z = O_p(K/Z)` are
        have hNpg : IsPGroup p ↥N := by
          have hker' : (π.comp N.subtype).ker = Z.subgroupOf N := by
            ext y
            rw [MonoidHom.mem_ker]
            exact QuotientGroup.eq_one_iff (y : X)
          have hrange' : (π.comp N.subtype).range = N.map π := by
            ext z
            constructor
            · rintro ⟨y, hy, rfl⟩
              exact Subgroup.mem_map_of_mem π y.2
            · rintro ⟨w, hw, rfl⟩
              exact ⟨⟨w, hw⟩, rfl⟩
          have hcard' := Subgroup.card_ker_mul_card_range (π.comp N.subtype)
          rw [hrange', hker'] at hcard'
          have hmap : N.map π = Work.GW2.pCoreIn p (K.map π) := by
            rw [hNdef, Subgroup.map_comap_eq,
              MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Z), top_inf_eq]
          have hpg_range : IsPGroup p ↥(N.map π) := by
            rw [hmap, Work.GW2.pCoreIn, Work.CORE2A.pCore_eq_opCore]
            exact (OddOrder.Isaacs.Ch01.opCore_isPGroup p ↥(K.map π)).map (K.map π).subtype
          have hpg_ker : IsPGroup p ↥(Z.subgroupOf N) := by
            have hcardZ : Nat.card ↥(Z.subgroupOf N) = Nat.card ↥Z :=
              Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleN).toEquiv
            obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp hZpg
            exact IsPGroup.of_card (n := c) (by rw [hcardZ, hc])
          obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hpg_range
          obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hpg_ker
          refine IsPGroup.of_card (n := a + b) ?_
          rw [← hcard', hb, ha, mul_comm (p ^ b) (p ^ a)]
          exact (pow_add p a b).symm
        -- `N ∩ K` is normal in `K`, so it lies in `O_p(K)`
        have hinf_ne : N.subgroupOf K = (N ⊓ K).subgroupOf K := by
          ext y
          simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
          exact ⟨fun h => ⟨h, y.2⟩, fun h => h.1⟩
        rw [hinf_ne, Work.CORE2A.pCore_eq_opCore]
        haveI : (N ⊓ K).Normal :=
          ⟨fun n hn g => ⟨hNnormal.conj_mem n hn.1 g, ‹K.Normal›.conj_mem n hn.2 g⟩⟩
        exact OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore
          (hNpg.to_le inf_le_left |>.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm)
      intro y hy
      have hy' : (⟨y, hPK hy⟩ : ↥K) ∈ N.subgroupOf K := by
        rw [Subgroup.mem_subgroupOf]
        exact hPN hy
      have := hNK hy'
      exact Subgroup.mem_map_of_mem K.subtype this

theorem coreOddStep {X : Type} [Group X] [Finite X]
    {K : Subgroup X} [K.Normal] (hKodd : Odd (Nat.card K))
    {t : X} (ht : orderOf t = 2) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {P : Subgroup X}
    (hP : IsPGroup p P) (hPK : P ≤ K)
    (hN : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (P : Set X))
    (hcomm : ⁅P, Subgroup.zpowers t⁆ = P) :
    P ≤ Work.GW2.pCoreIn p K :=
  coreOddStep_aux (Nat.card K) rfl hKodd ht hp hP hPK hN hcomm

end Target

end Work.DSTR
