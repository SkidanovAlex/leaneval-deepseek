/-
# The layer dichotomy D1 (Peterfalvi II p. 239)

The count of `ξ`-invariant layers of a Suzuki 2-group `P` of order `q³` is carried out on
`V = P / Z(P)`, which is an `𝔽₂`-space of order `q²` once we know

  `(i) ∀ x : P, x ^ 2 ∈ Z(P)`   (equivalently: `P / Z(P)` has exponent two),

from which `[P,P] ≤ Z(P)` follows as well (`x ↦ x ^ 2` is central, `⁅x,y⁆ = (xy)² x⁻² y⁻²`).
Everything else in this file is self-contained: the module structure on
`Additive (P ⧸ Z(P))`, the induced `σ` with `orderOf σ = 2 ^ n - 1` and `Semiregular σ`,
the bridge `Subgroup (P ⧸ Z(P)) ≃ Submodule (𝔽₂) (Additive (P ⧸ Z(P)))`, the invariance
dictionary and the linear-algebra count.

`(i)` is supplied by `Work.Higman.LCD.sq_mem_center_of_fpf`
(`Submission/Work/Higman/LCD/fpf_sq_center.lean`), the `FpfXi` shortcut: in this setting every
`ξ`-invariant subgroup `H` has `|H| ≡ 1 (mod q - 1)`, whence `Z(P) = Ω₁(P)`, every `ξ`-invariant
subgroup of `P` has order `1`, `q`, `q²` or `q³`, and the `C₄` shape `P' = A = P²` is excluded by
Higman's Lemma 8 applied to the cover `C = ⊤` (whose covering hypothesis is automatic here). -/
import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.typeB
import Submission.Work.Higman.LCD.fpf_sq_center
import Submission.Work.Higman.Layers.Defs
import Submission.Work.Higman.Layers.pow_le_card
import Submission.Work.Higman.Layers.dvd_finrank
import Submission.Work.Higman.Layers.exists_minpoly_vec
import Submission.Work.Higman.Layers.exists_two_constituents
import Submission.Work.Higman.Layers.count_eq_one_add_hom
import Submission.Work.Higman.Layers.hom_card_eq_one_or_card
import Submission.Work.Higman.Layers.drift_mem_center
import Submission.Work.Higman.Layers.layers_quotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Work.Higman

open LeanEval.GroupTheory.Defs
open scoped commutatorElement

/-- **The linear-algebra dichotomy.**  Let `V` be a finite `𝔽₂`-space of order `q ^ 2`
(`q = 2 ^ n`) carrying an endomorphism `σ` of order `q - 1` which is semiregular on `V ∖ {0}`.
Then the number of `σ`-invariant subspaces of dimension `n` is `2` or `q + 1`. -/
theorem invSubspaces_card_dichotomy {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {σ : V →ₗ[ZMod 2] V} {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card V = 2 ^ (2 * n))
    (horder : orderOf σ = 2 ^ n - 1) (hsr : Layers.Semiregular σ) :
    Nat.card (Layers.InvSubspaces σ n) = 2 ∨
      Nat.card (Layers.InvSubspaces σ n) = 2 ^ n + 1 := by
  obtain ⟨C₁, C₂, h1, h2, hdisj, hsup, hfr1, hfr2⟩ :=
    Layers.exists_two_constituents hn hcard horder hsr
  have hcount := Layers.count_eq_one_add_hom (n := n) h1 h2 hdisj hsup hfr1 hfr2
  have hC₂ : Nat.card ↥C₂ = 2 ^ n := by
    haveI : Module.Finite (ZMod 2) ↥C₂ := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥C₂), hfr2]
    norm_num
  rcases Layers.hom_card_eq_one_or_card h1 h2 with h | h
  · left
    calc Nat.card (Layers.InvSubspaces σ n)
        = 1 + Nat.card (Layers.HomInv σ C₂ C₁ h2.1 h1.1) := hcount
      _ = 1 + 1 := by rw [h]
      _ = 2 := by norm_num
  · right
    calc Nat.card (Layers.InvSubspaces σ n)
        = 1 + Nat.card (Layers.HomInv σ C₂ C₁ h2.1 h1.1) := hcount
      _ = 1 + Nat.card ↥C₂ := by rw [h]
      _ = 2 ^ n + 1 := by rw [hC₂]; omega

/-- **D1 (dichotomy of layers).**  In a Suzuki 2-group of order `q³` with `ξ` of order `q - 1`
acting semiregularly, the number of `ξ`-invariant layers `Z(P) ≤ M` of order `q²` is `2` or
`q + 1` — corresponding to `P/Z ≅ V₁ ⊕ V₂` with the two constituents non-isomorphic, resp.
isomorphic, `𝔽₂⟨ξ⟩`-modules. -/
theorem layers_card_dichotomy {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {ξ : MulAut P} (hξ : Work.Higman.FpfXi ξ) :
    Nat.card {M : Subgroup P // Work.Higman.IsXiLayer ξ M} = 2 ∨
      Nat.card {M : Subgroup P // Work.Higman.IsXiLayer ξ M} =
        Nat.card ↥(Subgroup.center P) + 1 := by
  classical
  obtain ⟨n, hZn⟩ := center_card_eq_two_pow h
  haveI : Nontrivial ↥(Subgroup.center P) := h.center_nontrivial
  have hn1 : 1 ≤ n := by
    haveI : Fintype ↥(Subgroup.center P) := Fintype.ofFinite _
    have hlt : (1 : ℕ) < 2 ^ n := by
      have hc := Fintype.one_lt_card (α := ↥(Subgroup.center P))
      rw [Fintype.card_eq_nat_card, hZn] at hc
      exact hc
    refine (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp ?_
    rw [pow_one]
    omega
  have hsquares : ∀ x : P, x ^ 2 ∈ Subgroup.center P := LCD.sq_mem_center_of_fpf h hξ
  have hPcard : Nat.card P = 2 ^ (3 * n) := by
    rw [hξ.card_cube, hZn, ← pow_mul, Nat.mul_comm]
  -- `P ⧸ Z(P)` has exponent two, hence is abelian
  have hmulself : ∀ v : P ⧸ Subgroup.center P, v * v = 1 := by
    intro v
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center P) v
    subst hx
    have h1 : (QuotientGroup.mk (x * x) : P ⧸ Subgroup.center P) = 1 :=
      (QuotientGroup.eq_one_iff (x * x)).mpr (by simpa [pow_two] using hsquares x)
    simpa [QuotientGroup.mk'_apply, ← map_mul] using h1
  have hcommQ : ∀ x y : P ⧸ Subgroup.center P, x * y = y * x := by
    intro x y
    have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hmulself x)
    have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hmulself y)
    have hxy : (x * y)⁻¹ = x * y :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hmulself (x * y))
    rw [← hxy, mul_inv_rev, hx, hy]
  -- the additive structure on `V = P ⧸ Z(P)`, built from the group structure
  letI : AddCommGroup (Additive (P ⧸ Subgroup.center P)) :=
    { (inferInstance : AddGroup (Additive (P ⧸ Subgroup.center P))) with
      add_comm := fun x y => by
        obtain ⟨q₁, rfl⟩ : ∃ q₁, Additive.ofMul q₁ = x := ⟨Additive.toMul x, ofMul_toMul x⟩
        obtain ⟨q₂, rfl⟩ : ∃ q₂, Additive.ofMul q₂ = y := ⟨Additive.toMul y, ofMul_toMul y⟩
        show Additive.ofMul q₁ + Additive.ofMul q₂ = Additive.ofMul q₂ + Additive.ofMul q₁
        rw [← ofMul_mul, ← ofMul_mul, hcommQ] }
  have h2smul : ∀ x : Additive (P ⧸ Subgroup.center P), (2 : ℕ) • x = 0 := by
    intro x
    obtain ⟨q, rfl⟩ : ∃ q, Additive.ofMul q = x := ⟨Additive.toMul x, ofMul_toMul x⟩
    have hq : q * q = 1 := by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center P) q
      rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      simpa [pow_two] using hsquares a
    show (2 : ℕ) • Additive.ofMul q = 0
    rw [two_nsmul, ← ofMul_mul, hq, ofMul_one]
  letI : Module (ZMod 2) (Additive (P ⧸ Subgroup.center P)) := AddCommGroup.zmodModule h2smul
  -- the automorphism of `V` induced by `ξ`
  let σ : Additive (P ⧸ Subgroup.center P) →ₗ[ZMod 2] Additive (P ⧸ Subgroup.center P) :=
    AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive (xiQuot ξ))
  have hσ_apply : ∀ a : P,
      σ (Additive.ofMul (QuotientGroup.mk' (Subgroup.center P) a)) =
        Additive.ofMul (QuotientGroup.mk' (Subgroup.center P) (ξ a)) := by
    intro a
    show (AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive (xiQuot ξ)))
      (Additive.ofMul (QuotientGroup.mk' (Subgroup.center P) a)) = _
    rw [AddMonoidHom.coe_toZModLinearMap]
    exact xiQuot_mk ξ a
  have hσpow : ∀ (k : ℕ) (a : P),
      (σ ^ k) (Additive.ofMul (QuotientGroup.mk' (Subgroup.center P) a)) =
        Additive.ofMul (QuotientGroup.mk' (Subgroup.center P) ((ξ ^ k) a)) := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
        intro a
        have h1 : (σ ^ (k + 1)) (Additive.ofMul (QuotientGroup.mk' (Subgroup.center P) a)) =
            (σ ^ k) (σ (Additive.ofMul (QuotientGroup.mk' (Subgroup.center P) a))) := by
          rw [pow_succ]
          rfl
        rw [h1, hσ_apply, ih]
        rw [show (ξ ^ (k + 1)) a = (ξ ^ k) (ξ a) by rw [pow_succ]; rfl]
  have hξpow : ξ ^ (2 ^ n - 1) = 1 := by
    rw [← hZn, ← hξ.order]
    exact pow_orderOf_eq_one ξ
  have horder_le : σ ^ (2 ^ n - 1) = 1 := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨q, rfl⟩ : ∃ q, Additive.ofMul q = x := ⟨Additive.toMul x, ofMul_toMul x⟩
    obtain ⟨a, rfl⟩ : ∃ a : P, QuotientGroup.mk' (Subgroup.center P) a = q :=
      QuotientGroup.mk'_surjective _ q
    rw [hσpow, hξpow]
    simp
  have hσ_eq_one_imp : ∀ m : ℕ, σ ^ m = 1 → ξ ^ m = 1 := by
    intro m hm
    by_contra hne
    have hmem : ∀ x : P, (ξ ^ m) x * x⁻¹ ∈ Subgroup.center P := by
      intro x
      have h1 : (σ ^ m) (Additive.ofMul (QuotientGroup.mk' (Subgroup.center P) x)) =
          Additive.ofMul (QuotientGroup.mk' (Subgroup.center P) x) := by rw [hm]; rfl
      rw [hσpow m x] at h1
      have h2 : QuotientGroup.mk' (Subgroup.center P) ((ξ ^ m) x) =
          QuotientGroup.mk' (Subgroup.center P) x := by
        have := congrArg Additive.toMul h1
        simpa using this
      have h3 : (QuotientGroup.mk' (Subgroup.center P) ((ξ ^ m) x * x⁻¹) : P ⧸ _) = 1 := by
        rw [map_mul, map_inv, h2, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h3
    have hinj : Function.Injective
        (fun x : P => (⟨(ξ ^ m) x * x⁻¹, hmem x⟩ : ↥(Subgroup.center P))) := by
      intro x y hxy
      have h1 : (ξ ^ m) x * x⁻¹ = (ξ ^ m) y * y⁻¹ := by
        have := congrArg (fun t : ↥(Subgroup.center P) => (t : P)) hxy
        simpa using this
      have h2 : (ξ ^ m) (x⁻¹ * y) = x⁻¹ * y := by
        rw [map_mul, map_inv]
        calc ((ξ ^ m) x)⁻¹ * (ξ ^ m) y = ((ξ ^ m) x)⁻¹ * ((ξ ^ m) x * x⁻¹ * y) := by
              rw [h1]; group
          _ = x⁻¹ * y := by group
      have h3 : x⁻¹ * y = 1 := hξ.fpf m hne _ h2
      calc x = x * (x⁻¹ * y) := by rw [h3, mul_one]
        _ = y := by group
    have hcard := Nat.card_le_card_of_injective _ hinj
    rw [hPcard, hZn] at hcard
    have h3n : 3 * n ≤ n := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard
    omega
  have horder : orderOf σ = 2 ^ n - 1 := by
    refine Nat.dvd_antisymm ?_ ?_
    · rw [orderOf_dvd_iff_pow_eq_one]
      exact horder_le
    · rw [← hZn, ← hξ.order]
      exact orderOf_dvd_iff_pow_eq_one.mpr (hσ_eq_one_imp (orderOf σ) (pow_orderOf_eq_one σ))
  have hσ_of_ξ : ∀ m : ℕ, ξ ^ m = 1 → σ ^ m = 1 := by
    intro m hm
    refine LinearMap.ext fun x => ?_
    obtain ⟨q, rfl⟩ : ∃ q, Additive.ofMul q = x := ⟨Additive.toMul x, ofMul_toMul x⟩
    obtain ⟨a, rfl⟩ : ∃ a : P, QuotientGroup.mk' (Subgroup.center P) a = q :=
      QuotientGroup.mk'_surjective _ q
    rw [hσpow, hm]
    simp
  have hsr : Layers.Semiregular σ := by
    intro k v hv hfix
    by_contra hk
    obtain ⟨q, rfl⟩ : ∃ q, Additive.ofMul q = v := ⟨Additive.toMul v, ofMul_toMul v⟩
    obtain ⟨a, rfl⟩ : ∃ a : P, QuotientGroup.mk' (Subgroup.center P) a = q :=
      QuotientGroup.mk'_surjective _ q
    rw [hσpow k a] at hfix
    have h2 : QuotientGroup.mk' (Subgroup.center P) ((ξ ^ k) a) =
        QuotientGroup.mk' (Subgroup.center P) a := by
      have := congrArg Additive.toMul hfix
      simpa using this
    have hdrift : (ξ ^ k) a * a⁻¹ ∈ Subgroup.center P := by
      have h3 : (QuotientGroup.mk' (Subgroup.center P) ((ξ ^ k) a * a⁻¹) : P ⧸ _) = 1 := by
        rw [map_mul, map_inv, h2, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h3
    have hk' : ξ ^ k ≠ 1 := fun hcon => hk (hσ_of_ξ k hcon)
    have haZ : a ∈ Subgroup.center P := drift_mem_center h hξ hk' hdrift
    have h4 : QuotientGroup.mk' (Subgroup.center P) a = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff a).mpr haZ
    rw [h4] at hv
    exact hv rfl
  have hcardV : Nat.card (Additive (P ⧸ Subgroup.center P)) = 2 ^ (2 * n) := by
    have h1 : Nat.card P = Nat.card (P ⧸ Subgroup.center P) * Nat.card ↥(Subgroup.center P) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    rw [hPcard, hZn] at h1
    have h3 : 2 ^ (2 * n) * 2 ^ n = 2 ^ (3 * n) := by
      rw [← pow_add]
      congr 1
      omega
    have h4 : Nat.card (P ⧸ Subgroup.center P) * 2 ^ n = (2 ^ (2 * n)) * 2 ^ n :=
      (h3.trans h1).symm
    have h5 : Nat.card (P ⧸ Subgroup.center P) = 2 ^ (2 * n) :=
      Nat.eq_of_mul_eq_mul_right (by positivity) h4
    have h6 : Nat.card (Additive (P ⧸ Subgroup.center P)) =
        Nat.card (P ⧸ Subgroup.center P) :=
      Nat.card_congr (Additive.ofMul : (P ⧸ Subgroup.center P) ≃
        Additive (P ⧸ Subgroup.center P))
    rw [h6]
    exact h5
  -- the group-theoretic bijection: layers ↔ invariant subgroups of `P ⧸ Z(P)` of order `2 ^ n`
  have hgrp := card_layers_eq_card_quotient (P := P) (ξ := ξ) (n := n) hZn
  -- the carrier-preserving bridge to submodules
  have hbridge : Nat.card {N : Subgroup (P ⧸ Subgroup.center P) //
        (∀ y ∈ N, xiQuot ξ y ∈ N) ∧ Nat.card ↥N = 2 ^ n} =
      Nat.card (Layers.InvSubspaces σ n) := by
    have hc01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by
      intro c
      revert c
      decide
    have hpowcard : ∀ U : Submodule (ZMod 2) (Additive (P ⧸ Subgroup.center P)),
        Nat.card ↥U = 2 ^ Module.finrank (ZMod 2) ↥U := by
      intro U
      haveI : Module.Finite (ZMod 2) ↥U := Module.Finite.of_finite
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥U)]
      norm_num
    let sm : Subgroup (P ⧸ Subgroup.center P) →
        Submodule (ZMod 2) (Additive (P ⧸ Subgroup.center P)) := fun N =>
      { carrier := (N : Set (P ⧸ Subgroup.center P))
        zero_mem' := N.one_mem
        add_mem' := fun hx hy => N.mul_mem hx hy
        smul_mem' := fun c x hx => by
          rcases hc01 c with rfl | rfl
          · rw [zero_smul]; exact N.one_mem
          · rwa [one_smul] }
    let sg : Submodule (ZMod 2) (Additive (P ⧸ Subgroup.center P)) →
        Subgroup (P ⧸ Subgroup.center P) := fun U =>
      { carrier := (U : Set (Additive (P ⧸ Subgroup.center P)))
        one_mem' := U.zero_mem
        mul_mem' := fun hx hy => U.add_mem hx hy
        inv_mem' := fun {x} hx => by
          have h1 := U.neg_mem (show Additive.ofMul x ∈ U from hx)
          rw [← ofMul_inv] at h1
          exact h1 }
    have hsm_sg : ∀ N : Submodule (ZMod 2) (Additive (P ⧸ Subgroup.center P)),
        sm (sg N) = N := fun N => SetLike.ext fun _ => Iff.rfl
    have hsg_sm : ∀ U : Subgroup (P ⧸ Subgroup.center P), sg (sm U) = U :=
      fun U => SetLike.ext fun _ => Iff.rfl
    have hinv_iff : ∀ (N : Subgroup (P ⧸ Subgroup.center P)),
        (∀ y ∈ N, xiQuot ξ y ∈ N) ↔ Layers.IsInv σ (sm N) := by
      intro N
      constructor
      · intro hN y hy
        obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center P) (Additive.toMul y)
        have hmem : QuotientGroup.mk' (Subgroup.center P) a ∈ N := by
          rw [ha]
          exact hy
        have hthis : xiQuot ξ (QuotientGroup.mk' (Subgroup.center P) a) ∈ N := hN _ hmem
        have hy' : y = Additive.ofMul (QuotientGroup.mk' (Subgroup.center P) a) := by
          rw [ha, ofMul_toMul]
        rw [hy', hσ_apply, ← xiQuot_mk ξ a]
        exact hthis
      · intro hN y hy
        have h1 : σ (Additive.ofMul y) ∈ sm N :=
          hN (Additive.ofMul y) (show Additive.ofMul y ∈ sm N from hy)
        obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center P) y
        have h2 : σ (Additive.ofMul (QuotientGroup.mk' (Subgroup.center P) a)) ∈ sm N := by
          rw [show Additive.ofMul (QuotientGroup.mk' (Subgroup.center P) a) =
            Additive.ofMul y by rw [ha]]
          exact h1
        rw [hσ_apply] at h2
        have h3 : QuotientGroup.mk' (Subgroup.center P) (ξ a) ∈ N := h2
        rw [show y = QuotientGroup.mk' (Subgroup.center P) a from ha.symm, xiQuot_mk]
        exact h3
    refine Nat.card_congr (Equiv.subtypeEquiv
      { toFun := sm, invFun := sg, left_inv := hsg_sm, right_inv := hsm_sg } ?_)
    intro N
    rw [hinv_iff N]
    constructor
    · rintro ⟨hinv, hcard⟩
      refine ⟨hinv, ?_⟩
      have h1 : Nat.card ↥(sm N) = 2 ^ n := by
        rw [show Nat.card ↥(sm N) = Nat.card ↥N from rfl, hcard]
      have h2 : (2 : ℕ) ^ Module.finrank (ZMod 2) ↥(sm N) = 2 ^ n := by
        rw [← hpowcard (sm N)]
        exact h1
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2
    · rintro ⟨hinv, hfr⟩
      replace hfr : Module.finrank (ZMod 2) ↥(sm N) = n := hfr
      refine ⟨hinv, ?_⟩
      have h1 : Nat.card ↥(sm N) = 2 ^ n := by rw [hpowcard (sm N), hfr]
      rw [show Nat.card ↥(sm N) = Nat.card ↥N from rfl] at h1
      exact h1
  -- the count
  have hcount := invSubspaces_card_dichotomy hn1 hcardV horder hsr
  rw [hgrp, hbridge]
  rcases hcount with h2 | h2
  · left; exact h2
  · right; rw [h2, hZn]

end Work.Higman
