/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The kernel of `phiHom σ`

`phiHom σ : Fˣ →* Fˣ`, `u ↦ u / σ u`, kills exactly the units fixed by `σ`, i.e. the
group of units of the fixed field of `σ`.  Consequently, for `σ` a ring automorphism of
`GF(p^k)` of prime order `r`, the kernel has `p ^ (k / r) - 1` elements: the fixed field of
`σ` has `p ^ (k / r)` elements (see `FixedField.lean`), and the kernel is its unit group,
i.e. its nonzero elements.
-/
import Mathlib
import Submission.Work.DSTR.M110.SplitCase.CardRangeDefs
import Submission.Work.DSTR.M110.SplitCase.FixedField

namespace Work.DSTR.M110.SplitCase

open Work.DSTR.M110.SplitAux

section Kernel

variable (F : Type*) [Field F]

/-- `phiHom σ` sends a unit to `1` exactly when `σ` fixes that unit. -/
lemma phiHom_eq_one_iff (σ : F ≃+* F) (u : Fˣ) :
    phiHom F σ u = 1 ↔ unitMap F σ u = u := by
  rw [phiHom_apply, mul_inv_eq_one, eq_comm]

/-- Membership in the kernel of `phiHom σ` means being fixed by `σ`. -/
lemma mem_ker_phiHom_iff (σ : F ≃+* F) (u : Fˣ) :
    u ∈ (phiHom F σ).ker ↔ unitMap F σ u = u := by
  rw [MonoidHom.mem_ker, phiHom_eq_one_iff]

/-- An element of `ker (phiHom σ)`, read in `F`, is a fixed point of `σ`. -/
lemma fixed_of_mem_ker_phiHom (σ : F ≃+* F) (u : ↥(phiHom F σ).ker) :
    σ ((u : Fˣ) : F) = ((u : Fˣ) : F) := by
  have h : unitMap F σ (u : Fˣ) = (u : Fˣ) :=
    (mem_ker_phiHom_iff F σ _).mp u.2
  simpa [unitMap_coe] using congrArg (fun v : Fˣ => (v : F)) h

/-- A nonzero fixed point of `σ`, regarded as a unit, lies in `ker (phiHom σ)`. -/
lemma mk0_mem_ker_phiHom (σ : F ≃+* F) (a : {a : F // σ a = a ∧ a ≠ 0}) :
    Units.mk0 a.1 a.2.2 ∈ (phiHom F σ).ker := by
  rw [mem_ker_phiHom_iff]
  exact Units.ext a.2.1

/-- The kernel of `phiHom σ` is the group of nonzero fixed points of `σ`. -/
noncomputable def kerEquivFixed (σ : F ≃+* F) :
    ↥(phiHom F σ).ker ≃ {a : F // σ a = a ∧ a ≠ 0} where
  toFun u := ⟨((u : Fˣ) : F), fixed_of_mem_ker_phiHom F σ u, Units.ne_zero (u : Fˣ)⟩
  invFun a := ⟨Units.mk0 a.1 a.2.2, mk0_mem_ker_phiHom F σ a⟩
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    exact Units.val_mk0 (u : Fˣ).ne_zero
  right_inv a := by
    apply Subtype.ext
    exact Units.val_mk0 a.2.2

/-- The kernel of `phiHom σ` has one element less than the fixed-point set of `σ`. -/
lemma card_ker_phiHom_eq (σ : F ≃+* F) :
    Nat.card ↥(phiHom F σ).ker = ({a : F | σ a = a} : Set F).ncard - 1 := by
  have h1 : Nat.card ↥(phiHom F σ).ker = ({a : F | σ a = a} \ {0}).ncard := by
    rw [Nat.card_congr (kerEquivFixed F σ)]
    exact Nat.card_coe_set_eq _
  rw [h1]
  exact Set.ncard_sdiff_singleton_of_mem (by simp)

end Kernel

theorem card_ker_phiHom (p k r : ℕ) [Fact p.Prime] (hk : 1 ≤ k)
    (hr : r.Prime) [DecidableEq (GaloisField p k)]
    (σ : GaloisField p k ≃+* GaloisField p k) (hσ : orderOf σ = r) :
    Nat.card ↥(Work.DSTR.M110.SplitCase.phiHom (GaloisField p k) σ).ker
      = p ^ (k / r) - 1 := by
  have hk0 : k ≠ 0 := by omega
  have hmain := card_ker_phiHom_eq (GaloisField p k) σ
  have hfix : ({a : GaloisField p k | σ a = a} : Set (GaloisField p k)).ncard
      = p ^ (k / r) := by
    rw [← Nat.card_coe_set_eq]
    exact card_fixed_of_orderOf_eq p k r hk0 hr σ hσ
  rw [hmain, hfix]

end Work.DSTR.M110.SplitCase
