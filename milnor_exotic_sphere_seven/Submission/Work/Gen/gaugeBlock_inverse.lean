import Mathlib
import Submission.Work.Gen.EulerGaugeCLMDefs
import Submission.Work.Gen.EulerGauge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# The Euler gauge blocks are invertible, and `H` is the conjugate of `G`

This module proves the six identities collected in `Work.Gen.gaugeBlock_inverse`:

* `GblockCLM i u` and `GblockInv i u` are mutually inverse (as continuous linear maps);
* `Hblock i u` is the conjugate of `Gblock i (star u)`, scaled by `(Qfun i u)⁻¹`;
* `HblockCLM` agrees with `Hblock` pointwise, and `HblockCLM`/`HblockInv` are mutually inverse.

All identities are read off from the explicit formulas `Gblock_apply`, `GblockInv_apply`,
`prV_apply` and the fact that `prV i u` is the orthogonal projection off the line `ℂ vVec i u`.
-/

namespace Work.Gen

open Work.Projective

noncomputable section

variable {n : ℕ}

/-! ## Elementary consequences of the explicit formulas -/

/-- On `Gblock` the projection `prV i u` only sees the `insCLM i` part: the `vVec i u` direction is
killed. -/
theorem prV_Gblock (i : Fin (n + 1)) (u : Fin n → ℂ) (x : Fin n → ℂ) (c : ℂ) :
    prV i u (Gblock i u (x, c)) = prV i u (insCLM i x) := by
  rw [Gblock_apply, map_add, map_smul, prV_prV, prV_self, smul_zero, add_zero]

/-- `ipCLM` against `Gblock` reads off the `vVec i u` coefficient times `Qfun`. -/
theorem ipCLM_Gblock (i : Fin (n + 1)) (u : Fin n → ℂ) (x : Fin n → ℂ) (c : ℂ) :
    ipCLM (vVec i u) (Gblock i u (x, c)) = c * Qfun i u := by
  rw [Gblock_apply, map_add, map_smul, ipCLM_prV, zero_add, smul_eq_mul, Qfun]

/-- Subtracting the `i`-th coordinate along `vVec i u` from `prV i u (insCLM i x)` recovers
`insCLM i x`. -/
theorem prV_insCLM_offset (i : Fin (n + 1)) (u : Fin n → ℂ) (x : Fin n → ℂ) :
    prV i u (insCLM i x) - (prV i u (insCLM i x) i) • vVec i u = insCLM i x := by
  rw [prV_apply]
  have hxi : insCLM i x i = 0 := by rw [insCLM_apply, dif_pos rfl]
  have hvi : vVec i u i = 1 := vVec_apply_same i u
  have hsub : (insCLM i x - (ipCLM (vVec i u) (insCLM i x) / Qfun i u) • vVec i u) i
      = -(ipCLM (vVec i u) (insCLM i x) / Qfun i u) := by
    rw [Pi.sub_apply, Pi.smul_apply, hxi, hvi, smul_eq_mul, mul_one, zero_sub]
  rw [hsub, neg_smul]
  abel

/-- The projection is compatible with conjugation. -/
theorem star_prV (i : Fin (n + 1)) (u : Fin n → ℂ) (w : Fin (n + 1) → ℂ) :
    star (prV i u w) = prV i (star u) (star w) := by
  rw [prV, prV, star_prCLM, star_vVec]

/-- The `T^{1,0}` block is compatible with conjugation: conjugating `Gblock i u` at the conjugated
point gives `Gblock i (star u)`. -/
theorem star_Gblock_star (i : Fin (n + 1)) (u : Fin n → ℂ)
    (p : (Fin n → ℂ) × ℂ) :
    star (Gblock i u (star p.1, star p.2)) = Gblock i (star u) p := by
  obtain ⟨x, c⟩ := p
  rw [Gblock_apply, Gblock_apply, star_add, star_smul, star_prV, star_vVec,
    star_insCLM, star_star, star_star]

/-! ## `Hblock` is the conjugate of `Gblock` -/

/-- `Hblock i u` is `(Qfun i u)⁻¹` times the conjugate block `Gblock i (star u)`. -/
theorem Hblock_eq (i : Fin (n + 1)) (u : Fin n → ℂ) (p : (Fin n → ℂ) × ℂ) :
    Hblock i u p = (Qfun i u)⁻¹ • Gblock i (star u) p := by
  obtain ⟨x, c⟩ := p
  rw [Hblock_apply, star_Gblock_star]

/-- The continuous linear map `HblockCLM` agrees with `Hblock` pointwise. -/
theorem HblockCLM_eq (i : Fin (n + 1)) (u : Fin n → ℂ) (p : (Fin n → ℂ) × ℂ) :
    HblockCLM i u p = Hblock i u p := by
  rw [HblockCLM, smul_apply, GblockCLM_apply, ← Hblock_eq]

/-! ## The `T^{1,0}` block is invertible -/

theorem GblockInv_GblockCLM (i : Fin (n + 1)) (u : Fin n → ℂ)
    (p : (Fin n → ℂ) × ℂ) :
    GblockInv i u (GblockCLM i u p) = p := by
  obtain ⟨x, c⟩ := p
  rw [GblockCLM_apply, GblockInv_apply]
  refine Prod.ext ?_ ?_
  · funext k
    rw [prV_Gblock, prV_insCLM_offset]
    exact insCLM_succAbove_apply i x k
  · rw [ipCLM_Gblock, mul_comm c (Qfun i u), ← mul_assoc,
      inv_mul_cancel₀ (Qfun_ne_zero i u), one_mul]

theorem GblockCLM_GblockInv (i : Fin (n + 1)) (u : Fin n → ℂ) (w : Fin (n + 1) → ℂ) :
    GblockCLM i u (GblockInv i u w) = w := by
  rw [GblockCLM_apply, GblockInv_apply]
  set z := prV i u w - (prV i u w i) • vVec i u with hz_def
  have hz0 : z i = 0 := by
    rw [hz_def, Pi.sub_apply, Pi.smul_apply, vVec_apply_same, smul_eq_mul, mul_one, sub_self]
  rw [Gblock_apply, insCLM_succAbove hz0, hz_def]
  rw [map_sub, map_smul, prV_prV, prV_self, smul_zero, sub_zero]
  rw [prV_apply]
  rw [show (Qfun i u)⁻¹ * ipCLM (vVec i u) w = ipCLM (vVec i u) w / Qfun i u by
    rw [div_eq_mul_inv, mul_comm]]
  rw [sub_add_cancel]

/-! ## The `T^{0,1}` block is invertible -/

theorem HblockInv_HblockCLM (i : Fin (n + 1)) (u : Fin n → ℂ)
    (p : (Fin n → ℂ) × ℂ) :
    HblockInv i u (HblockCLM i u p) = p := by
  rw [HblockInv, HblockCLM, smul_apply, smul_apply, map_smul, smul_smul,
    mul_inv_cancel₀ (Qfun_ne_zero i u), one_smul, GblockInv_GblockCLM]

theorem HblockCLM_HblockInv (i : Fin (n + 1)) (u : Fin n → ℂ) (w : Fin (n + 1) → ℂ) :
    HblockCLM i u (HblockInv i u w) = w := by
  rw [HblockCLM, HblockInv, smul_apply, smul_apply, map_smul, smul_smul,
    inv_mul_cancel₀ (Qfun_ne_zero i u), one_smul, GblockCLM_GblockInv]

/-! ## The target -/

theorem gaugeBlock_inverse :
    (∀ {n : ℕ} (i : Fin (n + 1)) (u : Fin n → ℂ) (p : (Fin n → ℂ) × ℂ),
      Work.Gen.GblockInv i u (Work.Gen.GblockCLM i u p) = p) ∧
    (∀ {n : ℕ} (i : Fin (n + 1)) (u : Fin n → ℂ) (w : Fin (n + 1) → ℂ),
      Work.Gen.GblockCLM i u (Work.Gen.GblockInv i u w) = w) ∧
    (∀ {n : ℕ} (i : Fin (n + 1)) (u : Fin n → ℂ) (p : (Fin n → ℂ) × ℂ),
      Work.Gen.Hblock i u p = (Work.Gen.Qfun i u)⁻¹ • Work.Gen.Gblock i (star u) p) ∧
    (∀ {n : ℕ} (i : Fin (n + 1)) (u : Fin n → ℂ) (p : (Fin n → ℂ) × ℂ),
      Work.Gen.HblockCLM i u p = Work.Gen.Hblock i u p) ∧
    (∀ {n : ℕ} (i : Fin (n + 1)) (u : Fin n → ℂ) (p : (Fin n → ℂ) × ℂ),
      Work.Gen.HblockInv i u (Work.Gen.HblockCLM i u p) = p) ∧
    (∀ {n : ℕ} (i : Fin (n + 1)) (u : Fin n → ℂ) (w : Fin (n + 1) → ℂ),
      Work.Gen.HblockCLM i u (Work.Gen.HblockInv i u w) = w) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n i u p; exact GblockInv_GblockCLM i u p
  · intro n i u w; exact GblockCLM_GblockInv i u w
  · intro n i u p; exact Hblock_eq i u p
  · intro n i u p; exact HblockCLM_eq i u p
  · intro n i u p; exact HblockInv_HblockCLM i u p
  · intro n i u w; exact HblockCLM_HblockInv i u w

end

end Work.Gen
