import Mathlib
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
# The Euler gauge blocks as continuous linear maps, with explicit inverses

`Work.Gen.Gblock i u` and `Work.Gen.Hblock i u` (in `EulerGauge.lean`) are the `T^{1,0}` and
`T^{0,1}` blocks of the Euler gauge, as plain functions `ℂ^n × ℂ → ℂ^{n+1}`.  This module promotes
them to continuous linear maps `GblockCLM`, `HblockCLM` and defines **explicit two-sided inverses**
`GblockInv`, `HblockInv`, using the orthogonal projection `prCLM` off the line `ℂ vVec i u`.
-/

namespace Work.Gen

open Work.Projective

noncomputable section

variable {n : ℕ}

/-! ## The projection `prCLM` and the insertion `insCLM` -/

theorem ipCLM_prCLM {k : ℕ} {v : Fin k → ℂ} (hv : v ≠ 0) (x : Fin k → ℂ) :
    ipCLM v (prCLM v x) = 0 := by
  have hQ : ipCLM v v ≠ 0 := ipCLM_self_ne_zero hv
  rw [prCLM_apply, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hQ, sub_self]

theorem prCLM_prCLM {k : ℕ} {v : Fin k → ℂ} (hv : v ≠ 0) (x : Fin k → ℂ) :
    prCLM v (prCLM v x) = prCLM v x := by
  rw [prCLM_apply, ipCLM_prCLM hv, zero_div, zero_smul, sub_zero]

theorem prV_apply (i : Fin (n + 1)) (u : Fin n → ℂ) (w : Fin (n + 1) → ℂ) :
    prV i u w = w - (ipCLM (vVec i u) w / Qfun i u) • vVec i u :=
  prCLM_apply _ _

theorem prV_self (i : Fin (n + 1)) (u : Fin n → ℂ) : prV i u (vVec i u) = 0 :=
  prCLM_self _ (Qfun_ne_zero i u)

theorem ipCLM_prV (i : Fin (n + 1)) (u : Fin n → ℂ) (w : Fin (n + 1) → ℂ) :
    ipCLM (vVec i u) (prV i u w) = 0 :=
  ipCLM_prCLM (vVec_ne_zero i u) w

theorem prV_prV (i : Fin (n + 1)) (u : Fin n → ℂ) (w : Fin (n + 1) → ℂ) :
    prV i u (prV i u w) = prV i u w :=
  prCLM_prCLM (vVec_ne_zero i u) w

theorem vVec_apply_same (i : Fin (n + 1)) (u : Fin n → ℂ) : vVec i u i = 1 :=
  Fin.insertNth_apply_same (α := fun _ => ℂ) i (1 : ℂ) u

theorem insCLM_succAbove_apply (i : Fin (n + 1)) (x : Fin n → ℂ) (k : Fin n) :
    insCLM i x (i.succAbove k) = x k := by
  rw [insCLM_apply, dif_neg (Fin.succAbove_ne i k), removeAbove_succAbove]

theorem insCLM_succAbove {i : Fin (n + 1)} {z : Fin (n + 1) → ℂ} (hi : z i = 0) :
    insCLM i (fun k => z (i.succAbove k)) = z := by
  funext m
  rw [insCLM_apply]
  by_cases h : m = i
  · subst h
    rw [dif_pos rfl, hi]
  · rw [dif_neg h, succAbove_removeAbove]

theorem star_vVec (i : Fin (n + 1)) (u : Fin n → ℂ) : star (vVec i u) = vVec i (star u) := by
  funext m
  rw [Pi.star_apply, vVec, vVec]
  by_cases h : m = i
  · subst h
    rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same]; simp
  · rw [insertNth_apply_of_ne i m h, insertNth_apply_of_ne i m h]; simp

/-! ## The blocks and their inverses -/

/-- The `T^{1,0}` block, as a continuous linear map. -/
def GblockCLM (i : Fin (n + 1)) (u : Fin n → ℂ) :
    ((Fin n → ℂ) × ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
  (prV i u).comp ((insCLM i).comp (ContinuousLinearMap.fst ℂ _ _)) +
    (ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ).smulRight (vVec i u)

theorem GblockCLM_apply (i : Fin (n + 1)) (u : Fin n → ℂ) (p : (Fin n → ℂ) × ℂ) :
    GblockCLM i u p = Gblock i u p := by
  obtain ⟨x, c⟩ := p
  simp [GblockCLM, Gblock]

/-- The inverse of the `T^{1,0}` block: project off the line `ℂ vVec i u` and read the
coordinates. -/
def GblockInv (i : Fin (n + 1)) (u : Fin n → ℂ) :
    (Fin (n + 1) → ℂ) →L[ℂ] ((Fin n → ℂ) × ℂ) :=
  (ContinuousLinearMap.pi fun k : Fin n =>
      (ContinuousLinearMap.proj (i.succAbove k)).comp
        (prV i u - (((ContinuousLinearMap.proj i).comp (prV i u)).smulRight (vVec i u)))).prod
    ((Qfun i u)⁻¹ • ipCLM (vVec i u))

theorem GblockInv_apply (i : Fin (n + 1)) (u : Fin n → ℂ) (w : Fin (n + 1) → ℂ) :
    GblockInv i u w
      = (fun k => (prV i u w - (prV i u w i) • vVec i u) (i.succAbove k),
          (Qfun i u)⁻¹ * ipCLM (vVec i u) w) := by
  refine Prod.ext ?_ ?_
  · funext k
    simp only [GblockInv, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, Pi.sub_apply, Pi.smul_apply]
  · simp only [GblockInv, ContinuousLinearMap.prod_apply, smul_apply, smul_eq_mul]

/-- The `T^{0,1}` block, as a continuous linear map. -/
def HblockCLM (i : Fin (n + 1)) (u : Fin n → ℂ) :
    ((Fin n → ℂ) × ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
  (Qfun i u)⁻¹ • GblockCLM i (star u)

/-- The inverse of the `T^{0,1}` block. -/
def HblockInv (i : Fin (n + 1)) (u : Fin n → ℂ) :
    (Fin (n + 1) → ℂ) →L[ℂ] ((Fin n → ℂ) × ℂ) :=
  Qfun i u • GblockInv i (star u)

end

end Work.Gen
