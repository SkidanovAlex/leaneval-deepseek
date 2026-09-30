import Mathlib
import Submission.Work.Certificates.SDR
import Submission.Work.Certificates.SOp.eqb_sound
import Submission.Work.Certificates.SOp.toMatrix_mul
import Submission.Work.Certificates.SOp.toMatrix_add
import Submission.Work.Certificates.SOp.toMatrix_sub
import Submission.Work.Certificates.SOp.toMatrix_neg
import Submission.Work.Certificates.SOp.toMatrix_id

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Reading the four equations out of a passing `SDR` check

`SDR.check S` decides, sparsely, the four equations `∂Z = 0`, `ρ∂ = 0`, `ρZ = 1` and
`1 - Zρ = ∂h + h∂` in every degree `k < S.N` (plus the `k = 0` instance of the last one, where
the `h∂` term vanishes).  This file turns a positive answer of that decision procedure into the
corresponding *matrix* identities: the sparse `eqb` tests are compared via normal forms
(`SOp.eqb_sound`), and the sparse operations are translated into matrix arithmetic by the
`SOp.toMatrix_*` lemmas.

The result is exactly the `checkDeg` data at degree `k`, `k < S.N`, in the form the homological
arguments downstream consume.
-/

namespace Work.Certificates.SDR

variable {C : FinChainCx}

/-- A passing `SDR.check` yields the four equations of `SDR.checkDeg` in every degree `k < S.N`,
as identities between the actual matrices `toMatrix`. -/
theorem check_implies (S : SDR C) (h : S.check = true) (k : ℕ) (hk : k < S.N) :
    (C.bd k).toMatrix * (S.Z (k+1)).toMatrix = 0 ∧
    (S.ρ k).toMatrix * (C.bd k).toMatrix = 0 ∧
    (S.ρ k).toMatrix * (S.Z k).toMatrix = 1 ∧
    (1 - (S.Z (k+1)).toMatrix * (S.ρ (k+1)).toMatrix =
      (C.bd (k+1)).toMatrix * (S.h (k+1)).toMatrix + (S.h k).toMatrix * (C.bd k).toMatrix) := by
  -- `S.check = true` splits into the `k = 0` homotopy equation and the degreewise checks.
  have hN : (List.range S.N).all S.checkDeg = true := by
    have h1 : (((SOp.id (C.dim 0)).sub ((S.Z 0).mul (S.ρ 0))).eqb
          ((C.bd 0).mul (S.h 0)) && (List.range S.N).all S.checkDeg) = true := h
    simp only [Bool.and_eq_true] at h1
    exact h1.2
  have hk' : k ∈ List.range S.N := List.mem_range.mpr hk
  have hcd : S.checkDeg k = true := (List.all_eq_true.mp hN) k hk'
  -- Split the four sparse `eqb` tests of degree `k`.
  simp only [SDR.checkDeg, Bool.and_eq_true] at hcd
  obtain ⟨⟨⟨hc1, hc2⟩, hc3⟩, hc4⟩ := hcd
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `∂Z = 0`
    have := SOp.eqb_sound hc1
    simp only [SOp.toMatrix_mul, SOp.toMatrix_zero] at this
    exact this
  · -- `ρ∂ = 0`
    have := SOp.eqb_sound hc2
    simp only [SOp.toMatrix_mul, SOp.toMatrix_zero] at this
    exact this
  · -- `ρZ = 1`
    have := SOp.eqb_sound hc3
    simp only [SOp.toMatrix_mul, SOp.toMatrix_id] at this
    exact this
  · -- `1 - Zρ = ∂h + h∂`
    have := SOp.eqb_sound hc4
    simp only [SOp.toMatrix_sub, SOp.toMatrix_mul, SOp.toMatrix_id, SOp.toMatrix_add] at this
    exact this

end Work.Certificates.SDR
