import Mathlib
import Submission.Work.Certificates.SDR
import Submission.Work.Certificates.SOp.eqb_sound
import Submission.Work.Certificates.SOp.toMatrix_mul
import Submission.Work.Certificates.SOp.toMatrix_sub
import Submission.Work.Certificates.SOp.toMatrix_id

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The degree-`0` homotopy equation of an `SDR` certificate

`SDR.check S` is the conjunction of the degree-`0` identity `1 - Z₀ρ₀ = ∂₀h₀` (where the
`h_{-1}∂_{-1}` term vanishes) with the degreewise checks `S.checkDeg k` for `k < S.N`.  This file
extracts that first conjunct, through the soundness `SOp.eqb_sound` of the sparse equality test
and the `SOp.toMatrix_*` lemmas translating sparse operations into matrix arithmetic.
-/

namespace Work.Certificates.SDR

variable {C : FinChainCx}

/-- The degree-`0` homotopy equation `1 - Z₀ρ₀ = ∂₀h₀` of a strong deformation retract
certificate, read off from the first conjunct of `SDR.check`. -/
theorem check_implies_homotopy_zero (S : SDR C) (h : S.check = true) :
    1 - (S.Z 0).toMatrix * (S.ρ 0).toMatrix = (C.bd 0).toMatrix * (S.h 0).toMatrix := by
  -- `S.check` is the conjunction of the degree-`0` equation with the higher-degree checks.
  have h1 : (((SOp.id (C.dim 0)).sub ((S.Z 0).mul (S.ρ 0))).eqb
      ((C.bd 0).mul (S.h 0))) = true := by
    have hh := h
    simp only [SDR.check] at hh
    exact (Bool.and_eq_true_iff.mp hh).1
  -- Soundness of the sparse equality test turns the sparse equality into a matrix equality ...
  have h2 := SOp.eqb_sound h1
  -- ... and the `toMatrix` API converts the sparse operations into matrix operations.
  rw [SOp.toMatrix_sub, SOp.toMatrix_id, SOp.toMatrix_mul, SOp.toMatrix_mul] at h2
  exact h2

end Work.Certificates.SDR
