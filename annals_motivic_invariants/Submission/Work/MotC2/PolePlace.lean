/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotC2

# The local ring at the point at infinity is contained in `T E`

Let `E` be a Weierstrass curve over a field `L`, `L(E) = Func E`, `u = 1/x`, `w = y/x²`, and
`T E ⊆ L(E)` the `L`-subalgebra of functions whose `(1, w)`-coordinates are fractions `P(x)/Q(x)`
with `deg P ≤ deg Q` (the functions regular at the point at infinity of the `x`-line).

By `Work.MotC2.PoleAux.infPlace_mem_iff` every element `f` of `infPlace E` (the local ring of the
point at infinity `O`) can be written as `a·b⁻¹` with `a, b` in the chart-at-infinity coordinate ring
`infCoordRing E = L[u, w]` and `b ∉ ⟨u, w⟩`.  By `Work.MotC2.exists_aeval_add_mul_infW` we may
write `b = P₀(u) + P₁(u)·w`, and `b ∉ ⟨u, w⟩` forces `P₀.coeff 0 ≠ 0` (`P₀.coeff 0 = 0` would give
`b = u·P₀'(u) + P₁(u)·w ∈ ⟨u, w⟩`).  Hence `b⁻¹ ∈ T E` by `Work.MotC2.inv_Tgen_of_u_poly'`, and
`a ∈ T E` since `T E` contains the whole chart ring; being an `L`-subalgebra, `T E` contains
`a·b⁻¹ = f`.

## Tags

elliptic curve, function field, pole order, chart at infinity
-/

import Mathlib
import Submission.Work.MotC2.PoleSetup
import Submission.Work.MotC2.PoleTgen
import Submission.Work.MotC2.PoleT
import Submission.Work.MotC2.PoleInv
import Submission.Work.MotC2.PoleAux
import Submission.Work.MotC2.exists_aeval_add_mul_infW

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve.Affine

set_option maxHeartbeats 1000000

namespace Work.MotC2

variable {L : Type*} [Field L]

/-- A polynomial in `u = 1/x` with coefficients in `L` lies in the chart-at-infinity coordinate
ring. -/
lemma aeval_infU_mem_infCoordRing (E : WeierstrassCurve L) (P : Polynomial L) :
    Polynomial.aeval (infU E) P ∈ infCoordRing E := by
  refine Algebra.adjoin_mono ?_ (Polynomial.aeval_mem_adjoin_singleton L (infU E))
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  simp

/-- **The local ring of the point at infinity is contained in `T E`.** -/
theorem infPlace_le_T (E : WeierstrassCurve L) [E.IsElliptic] : infPlace E ≤ T E := by
  intro f hf
  obtain ⟨a, b, hb, hab⟩ := (PoleAux.infPlace_mem_iff E f).mp hf
  have hb0 : (b : Func E) ≠ 0 := fun h0 =>
    hb ((PoleAux.mem_infIdealR_iff E b).mp (by rw [h0]; exact Submodule.zero_mem _))
  obtain ⟨β₀, β₁, hβ⟩ := exists_aeval_add_mul_infW L E b
  have hβ₀ : β₀.coeff 0 ≠ 0 := by
    intro h0
    refine hb ((PoleAux.mem_infIdealR_iff E b).mp ?_)
    obtain ⟨β₀', rfl⟩ := Polynomial.X_dvd_iff.mpr h0
    rw [hβ, map_mul, aeval_X]
    refine Submodule.add_mem _ ?_ ?_
    · have hu : infU E ∈ infIdeal E := Submodule.subset_span (by simp)
      have h := Submodule.smul_mem (infIdeal E)
        (⟨Polynomial.aeval (infU E) β₀', aeval_infU_mem_infCoordRing E β₀'⟩ : infCoordRing E) hu
      simpa [Subalgebra.smul_def, smul_eq_mul, mul_comm] using h
    · have hw : infW E ∈ infIdeal E := Submodule.subset_span (by simp)
      have h := Submodule.smul_mem (infIdeal E)
        (⟨Polynomial.aeval (infU E) β₁, aeval_infU_mem_infCoordRing E β₁⟩ : infCoordRing E) hw
      simpa [Subalgebra.smul_def, smul_eq_mul] using h
  have hinv : (b : Func E)⁻¹ ∈ T E := by
    obtain ⟨P, Q, P', Q', hQ, hQ', dQ, dQ', heq⟩ := inv_Tgen_of_u_poly' L E hβ hβ₀ hb0
    exact (mem_T_iff E _).mpr ⟨P, Q, P', Q', hQ, hQ', dQ, dQ', heq⟩
  have hf' : f = (a : Func E) * ((b : Func E))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hb0, hab]
  rw [hf']
  exact mul_mem (infCoordRing_le_T E a.2) hinv

end Work.MotC2
