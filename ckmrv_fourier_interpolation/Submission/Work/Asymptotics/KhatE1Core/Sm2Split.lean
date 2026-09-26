import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Sm1Split

/-!
# The `Sm2`-slice: `Sm2 = Sm2Ref + dSm2`

`Sm2 = j(τ)·Φ_ref·(1 - Δ(z)/q) - E₄(z)³·Φ_ref·d1(z)`, where `d1(z) = Δ(z)⁻¹ - q⁻¹ - 24`.

Two observations make this slice small.

* **`d1` is the `Δ⁻¹`-deviation already defined.**  `K24F.d1 z = Δ(z)⁻¹ - q⁻¹ - 24 = Donly z`
  (`d1_eq_Donly`), with `Donly` from `Sm1Split`.  So the second summand is a deviation times
  `E₄(z)³·Φ_ref`, and splitting `E₄(z)³ = E4Ref³ + dE4c` finishes it.
* **`1 - Δ(z)/q` needs no cancellation.**  Introducing `DqRef = 1 - 24q + 252q²` and
  `dDq = Δ(z)·q⁻¹ - DqRef` (the reference/deviation pair of `Δ(z)/q` at the `q³` truncation of
  `Δ`), the identity `1 - Δ(z)/q = (24q - 252q²) - dDq` is a pure `ring` identity in the atoms
  `Δ(z), q, q⁻¹` — no use of `q·q⁻¹ = 1`.

Consequently `Sm2 = Sm2Ref + dSm2` with

  `Sm2Ref = j(τ)·Φ_ref·(24q - 252q²)`,
  `dSm2   = -j(τ)·Φ_ref·dDq - E4Ref³·Φ_ref·Donly - dE4c·Φ_ref·Donly`,

and every summand of `dSm2` is one deviation times a reference cofactor.  The reference is
truncated at the `q³` (`E⁸`) level of `Δ`, so `dDq = O(q⁴) = O(‖E‖⁸)`; the `E`-degree-6
reference term `-252q²` is a genuine `B₆`-order contribution (`j(τ)·Φ_ref` carries `‖q(τ)‖⁻¹`),
which is consistent with `Bracket24B6Bound`.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- Reference value of `Δ(z)/q` at the `q³` truncation of `Δ`: `1 - 24q + 252q²`. -/
def DqRef (z : ℍ) : ℂ := 1 - 24 * Work.Kernels.qParamFun z
  + 252 * (Work.Kernels.qParamFun z) ^ 2

/-- Deviation of `Δ(z)/q` from `DqRef`. -/
def dDq (z : ℍ) : ℂ :=
  Work.Kernels.DeltaFun z * (Work.Kernels.qParamFun z)⁻¹ - DqRef z

/-- `1 - Δ(z)/q = (24q - 252q²) - dDq`, with no use of `q·q⁻¹ = 1`. -/
lemma Dq_split (z : ℍ) :
    1 - Work.Kernels.DeltaFun z / Work.Kernels.qParamFun z
      = (24 * Work.Kernels.qParamFun z - 252 * (Work.Kernels.qParamFun z) ^ 2) - dDq z := by
  simp only [dDq, DqRef, div_eq_mul_inv]
  ring

/-- `K24F.d1` is exactly the `Δ⁻¹`-deviation `Donly` of `Sm1Split`. -/
lemma d1_eq_Donly (z : ℍ) : Work.Asymptotics.K24F.d1 z = Donly z := by
  simp only [Work.Asymptotics.K24F.d1, Donly, DeltaInvRef]
  ring

/-- The reference part of `K24F.Sm2`. -/
def Sm2Ref (τ z : ℍ) : ℂ :=
  Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Phiref τ z
    * (24 * Work.Kernels.qParamFun z - 252 * (Work.Kernels.qParamFun z) ^ 2)

/-- The deviation part of `K24F.Sm2`. -/
def dSm2 (τ z : ℍ) : ℂ :=
  - (Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Phiref τ z * dDq z)
    - (E4Ref z ^ 3 * Work.Asymptotics.K24F.Phiref τ z * Donly z
        + dE4c z * Work.Asymptotics.K24F.Phiref τ z * Donly z)

/-- **The `Sm2`-split**: `Sm2 = Sm2Ref + dSm2`, exactly. -/
lemma Sm2_eq_ref_add (τ z : ℍ) :
    Work.Asymptotics.K24F.Sm2 τ z = Sm2Ref τ z + dSm2 τ z := by
  have hDq := Dq_split z
  have hd1 := d1_eq_Donly z
  have hE4 := E4Fun_cube_ref_add z
  simp only [Work.Asymptotics.K24F.Sm2, Sm2Ref, dSm2]
  rw [hDq, hd1, hE4]
  ring

end

end Work.Asymptotics.KhatE1Core
