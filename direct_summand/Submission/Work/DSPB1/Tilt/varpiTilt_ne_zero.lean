import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSPB1.Basic

/-!
# DSPB1 — the tilt `ϖ♭` of the pseudo-uniformizer is nonzero

This file proves `Work.DSPB1.Tilt.varpiTilt_ne_zero`: for a `p`-torsion-free `p`-adically
complete ring `C` with pseudo-uniformizer data `P : DSMap.PerfectoidData p C` and `p` not a
unit in `C`, the compatible system

  `Work.DSPB1.varpiTilt P = (n ↦ ϖ_n mod p) ∈ PreTilt C p = Perfection (C ⧸ (p)) p`

is a nonzero element of the tilt.

The mathematics is one line: the Teichmüller untilt of `varpiTilt P` is *exactly* `ϖ_0`
(`Work.DSPB1.varpiTilt_untilt`, proved in `Basic.lean`), `untilt` maps `0` to `0`, and
`ϖ_0 ≠ 0`.  The latter holds because `ϖ_0 ^ p = p * v` with `v` a unit, while `p ≠ 0` in `C`:
`p` is `C`-regular by `P.torsionFree`, so `p = 0` would make `C` trivial, hence `p` a unit.

## Contents

* `Work.DSPB1.Tilt.varpi_zero_ne_zero` — `ϖ_0 ≠ 0`;
* `Work.DSPB1.Tilt.varpiTilt_ne_zero` — `varpiTilt P ≠ 0`.
-/

set_option linter.style.haveILetI false

namespace Work.DSPB1.Tilt

/-- The zeroth pseudo-uniformizer is nonzero: `ϖ_0 ^ p = p * v` with `v` a unit, and `p ≠ 0`
since `p` is `C`-regular (`P.torsionFree`) while `p` is not a unit of `C`. -/
theorem varpi_zero_ne_zero {p : ℕ} [Fact p.Prime] {C : Type*} [CommRing C]
    [Fact ¬IsUnit (p : C)] (P : DSMap.PerfectoidData p C) : P.ϖ 0 ≠ 0 := by
  intro h0
  obtain ⟨v, hv⟩ := P.unit
  -- `ϖ_0 = 0` forces `p * v = 0`
  have hpv : (p : C) * (v : C) = 0 := by
    rw [← hv, h0]
    exact zero_pow (Fact.out (p := p.Prime)).ne_zero
  -- hence `p = 0` (multiply by the inverse of the unit `v`)
  have hp : (p : C) = 0 := by
    have h := congrArg (fun x : C => x * (↑v⁻¹ : C)) hpv
    simpa [mul_assoc] using h
  -- `p = 0` is `C`-regular, so `C` is trivial, and then `p` is a unit: contradiction
  have hreg : IsSMulRegular C (0 : C) := by
    rw [← hp]
    exact P.torsionFree
  haveI : Subsingleton C := hreg.subsingleton
  have hunit0 : IsUnit (0 : C) := ⟨1, Subsingleton.elim _ _⟩
  have : IsUnit (p : C) := by simpa [hp] using hunit0
  exact (Fact.out : ¬ IsUnit (p : C)) this

/-- **The tilt of the pseudo-uniformizer is nonzero.**

`varpiTilt P` is the compatible system `n ↦ ϖ_n mod p`; it is nonzero because its Teichmüller
untilt is `ϖ_0 ≠ 0`: if `varpiTilt P = 0`, then `ϖ_0 = untilt (varpiTilt P) = untilt 0 = 0`. -/
theorem varpiTilt_ne_zero {p : ℕ} [Fact p.Prime] {C : Type*} [CommRing C]
    [Fact ¬IsUnit (p : C)] (P : DSMap.PerfectoidData p C) : Work.DSPB1.varpiTilt P ≠ 0 := by
  intro h
  letI := P.complete
  have h1 : PreTilt.untilt (Work.DSPB1.varpiTilt P) = P.ϖ 0 := Work.DSPB1.varpiTilt_untilt P
  have hz : PreTilt.untilt (0 : PreTilt C p) = 0 := by
    change Perfection.teichmuller p (Ideal.span {(p : C)}) 0 = 0
    exact Perfection.teichmuller_zero
  rw [h, hz] at h1
  exact varpi_zero_ne_zero P h1.symm

end Work.DSPB1.Tilt
