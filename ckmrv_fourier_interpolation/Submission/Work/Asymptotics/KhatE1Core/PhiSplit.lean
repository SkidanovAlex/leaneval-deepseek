import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.KPlus24Refs

/-!
# The `Phi`-slice of the `K₊`-half: `Pfun`, `Vfun`, `Ufun` and `Phi` split off their references

This is the second slice of the `K₊` mirror of `KMinus24Split`.  Building on the reference atoms
of `KPlus24Refs` (`E4Ref`, `E2SRef`, `E14Ref`, `I4Ref` and the deviations `dE4`, `dE2S`, `dE14`,
`dI4`), it introduces

* `PfunRef`, `VfunRef`, `UfunRef` — `K24F.Pfun`, `K24F.Vfun`, `K24F.Ufun` with `E₄(z)`, `E₂ˢ(z)`,
  `E₁₄(z)` replaced by their cusp references;
* the deviations `dPfun`, `dVfun`, `dUfun`, written *structurally* as products of `dE4`, `dE2S`,
  `dE14` with the reference cofactors (so that they are immediately boundable);
* `PhiRef = PfunRef - VfunRef · I4Ref` and the deviation `dPhi`, again structural
  (`dPhi = dPfun - (VfunRef·dI4 + dVfun·I4Ref + dVfun·dI4)`).

Every split (`Pfun = PfunRef + dPfun`, `Vfun = VfunRef + dVfun`, `Ufun = UfunRef + dUfun`,
`Phi = PhiRef + dPhi`) is then a pure `ring` identity: the only inputs are the atom splits
`E4Fun_ref_split`, `E2S_ref_split`, `E14Fun_ref_split` and the bridge
`(E₄(z)^3)⁻¹ = I4Ref z + dI4 z`.

Together with `KMinus24Split`, this is the `K₊`/`K₋` scaffolding for the `E(z)`-expansion of
`X = KPlus24Group + KMinus24Group`: an explicit polynomial part (`PolyKM`, `PhiRef`, …) plus an
explicit deviation sum whose every summand carries one of `dE4, dE6, dE2S, dE14, dI4, …`.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-! ## The deviation of `6 E₄(z) - 6 E₂ˢ(z)²` and of `E₂ˢ(z)²` -/

/-- Deviation of the `z`-polynomial `6 E₄(z) - 6 E₂ˢ(z)²`. -/
def dQ4 (z : ℍ) : ℂ := 6 * dE4 z - 12 * E2SRef z * dE2S z - 6 * (dE2S z) ^ 2

/-- Deviation of `E₂ˢ(z)²`. -/
def dQ2 (z : ℍ) : ℂ := 2 * E2SRef z * dE2S z + (dE2S z) ^ 2

lemma dQ4_spec (z : ℍ) :
    6 * Work.Kernels.E4Fun z - 6 * (Work.Kernels.E2S z) ^ 2
      = (6 * E4Ref z - 6 * (E2SRef z) ^ 2) + dQ4 z := by
  simp only [dQ4, dE4, dE2S, E4Ref, E2SRef]; ring

lemma dQ2_spec (z : ℍ) :
    (Work.Kernels.E2S z) ^ 2 = (E2SRef z) ^ 2 + dQ2 z := by
  simp only [dQ2, dE2S, E2SRef]; ring

/-! ## `Pfun` -/

/-- `K24F.Pfun` with the `z`-atoms replaced by their cusp references. -/
def PfunRef (τ z : ℍ) : ℂ :=
  (Work.Asymptotics.K24F.r0 τ + Work.Asymptotics.K24F.r2 τ)
      * (6 * E4Ref z - 6 * (E2SRef z) ^ 2)
    + Work.Asymptotics.K24F.r1 τ
      * ((-12 * Work.Kernels.jInvariantFun τ + 8640) * E4Ref z
          + (12 * Work.Kernels.jInvariantFun τ - 12096) * (E2SRef z) ^ 2)

/-- Deviation of `K24F.Pfun`. -/
def dPfun (τ z : ℍ) : ℂ :=
  (Work.Asymptotics.K24F.r0 τ + Work.Asymptotics.K24F.r2 τ) * dQ4 z
    + Work.Asymptotics.K24F.r1 τ
      * ((-12 * Work.Kernels.jInvariantFun τ + 8640) * dE4 z
          + (12 * Work.Kernels.jInvariantFun τ - 12096) * dQ2 z)

lemma Pfun_eq_ref_add (τ z : ℍ) :
    Work.Asymptotics.K24F.Pfun τ z = PfunRef τ z + dPfun τ z := by
  simp only [Work.Asymptotics.K24F.Pfun, PfunRef, dPfun, dQ4, dQ2, dE4, dE2S, E4Ref, E2SRef]
  ring

/-! ## `Vfun` -/

/-- `K24F.Vfun` with the `z`-atoms replaced by their cusp references. -/
def VfunRef (τ z : ℍ) : ℂ :=
  -3456 * Work.Asymptotics.K24F.r1 τ * E14Ref z * E2SRef z

/-- Deviation of `K24F.Vfun`. -/
def dVfun (τ z : ℍ) : ℂ :=
  -3456 * Work.Asymptotics.K24F.r1 τ
    * (dE14 z * Work.Kernels.E2S z + E14Ref z * dE2S z)

lemma Vfun_eq_ref_add (τ z : ℍ) :
    Work.Asymptotics.K24F.Vfun τ z = VfunRef τ z + dVfun τ z := by
  simp only [Work.Asymptotics.K24F.Vfun, VfunRef, dVfun, dE14, dE2S, E14Ref, E2SRef]
  ring

/-! ## `Ufun` -/

/-- `K24F.Ufun` with the `z`-atoms replaced by their cusp references. -/
def UfunRef (τ z : ℍ) : ℂ :=
  1728 * Work.Asymptotics.K24F.r0 τ * (E2SRef z) ^ 2
    + 1728 * Work.Asymptotics.K24F.r2 τ * E4Ref z

/-- Deviation of `K24F.Ufun`. -/
def dUfun (τ z : ℍ) : ℂ :=
  1728 * Work.Asymptotics.K24F.r0 τ * dQ2 z + 1728 * Work.Asymptotics.K24F.r2 τ * dE4 z

lemma Ufun_eq_ref_add (τ z : ℍ) :
    Work.Asymptotics.K24F.Ufun τ z = UfunRef τ z + dUfun τ z := by
  simp only [Work.Asymptotics.K24F.Ufun, UfunRef, dUfun, dQ2, dE4, dE2S, E4Ref, E2SRef]
  ring_nf

/-! ## The `(E₄(z)^3)⁻¹` bridge to `dI4` -/

/-- `(E₄(z)^3)⁻¹ = (E₄(z)⁻¹)^3`, the form in which `dI4` is defined. -/
lemma E4Fun_cube_inv_eq (z : ℍ) :
    (Work.Kernels.E4Fun z ^ 3)⁻¹ = (Work.Kernels.E4Fun z)⁻¹ ^ 3 := by
  simp only [pow_three, mul_inv]

lemma E4Fun_cube_inv_ref_add (z : ℍ) :
    (Work.Kernels.E4Fun z ^ 3)⁻¹ = I4Ref z + dI4 z := by
  rw [E4Fun_cube_inv_eq]
  exact E4Fun_inv_cube_ref_split z

/-! ## `Phi` -/

/-- `K24F.Phi` with the `z`-atoms replaced by their cusp references. -/
def PhiRef (τ z : ℍ) : ℂ := PfunRef τ z - VfunRef τ z * I4Ref z

/-- Deviation of `K24F.Phi`. -/
def dPhi (τ z : ℍ) : ℂ :=
  dPfun τ z - (VfunRef τ z * dI4 z + dVfun τ z * I4Ref z + dVfun τ z * dI4 z)

lemma Phi_eq_ref_add (τ z : ℍ) :
    Work.Asymptotics.K24F.Phi τ z = PhiRef τ z + dPhi τ z := by
  have hP := Pfun_eq_ref_add τ z
  have hV := Vfun_eq_ref_add τ z
  have hI := E4Fun_cube_inv_ref_add z
  simp only [Work.Asymptotics.K24F.Phi, PhiRef, dPhi, div_eq_mul_inv]
  rw [hP, hV, hI]
  ring

end

end Work.Asymptotics.KhatE1Core
