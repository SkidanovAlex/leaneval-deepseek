import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Sig2.ThetaDefs
import Submission.Work.HP.Sig2.ThetaPoissonSetup

/-!
# Definitions for Banaszczyk's transference theorem

This file fixes the vocabulary used by the proof of `Work.HP.Lat.transference_exact`
(Banaszczyk's transference theorem, extreme cases):

* `scaleLat c L`, the lattice `c • L = {c • v : v ∈ L}` for `c : ℝ`;
* `latMass M = ∑_{z ∈ M, z ≠ 0} exp (-π ‖z‖²)`, the `δ` of Banaszczyk's argument;
* `Edelta R = exp (R/2 - π R) (2π)^{R/2}` and `Ehole R = exp (R/2 - π R/4) (π/2)^{R/2}`,
  the two numerical thresholds appearing in the Gaussian argument.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Work.HP.Lat

variable {ι : Type*} [Fintype ι]

/-! ## Scaling a lattice -/

/-- The `ℤ`-linear map `v ↦ c • v` on `ι → ℝ`. -/
def scaleLM (c : ℝ) : (ι → ℝ) →ₗ[ℤ] (ι → ℝ) where
  toFun v := c • v
  map_add' v w := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' k v := by
    show (c • (k • v) : ι → ℝ) = k • (c • v)
    rw [smul_comm]

@[simp] lemma scaleLM_apply (c : ℝ) (v : ι → ℝ) : scaleLM c v = c • v := rfl

/-- The lattice `c • L = {c • v : v ∈ L}`. -/
def scaleLat (c : ℝ) (L : Submodule ℤ (ι → ℝ)) : Submodule ℤ (ι → ℝ) :=
  L.map (scaleLM c)

lemma mem_scaleLat {c : ℝ} {L : Submodule ℤ (ι → ℝ)} {v : ι → ℝ} :
    v ∈ scaleLat c L ↔ ∃ w ∈ L, c • w = v := Iff.rfl

lemma scaleLat_mem_smul {c : ℝ} (hc : c ≠ 0) {L : Submodule ℤ (ι → ℝ)} {v : ι → ℝ} :
    v ∈ scaleLat c L ↔ c⁻¹ • v ∈ L := by
  constructor
  · rintro ⟨w, hw, hfl⟩
    rw [← hfl, scaleLM_apply, smul_smul, inv_mul_cancel₀ hc, one_smul]
    exact hw
  · intro h
    exact ⟨c⁻¹ • v, h, by rw [scaleLM_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]⟩

/-! ## The mass of a lattice away from the origin -/

/-- The `δ` of Banaszczyk's argument: `∑_{z ∈ M, z ≠ 0} exp (-π ‖z‖²)`. -/
def latMass (M : Submodule ℤ (ι → ℝ)) : ℝ :=
  ∑' z : M, if (z : ι → ℝ) = 0 then 0 else Real.exp (-Real.pi * (rNorm (z : ι → ℝ)) ^ 2)

/-! ## The numerical thresholds -/

/-- The threshold produced by the shell bound for the mass `δ` at radius `√R`:
`Edelta R = exp (R/2 - π R) (2π)^{R/2}`. -/
def Edelta (R : ℕ) : ℝ := Real.exp ((R : ℝ) / 2 - Real.pi * R) * (Real.sqrt (2 * Real.pi)) ^ R

/-- The threshold produced by the shell bound for a hole of radius `√R / 2`:
`Ehole R = exp (R/2 - π R/4) (π/2)^{R/2}`. -/
def Ehole (R : ℕ) : ℝ := Real.exp ((R : ℝ) / 2 - Real.pi * R / 4) * (Real.sqrt (Real.pi / 2)) ^ R

end Work.HP.Lat
