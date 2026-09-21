import Mathlib
import Submission.Work.Analysis.Abel.abel_self_convolution
import Submission.Work.OddRadon.Abel

/-!
# The Radon/Abel inversion of the odd case, in the `ν = c²` variable

`Submission/Work/OddCurve/Inv/` carries the *explicit* inversion of the one-variable Radon
transform used by the low-slope step of the odd-dimensional case (paper Step 3).  This file fixes
the vocabulary.

## Why the `ν = c²` variable

The library's `Work.OddRadon.radonProfile (2n+1) γ c = |S^{2n-2}| ∫_{-1}^1 (1-ν²)^{n-3/2} γ (cν) dν`
is, for an *even* `γ` and `c > 0`, equal to `2 |S^{2n-2}| c^{2-2n} T_{n-3/2} γ c` with
`T_α γ c = ∫_0^c (c²-s²)^α γ s ds`.  Substituting `s = √σ`, `c² = ν`, and writing
`Γ σ = γ (√σ)/√σ`, this is `|S^{2n-2}| c^{2-2n} J^{n-1/2} Γ ν`, where `J^p` is the *unnormalized*
fractional integral

  `J^p Γ ν = ∫_0^ν (ν-σ)^{p-1} Γ σ dσ`.

In these variables the inversion has no Gamma constants and no endpoint pathologies: the classical
Abel inversion is the statement that `J^{1/2}` is *surjective*, its explicit right inverse being
`G ↦ (1/π) J^{1/2}(G') + (G 0 / π) · σ^{-1/2}` (the `σ^{-1/2}` term supplies the constant which
`J^{1/2}` of a continuous function cannot see).

The two ingredients are already in the workspace, `sorry`-free:
`Commons.Analysis.Abel.abel_self_convolution` (`J^{1/2} J^{1/2} = π J^1`) and
`Commons.Analysis.Abel.integral_invSqrt_mul_invSqrt_sub` (`∫_a^b (√(b-v))⁻¹(√(v-a))⁻¹ = π`).
-/

namespace Work.OddCurve.Inv

open MeasureTheory Set Filter
open scoped Topology Interval

noncomputable section

/-- The unnormalized fractional integral `J^{1/2}` in the `ν`-variable:
`abelNu G ν = ∫_0^ν (√(ν-τ))⁻¹ G τ dτ`. -/
def abelNu (G : ℝ → ℝ) (ν : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..ν, (Real.sqrt (ν - τ))⁻¹ * G τ

/-- **The explicit right inverse of `abelNu`**: `G ↦ (1/π) J^{1/2}(G') + (G 0/π) σ^{-1/2}`. -/
def abelNuInv (G : ℝ → ℝ) (σ : ℝ) : ℝ :=
  (1 / Real.pi) * abelNu (deriv G) σ + (G 0 / Real.pi) * (Real.sqrt σ)⁻¹

/-- The value of `abelNu` at a general `ℝ`-power, for rewriting: `J^p` as used above. -/
def fracInt (p : ℝ) (G : ℝ → ℝ) (ν : ℝ) : ℝ :=
  ∫ σ in (0 : ℝ)..ν, (ν - σ) ^ (p - 1) * G σ

@[simp] lemma abelNu_zero (G : ℝ → ℝ) : abelNu G 0 = 0 := by
  simp [abelNu]

/-- **The Abel datum of a data function.**  For `K c = (2|S^{2n-2}|)⁻¹ c^{2n-2} F c`, this is the
`(n-1)`-fold reduction `D K`; it is the quantity which the right inverse of `abelNu` must reproduce
(`Ψ` in the file docstring). -/
def abelDatum (n : ℕ) (F : ℝ → ℝ) : ℝ → ℝ :=
  Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1)
    (fun c : ℝ => (2 * Work.OddRadon.sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) * F c)

/-- The Abel datum in the `ν = c²` variable: `ν ↦ 2 Ψ (√ν)`. -/
def abelDatumNu (n : ℕ) (F : ℝ → ℝ) : ℝ → ℝ := fun ν => 2 * abelDatum n F (Real.sqrt ν)

/-- **The explicit inverse of the one-variable Radon transform** `radonProfile (2n+1)`.
It is the *even* function `u ↦ |u| Γ(u²)` whose `Γ` is the right inverse of `J^{1/2}` applied to
the Abel datum of `F`; the `|u|` factor is the inverse of the `γ (√σ)/√σ` substitution. -/
def radonInvData (n : ℕ) (F : ℝ → ℝ) : ℝ → ℝ :=
  fun u => |u| * abelNuInv (abelDatumNu n F) (u ^ 2)

@[simp] lemma radonInvData_even (n : ℕ) (F : ℝ → ℝ) (u : ℝ) :
    radonInvData n F (-u) = radonInvData n F u := by
  simp [radonInvData]

/-- **The regularised inverse of `abelNu`.**  `abelNuInv` carries the term `(G 0/π)(√σ)⁻¹`, whose
value at `σ = 0` is Lean's `(0:ℝ)⁻¹ = 0` rather than the limit `+∞`; the product with the factor
`|u|` in `radonInvData` then *fails to cancel* at `u = 0`, making `radonInvData` discontinuous there
(it jumps from `G 0/π` to `0`).  This definition replaces the singular term by its limit, so that
`σ ↦ abelNuInvSmooth G σ` is the smooth function `σ ↦ (√σ/π)·abelNu G' σ + G 0/π`, equal to
`abelNuInv G` for `σ > 0`. -/
def abelNuInvSmooth (G : ℝ → ℝ) (σ : ℝ) : ℝ :=
  Real.sqrt σ / Real.pi * abelNu (deriv G) σ + G 0 / Real.pi

/-- **The regularised Radon inverse** (the one to use for the body construction): it is the even,
`C^∞` function `u ↦ h (u²)` with `h σ = (√σ/π)·abelNu ((abelDatumNu n F)') σ + abelDatumNu n F 0/π`.
It agrees with `radonInvData n F` off `0`, and `radonProfile (2n+1)` of it is again `F` (the two
differ at the single point `0`, which no integral sees). -/
def radonInvDataSmooth (n : ℕ) (F : ℝ → ℝ) (u : ℝ) : ℝ :=
  abelNuInvSmooth (abelDatumNu n F) (u ^ 2)

/-- The regularised inverse agrees with `radonInvData` away from the origin. -/
lemma radonInvDataSmooth_eq_radonInvData (n : ℕ) (F : ℝ → ℝ) {u : ℝ} (hu : u ≠ 0) :
    radonInvDataSmooth n F u = radonInvData n F u := by
  have hsqrt : Real.sqrt (u ^ 2) = |u| := Real.sqrt_sq_eq_abs u
  have hpos : (0 : ℝ) < |u| := abs_pos.mpr hu
  simp only [radonInvDataSmooth, radonInvData, abelNuInvSmooth, abelNuInv, hsqrt]
  field_simp

end

end Work.OddCurve.Inv
