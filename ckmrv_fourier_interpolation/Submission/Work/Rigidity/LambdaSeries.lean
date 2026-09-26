/-
# The `q`-expansion of `λ` at the cusp `i∞`

Near the cusp the modular lambda function `λ = θ₁₀⁴/θ₀₀⁴` becomes a holomorphic function
of `ζ = e^{π i τ}`, with `λ(τ) = 16 ζ + O(ζ²)`; that function has a simple zero at `ζ = 0`
with non-zero derivative, which is what makes `λ` locally surjective onto a punctured
neighbourhood of `0` along the region `Im τ > 1`.

This file introduces the three explicit power series that make this precise:

* `aSeries z = ∑_{m ≥ 0} z^{m(m+1)}`, the `q`-series of `θ₁₀` up to the factor
  `2 e^{π i τ/4}`;
* `bCore z = ∑_{m ≥ 0} z^{(m+1)²}`, the half of the `θ₀₀` series over the positive
  integers;
* `bSeries z = 1 + 2 * bCore z = ∑_{n ∈ ℤ} z^{n²}`, the `q`-series of `θ₀₀`;
* `lambdaSeries z = 16 z (aSeries z)⁴ / (bSeries z)⁴`, the `q`-expansion of `λ`.

All four convergent series are defined by `tsum`; their analyticity/bounds near `0` are the
subject of the companion files.
-/
import Mathlib

noncomputable section

namespace Work.Rigidity

/-- The `q`-series `∑_{m ≥ 0} z^{m (m + 1)}`; `θ₁₀(τ) = 2 e^{π i τ/4} aSeries (e^{π i τ})`. -/
def aSeries (z : ℂ) : ℂ := ∑' m : ℕ, z ^ (m * (m + 1))

/-- The `ℕ`-indexed half `∑_{m ≥ 0} z^{(m+1)^2}` of the `θ₀₀` `q`-series. -/
def bCore (z : ℂ) : ℂ := ∑' m : ℕ, z ^ ((m + 1) * (m + 1))

/-- The `q`-series `1 + 2 ∑_{m ≥ 0} z^{(m+1)^2} = ∑_{n ∈ ℤ} z^{n^2}` of `θ₀₀`. -/
def bSeries (z : ℂ) : ℂ := 1 + 2 * bCore z

/-- The `q`-expansion of `λ` at the cusp, as a function of `z = e^{π i τ}`:
`λ(τ) = lambdaSeries (e^{π i τ})`, and `lambdaSeries z = 16 z + O(z²)`. -/
def lambdaSeries (z : ℂ) : ℂ := 16 * z * (aSeries z) ^ 4 / (bSeries z) ^ 4

@[simp] lemma aSeries_apply (z : ℂ) : aSeries z = ∑' m : ℕ, z ^ (m * (m + 1)) := rfl
@[simp] lemma bCore_apply (z : ℂ) : bCore z = ∑' m : ℕ, z ^ ((m + 1) * (m + 1)) := rfl
@[simp] lemma bSeries_apply (z : ℂ) : bSeries z = 1 + 2 * bCore z := rfl
@[simp] lemma lambdaSeries_apply (z : ℂ) :
    lambdaSeries z = 16 * z * (aSeries z) ^ 4 / (bSeries z) ^ 4 := rfl

/-- The `m = 0` term of `aSeries` is `1`. -/
lemma aSeries_zero : aSeries 0 = 1 := by
  rw [aSeries_apply]
  rw [tsum_eq_single 0]
  · norm_num
  · intro m hm
    have hpos : 0 < m * (m + 1) := by
      have : 0 < m := Nat.pos_of_ne_zero hm
      nlinarith
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hpos)]

/-- `bCore 0 = 0`. -/
lemma bCore_zero : bCore 0 = 0 := by
  rw [bCore_apply]
  have h : (fun m : ℕ => (0 : ℂ) ^ ((m + 1) * (m + 1))) = fun _ : ℕ => 0 := by
    funext m
    rw [zero_pow]
    exact mul_ne_zero (Nat.succ_ne_zero m) (Nat.succ_ne_zero m)
  rw [h, tsum_zero]

/-- `bSeries 0 = 1`. -/
lemma bSeries_zero : bSeries 0 = 1 := by
  rw [bSeries_apply, bCore_zero]
  norm_num

/-- `lambdaSeries 0 = 0`. -/
lemma lambdaSeries_zero : lambdaSeries 0 = 0 := by
  rw [lambdaSeries_apply, aSeries_zero, bSeries_zero]
  ring

end Work.Rigidity
