import Mathlib
import Submission.Work.A3.Defs

/-!
# Hausdorff--Young on `ℤ`: the truncated Fourier transform and its pairing

This module sets up the objects used in the proof of `Work.A3.hausdorffYoung`, the
Hausdorff--Young inequality for finitely supported functions on `ℤ`

`‖f̂‖_{L^{p'}([0,1])} ≤ ‖f‖_{ℓ^p(ℤ)}`   (`1 < p ≤ 2`).

Since `f` is finitely supported (say in the finite set `s`), the Fourier transform
`kmtFhat f θ = ∑'_x f x · e(-xθ)` is the *finite* sum `kmtSum s f θ = ∑_{x ∈ s} f x · e(-xθ)`,
a trigonometric polynomial in `θ`.  The proof of Hausdorff--Young is the classical one:
Stein's bilinear interpolation between the two endpoint estimates for the *pairing*

`kmtPair s u v = ∫₀¹ (∑_{x ∈ s} u x · e(-xθ)) v(θ) dθ`

— the `(ℓ¹, L¹)` bound `|kmtPair s u v| ≤ ‖u‖_{ℓ¹} ‖v‖_{L¹}` (from `|∑_{x∈s} u x e(-xθ)| ≤ ‖u‖_{ℓ¹}`)
and the `(ℓ², L²)` bound `|kmtPair s u v| ≤ ‖u‖_{ℓ²} ‖v‖_{L²}` (Cauchy--Schwarz together with
Parseval/Plancherel for the trigonometric polynomial, i.e. the orthonormality of the characters
`e(-x·)` on `[0,1]`) — followed by the duality of `Lᵖ` against simple functions.

The pairing is *guarded* by the a.e.-measurability of the test function `v`: for a
non-a.e.-measurable `v` it is defined to be `0`.  This is what makes the two endpoint
estimates available for *all* functions `v` (the bilinear form `kmtPair` is not `ℂ`-linear in
`v` because Mathlib's Bochner integral is `0` on non-integrable functions), exactly as in
`Work.Analysis.Interpolation.trilinearPairing`.

## Main definitions

* `kmtChar` : the character `θ ↦ e(-xθ) = exp(-2πi x θ)`;
* `kmtNu` : Lebesgue measure restricted to `[0,1]` (total mass `1`);
* `kmtSum` : the truncated Fourier sum `∑_{x ∈ s} u x · e(-xθ)`;
* `kmtPair` : the pairing `∫₀¹ (∑_{x ∈ s} u x · e(-xθ)) v(θ) dθ`, guarded by a.e.-measurability
  of `v`.
-/

set_option autoImplicit false

namespace Work.A3

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

open Classical

noncomputable section

/-- The character `θ ↦ e(-xθ) = exp(-2πi x θ)` of the dual group of `ℤ`, evaluated at the
frequency `θ`. -/
def kmtChar (x : ℤ) (θ : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℝ) * θ)))

/-- Lebesgue measure restricted to `[0,1]`, the measure on the frequency space for the
Fourier transform on `ℤ` (it is normalised to have total mass `1`). -/
abbrev kmtNu : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The truncated Fourier sum `∑_{x ∈ s} u x · e(-xθ)` of a function `u` supported in the
finite set `s`.  (For such `u` it is the Fourier transform `kmtFhat u`.) -/
def kmtSum (s : Finset ℤ) (u : ℤ → ℂ) (θ : ℝ) : ℂ :=
  ∑ x ∈ s, u x * kmtChar x θ

/-- The bilinear pairing `(u, v) ↦ ∫₀¹ (∑_{x ∈ s} u x · e(-xθ)) v(θ) dθ` between functions on
`ℤ` and functions on the frequency space.  It is guarded by a.e.-measurability of the test
function `v` (for a non-a.e.-measurable `v` it is `0`), which is what makes its two endpoint
estimates available for arbitrary `v`. -/
def kmtPair (s : Finset ℤ) (u : ℤ → ℂ) (v : ℝ → ℂ) : ℂ :=
  if AEMeasurable v kmtNu then ∫ θ, kmtSum s u θ * v θ ∂kmtNu else 0

@[simp] lemma kmtChar_zero (θ : ℝ) : kmtChar 0 θ = 1 := by
  simp [kmtChar]

lemma norm_kmtChar (x : ℤ) (θ : ℝ) : ‖kmtChar x θ‖ = 1 := by
  simp [kmtChar, Complex.norm_exp]

lemma enorm_kmtChar (x : ℤ) (θ : ℝ) : ‖kmtChar x θ‖ₑ = 1 := by
  rw [← ofReal_norm, norm_kmtChar, ENNReal.ofReal_one]

lemma conj_kmtChar (x : ℤ) (θ : ℝ) : conj (kmtChar x θ) = kmtChar (-x) θ := by
  rw [kmtChar, kmtChar, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, Complex.conj_I, map_ofNat]

lemma kmtSum_zero_left (s : Finset ℤ) (θ : ℝ) : kmtSum s 0 θ = 0 := by
  simp [kmtSum]

@[simp] lemma kmtSum_apply (s : Finset ℤ) (u : ℤ → ℂ) (θ : ℝ) :
    kmtSum s u θ = ∑ x ∈ s, u x * kmtChar x θ := rfl

/-- The truncated Fourier sum is linear in its argument. -/
lemma kmtSum_add (s : Finset ℤ) (u v : ℤ → ℂ) (θ : ℝ) :
    kmtSum s (u + v) θ = kmtSum s u θ + kmtSum s v θ := by
  simp only [kmtSum_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma kmtSum_smul (s : Finset ℤ) (c : ℂ) (u : ℤ → ℂ) (θ : ℝ) :
    kmtSum s (c • u) θ = c * kmtSum s u θ := by
  simp only [kmtSum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

lemma kmtSum_sum {ι : Type*} (s : Finset ℤ) (t : Finset ι) (c : ι → ℂ) (w : ι → ℤ → ℂ)
    (θ : ℝ) :
    kmtSum s (∑ i ∈ t, c i • w i) θ = ∑ i ∈ t, c i * kmtSum s (w i) θ := by
  rw [kmtSum_apply]
  have h1 : ∀ x : ℤ, (∑ i ∈ t, c i • w i) x * kmtChar x θ
      = ∑ i ∈ t, (c i * w i x) * kmtChar x θ := by
    intro x
    rw [Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kmtSum_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Pointwise bound of the truncated Fourier sum by the `ℓ¹` norm of its coefficient function. -/
lemma enorm_kmtSum_le (s : Finset ℤ) (u : ℤ → ℂ) (θ : ℝ) :
    ‖kmtSum s u θ‖ₑ ≤ ∑ x ∈ s, ‖u x‖ₑ := by
  rw [kmtSum_apply]
  refine le_trans (enorm_sum_le _ _) (Finset.sum_le_sum fun x _ => ?_)
  rw [enorm_mul, enorm_kmtChar, mul_one]

lemma continuous_kmtSum (s : Finset ℤ) (u : ℤ → ℂ) :
    Continuous fun θ : ℝ => kmtSum s u θ := by
  simp only [kmtSum_apply]
  exact continuous_finsetSum _ fun x _ =>
    continuous_const.mul (by unfold kmtChar; fun_prop)

lemma aemeasurable_kmtSum (s : Finset ℤ) (u : ℤ → ℂ) :
    AEMeasurable (kmtSum s u) kmtNu :=
  (continuous_kmtSum s u).aemeasurable

/-- **Identification of the Fourier transform of a finitely supported function with its
truncated Fourier sum.** -/
lemma kmtFhat_eq_kmtSum {f : ℤ → ℂ} {s : Finset ℤ} (h : ∀ x ∉ s, f x = 0) (θ : ℝ) :
    kmtFhat f θ = kmtSum s f θ := by
  rw [kmtFhat, kmtSum_apply]
  exact tsum_eq_sum fun x hx => by rw [h x hx, zero_mul]

lemma kmtPair_of_aemeasurable {s : Finset ℤ} {u : ℤ → ℂ} {v : ℝ → ℂ}
    (hv : AEMeasurable v kmtNu) :
    kmtPair s u v = ∫ θ, kmtSum s u θ * v θ ∂kmtNu := by
  unfold kmtPair
  rw [if_pos hv]

lemma kmtPair_of_not_aemeasurable {s : Finset ℤ} {u : ℤ → ℂ} {v : ℝ → ℂ}
    (hv : ¬ AEMeasurable v kmtNu) : kmtPair s u v = 0 := by
  unfold kmtPair
  rw [if_neg hv]

end

end Work.A3
