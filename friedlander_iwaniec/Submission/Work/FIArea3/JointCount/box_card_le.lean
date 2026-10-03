/-
# `Work.FIArea3.JointCount.box_card_le` — the size of the polar box (5.14), sharp form

The polar box (5.14) consists of the **primary** Gaussian integers `z` (`IsPrimary`: `re` odd,
`im` even, `im ≡ re - 1 (mod 4)`) with `N < |z|² ≤ (1+θ)N` whose argument lies in a sector of
width `2πθ`.  Since the box embeds isometrically into the annulus
`√N ≤ |z| ≤ √((1+θ)N)`, `φ < arg z ≤ φ + 2πθ` of area `πθ²N` — eight times the density `1/8` of
the primary elements — the expected count is `(π/8)θ²N = (π/8)(θ√N)²`, and the lattice-point
error is `O(θ√N)`.

The proof is a single application of the sharp lattice-point count
`polarBox_lattice_count_sharp`: by `Work.FIArea5.S16Hecke.isPrimary_iff_coset` the primary
elements of `ℤ[i]` form exactly the coset `1 + (1+i)³ℤ[i]`, and with `(1+i)³ = -2 + 2i` this is
the lattice `z - 1 ∈ ℤ⟨-2,2⟩ + ℤ⟨-2,-2⟩` of covolume `8`.  Feeding `g₁ = ⟨-2,2⟩`,
`g₂ = ⟨-2,-2⟩`, `z₀ = 1`, `c = 8` into the sharp count gives

  `#box ≤ π(θ√N)²/8 + 16(θ√N)(√8 + √8)/8 + 1 = π(θ√N)²/8 + 4√8·θ√N + 1`,

and `4√8 ≤ 20`, `1 ≤ 20` finish.
-/
import Mathlib
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.JointCount.polarBox_lattice_count_sharp
import Submission.Work.FIArea5.S16Hecke.isPrimary_iff_coset

namespace Work.FIArea3.JointCount

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The primary coset `1 + (1+i)³ℤ[i]` in lattice coordinates -/

/-- `(1+i)³ = -2 + 2i`. -/
lemma one_add_I_pow_three : (1 + (⟨0, 1⟩ : GaussianInt)) ^ 3 = (⟨-2, 2⟩ : GaussianInt) := by
  decide

/-- Multiplication by `(1+i)³ = -2 + 2i`, in real/imaginary coordinates: the lattice
`ℤ⟨-2,2⟩ + ℤ⟨-2,-2⟩` (the `ℤ`-span of `(1+i)³` and `(1+i)³ i`). -/
lemma cube_mul_mk (a b : ℤ) :
    (⟨-2, 2⟩ : GaussianInt) * (⟨a, b⟩ : GaussianInt)
      = (a : GaussianInt) * (⟨-2, 2⟩ : GaussianInt)
        + (b : GaussianInt) * (⟨-2, -2⟩ : GaussianInt) := by
  ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_intCast, Zsqrtd.im_intCast] <;> ring

/-- **A primary Gaussian integer lies in the coset `1 + ℤ⟨-2,2⟩ + ℤ⟨-2,-2⟩`**, i.e. in
`1 + (1+i)³ℤ[i]`; that lattice has covolume `|det| = 8`. -/
lemma isPrimary_coset_rep {z : GaussianInt} (hz : Work.FIPlan.IsPrimary z) :
    ∃ a b : ℤ, z - 1 = (a : GaussianInt) * (⟨-2, 2⟩ : GaussianInt)
      + (b : GaussianInt) * (⟨-2, -2⟩ : GaussianInt) := by
  obtain ⟨w, hw⟩ := (Work.FIArea5.S16Hecke.isPrimary_iff_coset z).mp hz
  refine ⟨w.re, w.im, ?_⟩
  rw [hw, one_add_I_pow_three]
  have hw' : w = (⟨w.re, w.im⟩ : GaussianInt) := Zsqrtd.ext rfl rfl
  rw [hw', cube_mul_mk w.re w.im]
  ring

/-- `|(-2+2i)|² = 8`. -/
lemma gnorm_neg2_2 : Work.FIPlan.gnorm (⟨-2, 2⟩ : GaussianInt) = 8 := by decide

/-- `|(-2-2i)|² = 8`. -/
lemma gnorm_neg2_neg2 : Work.FIPlan.gnorm (⟨-2, -2⟩ : GaussianInt) = 8 := by decide

/-! ## The size of the polar box -/

theorem box_card_le (Pa : Work.FITop.Params) (φ : ℝ) :
    ((Work.FIArea3.polarBoxFinset Pa φ).card : ℝ)
      ≤ Real.pi / 8 * (Pa.θ * Real.sqrt Pa.N) ^ 2 + 20 * (Pa.θ * Real.sqrt Pa.N) + 20 := by
  -- the covolume of the lattice `ℤ⟨-2,2⟩ + ℤ⟨-2,-2⟩`
  have hdet : ((⟨-2, 2⟩ : GaussianInt).re * (⟨-2, -2⟩ : GaussianInt).im
      - (⟨-2, 2⟩ : GaussianInt).im * (⟨-2, -2⟩ : GaussianInt).re).natAbs = 8 := by decide
  have hsharp := polarBox_lattice_count_sharp Pa φ (1 : GaussianInt) (⟨-2, 2⟩ : GaussianInt)
    (⟨-2, -2⟩ : GaussianInt) 8 hdet (by norm_num)
  -- the orbit of `1` under the lattice is the whole primary coset, i.e. the whole polar box
  have hset : {z : GaussianInt | z ∈ Work.FIArea3.polarBoxFinset Pa φ ∧
        ∃ a b : ℤ, z - 1 = (a : GaussianInt) * (⟨-2, 2⟩ : GaussianInt)
          + (b : GaussianInt) * (⟨-2, -2⟩ : GaussianInt)}
      = (↑(Work.FIArea3.polarBoxFinset Pa φ) : Set GaussianInt) := by
    apply Set.Subset.antisymm
    · intro z hz
      exact hz.1
    · intro z hz
      exact ⟨hz, isPrimary_coset_rep ((Work.FIArea3.mem_polarBoxFinset.mp hz).2).1⟩
  rw [hset, Set.ncard_coe_finset] at hsharp
  -- `√|g₁|² = √|g₂|² = √8`
  have hgn1 : ((Work.FIPlan.gnorm (⟨-2, 2⟩ : GaussianInt) : ℕ) : ℝ) = 8 := by
    rw [gnorm_neg2_2]; norm_num
  have hgn2 : ((Work.FIPlan.gnorm (⟨-2, -2⟩ : GaussianInt) : ℕ) : ℝ) = 8 := by
    rw [gnorm_neg2_neg2]; norm_num
  rw [hgn1, hgn2] at hsharp
  have hu : 0 ≤ Pa.θ * Real.sqrt Pa.N := mul_nonneg Pa.hθ0.le (Real.sqrt_nonneg _)
  have hsqrt8 : Real.sqrt 8 ≤ 5 :=
    (Real.sqrt_le_left (show (0 : ℝ) ≤ 5 by norm_num)).mpr (by norm_num)
  have key : Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 / 8
        + 16 * (Pa.θ * Real.sqrt Pa.N) * (Real.sqrt 8 + Real.sqrt 8) / 8 + 1
      ≤ Real.pi / 8 * (Pa.θ * Real.sqrt Pa.N) ^ 2 + 20 * (Pa.θ * Real.sqrt Pa.N) + 20 := by
    have h1 : 16 * (Pa.θ * Real.sqrt Pa.N) * (Real.sqrt 8 + Real.sqrt 8) / 8
        ≤ 20 * (Pa.θ * Real.sqrt Pa.N) := by
      rw [show 16 * (Pa.θ * Real.sqrt Pa.N) * (Real.sqrt 8 + Real.sqrt 8) / 8
          = 4 * (Pa.θ * Real.sqrt Pa.N) * Real.sqrt 8 by ring]
      calc 4 * (Pa.θ * Real.sqrt Pa.N) * Real.sqrt 8
          ≤ 4 * (Pa.θ * Real.sqrt Pa.N) * 5 :=
            mul_le_mul_of_nonneg_left hsqrt8 (by linarith)
        _ = 20 * (Pa.θ * Real.sqrt Pa.N) := by ring
    have h2 : Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 / 8
        = Real.pi / 8 * (Pa.θ * Real.sqrt Pa.N) ^ 2 := by ring
    linarith [h1, h2]
  linarith [hsharp, key]

end

end Work.FIArea3.JointCount
