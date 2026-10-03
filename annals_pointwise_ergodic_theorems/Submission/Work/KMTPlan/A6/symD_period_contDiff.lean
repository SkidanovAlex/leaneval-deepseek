/-
# Periodicity and `C^4`-smoothness of the symbol difference `symD` of Area A6

`Work.KMTPlan.A6.symD` is the symbol (`ℝ × ℝ → ℂ`, the two variables being the two frequency
coordinates) of the difference between the concrete column `colSmall` and the model column
`lowModel` of the §6 model approximation: it is the sum over the exact-height arithmetic
frequencies `γ₁ ∈ (ℚ/ℤ)_{l₁}`, `γ₂ ∈ (ℚ/ℤ)_{l₂}` of the double lattice sum
`∑'_{m₁,m₂} M₀(x - γ₁ + m₁, y - γ₂ + m₂) · φ_N(x - γ₁ + m₁) · φ̃_N(y - γ₂ + m₂)`.

This module proves that this symbol is `1`-periodic in each variable and is `C^4`:

* **Periodicity** is *pure lattice bookkeeping*: replacing `x` by `x+1` only shifts the summation
  index `m₁ ↦ m₁ + 1`, and a sum over `ℤ` is invariant under that shift.  (No periodicity of `M₀`
  is used -- indeed `m̃_{N,ℝ}` is *not* `1`-periodic, cf. the discussion in
  `smallKernelMass_le.lean`.)
* **Smoothness** is local finiteness: for fixed `(x,y)` the summand vanishes for all but finitely
  many `m₁` (as `φ_N` has compact support) and all but finitely many `m₂`, and the same finite
  index set serves on a whole neighbourhood; so locally `symD` is a *finite* sum of products of
  `C^4` functions (`M₀` is `C^4` because `m̃_{N,ℝ}` is a parametric integral of a jointly smooth
  integrand, and `φ_N`, `φ̃_N` are rescalings of the smooth bump `η`).

The two analytic inputs are proved in the companion modules
`Work.KMTPlan.A6.mTildeDeriv_family_contDiff` (smoothness of the oscillatory integral `m̃_{N,ℝ}`
in its two frequency variables) and `Work.KMTPlan.A6.tsum_int_int_contDiff4` (local finiteness of
double lattice sums).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallSymDefs
import Submission.Work.KMTAreas.A7.varphiNt_bounds
import Submission.Work.KMTAreas.A7.fourierDecay_varphitildeN
import Submission.Work.KMTPlan.A6.tsum_int_int_contDiff4
import Submission.Work.KMTPlan.A6.mTildeDeriv_family_contDiff

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract

/-! ## Lattice shifts -/

/-- A sum over `ℤ` is invariant under the shift `m ↦ m + 1`. -/
lemma tsum_int_shift (f : ℤ → ℂ) : (∑' m : ℤ, f (m + 1)) = ∑' m : ℤ, f m := by
  simpa using Equiv.tsum_eq (Equiv.addRight (1 : ℤ)) f

/-! ## Smoothness of the elementary factors -/

/-- The cutoff `η` is `C^4`. -/
lemma contDiff4_kmtEta : ContDiff ℝ 4 (fun x : ℝ => kmtEta x) :=
  Work.KMTAreas.A7.contDiff_kmtEta 4

/-- The continuous character `e(x) = exp (2πi x)` is `C^4`. -/
lemma contDiff4_ee : ContDiff ℝ 4 Work.KMTAreas.A7.ee := by
  unfold Work.KMTAreas.A7.ee
  have h1 : ContDiff ℝ 4 (fun x : ℝ => ((x : ℂ))) := Complex.ofRealCLM.contDiff
  have h2 : ContDiff ℝ 4 (fun x : ℝ => (2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ)) :=
    contDiff_const.mul h1
  exact Complex.contDiff_exp.comp h2

/-- A linear function of the two frequency variables, composed with `e`, is `C^4`. -/
lemma contDiff4_ee_linear (c d : ℝ) :
    ContDiff ℝ 4 (fun p : ℝ × ℝ => Work.KMTAreas.A7.ee (p.1 * c + p.2 * d)) :=
  contDiff4_ee.comp ((contDiff_fst.mul contDiff_const).add (contDiff_snd.mul contDiff_const))

/-- The bump `φ_N` is `C^4`. -/
lemma contDiff4_varphiN (N k : ℕ) : ContDiff ℝ 4 (Work.KMTAreas.A7.varphiN N k) := by
  unfold Work.KMTAreas.A7.varphiN
  split
  · exact contDiff4_kmtEta.comp (contDiff_const.mul contDiff_id)
  · exact (contDiff4_kmtEta.comp (contDiff_const.mul contDiff_id)).sub
      (contDiff4_kmtEta.comp (contDiff_const.mul contDiff_id))

/-- The bump `φ̃_N` is `C^4`. -/
lemma contDiff4_varphitildeN (d N k : ℕ) :
    ContDiff ℝ 4 (Work.KMTAreas.A7.varphitildeN d N k) := by
  unfold Work.KMTAreas.A7.varphitildeN
  split_ifs
  · exact contDiff4_kmtEta.comp (contDiff_const.mul contDiff_id)
  · exact (contDiff4_kmtEta.comp (contDiff_const.mul contDiff_id)).sub
      (contDiff4_kmtEta.comp (contDiff_const.mul contDiff_id))

/-- A summand of the discrete average is `C^4` in the two frequency variables. -/
lemma contDiff4_momPhase (P : Polynomial ℤ) (N : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (n : ℤ) :
    ContDiff ℝ 4 (fun p : ℝ × ℝ => Work.KMTAreas.A7.momPhase P N α₁ α₂ p.1 p.2 n) := by
  have hlin : ContDiff ℝ 4 (fun p : ℝ × ℝ =>
      Work.KMTAreas.A7.ee (p.1 * (n : ℝ) + p.2 * Work.KMTAreas.A7.PevalR P (n : ℝ))) :=
    contDiff4_ee_linear (n : ℝ) (Work.KMTAreas.A7.PevalR P (n : ℝ))
  unfold Work.KMTAreas.A7.momPhase
  exact (ContDiff.mul (ContDiff.mul contDiff_const contDiff_const)) hlin

/-- The discrete average `weylAvg` is `C^4` in the two frequency variables. -/
lemma contDiff4_weylAvg (P : Polynomial ℤ) (N : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) :
    ContDiff ℝ 4 (fun p : ℝ × ℝ => Work.KMTAreas.A7.weylAvg P N α₁ α₂ p.1 p.2) := by
  unfold Work.KMTAreas.A7.weylAvg
  refine ContDiff.mul contDiff_const ?_
  refine ContDiff.sum (fun n _ => ?_)
  exact contDiff4_momPhase P N α₁ α₂ (n : ℤ)

/-- The oscillatory integral `m̃_{N,ℝ}` is `C^4` in the two frequency variables. -/
lemma contDiff4_mTilde (P : Polynomial ℤ) (N : ℕ) :
    ContDiff ℝ 4 (fun p : ℝ × ℝ => Work.KMTAreas.A7.mTilde P N p.1 p.2) := by
  have h := mTildeDeriv_family_contDiff P N 0 0
  have hfun : (fun p : ℝ × ℝ => Work.KMTAreas.A7.mTildeDeriv P N p.1 p.2 0 0)
      = fun p : ℝ × ℝ => Work.KMTAreas.A7.mTilde P N p.1 p.2 := by
    funext p
    simp only [Work.KMTAreas.A7.mTildeDeriv, Work.KMTAreas.A7.mTilde, pow_zero, mul_one]
  rwa [hfun] at h

/-- The symbol difference `M₀` of Proposition `mod-approx` is `C^4` in the two frequency
variables. -/
lemma contDiff4_M0 (P : Polynomial ℤ) (N q : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) :
    ContDiff ℝ 4 (fun p : ℝ × ℝ => Work.KMTAreas.A7.M0 P N q α₁ α₂ p.1 p.2) := by
  unfold Work.KMTAreas.A7.M0
  exact (contDiff4_weylAvg P N α₁ α₂).sub (ContDiff.mul contDiff_const (contDiff4_mTilde P N))

/-! ## The symbol `symD`: periodicity -/

/-- `symD` is `1`-periodic in its first variable: shifting `x` by `1` shifts the summation index
`m₁ ↦ m₁ + 1`, and the sum over `ℤ` is shift invariant. -/
lemma symD_shift_x (ρ : ℝ) (P : Polynomial ℤ) (N l₁ l₂ k₁ k₂ : ℕ) (x y : ℝ) :
    symD ρ P N l₁ l₂ k₁ k₂ (x + 1) y = symD ρ P N l₁ l₂ k₁ k₂ x y := by
  simp only [symD]
  refine Finset.sum_congr rfl (fun γ₁ _ => Finset.sum_congr rfl (fun γ₂ _ => ?_))
  rw [← tsum_int_shift (f := fun k : ℤ => ∑' m₂ : ℤ,
    Work.KMTAreas.A7.M0 P N (perQ γ₁ γ₂) γ₁ γ₂
        (x - gamR γ₁ + k) (y - gamR γ₂ + m₂)
      * Work.KMTAreas.A7.varphiN N k₁ (x - gamR γ₁ + k)
      * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ (y - gamR γ₂ + m₂))]
  refine tsum_congr (fun m₁ => tsum_congr (fun m₂ => ?_))
  rw [show x + 1 - gamR γ₁ + (m₁ : ℝ) = x - gamR γ₁ + ((m₁ + 1 : ℤ) : ℝ) by push_cast; ring]

/-- `symD` is `1`-periodic in its second variable. -/
lemma symD_shift_y (ρ : ℝ) (P : Polynomial ℤ) (N l₁ l₂ k₁ k₂ : ℕ) (x y : ℝ) :
    symD ρ P N l₁ l₂ k₁ k₂ x (y + 1) = symD ρ P N l₁ l₂ k₁ k₂ x y := by
  simp only [symD]
  refine Finset.sum_congr rfl (fun γ₁ _ => Finset.sum_congr rfl (fun γ₂ _ => ?_))
  refine tsum_congr (fun m₁ => ?_)
  rw [← tsum_int_shift (f := fun k : ℤ =>
    Work.KMTAreas.A7.M0 P N (perQ γ₁ γ₂) γ₁ γ₂
        (x - gamR γ₁ + m₁) (y - gamR γ₂ + k)
      * Work.KMTAreas.A7.varphiN N k₁ (x - gamR γ₁ + m₁)
      * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ (y - gamR γ₂ + k))]
  refine tsum_congr (fun m₂ => ?_)
  rw [show y + 1 - gamR γ₂ + (m₂ : ℝ) = y - gamR γ₂ + ((m₂ + 1 : ℤ) : ℝ) by push_cast; ring]

/-! ## The symbol `symD`: smoothness -/

/-- One fibre of `symD` (fixed pair of arithmetic frequencies) is `C^4`: this is the local
finiteness of the double lattice sum, the two bumps being compactly supported. -/
lemma contDiff4_symD_fibre (P : Polynomial ℤ) (N k₁ k₂ : ℕ)
    (γ₁ γ₂ : Work.Analysis.IonescuWainger.Circle) :
    ContDiff ℝ 4 (fun p : ℝ × ℝ =>
      ∑' m₁ : ℤ, ∑' m₂ : ℤ,
        Work.KMTAreas.A7.M0 P N (perQ γ₁ γ₂) γ₁ γ₂
            (p.1 - gamR γ₁ + m₁) (p.2 - gamR γ₂ + m₂)
          * Work.KMTAreas.A7.varphiN N k₁ (p.1 - gamR γ₁ + m₁)
          * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ (p.2 - gamR γ₂ + m₂)) :=
  tsum_int_int_contDiff4 (fun x y => Work.KMTAreas.A7.M0 P N (perQ γ₁ γ₂) γ₁ γ₂ x y)
    (contDiff4_M0 P N (perQ γ₁ γ₂) γ₁ γ₂)
    (Work.KMTAreas.A7.varphiN N k₁) (Work.KMTAreas.A7.varphitildeN P.natDegree N k₂)
    (contDiff4_varphiN N k₁) (contDiff4_varphitildeN P.natDegree N k₂)
    (Work.KMTAreas.A7.hasCompactSupport_varphiN N k₁)
    (Work.KMTAreas.A7.hasCompactSupport_varphitildeN P.natDegree N k₂)
    (-(gamR γ₁)) (-(gamR γ₂))

/-- **`symD` is `1`-periodic in both variables and `C^4`.** -/
theorem symD_period_contDiff (P : Polynomial ℤ) (ρ : ℝ) (N l₁ l₂ k₁ k₂ : ℕ) :
    (∀ x y : ℝ, Work.KMTPlan.A6.symD ρ P N l₁ l₂ k₁ k₂ (x + 1) y
        = Work.KMTPlan.A6.symD ρ P N l₁ l₂ k₁ k₂ x y) ∧
      (∀ x y : ℝ, Work.KMTPlan.A6.symD ρ P N l₁ l₂ k₁ k₂ x (y + 1)
        = Work.KMTPlan.A6.symD ρ P N l₁ l₂ k₁ k₂ x y) ∧
      ContDiff ℝ 4 (fun p : ℝ × ℝ => Work.KMTPlan.A6.symD ρ P N l₁ l₂ k₁ k₂ p.1 p.2) := by
  refine ⟨fun x y => symD_shift_x ρ P N l₁ l₂ k₁ k₂ x y,
    fun x y => symD_shift_y ρ P N l₁ l₂ k₁ k₂ x y, ?_⟩
  simp only [symD]
  refine ContDiff.sum (fun γ₁ _ => ContDiff.sum (fun γ₂ _ => ?_))
  exact contDiff4_symD_fibre P N k₁ k₂ γ₁ γ₂

end

end Work.KMTPlan.A6
