import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import ChallengeDeps
import Submission.Vinogradov.Core

open LeanEval.NumberTheory.VinogradovMeanValue
open scoped ComplexConjugate ENNReal BigOperators
open MeasureTheory Set Filter

set_option autoImplicit false

/-!
# Harmonic-analysis orthogonality for the Vinogradov system

Milestone (a) of the deep-core roadmap: the counting function `J s k X` is an
`L²` mean square of an exponential sum over the compact torus.

Concretely, let `𝕋 := AddCircle 1` and write `mFourier n θ` for the character
`θ ↦ exp (2πi Σ_j n_j θ_j)` on the `(k+1)`-dimensional torus `𝕋^{k+1}`.  For an
`s`-tuple `x ∈ [1,X]^s` let `powerSums k x : Fin (k+1) → ℤ` be the vector of its
power sums of degrees `0,1,…,k`, and put

    F(θ) := Σ_{x ∈ [1,X]^s} mFourier (powerSums k x) θ .

Then by the elementary orthogonality of characters (`∫ mFourier n = δ_{n,0}`,
an immediate consequence of the orthonormality of the Fourier monomials),

    J s k X = ∫_{𝕋^{k+1}} F(θ) · conj (F(θ)) dθ = ∫_{𝕋^{k+1}} |F(θ)|² dθ .

(the degree-0 moment is the constant `s` and is harmless; it makes the matching
condition exactly `∀ j ≤ k` as in the definition of `J`).

The measure on each factor is the normalised Haar measure of total mass `1`
(`volume` on `AddCircle 1` coincides with `haarAddCircle` because `T = 1`); the
local instances below make the types of the Fourier lemmas in
`Mathlib.Analysis.Fourier.AddCircleMulti` line up.

This is the standard first move of every proof of the deep core (Bourgain–
Demeter–Guth decoupling; Wooley efficient congruencing) and the point where
`J` becomes accessible to `L^p`/harmonic-analysis estimates.
-/

namespace Submission.Vinogradov

noncomputable section
open Classical

-- replicate the local instances of `Mathlib.Analysis.Fourier.AddCircleMulti` so
-- that `volume` on the unit torus is the product of the normalised Haar measures
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- An `s`-tuple of integers in `[1,X]`. -/
abbrev Tuple (s X : ℕ) := Fin s → Finset.Icc 1 X

/-- The moments (power sums of degrees `0,1,…,k`) of an `s`-tuple, as integers. -/
def powerSums (k : ℕ) {s X : ℕ} (x : Tuple s X) : Fin (k + 1) → ℤ :=
  fun j => (((∑ i : Fin s, (x i).1 ^ j.val) : ℕ) : ℤ)

/-- The exponential sum `Σ_x e(θ · moments(x))` over all `s`-tuples in `[1,X]^s`. -/
def ExpSum (k : ℕ) {s X : ℕ} (θ : UnitAddTorus (Fin (k + 1))) : ℂ :=
  ∑ x : Tuple s X, UnitAddTorus.mFourier (powerSums k x) θ

/-- Matching of all moments (degrees `0..k`) is exactly the `J`-matching
condition `∀ j ≤ k` from `Core.Matches`. -/
lemma powerSums_eq_iff_matches {k s X : ℕ} (x y : Tuple s X) :
    powerSums k x = powerSums k y ↔ Matches s k X (x, y) := by
  constructor
  · intro h j hj
    have hc := congrFun h ⟨j, by omega⟩
    change (((∑ i : Fin s, (x i).1 ^ j) : ℕ) : ℤ) = (((∑ i : Fin s, (y i).1 ^ j) : ℕ) : ℤ) at hc
    exact_mod_cast hc
  · intro h
    funext j
    change (((∑ i : Fin s, (x i).1 ^ j.val) : ℕ) : ℤ) = (((∑ i : Fin s, (y i).1 ^ j.val) : ℕ) : ℤ)
    have hn := h j.val (by omega)
    exact_mod_cast hn

/-- The set of pairs whose moments match is exactly the set counted by `J`. -/
lemma filter_mom_eq_filter_matches (s k X : ℕ) :
    (Finset.univ.filter (fun p : PairSpace s X => powerSums k p.1 = powerSums k p.2))
      = (Finset.univ.filter (Matches s k X)) := by
  ext p
  simp [powerSums_eq_iff_matches]

/-- The count of moment-matching pairs (as a complex number) is `J s k X`. -/
lemma card_filter_mom_eq (s k X : ℕ) :
    (((Finset.univ.filter (fun p : PairSpace s X => powerSums k p.1 = powerSums k p.2)).card : ℕ) : ℂ)
      = (J s k X : ℂ) := by
  rw [filter_mom_eq_filter_matches s k X]
  rw [J_eq_filter_card]
  norm_num

/-- Fourier monomials are integrable with respect to the normalised Haar measure. -/
lemma mFourier_integrable {d : Type*} [Fintype d] (n : d → ℤ) :
    Integrable (fun θ : UnitAddTorus d => (UnitAddTorus.mFourier (d := d) n) θ) volume := by
  exact (UnitAddTorus.mFourier (d := d) n).continuous.integrable_of_hasCompactSupport (by
    unfold HasCompactSupport tsupport
    exact IsCompact.of_isClosed_subset isCompact_univ isClosed_closure (subset_univ _))

/-- Continuous functions on the unit torus are integrable. -/
lemma integrable_torus_continuous {d : Type*} [Fintype d] {f : UnitAddTorus d → ℂ}
    (hc : Continuous f) : Integrable f volume := by
  exact hc.integrable_of_hasCompactSupport (by
    unfold HasCompactSupport tsupport
    exact IsCompact.of_isClosed_subset isCompact_univ isClosed_closure (subset_univ _))

/-- **Character orthogonality on the torus**: `∫ mFourier n = 1` if `n = 0` and
`0` otherwise. -/
lemma mFourier_integral_monomial {d : Type*} [Fintype d] (n : d → ℤ) :
    (∫ θ : UnitAddTorus d, (UnitAddTorus.mFourier (d := d) n) θ) = if n = 0 then (1 : ℂ) else 0 := by
  classical
  have hO := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := d))) (0 : d → ℤ) n
  have hinner : (∫ θ : UnitAddTorus d,
      (UnitAddTorus.mFourier (d := d) n) θ * starRingEnd ℂ ((UnitAddTorus.mFourier (d := d) 0) θ))
      = if (0 : d → ℤ) = n then (1 : ℂ) else 0 := by
    rw [← hO]
    dsimp [UnitAddTorus.mFourierLp]
    rw [MeasureTheory.ContinuousMap.inner_toLp volume (UnitAddTorus.mFourier (d := d) (0 : d → ℤ))
        (UnitAddTorus.mFourier (d := d) n)]
  have h0val : ∀ θ : UnitAddTorus d, starRingEnd ℂ ((UnitAddTorus.mFourier (d := d) 0) θ) = (1 : ℂ) := by
    intro θ
    have hz := DFunLike.congr_fun (UnitAddTorus.mFourier_zero (d := d)) θ
    rw [hz]
    simp
  calc
    (∫ θ : UnitAddTorus d, UnitAddTorus.mFourier (d := d) n θ)
        = ∫ θ : UnitAddTorus d,
            UnitAddTorus.mFourier (d := d) n θ * starRingEnd ℂ ((UnitAddTorus.mFourier (d := d) 0) θ) := by
            apply integral_congr_ae
            filter_upwards with θ
            rw [h0val θ]
            simp
    _ = if (0 : d → ℤ) = n then (1 : ℂ) else 0 := hinner
    _ = if n = 0 then (1 : ℂ) else 0 := by
            by_cases hn : n = 0
            · simp [hn]
            · simp [hn]
              exact fun h0n => hn h0n.symm

/-- Product of two finite sums is the sum over the product of the index sets. -/
lemma sum_pair_mul {α β : Type*} [Fintype α] [Fintype β] (a : α → ℂ) (b : β → ℂ) :
    (∑ x : α, a x) * (∑ y : β, b y) = ∑ p : α × β, a p.1 * b p.2 := by
  classical
  calc
    (∑ x : α, a x) * (∑ y : β, b y) = ∑ x : α, a x * (∑ y : β, b y) := by
      rw [Finset.sum_mul]
    _ = ∑ x : α, ∑ y : β, a x * b y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
    _ = ∑ p : α × β, a p.1 * b p.2 := by
      rw [← Finset.sum_product' (s := (Finset.univ : Finset α)) (t := (Finset.univ : Finset β))
          (f := fun x y => a x * b y)]
      rw [Finset.univ_product_univ]

/-- Pointwise identity: `F · conj F` is the double character sum over pairs. -/
lemma ExpSum_mul_conj (s k X : ℕ) :
    (fun θ : UnitAddTorus (Fin (k + 1)) =>
        ExpSum (s := s) (k := k) (X := X) θ * conj (ExpSum (s := s) (k := k) (X := X) θ))
    = fun θ : UnitAddTorus (Fin (k + 1)) =>
        ∑ p : PairSpace s X, UnitAddTorus.mFourier (powerSums k p.1 - powerSums k p.2) θ := by
  funext θ
  rw [ExpSum]
  have hconj : conj (∑ x : Tuple s X, UnitAddTorus.mFourier (powerSums k x) θ)
      = ∑ x : Tuple s X, UnitAddTorus.mFourier (-(powerSums k x)) θ := by
    rw [map_sum (starRingEnd ℂ)]
    apply Finset.sum_congr rfl
    intro x hx
    symm
    exact UnitAddTorus.mFourier_neg (n := powerSums k x) (x := θ)
  rw [hconj]
  rw [sum_pair_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← UnitAddTorus.mFourier_add (m := powerSums k p.1) (n := -(powerSums k p.2)) (x := θ)]
  rfl

/-- **Orthogonality (complex form)**: `J s k X = ∫_{𝕋^{k+1}} F·conj F` where
`F(θ) = Σ_x e(θ · moments(x))`. -/
theorem vmvt_orthogonality (s k X : ℕ) :
    (∫ θ : UnitAddTorus (Fin (k + 1)),
        ExpSum (s := s) (k := k) (X := X) θ * conj (ExpSum (s := s) (k := k) (X := X) θ))
      = (J s k X : ℂ) := by
  rw [ExpSum_mul_conj s k X]
  rw [integral_finsetSum (s := (Finset.univ : Finset (PairSpace s X)))
      (f := fun p : PairSpace s X => fun θ : UnitAddTorus (Fin (k + 1)) =>
        UnitAddTorus.mFourier (powerSums k p.1 - powerSums k p.2) θ)]
  · simp_rw [mFourier_integral_monomial]
    simp_rw [sub_eq_zero]
    rw [Finset.sum_boole]
    exact card_filter_mom_eq s k X
  · intro p hp
    exact mFourier_integrable (n := powerSums k p.1 - powerSums k p.2)

/-- **Orthogonality (real form)**: `J s k X = ∫_{𝕋^{k+1}} |F(θ)|² dθ`. -/
theorem vmvt_orthogonality_norm (s k X : ℕ) :
    (∫ θ : UnitAddTorus (Fin (k + 1)), ‖ExpSum (s := s) (k := k) (X := X) θ‖ ^ 2) = J s k X := by
  classical
  let F : UnitAddTorus (Fin (k + 1)) → ℂ := ExpSum (s := s) (k := k) (X := X)
  have hpt : (fun θ : UnitAddTorus (Fin (k + 1)) => F θ * conj (F θ))
      = fun θ : UnitAddTorus (Fin (k + 1)) => (Complex.normSq (F θ) : ℂ) := by
    funext θ
    rw [Complex.mul_conj]
  have h2 : (∫ θ : UnitAddTorus (Fin (k + 1)), F θ * conj (F θ))
      = (((∫ θ : UnitAddTorus (Fin (k + 1)), Complex.normSq (F θ)) : ℝ) : ℂ) := by
    calc
      (∫ θ : UnitAddTorus (Fin (k + 1)), F θ * conj (F θ))
          = ∫ θ : UnitAddTorus (Fin (k + 1)), (Complex.normSq (F θ) : ℂ) := by
            rw [hpt]
      _ = (((∫ θ : UnitAddTorus (Fin (k + 1)), Complex.normSq (F θ)) : ℝ) : ℂ) := by
            simpa using (integral_ofReal (𝕜 := ℂ) (μ := volume)
              (f := fun θ : UnitAddTorus (Fin (k + 1)) => Complex.normSq (F θ)))
  have horth : (∫ θ : UnitAddTorus (Fin (k + 1)), F θ * conj (F θ)) = (J s k X : ℂ) := by
    simpa [F] using vmvt_orthogonality s k X
  have hnorm : (∫ θ : UnitAddTorus (Fin (k + 1)), Complex.normSq (F θ))
      = (∫ θ : UnitAddTorus (Fin (k + 1)), ‖F θ‖ ^ 2) := by
    apply integral_congr_ae
    filter_upwards with θ
    exact Complex.normSq_eq_norm_sq (F θ)
  have hA : (((∫ θ : UnitAddTorus (Fin (k + 1)), Complex.normSq (F θ)) : ℝ) : ℂ) = (J s k X : ℂ) := by
    exact h2.symm.trans horth
  have hB : (((∫ θ : UnitAddTorus (Fin (k + 1)), ‖F θ‖ ^ 2) : ℝ) : ℂ)
      = (((∫ θ : UnitAddTorus (Fin (k + 1)), Complex.normSq (F θ)) : ℝ) : ℂ) := by
    rw [hnorm]
  have hI : (((∫ θ : UnitAddTorus (Fin (k + 1)), ‖F θ‖ ^ 2) : ℝ) : ℂ) = (J s k X : ℂ) := by
    exact hB.trans hA
  exact Complex.ofReal_inj.mp hI

end
end Submission.Vinogradov
