import Mathlib
import Submission.Work.BourgainPlan.Oscillation.defs
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.poly_block_defs
import Submission.Work.BourgainPlan.Maximal.poly_block_core_defs
import Submission.Work.BourgainPlan.Maximal.poly_block_cap
import Submission.Work.BourgainPlan.Maximal.poly_cutoff
import Submission.Work.BourgainPlan.Maximal.polyBlockCore_eq_weighted
import Submission.Work.BourgainPlan.Maximal.polyProfile_decay_sharp
import Submission.Work.BourgainPlan.Maximal.polyErrNorm_tsum_le
import Submission.Work.BourgainPlan.Maximal.model_pre
import Submission.Work.BourgainPlan.Maximal.shift_fourier_coeff_conj
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_model_maximal_l2

/-!
# Lacunary-scale vocabulary for the oscillation area

The circle-method (= maximal area) development keeps the model at **dyadic** scales `N = 2^k`.
Bourgain's oscillation inequality is stated along the **lacunary** scales `N_i = ⌊ρ^i⌋`, which are
not dyadic, so every notion that carries the scale must be re-stated at an arbitrary scale `N : ℕ`.

This file does exactly that, with the names `…N` (resp. `polyDilN`) for the arbitrary-scale
versions of the dyadic objects of `Work.BourgainPlan.Maximal`:

* `polyDilN P N = N ^ deg P` (the dilation, `polyDil P k` at `N = 2^k`);
* `polySharpTermN`, `polyBlockCoreN` — the *sharp core* (the honest-projection model, the profile
  replaced by the indicator `|N^d β| ≤ 1`), the arbitrary-scale versions of `polySharpTerm` and
  `polyBlockCore`;
* `polyErrValN` — the profile-replacement error at an arbitrary scale (`polyErrVal` at `N = 2^k`);
* `oscZ` — the `ℤ`-side block-oscillation functional of an *abstract* family `A : ℕ → ℤ → ℂ`;
* `polyWeylOp`, `polyModelOp`, `polyModelBlockOp` — the three operators the argument passes through,
  all as the Fourier integral `∫_0^1 (symbol) · ĝ(θ) · e(-2πi x θ) dθ`, so that `oscZ` can be
  applied to them directly.

Everything here is definitional plumbing; the analytic content is in the companion files.
-/

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

open Work.BourgainPlan.Maximal
open Commons.Analysis.ExponentialSums

/-- **The dilation at an arbitrary scale**: `N ^ deg P`.  At `N = 2^k` this is `polyDil P k`. -/
noncomputable def polyDilN (P : Polynomial ℤ) (N : ℕ) : ℝ := (N : ℝ) ^ P.natDegree

/-- The lacunary scale `⌊ρ ^ i⌋₊`. -/
noncomputable def lacScale (ρ : ℝ) (i : ℕ) : ℕ := ⌊ρ ^ i⌋₊

/-- **The `ℤ`-side block-oscillation functional of an abstract family** `A : ℕ → ℤ → ℂ`:
`Σ_{j<J} ∫_ℤ (sup_{k_j ≤ i < k_{j+1}} |A_i - A_{k_j}|)²`. -/
noncomputable def oscZ (A : ℕ → ℤ → ℂ) (J : ℕ) (k : ℕ → ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range J, ∫⁻ x : ℤ,
    (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ)
      ∂MeasureTheory.Measure.count

/-- The **true Weyl-kernel operator** on `ℤ` at an arbitrary scale `N`:
`∫_0^1 conj(N⁻¹Σ_{n<N} e(θ P n)) · ĝ(θ) · e(-2πi x θ) dθ`.  By `shift_fourier_coeff_conj` this is
the polynomial average `N⁻¹ Σ_{i<N} g (x + P i)`. -/
noncomputable def polyWeylOp (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ) (N : ℕ) (x : ℤ) : ℂ :=
  ∫ θ in (0 : ℝ)..1, (starRingEnd ℂ (polyWeylKernel P N θ)) *
    (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
    Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ))))

/-- The **major-arc model operator** on `ℤ` at an arbitrary scale `N` (the arbitrary-scale version
of `polyTkMax`). -/
noncomputable def polyModelOp (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ) (N : ℕ) (x : ℤ) : ℂ :=
  ∫ θ in (0 : ℝ)..1, (starRingEnd ℂ (polyMajorArcModelPre P ((1 : ℝ)/4) N θ)) *
    (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
    Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ))))

/-- The **`m`-th denominator block of the model operator** at an arbitrary scale `N` (the
arbitrary-scale version of `polyTkBlockMax`). -/
noncomputable def polyModelBlockOp (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ) (m N : ℕ)
    (x : ℤ) : ℂ :=
  ∫ θ in (0 : ℝ)..1, (starRingEnd ℂ (polyModelQBlock P m N θ)) *
    (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
    Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ))))

/-- **A single arc term of the sharp core at an arbitrary scale `N`**: the complete-sum weight
times the *honest* indicator of the window `|N^d (θ - (a/q+l)/c)| ≤ 1` (the arbitrary-scale
version of `polySharpTerm`). -/
noncomputable def polySharpTermN (P : Polynomial ℤ) (q a : ℕ) (l : ℤ) (N : ℕ) (θ : ℝ) : ℂ :=
  polyWeight P (q * P.leadingCoeff.toNat) (a + l * q) *
    (if |polyDilN P N * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))| ≤ 1
      then (1:ℂ) else 0)

/-- **The sharp core of the `m`-th denominator block at an arbitrary scale `N`** (the
arbitrary-scale version of `polyBlockCore`). -/
noncomputable def polyBlockCoreN (P : Polynomial ℤ) (m N : ℕ) (θ : ℝ) : ℂ :=
  ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
    starRingEnd ℂ (polySharpTermN P i.1 i.2 l N θ)

/-- **The profile-replacement error at an arbitrary scale `N`**: the offset between the smooth
profile `Φ_N(β)` and the sharp window (the arbitrary-scale version of `polyErrVal`). -/
noncomputable def polyErrValN (P : Polynomial ℤ) (β : ℝ) (N : ℕ) : ℝ :=
  ‖polyProfile P N β - (if |polyDilN P N * β| ≤ 1 then (1:ℂ) else 0)‖

/-! ## Definitional identifications with the dyadic objects of the maximal area -/

lemma polyDilN_two_pow (P : Polynomial ℤ) (k : ℕ) : polyDilN P (2 ^ k) = polyDil P k := by
  rw [polyDilN, polyDil, powDil]
  push_cast
  rfl

lemma polyTkMax_eq_polyModelOp (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ) (k : ℕ) (x : ℤ) :
    polyTkMax P g s k x = polyModelOp P g s (2 ^ k) x := rfl

lemma polyTkBlockMax_eq_polyModelBlockOp (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ)
    (m k : ℕ) (x : ℤ) :
    polyTkBlockMax P g s m k x = polyModelBlockOp P g s m (2 ^ k) x := rfl

lemma polySharpTermN_two_pow (P : Polynomial ℤ) (q a : ℕ) (l : ℤ) (k : ℕ) (θ : ℝ) :
    polySharpTermN P q a l (2 ^ k) θ = polySharpTerm P q a l k θ := by
  rw [polySharpTermN, polySharpTerm, polyDilN_two_pow]

lemma polyBlockCoreN_two_pow (P : Polynomial ℤ) (m k : ℕ) (θ : ℝ) :
    polyBlockCoreN P m (2 ^ k) θ = polyBlockCore P m k θ := by
  rw [polyBlockCoreN, polyBlockCore]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => ?_))
  rw [polySharpTermN_two_pow]

lemma polyErrValN_two_pow (P : Polynomial ℤ) (β : ℝ) (k : ℕ) :
    polyErrValN P β (2 ^ k) = polyErrVal P β k := by
  rw [polyErrValN, polyErrVal, polyDilN_two_pow]

/-- The major-arc radius at an arbitrary scale: `N^{-(d-1/4)}`. -/
noncomputable def polyArcRadN (P : Polynomial ℤ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ (-((P.natDegree : ℝ) - 1/4))

/-- The active index triples of the `m`-th block at an arbitrary scale `N`. -/
noncomputable def polyActIdxN (P : Polynomial ℤ) (m N : ℕ) (θ : ℝ) : Finset ((ℕ × ℕ) × ℤ) :=
  (polyAllIdx P m).filter
    (fun p => |(P.leadingCoeff : ℝ) * θ - (p.1.2 : ℝ)/(p.1.1 : ℝ) - (p.2 : ℝ)|
      ≤ polyArcRadN P N)

/-- The profile-replacement error of an arc term at an arbitrary scale. -/
noncomputable def polyErrNormN (P : Polynomial ℤ) (q a : ℕ) (l : ℤ) (N : ℕ) (θ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (polyErrValN P (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))) N)

/-- The profile-replacement error of the `m`-th block at an arbitrary scale `N`, with the sharp
core switched on only from the scale threshold `N₀`. -/
noncomputable def polyBlockErrN (P : Polynomial ℤ) (m N₀ N : ℕ) (θ : ℝ) : ℂ :=
  starRingEnd ℂ (polyModelQBlock P m N θ)
    - (if N₀ ≤ N then polyBlockCoreN P m N θ else 0)

/-- The profile-replacement error multiplier of the `m`-th block at an arbitrary scale. -/
noncomputable def polyErrMultN (P : Polynomial ℤ) (m N₀ N : ℕ) (θ : ℝ) : ℂ :=
  if 0 < θ ∧ θ < 1 then polyBlockErrN P m N₀ N θ else 0

/-- The same, switched off below the scale threshold `N₀` (so that only the genuinely small
profile error survives). -/
noncomputable def polyErrMultCutN (P : Polynomial ℤ) (m N₀ N : ℕ) (θ : ℝ) : ℂ :=
  if N₀ ≤ N then polyErrMultN P m N₀ N θ else 0

/-- The lift of a function `ℕ → ℝ` to a finitely supported function `ℤ → ℂ`. -/
noncomputable def liftZC (g : ℕ → ℝ) : ℤ → ℂ :=
  fun n => if 0 ≤ n then (((g n.toNat : ℝ) : ℂ)) else 0

/-- The lift of a finite support from `ℕ` to `ℤ`. -/
noncomputable def liftFinset (s : Finset ℕ) : Finset ℤ := s.image (fun n : ℕ => (n : ℤ))

lemma liftZC_of_nonneg (g : ℕ → ℝ) {n : ℤ} (hn : 0 ≤ n) : liftZC g n = (g n.toNat : ℂ) := by
  simp [liftZC, hn]

lemma liftZC_of_neg (g : ℕ → ℝ) {n : ℤ} (hn : ¬ 0 ≤ n) : liftZC g n = 0 := by
  simp [liftZC, hn]

lemma liftZC_support (g : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n, n ∉ s → g n = 0) :
    ∀ n : ℤ, n ∉ liftFinset s → liftZC g n = 0 := by
  intro n hn
  by_cases h0 : 0 ≤ n
  · rw [liftZC_of_nonneg g h0]
    have : n.toNat ∉ s := by
      intro hcon
      exact hn (Finset.mem_image.mpr ⟨n.toNat, hcon, by simp [Int.toNat_of_nonneg h0]⟩)
    rw [hs n.toNat this, Complex.ofReal_zero]
  · rw [liftZC_of_neg g h0]

/-- The dyadic index used to round the sharp radius `N^{-d}` down to a dyadic radius: the
integer `d·(⌊log₂ N⌋ + 1)`. -/
noncomputable def dyadIdx (d N : ℕ) : ℕ := d * (Nat.log 2 N + 1)

/-- The dyadic rounding of the sharp radius `N^{-d}`: `2^{-(dyadIdx d N) - 1}`, written as
`(1/2)^{dyadIdx d N + 1}`.  It satisfies the elementary comparisons
`dyadRad d N ≤ N^{-d} ≤ 2^{d+1}·dyadRad d N` (from `N ≤ 2^{⌊log₂N⌋+1}` and `2^{⌊log₂N⌋} ≤ N`), so
replacing the sharp window `|N^d β| ≤ 1` by the dyadic window `|β| ≤ dyadRad d N` loses only a
constant factor `2^{d+1}` in the radius — the resulting annulus has relative width `2^{d+1}` and is
paid for by the square function (its annuli are `O(1)`-overlapping along a lacunary sequence). -/
noncomputable def dyadRad (d N : ℕ) : ℝ := (1 / 2 : ℝ) ^ (dyadIdx d N + 1)

lemma dyadRad_pos (d N : ℕ) : 0 < dyadRad d N := by unfold dyadRad; positivity

lemma dyadRad_nonneg (d N : ℕ) : 0 ≤ dyadRad d N := (dyadRad_pos d N).le

lemma dyadRad_eq_inv (d N : ℕ) :
    dyadRad d N = (((2 : ℝ) ^ (dyadIdx d N + 1))⁻¹) := by
  rw [dyadRad, ← inv_pow]
  norm_num

lemma two_pow_log_le (N : ℕ) (hN : 1 ≤ N) : 2 ^ Nat.log 2 N ≤ N :=
  Nat.pow_log_le_self 2 (by omega)

/-- `dyadRad` is antitone in the scale. -/
lemma dyadRad_anti (d : ℕ) : Antitone (fun N : ℕ => dyadRad d N) := by
  intro M N hMN
  change dyadRad d N ≤ dyadRad d M
  rw [dyadRad_eq_inv, dyadRad_eq_inv]
  refine inv_le_inv₀ (by positivity) (by positivity) |>.mpr ?_
  refine pow_le_pow_right₀ (by norm_num) ?_
  unfold dyadIdx
  exact Nat.add_le_add_right (Nat.mul_le_mul_left d
    (Nat.add_le_add_right (Nat.log_mono_right hMN) 1)) 1

end

end Work.BourgainPlan.Oscillation
