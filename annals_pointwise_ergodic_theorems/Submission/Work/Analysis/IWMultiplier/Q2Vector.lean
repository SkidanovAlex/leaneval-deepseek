/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Analysis.IWMultiplier.Q2
import Submission.Port.Aesm

/-!
# The `q = 2` case for Hilbert-space-valued sequences

The statement of the Ionescu–Wainger multiplier theorem `IWLqBound` is *vector-valued*: the
multiplier is bounded on `ℓ^q(ℤ; H)` for every finite dimensional Hilbert space `H`, with a
constant independent of `H`.  In this file we obtain that uniformity at `q = 2` from the scalar
case: a scalar-`ℓ²` bound for the convolution kernel implies the `H`-valued bound, because the
operator acts coordinatewise in an orthonormal basis and Pythagoras (Parseval's identity) lets one
add up the scalar bounds.

The file also records the general bridge between `eLpNorm · 2` against the counting measure and the
`ℓ²` norm of the corresponding element of `lp (fun _ : ℤ => H) 2`, for an arbitrary normed space
`H` (the scalar case is `eLpNorm_two_count_eq_ofReal_lpNorm` in `Basic.lean`).

## Main results

* `Work.Analysis.IWMultiplier.IWLqBound_of_scalar_q2` — the scalar `q = 2` bound implies the
  Hilbert-space-valued one, with the same constant.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal NNReal InnerProductSpace
open MeasureTheory

namespace Work.Analysis.IWMultiplier

open Work.Analysis.IonescuWainger

section Aux

variable {H : Type*} [NormedAddCommGroup H]

/-- `eLpNorm · 2` against the counting measure on `ℤ`, as a sum of squares (in `ℝ≥0∞`). -/
theorem eLpNorm_two_rpow_two_count (g : ℤ → H) :
    (eLpNorm g 2 Measure.count) ^ (2 : ℝ) = ∑' n : ℤ, ‖g n‖ₑ ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (by norm_num) (by norm_num), lintegral_count,
    ← ENNReal.rpow_mul,
    show (1 / (2 : ℝ≥0∞).toReal) * 2 = 1 by simp, ENNReal.rpow_one,
    show (2 : ℝ≥0∞).toReal = 2 by simp]

/-- Parseval's identity in `ℝ≥0∞` form: the squared norm of a vector is the sum of the squares of
its coordinates in an orthonormal basis. -/
theorem enorm_sq_eq_sum {ι : Type*} [Fintype ι] [InnerProductSpace ℂ H]
    (b : OrthonormalBasis ι ℂ H) (x : H) :
    ‖x‖ₑ ^ (2 : ℝ) = ∑ i, ‖⟪b i, x⟫_ℂ‖ₑ ^ (2 : ℝ) := by
  rw [← ofReal_norm x,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg x) (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two,
    ← OrthonormalBasis.sum_sq_norm_inner_right b x,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Real.rpow_two,
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
    ofReal_norm (⟪b i, x⟫_ℂ)]

end Aux

section Coord

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The defining double sum of `iwConv` is finite when the sequence is finitely supported. -/
theorem summable_iwConv_tsum (A : Finset Circle) (Φ : Circle → ℂ) (f : ℤ → H)
    (hf : (Function.support f).Finite) (n : ℤ) :
    Summable (fun j : ℤ => iwKernel (iwSymbolSet A Φ) j • f (n - j)) := by
  refine summable_of_ne_finset_zero (s := hf.toFinset.image (fun m : ℤ => n - m)) ?_
  intro j hj
  have hzero : f (n - j) = 0 := by
    by_contra hne
    exact hj (Finset.mem_image.mpr ⟨n - j, hf.mem_toFinset.mpr hne, by ring⟩)
  rw [hzero, smul_zero]

/-- The IW multiplier acts coordinatewise: the `y`-component of `iwConv A Φ f n` is the scalar
IW multiplier applied to the `y`-component sequence. -/
theorem inner_iwConv (A : Finset Circle) (Φ : Circle → ℂ) (f : ℤ → H)
    (hf : (Function.support f).Finite) (y : H) (n : ℤ) :
    ⟪y, iwConv A Φ f n⟫_ℂ = iwConv A Φ (fun m => ⟪y, f m⟫_ℂ) n := by
  classical
  set s : Finset ℤ := hf.toFinset.image (fun m : ℤ => n - m) with hs
  have hvan : ∀ j : ℤ, j ∉ s → f (n - j) = 0 := by
    intro j hj
    by_contra hne
    exact hj (Finset.mem_image.mpr ⟨n - j, hf.mem_toFinset.mpr hne, by ring⟩)
  rw [iwConv_apply, iwConv_apply,
    tsum_eq_sum (L := SummationFilter.unconditional ℤ) (s := s)
      (fun j hj => by rw [hvan j hj, smul_zero]),
    tsum_eq_sum (L := SummationFilter.unconditional ℤ) (s := s)
      (fun j hj => by rw [hvan j hj, inner_zero_right, smul_zero]),
    inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_right, smul_eq_mul]

end Coord

/-- **The `q = 2` case is insensitive to the (finite dimensional) Hilbert space.**  A scalar
`ℓ²(ℤ)` bound for the IW multiplier with symbol `iwSymbolSet A Φ` implies the same bound with the
same constant for `ℓ²(ℤ; H)`, for every finite dimensional Hilbert space `H`.

The proof decomposes an `H`-valued sequence in an orthonormal basis of `H`: the multiplier acts
coordinatewise (`inner_iwConv`), so the squared `ℓ²(ℤ;H)` norm is the sum of the squared scalar
`ℓ²` norms of its coordinates (Parseval, `enorm_sq_eq_sum`), and each of those is bounded by the
scalar hypothesis. -/
theorem IWLqBound_of_scalar_q2 (A : Finset Circle) (Φ : Circle → ℂ) {C : NNReal}
    (h : IWLqBoundScalar A Φ 2 C) : IWLqBound A Φ 2 C := by
  intro H _ _ _ f hf
  classical
  set b := stdOrthonormalBasis ℂ H with hb
  have hcf : ∀ i : Fin (Module.finrank ℂ H),
      (Function.support (fun m : ℤ => ⟪b i, f m⟫_ℂ)).Finite := by
    intro i
    refine hf.subset ?_
    intro n hn
    rw [Function.mem_support] at hn ⊢
    intro hfn
    exact hn (by simp [hfn])
  -- summation swap over the finite basis index
  have hswap : ∀ g : Fin (Module.finrank ℂ H) → ℤ → ℝ≥0∞,
      (∑' n : ℤ, ∑ i, g i n) = ∑ i, ∑' n : ℤ, g i n := by
    intro g
    rw [show (∑' n : ℤ, ∑ i, g i n) = ∑' n : ℤ, ∑' i, g i n from
      tsum_congr fun n => (tsum_fintype (f := fun i => g i n)).symm, ENNReal.tsum_comm]
    exact tsum_fintype (f := fun i => ∑' n : ℤ, g i n)
  have hpoint : ∀ n : ℤ, ‖iwConv A Φ f n‖ₑ ^ (2 : ℝ)
      = ∑ i, ‖iwConv A Φ (fun m => ⟪b i, f m⟫_ℂ) n‖ₑ ^ (2 : ℝ) := by
    intro n
    rw [enorm_sq_eq_sum b (iwConv A Φ f n)]
    exact Finset.sum_congr rfl fun i _ => by rw [inner_iwConv A Φ f hf (b i) n]
  have hparseval : ∀ x : H, ‖x‖ₑ ^ (2 : ℝ) = ∑ i, ‖⟪b i, x⟫_ℂ‖ₑ ^ (2 : ℝ) :=
    fun x => enorm_sq_eq_sum b x
  -- the squared coordinate Parseval identity
  have hcoord : (eLpNorm f 2 Measure.count) ^ (2 : ℝ)
      = ∑ i, (eLpNorm (fun m : ℤ => ⟪b i, f m⟫_ℂ) 2 Measure.count) ^ (2 : ℝ) := by
    rw [eLpNorm_two_rpow_two_count f]
    calc ∑' n : ℤ, ‖f n‖ₑ ^ (2 : ℝ)
        = ∑' n : ℤ, ∑ i, ‖⟪b i, f n⟫_ℂ‖ₑ ^ (2 : ℝ) := tsum_congr fun n => hparseval (f n)
      _ = ∑ i, ∑' n : ℤ, ‖⟪b i, f n⟫_ℂ‖ₑ ^ (2 : ℝ) := hswap _
      _ = ∑ i, (eLpNorm (fun m : ℤ => ⟪b i, f m⟫_ℂ) 2 Measure.count) ^ (2 : ℝ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [eLpNorm_two_rpow_two_count]
  have key : (eLpNorm (iwConv A Φ f) 2 Measure.count) ^ (2 : ℝ)
      ≤ (ENNReal.ofReal (C : ℝ) * eLpNorm f 2 Measure.count) ^ (2 : ℝ) := by
    rw [eLpNorm_two_rpow_two_count (iwConv A Φ f)]
    calc ∑' n : ℤ, ‖iwConv A Φ f n‖ₑ ^ (2 : ℝ)
        = ∑' n : ℤ, ∑ i, ‖iwConv A Φ (fun m => ⟪b i, f m⟫_ℂ) n‖ₑ ^ (2 : ℝ) :=
          tsum_congr hpoint
      _ = ∑ i, ∑' n : ℤ, ‖iwConv A Φ (fun m => ⟪b i, f m⟫_ℂ) n‖ₑ ^ (2 : ℝ) := hswap _
      _ = ∑ i, (eLpNorm (iwConv A Φ (fun m => ⟪b i, f m⟫_ℂ)) 2 Measure.count) ^ (2 : ℝ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [eLpNorm_two_rpow_two_count]
      _ ≤ ∑ i, (ENNReal.ofReal (C : ℝ)
            * eLpNorm (fun m : ℤ => ⟪b i, f m⟫_ℂ) 2 Measure.count) ^ (2 : ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            exact ENNReal.rpow_le_rpow (h _ (hcf i)) (by norm_num)
      _ = (ENNReal.ofReal (C : ℝ) * eLpNorm f 2 Measure.count) ^ (2 : ℝ) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), hcoord,
              Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  have hX : eLpNorm (iwConv A Φ f) 2 Measure.count
      = ((eLpNorm (iwConv A Φ f) 2 Measure.count) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
  have hY : ENNReal.ofReal (C : ℝ) * eLpNorm f 2 Measure.count
      = ((ENNReal.ofReal (C : ℝ) * eLpNorm f 2 Measure.count) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
  rw [hX, hY]
  exact ENNReal.rpow_le_rpow key (by norm_num)

/-- **The `q = 2` case of the multiplier half of Theorem `thm:iw`, for all finite dimensional
Hilbert spaces.**  This is the full `q = 2` instance of the conclusion of
`IWMultiplierBoundStatement`: the IW multiplier with symbol `periodize φ` is bounded on
`ℓ²(ℤ; H)` by `⟨l⟩ M` for every finite dimensional Hilbert space `H`, where `M ≥ ‖φ‖_∞` encodes
the continuous `L²(ℝ)` multiplier norm. -/
theorem IWMultiplierBound_q2_vector {ρ Cρ : ℝ} (hρ : 0 < ρ) (hCρ : 2 ≤ Cρ)
    (hNA : ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → NonAliasing k (iwArithFreqs ρ l))
    {l : ℕ} {k : ℤ} (hgood : GoodMajorArcs ρ Cρ l k)
    {φ : ℝ → ℂ} (hφm : Measurable φ) (hφ : ∀ x, φ x ≠ 0 → x ∈ realArc k)
    (hsum : ∀ x, Summable fun j : ℤ => φ (x + j))
    {M : NNReal} (hM : ∀ x, ‖φ x‖ ≤ (M : ℝ)) :
    IWLqBound (iwArithFreqs ρ l) (periodize φ) 2 (angleBracket l * M) :=
  IWLqBound_of_scalar_q2 _ _
    (IWMultiplierBoundScalar_q2 hρ hCρ hNA hgood hφm hφ hsum hM)

/-- **The complete `q = 2` instance of Theorem `thm:iw`**: the continuous `L²(ℝ)` multiplier bound
and the discrete `ℓ²(ℤ; H)` Ionescu–Wainger bound hold simultaneously, with the same constant
`M = ‖T_φ‖_{L²→L²} = ‖φ‖_∞`, uniformly over all finite dimensional Hilbert spaces `H`. -/
theorem IWMultiplierBoundStatement_q2_vector {ρ Cρ : ℝ} (hρ : 0 < ρ) (hCρ : 2 ≤ Cρ)
    (hNA : ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → NonAliasing k (iwArithFreqs ρ l))
    {l : ℕ} {k : ℤ} (hgood : GoodMajorArcs ρ Cρ l k)
    {φ : ℝ → ℂ} (hφm : Measurable φ) (hφ : ∀ x, φ x ≠ 0 → x ∈ realArc k)
    (hsum : ∀ x, Summable fun j : ℤ => φ (x + j))
    {M : NNReal} (hM : ∀ x, ‖φ x‖ ≤ (M : ℝ)) :
    IsLqMultiplierBound 2 φ M ∧
      IWLqBound (iwArithFreqs ρ l) (periodize φ) 2 (angleBracket l * M) :=
  ⟨isLqMultiplierBound_two hM,
    IWMultiplierBound_q2_vector hρ hCρ hNA hgood hφm hφ hsum hM⟩

end Work.Analysis.IWMultiplier
