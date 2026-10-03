/-
# `Submission.Work.FIArea6.S16CleanCoreTwo_of_invBound`

*FI* Lemma 16.2 in the **two-constant** form of `Work.FIArea6.S16CleanCoreTwo`: for the coefficient
of (5.13) on the *clean* support `IsPrimary ∧ NoSmallPrimes` (5.3)+(5.8),

  `‖Σ_z q(arg z − φ)·p(|z|²)·μ(|z|²)·γ(|z|²;C)·χ(z)·(z/|z|)^j‖`

  `≤ C·[exp(-η c (4d)^{-ε}√log N) + exp(-η log N/log P)]·(4d)·N·(log N)^6`,

with the exponent constant `c` and the prefactor `C` independent, from the Hecke `L`-function
inverse bound (16.23)/(16.24) (`Work.FITop4.Bridge.HeckeLcontInvBoundAll`).

## The decomposition used here

The clean support is `A ∧ B` with `A = IsPrimary` and `B = NoSmallPrimes`.  The fleet's §16 cores
carry **support** restrictions on top of it:

* the (5.9) divisor bound `τ(|z|²) ≤ Pa.τ` (*FI* p. 984 waives (5.9) after (10.4)),
* the round-6.1 axis-freeness `IsAxisFree Pa z` (the paper's §5 axis avoidance; since
  `θ ≤ ϑ² ≪ ϑ`, a sector lying within angular distance `≲ ϑ` of an axis is *entirely*
  non-axis-free, so the clause is not vacuous and cannot be reinstated by truncating `q`: a `C²`
  bump of width `θ - ϑ` has `|q^{(j)}| ≍ ϑ^{-j} ≫ θ^{-j}`, outside the mollifier class).

As `Work.FIArea6.S16TwoDefs` records for `S16CompTwo`, the clean support is the *disjoint* union

  `{A ∧ B} = {A ∧ B ∧ τ ≤ Pa.τ ∧ IsAxisFree} ⊔ {A ∧ B ∧ ¬(τ ≤ Pa.τ ∧ IsAxisFree)}`,

so the clean sum is, pointwise inside the norm, the sum of the two slice sums, and its bound
follows from the slice bounds by the triangle inequality: the prefactors add and the exponent
constant is the *minimum* of the two, since `c ↦ exp(-η c (4d)^{-ε}√log N)` is decreasing
(`min c₁ c₂ ≤ c₁` makes the first slot *larger*, i.e. the bound weaker) while the second slot
`exp(-η log N/log P)` is common.  This is the assembly `S16CleanCoreTwo_of_two`: clean from the
*radial* core and the *complement* (`S16RadialNoClassTwo`, `S16CompTwo`) — the form in which the
paper proceeds (§16 on the smooth support, then the two extra restrictions removed separately,
§10 for (5.9) and §5 / round 6.1 for the axis).

The two halves of the first assembly are provided, with the hypothesis `h` of this file, by the two
support-restricted §16 cores of the fleet's current critical path:

* `Work.FIArea6.TauPieces.RadialNoClassTwo` (`Submission/Work/FIArea6/TauPieces/RadialNoClassTwo.lean`)
  — the radial core `S16RadialNoClassTwo`, routed through the `S16SubCore`-shaped radial core
  `Work.FIArea6.S16SubCoreRadial_from_invBound`;
* `Work.FIArea6.S16CompTwoDirect_of_invBound`
  (`Submission/Work/FIArea6/S16CompTwoDirect_of_invBound.lean`) — the complement `S16CompTwo`,
  decomposed into the near-axis slice `S16SubCoreAxis` and the many-divisors slice
  `S16SubCoreTau` (`S16CompTwo_of_subCores`).

Both are *support-restricted* §16 cores (not the clean core itself), so this file is a genuine
assembly and not a restatement of its own conclusion.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.S16CoreDefs
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea6.S16MellinInversion
import Submission.Work.FIArea6.TauPieces.TsumHeartDefs
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6
namespace Trunc

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The §16 summand, the supports, and the exponential slots

All of these are `abbrev`s (transparent definitions), so that the `if`-conditions below carry the
*same* `Decidable` instances as the conditions in the statements of the §16 cores (`ite` is
congruent only for equal instances). -/

/-- The common summand of the §16 supports: `q(arg z − φ)·p(|z|²)·μ(|z|²)·γ(|z|²;C)·χ(z)·(z/|z|)^j`,
without its support indicator. -/
abbrev S16Term (Pa : Work.FITop.Params) (φ : ℝ) (j : ℤ) (chi : GaussianInt → ℂ)
    (q p : ℝ → ℝ) (z : GaussianInt) : ℂ :=
  ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
    * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
    * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
    * chi z
    * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j

/-- The *clean* §16 support of (5.13): primary `z`, free of small primes (5.8). -/
abbrev S16SuppClean (Pa : Work.FITop.Params) (z : GaussianInt) : Prop :=
  Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z

/-- The support of the *radial* cores: the clean support with the (5.9) divisor bound and the
round-6.1 axis-freeness. -/
abbrev S16SuppRadial (Pa : Work.FITop.Params) (z : GaussianInt) : Prop :=
  Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
    (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.IsAxisFree Pa z

/-- The complement of the radial support inside the clean support. -/
abbrev S16SuppComp (Pa : Work.FITop.Params) (z : GaussianInt) : Prop :=
  Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
    ¬((((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ Work.FITop4.IsAxisFree Pa z)

/-- The first exponential slot of the §16 bound, `exp(-η c (4d)^{-ε}√log N)`. -/
abbrev S16E1 (Pa : Work.FITop.Params) (c : ℝ) (d : ℕ) (ε : ℝ) : ℝ :=
  Real.exp (-(Pa.η * c * (((4 * d : ℕ) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N)))

/-- The second exponential slot of the §16 bound, `exp(-η log N/log P)`. -/
abbrev S16E2 (Pa : Work.FITop.Params) : ℝ :=
  Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ)))

/-- The polynomial tail `(4d)·N·(log N)^6` of the §16 bound. -/
abbrev S16Tail (Pa : Work.FITop.Params) (d : ℕ) : ℝ :=
  ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)

/-- The §16 right-hand side of prefactor `C'` in the `S16E1`/`S16E2`/`S16Tail` vocabulary equals
the displayed form in which the §16 cores state it. -/
lemma S16RH_eq (C' : ℝ) (Pa : Work.FITop.Params) (c : ℝ) (d : ℕ) (ε : ℝ) :
    C' * (S16E1 Pa c d ε + S16E2 Pa) * S16Tail Pa d
      = C' * (Real.exp (-(Pa.η * c * (((4 * d : ℕ) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
          + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
        * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by
  have h1 : S16E1 Pa c d ε = Real.exp (-(Pa.η * c * (((4 * d : ℕ) : ℝ)) ^ (-ε)
      * Real.sqrt (Real.log Pa.N))) := rfl
  have h2 : S16E2 Pa = Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))) := rfl
  have h3 : S16Tail Pa d = ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := rfl
  rw [h1, h2, h3]
  ring

/-! ## 2. The partitions of the clean support -/

/-- **Two-way partition** of the clean support into the radially restricted support and its
complement.  Off the clean support both sides vanish, on the radial support the complement term is
`0`, and on the complement the radial term is `0`. -/
lemma S16Term_split (Pa : Work.FITop.Params) (φ : ℝ) (j : ℤ) (chi : GaussianInt → ℂ)
    (q p : ℝ → ℝ) (z : GaussianInt) :
    (if S16SuppClean Pa z then S16Term Pa φ j chi q p z else 0)
      = (if S16SuppRadial Pa z then S16Term Pa φ j chi q p z else 0)
        + (if S16SuppComp Pa z then S16Term Pa φ j chi q p z else 0) := by
  by_cases hA : S16SuppClean Pa z
  · by_cases hD : (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧
        Work.FITop4.IsAxisFree Pa z
    · rw [if_pos hA, if_pos (show S16SuppRadial Pa z from ⟨hA.1, hA.2, hD⟩),
        if_neg (show ¬ S16SuppComp Pa z from fun hc => hc.2.2 hD), add_zero]
    · rw [if_pos hA, if_neg (show ¬ S16SuppRadial Pa z from fun hc => hD hc.2.2),
        if_pos (show S16SuppComp Pa z from ⟨hA.1, hA.2, hD⟩), zero_add]
  · rw [if_neg hA,
      if_neg (show ¬ S16SuppRadial Pa z from fun hc => hA ⟨hc.1, hc.2.1⟩),
      if_neg (show ¬ S16SuppComp Pa z from fun hc => hA ⟨hc.1, hc.2.1⟩), add_zero]

/-! ## 3. The arithmetic of combining §16 bounds -/

lemma S16E1_pos (Pa : Work.FITop.Params) (c : ℝ) (d : ℕ) (ε : ℝ) : 0 < S16E1 Pa c d ε :=
  Real.exp_pos _

lemma S16E2_pos (Pa : Work.FITop.Params) : 0 < S16E2 Pa := Real.exp_pos _

lemma S16Tail_nonneg (Pa : Work.FITop.Params) (d : ℕ) : 0 ≤ S16Tail Pa d := by
  have h4d : (0 : ℝ) ≤ ((4 * d : ℕ) : ℝ) := by positivity
  have hN : (0 : ℝ) ≤ Pa.N := le_trans zero_le_one Pa.hN1
  have hl : (0 : ℝ) ≤ Real.log Pa.N := Real.log_nonneg Pa.hN1
  show 0 ≤ ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)
  exact mul_nonneg (mul_nonneg h4d hN) (pow_nonneg hl 6)

/-- The first exponential slot is *decreasing* in its constant: a smaller `c` gives a weaker
(larger) bound. -/
lemma S16E1_mono (Pa : Work.FITop.Params) {c c' : ℝ} (hc : c' ≤ c) (d : ℕ) (ε : ℝ) :
    S16E1 Pa c d ε ≤ S16E1 Pa c' d ε := by
  show Real.exp (-(Pa.η * c * (((4 * d : ℕ) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
      ≤ Real.exp (-(Pa.η * c' * (((4 * d : ℕ) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
  apply Real.exp_le_exp.mpr
  have hη : 0 ≤ Pa.η := le_of_lt Pa.hη
  have hK : 0 ≤ (((4 * d : ℕ) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.sqrt_nonneg _)
  have h1 : Pa.η * c' ≤ Pa.η * c := mul_le_mul_of_nonneg_left hc hη
  have h2 : Pa.η * c' * ((((4 * d : ℕ) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N))
      ≤ Pa.η * c * ((((4 * d : ℕ) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N)) :=
    mul_le_mul_of_nonneg_right h1 hK
  linarith

/-- **Combining two §16 bounds of the two-constant shape**: the prefactors add and the exponent
constant is the smaller one. -/
lemma S16_two_add (C₁ C₂ A₁ A₂ A E T : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hT : 0 ≤ T)
    (h₁ : A₁ ≤ A) (h₂ : A₂ ≤ A) :
    C₁ * (A₁ + E) * T + C₂ * (A₂ + E) * T ≤ (C₁ + C₂) * (A + E) * T := by
  have hb₁ : C₁ * (A₁ + E) * T ≤ C₁ * (A + E) * T :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add h₁ le_rfl) hC₁) hT
  have hb₂ : C₂ * (A₂ + E) * T ≤ C₂ * (A + E) * T :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add h₂ le_rfl) hC₂) hT
  have hsplit : C₁ * (A + E) * T + C₂ * (A + E) * T = (C₁ + C₂) * (A + E) * T := by ring
  linarith [hb₁, hb₂]

open MeasureTheory Filter
open scoped Topology

lemma summable_tau_sq_mul_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-σ)) := by
  set ε : ℝ := (σ - 1) / 4 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨C, hCpos, hC⟩ := Commons.NumberTheory.DivisorBound.card_divisors_le_rpow ε hε
  have hexp : -(σ + 1) / 2 < -1 := by linarith
  have hmaj : Summable (fun n : ℕ => C ^ 2 * (n : ℝ) ^ (-(σ + 1) / 2)) :=
    (Real.summable_nat_rpow.mpr hexp).mul_left (C ^ 2)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmaj
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have h0 : ((0:ℕ):ℝ) = (0:ℝ) := by norm_num
    rw [h0, Real.zero_rpow (by linarith : -σ ≠ 0),
      Real.zero_rpow (by linarith : -(σ + 1) / 2 ≠ 0)]
    norm_num
  · have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hτ := hC n
    have hstep : ((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-σ)
        ≤ (C * (n : ℝ) ^ ε) ^ 2 * (n : ℝ) ^ (-σ) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hτ 2)
        (Real.rpow_nonneg hn.le _)
    refine hstep.trans (le_of_eq ?_)
    have key : ((n : ℝ) ^ ε) ^ 2 = (n : ℝ) ^ (2 * ε) := by
      have e1 : ((n : ℝ) ^ ε) ^ 2 = ((n : ℝ) ^ ε) ^ (((2:ℕ)) : ℝ) :=
        (Real.rpow_natCast ((n : ℝ) ^ ε) 2).symm
      have h : ((n : ℝ) ^ ε) ^ (((2:ℕ)) : ℝ) = (n : ℝ) ^ (ε * (((2:ℕ)) : ℝ)) :=
        (Real.rpow_mul hn.le ε (((2:ℕ)) : ℝ)).symm
      have e2 : (n : ℝ) ^ (ε * (((2:ℕ)) : ℝ)) = (n : ℝ) ^ (2 * ε) := by
        congr 1
        push_cast
        ring
      exact e1.trans (h.trans e2)
    rw [mul_pow, key]
    have hassoc : C ^ 2 * (n : ℝ) ^ (2 * ε) * (n : ℝ) ^ (-σ)
        = C ^ 2 * ((n : ℝ) ^ (2 * ε) * (n : ℝ) ^ (-σ)) := by ring
    rw [hassoc, ← Real.rpow_add hn]
    congr 1
    rw [hεdef]
    ring

/-! ## 2. Bounds on the coefficient `c(n)` of (16.30) -/

lemma abs_moebius_le_one (n : ℕ) : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> rw [h] <;> norm_num

lemma norm_moebius_le_one (n : ℕ) :
    ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> rw [h] <;> norm_num

lemma norm_gammaTrunc_le (C : ℝ) (n : ℕ) :
    ‖(Work.FIPlan.gammaTrunc C n : ℂ)‖ ≤ (n.divisors.card : ℝ) := by
  rw [Work.FIPlan.gammaTrunc, Complex.norm_real, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ C),
      |(ArithmeticFunction.moebius d : ℝ)| ≤
      ∑ _d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ C), (1 : ℝ) := by
    refine Finset.sum_le_sum (fun d _ => ?_)
    simpa using abs_moebius_le_one d
  have h2 : ∑ _d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ C), (1 : ℝ)
      = ((n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ C)).card : ℝ) := by simp
  have h3 : ((n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ C)).card : ℝ)
      ≤ (n.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_filter_le n.divisors _
  linarith

lemma tcoef_zero (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) :
    Work.FIArea6.TauPieces.tcoef Pa chi m 0 = 0 := by
  unfold Work.FIArea6.TauPieces.tcoef
  have h : ¬ Work.FIArea6Hecke.NoSmallPrimesNat Pa 0 := by
    intro hh
    exact hh 2 Nat.prime_two Pa.hP2 (dvd_zero 2)
  simp [h]

lemma norm_tcoef_le (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖Work.FIArea6.TauPieces.tcoef Pa chi m n‖ ≤ 4 * ((n.divisors.card : ℝ)) ^ 2 := by
  unfold Work.FIArea6.TauPieces.tcoef
  split_ifs with h
  · have hA := Work.FIArea5.S16Hecke.heckeLam_bound chi m hchi hn
    have hB := norm_moebius_le_one n
    have hC := norm_gammaTrunc_le Pa.C n
    have hτ : (0 : ℝ) ≤ (n.divisors.card : ℝ) := by positivity
    calc ‖Work.FIArea5.S16Hecke.heckeLam chi m n
            * ((ArithmeticFunction.moebius n : ℤ) : ℂ)
            * (Work.FIPlan.gammaTrunc Pa.C n : ℂ)‖
        = ‖Work.FIArea5.S16Hecke.heckeLam chi m n‖
            * ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖
            * ‖(Work.FIPlan.gammaTrunc Pa.C n : ℂ)‖ := by rw [norm_mul, norm_mul]
      _ ≤ (4 * (n.divisors.card : ℝ)) * 1 * (n.divisors.card : ℝ) := by
          refine mul_le_mul (mul_le_mul hA hB (norm_nonneg _) (by positivity)) hC
            (norm_nonneg _) (by positivity)
      _ = 4 * ((n.divisors.card : ℝ)) ^ 2 := by ring
  · rw [norm_zero]
    positivity

lemma summable_norm_tcoef_mul_rpow_neg (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ‖Work.FIArea6.TauPieces.tcoef Pa chi m n‖ * (n : ℝ) ^ (-σ)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_tau_sq_mul_rpow_neg hσ).mul_left 4)
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    rw [tcoef_zero]
    simp
  · have hτ : (0 : ℝ) ≤ (n.divisors.card : ℝ) := by positivity
    have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    calc ‖Work.FIArea6.TauPieces.tcoef Pa chi m n‖ * (n : ℝ) ^ (-σ)
        ≤ (4 * ((n.divisors.card : ℝ)) ^ 2) * (n : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right (norm_tcoef_le Pa chi m hchi hnpos) hpow
      _ = 4 * (((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-σ)) := by ring



/-- `mellinInv` with the scalar multiplications written as multiplications. -/
lemma mellinInv_eq (σ : ℝ) (F : ℂ → ℂ) (x : ℝ) :
    mellinInv σ F x = ((1 / (2 * Real.pi) : ℝ) : ℂ)
      * ∫ y : ℝ, ((x : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * Complex.I))
          * F ((σ : ℂ) + (y : ℂ) * Complex.I)) := by
  rw [mellinInv]
  simp only [Complex.real_smul, smul_eq_mul]

/-- The `M`-th partial-sum integrand of the Mellin representation of `Tsum`. -/
def partialIntegrand (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ)
    (σ : ℝ) (M : ℕ) (t : ℝ) : ℂ :=
  mellin (fun u : ℝ => (p u : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)
    * ∑ k ∈ (Finset.range M).filter (fun k => k ≠ 0),
        Work.FIArea6.TauPieces.tcoef Pa chi m k
          * ((k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))

/-- The limit integrand of the Mellin representation of `Tsum`. -/
def limitIntegrand (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ)
    (σ : ℝ) (t : ℝ) : ℂ :=
  mellin (fun u : ℝ => (p u : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)
    * Work.FIArea6.TauPieces.Zsfun Pa chi m ((σ : ℂ) + (t : ℂ) * Complex.I)



/-! ## 4. The Mellin representation of `Tsum` -/

theorem S16TsumMellinRep (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ)
    {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hθ1 : Pa.θ ≤ 1)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    (hpC : ContDiff ℝ 2 p) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hpsupp : ∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    (hd2 : ∀ u, |iteratedDeriv 2 p u| ≤ 1048576 / (Pa.θ * Pa.N) ^ 2) :
    Work.FIArea6Hecke.Tsum Pa chi m p
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, (mellin (fun u : ℝ => (p u : ℂ))
            ((σ : ℂ) + (t : ℂ) * Complex.I)
          * Work.FIArea6.TauPieces.Zsfun Pa chi m ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hN : 0 < Pa.N := lt_of_lt_of_le zero_lt_one Pa.hN1
  have hθ : 0 < Pa.θ := Pa.hθ0
  have hB : Pa.N ≤ (1 + Pa.θ) * Pa.N := by nlinarith
  have hσpos : 0 < σ := by linarith
  have hσhalf : (1 : ℝ) / 2 ≤ σ := by linarith
  have hpabs : ∀ u, |p u| ≤ 1 := fun u => abs_le.mpr ⟨by linarith [hp0 u], hp1 u⟩
  have hmellin_cont : Continuous (fun y : ℝ => mellin (fun u : ℝ => (p u : ℂ))
      ((σ : ℂ) + (y : ℂ) * Complex.I)) :=
    S16MellinVerticalContinuous p Pa.N ((1 + Pa.θ) * Pa.N) σ hN hB hpC.continuous hpabs hσpos
      hpsupp
  have hKsumm_of : ∀ s : ℂ, 1 < s.re →
      Summable (fun n : ℕ => ‖Work.FIArea6.TauPieces.tcoef Pa chi m n‖ * (n : ℝ) ^ (-s.re)) :=
    fun s hs => summable_norm_tcoef_mul_rpow_neg Pa chi m hchi hs
  have hZsumm : ∀ s : ℂ, 1 < s.re →
      Summable (fun k : ℕ => Work.FIArea6.TauPieces.tcoef Pa chi m k * (k : ℂ) ^ (-s)) := by
    intro s hs
    refine Summable.of_norm ?_
    refine (hKsumm_of s hs).congr (fun k => ?_)
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      rw [tcoef_zero]
      simp
    · have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
      rw [norm_mul, ← Complex.ofReal_natCast k, Complex.norm_cpow_eq_rpow_re_of_pos hkR]
      congr 1
  have hTsum_eq : Work.FIArea6Hecke.Tsum Pa chi m p
      = ∑' n : ℕ, Work.FIArea6.TauPieces.tcoef Pa chi m n * (p (n : ℝ) : ℂ) := by
    rw [Work.FIArea6Hecke.Tsum]
    refine tsum_congr (fun n => ?_)
    unfold Work.FIArea6.TauPieces.tcoef
    by_cases h : Work.FIArea6Hecke.NoSmallPrimesNat Pa n <;> simp [h, mul_assoc]
  have hsummp : Summable (fun n : ℕ =>
      Work.FIArea6.TauPieces.tcoef Pa chi m n * (p (n : ℝ) : ℂ)) := by
    refine summable_of_ne_finset_zero (s := Finset.Icc 1 ⌊(1 + Pa.θ) * Pa.N⌋₊) ?_
    intro n hn
    by_cases hn0 : n = 0
    · subst hn0
      rw [tcoef_zero, zero_mul]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      rw [Finset.mem_Icc, not_and_or] at hn
      have hM : ⌊(1 + Pa.θ) * Pa.N⌋₊ < n := by
        rcases hn with h | h
        · exact absurd hn1 h
        · exact not_le.mp h
      have hpz : p (n : ℝ) = 0 := by
        by_contra hne
        have h2 := (hpsupp (n : ℝ) hne).2
        have hle : ((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
          exact_mod_cast hM
        have h3 := Nat.lt_floor_add_one ((1 + Pa.θ) * Pa.N)
        linarith
      rw [hpz]
      simp
  have hTsumLim : Tendsto (fun M : ℕ => ∑ k ∈ Finset.range M,
      Work.FIArea6.TauPieces.tcoef Pa chi m k * (p (k : ℝ) : ℂ)) atTop
      (𝓝 (Work.FIArea6Hecke.Tsum Pa chi m p)) := by
    have h := hsummp.hasSum.tendsto_sum_nat
    rwa [← hTsum_eq] at h
  have hsingle : ∀ k : ℕ, 1 ≤ k →
      (∫ t : ℝ, (((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
          * mellin (fun u : ℝ => (p u : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)))
        = (((2 * Real.pi : ℝ)) : ℂ) * (p (k : ℝ) : ℂ) := by
    intro k hk
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hm := S16MellinInversion p Pa.N Pa.θ σ (k : ℝ) hN hθ hθ1 hpC hp0 hp1 hpsupp hd2
      hσhalf hσ2 hkR
    rw [mellinInv_eq] at hm
    have h2pi : (((2 * Real.pi : ℝ)) : ℂ) * (((1 / (2 * Real.pi) : ℝ)) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul]
      congr 1
      field_simp
    have hmul := congrArg (fun z : ℂ => (((2 * Real.pi : ℝ)) : ℂ) * z) hm
    rw [← mul_assoc, h2pi, one_mul] at hmul
    exact hmul
  have hsingle2 : ∀ k : ℕ, 1 ≤ k →
      (∫ t : ℝ, (mellin (fun u : ℝ => (p u : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)
          * (Work.FIArea6.TauPieces.tcoef Pa chi m k
              * ((k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))))))
        = Work.FIArea6.TauPieces.tcoef Pa chi m k
            * ((((2 * Real.pi : ℝ)) : ℂ) * (p (k : ℝ) : ℂ)) := by
    intro k hk
    have hcongr : (fun t : ℝ => mellin (fun u : ℝ => (p u : ℂ))
          ((σ : ℂ) + (t : ℂ) * Complex.I)
          * (Work.FIArea6.TauPieces.tcoef Pa chi m k
              * ((k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))))
        = fun t : ℝ => Work.FIArea6.TauPieces.tcoef Pa chi m k
            * ((((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
              * mellin (fun u : ℝ => (p u : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I))) := by
      funext t
      rw [Complex.ofReal_natCast]
      ring
    rw [hcongr, integral_const_mul, hsingle k hk]
  have hInt : ∀ k : ℕ, 1 ≤ k → Integrable (fun t : ℝ =>
      mellin (fun u : ℝ => (p u : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)
        * (Work.FIArea6.TauPieces.tcoef Pa chi m k
            * ((k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))))) := by
    intro k hk
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hkC : (k : ℂ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hcont : Continuous (fun t : ℝ => mellin (fun u : ℝ => (p u : ℂ))
        ((σ : ℂ) + (t : ℂ) * Complex.I)
          * (Work.FIArea6.TauPieces.tcoef Pa chi m k
              * ((k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))))) := by
      refine Continuous.mul hmellin_cont (Continuous.mul continuous_const ?_)
      rw [continuous_iff_continuousAt]
      intro t
      exact ContinuousAt.const_cpow (by fun_prop) (Or.inl hkC)
    refine Integrable.mono' (S16InvSqIntegrable Pa.θ
      (‖Work.FIArea6.TauPieces.tcoef Pa chi m k‖ * (k : ℝ) ^ (-σ)
        * (10000000 * Pa.θ * Pa.N ^ σ)) (ne_of_gt hθ)) hcont.aestronglyMeasurable ?_
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht
    have hmv := S16MellinVerticalBound p Pa.N Pa.θ σ hN hθ hθ1 hpC hp0 hp1 hpsupp hd2
      hσhalf hσ2 t ht
    have hkn : ‖((k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖ = (k : ℝ) ^ (-σ) := by
      rw [← Complex.ofReal_natCast k, Complex.norm_cpow_eq_rpow_re_of_pos hkR]
      congr 1
      simp
    rw [norm_mul, norm_mul, hkn]
    have h1 : (0 : ℝ) ≤ (k : ℝ) ^ (-σ) := Real.rpow_nonneg hkR.le _
    have h2 : (0 : ℝ) ≤ ‖Work.FIArea6.TauPieces.tcoef Pa chi m k‖ := norm_nonneg _
    calc ‖mellin (fun u : ℝ => (p u : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            * (‖Work.FIArea6.TauPieces.tcoef Pa chi m k‖ * (k : ℝ) ^ (-σ))
        ≤ (10000000 * Pa.θ * Pa.N ^ σ * (1 + (Pa.θ * t) ^ 2)⁻¹)
            * (‖Work.FIArea6.TauPieces.tcoef Pa chi m k‖ * (k : ℝ) ^ (-σ)) :=
          mul_le_mul_of_nonneg_right hmv (mul_nonneg h2 h1)
      _ = (‖Work.FIArea6.TauPieces.tcoef Pa chi m k‖ * (k : ℝ) ^ (-σ)
            * (10000000 * Pa.θ * Pa.N ^ σ)) * (1 + (Pa.θ * t) ^ 2)⁻¹ := by ring
  have hPlim : ∀ s : ℂ, 1 < s.re → Tendsto (fun M : ℕ =>
      ∑ k ∈ (Finset.range M).filter (fun k => k ≠ 0),
        Work.FIArea6.TauPieces.tcoef Pa chi m k * (k : ℂ) ^ (-s)) atTop
      (𝓝 (Work.FIArea6.TauPieces.Zsfun Pa chi m s)) := by
    intro s hs
    have hiff : (fun M : ℕ => ∑ k ∈ (Finset.range M).filter (fun k => k ≠ 0),
          Work.FIArea6.TauPieces.tcoef Pa chi m k * (k : ℂ) ^ (-s))
        = fun M : ℕ => ∑ k ∈ Finset.range M,
          Work.FIArea6.TauPieces.tcoef Pa chi m k * (k : ℂ) ^ (-s) := by
      funext M
      refine Finset.sum_filter_of_ne (fun k _ hne => ?_)
      rintro rfl
      exact hne (by rw [tcoef_zero, zero_mul])
    rw [hiff]
    exact (hZsumm s hs).hasSum.tendsto_sum_nat
  set K : ℝ := ∑' n : ℕ, ‖Work.FIArea6.TauPieces.tcoef Pa chi m n‖ * (n : ℝ) ^ (-σ) with hKdef
  have hKnn : 0 ≤ K := tsum_nonneg (fun n => mul_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hDCT : Tendsto (fun M : ℕ => ∫ t : ℝ, partialIntegrand Pa chi m p σ M t) atTop
      (𝓝 (∫ t : ℝ, limitIntegrand Pa chi m p σ t)) := by
    refine tendsto_integral_of_dominated_convergence (μ := volume)
      (fun t : ℝ => (10000000 * Pa.θ * Pa.N ^ σ * K) * (1 + (Pa.θ * t) ^ 2)⁻¹)
      ?_ ?_ ?_ ?_
    · intro M
      refine Continuous.aestronglyMeasurable ?_
      unfold partialIntegrand
      refine Continuous.mul hmellin_cont (continuous_finset_sum _ (fun k hk => ?_))
      have hk0 : k ≠ 0 := (Finset.mem_filter.mp hk).2
      have hkC : (k : ℂ) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        exact hk0
      refine Continuous.mul continuous_const ?_
      rw [continuous_iff_continuousAt]
      intro t
      exact ContinuousAt.const_cpow (by fun_prop) (Or.inl hkC)
    · exact S16InvSqIntegrable Pa.θ _ (ne_of_gt hθ)
    · intro M
      filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht
      have hmv := S16MellinVerticalBound p Pa.N Pa.θ σ hN hθ hθ1 hpC hp0 hp1 hpsupp hd2
        hσhalf hσ2 t ht
      rw [partialIntegrand, norm_mul]
      have hP : ‖∑ k ∈ (Finset.range M).filter (fun k => k ≠ 0),
          Work.FIArea6.TauPieces.tcoef Pa chi m k
            * ((k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖ ≤ K := by
        refine (norm_sum_le _ _).trans ?_
        have hle : ∑ k ∈ (Finset.range M).filter (fun k => k ≠ 0),
            ‖Work.FIArea6.TauPieces.tcoef Pa chi m k
              * ((k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖
            ≤ ∑ k ∈ (Finset.range M).filter (fun k => k ≠ 0),
              ‖Work.FIArea6.TauPieces.tcoef Pa chi m k‖ * (k : ℝ) ^ (-σ) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          have hk0 : k ≠ 0 := (Finset.mem_filter.mp hk).2
          have hkR : (0 : ℝ) < (k : ℝ) := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
          rw [norm_mul, ← Complex.ofReal_natCast k, Complex.norm_cpow_eq_rpow_re_of_pos hkR]
          congr 1
          simp
        refine hle.trans ?_
        refine Summable.sum_le_tsum ((Finset.range M).filter (fun k => k ≠ 0))
          (fun k _ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg k) _)) ?_
        simpa only [hKdef, Complex.ofReal_re] using hKsumm_of (σ : ℂ) (by simpa using hσ1)
      calc ‖mellin (fun u : ℝ => (p u : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            * ‖∑ k ∈ (Finset.range M).filter (fun k => k ≠ 0),
                Work.FIArea6.TauPieces.tcoef Pa chi m k
                  * ((k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖
          ≤ (10000000 * Pa.θ * Pa.N ^ σ * (1 + (Pa.θ * t) ^ 2)⁻¹) * K :=
            mul_le_mul hmv hP (norm_nonneg _) (by positivity)
        _ = (10000000 * Pa.θ * Pa.N ^ σ * K) * (1 + (Pa.θ * t) ^ 2)⁻¹ := by ring
    · filter_upwards with t
      have hs : 1 < (((σ : ℂ) + (t : ℂ) * Complex.I)).re := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
        simpa using hσ1
      have h1 : Tendsto (fun M : ℕ => mellin (fun u : ℝ => (p u : ℂ))
            ((σ : ℂ) + (t : ℂ) * Complex.I)
            * ∑ k ∈ (Finset.range M).filter (fun k => k ≠ 0),
                Work.FIArea6.TauPieces.tcoef Pa chi m k
                  * ((k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))) atTop
          (𝓝 (mellin (fun u : ℝ => (p u : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)
            * Work.FIArea6.TauPieces.Zsfun Pa chi m ((σ : ℂ) + (t : ℂ) * Complex.I))) :=
        tendsto_const_nhds.mul (hPlim ((σ : ℂ) + (t : ℂ) * Complex.I) hs)
      simpa only [partialIntegrand, limitIntegrand] using h1
  have hIntEq : ∀ M : ℕ, (∫ t : ℝ, partialIntegrand Pa chi m p σ M t)
      = ((((2 * Real.pi : ℝ)) : ℂ)) * ∑ k ∈ Finset.range M,
          Work.FIArea6.TauPieces.tcoef Pa chi m k * (p (k : ℝ) : ℂ) := by
    intro M
    have hfin : (∫ t : ℝ, partialIntegrand Pa chi m p σ M t)
        = ∑ k ∈ (Finset.range M).filter (fun k => k ≠ 0),
            Work.FIArea6.TauPieces.tcoef Pa chi m k
              * ((((2 * Real.pi : ℝ)) : ℂ) * (p (k : ℝ) : ℂ)) := by
      unfold partialIntegrand
      have hfun : (fun t : ℝ => mellin (fun u : ℝ => (p u : ℂ))
            ((σ : ℂ) + (t : ℂ) * Complex.I)
            * ∑ k ∈ (Finset.range M).filter (fun k => k ≠ 0),
                Work.FIArea6.TauPieces.tcoef Pa chi m k
                  * ((k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))))
          = fun t : ℝ => ∑ k ∈ (Finset.range M).filter (fun k => k ≠ 0),
              (mellin (fun u : ℝ => (p u : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)
                * (Work.FIArea6.TauPieces.tcoef Pa chi m k
                    * ((k : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))))) := by
        funext t
        rw [Finset.mul_sum]
      rw [hfun, integral_finset_sum]
      · exact Finset.sum_congr rfl (fun k hk =>
          hsingle2 k (Nat.one_le_iff_ne_zero.mpr (Finset.mem_filter.mp hk).2))
      · intro k hk
        exact hInt k (Nat.one_le_iff_ne_zero.mpr (Finset.mem_filter.mp hk).2)
    rw [hfin]
    have h1 : ∑ k ∈ (Finset.range M).filter (fun k => k ≠ 0),
          Work.FIArea6.TauPieces.tcoef Pa chi m k
            * ((((2 * Real.pi : ℝ)) : ℂ) * (p (k : ℝ) : ℂ))
        = ((((2 * Real.pi : ℝ)) : ℂ)) * ∑ k ∈ (Finset.range M).filter (fun k => k ≠ 0),
            Work.FIArea6.TauPieces.tcoef Pa chi m k * (p (k : ℝ) : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [h1]
    congr 1
    exact Finset.sum_filter_of_ne (fun k _ hne => by
      rintro rfl
      exact hne (by rw [tcoef_zero, zero_mul]))
  have hlim_int_sum : Tendsto (fun M : ℕ => ∫ t : ℝ, partialIntegrand Pa chi m p σ M t)
      atTop (𝓝 ((((2 * Real.pi : ℝ)) : ℂ) * Work.FIArea6Hecke.Tsum Pa chi m p)) := by
    have h2 := hTsumLim.const_mul ((((2 * Real.pi : ℝ)) : ℂ))
    simpa only [← hIntEq] using h2
  have huniq : (∫ t : ℝ, limitIntegrand Pa chi m p σ t)
      = ((((2 * Real.pi : ℝ)) : ℂ)) * Work.FIArea6Hecke.Tsum Pa chi m p :=
    tendsto_nhds_unique hDCT hlim_int_sum
  have h2pi_inv : (((1 / (2 * Real.pi) : ℝ)) : ℂ) * ((((2 * Real.pi : ℝ)) : ℂ)) = 1 := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  calc Work.FIArea6Hecke.Tsum Pa chi m p
      = ((((1 / (2 * Real.pi) : ℝ)) : ℂ) * ((((2 * Real.pi : ℝ)) : ℂ)))
          * Work.FIArea6Hecke.Tsum Pa chi m p := by rw [h2pi_inv, one_mul]
    _ = ((((1 / (2 * Real.pi) : ℝ)) : ℂ))
          * (∫ t : ℝ, limitIntegrand Pa chi m p σ t) := by rw [huniq]; ring
    _ = (1 / (2 * Real.pi)) * ∫ t : ℝ, (mellin (fun u : ℝ => (p u : ℂ))
            ((σ : ℂ) + (t : ℂ) * Complex.I)
          * Work.FIArea6.TauPieces.Zsfun Pa chi m ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
      have hc : (((1 / (2 * Real.pi) : ℝ)) : ℂ) = 1 / (2 * (Real.pi : ℂ)) := by
        push_cast
        ring
      rw [hc]
      congr 1


end

end Trunc

end Work.FIArea6
