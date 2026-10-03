import Mathlib
import Submission.Work.FIPiChain.HasB
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.S3zdev
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.window_marginsC
import Submission.Work.FITop.BformAtilEqXsum
import Submission.Work.FITop.AtilTauPowFourLe
import Submission.Work.FITop.Defs
import Submission.ASP.S7c
import Submission.ASP.S8b
import Submission.ASP.S20
import Submission.ASP.S21
import Submission.ASP.S22
import Submission.ASP.S23
import Submission.ASP.S24
import Submission.ASP.S25
import Submission.Work.FITop.SingleDvdTauSqLe
import Submission.Work.FITop.WindowRangeMarginsChain
import Submission.Work.FITop.BprimeWindowDelta1
import Submission.Work.FITop.RangeCheckChain
import Submission.ASP.S30
import Submission.Work.FITop.WolkeSquarefreeTau
import Submission.Work.FITop.AdTauAggregate
import Submission.Work.FITop.SumIteDivDvd
import Submission.Work.FIChain.rhoWindowC_param
import Submission.Work.FITop.RhoWindowCProp41
import Submission.Work.FIChain.Tsum_uniformAll
import Submission.Work.FIChain.Tsum2_uniformAll
import Submission.Work.FIChain.chainRangeFactsC
import Submission.Work.FIPiChain.Chain.chainRangeWideB
import Submission.Work.FIChain.LocalS6c
import Submission.Work.FIChain.assemblyC
import Submission.Work.FIPiChain.Chain.S3phiBDefs
import Submission.Work.FIPiChain.Chain.S3phiT_B
import Submission.Work.FIChain.S3plusC_machinery
import Submission.Work.FIPiChain.Chain.S3phiS1_B
import Submission.Work.FIPiChain.Chain.S3phiS2_B
import Submission.Work.FIPiChain.Chain.S3phiT2_B

set_option maxHeartbeats 4000000

open Work.FIChain

namespace Work.FIPiChain

variable [HasBc]

open Finset Filter MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-! ## 0. Why the statement below, as written, is not a sub-step (research log)

`S3phi_Bstar_v2` quantifies over the pair `(lam, C_sieve)` subject to `SieveInput` alone, while `K`
and the normalisation `H` are quantified *before* `x, lam, C_sieve`: the claim is *uniform in
`C_sieve`*.  Three verified facts show that this is not the lemma the endgame needs, and that it
cannot be obtained by the `§4–§7` transcription its docstring prescribes.

1. **`SieveInput` bounds `C_sieve` only from below.**  Its only occurrence of `C_sieve` is the
   sieve inequality `∑_{ν ≤ Δ, ♠} λ_ν (g ν · hSieve ν) ≤ C_sieve · ∏_{p < Δ} (1 − g p hSieve p)`,
   whose right-hand side is a *positive* multiple of `C_sieve` (`sieveProd_pos`).  For the trivial
   weight `λ = δ₁` (`λ 1 = 1`, `λ ν = 0` otherwise) all eight remaining conjuncts of `SieveInput`
   hold for free — `ρ ≡ 1`, so the two positivity conjuncts reduce to `g d ≥ 0` and `1 ≥ 0` — and
   the admissible constants are *exactly* `{C : 0 < C, 1 ≤ C·∏(…)}`, an upper-unbounded set:
   `SieveInput_lamδ_iff` and `exists_SieveInput_lamδ_large` in
   `Submission/Work/FIChain/S3phiBstarDefs.lean`.  So the statement must hold with one fixed `K`
   for `C_sieve` arbitrarily large.

2. **Every `§6` estimate available in this workspace is proportional to `C_sieve`.**
   `Submission.ASP.S1_bound_of_sieve` (`Submission/ASP/S6c.lean:763`; identical local copy
   `Work.FIChain.LocalS6c.S1_bound_of_sieve`, `LocalS6c.lean:763`) reads
   `|S₁| ≤ Ã·C₅·((δ₂)^ε·C_sieve·e^{32C₀}·C₁/log Δ) + log(M δ₂)·RemainderSum`, and its only access to
   `M₆` is `M6_le`, again with `C_sieve` (the crude `abs_S1_bd` is far too weak for a `loglog/log`
   rate).  The rate `Ã·loglog x/log x` that the docstring derives from it —
   `C₅ = L6 ≤ C₆(1+loglog x)` together with `(δ₂)^ε·C_sieve·e^{32C₀}·C₁ = O(1)` — needs precisely
   `C_sieve = O(1)`: that is the extra conjunct `C_sieve ≤ K` of `assemblyC`'s hypothesis `hsieve`
   (`Work.FIChain.assemblyC:485`), consumed at `:1083–1136` through `(d2n)^ε·Cs ≤ e²·Ksie`.

3. **At `λ = δ₁` the statement is as strong as the chapter's target.**  With `λ = δ₁` (`ρ ≡ 1`) the
   smoothed identity (3.4) (`S_eq_split`, `S_eq_y_smoothed`) reads
   `∑_{z < n ≤ x} a_n Λ(n) = Φ(z) + S3avgFix(z)`; the *`z`-averaged* `§8` bounds — the sorry-free
   `Work.FIChain.s3MainPlus_pt_le`, `s3RemPlus_zavg_le`, `S3plusC_zavg_le`, `S3minusC_zavg_le`, with
   the mean-value principle `exists_z1_le_of_measurable_zavg` — supply a `z₁` in the window with
   `|S3avgFix(z₁)| ≪ Ã(x)/log x`, so the claimed bound at `z₁` would give
   `|∑_{z₁ < n ≤ x} a_n Λ(n) − H·Ã(x)| ≪ Ã(x)·loglog x/log x`: the prime-sum asymptotic that
   `Work.FIChain.primeSum_bound_of_prop41`/`assemblyC` are engineered to produce, but *only* with
   the `Δ`-uniform sieve bound.  So the statement is not a strict sub-step: proving it would prove
   the chapter's theorem, and it cannot be reached by transcribing `§5–§8`.

(A fourth, smaller point: the `S₂`-summand is *itself* not derivable from `SieveInput` alone — the
companion's `(B′)`-window of §7 is available only from the frozen contract `Work.FIChain.Prop41Stmt`
(`Work.FIChain.windows_at_Bstar`, `Work.FITop.BprimeWindowOfProp41`); the statement below does carry
that hypothesis, so this is not a defect of the statement, but the corresponding sub-lemma
`Work.FIChain.S3phiS2_Bstar` without `h` was independently returned "mis-stated" for this reason.)

**Remedy, and what is proved in this file.**  Quantify the sieve weight *with* a uniform bound on its
constant: for a fixed `K₀ > 0` assume `SieveInput … lam C_sieve` **and `C_sieve ≤ K₀`**.  That is
exactly the shape in which the endgame's weight is available: `Work.FIChain.FIChainSieveGap` is
*proved* (`rosserLambda_FIgtil_r2`, module `Submission.Work.FIChain.FIChainSieveGap_discharged`),
i.e. for every `Δ ≥ 3` there is a weight with `SieveInput` and a `Δ`-uniform bound on `C_sieve`.
With that hypothesis the prescribed transcription goes through verbatim and is *proved* here:

* `Work.FIChain.S3phiT_Bstar` — the `T`-summand (unconditional);
* `Work.FIChain.S3phiT2_Bstar` — the `T₂`-summand, uniform over the `z`-window (unconditional);
* `Work.FIChain.S3phiS2_Bstar_of_prop41` — the `S₂`-summand from the `(B′)`-window;
* `Work.FIChain.S3phiS1_Bstar (K₀)` — the `S₁`-summand, *with* the uniform sieve bound `C_sieve ≤ K₀`;
* `Work.FIChain.s3phi_assembly` — the assembly (the integral identity
  `∫(T − T₂ + S₂ + S₁) dy/y = ∫T dy/y − ∫T₂ dy/y + ∫S₂ dy/y + ∫S₁ dy/y`, `∫_Y^{eY} dy/y = 1`, the
  triangle inequality and the constant bookkeeping);
* `Work.FIChain.S3phi_Bstar_v2_sieveBound` — the corrected statement;
* `Work.FIChain.S3phi_Bstar_v2_of_sieveGap` — the same from `FIChainSieveGap`.

Recommended restatement of the request: `S3phi_Bstar_v2_sieveBound` (and the matching private
`s3f_phi_Bstar` of `Submission/Work/FIChain/S3fixed_signed_le.lean`, which is consumed with the
weight of `rosserLambda_FIgtil_r2`, i.e. with `C_sieve ≤ Ksie`).
-/

/-- The elementary four-term triangle inequality `|A - B + C + D| ≤ |A|+|B|+|C|+|D|`. -/
lemma abs_four_le (A B C D : ℝ) : |A - B + C + D| ≤ |A| + |B| + |C| + |D| := by
  have h1 := abs_add_le (A - B + C) D
  have h2 := abs_add_le (A - B) C
  have h3 : |A - B| ≤ |A| + |B| :=
    abs_sub_le_iff.mpr ⟨by linarith [le_abs_self A, neg_le_abs B],
      by linarith [le_abs_self B, neg_le_abs A]⟩
  linarith [abs_nonneg (A - B), abs_nonneg (A - B + C), abs_nonneg (A - B + C + D)]

/-! ## 1. A pointwise bound integrates against `dy/y` to the same bound -/

/-- If `|f y| ≤ c` on `[Y, e·Y]` with `c ≥ 0` and `0 < Y`, then `|∫_Y^{eY} f y dy/y| ≤ c`
(because `∫_Y^{eY} dy/y = 1`). -/
lemma abs_integral_div_le {f : ℝ → ℝ} {Y c : ℝ} (hY : 0 < Y) (hc : 0 ≤ c)
    (h : ∀ y ∈ Set.Icc Y (Real.exp 1 * Y), |f y| ≤ c)
    (hf : IntervalIntegrable (fun y : ℝ => f y / y) volume Y (Real.exp 1 * Y)) :
    |(∫ y in Y..(Real.exp 1 * Y), f y / y)| ≤ c := by
  have hYle : Y ≤ Real.exp 1 * Y := le_mul_of_one_le_left hY.le (Real.one_le_exp (by norm_num))
  have hi2 : IntervalIntegrable (fun y : ℝ => c / y) volume Y (Real.exp 1 * Y) :=
    Submission.ASP.intervalIntegrable_div_of_bound' (f := fun _ : ℝ => c) measurable_const hY
      (fun u _ => by rw [abs_of_nonneg hc])
  have hmono : (∫ y in Y..(Real.exp 1 * Y), |f y / y|) ≤ ∫ y in Y..(Real.exp 1 * Y), c / y := by
    refine intervalIntegral.integral_mono_on hYle hf.abs hi2 (fun u hu => ?_)
    have hu0 : 0 < u := lt_of_lt_of_le hY hu.1
    rw [abs_div, abs_of_pos hu0]
    exact div_le_div_of_nonneg_right (h u hu) hu0.le
  calc |(∫ y in Y..(Real.exp 1 * Y), f y / y)|
      ≤ (∫ y in Y..(Real.exp 1 * Y), |f y / y|) :=
        intervalIntegral.abs_integral_le_integral_abs (f := fun y : ℝ => f y / y) hYle
    _ ≤ (∫ y in Y..(Real.exp 1 * Y), c / y) := hmono
    _ = c := intervalIntegral_const_div_exp c Y hY

/-! ## 2. The assembly of the four summand estimates -/

/-- **Assembly of the `§4–§7` bound** from the four per-summand estimates `P1` (`T`), `P2` (`T₂`),
`P3` (`S₂`, `y`-integrated) and `P4` (`S₁`, which consumes the uniform sieve bound
`C_sieve ≤ K₀`).  The point of this statement is the *assembly*: the identity
`∫(T − T₂ + S₂ + S₁)(y,z) dy/y = ∫T dy/y − ∫T₂ dy/y + ∫S₂ dy/y + ∫S₁ dy/y` together with
`∫_Y^{eY} dy/y = 1` (so that `H·Ã(x) = ∫ (H·Ã(x)) dy/y`), the triangle inequality, and the
constant bookkeeping. -/
theorem s3phi_assembly (K₀ : ℝ) (hK₀ : 0 < K₀)
    (P1 : ∃ K H : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x → s3phiCond x →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        SieveInput Submission.ASP.FIgtil (Deltac x) lam C_sieve →
        ∀ y ∈ s3phiYwin x,
          |s3phiT x lam y - H * AcountAtilC x| ≤ K * AcountAtilC x * s3phiRate x)
    (P2 : ∃ K : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x → s3phiCond x →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        SieveInput Submission.ASP.FIgtil (Deltac x) lam C_sieve →
        ∀ y ∈ s3phiYwin x, ∀ z ∈ s3phiZwin x,
          |s3phiT2 x lam y z| ≤ K * AcountAtilC x * s3phiRate x)
    (P3 : ∃ K : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x → s3phiCond x →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        SieveInput Submission.ASP.FIgtil (Deltac x) lam C_sieve →
        ∀ z ∈ s3phiZwin x,
          (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val), |s3phiS2 x lam y z| / y)
            ≤ K * AcountAtilC x * s3phiRate x)
    (P4 : ∃ K : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x → s3phiCond x →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        SieveInput Submission.ASP.FIgtil (Deltac x) lam C_sieve → C_sieve ≤ K₀ →
        ∀ y ∈ s3phiYwin x, ∀ z ∈ s3phiZwin x,
          |s3phiS1 x lam y z| ≤ K * AcountAtilC x * s3phiRate x) :
    ∃ K H : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x → s3phiCond x →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        SieveInput Submission.ASP.FIgtil (Deltac x) lam C_sieve → C_sieve ≤ K₀ →
        ∀ z ∈ s3phiZwin x,
          |s3phiPhi x lam z - H * AcountAtilC x| ≤ K * AcountAtilC x * s3phiRate x := by
  classical
  obtain ⟨K1, H, x1, hK1, hP1⟩ := P1
  obtain ⟨K2, x2, hK2, hP2⟩ := P2
  obtain ⟨K3, x3, hK3, hP3⟩ := P3
  obtain ⟨K4, x4, hK4, hP4⟩ := P4
  refine ⟨K1 + K2 + K3 + K4 + 1, H, max (max (max x1 x2) (max x3 x4)) 3, by positivity, ?_⟩
  intro x hx hcond lam Cs hSI hCs z hz
  rw [max_le_iff] at hx
  obtain ⟨hxAB, hx3nat⟩ := hx
  rw [max_le_iff] at hxAB
  obtain ⟨hx12, hx34⟩ := hxAB
  rw [max_le_iff] at hx12 hx34
  obtain ⟨hx1, hx2⟩ := hx12
  obtain ⟨hx3, hx4⟩ := hx34
  -- basic positivity
  have hx1R : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hYnonneg : 0 ≤ Yc x HasBc.val := by
    rw [Yc]
    exact div_nonneg (Real.sqrt_nonneg _)
      (mul_pos (pow_pos (by norm_num) _) (Real.rpow_pos_of_pos (Real.log_pos hx1R) _)).le
  have hYpos : 0 < Yc x HasBc.val := by
    rw [Yc]
    exact div_pos (Real.sqrt_pos.mpr (by linarith))
      (mul_pos (pow_pos (by norm_num) _) (Real.rpow_pos_of_pos (Real.log_pos hx1R) _))
  have hYle : Yc x HasBc.val ≤ Real.exp 1 * Yc x HasBc.val :=
    le_mul_of_one_le_left hYnonneg (Real.one_le_exp (by norm_num))
  have hsc1 : (1 : ℝ) ≤ sc x HasBc.val := by rw [sc]; exact one_le_pow₀ (by norm_num)
  have hscpos : (0 : ℝ) < sc x HasBc.val := lt_of_lt_of_le zero_lt_one hsc1
  have hA0 : 0 ≤ AcountAtilC x := Work.FITop.AcountAtil_nonneg' x
  have hx3R : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3nat
  have hlogx1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three, hx3R])
  have hR0 : 0 ≤ s3phiRate x := by
    rw [s3phiRate]
    exact div_nonneg (Real.log_nonneg hlogx1) (Real.log_pos hx1R).le
  -- the estimates
  have hE1 := hP1 x hx1 hcond lam Cs hSI
  have hE2 := hP2 x hx2 hcond lam Cs hSI
  have hE3 := hP3 x hx3 hcond lam Cs hSI z hz
  have hE4 := hP4 x hx4 hcond lam Cs hSI hCs
  -- integrability
  have hintT : IntervalIntegrable
      (fun y : ℝ => Submission.ASP.Tsum atilc lam (x : ℝ) y / y) volume (Yc x HasBc.val)
      (Real.exp 1 * Yc x HasBc.val) :=
    Submission.ASP.intervalIntegrable_Tsum_div atilc lam x hYpos
  have hintT2 : IntervalIntegrable
      (fun y : ℝ => Submission.ASP.Tsum2 atilc lam (x : ℝ) y z / y) volume (Yc x HasBc.val)
      (Real.exp 1 * Yc x HasBc.val) :=
    Submission.ASP.intervalIntegrable_Tsum2_div atilc lam x z hYpos
  have hintS2 : IntervalIntegrable
      (fun y : ℝ => Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y) / y) volume (Yc x HasBc.val)
      (Real.exp 1 * Yc x HasBc.val) :=
    Submission.ASP.intervalIntegrable_S2_div (z := z) atilc lam x hsc1 hYpos
  have hintS1 : IntervalIntegrable
      (fun y : ℝ => Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z) / y)
      volume (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val) :=
    Submission.ASP.intervalIntegrable_S1_div (z := z) atilc lam x hsc1 hYpos
  have hintc : IntervalIntegrable (fun y : ℝ => (H * AcountAtilC x) / y) volume (Yc x HasBc.val)
      (Real.exp 1 * Yc x HasBc.val) :=
    Submission.ASP.intervalIntegrable_div_of_bound' (f := fun _ : ℝ => H * AcountAtilC x)
      measurable_const hYpos (C := |H * AcountAtilC x|) (fun u _ => le_rfl)
  have hintTsub : IntervalIntegrable
      (fun y : ℝ => (Submission.ASP.Tsum atilc lam (x : ℝ) y - H * AcountAtilC x) / y)
      volume (Yc x HasBc.val) (Real.exp 1 * Yc x HasBc.val) :=
    (hintT.sub hintc).congr (fun y _ => by rw [sub_div])
  -- the integral identities
  have hconst : (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val), (H * AcountAtilC x) / y)
      = H * AcountAtilC x := intervalIntegral_const_div_exp _ _ hYpos
  have hsub : (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
        (Submission.ASP.Tsum atilc lam (x : ℝ) y - H * AcountAtilC x) / y)
      = (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            Submission.ASP.Tsum atilc lam (x : ℝ) y / y)
        - (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val), (H * AcountAtilC x) / y) := by
    rw [← intervalIntegral.integral_sub hintT hintc]
    exact intervalIntegral.integral_congr (fun y _ => by rw [sub_div])
  have hadd : (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
        (Submission.ASP.Tsum atilc lam (x : ℝ) y - Submission.ASP.Tsum2 atilc lam (x : ℝ) y z
          + Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y)
          + Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z)) / y)
      = (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            Submission.ASP.Tsum atilc lam (x : ℝ) y / y)
        - (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            Submission.ASP.Tsum2 atilc lam (x : ℝ) y z / y)
        + (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y) / y)
        + (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z) / y) := by
    have h12 : IntervalIntegrable (fun y : ℝ => (Submission.ASP.Tsum atilc lam (x : ℝ) y
        - Submission.ASP.Tsum2 atilc lam (x : ℝ) y z) / y) volume (Yc x HasBc.val)
        (Real.exp 1 * Yc x HasBc.val) :=
      (hintT.sub hintT2).congr (fun y _ => by rw [sub_div])
    have h34 : IntervalIntegrable (fun y : ℝ => (Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y)
        + Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z)) / y) volume (Yc x HasBc.val)
        (Real.exp 1 * Yc x HasBc.val) :=
      (hintS2.add hintS1).congr (fun y _ => by rw [add_div])
    rw [show (fun y : ℝ => (Submission.ASP.Tsum atilc lam (x : ℝ) y
          - Submission.ASP.Tsum2 atilc lam (x : ℝ) y z
          + Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y)
          + Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z)) / y)
        = fun y : ℝ => (Submission.ASP.Tsum atilc lam (x : ℝ) y
            - Submission.ASP.Tsum2 atilc lam (x : ℝ) y z) / y
          + (Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y)
            + Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z)) / y from by
      funext y; ring]
    rw [intervalIntegral.integral_add h12 h34]
    rw [show (fun y : ℝ => (Submission.ASP.Tsum atilc lam (x : ℝ) y
          - Submission.ASP.Tsum2 atilc lam (x : ℝ) y z) / y)
        = fun y : ℝ => Submission.ASP.Tsum atilc lam (x : ℝ) y / y
          - Submission.ASP.Tsum2 atilc lam (x : ℝ) y z / y from by funext y; ring]
    rw [show (fun y : ℝ => (Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y)
          + Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z)) / y)
        = fun y : ℝ => Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y) / y
          + Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z) / y from by
      funext y; ring]
    rw [intervalIntegral.integral_sub hintT hintT2, intervalIntegral.integral_add hintS2 hintS1]
    ring
  have hkey : s3phiPhi x lam z - H * AcountAtilC x
      = (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            (Submission.ASP.Tsum atilc lam (x : ℝ) y - H * AcountAtilC x) / y)
        - (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            Submission.ASP.Tsum2 atilc lam (x : ℝ) y z / y)
        + (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y) / y)
        + (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z) / y) := by
    have hphi : s3phiPhi x lam z
        = (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
              Submission.ASP.Tsum atilc lam (x : ℝ) y / y)
          - (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
              Submission.ASP.Tsum2 atilc lam (x : ℝ) y z / y)
          + (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
              Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y) / y)
          + (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
              Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z) / y) := by
      rw [s3phiPhi]
      exact hadd
    have hHA : H * AcountAtilC x
        = (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val), (H * AcountAtilC x) / y) :=
      hconst.symm
    calc s3phiPhi x lam z - H * AcountAtilC x
        = ((∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
              Submission.ASP.Tsum atilc lam (x : ℝ) y / y)
            - (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
              Submission.ASP.Tsum2 atilc lam (x : ℝ) y z / y)
            + (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
              Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y) / y)
            + (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
              Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z) / y))
          - (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val), (H * AcountAtilC x) / y) := by
          rw [hphi]
          linarith [hHA]
      _ = (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
              (Submission.ASP.Tsum atilc lam (x : ℝ) y - H * AcountAtilC x) / y)
            - (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
              Submission.ASP.Tsum2 atilc lam (x : ℝ) y z / y)
            + (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
              Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y) / y)
            + (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
              Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z) / y) := by
          linarith [hsub]
  -- the four bounds
  have hc1 : 0 ≤ K1 * AcountAtilC x * s3phiRate x :=
    mul_nonneg (mul_nonneg hK1.le hA0) hR0
  have hc2 : 0 ≤ K2 * AcountAtilC x * s3phiRate x :=
    mul_nonneg (mul_nonneg hK2.le hA0) hR0
  have hc3 : 0 ≤ K3 * AcountAtilC x * s3phiRate x :=
    mul_nonneg (mul_nonneg hK3.le hA0) hR0
  have hc4 : 0 ≤ K4 * AcountAtilC x * s3phiRate x :=
    mul_nonneg (mul_nonneg hK4.le hA0) hR0
  have hb1 : |(∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
        (Submission.ASP.Tsum atilc lam (x : ℝ) y - H * AcountAtilC x) / y)|
      ≤ K1 * AcountAtilC x * s3phiRate x :=
    abs_integral_div_le hYpos hc1
      (fun y hy => by simpa [s3phiT] using hE1 y hy) hintTsub
  have hb2 : |(∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
        Submission.ASP.Tsum2 atilc lam (x : ℝ) y z / y)|
      ≤ K2 * AcountAtilC x * s3phiRate x :=
    abs_integral_div_le hYpos hc2
      (fun y hy => by simpa [s3phiT2] using hE2 y hy z hz) hintT2
  have hb3 : |(∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
        Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y) / y)|
      ≤ K3 * AcountAtilC x * s3phiRate x := by
    refine le_trans
      (intervalIntegral.abs_integral_le_integral_abs
        (f := fun y : ℝ => Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y) / y) hYle) ?_
    have heq : (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
          |Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y) / y|)
        = (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            |Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y)| / y) := by
      refine intervalIntegral.integral_congr (fun y hy => ?_)
      have hy0 : 0 ≤ y := by
        have h1 := hy.1
        rw [min_eq_left hYle] at h1
        linarith [hYpos]
      rw [abs_div, abs_of_nonneg hy0]
    rw [heq]
    simpa [s3phiS2] using hE3
  have hb4 : |(∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
        Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z) / y)|
      ≤ K4 * AcountAtilC x * s3phiRate x :=
    abs_integral_div_le hYpos hc4
      (fun y hy => by simpa [s3phiS1] using hE4 y hy z hz) hintS1
  -- combine
  rw [hkey]
  have htri : |(∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
          (Submission.ASP.Tsum atilc lam (x : ℝ) y - H * AcountAtilC x) / y)
        - (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            Submission.ASP.Tsum2 atilc lam (x : ℝ) y z / y)
        + (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y) / y)
        + (∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z) / y)|
      ≤ |(∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            (Submission.ASP.Tsum atilc lam (x : ℝ) y - H * AcountAtilC x) / y)|
        + |(∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            Submission.ASP.Tsum2 atilc lam (x : ℝ) y z / y)|
        + |(∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            Submission.ASP.S2 atilc lam x y z (sc x HasBc.val * y) / y)|
        + |(∫ y in Yc x HasBc.val..(Real.exp 1 * Yc x HasBc.val),
            Submission.ASP.S1 atilc lam x (sc x HasBc.val * y) (sc x HasBc.val * z) / y)| :=
    abs_four_le _ _ _ _
  refine le_trans htri ?_
  have hsum0 : K1 * AcountAtilC x * s3phiRate x + K2 * AcountAtilC x * s3phiRate x
      + K3 * AcountAtilC x * s3phiRate x + K4 * AcountAtilC x * s3phiRate x
      = (K1 + K2 + K3 + K4) * (AcountAtilC x * s3phiRate x) := by ring
  have hlem : (K1 + K2 + K3 + K4) * (AcountAtilC x * s3phiRate x)
      ≤ (K1 + K2 + K3 + K4 + 1) * (AcountAtilC x * s3phiRate x) := by
    have h := mul_nonneg hA0 hR0
    nlinarith [h]
  have hfin : (K1 + K2 + K3 + K4 + 1) * (AcountAtilC x * s3phiRate x)
      = (K1 + K2 + K3 + K4 + 1) * AcountAtilC x * s3phiRate x := by ring
  linarith [hb1, hb2, hb3, hb4, hsum0.le, hlem, hfin.le]

/-! ## 3. The corrected statement, first with the `T₂`-input still abstract -/

/-- The assembly `Work.FIChain.s3phi_assembly` fed with the three summand estimates that are
available unconditionally (`T`-, `S₂`- and `S₁`-parts); the `T₂`-part is still a parameter. -/
theorem s3phi_of_three (Kbp : ℝ) (hKbp : 0 < Kbp) (xbp : ℕ)
    (hBwin : ∀ x : ℕ, xbp ≤ x → Work.FIChain.BprimeWindowInt atilc x wc
      (Kbp * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)))
      (Yc x HasBc.val / (Deltac x : ℝ)) (sc x HasBc.val * (Real.exp 1 * Yc x HasBc.val)))
    (K₀ : ℝ) (hK₀ : 0 < K₀)
    (P2 : ∃ K : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x → s3phiCond x →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        SieveInput Submission.ASP.FIgtil (Deltac x) lam C_sieve →
        ∀ y ∈ s3phiYwin x, ∀ z ∈ s3phiZwin x,
          |s3phiT2 x lam y z| ≤ K * AcountAtilC x * s3phiRate x) :
    ∃ K H : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x → s3phiCond x →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        SieveInput Submission.ASP.FIgtil (Deltac x) lam C_sieve → C_sieve ≤ K₀ →
        ∀ z ∈ s3phiZwin x,
          |s3phiPhi x lam z - H * AcountAtilC x| ≤ K * AcountAtilC x * s3phiRate x :=
  s3phi_assembly K₀ hK₀ S3phiT_Bstar P2 (S3phiS2_Bstar_of_window Kbp hKbp xbp hBwin)
    (S3phiS1_Bstar K₀ hK₀)

/-! ## 4. The corrected statement: the `§4–§7` bound with the uniform sieve bound `C_sieve ≤ K₀`

This is the *minimal edit* of the requested statement below that is provable by the prescribed
transcription: the sieve constant is asked to be bounded by the parameter `K₀`.  The endgame's
weight satisfies exactly this, with `K₀` the constant of `Work.FIChain.FIChainSieveGap`
(`Work.FIChain.rosserLambda_FIgtil_r2`, module `Submission.Work.FIChain.FIChainSieveGap_discharged`).
-/

/-- **The `§4–§7` part of the companion's identity (3.4), uniform over the `z`-window, for a sieve
weight whose constant `C_sieve` is bounded by `K₀`.**

The proof is the transcription prescribed by the docstring below, in its four summands
(`Work.FIChain.S3phiT_Bstar`, `S3phiT2_Bstar`, `S3phiS2_Bstar_of_prop41`,
`S3phiS1_Bstar`) assembled by `Work.FIChain.s3phi_of_three` /
`Work.FIChain.s3phi_assembly`. -/
theorem S3phi_Bstar_v2_sieveBound (Kbp : ℝ) (hKbp : 0 < Kbp) (xbp : ℕ)
    (hBwin : ∀ x : ℕ, xbp ≤ x → Work.FIChain.BprimeWindowInt atilc x wc
      (Kbp * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)))
      (Yc x HasBc.val / (Deltac x : ℝ)) (sc x HasBc.val * (Real.exp 1 * Yc x HasBc.val)))
    (K₀ : ℝ) (hK₀ : 0 < K₀) :
    ∃ K H : ℝ, ∃ x₀ : ℕ, 0 < K ∧ ∀ x : ℕ, x₀ ≤ x →
      (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 64) + 2 < Work.FIChain.Yc x HasBc.val / (Work.FIChain.Deltac x : ℝ) →
      ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
        Work.FIChain.SieveInput Submission.ASP.FIgtil (Work.FIChain.Deltac x) lam C_sieve →
        C_sieve ≤ K₀ →
        ∀ z ∈ Set.Icc (Work.FIChain.zc x HasBc.val) (Real.exp 1 * Work.FIChain.zc x HasBc.val),
          |(∫ y in Work.FIChain.Yc x HasBc.val..(Real.exp 1 * Work.FIChain.Yc x HasBc.val), (Submission.ASP.Tsum Work.FIChain.atilc lam (x : ℝ) y - Submission.ASP.Tsum2 Work.FIChain.atilc lam (x : ℝ) y z + Submission.ASP.S2 Work.FIChain.atilc lam x y z (Work.FIChain.sc x HasBc.val * y) + Submission.ASP.S1 Work.FIChain.atilc lam x (Work.FIChain.sc x HasBc.val * y) (Work.FIChain.sc x HasBc.val * z)) / y) - H * Work.FIChain.AcountAtilC x|
          ≤ K * Work.FIChain.AcountAtilC x * (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) :=
  s3phi_of_three Kbp hKbp xbp hBwin K₀ hK₀ S3phiT2_Bstar



end Work.FIPiChain
