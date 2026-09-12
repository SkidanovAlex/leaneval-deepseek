import Submission.HilbertMink
import Submission.Contracts
import Submission.EnergyHalf
import Submission.ArithmeticAssembly
import Submission.SerreHolder
import Submission.MuAtomFree
import Submission.SerrePotentialIcc
import Submission.LogProductMeasure
import Submission.WnormToolkit
/-!
# cor:neg_energy — the energy of the (arithmetic) Serre measure is ≤ 0

`cor_neg_energy_of_hilbert : Submission.HilbertMink.hilbertProp → EnergyHalf.energy ≤ 0`.

(`hilbertProp` = Smith prop:Hilbert for our Serre data; combined later with
`hilbert_of_mink mink_upper` this yields the unconditional `energy ≤ 0`.)
`energy = EnergyHalf.energy = ∫_ℝ U^μ dμ`, `U^μ = logPotential μ = log w`
(`w = WeightedNorm.weight μ` on all of ℝ), and `μ = muSerre =
serreMeasure gSerre aSerre bSerre` is arithmetic:
`ArithmeticAssembly.serre_arithmetic : ArithmeticOn μ`, i.e.
`∀ Q ≠ 0, 0 ≤ ∫ x, Real.log |aeval x Q| ∂μ`.

## Proof (paper GON.tex cor:neg_energy)

Fix `n ≥ 4` (large enough for the sign computations below; n ≥ 4 suffices).
From `hh : hilbertProp` at `n`: a family `Q : Fin (n+1) → Polynomial ℤ`,
`hlin` (ℚ-lin-indep via `MinkBox.LinIndepInt (n+1)`), `hdeg : ∀ i,
(Q i).natDegree ≤ n`, and
`hprod : ∏ i, wnorm n (zmap (Q i)) ≤ (n:ℝ)^(C0·n) · exp(½ n²·energy)`
(`⟨C0, hC0, hh0⟩ := hh`).

**Step 1 — pick `Q* := Q i0` with minimal norm.**  Let
`P i := zmap (Q i)`, `w i := wnorm n (P i)`.  All `w i ≥ 0`
(`WnormToolkit.wnorm_nonneg`).  Show `0 < ∏ i, w i` first: each `Q i ≠ 0`
(ℚ-lin-indep family) and `wnorm n (zmap (Q i)) > 0` (a nonzero polynomial is
not identically 0 on `[aSerre,bSerre]`, and `0 < w(x)` everywhere, so the sup
is `> 0`; find x0 with `(zmap (Q i)).eval x0 ≠ 0` — a nonzero real polynomial
has finitely many roots).  Then choose `i0 : Fin (n+1)` with
`w i0 ≤ (∏ i, w i) ^ (1 / (n+1))` (classical: exists via
`Finset.exists_le_prod_of_le`-style or by contradiction using
`Finset.prod_lt_prod`).  Write `Q* := Q i0`, `S := wnorm n (zmap Q*)`.

**Step 2 — combine arithmeticity with the norm bound.**  Arithmeticity at
`Q*` (need `Q* ≠ 0`, from `hlin`):
`0 ≤ A := ∫ x, Real.log |aeval x Q*| ∂μ`.  We will show
`A = B − n·energy` where `B := ∫ x, Real.log |aeval x Q*| + n · Real.log
(weight μ x) ∂μ` (use the pointwise identity
`Real.log |aeval x Q*| = (Real.log |aeval x Q*| + n·Real.log (weight μ x)) −
n·Real.log (weight μ x)` and `∫ n·log w dμ = n·energy`, the latter from
`Real.log (weight μ x) = logPotential μ (x:ℂ)` for every x
(`WeightedNorm.weight` def + `Real.log_exp`) and the definition of `energy`;
integrability of all terms: see Step 3).

**Step 3 — `B ≤ Real.log S`.**  For every `x ∈ [aSerre,bSerre]` with
`aeval x Q* ≠ 0`:
`Real.log |aeval x Q*| + n·Real.log (weight μ x) =
Real.log (|aeval x Q*| · (weight μ x)^n) ≤ Real.log S`
because `|aeval x Q*|·(weight μ x)^n ∈ {y ↦ ...}` and `S` is the sSup of that
set over `[aSerre,bSerre]` (prove an element-wise lemma
`wnorm_ge_pointwise`-style: every element of the defining set is `≤ S`, and
take logs — the set value is positive).  Since `μ` is supported in
`[aSerre,bSerre]` (`SupportConcentration.serre_compl_Icc`) and the set
`{x | aeval x Q* = 0}` has `μ`-measure zero (finitely many real roots:
`LogProductMeasure.measure_realRootSet_zero Q* hQ*` — real roots inside the
interval are a subset; or prove directly: the real roots of `Q*` are finitely
many and `MuAtomFree.serre_atom_free` makes singletons null), the inequality
holds `μ`-a.e., so `B ≤ Real.log S·μ(ℝ) = Real.log S` (need integrability of
`x ↦ log|aeval x Q*|` w.r.t. μ — model on
`ArithmeticAssembly`'s internal `hint_logQ'`/`LogProductMeasure` lemmas
(`sum_log_dist_integrable`, `log_dist_integrable`); and of
`x ↦ log(weight μ x)` — it equals `logPotential μ (x:ℂ)`, integrable by
`EnergyHalf.integrable_logPotential`-style results; combine with
`MeasureTheory.integral_mono_ae` / `integral_le_of_ae_le`).

**Step 4 — log-norm bound from the product.**  `Real.log S ≤ (Real.log
(∏ i, w i)) / (n+1) ≤ (C0·n·Real.log n + ½·n²·energy)/(n+1)` (log of
`hprod`; all `w i > 0`, `S > 0` so logs are defined; use
`Real.log_le_log`, `Real.log_mul`, `Real.log_rpow` carefully with positivity;
note `Real.log (exp u) = u`).

**Step 5 — conclude `energy ≤ 0`.**  Chaining:
`0 ≤ A = B − n·energy ≤ Real.log S − n·energy ≤ (C0·n·Real.log n +
½n²·energy)/(n+1) − n·energy`.
Multiply by `(n+1) > 0` and rearrange (all real arithmetic; the coefficient of
`energy` on the RHS is `½n² − n(n+1) = −(n²/2 + n) < 0` for `n ≥ 1`):
`0 ≤ C0·n·log n − energy·(n²/2 + n)`, i.e.
`energy ≤ C0·n·log n/(n²/2 + n) ≤ 2·C0·log n/n·(correction)`.  As this holds
for every `n ≥ 4` with the SAME `C0`, show `energy ≤ 0` by contradiction: if
`0 < energy`, choose `n ≥ 4` with `2·C0·Real.log (n:ℝ)/(n:ℝ) < energy`
(`tendsto` of `Real.log n / n` to 0 at top — use
`tendsto_log_div_self_atTop` or an elementary bound `Real.log n ≤ √n`-style:
for every `ε > 0` there is `N` with `∀ n ≥ N, 2C0 log n/n < ε`; you may
instead use `Filter.Tendsto` + `exists_lt_of_tendsto_atTop`-type results).

## Notes
* The final theorem statement needs no hypotheses other than `hh`; the
  arithmeticity and all measure facts are unconditional (verified elsewhere).
* You may import anything else from Mathlib or Submission and add helper
  lemmas (namespace `Submission.EnergyNeg`).
* No unresolved placeholders; `#print axioms` must show only `propext, Quot.sound,
  Classical.choice`.
-/


noncomputable section

open MeasureTheory
open Polynomial
open scoped Real ENNReal BigOperators Topology

namespace Submission.EnergyNeg

open Filter
open Submission.MinkBox
open Submission.Contracts
open Submission.HilbertMink
open Submission.EnergyHalf
open Submission.WeightedNorm
open Submission.SerreExample
open Submission.PotentialDefs
open Submission.PotentialContinuity
open Submission.WnormToolkit
open Submission.LogProductMeasure (rootMultiset serreMu ae_mem_Icc_serre realRootSet ae_log_q_eq_sum sum_log_dist_integrable measure_realRootSet_zero)
open Submission.ArithmeticAssembly (real_log_aeval_eq_complex aeval_complex_of_aeval arithmetic)
open Submission.Serre

instance muSerre_probability : IsProbabilityMeasure muSerre := by
  constructor
  unfold muSerre
  exact muS_univ

lemma muSerre_eq_muS : muSerre = muS := by
  unfold muSerre
  rfl

lemma muSerre_univ : muSerre Set.univ = 1 := by
  unfold muSerre
  exact muS_univ

lemma muSerre_Icc : muSerre (Set.Icc aSerre bSerre) = 1 := by
  unfold muSerre
  exact muS_Icc

lemma muSerre_compl_Icc : muSerre (Set.Icc aSerre bSerre)ᶜ = 0 := by
  unfold muSerre
  exact muS_compl_Icc

lemma ae_mem_Icc : (∀ᵐ x ∂muSerre, x ∈ Set.Icc aSerre bSerre) := by
  unfold muSerre
  exact ae_mem_Icc_serre

lemma integral_const_muSerre (c : ℝ) : (∫ x : ℝ, c ∂muSerre) = c := by
  rw [MeasureTheory.integral_const]
  rw [smul_eq_mul]
  rw [MeasureTheory.Measure.real_def]
  rw [muSerre_univ]
  norm_num

lemma log_weight_eq (x : ℝ) :
    Real.log (weight muSerre x) = logPotential muSerre (x : ℂ) := by
  unfold weight
  rw [Real.log_exp]

lemma log_weight_integrable : Integrable (fun x : ℝ => Real.log (weight muSerre x)) muSerre := by
  have h1 : Integrable (fun x : ℝ => logPotential muS (x : ℂ)) muS := integrable_logPotential
  have h1s : Integrable (fun x : ℝ => logPotential muS (x : ℂ)) muSerre := by
    rw [muSerre_eq_muS]
    exact h1
  refine h1s.congr ?_
  filter_upwards with x
  calc
    logPotential muS (x : ℂ) = logPotential muSerre (x : ℂ) := by unfold muSerre; rfl
    _ = Real.log (weight muSerre x) := (log_weight_eq x).symm

lemma log_weight_integral :
    (∫ x : ℝ, Real.log (weight muSerre x) ∂muSerre) = energy := by
  calc
    (∫ x : ℝ, Real.log (weight muSerre x) ∂muSerre)
        = (∫ x : ℝ, logPotential muSerre (x : ℂ) ∂muSerre) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            exact log_weight_eq x
    _ = energy := by
            unfold energy muSerre
            rfl

lemma aeval_eq_zmap_eval (Q : Polynomial ℤ) (x : ℝ) :
    Polynomial.aeval x Q = (zmap Q).eval x := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  rfl

lemma log_aeval_integrable (Q : Polynomial ℤ) (hQ : Q ≠ 0) :
    Integrable (fun x : ℝ => Real.log |Polynomial.aeval x Q|) muSerre := by
  have hpoint : (fun x : ℝ => Real.log |Polynomial.aeval x Q|) =ᵐ[muSerre]
      (fun x : ℝ => Real.log ‖Polynomial.aeval (x : ℂ) Q‖) := by
    filter_upwards with x
    exact real_log_aeval_eq_complex Q x
  let S : ℝ → ℝ := fun x => ((rootMultiset Q).map (fun z : ℂ => Real.log ‖(x : ℂ) - z‖)).sum
  let c : ℝ := Real.log ‖(((Q.leadingCoeff : ℤ) : ℂ))‖
  have hS : Integrable S muSerre := by
    simpa [S, muSerre] using (sum_log_dist_integrable Q)
  have hcS : Integrable (fun x : ℝ => c + S x) muSerre :=
    (MeasureTheory.integrable_const c).add hS
  have hae : (fun x : ℝ => c + S x) =ᵐ[muSerre]
      (fun x : ℝ => Real.log ‖Polynomial.aeval (x : ℂ) Q‖) := by
    have h0 := ae_log_q_eq_sum Q hQ
    simpa [c, S, muSerre] using h0.symm
  have hLint : Integrable (fun x : ℝ => Real.log ‖Polynomial.aeval (x : ℂ) Q‖) muSerre :=
    hcS.congr hae
  exact hLint.congr hpoint.symm


/-- the set where the real map vanishes is exactly the complex real-root set -/
lemma zeroSet_zmap_eq_realRootSet (Q : Polynomial ℤ) :
    {x : ℝ | (zmap Q).eval x = 0} = realRootSet Q := by
  ext x
  constructor
  · intro hx
    change Polynomial.aeval (x : ℂ) Q = 0
    have hx' : Polynomial.aeval x Q = 0 := by
      simpa [aeval_eq_zmap_eval] using hx
    have hc : ((Polynomial.aeval x Q : ℝ) : ℂ) = 0 := by
      simpa using congrArg (fun r : ℝ => (r : ℂ)) hx'
    rw [← aeval_complex_of_aeval Q x]
    exact hc
  · intro hx
    change Polynomial.aeval (x : ℂ) Q = 0 at hx
    have hc : ((Polynomial.aeval x Q : ℝ) : ℂ) = 0 := by
      rw [aeval_complex_of_aeval Q x]
      exact hx
    have hR : Polynomial.aeval x Q = 0 := Complex.ofReal_eq_zero.mp hc
    change (zmap Q).eval x = 0
    simpa [aeval_eq_zmap_eval] using hR

/-- roots of `Q` are `muSerre`-null -/
lemma realRootSet_null (Q : Polynomial ℤ) (hQ : Q ≠ 0) : muSerre (realRootSet Q) = 0 := by
  simpa [muSerre] using measure_realRootSet_zero Q hQ

/-- a nonzero integer polynomial has a point in the interval where its real map does not vanish -/
lemma exists_eval_ne_zero_in_Icc (Q : Polynomial ℤ) (hQ : Q ≠ 0) :
    ∃ x : ℝ, x ∈ Set.Icc aSerre bSerre ∧ (zmap Q).eval x ≠ 0 := by
  by_contra h
  have hall : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → (zmap Q).eval x = 0 := by
    intro x hx
    by_contra hx0
    exact h ⟨x, hx, hx0⟩
  have hsub : Set.Icc aSerre bSerre ⊆ realRootSet Q := by
    intro x hx
    rw [← zeroSet_zmap_eq_realRootSet Q]
    exact hall x hx
  have hmono : muSerre (Set.Icc aSerre bSerre) ≤ muSerre (realRootSet Q) := measure_mono hsub
  have hb : (0 : ℝ≥0∞) < 1 := by norm_num
  rw [muSerre_Icc, realRootSet_null Q hQ] at hmono
  exact (not_le_of_gt hb) hmono

/-- the weighted norm of the real map of a nonzero integer polynomial is positive -/
lemma wnorm_zmap_pos (n : ℕ) (Q : Polynomial ℤ) (hQ : Q ≠ 0) : 0 < wnorm n (zmap Q) := by
  rcases exists_eval_ne_zero_in_Icc Q hQ with ⟨x, hxmem, hx0⟩
  have hval : 0 < (weight muSerre x) ^ n * |(zmap Q).eval x| :=
    mul_pos (pow_pos (weight_pos muSerre x) n) (abs_pos.mpr hx0)
  have hle : (weight muSerre x) ^ n * |(zmap Q).eval x| ≤ wnorm n (zmap Q) :=
    wnorm_ge_pointwise n (zmap Q) hxmem
  exact lt_of_lt_of_le hval hle


/-- pointwise: on the interval away from roots, `log|Q(x)| + n·log w(x) ≤ log‖Q‖_{n}` -/
lemma pointwise_log_bound (Q : Polynomial ℤ) {n : ℕ} {x : ℝ}
    (hxI : x ∈ Set.Icc aSerre bSerre) (hx0 : (zmap Q).eval x ≠ 0) :
    Real.log |Polynomial.aeval x Q| + (n : ℝ) * Real.log (weight muSerre x) ≤
      Real.log (wnorm n (zmap Q)) := by
  let v : ℝ := (weight muSerre x) ^ n * |(zmap Q).eval x|
  have hvpos : 0 < v := by
    dsimp [v]
    exact mul_pos (pow_pos (weight_pos muSerre x) n) (abs_pos.mpr hx0)
  have hle : v ≤ wnorm n (zmap Q) := by
    dsimp [v]
    exact wnorm_ge_pointwise n (zmap Q) hxI
  have hSpos : 0 < wnorm n (zmap Q) := lt_of_lt_of_le hvpos hle
  have hlogle : Real.log v ≤ Real.log (wnorm n (zmap Q)) := Real.log_le_log hvpos hle
  have hlogv : Real.log v =
      Real.log |Polynomial.aeval x Q| + (n : ℝ) * Real.log (weight muSerre x) := by
    dsimp [v]
    calc
      Real.log ((weight muSerre x) ^ n * |(zmap Q).eval x|)
          = Real.log ((weight muSerre x) ^ n) + Real.log |(zmap Q).eval x| := by
              rw [Real.log_mul (pow_ne_zero n (ne_of_gt (weight_pos muSerre x)))
                (abs_ne_zero.mpr hx0)]
      _ = (n : ℝ) * Real.log (weight muSerre x) + Real.log |(zmap Q).eval x| := by
              rw [Real.log_pow]
      _ = Real.log |(zmap Q).eval x| + (n : ℝ) * Real.log (weight muSerre x) := by ring
      _ = Real.log |Polynomial.aeval x Q| + (n : ℝ) * Real.log (weight muSerre x) := by
              rw [← aeval_eq_zmap_eval Q x]
  rwa [← hlogv]

/-- a.e. version of the pointwise bound -/
lemma log_bound_ae (Q : Polynomial ℤ) (hQ : Q ≠ 0) (n : ℕ) :
    (fun x : ℝ => Real.log |Polynomial.aeval x Q| + (n : ℝ) * Real.log (weight muSerre x)) ≤ᵐ[muSerre]
      (fun _ : ℝ => Real.log (wnorm n (zmap Q))) := by
  change (∀ᵐ x ∂muSerre, Real.log |Polynomial.aeval x Q| + (n : ℝ) * Real.log (weight muSerre x) ≤
      Real.log (wnorm n (zmap Q)))
  rw [MeasureTheory.ae_iff]
  let bad : Set ℝ := {x : ℝ | ¬ (Real.log |Polynomial.aeval x Q| + (n : ℝ) * Real.log (weight muSerre x) ≤
      Real.log (wnorm n (zmap Q)))}
  have hsub : bad ⊆ (Set.Icc aSerre bSerre)ᶜ ∪ {x : ℝ | (zmap Q).eval x = 0} := by
    intro x hx
    by_cases hxI : x ∈ Set.Icc aSerre bSerre
    · by_cases hx0 : (zmap Q).eval x = 0
      · right
        exact hx0
      · left
        exfalso
        exact hx (pointwise_log_bound Q (n := n) hxI hx0)
    · left
      exact hxI
  have hz : muSerre {x : ℝ | (zmap Q).eval x = 0} = 0 := by
    rw [zeroSet_zmap_eq_realRootSet Q]
    exact realRootSet_null Q hQ
  have hu : muSerre ((Set.Icc aSerre bSerre)ᶜ ∪ {x : ℝ | (zmap Q).eval x = 0}) = 0 :=
    measure_union_null muSerre_compl_Icc hz
  exact measure_mono_null hsub hu

/-- arithmeticity, in `muSerre` form -/
lemma arithmetic_muSerre (Q : Polynomial ℤ) (hQ : Q ≠ 0) :
    0 ≤ (∫ x : ℝ, Real.log |Polynomial.aeval x Q| ∂muSerre) := by
  simpa [muSerre] using arithmetic Q hQ

/-- the fundamental per-polynomial bound: `n·energy ≤ log ‖Q‖_n`. -/
lemma energy_le_log_wnorm (Q : Polynomial ℤ) (hQ : Q ≠ 0) (n : ℕ) :
    (n : ℝ) * energy ≤ Real.log (wnorm n (zmap Q)) := by
  let f : ℝ → ℝ := fun x => Real.log |Polynomial.aeval x Q| +
      (n : ℝ) * Real.log (weight muSerre x)
  have hfint : Integrable f muSerre := by
    dsimp [f]
    exact (log_aeval_integrable Q hQ).add (log_weight_integrable.const_mul (n : ℝ))
  have hcst : Integrable (fun _ : ℝ => Real.log (wnorm n (zmap Q))) muSerre :=
    MeasureTheory.integrable_const _
  have hmono := MeasureTheory.integral_mono_ae (μ := muSerre) hfint hcst (log_bound_ae Q hQ n)
  have hmono' : (∫ x : ℝ, f x ∂muSerre) ≤ Real.log (wnorm n (zmap Q)) := by
    calc
      (∫ x : ℝ, f x ∂muSerre) ≤ (∫ x : ℝ, Real.log (wnorm n (zmap Q)) ∂muSerre) := hmono
      _ = Real.log (wnorm n (zmap Q)) := integral_const_muSerre _
  have hid : (∫ x : ℝ, f x ∂muSerre) =
      (∫ x : ℝ, Real.log |Polynomial.aeval x Q| ∂muSerre) + (n : ℝ) * energy := by
    calc
      (∫ x : ℝ, f x ∂muSerre)
          = (∫ x : ℝ, Real.log |Polynomial.aeval x Q| ∂muSerre) +
            (∫ x : ℝ, (n : ℝ) * Real.log (weight muSerre x) ∂muSerre) := by
              rw [show (fun x : ℝ => f x) = (fun x : ℝ => Real.log |Polynomial.aeval x Q| +
                  (n : ℝ) * Real.log (weight muSerre x)) by rfl]
              exact MeasureTheory.integral_add (log_aeval_integrable Q hQ)
                (log_weight_integrable.const_mul (n : ℝ))
      _ = (∫ x : ℝ, Real.log |Polynomial.aeval x Q| ∂muSerre) +
            (n : ℝ) * (∫ x : ℝ, Real.log (weight muSerre x) ∂muSerre) := by
              congr 1
              rw [MeasureTheory.integral_const_mul (n : ℝ) (fun x : ℝ => Real.log (weight muSerre x))]
      _ = (∫ x : ℝ, Real.log |Polynomial.aeval x Q| ∂muSerre) + (n : ℝ) * energy := by
              rw [log_weight_integral]
  calc
    (n : ℝ) * energy ≤ (∫ x : ℝ, Real.log |Polynomial.aeval x Q| ∂muSerre) + (n : ℝ) * energy := by
      nlinarith [arithmetic_muSerre Q hQ]
    _ = (∫ x : ℝ, f x ∂muSerre) := hid.symm
    _ ≤ Real.log (wnorm n (zmap Q)) := hmono'

/-- per-index `Q i` nonzero from linear independence -/
lemma Q_ne_zero_of_hlin {d : ℕ} (Q : Fin d → Polynomial ℤ)
    (hQ : LinIndepInt d Q) (i : Fin d) : Q i ≠ 0 := by
  intro hzero
  have hne0 : coeffVec d (Q i) ≠ 0 := hQ.ne_zero i
  apply hne0
  ext j
  simp [coeffVec, hzero]

/-- the per-`n` bound obtained by summing the per-polynomial bounds -/
lemma per_n_bound (C0 : ℝ) {n : ℕ} (hn : 2 ≤ n) (Q : Fin (n + 1) → Polynomial ℤ)
    (hlin : LinIndepInt (n + 1) Q)
    (hprod : (∏ i : Fin (n + 1), wnorm n (zmap (Q i))) ≤
      (n : ℝ) ^ (C0 * (n : ℝ)) * Real.exp ((1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy)) :
    energy * ((1 / 2 : ℝ) * (n : ℝ) + 1) ≤ C0 * Real.log (n : ℝ) := by
  let w : Fin (n + 1) → ℝ := fun i => wnorm n (zmap (Q i))
  have hQi : ∀ i : Fin (n + 1), Q i ≠ 0 := fun i => Q_ne_zero_of_hlin Q hlin i
  have hwpos : ∀ i : Fin (n + 1), 0 < w i := by
    intro i
    exact wnorm_zmap_pos n (Q i) (hQi i)
  have hind : ∀ i : Fin (n + 1), (n : ℝ) * energy ≤ Real.log (w i) := by
    intro i
    exact energy_le_log_wnorm (Q i) (hQi i) n
  have hsum0 : (∑ i : Fin (n + 1), ((n : ℝ) * energy)) ≤
      (∑ i : Fin (n + 1), Real.log (w i)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hind i
  have hsum_lhs : (∑ i : Fin (n + 1), ((n : ℝ) * energy)) =
      ((n + 1 : ℕ) : ℝ) * ((n : ℝ) * energy) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have hlogprod : (∑ i : Fin (n + 1), Real.log (w i)) = Real.log (∏ i : Fin (n + 1), w i) := by
    rw [Real.log_prod]
    intro i hi
    exact ne_of_gt (hwpos i)
  have hsum1 : ((n + 1 : ℕ) : ℝ) * ((n : ℝ) * energy) ≤ Real.log (∏ i : Fin (n + 1), w i) := by
    rw [← hlogprod, ← hsum_lhs]
    exact hsum0
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hBpos : 0 < (n : ℝ) ^ (C0 * (n : ℝ)) * Real.exp ((1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy) := by
    exact mul_pos (Real.rpow_pos_of_pos hnR _) (Real.exp_pos _)
  have hPpos : 0 < (∏ i : Fin (n + 1), w i) := Finset.prod_pos (fun i hi => hwpos i)
  have hlogprod_le : Real.log (∏ i : Fin (n + 1), w i) ≤
      C0 * (n : ℝ) * Real.log (n : ℝ) + (1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy := by
    have hle := Real.log_le_log hPpos hprod
    calc
      Real.log (∏ i : Fin (n + 1), w i)
          ≤ Real.log ((n : ℝ) ^ (C0 * (n : ℝ)) * Real.exp ((1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy)) := hle
      _ = Real.log ((n : ℝ) ^ (C0 * (n : ℝ))) +
            Real.log (Real.exp ((1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy)) := by
            rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hnR _)) (ne_of_gt (Real.exp_pos _))]
      _ = (C0 * (n : ℝ)) * Real.log (n : ℝ) + (1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy := by
            rw [Real.log_rpow hnR, Real.log_exp]
      _ = C0 * (n : ℝ) * Real.log (n : ℝ) + (1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy := by ring
  have hchain : ((n + 1 : ℕ) : ℝ) * ((n : ℝ) * energy) ≤
      C0 * (n : ℝ) * Real.log (n : ℝ) + (1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy :=
    le_trans hsum1 hlogprod_le
  have hchain' : ((n : ℝ) + 1) * ((n : ℝ) * energy) ≤
      C0 * (n : ℝ) * Real.log (n : ℝ) + (1 / 2 : ℝ) * (n : ℝ) ^ 2 * energy := by
    norm_num at hchain ⊢
    exact hchain
  have hlin1 : (n : ℝ) * (energy * ((1 / 2 : ℝ) * (n : ℝ) + 1)) ≤
      (n : ℝ) * (C0 * Real.log (n : ℝ)) := by
    nlinarith [hchain']
  by_contra hc
  have ha : C0 * Real.log (n : ℝ) < energy * ((1 / 2 : ℝ) * (n : ℝ) + 1) := lt_of_not_ge hc
  have hpos : 0 < (n : ℝ) * (energy * ((1 / 2 : ℝ) * (n : ℝ) + 1) - C0 * Real.log (n : ℝ)) := by
    exact mul_pos hnR (sub_pos.mpr ha)
  have hle0 : (n : ℝ) * (energy * ((1 / 2 : ℝ) * (n : ℝ) + 1) - C0 * Real.log (n : ℝ)) ≤ 0 := by
    nlinarith [hlin1]
  linarith


/-- the final theorem: energy of the Serre measure is non-positive. -/
theorem cor_neg_energy_of_hilbert (hh : hilbertProp) : energy ≤ 0 := by
  by_contra hnot
  have hE : 0 < energy := lt_of_not_ge hnot
  rcases hh with ⟨C0, hC0pos, hh0⟩
  have hper : ∀ n : ℕ, 2 ≤ n →
      energy * ((1 / 2 : ℝ) * (n : ℝ) + 1) ≤ C0 * Real.log (n : ℝ) := by
    intro n hn
    rcases hh0 n hn with ⟨Q, hlin, hdeg, hprod⟩
    exact per_n_bound C0 (n := n) hn Q hlin hprod
  have hbase : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    have hR := Real.tendsto_pow_log_div_mul_add_atTop (a := 1) (b := 0) 1 one_ne_zero
    have hR1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by simpa using hR
    simpa [Function.comp_def] using (hR1.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hscaled0 : Tendsto (fun n : ℕ => (2 * C0) * (Real.log (n : ℝ) / (n : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    simpa using (hbase.const_mul (2 * C0))
  have hbig : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ (2 * C0) * (Real.log (n : ℝ) / (n : ℝ)) < energy := by
    have hev2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
      Filter.eventually_atTop.mpr ⟨2, by intro b hb; exact hb⟩
    filter_upwards [hscaled0.eventually (Metric.ball_mem_nhds 0 hE), hev2] with n hn hn2
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hnR0 : 0 ≤ (n : ℝ) := le_of_lt hnR
    have hC0 : 0 ≤ 2 * C0 := mul_nonneg (by norm_num) (le_of_lt hC0pos)
    have hmag : |(2 * C0) * (Real.log (n : ℝ) / (n : ℝ))| < energy := by
      simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_pos hC0pos, abs_of_nonneg hC0, abs_div,
        abs_of_nonneg hnR0] using hn
    exact ⟨hn2, (abs_lt.mp hmag).2⟩
  rcases hbig.exists with ⟨n, hn2, hlt⟩
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlt2 : C0 * Real.log (n : ℝ) < energy * ((1 / 2 : ℝ) * (n : ℝ)) := by
    have h1 : 2 * C0 * Real.log (n : ℝ) < energy * (n : ℝ) := by
      have hm := (mul_lt_mul_of_pos_right hlt hnR)
      field_simp [ne_of_gt hnR] at hm
      nlinarith
    have hhalf := (mul_lt_mul_of_pos_left h1 (by norm_num : 0 < (1 / 2 : ℝ)))
    nlinarith [hhalf]
  have hbad := hper n hn2
  nlinarith [hbad, hlt2, hE]

end Submission.EnergyNeg
