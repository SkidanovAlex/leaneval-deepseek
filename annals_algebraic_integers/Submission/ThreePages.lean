import Submission.Quantile
import Submission.SerrePotentialIcc
import Submission.LogKernel
import Submission.PotentialDefs
import Submission.PotentialContinuity
import Submission.SerreHolder
import Submission.Contracts
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Polynomial

/-!
# Approximating polynomials (`prop:three_pages`, potential half)

For `μ = muS` on `[aSerre,bSerre]`, with quantile roots `α_i`
(`Quantile.alpha n i`, `cdf α_i = i/n`, `1 ≤ i ≤ n`), define the real monic
approximating polynomial `P_{n,μ} := ∏_{i=1}^n (X − α_i)`.  The goal of this
module is Smith's `eq:potential_approx` / `eq:explicit_pot_approx`
(prelim.tex `prop:three_pages`):

    | n·U^μ(x) + log|P_{n,μ}(x)| − log ρ_n(x) | ≤ C·log(n+2)

for `x ∈ [aSerre,bSerre]` with `ρ_n(x) := min_i |x − α_i| > 0` (i.e. `x` not
a root), where `U^μ(x) = logPotential muS (x:ℂ)`.  (Equivalently:
`w_μ(x)^n · |P_{n,μ}(x)| ≍ ρ_n(x)` for `x ∈ Σ` — `eq:potential_approx`.)

THE PAPER'S PROOF (prelim.tex `prop:three_pages`, with η = 1/2, C0 a bound
such that Σ ⊆ [−C0,C0]; we may take `C0 := bSerre` since 0 < aSerre < bSerre,
and note x ∈ Σ = [aSerre,bSerre] here):

1. `eq:relTone` (log-layer-cake identity): for `x ∈ [−C0,C0]`,
   U^{μ_n}(x) − U^μ(x) = ∫_0^{2C0} r⁻¹·(μ_n − μ)(I(x,r)) dr, where `μ_n` is
   the counting measure of the α_i (each atom 1/n) and `I(x,r) := [x−r,x+r]`.
   Derive it from the elementary identity `−log|x−t| = ∫_{|x−t|}^{R} r⁻¹ dr −
   log R` valid for `0 < |x−t| ≤ R` (Fubini/Tonelli), with
   `R := 2·bSerre` (or `bSerre − aSerre`): both μ and μ_n are supported in
   [aSerre,bSerre] so |x−t| ≤ bSerre−aSerre for x,t in the interval.
   Formally: for the ATOMIC side use the finite sum directly
   (`U^{μ_n}(x) := −(1/n)·Σ_{i=1}^n log|x−α_i|`), and for μ use the
   measure-level identity
   `(∫ t, −log|x−t| dμ) = −log(R)·μ(ℝ) + ∫_0^R r⁻¹·μ(Icc(x−r)(x+r)) dr`
   (from `log s = log R − ∫_s^R dr/r`, Fubini with the nonneg integrand
   `(r,t) ↦ r⁻¹·1_{|x−t| ≤ r}` over `(0,R] × [a,b]`, using
   `MeasureTheory.lintegral_prod`/Tonelli or the monotone-convergence
   theorems, converting ENNReal↔ℝ via `lintegral` finiteness).  The
   r-integral of `r⁻¹·μ(Icc(x−r)(x+r))` converges near 0 because
   `μ(Icc(x−r)(x+r)) ≤ C·√(2r)` (Hölder; `Quantile.exists_interval_holder`).

2. Set `δ := (1/3)·(C·n)^{-2}` where `C` comes from
   `Quantile.exists_spacing` (so gaps between consecutive α_i are ≥ (C·n)^{-2},
   hence the interval `(x−δ, x+δ)` contains at most one root; use
   `Quantile.at_most_one_root_in_short_interval` with s = 2δ < (C·n)^{-2}).

3. `eq:delta_mun`: for x not a root,
   `| (1/n)·log ρ(x) + ∫_0^δ r⁻¹·μ_n(I(x,r)) dr | ≤ (1/n)·log(max(δ⁻¹, 2·bSerre))`
   (if the unique root α at distance ρ ≤ δ is present the integral is
   `(1/n)·∫_ρ^δ dr/r = (1/n)(log δ − log ρ)` by `LogKernel`; else it is 0 and
   ρ ≥ δ).  In the final bound this term is absorbed (multiplied by n it is
   O(log n)).

4. `eq:delta_mu`: `∫_0^δ r⁻¹·μ(I(x,r)) dr ≤ C′·√δ` (Hölder), so after
   multiplying by n it is O(n·n^{-1}) = O(1) ≤ C·log n.

5. `eq:del3c0`: `|∫_δ^{2C0} r⁻¹·(μ_n − μ)(I(x,r)) dr| ≤ C/n·∫_δ^{2C0} dr/r =
   (C/n)·log(2C0/δ)` (no-telescope on intervals:
   `Quantile.exists_interval_no_telescope`); times n it is O(log n).

6. Sum: `| n·(U^{μ_n}(x) − U^μ(x)) − log ρ(x) | ≤ C·log(n+2)`; then since
   `−n·U^{μ_n}(x) = log|P_{n,μ}(x)|`, `n·(U^μ(x) − U^{μ_n}(x)) − log ρ =
   n·U^μ + log|P| − log ρ`, giving the theorem.  (Sign note: the bound is on
   `|n·U^μ + log|P| − log ρ|`.)

WORKING SUGGESTIONS:
* Work with REAL Bochner integrals; the atomic side is a finite sum
  (`Finset.sum`), the measure side uses `∫ t, ... ∂muS`; the r-integrals are
  `∫ r in a..b` (interval integrals) where needed, or improper handled via
  the layer-cake/lintegral lemmas.  You may introduce helper lemmas.
* Define `rho n x := (Finset.Icc 1 n).inf' ⟨1, by simp⟩ (fun i => |x − alpha n i|)`
  (Finset.inf' with a nonemptiness proof) — or any equivalent min over the
  finite index set; prove `rho_pos_of_not_root` and that if `0 < rho n x`
  then for the unique i with `rho n x = |x − alpha n i|` (some `i ∈ [1..n]`)
  no other root lies in `(x − δ, x + δ)`.
* `logPotential muS (x : ℂ) = ∫ t, -Real.log ‖(x:ℂ) − (t:ℂ)‖ ∂muS`, and for
  real x this is `∫ t, -Real.log |x − t| ∂muS`
  (`PotentialContinuity.log_norm_sub_ofReal`, use `integral_congr_ae`).
* You may need (and may prove) that the approximating poly is
  `(approxPoly n).eval x = ∏ (x − α_i)` with `|·|` distributed.
* Constants: keep the final bound with ∃-C; absorb everything into it.

Prove ALL of the following declarations (replacing the placeholder proofs). You may add any
number of helper lemmas and definitions. Keep the statements EXACTLY as
written. Do NOT change `approxPoly`, `rho`, or the main theorem.
-/

noncomputable section

open MeasureTheory
open Filter
open scoped Real ENNReal BigOperators
open Polynomial

namespace Submission.ThreePages

open Submission.PotentialDefs
open Submission.SerreExample
open Submission.PotentialContinuity
open Submission.Quantile
open Submission.Contracts
open Submission.WeightedNorm

/-- The degree-`n` approximating polynomial of `μ`
`P_{n,μ} = ∏_{i=1}^n (X − α_{n,i})`. -/
noncomputable def approxPoly (n : ℕ) : Polynomial ℝ :=
  ∏ i ∈ Finset.Icc 1 n, (Polynomial.X - Polynomial.C (alpha n i))

/-- `ρ_n(x) = min_{1 ≤ i ≤ n} |x − α_{n,i}|` (0 only at the roots). -/
noncomputable def rho (n : ℕ) (x : ℝ) : ℝ := by
  classical
  exact if h : (Finset.Icc 1 n).Nonempty then
    (Finset.Icc 1 n).inf' h (fun i : ℕ => |x - alpha n i|) else 0


/-- `Finset.Icc 1 n` is nonempty for `1 ≤ n`. -/
lemma Icc_one_n_nonempty {n : ℕ} (hn : 1 ≤ n) : (Finset.Icc 1 n).Nonempty :=
  ⟨1, by simp [hn]⟩

/-- For `1 ≤ n`, `rho n x` unfolds to the `inf'` over the index set. -/
lemma rho_eq_inf {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    rho n x = (Finset.Icc 1 n).inf' (Icc_one_n_nonempty hn) (fun i : ℕ => |x - alpha n i|) := by
  unfold rho
  rw [dif_pos (Icc_one_n_nonempty hn)]

/-- `rho n x` is a lower bound for all the root distances. -/
lemma rho_le_root {n : ℕ} (hn : 1 ≤ n) (x : ℝ) {i : ℕ} (hi : i ∈ Finset.Icc 1 n) :
    rho n x ≤ |x - alpha n i| := by
  rw [rho_eq_inf hn x]
  exact Finset.inf'_le (fun i : ℕ => |x - alpha n i|) hi

/-- `rho n x ≥ 0`. -/
lemma rho_nonneg {n : ℕ} (x : ℝ) : 0 ≤ rho n x := by
  by_cases hn : 1 ≤ n
  · rw [rho_eq_inf hn x]
    exact Finset.le_inf' (Icc_one_n_nonempty hn) (fun i : ℕ => |x - alpha n i|) (by intro i hi; exact abs_nonneg _)
  · unfold rho
    have hnot : ¬ (Finset.Icc 1 n).Nonempty := by
      intro h
      rcases h with ⟨j, hj⟩
      have hj1 : (1 : ℕ) ≤ j := (Finset.mem_Icc.mp hj).1
      have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
      omega
    rw [dif_neg hnot]

/-- There is an index attaining the minimum distance (`rho`) — strong form. -/
lemma exists_index_rho (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    ∃ i : ℕ, i ∈ Finset.Icc 1 n ∧ rho n x = |x - alpha n i| := by
  let s0 : Set ℝ := {y : ℝ | ∃ i : ℕ, i ∈ Finset.Icc 1 n ∧ y = |x - alpha n i|}
  have hm : (Finset.Icc 1 n).inf' (Icc_one_n_nonempty hn) (fun i : ℕ => |x - alpha n i|) ∈ s0 := by
    apply Finset.inf'_mem (s := s0) (t := Finset.Icc 1 n) (H := Icc_one_n_nonempty hn)
      (p := fun i : ℕ => |x - alpha n i|)
    · intro a ha b hb
      rcases ha with ⟨i, hi, rfl⟩
      rcases hb with ⟨j, hj, rfl⟩
      by_cases hab : |x - alpha n i| ≤ |x - alpha n j|
      · refine ⟨i, hi, ?_⟩
        exact min_eq_left hab
      · refine ⟨j, hj, ?_⟩
        exact min_eq_right (le_of_not_ge hab)
    · intro i hi
      exact ⟨i, hi, rfl⟩
  rcases hm with ⟨i, hi, hval⟩
  refine ⟨i, hi, ?_⟩
  rw [rho_eq_inf hn x]
  exact hval

/-- `(approxPoly n).eval x = ∏_{i=1}^n (x − α_i)` (monic, real). -/
lemma approxPoly_eval (n : ℕ) (x : ℝ) :
    (approxPoly n).eval x = ∏ i ∈ Finset.Icc 1 n, (x - alpha n i) := by
  unfold approxPoly
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

/-- `approxPoly n` is monic of degree n (for n ≥ 1). -/
lemma approxPoly_monic (n : ℕ) (hn : 1 ≤ n) : (approxPoly n).Monic := by
  unfold approxPoly
  exact Polynomial.monic_prod_of_monic (Finset.Icc 1 n) (fun i => Polynomial.X - Polynomial.C (alpha n i))
    (by intro i hi; exact Polynomial.monic_X_sub_C (alpha n i))

lemma approxPoly_natDegree (n : ℕ) (hn : 1 ≤ n) : (approxPoly n).natDegree = n := by
  unfold approxPoly
  have hmonic : ∀ i ∈ Finset.Icc 1 n,
      ((Polynomial.X - Polynomial.C (alpha n i)) : Polynomial ℝ).Monic := by
    intro i hi
    exact Polynomial.monic_X_sub_C (alpha n i)
  rw [Polynomial.natDegree_prod_of_monic (Finset.Icc 1 n) (fun i => Polynomial.X - Polynomial.C (alpha n i)) hmonic]
  have hsum : (∑ i ∈ Finset.Icc 1 n, ((Polynomial.X - Polynomial.C (alpha n i)).natDegree : ℕ)) = n := by
    calc
      (∑ i ∈ Finset.Icc 1 n, ((Polynomial.X - Polynomial.C (alpha n i)).natDegree : ℕ))
          = ∑ i ∈ Finset.Icc 1 n, (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact Polynomial.natDegree_X_sub_C (alpha n i)
      _ = (Finset.Icc 1 n).card := by simp
      _ = n := by
        have hcard : (Finset.Icc 1 n).card = n := by
          simpa using (Finset.card_Icc (a := 1) (b := n))
        rw [hcard]
  simpa using hsum

/-- If `0 < rho n x` then `x` is not a root of the approximating polynomial. -/
lemma rho_pos_eval_ne_zero {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < rho n x) :
    (approxPoly n).eval x ≠ 0 := by
  rw [approxPoly_eval]
  rw [Finset.prod_ne_zero_iff]
  intro i hi hzi
  have hle : rho n x ≤ |x - alpha n i| := rho_le_root hn x hi
  have hxeq : x = alpha n i := sub_eq_zero.mp hzi
  have hsub : |x - alpha n i| = 0 := by simp [hxeq]
  nlinarith

/-- For `n ≥ 1` and `x` with positive `ρ`, there is an index `i ∈ [1..n]`
attaining the minimum (nearest root). -/
lemma exists_index_eq_rho {n : ℕ} (hn : 1 ≤ n) (x : ℝ) (hx : 0 < rho n x) :
    ∃ i : ℕ, i ∈ Finset.Icc 1 n ∧ rho n x = |x - alpha n i| :=
  exists_index_rho n hn x

/-- The nearest-root distance for a root itself is 0: for `1 ≤ i ≤ n`,
`rho n (alpha n i) = 0`. -/
lemma rho_root_zero {n i : ℕ} (hn : 1 ≤ n) (hi : 1 ≤ i) (hin : i ≤ n) :
    rho n (alpha n i) = 0 := by
  apply le_antisymm
  · -- rho ≤ 0 via the root itself
    calc
      rho n (alpha n i) ≤ |alpha n i - alpha n i| := rho_le_root hn (alpha n i) (Finset.mem_Icc.mpr ⟨hi, hin⟩)
      _ = 0 := by simp
  · exact rho_nonneg (alpha n i)

/-- Distance-to-root-set is bounded by the interval length. -/
lemma rho_le_diam {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    rho n x ≤ bSerre - aSerre := by
  calc
    rho n x ≤ |x - alpha n 1| := rho_le_root hn x (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    _ ≤ bSerre - aSerre := by
      have halpha : alpha n 1 ∈ Set.Icc aSerre bSerre := alpha_mem_Icc hn (by omega) (by omega)
      have hxA : aSerre ≤ x := hx.1
      have hxB : x ≤ bSerre := hx.2
      have h1 : x - alpha n 1 ≤ bSerre - aSerre := by linarith [hxB, halpha.1]
      have h2 : alpha n 1 - x ≤ bSerre - aSerre := by linarith [halpha.2, hxA]
      exact abs_sub_le_iff.mpr ⟨h1, h2⟩

def Rserre : ℝ := bSerre - aSerre
lemma Rserre_pos : 0 < Rserre := by dsimp [Rserre]; linarith [a_lt_b]

lemma muS_atom_free (x : ℝ) : muS {x} = 0 := by
  simpa using (MuAtomFree.serre_atom_free x)

lemma ball_eq_Icc (x r : ℝ) : {t : ℝ | |t - x| ≤ r} = Set.Icc (x - r) (x + r) := by
  ext t
  constructor
  · intro ht
    change |t - x| ≤ r at ht
    rw [abs_le] at ht
    exact ⟨by linarith, by linarith⟩
  · intro ht
    rw [Set.mem_Icc] at ht
    change |t - x| ≤ r
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩

lemma ball_eq_Icc' (x r : ℝ) : {t : ℝ | |x - t| ≤ r} = Set.Icc (x - r) (x + r) := by
  simpa [abs_sub_comm] using ball_eq_Icc x r

lemma muS_pair_zero (x y : ℝ) : muS ({x, y} : Set ℝ) = 0 := by
  have hunion : muS (({x} : Set ℝ) ∪ {y}) = 0 := by
    apply MeasureTheory.measure_union_null
    · simpa using (muS_atom_free x)
    · simpa using (muS_atom_free y)
  apply le_antisymm
  · calc
      muS ({x, y} : Set ℝ) ≤ muS (({x} : Set ℝ) ∪ {y}) := measure_mono (by
        intro t ht
        simp at ht ⊢
        rcases ht with rfl | rfl <;> simp)
      _ = 0 := hunion
  · exact bot_le

def Mball (x r : ℝ) : ℝ := (muS (Set.Icc (x - r) (x + r))).toReal

lemma Mball_nonneg (x r : ℝ) : 0 ≤ Mball x r := ENNReal.toReal_nonneg

lemma Mball_mono {x : ℝ} {r s : ℝ} (hr0 : 0 ≤ r) (hrs : r ≤ s) : Mball x r ≤ Mball x s := by
  dsimp [Mball]
  exact Quantile.toReal_mono (by
    intro t ht
    rw [Set.mem_Icc] at ht
    rw [Set.mem_Icc]
    constructor <;> nlinarith [ht.1, ht.2, hrs, hr0])

/-- potential kernel in the tail variable: f(t) = -log(|x-t|/R) (0 at |x-t|=0). -/
def kernel (x R : ℝ) (t : ℝ) : ℝ := -Real.log (|x - t| / R)

/-- For s > 0, `{t | s ≤ kernel x R t} = Icc (x - R*e^{-s}) (x + R*e^{-s}) \ {x}`. -/
lemma tail_eq_ball_sdiff (x R s : ℝ) (hR : 0 < R) (hs : 0 < s) :
    {t : ℝ | s ≤ kernel x R t} =
      (Set.Icc (x - R * Real.exp (-s)) (x + R * Real.exp (-s))) \ {x} := by
  ext t
  constructor
  · intro ht
    have hsle : s ≤ kernel x R t := ht
    have htx : t ≠ x := by
      intro htx
      subst t
      dsimp [kernel] at hsle
      simp at hsle
      linarith
    constructor
    · have hdist : 0 < |x - t| := by
        rw [abs_pos]
        intro hsub
        apply htx
        linarith
      have hlog : Real.log (|x - t| / R) ≤ -s := by
        dsimp [kernel] at hsle
        linarith
      have hdiv_pos : 0 < |x - t| / R := div_pos hdist hR
      have hle := (Real.log_le_iff_le_exp hdiv_pos).mp hlog
      have hsmall : |x - t| ≤ R * Real.exp (-s) := by
        have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt hR)
        have hrewrite : |x - t| / R * R = |x - t| := by
          field_simp [ne_of_gt hR]
        rw [hrewrite] at hmul
        nlinarith [mul_comm (Real.exp (-s)) R]
      rw [Set.mem_Icc]
      rw [abs_le] at hsmall
      constructor <;> linarith
    · simpa using htx
  · intro ht
    rcases ht with ⟨hIcc, htx⟩
    have htxne : t ≠ x := by simpa using htx
    have hdist : 0 < |x - t| := by
      rw [abs_pos]
      intro hsub
      apply htxne
      linarith
    have hsmall : |x - t| ≤ R * Real.exp (-s) := by
      rw [Set.mem_Icc] at hIcc
      rw [abs_le]
      constructor <;> linarith
    have hlelog : Real.log (|x - t| / R) ≤ -s := by
      have hdivpos : 0 < |x - t| / R := div_pos hdist hR
      have hmono : Real.log (|x - t| / R) ≤ Real.log (R * Real.exp (-s) / R) := by
        apply Real.log_le_log hdivpos
        exact div_le_div_of_nonneg_right hsmall (le_of_lt hR)
      have hsimp : Real.log (R * Real.exp (-s) / R) = -s := by
        have hRne : R ≠ 0 := ne_of_gt hR
        field_simp [hRne]
        rw [Real.log_exp]
      linarith
    dsimp [kernel]
    linarith


/-- f := kernel x R is pointwise (for t ≠ x) equal to -log|x-t| + logR. -/
lemma kernel_eq_log (x R : ℝ) (hR : 0 < R) {t : ℝ} (ht : t ≠ x) :
    kernel x R t = -Real.log (|x - t|) + Real.log R := by
  have hdist : 0 < |x - t| := by
    rw [abs_pos]
    intro hsub
    apply ht
    linarith
  dsimp [kernel]
  rw [Real.log_div (ne_of_gt hdist) (ne_of_gt hR)]
  ring

/-- kernel x R = -log|x-t| + logR a.e. w.r.t. muS (exception t = x, null). -/
lemma kernel_ae_eq_log (x R : ℝ) (hR : 0 < R) :
    (fun t : ℝ => kernel x R t) =ᵐ[muS] (fun t : ℝ => -Real.log (|x - t|) + Real.log R) := by
  apply MeasureTheory.mem_ae_iff.mpr
  have hsubset : {t : ℝ | kernel x R t ≠ -Real.log (|x - t|) + Real.log R} ⊆ ({x} : Set ℝ) := by
    intro t ht
    by_contra htx
    have hk := kernel_eq_log x R hR htx
    exact ht hk
  exact measure_mono_null hsubset (by simpa using (muS_atom_free x))

/-- kernel x R is bounded by |log|x-t|| + |log R|. -/
lemma kernel_le_abs (x R : ℝ) (hR : 0 < R) (t : ℝ) :
    |kernel x R t| ≤ |Real.log (|x - t|)| + |Real.log R| := by
  by_cases ht : t = x
  · subst t
    dsimp [kernel]
    simp
  · have hk := kernel_eq_log x R hR ht
    rw [hk]
    calc
      |(-Real.log (|x - t|) + Real.log R)| ≤ |Real.log (|x - t|)| + |Real.log R| := by
        simpa [abs_neg] using (abs_add_le (-Real.log (|x - t|)) (Real.log R))
/-- kernel is integrable against muS. -/
lemma kernel_integrable (x R : ℝ) (hR : 0 < R) :
    MeasureTheory.Integrable (fun t : ℝ => kernel x R t) muS := by
  have hg : MeasureTheory.Integrable (fun t : ℝ => |Real.log (|x - t|)| + |Real.log R|) muS := by
    exact (logAbs_integrable x).add (MeasureTheory.integrable_const |Real.log R|)
  refine MeasureTheory.Integrable.mono' hg ?_ ?_
  · apply Measurable.aestronglyMeasurable
    dsimp [kernel]
    fun_prop
  · refine Filter.Eventually.of_forall (fun t => ?_)
    simpa [Real.norm_eq_abs] using kernel_le_abs x R hR t



/-- muS.real of the tail set {t : s ≤ kernel x R t} equals the ball mass at radius R·e^{-s}. -/
lemma real_tail_eq_Mball (x R s : ℝ) (hR : 0 < R) (hs : 0 < s) :
    muS.real {t : ℝ | s ≤ kernel x R t} = Mball x (R * Real.exp (-s)) := by
  change (muS {t : ℝ | s ≤ kernel x R t}).toReal =
    (muS (Set.Icc (x - R * Real.exp (-s)) (x + R * Real.exp (-s)))).toReal
  congr 1
  rw [tail_eq_ball_sdiff x R s hR hs]
  exact measure_sdiff_null (μ := muS) (s := Set.Icc (x - R * Real.exp (-s)) (x + R * Real.exp (-s)))
    (t := ({x} : Set ℝ)) (by simpa using (muS_atom_free x))

/-- Nonnegativity of the kernel at points of the interval (R = bSerre - aSerre). -/
lemma kernel_nonneg_at (x : ℝ) (hx : x ∈ Set.Icc aSerre bSerre) {t : ℝ}
    (ht : t ∈ Set.Icc aSerre bSerre) : 0 ≤ kernel x Rserre t := by
  have hxR : |x - t| ≤ Rserre := by
    rw [abs_sub_le_iff]
    constructor <;> dsimp [Rserre] <;> linarith [hx.1, hx.2, ht.1, ht.2]
  by_cases htx : t = x
  · subst t
    dsimp [kernel]
    simp
  · have hk := kernel_eq_log x Rserre Rserre_pos htx
    have hdist0 : 0 < |x - t| := by
      rw [abs_pos]
      intro hsub
      apply htx
      linarith
    have hdiv_le : |x - t| / Rserre ≤ 1 := by
      rw [div_le_one Rserre_pos]
      exact hxR
    have hlog0 : 0 ≤ -Real.log (|x - t|) + Real.log Rserre := by
      have hle' : Real.log (|x - t|) ≤ Real.log Rserre := Real.log_le_log hdist0 hxR
      linarith
    rwa [hk]

/-- Nonnegativity of the kernel a.e. (uses support in [aSerre,bSerre]). -/
lemma kernel_nonneg_ae (x : ℝ) (hx : x ∈ Set.Icc aSerre bSerre) :
    0 ≤ᵐ[muS] fun t : ℝ => kernel x Rserre t := by
  apply MeasureTheory.mem_ae_iff.mpr
  have hsubset : {t : ℝ | ¬ 0 ≤ kernel x Rserre t} ⊆ (Set.Icc aSerre bSerre)ᶜ := by
    intro t ht
    by_contra htI
    have htI' : t ∈ Set.Icc aSerre bSerre := by simpa using htI
    exact ht (kernel_nonneg_at x hx htI')
  have hsubnull : muS {t : ℝ | ¬ 0 ≤ kernel x Rserre t} = 0 := by
    exact measure_mono_null (μ := muS) hsubset (by simpa using PotentialContinuity.muS_compl_Icc)
  simpa [Set.compl_setOf, not_le] using hsubnull

/-- log potential on reals equals integral of -log|x-t|. -/
lemma logPotential_eq_integral_log (x : ℝ) :
    logPotential muS (x : ℂ) = (∫ t : ℝ, -Real.log (|x - t|) ∂muS) := by
  unfold logPotential
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall (fun t : ℝ => log_norm_sub_ofReal x t)

/-- Layer cake for the kernel (real form). -/
lemma layerCakeTail (x : ℝ) (hx : x ∈ Set.Icc aSerre bSerre) :
    (∫ s : ℝ in Set.Ioi 0, Mball x (Rserre * Real.exp (-s))) =
      logPotential muS (x : ℂ) + Real.log Rserre := by
  -- layer cake for f = kernel x Rserre
  have hf_int : MeasureTheory.Integrable (fun t : ℝ => kernel x Rserre t) muS :=
    kernel_integrable x Rserre Rserre_pos
  have hf_nn : 0 ≤ᵐ[muS] fun t : ℝ => kernel x Rserre t := kernel_nonneg_ae x hx
  have hLC := MeasureTheory.Integrable.integral_eq_integral_meas_le (μ := muS)
    (f := fun t : ℝ => kernel x Rserre t) hf_int hf_nn
  -- RHS integrand equality (pointwise on s > 0)
  have hRHS : (∫ s : ℝ in Set.Ioi 0, muS.real {a : ℝ | s ≤ kernel x Rserre a})
      = (∫ s : ℝ in Set.Ioi 0, Mball x (Rserre * Real.exp (-s))) := by
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
    apply Filter.Eventually.of_forall
    intro s hs
    exact real_tail_eq_Mball x Rserre s Rserre_pos (Set.mem_Ioi.mp hs)
  -- LHS
  have hLHS : (∫ t : ℝ, kernel x Rserre t ∂muS) = logPotential muS (x : ℂ) + Real.log Rserre := by
    have hae := kernel_ae_eq_log x Rserre Rserre_pos
    calc
      (∫ t : ℝ, kernel x Rserre t ∂muS)
          = (∫ t : ℝ, -Real.log (|x - t|) + Real.log Rserre ∂muS) :=
            MeasureTheory.integral_congr_ae hae
      _ = logPotential muS (x : ℂ) + Real.log Rserre := by
        have hsub : (∫ t : ℝ, -Real.log (|x - t|) + Real.log Rserre ∂muS)
            = (∫ t : ℝ, -Real.log (|x - t|) ∂muS) + Real.log Rserre * (muS Set.univ).toReal := by
          rw [MeasureTheory.integral_add]
          · rw [MeasureTheory.integral_const]
            rw [smul_eq_mul, MeasureTheory.Measure.real_def]
            rw [muS_univ]
            norm_num
          · simpa using (log_integrable x).neg
          · exact MeasureTheory.integrable_const (Real.log Rserre)
        rw [hsub]
        rw [logPotential_eq_integral_log]
        have hmu : (muS Set.univ).toReal = 1 := by
          simp
        rw [hmu, mul_one]
  calc
    (∫ s : ℝ in Set.Ioi 0, Mball x (Rserre * Real.exp (-s)))
        = (∫ s : ℝ in Set.Ioi 0, muS.real {a : ℝ | s ≤ kernel x Rserre a}) := hRHS.symm
    _ = (∫ t : ℝ, kernel x Rserre t ∂muS) := hLC.symm
    _ = logPotential muS (x : ℂ) + Real.log Rserre := hLHS


/-- Radius in the tail variable: `r(s) = Rserre·e^{-s}`. -/
def tailRad (s : ℝ) : ℝ := Rserre * Real.exp (-s)

/-- The μ-mass of the tail ball of radius `Rserre·e^{-s}`. -/
noncomputable def tailMass (x s : ℝ) : ℝ := Mball x (tailRad s)

/-- Number of roots `α_i` (i in `[1..n]`) inside the tail ball of radius `Rserre·e^{-s}`. -/
def tailCount (n : ℕ) (x s : ℝ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun i : ℕ => alpha n i ∈ Set.Icc (x - tailRad s) (x + tailRad s))).card

/-- layer cake in terms of `tailMass`. -/
lemma layerCake_tailMass (x : ℝ) (hx : x ∈ Set.Icc aSerre bSerre) :
    (∫ s : ℝ in Set.Ioi 0, tailMass x s) = logPotential muS (x : ℂ) + Real.log Rserre := by
  have h := layerCakeTail x hx
  simpa [tailMass, tailRad] using h

/-- For a non-root `x`, `|P_n(x)| = ∏ |x − α_i|` and its log is the sum of the logs. -/
lemma log_abs_eval (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hrho : 0 < rho n x) :
    Real.log |(approxPoly n).eval x| = ∑ i ∈ Finset.Icc 1 n, Real.log (|x - alpha n i|) := by
  have hfac_ne : ∀ i ∈ Finset.Icc 1 n, |x - alpha n i| ≠ 0 := by
    intro i hi
    have hle : rho n x ≤ |x - alpha n i| := rho_le_root hn x hi
    exact ne_of_gt (lt_of_lt_of_le hrho hle)
  rw [approxPoly_eval]
  rw [Finset.abs_prod]
  rw [Real.log_prod hfac_ne]


/-- Root distances to x are in `(0, Rserre]` (non-root, x in interval). -/
lemma root_dist_pos {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hrho : 0 < rho n x) :
    ∀ i : ℕ, i ∈ Finset.Icc 1 n → 0 < |x - alpha n i| := by
  intro i hi
  have hle : rho n x ≤ |x - alpha n i| := rho_le_root hn x hi
  exact lt_of_lt_of_le hrho hle

/-- Root distances to x are at most `Rserre` (x and roots in the interval). -/
lemma root_dist_le_R {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre)
    {i : ℕ} (hi : i ∈ Finset.Icc 1 n) : |x - alpha n i| ≤ Rserre := by
  have hi' : 1 ≤ i ∧ i ≤ n := Finset.mem_Icc.mp hi
  have halpha : alpha n i ∈ Set.Icc aSerre bSerre := alpha_mem_Icc hn hi'.1 hi'.2
  rw [abs_sub_le_iff]
  constructor <;> dsimp [Rserre] <;> linarith [hx.1, hx.2, halpha.1, halpha.2]

/-- For a root with `1 ≤ i ≤ n`, distance to x is ≤ r iff root in the ball. -/
lemma root_in_ball_iff_dist {n : ℕ} {x r : ℝ} (hr : 0 ≤ r) {i : ℕ}
    (hi : i ∈ Finset.Icc 1 n) :
    (alpha n i ∈ Set.Icc (x - r) (x + r)) ↔ |x - alpha n i| ≤ r := by
  rw [Set.mem_Icc]
  rw [abs_le]
  constructor
  · intro h
    constructor <;> linarith
  · intro h
    constructor <;> linarith

/-- `μ(Icc u v) = cdf v - cdf u` on the interval (atom-free). -/
lemma muS_Icc_eq_cdf_sub {u v : ℝ} (hu : aSerre ≤ u) (huv : u ≤ v) :
    (muS (Set.Icc u v)).toReal = cdf v - cdf u := by
  have hsetdiff : muS (Set.Ioc u v) = muS (Set.Icc u v) := by
    apply le_antisymm
    · exact measure_mono (Set.Ioc_subset_Icc_self)
    · have hIcc : Set.Icc u v = Set.Ioc u v ∪ {u} := by
        ext t
        constructor
        · intro ht
          by_cases htu : t = u
          · right; simp [htu]
          · left
            have htu' : u ≠ t := by
              intro h
              exact htu h.symm
            exact ⟨lt_of_le_of_ne ht.1 htu', ht.2⟩
        · intro ht
          rcases ht with htIoc | htE
          · rw [Set.mem_Icc]
            exact ⟨le_of_lt htIoc.1, htIoc.2⟩
          · rw [Set.mem_singleton_iff] at htE
            subst t
            exact ⟨le_rfl, huv⟩
      have hmeas2 : MeasurableSet ({u} : Set ℝ) := measurableSet_singleton u
      have hdisj : Disjoint (Set.Ioc u v) ({u} : Set ℝ) := by
        rw [Set.disjoint_left]
        intro t ht hsing
        have htu : t = u := by simpa using hsing
        exact (lt_irrefl u) (lt_of_lt_of_le ht.1 (le_of_eq htu))
      have hsingle : muS {u} = 0 := by simpa using (muS_atom_free u)
      rw [hIcc]
      have h1 : muS (Set.Ioc u v ∪ {u}) = muS (Set.Ioc u v) + muS {u} :=
        MeasureTheory.measure_union hdisj hmeas2
      rw [h1, hsingle]
      simp
  calc
    (muS (Set.Icc u v)).toReal = (muS (Set.Ioc u v)).toReal := by
      congr 1
      exact hsetdiff.symm
    _ = cdf v - cdf u := by rw [cdf_sub_eq_Ioc huv]

/-- Counting roots in a tail ball, as a real sum of indicators. -/
lemma tailCount_as_sum (n : ℕ) (x s : ℝ) :
    (tailCount n x s : ℝ) =
      ∑ i ∈ Finset.Icc 1 n, (if alpha n i ∈ Set.Icc (x - tailRad s) (x + tailRad s) then 1 else 0) := by
  unfold tailCount
  rw [Finset.card_filter]
  norm_num

/-- measure of the tail ball equals measure of the clamped ball. -/
lemma mu_ball_clamped (x r : ℝ) : (muS (Set.Icc (x - r) (x + r))).toReal =
    (muS (Set.Icc (max (x - r) aSerre) (min (x + r) bSerre))).toReal := by
  let A := Set.Icc (x - r) (x + r)
  let B := A ∩ Set.Icc aSerre bSerre
  have hmeasA : MeasurableSet A := isClosed_Icc.measurableSet
  have hmeasB : MeasurableSet B := hmeasA.inter isClosed_Icc.measurableSet
  have hBsub : B ⊆ A := by intro t ht; exact ht.1
  have hdiff : muS (A \ B) = 0 := by
    have hset : A \ B = A ∩ (Set.Icc aSerre bSerre)ᶜ := by
      ext t
      constructor
      · intro ht
        exact ⟨ht.1, fun htI => ht.2 ⟨ht.1, htI⟩⟩
      · intro ht
        exact ⟨ht.1, fun htI => ht.2 htI.2⟩
    rw [hset]
    exact measure_inter_null_of_null_right A
      (by simpa using (PotentialContinuity.muS_compl_Icc : muS (Set.Icc aSerre bSerre)ᶜ = 0))
  have hunion : A = B ∪ (A \ B) := by
    ext t
    constructor
    · intro ht
      by_cases htI : t ∈ Set.Icc aSerre bSerre
      · left; exact ⟨ht, htI⟩
      · right; exact ⟨ht, fun htB => htI htB.2⟩
    · intro ht
      rcases ht with htB | htd
      · exact hBsub htB
      · exact htd.1
  have hmain : muS A = muS B := by
    calc
      muS A = muS (B ∪ (A \ B)) := congrArg muS hunion
      _ = muS B + muS (A \ B) := by
        rw [MeasureTheory.measure_union]
        · rw [Set.disjoint_left]
          intro t htB htd
          exact htd.2 htB
        · exact hmeasA.diff hmeasB
      _ = muS B := by rw [hdiff]; simp
  have hset : A ∩ Set.Icc aSerre bSerre =
      Set.Icc (max (x - r) aSerre) (min (x + r) bSerre) := by
    ext t
    constructor
    · intro ht
      rw [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Icc] at ht
      constructor
      · exact max_le ht.1.1 ht.2.1
      · exact le_min ht.1.2 ht.2.2
    · intro ht
      rw [Set.mem_Icc] at ht
      rw [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Icc]
      constructor
      · constructor
        · exact le_trans (le_max_left (x - r) aSerre) ht.1
        · exact le_trans ht.2 (min_le_left (x + r) bSerre)
      · constructor
        · exact le_trans (le_max_right (x - r) aSerre) ht.1
        · exact le_trans ht.2 (min_le_right (x + r) bSerre)
  congr 1
  rw [← hset]
  change muS A = muS B
  exact hmain

/-- pointwise no-telescope for tail masses: `|n·tailMass − tailCount| ≤ Cnt` for `s ≥ 0`. -/
lemma noTel_tail_mass (Cnt : ℝ) (hCnt : 0 ≤ Cnt)
    (hnt : ∀ (m : ℕ), 2 ≤ m → ∀ u v : ℝ, aSerre ≤ u → u ≤ v → v ≤ bSerre →
      |(((Finset.Icc 1 m).filter fun i : ℕ => u ≤ alpha m i ∧ alpha m i ≤ v).card : ℝ) / (m : ℝ)
          - (cdf v - cdf u)| ≤ Cnt / (m : ℝ))
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre)
    (s : ℝ) (hs : 0 ≤ s) :
    |(n : ℝ) * tailMass x s - (tailCount n x s : ℝ)| ≤ Cnt := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  let r := tailRad s
  have hr : 0 ≤ r := by
    dsimp [r, tailRad]
    exact mul_nonneg (le_of_lt Rserre_pos) (Real.exp_pos (-s)).le
  let u := max (x - r) aSerre
  let v := min (x + r) bSerre
  have hua : aSerre ≤ u := by dsimp [u]; exact le_max_right _ _
  have hvb : v ≤ bSerre := by dsimp [v]; exact min_le_right _ _
  have huv : u ≤ v := by
    dsimp [u, v]
    apply le_min
    · apply max_le
      · linarith
      · linarith [hx.1]
    · apply max_le
      · linarith [hx.2]
      · linarith [a_lt_b]
  have hnt' := hnt n hn u v hua huv hvb
  have hcnt : tailCount n x s =
      ((Finset.Icc 1 n).filter (fun i : ℕ => u ≤ alpha n i ∧ alpha n i ≤ v)).card := by
    unfold tailCount
    congr 1
    apply Finset.ext
    intro i
    by_cases hi : i ∈ Finset.Icc 1 n
    · have hi' : 1 ≤ i ∧ i ≤ n := Finset.mem_Icc.mp hi
      have hα : alpha n i ∈ Set.Icc aSerre bSerre := alpha_mem_Icc (by omega) hi'.1 hi'.2
      have hiff : (alpha n i ∈ Set.Icc (x - tailRad s) (x + tailRad s))
          ↔ (u ≤ alpha n i ∧ alpha n i ≤ v) := by
        have hr' : tailRad s = r := rfl
        rw [hr']
        rw [Set.mem_Icc]
        constructor
        · intro hmem
          dsimp [u, v]
          constructor
          · exact max_le hmem.1 hα.1
          · exact le_min hmem.2 hα.2
        · intro hmem
          dsimp [u, v] at hmem
          constructor
          · exact le_trans (le_max_left (x - r) aSerre) hmem.1
          · exact le_trans hmem.2 (min_le_left (x + r) bSerre)
      rw [Finset.mem_filter]
      rw [Finset.mem_filter]
      constructor
      · intro h
        exact ⟨h.1, (hiff).mp h.2⟩
      · intro h
        exact ⟨h.1, (hiff).mpr h.2⟩
    · simp [hi]
  -- (cdf v - cdf u) = mass of [u,v] = mass of ball
  have hcdf : cdf v - cdf u = (muS (Set.Icc u v)).toReal := (muS_Icc_eq_cdf_sub hua huv).symm
  have hmass : tailMass x s = (muS (Set.Icc u v)).toReal := by
    dsimp [tailMass, Mball, u, v, r]
    rw [mu_ball_clamped]
  have hnt'' : |((cdf v - cdf u) - (tailCount n x s : ℝ) / (n : ℝ))| ≤ Cnt / (n : ℝ) := by
    have htmp := hnt'
    -- hnt' : |tailCount/n − (cdfv−cdfu)| ≤ Cnt/n
    have hcnt' : ((Finset.Icc 1 n).filter (fun i : ℕ => u ≤ alpha n i ∧ alpha n i ≤ v)).card = tailCount n x s := hcnt.symm
    simpa [abs_sub_comm, hcnt'] using htmp
  have hscaled : |(n : ℝ) * ((cdf v - cdf u) - (tailCount n x s : ℝ) / (n : ℝ))| ≤ Cnt := by
    have hmul := mul_le_mul_of_nonneg_right hnt'' (le_of_lt hnpos)
    have hiden : |(n : ℝ) * ((cdf v - cdf u) - (tailCount n x s : ℝ) / (n : ℝ))|
        = |((cdf v - cdf u) - (tailCount n x s : ℝ) / (n : ℝ))| * (n : ℝ) := by
      rw [abs_mul]
      rw [mul_comm]
      congr 1
      rw [abs_of_nonneg (le_of_lt hnpos)]
    rw [hiden]
    calc
      |((cdf v - cdf u) - (tailCount n x s : ℝ) / (n : ℝ))| * (n : ℝ)
          ≤ (Cnt / (n : ℝ)) * (n : ℝ) := hmul
      _ = Cnt := by field_simp [ne_of_gt hnpos]
  have heq : (n : ℝ) * tailMass x s - (tailCount n x s : ℝ)
      = (n : ℝ) * ((cdf v - cdf u) - (tailCount n x s : ℝ) / (n : ℝ)) := by
    rw [hmass, hcdf]
    field_simp [ne_of_gt hnpos]
  rw [heq]
  exact hscaled


/-- tail radius is strictly positive. -/
lemma tailRad_pos (s : ℝ) : 0 < tailRad s := by
  dsimp [tailRad]
  exact mul_pos Rserre_pos (Real.exp_pos (-s))

/-- ball mass is bounded by `Cmu·√(2r)`. -/
lemma Mball_le (x r : ℝ) (hr : 0 ≤ r) : Mball x r ≤ Cmu * Real.sqrt (2 * r) := by
  have hE : muS (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (Cmu * Real.sqrt (2 * r)) := by
    simpa [ball_eq_Icc] using muS_ball_mass x hr
  have htop : muS (Set.Icc (x - r) (x + r)) ≠ ∞ := (muS_lt_top (Set.Icc (x - r) (x + r))).ne
  have htop2 : ENNReal.ofReal (Cmu * Real.sqrt (2 * r)) ≠ ∞ := ENNReal.ofReal_ne_top
  have hnr : 0 ≤ Cmu * Real.sqrt (2 * r) := mul_nonneg (le_of_lt Cmu_pos) (Real.sqrt_nonneg _)
  have hle : (muS (Set.Icc (x - r) (x + r))).toReal ≤ Cmu * Real.sqrt (2 * r) := by
    have hlt : muS (Set.Icc (x - r) (x + r)) < ∞ := muS_lt_top (Set.Icc (x - r) (x + r))
    have hconv := (ENNReal.toReal_le_toReal hlt.ne htop2).2 hE
    rwa [ENNReal.toReal_ofReal hnr] at hconv
  simpa [Mball] using hle

/-- tail mass decays like `e^{-s/2}`. -/
lemma tailMass_le_decay (x s : ℝ) :
    tailMass x s ≤ Cmu * Real.sqrt (2 * Rserre) * Real.exp (-s / 2) := by
  have h := Mball_le x (tailRad s) (le_of_lt (tailRad_pos s))
  have hsq : Real.sqrt (2 * tailRad s) ≤ Real.sqrt (2 * Rserre) * Real.exp (-s / 2) := by
    have hfactor : 2 * tailRad s = (2 * Rserre) * Real.exp (-s) := by
      dsimp [tailRad]
      ring
    rw [hfactor]
    have hsqm : Real.sqrt ((2 * Rserre) * Real.exp (-s)) =
        Real.sqrt (2 * Rserre) * Real.sqrt (Real.exp (-s)) :=
      Real.sqrt_mul (x := 2 * Rserre) (mul_nonneg (by norm_num) (le_of_lt Rserre_pos)) (Real.exp (-s))
    rw [hsqm]
    have hpow : Real.exp (-s) = (Real.exp (-s / 2)) ^ 2 := by
      calc
        Real.exp (-s) = Real.exp (-s / 2 + -s / 2) := by congr 1; ring
        _ = Real.exp (-s / 2) * Real.exp (-s / 2) := Real.exp_add _ _
        _ = (Real.exp (-s / 2)) ^ 2 := by rw [sq]
    have hsq2 : Real.sqrt (Real.exp (-s)) = Real.exp (-s / 2) := by
      rw [hpow]
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_pos (Real.exp_pos _)]
    rw [hsq2]
  calc
    tailMass x s = Mball x (tailRad s) := by rfl
    _ ≤ Cmu * Real.sqrt (2 * tailRad s) := h
    _ ≤ Cmu * (Real.sqrt (2 * Rserre) * Real.exp (-s / 2)) := by
      exact mul_le_mul_of_nonneg_left hsq (le_of_lt Cmu_pos)
    _ = Cmu * Real.sqrt (2 * Rserre) * Real.exp (-s / 2) := by ring

/-- tail mass is antitone in s. -/
lemma tailMass_antitone (x : ℝ) : Antitone (fun s : ℝ => tailMass x s) := by
  intro s1 s2 hs12
  dsimp [tailMass]
  have hrs : tailRad s2 ≤ tailRad s1 := by
    dsimp [tailRad]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt Rserre_pos)
    exact (Real.exp_le_exp).2 (by linarith)
  exact Mball_mono (le_of_lt (tailRad_pos s2)) hrs

/-- tail mass is measurable. -/
lemma tailMass_measurable (x : ℝ) : Measurable (fun s : ℝ => tailMass x s) :=
  (tailMass_antitone x).measurable

/-- tail count is antitone in s. -/
lemma tailCount_antitone (n : ℕ) (x : ℝ) : Antitone (fun s : ℝ => (tailCount n x s : ℝ)) := by
  intro s1 s2 hs12
  have hrs : tailRad s2 ≤ tailRad s1 := by
    dsimp [tailRad]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt Rserre_pos)
    exact (Real.exp_le_exp).2 (by linarith)
  have hcard : tailCount n x s2 ≤ tailCount n x s1 := by
    unfold tailCount
    exact Finset.card_le_card (by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨hi1, hi2⟩
      apply Finset.mem_filter.mpr
      constructor
      · exact hi1
      · have h1 : |x - alpha n i| ≤ tailRad s2 :=
          (root_in_ball_iff_dist (le_of_lt (tailRad_pos s2)) hi1).mp hi2
        have h2 : |x - alpha n i| ≤ tailRad s1 := le_trans h1 hrs
        exact (root_in_ball_iff_dist (le_of_lt (tailRad_pos s1)) hi1).mpr h2)
  change (tailCount n x s2 : ℝ) ≤ (tailCount n x s1 : ℝ)
  exact_mod_cast hcard

/-- tail mass is integrable on the half-line. -/
lemma tailMass_integrableOn (x : ℝ) :
    MeasureTheory.IntegrableOn (fun s : ℝ => tailMass x s) (Set.Ioi 0) volume := by
  let g : ℝ → ℝ := fun s : ℝ => Cmu * Real.sqrt (2 * Rserre) * Real.exp (-s / 2)
  have hg : MeasureTheory.IntegrableOn g (Set.Ioi 0) volume := by
    let C : ℝ := Cmu * Real.sqrt (2 * Rserre)
    have hbase : MeasureTheory.IntegrableOn (fun s : ℝ => Real.exp (-s / 2)) (Set.Ioi 0) volume := by
      have hident : (fun s : ℝ => Real.exp (-s / 2)) = fun s : ℝ => Real.exp (-(1 / 2 : ℝ) * s) := by
        funext s
        congr 1
        ring
      rw [hident]
      exact integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) 0
    have hmul : MeasureTheory.IntegrableOn (fun s : ℝ => C * Real.exp (-s / 2)) (Set.Ioi 0) volume := by
      change MeasureTheory.Integrable (fun s : ℝ => C * Real.exp (-s / 2)) (volume.restrict (Set.Ioi 0))
      exact hbase.const_mul C
    simpa [g, C] using hmul
  refine MeasureTheory.Integrable.mono' hg ?_ ?_
  · exact (tailMass_measurable x).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun s => ?_)
    have h := tailMass_le_decay x s
    have hnn : 0 ≤ g s := by
      dsimp [g]
      exact mul_nonneg (mul_nonneg (le_of_lt Cmu_pos) (Real.sqrt_nonneg _)) (Real.exp_pos _).le
    have hnn' : 0 ≤ tailMass x s := Mball_nonneg x (tailRad s)
    simpa [Real.norm_eq_abs, g, abs_of_nonneg hnn', abs_of_nonneg hnn] using h


/-- `logRatio n x i := log(Rserre / |x − α_i|)` (≥ 0 for roots in range, non-root x). -/
def logRatio (n : ℕ) (x : ℝ) (i : ℕ) : ℝ := Real.log (Rserre / |x - alpha n i|)

/-- `log s_i = logRserre − logRatio n x i` for a root in range. -/
lemma log_dist_eq_logR_sub_ratio {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ Set.Icc aSerre bSerre) (hrho : 0 < rho n x) {i : ℕ} (hi : i ∈ Finset.Icc 1 n) :
    Real.log (|x - alpha n i|) = Real.log Rserre - logRatio n x i := by
  have hsi : 0 < |x - alpha n i| := root_dist_pos hn hrho i hi
  dsimp [logRatio]
  rw [Real.log_div (ne_of_gt Rserre_pos) (ne_of_gt hsi)]
  ring

/-- `Σ_i log|x−α_i| = n·logRserre − Σ_i logRatio n x i` (roots in range). -/
lemma sum_logs_eq_sum_ratio (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre)
    (hrho : 0 < rho n x) :
    (∑ i ∈ Finset.Icc 1 n, Real.log (|x - alpha n i|))
      = (n : ℝ) * Real.log Rserre - ∑ i ∈ Finset.Icc 1 n, logRatio n x i := by
  have hcard : (Finset.Icc 1 n).card = n := by
    simpa using (Finset.card_Icc (a := 1) (b := n))
  calc
    (∑ i ∈ Finset.Icc 1 n, Real.log (|x - alpha n i|))
        = ∑ i ∈ Finset.Icc 1 n, (Real.log Rserre - logRatio n x i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact log_dist_eq_logR_sub_ratio hn hx hrho hi
    _ = (∑ i ∈ Finset.Icc 1 n, Real.log Rserre) - ∑ i ∈ Finset.Icc 1 n, logRatio n x i := by
          rw [Finset.sum_sub_distrib]
    _ = (n : ℝ) * Real.log Rserre - ∑ i ∈ Finset.Icc 1 n, logRatio n x i := by
          congr 1
          rw [Finset.sum_const]
          rw [hcard]
          simp

/-- each `logRatio n x i` is nonnegative (root in range, x non-root). -/
lemma logRatio_nonneg {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre)
    (hrho : 0 < rho n x) {i : ℕ} (hi : i ∈ Finset.Icc 1 n) : 0 ≤ logRatio n x i := by
  have hsi : 0 < |x - alpha n i| := root_dist_pos hn hrho i hi
  have hsR : |x - alpha n i| ≤ Rserre := root_dist_le_R hn hx hi
  dsimp [logRatio]
  exact Real.log_nonneg (by
    rw [one_le_div hsi]
    exact hsR)

/-- root is in the tail ball iff `s ≤ logRatio n x i`. -/
lemma root_in_tail_iff_logRatio {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre)
    (hrho : 0 < rho n x) {i : ℕ} (hi : i ∈ Finset.Icc 1 n) (s : ℝ) :
    (alpha n i ∈ Set.Icc (x - tailRad s) (x + tailRad s)) ↔ s ≤ logRatio n x i := by
  have hsi : 0 < |x - alpha n i| := root_dist_pos hn hrho i hi
  have hdiv : 0 < Rserre / |x - alpha n i| := div_pos Rserre_pos hsi
  have hmem : (alpha n i ∈ Set.Icc (x - tailRad s) (x + tailRad s)) ↔ |x - alpha n i| ≤ tailRad s :=
    root_in_ball_iff_dist (le_of_lt (tailRad_pos s)) hi
  rw [hmem]
  dsimp [logRatio, tailRad]
  constructor
  · intro hle
    have hms := mul_le_mul_of_nonneg_right hle (Real.exp_pos s).le
    have he : Real.exp (-s) * Real.exp s = 1 := by
      rw [← Real.exp_add]
      norm_num
    have hcancel : (Rserre * Real.exp (-s)) * Real.exp s = Rserre := by
      rw [mul_assoc, he, mul_one]
    have hle' : |x - alpha n i| * Real.exp s ≤ Rserre := by
      rwa [← hcancel]
    have hExpLe : Real.exp s ≤ Rserre / |x - alpha n i| := by
      rw [le_div_iff₀ hsi]
      -- e^s ≤ R/a ⟺ e^s·a ≤ R
      rwa [mul_comm]
    exact (Real.le_log_iff_exp_le hdiv).2 hExpLe
  · intro hs
    have hExpLe : Real.exp s ≤ Rserre / |x - alpha n i| := (Real.le_log_iff_exp_le hdiv).1 hs
    have hmul1 : |x - alpha n i| * Real.exp s ≤ Rserre := by
      rw [le_div_iff₀ hsi] at hExpLe
      rwa [mul_comm] at hExpLe
    have hle' : |x - alpha n i| ≤ Rserre * Real.exp (-s) := by
      -- from a·e^s ≤ R: multiply by e^{-s}
      have hms := mul_le_mul_of_nonneg_right hmul1 (Real.exp_pos (-s)).le
      have hcancel : (|x - alpha n i| * Real.exp s) * Real.exp (-s) = |x - alpha n i| := by
        rw [mul_assoc]
        have he : Real.exp s * Real.exp (-s) = 1 := by
          rw [← Real.exp_add]
          norm_num
        rw [he, mul_one]
      have hR : Rserre * Real.exp (-s) = (Rserre * Real.exp (-s)) * 1 := by ring
      rw [hcancel] at hms
      simpa [mul_assoc, mul_comm, mul_left_comm] using hms
    exact hle'


/-- For `0 ≤ L`, `∫_{s ∈ (0,∞)} 1_{s ≤ L} ds = L`. -/
lemma integral_Ioi_if_le (L : ℝ) (hL : 0 ≤ L) :
    (∫ s : ℝ in Set.Ioi 0, (if s ≤ L then (1 : ℝ) else 0)) = L := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  have hfun : (fun s : ℝ => (if s ≤ L then (1 : ℝ) else 0)) =
      (Set.Iic L).indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext s
    by_cases hs : s ≤ L <;> simp [hs]
  calc
    (∫ s : ℝ in Set.Ioi 0, (if s ≤ L then (1 : ℝ) else 0))
        = ∫ s : ℝ, (if s ≤ L then (1 : ℝ) else 0) ∂(volume.restrict (Set.Ioi 0)) := rfl
    _ = ∫ s : ℝ, (Set.Iic L).indicator (fun _ : ℝ => (1 : ℝ)) s ∂μ := by
          rw [hfun]
    _ = L := by
          rw [MeasureTheory.integral_indicator_const (μ := μ) (e := (1 : ℝ)) (s := Set.Iic L) measurableSet_Iic]
          simp [μ, MeasureTheory.Measure.real_def]
          have hset : Set.Iic L ∩ Set.Ioi 0 = Set.Ioc 0 L := by
            ext s
            simp [Set.Iic, Set.Ioi, Set.Ioc, and_comm]
          rw [hset]
          rw [Real.volume_Ioc]
          simp [ENNReal.toReal_ofReal hL]

/-- Each summand `s ↦ 1_{s ≤ L}` is integrable on the half-line. -/
lemma integrable_Ioi_if_le (L : ℝ) :
    MeasureTheory.Integrable (fun s : ℝ => (if s ≤ L then (1 : ℝ) else 0))
      (volume.restrict (Set.Ioi 0)) := by
  have hfun : (fun s : ℝ => (if s ≤ L then (1 : ℝ) else 0)) =
      (Set.Iic L).indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext s
    by_cases hs : s ≤ L <;> simp [hs]
  rw [hfun]
  refine MeasureTheory.IntegrableOn.integrable_indicator ?_ measurableSet_Iic
  have hfin : ((volume.restrict (Set.Ioi 0)) (Set.Iic L)) ≠ ∞ := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Iic]
    have hset : Set.Iic L ∩ Set.Ioi 0 = Set.Ioc 0 L := by
      ext s
      simp [Set.Iic, Set.Ioi, Set.Ioc, and_comm]
    rw [hset]
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  simpa using (integrableOn_const (μ := volume.restrict (Set.Ioi 0)) (s := Set.Iic L) (C := (1:ℝ)) (hs := hfin))

/-- `∫_s tailCount n x s = Σ_i log(Rserre/|x−α_i|)` (for 1 ≤ n, x ∈ interval, non-root). -/
lemma atomicTailIntegral (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre)
    (hrho : 0 < rho n x) :
    (∫ s : ℝ in Set.Ioi 0, (tailCount n x s : ℝ)) =
      ∑ i ∈ Finset.Icc 1 n, Real.log (Rserre / |x - alpha n i|) := by
  have hfun : (fun s : ℝ => (tailCount n x s : ℝ)) =
      (fun s : ℝ => ∑ i ∈ Finset.Icc 1 n, (if s ≤ logRatio n x i then (1 : ℝ) else 0)) := by
    funext s
    rw [tailCount_as_sum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hmem : alpha n i ∈ Set.Icc (x - tailRad s) (x + tailRad s)
    · have hs : s ≤ logRatio n x i := (root_in_tail_iff_logRatio hn hx hrho hi s).mp hmem
      simp [hmem, hs]
    · have hns : ¬ s ≤ logRatio n x i := by
        intro hst
        exact hmem ((root_in_tail_iff_logRatio hn hx hrho hi s).mpr hst)
      simp [hmem, hns]
  have hintegrable : ∀ i ∈ Finset.Icc 1 n,
      MeasureTheory.Integrable (fun s : ℝ => (if s ≤ logRatio n x i then (1 : ℝ) else 0))
        (volume.restrict (Set.Ioi 0)) := by
    intro i hi
    exact integrable_Ioi_if_le (logRatio n x i)
  calc
    (∫ s : ℝ in Set.Ioi 0, (tailCount n x s : ℝ))
        = ∫ s : ℝ in Set.Ioi 0, (∑ i ∈ Finset.Icc 1 n, (if s ≤ logRatio n x i then (1 : ℝ) else 0)) := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall (fun s => congrFun hfun s)
    _ = ∑ i ∈ Finset.Icc 1 n, (∫ s : ℝ in Set.Ioi 0, (if s ≤ logRatio n x i then (1 : ℝ) else 0)) := by
          rw [MeasureTheory.integral_finsetSum]
          exact hintegrable
    _ = ∑ i ∈ Finset.Icc 1 n, logRatio n x i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact integral_Ioi_if_le (logRatio n x i) (logRatio_nonneg hn hx hrho hi)
    _ = ∑ i ∈ Finset.Icc 1 n, Real.log (Rserre / |x - alpha n i|) := by
          simp [logRatio]




open Submission.ThreePages
open Submission.SerreExample
open Submission.PotentialContinuity
open Submission.Quantile

/-- The Serre interval length is at least 1. -/
lemma Rserre_ge_one : (1 : ℝ) ≤ Rserre := by
  norm_num [Rserre, aSerre, bSerre]

/-- `log Rserre ≥ 0`. -/
lemma log_Rserre_nonneg : 0 ≤ Real.log Rserre :=
  Real.log_nonneg Rserre_ge_one

/-- If `log(Rserre/c) < s` then the tail radius at `s` is below `c`. -/
lemma tailRad_lt_of_log_lt {s c : ℝ} (hc0 : 0 < c) (hs : Real.log (Rserre / c) < s) :
    tailRad s < c := by
  dsimp [tailRad]
  have hq : 0 < Rserre / c := div_pos Rserre_pos hc0
  have hlt : Rserre / c < Real.exp s := (Real.log_lt_iff_lt_exp hq).mp hs
  have hmul1 : Rserre < Real.exp s * c := (div_lt_iff₀ hc0).mp hlt
  have he : Real.exp s * Real.exp (-s) = 1 := by
    rw [← Real.exp_add]
    have hs0 : s + (-s) = 0 := by ring
    rw [hs0, Real.exp_zero]
  calc
    Rserre * Real.exp (-s) < (Real.exp s * c) * Real.exp (-s) :=
      mul_lt_mul_of_pos_right hmul1 (Real.exp_pos (-s))
    _ = c * (Real.exp s * Real.exp (-s)) := by ring_nf
    _ = c := by rw [he, mul_one]

/-- If `s < log(Rserre/c)` then the tail radius at `s` exceeds `c`. -/
lemma tailRad_gt_of_lt_log {s c : ℝ} (hc0 : 0 < c) (hs : s < Real.log (Rserre / c)) :
    c < tailRad s := by
  dsimp [tailRad]
  have hq : 0 < Rserre / c := div_pos Rserre_pos hc0
  have hlt : Real.exp s < Rserre / c := (Real.lt_log_iff_exp_lt hq).mp hs
  have hmul1 : Real.exp s * c < Rserre := (lt_div_iff₀ hc0).mp hlt
  have he : Real.exp s * Real.exp (-s) = 1 := by
    rw [← Real.exp_add]
    have hs0 : s + (-s) = 0 := by ring
    rw [hs0, Real.exp_zero]
  calc
    c = c * (Real.exp s * Real.exp (-s)) := by rw [he, mul_one]
    _ = (Real.exp s * c) * Real.exp (-s) := by ring_nf
    _ < Rserre * Real.exp (-s) :=
      mul_lt_mul_of_pos_right hmul1 (Real.exp_pos (-s))

/-- tail count is 0 when the radius is below the nearest-root distance. -/
lemma tailCount_zero_radius_lt_rho (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre)
    (hrho : 0 < rho n x) (s : ℝ) (hs : Real.log (Rserre / rho n x) < s) :
    tailCount n x s = 0 := by
  have hρ : tailRad s < rho n x := tailRad_lt_of_log_lt hrho hs
  unfold tailCount
  have hf : (Finset.Icc 1 n).filter (fun i : ℕ => alpha n i ∈ Set.Icc (x - tailRad s) (x + tailRad s)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hi1, hi2⟩
    have hball : |x - alpha n i| ≤ tailRad s :=
      (root_in_ball_iff_dist (le_of_lt (tailRad_pos s)) hi1).mp hi2
    have hle : rho n x ≤ |x - alpha n i| := rho_le_root hn x hi1
    nlinarith
  rw [hf]
  simp

/-- tail count is 1 on the annulus between radius ρ and radius δ (when ρ ≤ δ). -/
lemma tailCount_one_on_annulus (n : ℕ) (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre)
    (hrho : 0 < rho n x) (δ : ℝ) (hδ0 : 0 < δ) (hrδ : rho n x ≤ δ)
    (hatmost : ((Finset.Icc 1 n).filter (fun i : ℕ => x - δ ≤ alpha n i ∧ alpha n i ≤ x + δ)).card ≤ 1)
    (s : ℝ) (hsδ : Real.log (Rserre / δ) < s) (hsρ : s < Real.log (Rserre / rho n x)) :
    tailCount n x s = 1 := by
  have hn1 : 1 ≤ n := by omega
  have htailδ : tailRad s < δ := tailRad_lt_of_log_lt hδ0 hsδ
  have hρtail : rho n x < tailRad s := tailRad_gt_of_lt_log hrho hsρ
  have hle1 : tailCount n x s ≤ 1 := by
    unfold tailCount
    have hsub :
        (Finset.Icc 1 n).filter (fun i : ℕ => alpha n i ∈ Set.Icc (x - tailRad s) (x + tailRad s))
          ⊆ (Finset.Icc 1 n).filter (fun i : ℕ => x - δ ≤ alpha n i ∧ alpha n i ≤ x + δ) := by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨hi1, hi2⟩
      have hball : |x - alpha n i| ≤ tailRad s :=
        (root_in_ball_iff_dist (le_of_lt (tailRad_pos s)) hi1).mp hi2
      have hleδ : |x - alpha n i| ≤ δ := le_trans hball (le_of_lt htailδ)
      apply Finset.mem_filter.mpr
      constructor
      · exact hi1
      · exact (root_in_ball_iff_dist (le_of_lt hδ0) hi1).mpr hleδ
    have hcard := Finset.card_le_card hsub
    exact le_trans hcard hatmost
  have hge1 : 1 ≤ tailCount n x s := by
    rcases exists_index_rho n hn1 x with ⟨i0, hi0, hrho_eq⟩
    unfold tailCount
    have hi0mem : i0 ∈ (Finset.Icc 1 n).filter
        (fun i : ℕ => alpha n i ∈ Set.Icc (x - tailRad s) (x + tailRad s)) := by
      apply Finset.mem_filter.mpr
      constructor
      · exact hi0
      · have hdist : |x - alpha n i0| < tailRad s := by
          rwa [← hrho_eq]
        exact (root_in_ball_iff_dist (le_of_lt (tailRad_pos s)) hi0).mpr (le_of_lt hdist)
    have hpos : 0 < ((Finset.Icc 1 n).filter
        (fun i : ℕ => alpha n i ∈ Set.Icc (x - tailRad s) (x + tailRad s))).card :=
      Finset.card_pos.mpr ⟨i0, hi0mem⟩
    omega
  exact le_antisymm hle1 hge1


/-- At the radius level `s = log(Rserre/ρ)` (radius exactly ρ), the tail count is 1
(when ρ ≤ δ and the δ-ball holds at most one root). -/
lemma tailCount_one_at_radius (n : ℕ) (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre)
    (hrho : 0 < rho n x) (δ : ℝ) (hδ0 : 0 < δ) (hrδ : rho n x ≤ δ)
    (hatmost : ((Finset.Icc 1 n).filter (fun i : ℕ => x - δ ≤ alpha n i ∧ alpha n i ≤ x + δ)).card ≤ 1) :
    tailCount n x (Real.log (Rserre / rho n x)) = 1 := by
  classical
  have hn1 : 1 ≤ n := by omega
  let r0 : ℝ := tailRad (Real.log (Rserre / rho n x))
  have hρr0 : r0 = rho n x := by
    dsimp [r0, tailRad]
    have hq : 0 < Rserre / rho n x := div_pos Rserre_pos hrho
    calc
      Rserre * Real.exp (-Real.log (Rserre / rho n x))
          = Rserre * (Real.exp (Real.log (Rserre / rho n x)))⁻¹ := by rw [Real.exp_neg]
      _ = Rserre * (Rserre / rho n x)⁻¹ := by rw [Real.exp_log hq]
      _ = rho n x := by
        field_simp [ne_of_gt Rserre_pos, ne_of_gt hrho]
  have hle1 : tailCount n x (Real.log (Rserre / rho n x)) ≤ 1 := by
    unfold tailCount
    have hsub :
        (Finset.Icc 1 n).filter (fun i : ℕ => alpha n i ∈ Set.Icc (x - r0) (x + r0))
          ⊆ (Finset.Icc 1 n).filter (fun i : ℕ => x - δ ≤ alpha n i ∧ alpha n i ≤ x + δ) := by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨hi1, hi2⟩
      have hball0 : |x - alpha n i| ≤ r0 :=
        (root_in_ball_iff_dist (le_of_lt (tailRad_pos (Real.log (Rserre / rho n x)))) hi1).mp hi2
      have hball : |x - alpha n i| ≤ rho n x := by rwa [hρr0] at hball0
      have hleδ : |x - alpha n i| ≤ δ := le_trans hball hrδ
      apply Finset.mem_filter.mpr
      constructor
      · exact hi1
      · exact (root_in_ball_iff_dist (le_of_lt hδ0) hi1).mpr hleδ
    have hcard := Finset.card_le_card hsub
    -- tailCount filter (with tailRad) is the same finset as with r0 (r0 is the let)
    simpa [tailCount, r0] using (le_trans hcard hatmost)
  have hge1 : 1 ≤ tailCount n x (Real.log (Rserre / rho n x)) := by
    unfold tailCount
    rcases exists_index_rho n hn1 x with ⟨i0, hi0, hrho_eq⟩
    have hi0mem : i0 ∈ (Finset.Icc 1 n).filter
        (fun i : ℕ => alpha n i ∈ Set.Icc (x - r0) (x + r0)) := by
      apply Finset.mem_filter.mpr
      constructor
      · exact hi0
      · have hdist : |x - alpha n i0| ≤ rho n x := by rw [hrho_eq]
        have hdist0 : |x - alpha n i0| ≤ r0 := by rwa [hρr0]
        exact (root_in_ball_iff_dist (le_of_lt (tailRad_pos (Real.log (Rserre / rho n x)))) hi0).mpr hdist0
    have hpos : 0 < ((Finset.Icc 1 n).filter
        (fun i : ℕ => alpha n i ∈ Set.Icc (x - r0) (x + r0))).card :=
      Finset.card_pos.mpr ⟨i0, hi0mem⟩
    simpa [tailCount, r0] using hpos
  exact le_antisymm hle1 hge1


/-- In the case `ρ ≤ δ` (one root at most in the δ-ball), the tail-count integral
over `(sδ, ∞)` is exactly `log(Rserre/ρ) − sδ`. -/
lemma integral_tailCount_Ioi_eq (n : ℕ) (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre)
    (hrho : 0 < rho n x) (δ : ℝ) (hδ0 : 0 < δ) (hrδ : rho n x ≤ δ)
    (hatmost : ((Finset.Icc 1 n).filter (fun i : ℕ => x - δ ≤ alpha n i ∧ alpha n i ≤ x + δ)).card ≤ 1)
    (sδ : ℝ) (hsδ : sδ = Real.log (Rserre / δ)) :
    (∫ s : ℝ in Set.Ioi sδ, (tailCount n x s : ℝ)) = Real.log (Rserre / rho n x) - sδ := by
  classical
  have hn1 : 1 ≤ n := by omega
  let L : ℝ := Real.log (Rserre / rho n x)
  have hsδleL : sδ ≤ L := by
    dsimp [L]
    rw [hsδ]
    apply Real.log_le_log
    · exact div_pos Rserre_pos hδ0
    · exact div_le_div_of_nonneg_left (le_of_lt Rserre_pos) hrho hrδ
  have hpt : (fun s : ℝ => (Set.Ioi sδ).indicator (fun t : ℝ => (tailCount n x t : ℝ)) s) =
      fun s : ℝ => (Set.Ioc sδ L).indicator (fun _ : ℝ => (1 : ℝ)) s := by
    funext s
    by_cases hsIoi : s ∈ Set.Ioi sδ
    · have hssδ : sδ < s := hsIoi
      by_cases hsL : s ≤ L
      · have hmemIoc : s ∈ Set.Ioc sδ L := ⟨hssδ, hsL⟩
        have hFs : (tailCount n x s : ℝ) = 1 := by
          have hslt_or : s < L ∨ s = L := lt_or_eq_of_le hsL
          rcases hslt_or with hslt | hseq
          · have h1 : Real.log (Rserre / δ) < s := by
              rwa [hsδ] at hssδ
            have h2 : s < Real.log (Rserre / rho n x) := by
              dsimp [L] at hslt
              exact hslt
            exact_mod_cast tailCount_one_on_annulus n hn hx hrho δ hδ0 hrδ hatmost s h1 h2
          · subst s
            have hL1 : tailCount n x L = 1 :=
              tailCount_one_at_radius n hn hx hrho δ hδ0 hrδ hatmost
            exact_mod_cast hL1
        calc
          (Set.Ioi sδ).indicator (fun t : ℝ => (tailCount n x t : ℝ)) s = (tailCount n x s : ℝ) := by
            rw [Set.indicator_of_mem hsIoi]
          _ = (1 : ℝ) := hFs
          _ = (Set.Ioc sδ L).indicator (fun _ : ℝ => (1 : ℝ)) s := by
            rw [Set.indicator_of_mem hmemIoc]
      · have hsLlt : L < s := lt_of_not_ge hsL
        have hnotIoc : s ∉ Set.Ioc sδ L := by
          intro hm
          exact hsL hm.2
        have hFs0 : (tailCount n x s : ℝ) = 0 := by
          have hloglt : Real.log (Rserre / rho n x) < s := by
            dsimp [L] at hsLlt
            exact hsLlt
          have hz : tailCount n x s = 0 :=
            tailCount_zero_radius_lt_rho n hn1 hx hrho s hloglt
          exact_mod_cast hz
        calc
          (Set.Ioi sδ).indicator (fun t : ℝ => (tailCount n x t : ℝ)) s = (tailCount n x s : ℝ) := by
            rw [Set.indicator_of_mem hsIoi]
          _ = 0 := hFs0
          _ = (Set.Ioc sδ L).indicator (fun _ : ℝ => (1 : ℝ)) s := by
            rw [Set.indicator_apply, if_neg hnotIoc]
    · have hnotIoc : s ∉ Set.Ioc sδ L := by
        intro hm
        exact hsIoi hm.1
      calc
        (Set.Ioi sδ).indicator (fun t : ℝ => (tailCount n x t : ℝ)) s = 0 := by
          rw [Set.indicator_apply, if_neg hsIoi]
        _ = (Set.Ioc sδ L).indicator (fun _ : ℝ => (1 : ℝ)) s := by
          rw [Set.indicator_apply, if_neg hnotIoc]
  calc
    (∫ s : ℝ in Set.Ioi sδ, (tailCount n x s : ℝ))
        = ∫ s : ℝ, (Set.Ioi sδ).indicator (fun t : ℝ => (tailCount n x t : ℝ)) s := by
          rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    _ = ∫ s : ℝ, (Set.Ioc sδ L).indicator (fun _ : ℝ => (1 : ℝ)) s := by rw [hpt]
    _ = ∫ s : ℝ in Set.Ioc sδ L, (1 : ℝ) := by
          rw [MeasureTheory.integral_indicator measurableSet_Ioc]
    _ = ∫ s : ℝ in sδ..L, (1 : ℝ) := by
          rw [← intervalIntegral.integral_of_le hsδleL]
    _ = (L - sδ) • (1 : ℝ) := intervalIntegral.integral_const (1 : ℝ)
    _ = L - sδ := by simp

/-- the atomic piece bound. -/
lemma atomic_piece_bound (n : ℕ) (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre)
    (hrho : 0 < rho n x) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hatmost : ((Finset.Icc 1 n).filter (fun i : ℕ => x - δ ≤ alpha n i ∧ alpha n i ≤ x + δ)).card ≤ 1)
    (sδ : ℝ) (hsδ : sδ = Real.log (Rserre / δ)) :
    |(-Real.log (rho n x) - (∫ s : ℝ in Set.Ioi sδ, (tailCount n x s : ℝ)))| ≤
      Real.log Rserre + Real.log (1 / δ) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hlogR : 0 ≤ Real.log Rserre := log_Rserre_nonneg
  have hloginvδ_nonneg : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg
    exact (one_le_div hδ0).mpr hδ1.le
  have hloginv : Real.log (1 / δ) = -Real.log δ := by
    rw [one_div, Real.log_inv]
  by_cases hrδ : rho n x ≤ δ
  · have hinteg : (∫ s : ℝ in Set.Ioi sδ, (tailCount n x s : ℝ))
        = Real.log (Rserre / rho n x) - sδ :=
      integral_tailCount_Ioi_eq n hn hx hrho δ hδ0 hrδ hatmost sδ hsδ
    have hmain : -Real.log (rho n x) - (∫ s : ℝ in Set.Ioi sδ, (tailCount n x s : ℝ))
        = -Real.log δ := by
      rw [hinteg]
      have h1 : Real.log (Rserre / rho n x) = Real.log Rserre - Real.log (rho n x) :=
        Real.log_div (ne_of_gt Rserre_pos) (ne_of_gt hrho)
      have h2 : sδ = Real.log Rserre - Real.log δ := by
        rw [hsδ]
        exact Real.log_div (ne_of_gt Rserre_pos) (ne_of_gt hδ0)
      rw [h1, h2]
      ring
    rw [hmain]
    have hlogδneg : Real.log δ < 0 := (Real.log_neg_iff hδ0).2 hδ1
    rw [hloginv]
    rw [abs_of_pos (neg_pos.mpr hlogδneg)]
    linarith
  · have hδρ : δ < rho n x := lt_of_not_ge hrδ
    have hinteq0 : (∫ s : ℝ in Set.Ioi sδ, (tailCount n x s : ℝ)) = 0 := by
      apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
      intro s hs
      have hsδs : sδ < s := hs
      have hloglt : Real.log (Rserre / rho n x) < Real.log (Rserre / δ) := by
        have hq1 : 0 < Rserre / rho n x := div_pos Rserre_pos hrho
        apply Real.log_lt_log hq1
        exact div_lt_div_of_pos_left Rserre_pos hδ0 hδρ
      have hslog : Real.log (Rserre / δ) < s := by
        rwa [hsδ] at hsδs
      have hz : tailCount n x s = 0 :=
        tailCount_zero_radius_lt_rho n hn1 hx hrho s (lt_trans hloglt hslog)
      exact_mod_cast hz
    rw [hinteq0, sub_zero, abs_neg, abs_le]
    constructor
    · have hlogδle : Real.log δ ≤ Real.log (rho n x) := Real.log_le_log hδ0 (le_of_lt hδρ)
      have hneg_le : -Real.log (1 / δ) ≤ Real.log (rho n x) := by
        rw [hloginv]
        linarith
      linarith
    · have hlogrho_le : Real.log (rho n x) ≤ Real.log Rserre := by
        apply Real.log_le_log hrho
        simpa [Rserre] using (rho_le_diam hn1 hx)
      linarith



/-- `log(n+2) ≥ log 4` for `n ≥ 2`. -/
lemma log_np2_ge_log4 {n : ℕ} (hn : 2 ≤ n) : Real.log 4 ≤ Real.log ((n : ℝ) + 2) := by
  exact Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : (4 : ℕ) ≤ n + 2))

/-- `log(1/δ) ≤ 2·log(n+2) + log(4·Csp²)` when `δ = (Csp·n)^{-2}/4`, `Csp ≥ 1`, `n ≥ 2`. -/
lemma log_one_over_delta_le (Csp δ : ℝ) (n : ℕ) (hCsp : 1 ≤ Csp) (hn : 2 ≤ n)
    (hδ : δ = ((Csp * (n : ℝ))⁻¹ ^ 2) / 4) :
    Real.log (1 / δ) ≤ 2 * Real.log ((n : ℝ) + 2) + Real.log (4 * Csp ^ 2) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hCsp0 : 0 < Csp := by linarith
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hrec : 1 / δ = 4 * (Csp * (n : ℝ)) ^ 2 := by
    rw [hδ]
    field_simp [hCsp0.ne', hn0.ne']
  rw [hrec]
  have hnp20 : 0 < (n : ℝ) + 2 := by linarith
  have hnn : (n : ℝ) ≤ (n : ℝ) + 2 := by linarith
  have hprod : 4 * (Csp * (n : ℝ)) ^ 2 ≤ 4 * (Csp * ((n : ℝ) + 2)) ^ 2 := by
    have hpow : (Csp * (n : ℝ)) ^ 2 ≤ (Csp * ((n : ℝ) + 2)) ^ 2 := by
      apply pow_le_pow_left₀ (mul_nonneg (le_of_lt hCsp0) (le_of_lt hn0))
      exact mul_le_mul_of_nonneg_left hnn (le_of_lt hCsp0)
    nlinarith
  have hlogmono : Real.log (4 * (Csp * (n : ℝ)) ^ 2) ≤ Real.log (4 * (Csp * ((n : ℝ) + 2)) ^ 2) := by
    exact Real.log_le_log (by positivity) hprod
  have hfac : 4 * (Csp * ((n : ℝ) + 2)) ^ 2 = (4 * Csp ^ 2) * ((n : ℝ) + 2) ^ 2 := by ring
  rw [hfac] at hlogmono
  have hlogs : Real.log ((4 * Csp ^ 2) * ((n : ℝ) + 2) ^ 2)
      = Real.log (4 * Csp ^ 2) + 2 * Real.log ((n : ℝ) + 2) := by
    have h1 : Real.log ((4 * Csp ^ 2) * ((n : ℝ) + 2) ^ 2)
        = Real.log (4 * Csp ^ 2) + Real.log (((n : ℝ) + 2) ^ 2) := by
      rw [Real.log_mul (by positivity) (by positivity)]
    rw [h1]
    congr 1
    rw [Real.log_pow ((n : ℝ) + 2) 2]
    norm_num
  rw [hlogs] at hlogmono
  simpa [add_comm, add_left_comm, add_assoc] using hlogmono

/-- `log(Rserre/δ) ≤ 2·log(n+2) + log(4·Csp²·Rserre)` with same hypotheses. -/
lemma log_R_over_delta_le (Csp δ : ℝ) (n : ℕ) (hCsp : 1 ≤ Csp) (hn : 2 ≤ n)
    (hδ : δ = ((Csp * (n : ℝ))⁻¹ ^ 2) / 4) :
    Real.log (Rserre / δ) ≤ 2 * Real.log ((n : ℝ) + 2) + Real.log (4 * Csp ^ 2 * Rserre) := by
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hlog : Real.log (Rserre / δ) = Real.log Rserre + Real.log (1 / δ) := by
    rw [Real.log_div (ne_of_gt Rserre_pos) (ne_of_gt hδ0)]
    have hli : Real.log (1 / δ) = -Real.log δ := by
      simpa [one_div] using (Real.log_inv δ)
    linarith
  rw [hlog]
  have h1 := log_one_over_delta_le Csp δ n hCsp hn hδ
  have hcsp2 : (4 * Csp ^ 2) ≠ 0 := by
    have h : 0 < 4 * Csp ^ 2 := by nlinarith [hCsp]
    exact ne_of_gt h
  have heq : Real.log (4 * Csp ^ 2) + Real.log Rserre = Real.log (4 * Csp ^ 2 * Rserre) := by
    rw [← Real.log_mul hcsp2 (ne_of_gt Rserre_pos)]
  nlinarith [h1, heq]

/-- `n · sqrt(2δ) ≤ 1` for `δ = (Csp n)^{-2}/4`, `Csp ≥ 1`, `n ≥ 2`. -/
lemma n_sqrt_two_delta_le_one (Csp δ : ℝ) (n : ℕ) (hCsp : 1 ≤ Csp) (hn : 2 ≤ n)
    (hδ : δ = ((Csp * (n : ℝ))⁻¹ ^ 2) / 4) :
    (n : ℝ) * Real.sqrt (2 * δ) ≤ 1 := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hCsp0 : 0 < Csp := by linarith
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have h2δ : 2 * δ ≤ (Csp * (n : ℝ))⁻¹ ^ 2 := by
    rw [hδ]
    have hx0 : 0 ≤ (Csp * (n : ℝ))⁻¹ ^ 2 := by positivity
    have hc : 2 * (((Csp * (n : ℝ))⁻¹ ^ 2) / 4) = ((Csp * (n : ℝ))⁻¹ ^ 2) / 2 := by ring
    rw [hc]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hsqrtle : Real.sqrt (2 * δ) ≤ Real.sqrt ((Csp * (n : ℝ))⁻¹ ^ 2) := by
    exact Real.sqrt_le_sqrt h2δ
  have hsqid : Real.sqrt ((Csp * (n : ℝ))⁻¹ ^ 2) = (Csp * (n : ℝ))⁻¹ := by
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg (inv_nonneg.mpr (mul_nonneg (le_of_lt hCsp0) (le_of_lt hn0)))]
  have hsq : Real.sqrt (2 * δ) ≤ (Csp * (n : ℝ))⁻¹ := by
    rwa [hsqid] at hsqrtle
  have hmul := mul_le_mul_of_nonneg_left hsq (le_of_lt hn0)
  have hcancel : (n : ℝ) * (Csp * (n : ℝ))⁻¹ = Csp⁻¹ := by
    field_simp [hn0.ne', hCsp0.ne']
  rw [hcancel] at hmul
  have hle : Csp⁻¹ ≤ 1 := by
    rw [← one_div]
    exact (div_le_iff₀ hCsp0).2 (by simpa using hCsp)
  exact le_trans hmul hle

/-- each tail count is at most `n` (counting a subset of `[1..n]`). -/
lemma tailCount_le_n (n : ℕ) (x s : ℝ) : (tailCount n x s : ℝ) ≤ (n : ℝ) := by
  have hc : tailCount n x s ≤ n := by
    unfold tailCount
    calc
      ((Finset.Icc 1 n).filter (fun i : ℕ => alpha n i ∈ Set.Icc (x - tailRad s) (x + tailRad s))).card
          ≤ (Finset.Icc 1 n).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = n := by
        rw [Nat.card_Icc]
        omega
  exact_mod_cast hc

/-- `tailRad s = Rserre·e^{-s}` is strictly below `c` once `log(Rserre/c) < s`. -/
lemma tailRad_lt_of_log_lt_self {s c : ℝ} (hc0 : 0 < c) (hs : Real.log (Rserre / c) < s) :
    tailRad s < c := by
  dsimp [tailRad]
  have hq : 0 < Rserre / c := div_pos Rserre_pos hc0
  have hlt : Rserre / c < Real.exp s := (Real.log_lt_iff_lt_exp hq).mp hs
  have hmul1 : Rserre < Real.exp s * c := (div_lt_iff₀ hc0).mp hlt
  have he : Real.exp s * Real.exp (-s) = 1 := by
    rw [← Real.exp_add]
    have hs0 : s + (-s) = 0 := by ring
    rw [hs0, Real.exp_zero]
  calc
    Rserre * Real.exp (-s) < (Real.exp s * c) * Real.exp (-s) :=
      mul_lt_mul_of_pos_right hmul1 (Real.exp_pos (-s))
    _ = c * (Real.exp s * Real.exp (-s)) := by ring
    _ = c := by rw [he, mul_one]

/-- If `log(Rserre/rho) < s` then the tail ball contains no roots (`tailCount = 0`). -/
lemma tailCount_zero_of_log_lt (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hrho : 0 < rho n x) (s : ℝ)
    (hs : Real.log (Rserre / rho n x) < s) : tailCount n x s = 0 := by
  have hρ : tailRad s < rho n x := tailRad_lt_of_log_lt_self hrho hs
  unfold tailCount
  have hf : (Finset.Icc 1 n).filter (fun i : ℕ => alpha n i ∈ Set.Icc (x - tailRad s) (x + tailRad s)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hi1, hi2⟩
    have hball : |x - alpha n i| ≤ tailRad s :=
      (root_in_ball_iff_dist (le_of_lt (tailRad_pos s)) hi1).mp hi2
    have hle : rho n x ≤ |x - alpha n i| := rho_le_root hn x hi1
    nlinarith
  rw [hf]
  simp

/-- `tailCount` is integrable on the half-line (at a non-root `x`, so the tail count
eventually vanishes). -/
lemma tailCount_integrableOn (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hrho : 0 < rho n x) :
    MeasureTheory.IntegrableOn (fun s : ℝ => (tailCount n x s : ℝ)) (Set.Ioi 0) volume := by
  let f : ℝ → ℝ := fun s : ℝ => (tailCount n x s : ℝ)
  let S : ℝ := max (Real.log (Rserre / rho n x) + 1) 0
  have hS0 : 0 ≤ S := by dsimp [S]; exact le_max_right _ _
  have hvan : ∀ s : ℝ, S ≤ s → tailCount n x s = 0 := by
    intro s hs
    apply tailCount_zero_of_log_lt n hn hrho s
    have h1 : Real.log (Rserre / rho n x) + 1 ≤ S := by dsimp [S]; exact le_max_left _ _
    have h2 : Real.log (Rserre / rho n x) < Real.log (Rserre / rho n x) + 1 := by linarith
    exact lt_of_lt_of_le h2 (le_trans h1 hs)
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 S ∪ Set.Ioi S := by
    ext s
    simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union, Set.mem_Ioi]
    constructor
    · intro hsp
      by_cases hsS : s ≤ S
      · left; exact ⟨hsp, hsS⟩
      · right; exact lt_of_not_ge hsS
    · intro hsp
      rcases hsp with h1 | h2
      · exact h1.1
      · exact lt_of_le_of_lt hS0 h2
  have hmeas : Measurable f := by
    dsimp [f]
    exact (tailCount_antitone n x).measurable
  have hfin : volume (Set.Ioc 0 S) ≠ ∞ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hg1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (n : ℝ)) (Set.Ioc 0 S) volume := by
    exact MeasureTheory.integrableOn_const (μ := volume) (s := Set.Ioc 0 S) (C := (n : ℝ)) hfin (by simp)
  have hf1 : MeasureTheory.IntegrableOn f (Set.Ioc 0 S) volume := by
    refine MeasureTheory.Integrable.mono' hg1 hmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun s => ?_)
    have hnn : 0 ≤ (tailCount n x s : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have hle : (tailCount n x s : ℝ) ≤ (n : ℝ) := tailCount_le_n n x s
    simpa [f, Real.norm_eq_abs, abs_of_nonneg hnn] using hle
  have hf2 : MeasureTheory.IntegrableOn f (Set.Ioi S) volume := by
    have hz : MeasureTheory.IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Ioi S) volume :=
      MeasureTheory.integrableOn_zero
    refine hz.congr_fun ?_ measurableSet_Ioi
    intro s hs
    dsimp [f]
    exact_mod_cast (hvan s (le_of_lt hs)).symm
  have hunion : MeasureTheory.IntegrableOn f (Set.Ioc 0 S ∪ Set.Ioi S) volume := hf1.union hf2
  rwa [← hsplit] at hunion

/-- `n·tailMass − tailCount` is integrable on `(0,∞)` (at a non-root `x`). -/
lemma diff_integrableOn (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hrho : 0 < rho n x) :
    MeasureTheory.IntegrableOn (fun s : ℝ => ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ)))
      (Set.Ioi 0) volume := by
  have ht : MeasureTheory.IntegrableOn (fun s : ℝ => (tailCount n x s : ℝ)) (Set.Ioi 0) volume :=
    tailCount_integrableOn n hn hrho
  have hm : MeasureTheory.IntegrableOn (fun s : ℝ => (n : ℝ) * tailMass x s) (Set.Ioi 0) volume := by
    have htm : MeasureTheory.Integrable (fun s : ℝ => tailMass x s) (volume.restrict (Set.Ioi 0)) := by
      simpa [MeasureTheory.IntegrableOn] using tailMass_integrableOn x
    simpa [MeasureTheory.IntegrableOn] using (htm.const_mul (n : ℝ))
  exact hm.sub ht

/-- On the set `(0, s0]` the difference is integrable as well. -/
lemma diff_integrableOn_Ioc (n : ℕ) (x : ℝ) (s0 : ℝ) :
    MeasureTheory.IntegrableOn (fun s : ℝ => ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ)))
      (Set.Ioc 0 s0) volume := by
  let g : ℝ → ℝ := fun s : ℝ => ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ))
  let C1 : ℝ := Cmu * Real.sqrt (2 * Rserre)
  have hC1 : 0 ≤ C1 := by
    dsimp [C1]
    exact mul_nonneg (le_of_lt Cmu_pos) (Real.sqrt_nonneg _)
  let B : ℝ := (n : ℝ) * C1 + (n : ℝ)
  have hb : ∀ s : ℝ, 0 ≤ s → |g s| ≤ B := by
    intro s hs0
    have hdec : tailMass x s ≤ C1 * Real.exp (-s / 2) := by
      dsimp [C1]
      exact tailMass_le_decay x s
    have hexp : Real.exp (-s / 2) ≤ (1 : ℝ) := by
      have : -s / 2 ≤ 0 := by linarith
      simpa using (Real.exp_le_exp).2 this
    have hmC : tailMass x s ≤ C1 := by
      calc
        tailMass x s ≤ C1 * Real.exp (-s / 2) := hdec
        _ ≤ C1 * 1 := mul_le_mul_of_nonneg_left hexp hC1
        _ = C1 := by ring
    have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have ha0 : 0 ≤ (n : ℝ) * tailMass x s := by
      exact mul_nonneg hn0 (by simpa [tailMass] using Mball_nonneg x (tailRad s))
    have hb0 : 0 ≤ (tailCount n x s : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have ha : (n : ℝ) * tailMass x s ≤ (n : ℝ) * C1 := by
      exact mul_le_mul_of_nonneg_left hmC hn0
    have hb1 : (tailCount n x s : ℝ) ≤ (n : ℝ) := tailCount_le_n n x s
    have htri : |(n : ℝ) * tailMass x s - (tailCount n x s : ℝ)|
        ≤ (n : ℝ) * tailMass x s + (tailCount n x s : ℝ) := by
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have hsum : (n : ℝ) * tailMass x s + (tailCount n x s : ℝ) ≤ B := by
      dsimp [B]
      have h1s : (n : ℝ) * tailMass x s + (tailCount n x s : ℝ)
          ≤ (n : ℝ) * C1 + (tailCount n x s : ℝ) := add_le_add_left ha (tailCount n x s : ℝ)
      have h2s : (n : ℝ) * C1 + (tailCount n x s : ℝ) ≤ (n : ℝ) * C1 + (n : ℝ) := add_le_add_right hb1 ((n : ℝ) * C1)
      exact le_trans h1s h2s
    simpa [g, Real.norm_eq_abs] using le_trans htri hsum
  have hgmeas : Measurable g := by
    dsimp [g]
    have h1m : Measurable (fun s : ℝ => (n : ℝ) * tailMass x s) :=
      (tailMass_measurable x).const_mul (n : ℝ)
    have h2m : Measurable (fun s : ℝ => (tailCount n x s : ℝ)) := (tailCount_antitone n x).measurable
    exact h1m.sub h2m
  have hg : MeasureTheory.IntegrableOn g (Set.Ioc 0 s0) volume := by
    have hfin : volume (Set.Ioc 0 s0) ≠ ∞ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    have hgc : MeasureTheory.IntegrableOn (fun _ : ℝ => B) (Set.Ioc 0 s0) volume := by
      exact MeasureTheory.integrableOn_const (μ := volume) (s := Set.Ioc 0 s0) (C := B) hfin (by simp)
    refine MeasureTheory.Integrable.mono' hgc hgmeas.aestronglyMeasurable ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun s hs => ?_)
    have hs0 : 0 ≤ s := le_of_lt hs.1
    simpa [g, Real.norm_eq_abs] using hb s hs0
  simpa [g] using hg


/-- Splitting the half-line integral at `s0 ≥ 0`. -/
lemma Ioi_split (f : ℝ → ℝ) (s0 : ℝ) (hs0 : 0 ≤ s0)
    (hf : MeasureTheory.IntegrableOn f (Set.Ioi 0) volume) :
    (∫ s : ℝ in Set.Ioi 0, f s) =
      (∫ s : ℝ in Set.Ioc 0 s0, f s) + (∫ s : ℝ in Set.Ioi s0, f s) := by
  have hsub1 : Set.Ioc 0 s0 ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact hx.1
  have hsub2 : Set.Ioi s0 ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_le_of_lt hs0 hx
  have hf1 : MeasureTheory.IntegrableOn f (Set.Ioc 0 s0) volume := hf.mono_set hsub1
  have hf2 : MeasureTheory.IntegrableOn f (Set.Ioi s0) volume := hf.mono_set hsub2
  have hcover : Set.Ioi (0 : ℝ) = Set.Ioc 0 s0 ∪ Set.Ioi s0 := by
    ext x
    constructor
    · intro hx
      by_cases hxs : x ≤ s0
      · exact Or.inl ⟨hx, hxs⟩
      · exact Or.inr (lt_of_not_ge hxs)
    · intro hx
      rcases hx with hx | hx
      · exact hx.1
      · exact lt_of_le_of_lt hs0 hx
  have hdisj : Disjoint (Set.Ioc 0 s0) (Set.Ioi s0) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact (not_lt_of_ge hx1.2) hx2
  rw [hcover]
  rw [MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hf1 hf2]

/-- integral of `e^{-s/2}` over `(s0, ∞)` equals `2·e^{-s0/2}`. -/
lemma integral_exp_half_Ioi (s0 : ℝ) :
    (∫ s : ℝ in Set.Ioi s0, Real.exp (-s / 2)) = 2 * Real.exp (-s0 / 2) := by
  have hφ : (fun s : ℝ => Real.exp (-s / 2)) = fun s : ℝ => Real.exp (-(1 / 2 : ℝ) * s) := by
    funext s
    congr 1
    ring
  rw [hφ]
  rw [integral_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) s0]
  ring_nf

/-- decay-piece bound: `∫_{(s0,∞)} n·tailMass ≤ n·Cmu·√(2Rserre)·2·e^{-s0/2}`. -/
lemma tailMass_tailpiece_le (n : ℕ) (x s0 : ℝ) :
    (∫ s : ℝ in Set.Ioi s0, (n : ℝ) * tailMass x s)
      ≤ (n : ℝ) * Cmu * Real.sqrt (2 * Rserre) * (2 * Real.exp (-s0 / 2)) := by
  let b : ℝ → ℝ := fun s : ℝ => (n : ℝ) * Cmu * Real.sqrt (2 * Rserre) * Real.exp (-s / 2)
  have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have htail_nonneg : ∀ s : ℝ, 0 ≤ tailMass x s := by
    intro s
    simpa [tailMass] using Mball_nonneg x (tailRad s)
  have hpt_le : ∀ s : ℝ, (n : ℝ) * tailMass x s ≤ b s := by
    intro s
    calc
      (n : ℝ) * tailMass x s
          ≤ (n : ℝ) * (Cmu * Real.sqrt (2 * Rserre) * Real.exp (-s / 2)) :=
            mul_le_mul_of_nonneg_left (tailMass_le_decay x s) hn0
      _ = b s := by
        dsimp [b]
        ring
  have hident : (fun s : ℝ => Real.exp (-s / 2)) = fun s : ℝ => Real.exp (-(1 / 2 : ℝ) * s) := by
    funext s
    congr 1
    ring
  have hbase : MeasureTheory.IntegrableOn (fun s : ℝ => Real.exp (-s / 2)) (Set.Ioi s0) volume := by
    rw [hident]
    exact integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) s0
  have hb_int : MeasureTheory.IntegrableOn b (Set.Ioi s0) volume := by
    change MeasureTheory.Integrable
      (fun s : ℝ => (n : ℝ) * Cmu * Real.sqrt (2 * Rserre) * Real.exp (-s / 2))
        (volume.restrict (Set.Ioi s0))
    exact hbase.const_mul ((n : ℝ) * Cmu * Real.sqrt (2 * Rserre))
  have hf0 : 0 ≤ᵐ[volume.restrict (Set.Ioi s0)] (fun s : ℝ => (n : ℝ) * tailMass x s) := by
    exact ae_of_all _ (fun s => mul_nonneg hn0 (htail_nonneg s))
  have hfle : (fun s : ℝ => (n : ℝ) * tailMass x s) ≤ᵐ[volume.restrict (Set.Ioi s0)] b := by
    exact ae_of_all _ hpt_le
  have hmono : (∫ s : ℝ in Set.Ioi s0, (n : ℝ) * tailMass x s) ≤ ∫ s : ℝ in Set.Ioi s0, b s := by
    simpa using (MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict (Set.Ioi s0))
      (f := fun s : ℝ => (n : ℝ) * tailMass x s) (g := b) hf0 hb_int hfle)
  have hval : (∫ s : ℝ in Set.Ioi s0, b s) =
      (n : ℝ) * Cmu * Real.sqrt (2 * Rserre) * (2 * Real.exp (-s0 / 2)) := by
    dsimp [b]
    rw [integral_const_mul]
    rw [integral_exp_half_Ioi]
  calc
    (∫ s : ℝ in Set.Ioi s0, (n : ℝ) * tailMass x s) ≤ ∫ s : ℝ in Set.Ioi s0, b s := hmono
    _ = (n : ℝ) * Cmu * Real.sqrt (2 * Rserre) * (2 * Real.exp (-s0 / 2)) := hval

/-- `|n·tailMass − tailCount| ≤ Cnt` pointwise on `(0, s0]` is integrated:
`|∫_{(0,s0]} (n·tailMass − tailCount)| ≤ Cnt·s0`. -/
lemma noTel_Ioc_bound (n : ℕ) (x : ℝ) (Cnt s0 : ℝ) (hCnt : 0 ≤ Cnt) (hs0 : 0 ≤ s0)
    (hpt : ∀ s : ℝ, 0 ≤ s → s ≤ s0 →
      |(n : ℝ) * tailMass x s - (tailCount n x s : ℝ)| ≤ Cnt) :
    |(∫ s : ℝ in Set.Ioc 0 s0, ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ)))| ≤ Cnt * s0 := by
  have hvol : volume (Set.Ioc 0 s0) < ∞ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hb : ∀ s ∈ Set.Ioc 0 s0,
      ‖(n : ℝ) * tailMass x s - (tailCount n x s : ℝ)‖ ≤ Cnt := by
    intro s hs
    rw [Real.norm_eq_abs]
    exact hpt s (le_of_lt hs.1) hs.2
  have hmain := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc 0 s0)
    (f := fun s : ℝ => (n : ℝ) * tailMass x s - (tailCount n x s : ℝ)) hvol hb
  have hreal : (volume (Set.Ioc 0 s0)).toReal = s0 := by
    rw [Real.volume_Ioc]
    simp [hs0]
  have hmain0 : ‖(∫ s : ℝ in Set.Ioc 0 s0, ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ)))‖
      ≤ Cnt * (volume (Set.Ioc 0 s0)).toReal := by
    simpa [Measure.real] using hmain
  have hmain1 : ‖(∫ s : ℝ in Set.Ioc 0 s0, ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ)))‖
      ≤ Cnt * s0 := by
    exact le_trans hmain0 (mul_le_mul_of_nonneg_left (le_of_eq hreal) hCnt)
  simpa [Real.norm_eq_abs] using hmain1



/-- `√(e^{-x}) = e^{-x/2}`. -/
lemma sqrt_exp_neg (x : ℝ) : Real.sqrt (Real.exp (-x)) = Real.exp (-x / 2) := by
  have hpow : Real.exp (-x) = (Real.exp (-x / 2)) ^ 2 := by
    calc
      Real.exp (-x) = Real.exp (-x / 2 + -x / 2) := by congr 1; ring
      _ = Real.exp (-x / 2) * Real.exp (-x / 2) := Real.exp_add _ _
      _ = (Real.exp (-x / 2)) ^ 2 := by rw [sq]
  rw [hpow]
  rw [Real.sqrt_sq_eq_abs]
  rw [abs_of_pos (Real.exp_pos _)]


/-- `exp(-(1/2)·log(Rserre/δ)) = √(δ/Rserre)` for `0 < δ`. -/
lemma exp_half_log_ratio {δ : ℝ} (hδ : 0 < δ) :
    Real.exp (-(1 / 2 : ℝ) * Real.log (Rserre / δ)) = Real.sqrt (δ / Rserre) := by
  have ha : 0 < Rserre / δ := div_pos Rserre_pos hδ
  have h1 : Real.exp (-Real.log (Rserre / δ)) = δ / Rserre := by
    rw [Real.exp_neg]
    rw [Real.exp_log ha]
    field_simp [ne_of_gt hδ]
  let a : ℝ := Real.exp (-(1 / 2 : ℝ) * Real.log (Rserre / δ))
  let b : ℝ := Real.sqrt (δ / Rserre)
  have ha0 : 0 ≤ a := (Real.exp_pos _).le
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hsa : a ^ 2 = δ / Rserre := by
    dsimp [a]
    calc
      (Real.exp (-(1 / 2 : ℝ) * Real.log (Rserre / δ))) ^ 2
          = Real.exp (-Real.log (Rserre / δ)) := by
            rw [sq]
            rw [← Real.exp_add]
            congr 1
            ring
      _ = δ / Rserre := h1
  have hsb : b ^ 2 = δ / Rserre := by
    dsimp [b]
    exact Real.sq_sqrt (div_nonneg (le_of_lt hδ) (le_of_lt Rserre_pos))
  apply le_antisymm
  · have hle : a ^ 2 ≤ b ^ 2 := by rw [hsa, hsb]
    have habs := (sq_le_sq.mp hle)
    have habsa : |a| = a := abs_of_nonneg ha0
    have habsb : |b| = b := abs_of_nonneg hb0
    rwa [habsa, habsb] at habs
  · have hle : b ^ 2 ≤ a ^ 2 := by rw [hsb, hsa]
    have habs := (sq_le_sq.mp hle)
    have habsa : |a| = a := abs_of_nonneg ha0
    have habsb : |b| = b := abs_of_nonneg hb0
    rwa [habsa, habsb] at habs


/-- the atomic tail integral equals the sum of the log ratios. -/
lemma atomic_tail_sum (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre)
    (hrho : 0 < rho n x) :
    (∫ s : ℝ in Set.Ioi 0, (tailCount n x s : ℝ)) = ∑ i ∈ Finset.Icc 1 n, logRatio n x i := by
  simpa [logRatio] using (atomicTailIntegral n hn hx hrho)

/-- exact representation of the target quantity. -/
lemma T_eq (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) (hrho : 0 < rho n x) :
    (n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x|
        - Real.log (rho n x)
      = (n : ℝ) * (∫ s : ℝ in Set.Ioi 0, tailMass x s)
        - (∫ s : ℝ in Set.Ioi 0, (tailCount n x s : ℝ))
        - Real.log (rho n x) := by
  have hlc := layerCakeTail x hx
  have hU : logPotential muS (x : ℂ) = (∫ s : ℝ in Set.Ioi 0, tailMass x s) - Real.log Rserre := by
    linarith [layerCake_tailMass x hx]
  have hat := atomic_tail_sum n hn hx hrho
  have hsum := sum_logs_eq_sum_ratio n hn hx hrho
  rw [log_abs_eval n hn x hrho]
  calc
    (n : ℝ) * logPotential muS (x : ℂ) + (∑ i ∈ Finset.Icc 1 n, Real.log (|x - alpha n i|))
        - Real.log (rho n x)
        = (n : ℝ) * ((∫ s : ℝ in Set.Ioi 0, tailMass x s) - Real.log Rserre)
            + ((n : ℝ) * Real.log Rserre - ∑ i ∈ Finset.Icc 1 n, logRatio n x i)
            - Real.log (rho n x) := by rw [hU, hsum]
    _ = (n : ℝ) * (∫ s : ℝ in Set.Ioi 0, tailMass x s)
          - (∑ i ∈ Finset.Icc 1 n, logRatio n x i) - Real.log (rho n x) := by ring
    _ = (n : ℝ) * (∫ s : ℝ in Set.Ioi 0, tailMass x s)
          - (∫ s : ℝ in Set.Ioi 0, (tailCount n x s : ℝ)) - Real.log (rho n x) := by rw [← hat]


/-- decompose the target into the `(0,sδ]` and `(sδ,∞)` pieces. -/
lemma decompose_T (n : ℕ) (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre)
    (hrho : 0 < rho n x) (sδ : ℝ) (hsδ0 : 0 ≤ sδ) :
    (n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x|
        - Real.log (rho n x)
      = (∫ s : ℝ in Set.Ioc 0 sδ, ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ)))
        + (∫ s : ℝ in Set.Ioi sδ, ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ)))
        - Real.log (rho n x) := by
  have hT := T_eq n (by omega : 1 ≤ n) hx hrho
  -- linearity over Ioi 0
  have hlin : (∫ s : ℝ in Set.Ioi 0, ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ)))
      = (n : ℝ) * (∫ s : ℝ in Set.Ioi 0, tailMass x s)
        - (∫ s : ℝ in Set.Ioi 0, (tailCount n x s : ℝ)) := by
    -- integral_sub etc.
    have hf : MeasureTheory.Integrable (fun s : ℝ => (n : ℝ) * tailMass x s) (volume.restrict (Set.Ioi 0)) := by
      change MeasureTheory.IntegrableOn (fun s : ℝ => (n : ℝ) * tailMass x s) (Set.Ioi 0) volume
      exact (tailMass_integrableOn x).const_mul (n : ℝ)
    have hg : MeasureTheory.Integrable (fun s : ℝ => (tailCount n x s : ℝ)) (volume.restrict (Set.Ioi 0)) := by
      change MeasureTheory.IntegrableOn (fun s : ℝ => (tailCount n x s : ℝ)) (Set.Ioi 0) volume
      exact tailCount_integrableOn n (by omega : 1 ≤ n) hrho
    have hsub := MeasureTheory.integral_sub hf hg
    have hmul : (∫ s : ℝ in Set.Ioi 0, (n : ℝ) * tailMass x s)
        = (n : ℝ) * (∫ s : ℝ in Set.Ioi 0, tailMass x s) := by
      exact MeasureTheory.integral_const_mul (n : ℝ) (fun s : ℝ => tailMass x s)
    rw [hsub]
    rw [hmul]
  -- split the difference integral at sδ
  have hsplit := Ioi_split (fun s : ℝ => ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ))) sδ hsδ0
    (diff_integrableOn n (by omega : 1 ≤ n) hrho)
  calc
    (n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x| - Real.log (rho n x)
        = (∫ s : ℝ in Set.Ioi 0, ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ)))
            - Real.log (rho n x) := by
          rw [hT]
          rw [hlin]
    _ = (∫ s : ℝ in Set.Ioc 0 sδ, ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ)))
          + (∫ s : ℝ in Set.Ioi sδ, ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ)))
          - Real.log (rho n x) := by rw [hsplit]

/-- absorption: `B ≤ (B/L)·A` for `B ≥ 0`, `0 < L ≤ A`. -/
lemma abs_absorb {A B L : ℝ} (hB : 0 ≤ B) (hL : 0 < L) (hge : L ≤ A) :
    B ≤ (B / L) * A := by
  have hA : 0 ≤ A / L := le_of_lt (div_pos (lt_of_lt_of_le hL hge) hL)
  have hone : 1 ≤ A / L := (one_le_div hL).2 hge
  have hBm : B ≤ B * (A / L) := by
    simpa using (mul_le_mul_of_nonneg_left hone hB)
  have hBmL : B * (A / L) = (B / L) * A := by
    field_simp [ne_of_gt hL]
  rwa [hBmL] at hBm

/-- linearity of set integrals on the half-line piece. -/
lemma integral_lin_Ioi (a s0 : ℝ) (f g : ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn f (Set.Ioi s0) volume)
    (hg : MeasureTheory.IntegrableOn g (Set.Ioi s0) volume) :
    (∫ s : ℝ in Set.Ioi s0, (a * f s - g s))
      = a * (∫ s : ℝ in Set.Ioi s0, f s) - (∫ s : ℝ in Set.Ioi s0, g s) := by
  have hfm : MeasureTheory.Integrable (fun s : ℝ => a * f s) (volume.restrict (Set.Ioi s0)) := by
    change MeasureTheory.IntegrableOn (fun s : ℝ => a * f s) (Set.Ioi s0) volume
    exact hf.const_mul a
  have hgm : MeasureTheory.Integrable (fun s : ℝ => g s) (volume.restrict (Set.Ioi s0)) := by
    change MeasureTheory.IntegrableOn g (Set.Ioi s0) volume
    exact hg
  calc
    (∫ s : ℝ in Set.Ioi s0, (a * f s - g s))
        = (∫ s : ℝ in Set.Ioi s0, a * f s) - (∫ s : ℝ in Set.Ioi s0, g s) := by
          rw [MeasureTheory.integral_sub hfm hgm]
    _ = a * (∫ s : ℝ in Set.Ioi s0, f s) - (∫ s : ℝ in Set.Ioi s0, g s) := by
          congr 1
          rw [MeasureTheory.integral_const_mul a f]

/-- bound the `(sδ,∞)` difference piece: `|D − logρ| ≤ n·B2 + |C2 + logρ|`. -/
lemma bound_D (n : ℕ) (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre)
    (hrho : 0 < rho n x) (sδ : ℝ) (hsδ0 : 0 ≤ sδ) :
    |(∫ s : ℝ in Set.Ioi sδ, ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ)))
        - Real.log (rho n x)|
      ≤ (n : ℝ) * (∫ s : ℝ in Set.Ioi sδ, tailMass x s)
        + |Real.log (rho n x) + (∫ s : ℝ in Set.Ioi sδ, (tailCount n x s : ℝ))| := by
  have hf : MeasureTheory.IntegrableOn (fun s : ℝ => tailMass x s) (Set.Ioi sδ) volume := by
    exact (tailMass_integrableOn x).mono_set (by intro s hs; exact lt_of_le_of_lt hsδ0 (Set.mem_Ioi.mp hs))
  have hg : MeasureTheory.IntegrableOn (fun s : ℝ => (tailCount n x s : ℝ)) (Set.Ioi sδ) volume := by
    exact (tailCount_integrableOn n hn hrho).mono_set (by intro s hs; exact lt_of_le_of_lt hsδ0 (Set.mem_Ioi.mp hs))
  have hlin := integral_lin_Ioi (n : ℝ) sδ (fun s : ℝ => tailMass x s) (fun s : ℝ => (tailCount n x s : ℝ)) hf hg
  let u : ℝ := (n : ℝ) * (∫ s : ℝ in Set.Ioi sδ, tailMass x s)
  let C2 : ℝ := ∫ s : ℝ in Set.Ioi sδ, (tailCount n x s : ℝ)
  let l : ℝ := Real.log (rho n x)
  have hB2 : 0 ≤ u := by
    dsimp [u]
    have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hnn : 0 ≤ (∫ s : ℝ in Set.Ioi sδ, tailMass x s) := by
      apply MeasureTheory.integral_nonneg_of_ae
      · filter_upwards with s
        exact Mball_nonneg x (tailRad s)
    exact mul_nonneg hn0 hnn
  have htri : |u - (C2 + l)| ≤ u + |C2 + l| := by
    have ht := abs_add_le u (-(C2 + l))
    have hu' : |u| = u := abs_of_nonneg hB2
    have harg' : u - (C2 + l) = u + (-(C2 + l)) := by ring
    calc
      |u - (C2 + l)| = |u + (-(C2 + l))| := by rw [harg']
      _ ≤ |u| + |-(C2 + l)| := ht
      _ = u + |C2 + l| := by rw [hu']; rw [abs_neg]
  have harg2 : (∫ s : ℝ in Set.Ioi sδ, ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ)))
        - Real.log (rho n x) = u - (C2 + l) := by
    rw [hlin]
    dsimp [u, C2, l]
    ring
  rw [harg2]
  dsimp [u, C2, l]
  simpa [add_comm] using htri

/-- **Main theorem (eq:explicit_pot_approx for our interval):**
`| n·U^μ(x) + log|P_{n,μ}(x)| − log ρ_n(x) | ≤ C·log(n+2)`
for `n ≥ 2`, `x ∈ [aSerre,bSerre]`, `0 < ρ_n(x)`. -/
theorem approx_potential_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      0 < rho n x →
      |(n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x|
          - Real.log (rho n x)| ≤ C * Real.log ((n : ℝ) + 2) := by
  rcases at_most_one_root_in_short_interval with ⟨Csp, hCsp1, hCsp⟩
  rcases exists_interval_no_telescope with ⟨Cnt, hCntPos, hNoTel⟩
  have hCnt : 0 ≤ Cnt := le_of_lt hCntPos
  let L : ℝ := Real.log 4
  have hL : 0 < L := by dsimp [L]; exact Real.log_pos (by norm_num)
  let L1 : ℝ := Real.log (4 * Csp ^ 2 * Rserre)
  let L2 : ℝ := Real.log (4 * Csp ^ 2)
  have hL1nn : 0 ≤ L1 := by
    dsimp [L1]
    apply Real.log_nonneg
    nlinarith [hCsp1, Rserre_ge_one]
  have hL2nn : 0 ≤ L2 := by
    dsimp [L2]
    apply Real.log_nonneg
    nlinarith [hCsp1]
  have hRnn : 0 ≤ Real.log Rserre := log_Rserre_nonneg
  let B0 : ℝ := 2 * Cnt * L1 + 2 * Cmu + Real.log Rserre + L2
  have hCmuNN : 0 ≤ Cmu := le_of_lt Cmu_pos
  have hB0 : 0 ≤ B0 := by
    dsimp [B0]
    nlinarith [hCnt, hL1nn, hCmuNN, hRnn, hL2nn]
  let C0 : ℝ := (2 * (Cnt + 1)) + B0 / L
  refine ⟨C0, ?_, ?_⟩
  · have h1 : 0 < 2 * (Cnt + 1) := by nlinarith [hCnt]
    have h2 : 0 ≤ B0 / L := div_nonneg hB0 (le_of_lt hL)
    dsimp [C0]
    nlinarith
  · intro n hn x hx hrho
    have hn1 : 1 ≤ n := by omega
    let δ : ℝ := ((Csp * (n : ℝ))⁻¹ ^ 2) / 4
    have hδ : δ = ((Csp * (n : ℝ))⁻¹ ^ 2) / 4 := rfl
    have hCsp0 : 0 < Csp := by linarith
    have hnn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hmn0 : 0 < Csp * (n : ℝ) := mul_pos hCsp0 hnn0
    have hδ0 : 0 < δ := by
      dsimp [δ]
      exact div_pos (pow_pos (inv_pos.mpr hmn0) 2) (by norm_num)
    have hδ1 : δ < 1 := by
      dsimp [δ]
      have hnn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hsp : 2 ≤ Csp * (n : ℝ) := by nlinarith [hCsp1, hnn2]
      have hinv : (Csp * (n : ℝ))⁻¹ ≤ (1 / 2 : ℝ) := by
        rw [one_div]
        exact (inv_le_inv₀ hmn0 (by norm_num : (0 : ℝ) < 2)).2 hsp
      have hpow : (Csp * (n : ℝ))⁻¹ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt hmn0)) hinv 2
      nlinarith
    have h2δ : 2 * δ < (Csp * (n : ℝ))⁻¹ ^ 2 := by
      dsimp [δ]
      have hxpos : 0 < (Csp * (n : ℝ))⁻¹ ^ 2 := pow_pos (inv_pos.mpr hmn0) 2
      have hc : 2 * (((Csp * (n : ℝ))⁻¹ ^ 2) / 4) = ((Csp * (n : ℝ))⁻¹ ^ 2) / 2 := by ring
      rw [hc]
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    let sδ : ℝ := Real.log (Rserre / δ)
    have hsδ0 : 0 ≤ sδ := by
      dsimp [sδ]
      apply Real.log_nonneg
      rw [one_le_div hδ0]
      have hR1 : 1 ≤ Rserre := Rserre_ge_one
      nlinarith
    have hAtMost := hCsp n hn (x - δ) (2 * δ) (by linarith) h2δ
    have hatmost : ((Finset.Icc 1 n).filter (fun i : ℕ => x - δ ≤ alpha n i ∧ alpha n i ≤ x + δ)).card ≤ 1 := by
      simpa [show x - δ + 2 * δ = x + δ by ring] using hAtMost
    have hdec := decompose_T n hn hx hrho sδ hsδ0
    have hpt : ∀ s : ℝ, 0 ≤ s → s ≤ sδ →
        |(n : ℝ) * tailMass x s - (tailCount n x s : ℝ)| ≤ Cnt := by
      intro s hs0 hsle
      exact noTel_tail_mass Cnt hCnt hNoTel hn hx s hs0
    have hA : |(∫ s : ℝ in Set.Ioc 0 sδ, ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ)))|
        ≤ Cnt * sδ := by
      exact noTel_Ioc_bound n x Cnt sδ hCnt hsδ0 hpt
    have hB2 : (n : ℝ) * (∫ s : ℝ in Set.Ioi sδ, tailMass x s) ≤ 2 * Cmu := by
      have h1 := tailMass_tailpiece_le n x sδ
      have hsδeq : sδ = Real.log (Rserre / δ) := rfl
      have heq : Real.exp (-sδ / 2) = Real.sqrt (δ / Rserre) := by
        rw [hsδeq]
        have h := exp_half_log_ratio hδ0
        calc
          Real.exp (-Real.log (Rserre / δ) / 2) = Real.exp (-(1 / 2 : ℝ) * Real.log (Rserre / δ)) := by congr 1; ring
          _ = Real.sqrt (δ / Rserre) := h
      have hsqrtm : Real.sqrt (2 * Rserre) * Real.sqrt (δ / Rserre) = Real.sqrt (2 * δ) := by
        have hx : 0 ≤ (2 : ℝ) * Rserre := mul_nonneg (by norm_num) (le_of_lt Rserre_pos)
        rw [← Real.sqrt_mul (x := (2 : ℝ) * Rserre) hx (δ / Rserre)]
        congr 1
        field_simp [ne_of_gt Rserre_pos, ne_of_gt hδ0]
      have hnsq : (n : ℝ) * Real.sqrt (2 * δ) ≤ 1 := n_sqrt_two_delta_le_one Csp δ n hCsp1 hn hδ
      have hmulid : (∫ s : ℝ in Set.Ioi sδ, (n : ℝ) * tailMass x s)
          = (n : ℝ) * (∫ s : ℝ in Set.Ioi sδ, tailMass x s) := by
        exact MeasureTheory.integral_const_mul (n : ℝ) (fun s : ℝ => tailMass x s)
      rw [hmulid] at h1
      rw [heq] at h1
      have h1' : (n : ℝ) * (∫ s : ℝ in Set.Ioi sδ, tailMass x s)
          ≤ 2 * Cmu * ((n : ℝ) * Real.sqrt (2 * δ)) := by
        calc
          (n : ℝ) * (∫ s : ℝ in Set.Ioi sδ, tailMass x s)
              ≤ (n : ℝ) * Cmu * Real.sqrt (2 * Rserre) * (2 * Real.sqrt (δ / Rserre)) := h1
          _ = 2 * Cmu * ((n : ℝ) * (Real.sqrt (2 * Rserre) * Real.sqrt (δ / Rserre))) := by ring
          _ = 2 * Cmu * ((n : ℝ) * Real.sqrt (2 * δ)) := by rw [hsqrtm]
      nlinarith [h1', hnsq, hCmuNN]
    have hC2 : |Real.log (rho n x) + (∫ s : ℝ in Set.Ioi sδ, (tailCount n x s : ℝ))|
        ≤ Real.log Rserre + Real.log (1 / δ) := by
      have hatom := atomic_piece_bound n hn hx hrho δ hδ0 hδ1 hatmost sδ rfl
      have hEq : |Real.log (rho n x) + (∫ s : ℝ in Set.Ioi sδ, (tailCount n x s : ℝ))|
          = |(-Real.log (rho n x) - (∫ s : ℝ in Set.Ioi sδ, (tailCount n x s : ℝ)))| := by
        rw [← abs_neg (Real.log (rho n x) + (∫ s : ℝ in Set.Ioi sδ, (tailCount n x s : ℝ)))]
        congr 1
        ring
      rwa [hEq.symm] at hatom
    have hDb := bound_D n hn1 hx hrho sδ hsδ0
    have hTbound : |(n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x|
        - Real.log (rho n x)| ≤ Cnt * sδ
          + ((n : ℝ) * (∫ s : ℝ in Set.Ioi sδ, tailMass x s)
            + |Real.log (rho n x) + (∫ s : ℝ in Set.Ioi sδ, (tailCount n x s : ℝ))|) := by
      have hT2 : (n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x|
            - Real.log (rho n x)
          = (∫ s : ℝ in Set.Ioc 0 sδ, ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ)))
            + ((∫ s : ℝ in Set.Ioi sδ, ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ)))
              - Real.log (rho n x)) := by
        rw [hdec]
        ring
      rw [hT2]
      exact le_trans (abs_add_le
        (∫ s : ℝ in Set.Ioc 0 sδ, ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ)))
        ((∫ s : ℝ in Set.Ioi sδ, ((n : ℝ) * tailMass x s - (tailCount n x s : ℝ)))
          - Real.log (rho n x)))
        (add_le_add hA hDb)
    have hFinal0 : |(n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x|
          - Real.log (rho n x)| ≤ Cnt * sδ + 2 * Cmu + Real.log Rserre + Real.log (1 / δ) := by
      calc
        |(n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x| - Real.log (rho n x)|
            ≤ Cnt * sδ + ((n : ℝ) * (∫ s : ℝ in Set.Ioi sδ, tailMass x s)
              + |Real.log (rho n x) + (∫ s : ℝ in Set.Ioi sδ, (tailCount n x s : ℝ))|) := hTbound
        _ ≤ Cnt * sδ + (2 * Cmu + |Real.log (rho n x) + (∫ s : ℝ in Set.Ioi sδ, (tailCount n x s : ℝ))|) := by
              nlinarith [hB2]
        _ ≤ Cnt * sδ + (2 * Cmu + (Real.log Rserre + Real.log (1 / δ))) := by
              nlinarith [hC2]
        _ = Cnt * sδ + 2 * Cmu + Real.log Rserre + Real.log (1 / δ) := by ring
    have h1nsδ : sδ ≤ 2 * Real.log ((n : ℝ) + 2) + L1 := by
      dsimp [L1, sδ]
      exact log_R_over_delta_le Csp δ n hCsp1 hn hδ
    have h1δ : Real.log (1 / δ) ≤ 2 * Real.log ((n : ℝ) + 2) + L2 := by
      dsimp [L2]
      exact log_one_over_delta_le Csp δ n hCsp1 hn hδ
    have hLg : L ≤ Real.log ((n : ℝ) + 2) := by
      dsimp [L]
      exact log_np2_ge_log4 hn
    have hBnd : |(n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x|
          - Real.log (rho n x)| ≤ 2 * (Cnt + 1) * Real.log ((n : ℝ) + 2) + B0 := by
      have hsteps : Cnt * sδ + 2 * Cmu + Real.log Rserre + Real.log (1 / δ)
          ≤ 2 * (Cnt + 1) * Real.log ((n : ℝ) + 2) + B0 := by
        nlinarith [h1nsδ, h1δ, hL1nn, hL2nn, hRnn, hCnt]
      calc
        |(n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x| - Real.log (rho n x)|
            ≤ Cnt * sδ + 2 * Cmu + Real.log Rserre + Real.log (1 / δ) := hFinal0
        _ ≤ 2 * (Cnt + 1) * Real.log ((n : ℝ) + 2) + B0 := hsteps
    have hAbs := abs_absorb (B := B0) (A := Real.log ((n : ℝ) + 2)) hB0 hL hLg
    have hC0def : (2 * (Cnt + 1)) + B0 / L = C0 := rfl
    have hsplit : (2 * (Cnt + 1) + B0 / L) * Real.log ((n : ℝ) + 2)
        = 2 * (Cnt + 1) * Real.log ((n : ℝ) + 2) + (B0 / L) * Real.log ((n : ℝ) + 2) := by ring
    have hsum : 2 * (Cnt + 1) * Real.log ((n : ℝ) + 2) + B0
        ≤ (2 * (Cnt + 1) + B0 / L) * Real.log ((n : ℝ) + 2) := by
      have hpart : 2 * (Cnt + 1) * Real.log ((n : ℝ) + 2) + B0
          ≤ 2 * (Cnt + 1) * Real.log ((n : ℝ) + 2) + (B0 / L) * Real.log ((n : ℝ) + 2) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_left hAbs (2 * (Cnt + 1) * Real.log ((n : ℝ) + 2)))
      rwa [← hsplit] at hpart
    calc
      |(n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x| - Real.log (rho n x)|
          ≤ 2 * (Cnt + 1) * Real.log ((n : ℝ) + 2) + B0 := hBnd
      _ ≤ (2 * (Cnt + 1) + B0 / L) * Real.log ((n : ℝ) + 2) := hsum
      _ = C0 * Real.log ((n : ℝ) + 2) := by rw [hC0def]

/-- **eq:potential_approx (upper form):** `w_μ(x)^n·|P_{n,μ}(x)| ≤ n^C·ρ_n(x)`
for `x ∈ Σ` (roots included: both sides are 0 at a root, and elsewhere use
the main theorem). -/
theorem potential_approx_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      (weight muS x) ^ n * |(approxPoly n).eval x| ≤
        (n : ℝ) ^ C * rho n x := by
  rcases approx_potential_bound with ⟨C1, hC1, hMain⟩
  refine ⟨2 * C1, mul_pos (by norm_num) hC1, ?_⟩
  intro n hn x hx
  by_cases hrz : rho n x = 0
  · -- at a root `rho = 0`, `x` is one of the `alpha n i`, so `P(x) = 0` and
    -- both sides of the claimed inequality vanish.
    have hn1 : 1 ≤ n := by omega
    rcases exists_index_rho (n := n) hn1 x with ⟨i, hi, hval⟩
    have hxi : x = alpha n i := by
      have hz : |x - alpha n i| = 0 := by
        rw [← hval, hrz]
      have hsub : x - alpha n i = 0 := abs_eq_zero.mp hz
      linarith
    have hP0 : (approxPoly n).eval x = 0 := by
      rw [approxPoly_eval n x]
      exact Finset.prod_eq_zero hi (by simp [hxi])
    simp [hrz, hP0]
  · -- `0 < rho n x`: exponentiate the main bound `|X| ≤ C1·log(n+2)`.
    have hrpos : 0 < rho n x := lt_of_le_of_ne (rho_nonneg (n := n) x) (Ne.symm hrz)
    have hn1 : 1 ≤ n := by omega
    have hn0R : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hnn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnp2pos : 0 < (n : ℝ) + 2 := by linarith
    -- `log(n+2) ≤ 2·log n` for `n ≥ 2`
    have hle : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    have hlogest : Real.log ((n : ℝ) + 2) ≤ 2 * Real.log (n : ℝ) := by
      have h1 := Real.log_le_log hnp2pos hle
      have h2 : Real.log ((n : ℝ) ^ 2) = 2 * Real.log (n : ℝ) := by
        rw [Real.log_pow]
        ring
      rwa [h2] at h1
    have hC1nn : 0 ≤ C1 := le_of_lt hC1
    have hm := mul_le_mul_of_nonneg_left hlogest hC1nn
    have hring : C1 * (2 * Real.log (n : ℝ)) = (2 * C1) * Real.log (n : ℝ) := by ring
    have hlog2 : C1 * Real.log ((n : ℝ) + 2) ≤ (2 * C1) * Real.log (n : ℝ) := by
      rwa [hring] at hm
    -- main bound
    have hBnd : |(n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x|
        - Real.log (rho n x)| ≤ C1 * Real.log ((n : ℝ) + 2) := hMain n hn x hx hrpos
    have hA := (abs_le.mp hBnd).2
    have hlin1 : (n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x|
        ≤ Real.log (rho n x) + C1 * Real.log ((n : ℝ) + 2) := by linarith
    have hfin : (n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x|
        ≤ (2 * C1) * Real.log (n : ℝ) + Real.log (rho n x) := by linarith
    -- exponentiate `exp(n·U + log|P|) ≤ exp(log rho + 2·C1·log n)`
    have hwlog : Real.log (weight muS x) = logPotential muS (x : ℂ) := by
      unfold Submission.WeightedNorm.weight
      exact Real.log_exp (logPotential muS (x : ℂ))
    have hPne : (approxPoly n).eval x ≠ 0 := rho_pos_eval_ne_zero (n := n) hn1 (x := x) hrpos
    have hPabs0 : 0 < |(approxPoly n).eval x| := abs_pos.mpr hPne
    have hpos1 : 0 < (weight muS x) ^ n * |(approxPoly n).eval x| :=
      mul_pos (pow_pos (weight_pos muS x) n) hPabs0
    have hpos2 : 0 < (n : ℝ) ^ (2 * C1) * rho n x :=
      mul_pos (Real.rpow_pos_of_pos hn0R (2 * C1)) hrpos
    have hlogLHS : Real.log ((weight muS x) ^ n * |(approxPoly n).eval x|)
        = (n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x| := by
      calc
        Real.log ((weight muS x) ^ n * |(approxPoly n).eval x|)
            = Real.log ((weight muS x) ^ n) + Real.log |(approxPoly n).eval x| :=
                Real.log_mul (pow_ne_zero n (ne_of_gt (weight_pos muS x)))
                  (ne_of_gt hPabs0)
        _ = (n : ℝ) * Real.log (weight muS x) + Real.log |(approxPoly n).eval x| := by
                rw [Real.log_pow]
        _ = (n : ℝ) * logPotential muS (x : ℂ) + Real.log |(approxPoly n).eval x| := by
                rw [hwlog]
    have hlogRHS : Real.log ((n : ℝ) ^ (2 * C1) * rho n x)
        = (2 * C1) * Real.log (n : ℝ) + Real.log (rho n x) := by
      calc
        Real.log ((n : ℝ) ^ (2 * C1) * rho n x)
            = Real.log ((n : ℝ) ^ (2 * C1)) + Real.log (rho n x) :=
                Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hn0R (2 * C1)))
                  (ne_of_gt hrpos)
        _ = (2 * C1) * Real.log (n : ℝ) + Real.log (rho n x) := by
                rw [Real.log_rpow hn0R]
    have hlogineq : Real.log ((weight muS x) ^ n * |(approxPoly n).eval x|)
        ≤ Real.log ((n : ℝ) ^ (2 * C1) * rho n x) := by
      rw [hlogLHS, hlogRHS]
      exact hfin
    have hconv : Real.exp (Real.log ((weight muS x) ^ n * |(approxPoly n).eval x|)) ≤
        Real.exp (Real.log ((n : ℝ) ^ (2 * C1) * rho n x)) := Real.exp_le_exp.mpr hlogineq
    rwa [Real.exp_log hpos1, Real.exp_log hpos2] at hconv


/-- **eq:potential_approx (lower form):** `n^{-C}·ρ_n(x) ≤ w_μ(x)^n·|P_{n,μ}(x)|`
for `x ∈ Σ` (at a root `ρ = 0` and `P = 0`, so the inequality is
`0 ≤ 0`; elsewhere exponentiate the main theorem). -/
theorem potential_approx_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      (n : ℝ) ^ (-C) * rho n x ≤
        (weight muS x) ^ n * |(approxPoly n).eval x| := by
  rcases approx_potential_bound with ⟨C0, hC0pos, hC0⟩
  let C : ℝ := 2 * C0 + 1
  have hCpos : 0 < C := by
    dsimp [C]
    nlinarith
  refine ⟨C, hCpos, ?_⟩
  intro n hn x hx
  have hn1 : 1 ≤ n := by omega
  have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1r : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hC0nn : 0 ≤ C0 := le_of_lt hC0pos
  let B : ℝ := Real.log ((n : ℝ) + 2)
  have hlog2 : B ≤ 2 * Real.log (n : ℝ) := by
    dsimp [B]
    have hsq : (n : ℝ) + 2 ≤ (n : ℝ) * (n : ℝ) := by
      nlinarith [hn2r]
    have hlogsq : Real.log ((n : ℝ) * (n : ℝ)) = 2 * Real.log (n : ℝ) := by
      rw [Real.log_mul (by exact_mod_cast (by omega : (n : ℕ) ≠ 0))
        (by exact_mod_cast (by omega : (n : ℕ) ≠ 0))]
      ring
    calc
      Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) * (n : ℝ)) :=
        Real.log_le_log (by linarith) hsq
      _ = 2 * Real.log (n : ℝ) := hlogsq
  have hlogpos : 0 ≤ Real.log (n : ℝ) := le_of_lt (Real.log_pos hn1r)
  have hlogC : C0 * B ≤ C * Real.log (n : ℝ) := by
    dsimp [C]
    have hC0B : C0 * B ≤ (2 * C0) * Real.log (n : ℝ) := by
      calc
        C0 * B ≤ C0 * (2 * Real.log (n : ℝ)) := mul_le_mul_of_nonneg_left hlog2 hC0nn
        _ = (2 * C0) * Real.log (n : ℝ) := by ring
    calc
      C0 * B ≤ (2 * C0) * Real.log (n : ℝ) := hC0B
      _ ≤ (2 * C0 + 1) * Real.log (n : ℝ) := by nlinarith [hlogpos]
  by_cases hρ0 : rho n x = 0
  · rw [hρ0]
    have hRhs : 0 ≤ (weight muS x) ^ n * |(approxPoly n).eval x| :=
      mul_nonneg (pow_nonneg (le_of_lt (weight_pos muS x)) n) (abs_nonneg _)
    simpa using hRhs
  · have hρpos : 0 < rho n x := lt_of_le_of_ne (rho_nonneg (n := n) x) (Ne.symm hρ0)
    let U : ℝ := logPotential muS (x : ℂ)
    let P : ℝ := (approxPoly n).eval x
    have hPne : P ≠ 0 := by
      dsimp [P]
      exact rho_pos_eval_ne_zero hn1 hρpos
    have hPpos : 0 < |P| := abs_pos.mpr hPne
    have hBnd : |(n : ℝ) * U + Real.log |P| - Real.log (rho n x)| ≤ C0 * B := by
      simpa [U, P, B] using hC0 n hn x hx hρpos
    have hge : -(C0 * B) ≤ (n : ℝ) * U + Real.log |P| - Real.log (rho n x) :=
      (abs_le.mp hBnd).1
    have hlin : Real.log (rho n x) - (n : ℝ) * U - C0 * B ≤ Real.log |P| := by
      nlinarith
    have hexp0 :
        Real.exp (Real.log (rho n x) - (n : ℝ) * U - C0 * B) ≤
          Real.exp (Real.log |P|) :=
      (Real.exp_le_exp).2 hlin
    have hpow_n : 0 < Real.exp ((n : ℝ) * U) := Real.exp_pos _
    have hbase :
        Real.exp ((n : ℝ) * U) *
            Real.exp (Real.log (rho n x) - (n : ℝ) * U - C0 * B) ≤
          Real.exp ((n : ℝ) * U) * Real.exp (Real.log |P|) := by
      exact mul_le_mul_of_nonneg_left hexp0 (le_of_lt hpow_n)
    have hsumL :
        Real.log (rho n x) - C0 * B =
          (n : ℝ) * U + (Real.log (rho n x) - (n : ℝ) * U - C0 * B) := by
      ring
    have hLHS :
        Real.exp (Real.log (rho n x) - C0 * B) =
          Real.exp ((n : ℝ) * U) *
            Real.exp (Real.log (rho n x) - (n : ℝ) * U - C0 * B) := by
      rw [← Real.exp_add, hsumL]
    have hmult :
        Real.exp (Real.log (rho n x) - C0 * B) ≤
          Real.exp ((n : ℝ) * U) * Real.exp (Real.log |P|) := by
      rwa [← hLHS] at hbase
    have hmult2 :
        Real.exp (Real.log (rho n x) - C0 * B) ≤
          Real.exp ((n : ℝ) * U) * |P| := by
      calc
        Real.exp (Real.log (rho n x) - C0 * B) ≤
            Real.exp ((n : ℝ) * U) * Real.exp (Real.log |P|) := hmult
        _ = Real.exp ((n : ℝ) * U) * |P| := by rw [Real.exp_log hPpos]
    have hsplitL : Real.log (rho n x) - C0 * B = Real.log (rho n x) + (-(C0 * B)) := by
      ring
    have hL2 :
        Real.exp (Real.log (rho n x) - C0 * B) =
          rho n x * Real.exp (-(C0 * B)) := by
      rw [hsplitL, Real.exp_add, Real.exp_log hρpos]
    have hprod :
        rho n x * Real.exp (-(C0 * B)) ≤ Real.exp ((n : ℝ) * U) * |P| := by
      rwa [hL2] at hmult2
    have hwU : Real.exp ((n : ℝ) * U) = (weight muS x) ^ n := by
      rw [show weight muS x = Real.exp U by rfl]
      exact Real.exp_nat_mul U n
    have hprod2 : rho n x * Real.exp (-(C0 * B)) ≤ (weight muS x) ^ n * |P| := by
      rwa [hwU] at hprod
    have hcomp : (n : ℝ) ^ (-C) ≤ Real.exp (-(C0 * B)) := by
      have hneg : -(C * Real.log (n : ℝ)) ≤ -(C0 * B) := by
        nlinarith
      have hle_arg : Real.log (n : ℝ) * (-C) ≤ -(C0 * B) := by
        calc
          Real.log (n : ℝ) * (-C) = -(C * Real.log (n : ℝ)) := by ring
          _ ≤ -(C0 * B) := hneg
      rw [Real.rpow_def_of_pos hnpos]
      exact (Real.exp_le_exp).2 hle_arg
    have hmulpow : (n : ℝ) ^ (-C) * rho n x ≤
        Real.exp (-(C0 * B)) * rho n x :=
      mul_le_mul_of_nonneg_right hcomp (rho_nonneg (n := n) x)
    calc
      (n : ℝ) ^ (-C) * rho n x ≤ Real.exp (-(C0 * B)) * rho n x := hmulpow
      _ = rho n x * Real.exp (-(C0 * B)) := by ring
      _ ≤ (weight muS x) ^ n * |(approxPoly n).eval x| := by simpa [P] using hprod2


/-- `n + 2 ≤ n²` for real `n ≥ 2`. -/
lemma np2_le_sq {n : ℕ} (hn : 2 ≤ n) : (n : ℝ) + 2 ≤ (n : ℝ) ^ (2 : ℕ) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hprod : 0 ≤ (n : ℝ) * ((n : ℝ) - 2) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- The interval length `Rserre = bSerre − aSerre` is `≤ n³` for real `n ≥ 2`
(since `Rserre < 8 ≤ n³`). -/
lemma Rserre_le_cube {n : ℕ} (hn : 2 ≤ n) : Rserre ≤ (n : ℝ) ^ (3 : ℕ) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h8 : Rserre ≤ (8 : ℝ) := by
    dsimp [Rserre]
    norm_num [aSerre, bSerre]
  have hpow : (8 : ℝ) ≤ (n : ℝ) ^ (3 : ℕ) := by
    have hn3 : (2 : ℝ) ^ (3 : ℕ) ≤ (n : ℝ) ^ (3 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) hnR 3
    norm_num at hn3 ⊢
    exact hn3
  exact le_trans h8 hpow

/-- **Pointwise weighted-norm upper bound:** for some `C > 0`,
`w_μ(x)^n·|P_{n}(x)| ≤ n^C` for every `n ≥ 2` and `x ∈ [aSerre,bSerre]`
(from `approx_potential_bound`, splitting at the roots where `ρ_n(x) = 0`). -/
lemma ptwise_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      (weight muSerre x) ^ n * |(approxPoly n).eval x| ≤ (n : ℝ) ^ C := by
  rcases potential_approx_upper with ⟨Cu, hCu, hup⟩
  refine ⟨Cu + 3, by nlinarith [hCu], ?_⟩
  intro n hn x hx
  have hn1 : 1 ≤ n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have htarget : (weight muSerre x) ^ n * |(approxPoly n).eval x| ≤ (n : ℝ) ^ Cu * rho n x := by
    change (weight muS x) ^ n * |(approxPoly n).eval x| ≤ (n : ℝ) ^ Cu * rho n x
    exact hup n hn x hx
  have hρle : rho n x ≤ Rserre := rho_le_diam hn1 hx
  have hρnn : 0 ≤ rho n x := rho_nonneg (n := n) x
  have hpowCu : 0 ≤ (n : ℝ) ^ Cu := Real.rpow_nonneg (le_of_lt hnpos) Cu
  have hR : Rserre ≤ (n : ℝ) ^ (3 : ℕ) := Rserre_le_cube hn
  have hstep : (n : ℝ) ^ Cu * rho n x ≤ (n : ℝ) ^ Cu * Rserre :=
    mul_le_mul_of_nonneg_left hρle hpowCu
  have hstep2 : (n : ℝ) ^ Cu * Rserre ≤ (n : ℝ) ^ Cu * (n : ℝ) ^ (3 : ℕ) :=
    mul_le_mul_of_nonneg_left hR hpowCu
  have hstep3 : (n : ℝ) ^ Cu * (n : ℝ) ^ (3 : ℕ) = (n : ℝ) ^ (Cu + 3) := by
    have hn3 : (n : ℝ) ^ (3 : ℕ) = (n : ℝ) ^ ((3 : ℝ)) := (Real.rpow_natCast (n : ℝ) 3).symm
    rw [hn3]
    rw [← Real.rpow_add hnpos Cu (3 : ℝ)]
  calc
    (weight muSerre x) ^ n * |(approxPoly n).eval x| ≤ (n : ℝ) ^ Cu * rho n x := htarget
    _ ≤ (n : ℝ) ^ Cu * Rserre := hstep
    _ ≤ (n : ℝ) ^ Cu * (n : ℝ) ^ (3 : ℕ) := hstep2
    _ = (n : ℝ) ^ (Cu + 3) := hstep3

theorem approx_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      wnorm n (approxPoly n) ≤ (n : ℝ) ^ C := by
  rcases ptwise_bound with ⟨C, hCpos, hpt⟩
  refine ⟨C, hCpos, ?_⟩
  intro n hn
  unfold wnorm
  apply csSup_le
  · -- the defining image set is nonempty (aSerre ∈ [aSerre,bSerre])
    refine ⟨(weight muSerre aSerre) ^ n * |(approxPoly n).eval aSerre|, aSerre, ?_⟩
    exact ⟨⟨le_rfl, a_le_b⟩, rfl⟩
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hpt n hn x hx


end Submission.ThreePages
