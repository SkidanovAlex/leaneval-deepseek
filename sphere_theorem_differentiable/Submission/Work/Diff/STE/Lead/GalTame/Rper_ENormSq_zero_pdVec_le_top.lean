import Mathlib
import Submission.Work.Diff.STE.Lead.GalTame.Defs
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.CSq_le_ENormSq
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.Lead.Rper_contDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Interpolation of the Fourier energy: `ENormSq 0 (∂^β f) ≤ C (ENormSq k f + ENormSq 0 f)`

The tame (L²) transport data of the DeTurck operator (`GalTame/Defs.lean`) needs a bound on the
`L²` norm of a *single* `m`-th order derivative `∂^β f` (`m ≤ k`) of a periodic component `f` by
the level-`k` energy `ENormSq k f` plus the `L²` energy `ENormSq 0 f`:

  `ENormSq 0 (pdVec m β f) ≤ C (ENormSq k f + ENormSq 0 f)`,   `m ≤ k`,

with a constant `C` depending only on `k` and the dimension `ι` — in particular *uniform in `f`*,
which is essential because the target quantifies over all sections `h` (and all charts, frames and
component indices).

## Route (Fourier, with no loss)

Everything happens on the Fourier side, where both sides are explicit:

* `ENormSq 0 g = ∫_{unitCube} ‖g‖²` (`ENormSq_zero`), and for a smooth `1`-periodic `f` the
  Fourier series reproduces `f` (`flat.seriesFun_fourierCoeff`), so term by term differentiation
  (`pdList_seriesFun`) turns the derivative into the multiplier family
  `dmulV (List.ofFn β) (fourierCoeff f)`, whose `L²` norm is the `ℓ²` norm of its coefficients
  (`ens_integral_normSq_seriesFun`, i.e. Parseval for a series).
* Termwise, `‖dmulV (List.ofFn β) c μ‖² ≤ ((2π)² ⟨μ⟩)^{m} ‖c μ‖²` (`norm_sq_dmulV_le`), and
  `((2π)² ⟨μ⟩)^m ≤ ((2π)² ⟨μ⟩)^k = (2π)^{2k} ⟨μ⟩^k` because `m ≤ k` and `(2π)² ⟨μ⟩ ≥ 1`.
  Summing gives `ENormSq 0 (pdVec m β f) ≤ (2π)^{2k} · CSq k (fourierCoeff f)`.
* The Sobolev comparison `CSq_le_ENormSq` bounds the weighted `ℓ²` norm of the coefficients by
  `C (ENormSq k f + ENormSq 0 f)`.

The only technical input is that a smooth `1`-periodic function has Fourier coefficients decaying
faster than every polynomial weight from below (`fourierCoeff_moment_summable`, derived from
`summable_weighted_fourierCoeff_of_contDiff` by the Cauchy–Schwarz/weight-splitting argument
`summable_norm_of_CSq`).

## Application

Instantiating at `f = D.Rper i h a b` for Layer B3 data `D` and a section `h` with smooth chart
data (`Lead.Rper_contDiff_and_periodic`) gives the target
`Work.Diff.STE.Lead.GalTame.Rper_ENormSq_zero_pdVec_le_top` with the *same* constant for every
section, chart, frame index and multi-index — no compactness or uniformity argument is needed,
because the Fourier bound is universal.
-/

namespace Work.Diff.STE.Lead.GalTame

open MeasureTheory BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Rapid decay of the Fourier coefficients of a smooth periodic function.**  For a `C^∞`,
`1`-periodic `f` and every `N`, the weighted `ℓ¹`-moment `Σ_μ ⟨μ⟩^N ‖û(μ)‖` is finite.

Route: `Σ_μ ⟨μ⟩^N ‖û(μ)‖` is the `ℓ¹`-norm of the coefficients of the family
`μ ↦ ⟨μ⟩^N û(μ)`, and `Work.Diff.STE.summable_norm_of_CSq` converts the weighted `ℓ²`-bound of
that family at a level `K > card ι / 2` — which is `Σ_μ ⟨μ⟩^{K+2N} ‖û(μ)‖²`, summable by
`summable_weighted_fourierCoeff_of_contDiff` — into its summability. -/
lemma fourierCoeff_moment_summable
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Work.Diff.STE.Periodic1 f) :
    ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖Work.Diff.STE.fourierCoeff f k‖) := by
  intro N
  obtain ⟨K, hK⟩ : ∃ K : ℕ, Fintype.card ι < 2 * K := ⟨Fintype.card ι + 1, by omega⟩
  have h2 : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ K *
      ‖(fun k : ι → ℤ => (((Work.Diff.STE.wt k) ^ N : ℝ) : ℂ)
        * Work.Diff.STE.fourierCoeff f k) k‖ ^ 2) := by
    refine (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff f hf hper (K + 2 * N)).congr
      (fun k => ?_)
    have hw : (0 : ℝ) ≤ Work.Diff.STE.wt k ^ N :=
      pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) N
    rw [norm_mul, Complex.norm_of_nonneg hw, mul_pow, ← pow_mul, Nat.mul_comm N 2, pow_add]
    ring
  have h3 := Work.Diff.STE.summable_norm_of_CSq (ι := ι) K hK
    (fun k : ι → ℤ => (((Work.Diff.STE.wt k) ^ N : ℝ) : ℂ) * Work.Diff.STE.fourierCoeff f k) h2
  exact h3.congr (fun k => by
    rw [norm_mul, Complex.norm_of_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) N)])

/-- **Interpolation of a single derivative between the `L²` and `Hᵏ` energies on the torus.**
There is a constant `C` (depending only on `k` and `ι`) such that for every `C^∞`, `1`-periodic
`f`, every `m ≤ k` and every multi-index `β : Fin m → ι`,

  `ENormSq 0 (pdVec m β f) ≤ C (ENormSq k f + ENormSq 0 f)`.

In particular the constant is **uniform in `f`**; this is the property that the target
(`Rper_ENormSq_zero_pdVec_le_top`) needs in order to quantify over arbitrary sections. -/
lemma ENormSq_zero_pdVec_le_smooth (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (_hm : m ≤ k) (β : Fin m → ι) (f : (ι → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) f → Work.Diff.STE.Periodic1 f →
      Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β f)
        ≤ C * (Work.Diff.STE.ENormSq k f + Work.Diff.STE.ENormSq 0 f) := by
  classical
  obtain ⟨Cc, hCc, hCSq⟩ := Work.Diff.STE.CSq_le_ENormSq (ι := ι) k
  refine ⟨(2 * Real.pi) ^ (2 * k) * Cc, mul_nonneg (pow_nonneg (by positivity) _) hCc, ?_⟩
  intro m hm β f hf hper
  have hdecay : ∀ N : ℕ, Summable (fun k' : ι → ℤ =>
      (Work.Diff.STE.wt k') ^ N * ‖Work.Diff.STE.fourierCoeff f k'‖) :=
    fourierCoeff_moment_summable f hf hper
  have hfser : f = Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff f) :=
    funext (fun x => (Work.Diff.STE.flat.seriesFun_fourierCoeff f hf hper x).symm)
  have hpd : Work.Diff.STE.pdVec m β f
      = Work.Diff.STE.seriesFun
          (Work.Diff.STE.dmulV (List.ofFn β) (Work.Diff.STE.fourierCoeff f)) := by
    conv_lhs => rw [hfser]
    exact funext (Work.Diff.STE.pdList_seriesFun (List.ofFn β)
      (Work.Diff.STE.fourierCoeff f) hdecay)
  have hsumm : Summable (fun k' : ι → ℤ =>
      ‖Work.Diff.STE.dmulV (List.ofFn β) (Work.Diff.STE.fourierCoeff f) k'‖) := by
    simpa using Work.Diff.STE.summable_dmulV (List.ofFn β) (Work.Diff.STE.fourierCoeff f) hdecay 0
  have hsq : Summable (fun k' : ι → ℤ =>
      ‖Work.Diff.STE.dmulV (List.ofFn β) (Work.Diff.STE.fourierCoeff f) k'‖ ^ 2) :=
    Work.Diff.STE.summable_sq_of_nonneg hsumm (fun _ => norm_nonneg _)
  have hbd : Summable (fun k' : ι → ℤ => (2 * Real.pi) ^ (2 * k) *
      ((Work.Diff.STE.wt k') ^ k * ‖Work.Diff.STE.fourierCoeff f k'‖ ^ 2)) :=
    (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff f hf hper k).mul_left _
  have hkey : (∑' k' : ι → ℤ,
        ‖Work.Diff.STE.dmulV (List.ofFn β) (Work.Diff.STE.fourierCoeff f) k'‖ ^ 2)
      ≤ (2 * Real.pi) ^ (2 * k) * Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff f) := by
    rw [Work.Diff.STE.CSq, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun k' => ?_) hsq hbd
    have hbase : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 * Work.Diff.STE.wt k' := by
      have h1 : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
      have h2 : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 := by positivity
      have h3 : (0 : ℝ) ≤ Work.Diff.STE.wt k' := le_of_lt (Work.Diff.STE.wt_pos k')
      nlinarith [Work.Diff.STE.wt_one_le k']
    calc ‖Work.Diff.STE.dmulV (List.ofFn β) (Work.Diff.STE.fourierCoeff f) k'‖ ^ 2
        ≤ ((2 * Real.pi) ^ 2 * Work.Diff.STE.wt k') ^ (List.ofFn β).length
            * ‖Work.Diff.STE.fourierCoeff f k'‖ ^ 2 :=
          Work.Diff.STE.norm_sq_dmulV_le _ _ _
      _ = ((2 * Real.pi) ^ 2 * Work.Diff.STE.wt k') ^ m
            * ‖Work.Diff.STE.fourierCoeff f k'‖ ^ 2 := by
          rw [List.length_ofFn]
      _ ≤ ((2 * Real.pi) ^ 2 * Work.Diff.STE.wt k') ^ k
            * ‖Work.Diff.STE.fourierCoeff f k'‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hbase hm) (sq_nonneg _)
      _ = (2 * Real.pi) ^ (2 * k)
            * (Work.Diff.STE.wt k' ^ k * ‖Work.Diff.STE.fourierCoeff f k'‖ ^ 2) := by
          rw [mul_pow, ← pow_mul]; ring
  have hcont : ContDiff ℝ (↑k) f := hf.of_le (by exact_mod_cast le_top)
  have hCcf := hCSq f hcont hper
  have hEnorm : Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β f)
      = ∑' k' : ι → ℤ,
          ‖Work.Diff.STE.dmulV (List.ofFn β) (Work.Diff.STE.fourierCoeff f) k'‖ ^ 2 := by
    rw [Work.Diff.STE.ENormSq_zero, hpd,
      Work.Diff.STE.ens_integral_normSq_seriesFun _ hsumm]
  calc Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β f)
      = ∑' k' : ι → ℤ,
          ‖Work.Diff.STE.dmulV (List.ofFn β) (Work.Diff.STE.fourierCoeff f) k'‖ ^ 2 := hEnorm
    _ ≤ (2 * Real.pi) ^ (2 * k) * Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff f) := hkey
    _ ≤ (2 * Real.pi) ^ (2 * k)
          * (Cc * (Work.Diff.STE.ENormSq k f + Work.Diff.STE.ENormSq 0 f)) :=
        mul_le_mul_of_nonneg_left hCcf (by positivity)
    _ = ((2 * Real.pi) ^ (2 * k) * Cc)
          * (Work.Diff.STE.ENormSq k f + Work.Diff.STE.ENormSq 0 f) := by
        ring

end

theorem Rper_ENormSq_zero_pdVec_le_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (m : ℕ) (hm : m ≤ k)
        (β : Fin m → Fin (Module.finrank ℝ E)),
        Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β (D.Rper i h a b))
          ≤ C * (Work.Diff.STE.ENormSq k (D.Rper i h a b)
                  + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)) := by
  classical
  obtain ⟨C, hC0, hC⟩ :=
    ENormSq_zero_pdVec_le_smooth (ι := Fin (Module.finrank ℝ E)) k
  refine ⟨C, hC0, ?_⟩
  intro h hsmooth i a b m hm β
  obtain ⟨hsm, hper⟩ :=
    Work.Diff.STE.Lead.Rper_contDiff_and_periodic D h hsmooth i a b
  exact hC m hm β (D.Rper i h a b) hsm hper

end Work.Diff.STE.Lead.GalTame
