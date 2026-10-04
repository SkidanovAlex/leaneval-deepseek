import Mathlib
import Submission.Work.Diff.STE.flat.TowerDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Time differentiation of a matrix-valued Fourier series with a Lipschitz bound

The target theorem `hasDerivWithinAt_seriesFunM` differentiates, at a point `t ∈ [0,τ)`, the
coefficient-determined Fourier series `s ↦ seriesFunM (d s) x` of a family of coefficient
families `d : ℝ → (Fin n → ℤ) → MatC n`, with derivative `seriesFunM d' x`.

The hypotheses are exactly what the limit/Arzelà–Ascoli step of the flat short-time existence
theorem provides at a single time `t`:

* `hdiff` — the entries are Lipschitz in `s` on `[0,τ)` with a *summable* weight `g k` (so that
  the tails of the series are uniformly controlled),
* `hdt` — the entries of `d t` are absolutely summable (so that `seriesFunM (d t)` is a genuine
  absolutely convergent series),
* `hder` — the entries have the within-derivative `d' k a b` at `t` (only at `t`, not on a
  neighbourhood: this is why the Lipschitz bound is needed).

## The proof

Entrywise (`hasDerivWithinAt_seriesFun_core`), the slope of the series is the series of the slopes,

`slope (fun u ↦ ∑' k, c u k · χ_k) t s = ∑' k, slope (fun u ↦ c u k) t s · χ_k`  (`s ≠ t`),

because the tsum splits (`Summable.tsum_sub`, `Summable.tsum_const_smul`).  Each summand tends to
`c' k · χ_k` (`hder`), and the norms of the summands are uniformly bounded by the summable `g`
(`hdiff`, since `‖χ_k‖ = 1`).  Tannery's theorem (`tendsto_tsum_of_dominated_convergence`)
therefore gives the convergence `∑' k, slope (c · k) t s · χ_k → ∑' k, c' k · χ_k`, i.e. the slope
of the series tends to `seriesFun c' x`.  `hasDerivWithinAt_iff_tendsto_slope` turns this into the
statement, and `hasDerivWithinAt_pi` (twice) assembles the matrix statement from the entries.
-/

namespace Work.Diff.STE.flat

open scoped BigOperators Topology
open Filter

set_option maxHeartbeats 1000000

noncomputable section

/-- The Fourier characters `k ↦ exp (2πi k·x)` have unit modulus. -/
lemma norm_fourierExp_char {n : ℕ} (k : Fin n → ℤ) (x : Fin n → ℝ) :
    ‖Work.Diff.STE.fourierExp k x‖ = 1 := by
  rw [Work.Diff.STE.fourierExp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * ∑ i, (k i : ℂ) * (x i : ℂ))
      = (((2 * Real.pi * ∑ i, ((k i : ℤ) : ℝ) * (x i)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- **Term-by-term time differentiation of a ℂ-valued Fourier series.**  This is the entrywise
core of `hasDerivWithinAt_seriesFunM`. -/
lemma hasDerivWithinAt_seriesFun_core {n : ℕ} {τ t : ℝ} (hτ : 0 < τ)
    (ht : t ∈ Set.Ico (0 : ℝ) τ)
    (c : ℝ → (Fin n → ℤ) → ℂ) (c' : (Fin n → ℤ) → ℂ) (x : Fin n → ℝ)
    (g : (Fin n → ℤ) → ℝ) (hg : Summable g) (hg0 : ∀ k, 0 ≤ g k)
    (hdiff : ∀ s ∈ Set.Ico (0 : ℝ) τ, ∀ k, ‖c s k - c t k‖ ≤ |s - t| * g k)
    (hct : Summable (fun k => ‖c t k‖))
    (hder : ∀ k, HasDerivWithinAt (fun s => c s k) (c' k) (Set.Ico (0 : ℝ) τ) t) :
    HasDerivWithinAt (fun s => Work.Diff.STE.seriesFun (c s) x)
      (Work.Diff.STE.seriesFun c' x) (Set.Ico (0 : ℝ) τ) t := by
  set S : Set ℝ := Set.Ico (0 : ℝ) τ with hSdef
  have hchar : ∀ k, ‖Work.Diff.STE.fourierExp k x‖ = 1 := fun k => norm_fourierExp_char k x
  have hcts : Summable (fun k : Fin n → ℤ => c t k) := Summable.of_norm hct
  -- Summability of the coefficient family at every point of `S` (comparison with `t`).
  have hcsum : ∀ s ∈ S, Summable (fun k : Fin n → ℤ => c s k) := by
    intro s hs
    refine Summable.of_norm_bounded (Summable.add hct (Summable.mul_left |s - t| hg))
      (fun k => ?_)
    calc ‖c s k‖ ≤ ‖c t k‖ + ‖c s k - c t k‖ := by
          simpa using norm_add_le (c t k) (c s k - c t k)
      _ ≤ ‖c t k‖ + |s - t| * g k := add_le_add le_rfl (hdiff s hs k)
  -- Multiplying a coefficient family by the (`x`-dependent) Fourier character preserves summability.
  have hmul : ∀ f : (Fin n → ℤ) → ℂ, Summable f →
      Summable (fun k : Fin n → ℤ => f k * Work.Diff.STE.fourierExp k x) := by
    intro f hf
    exact Summable.of_norm (by simpa only [norm_mul, hchar, mul_one] using hf.norm)
  -- The slope of the series is the series of the slopes (for `s ≠ t`), in explicit form.
  have hslope : ∀ s ∈ S \ {t},
      (s - t)⁻¹ • (Work.Diff.STE.seriesFun (c s) x - Work.Diff.STE.seriesFun (c t) x)
        = ∑' k : Fin n → ℤ,
            ((s - t)⁻¹ • (c s k - c t k)) * Work.Diff.STE.fourierExp k x := by
    intro s hs
    have hsums := hmul (fun k => c s k) (hcsum s hs.1)
    have hsumt := hmul (fun k => c t k) hcts
    have hsub : (∑' k : Fin n → ℤ, c s k * Work.Diff.STE.fourierExp k x)
          - (∑' k : Fin n → ℤ, c t k * Work.Diff.STE.fourierExp k x)
        = ∑' k : Fin n → ℤ, (c s k - c t k) * Work.Diff.STE.fourierExp k x := by
      rw [← Summable.tsum_sub hsums hsumt]
      exact tsum_congr (fun k => by ring)
    have hsumd : Summable
        (fun k : Fin n → ℤ => (c s k - c t k) * Work.Diff.STE.fourierExp k x) :=
      hmul (fun k => c s k - c t k) (Summable.sub (hcsum s hs.1) hcts)
    rw [show Work.Diff.STE.seriesFun (c s) x
          = ∑' k : Fin n → ℤ, c s k * Work.Diff.STE.fourierExp k x from rfl,
      show Work.Diff.STE.seriesFun (c t) x
          = ∑' k : Fin n → ℤ, c t k * Work.Diff.STE.fourierExp k x from rfl, hsub]
    rw [← Summable.tsum_const_smul (s - t)⁻¹ hsumd]
    refine tsum_congr (fun k => ?_)
    rw [smul_mul_assoc]
  -- Tannery's theorem: the series of the slopes converges to the series of the derivatives.
  have hlim : Filter.Tendsto
      (fun s => ∑' k : Fin n → ℤ,
          ((s - t)⁻¹ • (c s k - c t k)) * Work.Diff.STE.fourierExp k x)
      (𝓝[S \ {t}] t) (nhds (Work.Diff.STE.seriesFun c' x)) := by
    refine tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[S \ {t}] t)
      (f := fun s k => ((s - t)⁻¹ • (c s k - c t k)) * Work.Diff.STE.fourierExp k x)
      (g := fun k => c' k * Work.Diff.STE.fourierExp k x) (bound := g) hg ?_ ?_
    · intro k
      have h1 : Filter.Tendsto (slope (fun u => c u k) t) (𝓝[S \ {t}] t) (nhds (c' k)) :=
        hasDerivWithinAt_iff_tendsto_slope.mp (hder k)
      simpa only [slope_def_module] using h1.mul_const (Work.Diff.STE.fourierExp k x)
    · rw [eventually_nhdsWithin_iff]
      filter_upwards with s hs k
      have hst : s ≠ t := hs.2
      have habs : 0 < |s - t| := abs_pos.mpr (sub_ne_zero.mpr hst)
      have hb : ‖(s - t)⁻¹ • (c s k - c t k)‖ ≤ g k := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv]
        calc |s - t|⁻¹ * ‖c s k - c t k‖ ≤ |s - t|⁻¹ * (|s - t| * g k) :=
              mul_le_mul_of_nonneg_left (hdiff s hs.1 k) (inv_nonneg.mpr (abs_nonneg _))
          _ = g k := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt habs), one_mul]
      rw [norm_mul, hchar k, mul_one]
      exact hb
  refine hasDerivWithinAt_iff_tendsto_slope.mpr ?_
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [slope_def_module]
  exact (hslope s hs).symm

theorem hasDerivWithinAt_seriesFunM {n : ℕ} {τ t : ℝ} (hτ : 0 < τ) (ht : t ∈ Set.Ico (0 : ℝ) τ)
    (x : Fin n → ℝ)
    (d : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (d' : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (g : (Fin n → ℤ) → ℝ) (hg : Summable g) (hg0 : ∀ k : Fin n → ℤ, 0 ≤ g k)
    (hdiff : ∀ s ∈ Set.Ico (0 : ℝ) τ, ∀ (k : Fin n → ℤ) (a b : Fin n),
      ‖d s k a b - d t k a b‖ ≤ |s - t| * g k)
    (hdt : ∀ a b : Fin n, Summable (fun k : Fin n → ℤ => ‖d t k a b‖))
    (hder : ∀ (k : Fin n → ℤ) (a b : Fin n),
      HasDerivWithinAt (fun s : ℝ => d s k a b) (d' k a b) (Set.Ico (0 : ℝ) τ) t) :
    HasDerivWithinAt (fun s : ℝ => Work.Diff.STE.Flat.seriesFunM (d s) x)
      (Work.Diff.STE.Flat.seriesFunM d' x) (Set.Ico (0 : ℝ) τ) t := by
  refine hasDerivWithinAt_pi.mpr (fun a => hasDerivWithinAt_pi.mpr (fun b => ?_))
  have hcore := hasDerivWithinAt_seriesFun_core (τ := τ) (t := t) (x := x) (g := g)
    (c := fun s k => d s k a b) (c' := fun k => d' k a b) hτ ht hg hg0
    (fun s hs k => hdiff s hs k a b) (hdt a b) (fun k => hder k a b)
  simpa only [Work.Diff.STE.Flat.seriesFunM_apply] using hcore

end

end Work.Diff.STE.flat
