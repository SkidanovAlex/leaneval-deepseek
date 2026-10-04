import Mathlib
import Submission.Work.Diff.STE.B3.BNorm_prelim
import Submission.Work.Diff.STE.contDiff_seriesFun
import Submission.Work.Diff.STE.summable_norm_of_CSq
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `STruncC ρ ε f` is smooth and `1`-periodic

`Work.Diff.STE.STruncC ρ ε f` is the complex lift of the Friedrichs truncation of the
periodisation `per f y = ∑' m, f (y + m)` of a real function `f` supported in the open unit cube,
i.e. the function whose Fourier coefficients are `ρ (ε • m)` times those of `per f`:

`STruncC ρ ε f z = ofReal (re (seriesFun (trunc ρ ε (fourierCoeff (per f))) z))`.

The facts proved here are exactly what the Layer B3 Galerkin scheme needs:

* `per f` is `C^∞` and `1`-periodic (the toolkit lemma `periodization_contDiff_periodic`);
* a smooth periodic torus function has Fourier coefficients decaying faster than every polynomial
  (`summable_weighted_fourierCoeff_of_contDiff`, in its weighted `ℓ²` form), and truncating them by
  a factor `ρ` of modulus `≤ 1` preserves that decay — hence the Fourier series
  `seriesFun (trunc …)` converges `C^∞` (`contDiff_seriesFun`);
* the passage to the real part and back is real-linear and continuous, so preserves smoothness, and
  it preserves `1`-periodicity because `seriesFun c` is a sum of `1`-periodic characters.

The only non-trivial arithmetic is the passage from the weighted `ℓ²` summability
`Σ_k ⟨k⟩^{2s} ‖û(k)‖² < ∞` to the `ℓ¹`-weighted summability `Σ_k ⟨k⟩^N ‖û(k)‖ < ∞` required by
`contDiff_seriesFun`: we apply the AM–GM argument of `summable_norm_of_CSq` to the rescaled family
`k ↦ ⟨k⟩^N û(k)`.
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.B3

/-- **The `ℓ¹`-weighted summability of a coefficient family from its weighted `ℓ²` summability.**

If `Σ_k ⟨k⟩^{2M} ‖c k‖² < ∞` for every `M`, then `Σ_k ⟨k⟩^N ‖c k‖ < ∞` for every `N`.

This is the inclusion `ℓ²(⟨k⟩^{N + card ι + 1}) ⊆ ℓ¹(⟨k⟩^N)`, proved by applying
`summable_norm_of_CSq` to the rescaled family `k ↦ ⟨k⟩^N · c k`. -/
private lemma summable_wt_pow_mul_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : (ι → ℤ) → ℂ) (N : ℕ)
    (h : ∀ M : ℕ, Summable (fun k : ι → ℤ => (wt k) ^ M * ‖c k‖ ^ 2)) :
    Summable (fun k : ι → ℤ => (wt k) ^ N * ‖c k‖) := by
  have hnorm : ∀ k : ι → ℤ, ‖((((wt k) ^ N : ℝ)) : ℂ)‖ = (wt k) ^ N := by
    intro k
    rw [show ‖((((wt k) ^ N : ℝ)) : ℂ)‖ = |(wt k) ^ N| from by simp]
    exact abs_of_nonneg (pow_nonneg (le_of_lt (wt_pos k)) N)
  have hs : Fintype.card ι < 2 * (N + Fintype.card ι + 1) := by omega
  have hpt : ∀ k : ι → ℤ,
      (wt k) ^ (N + Fintype.card ι + 1) * ‖(((wt k) ^ N : ℝ) : ℂ) * c k‖ ^ 2
        = (wt k) ^ (N + Fintype.card ι + 1 + 2 * N) * ‖c k‖ ^ 2 := by
    intro k
    rw [norm_mul, hnorm k, mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
    rw [show N * 2 = 2 * N from by omega]
  have hCSq : Summable (fun k : ι → ℤ =>
      (wt k) ^ (N + Fintype.card ι + 1) * ‖(((wt k) ^ N : ℝ) : ℂ) * c k‖ ^ 2) :=
    (h (N + Fintype.card ι + 1 + 2 * N)).congr (fun k => (hpt k).symm)
  have h1 := summable_norm_of_CSq (N + Fintype.card ι + 1) hs
    (fun k => (((wt k) ^ N : ℝ) : ℂ) * c k) hCSq
  exact h1.congr (fun k => by rw [norm_mul, hnorm k])

/-- Truncation of Fourier coefficients by a factor of modulus `≤ 1` preserves the weighted `ℓ²`
summability: `‖trunc ρ ε c k‖ ≤ ‖c k‖` pointwise and the weight `⟨k⟩^M` is nonnegative. -/
private lemma summable_weighted_trunc {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ) (c : (ι → ℤ) → ℂ)
    (h : ∀ M : ℕ, Summable (fun k : ι → ℤ => (wt k) ^ M * ‖c k‖ ^ 2)) :
    ∀ M : ℕ, Summable (fun k : ι → ℤ => (wt k) ^ M * ‖trunc ρ ε c k‖ ^ 2) := by
  intro M
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (h M)
  · exact mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) M) (sq_nonneg _)
  · have h1 : ‖trunc ρ ε c k‖ ≤ ‖c k‖ := by
      rw [trunc, norm_mul]
      have h2 : ‖((ρ (ε • fun i => (k i : ℝ))) : ℂ)‖ ≤ 1 := by
        simpa using hρ (ε • fun i => (k i : ℝ))
      calc ‖((ρ (ε • fun i => (k i : ℝ))) : ℂ)‖ * ‖c k‖ ≤ 1 * ‖c k‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ = ‖c k‖ := one_mul _
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2)
      (pow_nonneg (le_of_lt (wt_pos k)) M)

/-- **The truncated Fourier series of a smooth periodic function is smooth and `1`-periodic.** -/
private lemma contDiff_periodic_truncSeries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ) (g : (ι → ℝ) → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgp : Periodic1 g) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ι → ℝ => Complex.ofReal
        (Complex.re (seriesFun (trunc ρ ε (fourierCoeff g)) z))) ∧
      Periodic1 (fun z : ι → ℝ => Complex.ofReal
        (Complex.re (seriesFun (trunc ρ ε (fourierCoeff g)) z))) := by
  have hweighted : ∀ M : ℕ, Summable (fun k : ι → ℤ =>
      (wt k) ^ M * ‖trunc ρ ε (fourierCoeff g) k‖ ^ 2) :=
    summable_weighted_trunc ρ hρ ε (fourierCoeff g)
      (summable_weighted_fourierCoeff_of_contDiff g hg hgp)
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (seriesFun (trunc ρ ε (fourierCoeff g))) :=
    contDiff_seriesFun _ (fun N => summable_wt_pow_mul_norm _ N hweighted)
  refine ⟨?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp hcd)
  · intro i x
    change Complex.ofReal (Complex.re (seriesFun (trunc ρ ε (fourierCoeff g))
        (x + Pi.single i 1))) = Complex.ofReal (Complex.re (seriesFun
          (trunc ρ ε (fourierCoeff g)) x))
    rw [flat.periodic1_seriesFun _ i x]

theorem STruncC_contDiff_periodic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfsupp : Function.support f ⊆
      Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.STruncC ρ ε f) ∧
      Work.Diff.STE.Periodic1 (Work.Diff.STE.STruncC ρ ε f) := by
  classical
  have hfC : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => ((f y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hf
  have hsuppC : Function.support (fun y : ι → ℝ => ((f y : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro y hy
    exact hfsupp (by simpa [Function.mem_support] using hy)
  obtain ⟨hg, hgp, -⟩ :=
    periodization_contDiff_periodic (fun y : ι → ℝ => ((f y : ℝ) : ℂ)) hfC hsuppC
  have h := contDiff_periodic_truncSeries ρ hρ ε _ hg hgp
  exact ⟨h.1, h.2⟩

end Work.Diff.STE.B3
