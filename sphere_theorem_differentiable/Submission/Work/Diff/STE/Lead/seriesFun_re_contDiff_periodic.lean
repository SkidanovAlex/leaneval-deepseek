import Mathlib
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.contDiff_seriesFun
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.pd_seriesFun
import Submission.Work.Diff.STE.CSq_comp_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness and periodicity of the real part of a rapidly decaying Fourier series

Let `c : (ι → ℤ) → ℂ` be a coefficient family with a *uniform* rapid decay: for every `M`,
`‖c k‖ * ⟨k⟩^M ≤ C`, with `⟨k⟩² = wt k = 1 + Σ kᵢ²`.  Then `seriesFun c x = ∑'_k c k e^{2πi k·x}`
is `C^∞` on the torus `ι → ℝ` (`Work.Diff.STE.contDiff_seriesFun`), and it is `1`-periodic in
every coordinate (`Work.Diff.STE.periodic_seriesFun`).  Both properties are inherited by the real
part `x ↦ (seriesFun c x).re`.

The target of this file is the packaged form of those two facts for the family
`c = fun μ ↦ g i a b μ t` of the STE development, where the decay hypothesis is stated uniformly
for `t ∈ [0, τ₀)` and for all the finitely many index parameters.

The only work beyond the two cited lemmas is turning the *decay* hypothesis into the *summability*
of every weighted moment `Σ_k ⟨k⟩^N ‖c k‖` (the hypothesis of `contDiff_seriesFun`); this is
`summable_wt_pow_mul_norm_of_decay` below, whose proof uses the multi-dimensional `p`-series
`Work.Diff.STE.summable_wt_zpow`.
-/

namespace Work.Diff.STE.Lead

open Work.Diff.STE

/-- **Summability of the weighted moments from a uniform decay bound.**  If
`‖c k‖ * ⟨k⟩^M ≤ D` for all `k` and `N ≤ M` with `card ι < 2 (M - N)`, then
`Σ_k ⟨k⟩^N ‖c k‖` converges: the decay at order `M` makes `⟨k⟩^N ‖c k‖` dominated by
`D ⟨k⟩^{-(M-N)}`, and the latter is summable by the `p`-series estimate
`Work.Diff.STE.summable_wt_zpow`. -/
private lemma summable_wt_pow_mul_norm_of_decay {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c : (ι → ℤ) → ℂ} {D : ℝ} (N M : ℕ) (hNM : N ≤ M)
    (hcard : Fintype.card ι < 2 * (M - N))
    (h : ∀ k : ι → ℤ, ‖c k‖ * (wt k) ^ M ≤ D) :
    Summable (fun k : ι → ℤ => (wt k) ^ N * ‖c k‖) := by
  -- the majorant `⟨k⟩^{-(M-N)}` is summable
  have hz : Summable (fun k : ι → ℤ => ((wt k) ^ (M - N))⁻¹) := by
    have h' := Work.Diff.STE.summable_wt_zpow (ι := ι) (M - N) hcard
    refine h'.congr (fun k => ?_)
    rw [zpow_neg, zpow_natCast]
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (wt_pos k).le N) (norm_nonneg _)) (fun k => ?_)
    (hz.mul_left D)
  -- `‖c k‖ ≤ D / ⟨k⟩^M`
  have hle : ‖c k‖ ≤ D * ((wt k) ^ M)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (wt_pos k) M)]
    exact h k
  have hpow : (wt k) ^ M = (wt k) ^ N * (wt k) ^ (M - N) := by
    rw [← pow_add]; congr 1; omega
  have hcancel : (wt k) ^ N * ((wt k) ^ M)⁻¹ = ((wt k) ^ (M - N))⁻¹ := by
    rw [hpow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero N (ne_of_gt (wt_pos k))),
      one_mul]
  calc (wt k) ^ N * ‖c k‖
      ≤ (wt k) ^ N * (D * ((wt k) ^ M)⁻¹) :=
        mul_le_mul_of_nonneg_left hle (pow_nonneg (wt_pos k).le N)
    _ = D * ((wt k) ^ N * ((wt k) ^ M)⁻¹) := by ring
    _ = D * ((wt k) ^ (M - N))⁻¹ := by rw [hcancel]

theorem seriesFun_re_contDiff_periodic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀]
    (τ₀ : ℝ)
    (g : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℤ) → ℝ → ℂ)
    (hdec : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ) (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ₀ →
        ‖g i a b μ t‖ * (Work.Diff.STE.wt μ) ^ M ≤ C)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    ∀ t ∈ Set.Ico (0 : ℝ) τ₀,
      ContDiff ℝ (⊤ : ℕ∞)
          (fun z => (Work.Diff.STE.seriesFun (fun μ => g i a b μ t) z).re) ∧
        Work.Diff.STE.Periodic1
          (fun z => (Work.Diff.STE.seriesFun (fun μ => g i a b μ t) z).re) := by
  intro t ht
  set c : (Fin (Module.finrank ℝ E) → ℤ) → ℂ := fun μ => g i a b μ t with hc
  -- all weighted moments of the coefficient family are summable, at every order
  have hmom : ∀ N : ℕ, Summable (fun k : Fin (Module.finrank ℝ E) → ℤ =>
      (Work.Diff.STE.wt k) ^ N * ‖c k‖) := by
    intro N
    obtain ⟨D, _hD0, hDb⟩ := hdec (N + (Module.finrank ℝ E + 1))
    exact summable_wt_pow_mul_norm_of_decay (c := c) (D := D) N
      (N + (Module.finrank ℝ E + 1)) (by omega)
      (by simp only [Fintype.card_fin]; omega) (fun k => hDb i a b k t ht)
  constructor
  · -- smoothness of the series, and of its real part
    have hcont : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.seriesFun c) :=
      Work.Diff.STE.contDiff_seriesFun c hmom
    have h := Complex.reCLM.contDiff.comp hcont
    simpa only [Function.comp_def, Complex.reCLM_apply] using h
  · -- periodicity of the series, and of its real part
    have hper := Work.Diff.STE.periodic_seriesFun c
    intro j x
    exact congrArg Complex.re (hper j x)

end Work.Diff.STE.Lead
