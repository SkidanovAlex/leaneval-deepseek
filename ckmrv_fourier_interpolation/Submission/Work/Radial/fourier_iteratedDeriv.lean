import Mathlib

namespace Work.Radial

open scoped ContDiff FourierTransform
open MeasureTheory

/-- **Fourier inversion for the `m`-th derivative.**  If `h : ℝ → ℂ` is smooth with compact
support then its `m`-th iterated derivative is recovered from its Fourier transform by the
inverse Fourier integral

`iteratedDeriv m h t = ∫ u, (2 * π * I * u) ^ m * (𝓕 h) u * Complex.exp (2 * π * I * u * t)`.

The proof combines `Real.fourier_iteratedDeriv` (the Fourier transform of the `m`-th
derivative is `(2πI x)^m` times the Fourier transform) with Fourier inversion for a
continuous integrable function whose Fourier transform is integrable; compact support and
smoothness of `h` exhibit all the relevant functions as Schwartz functions. -/
theorem fourier_iteratedDeriv {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    (hsupp : ∃ R : ℝ, ∀ t : ℝ, R ≤ |t| → h t = 0) (m : ℕ) (t : ℝ) :
    iteratedDeriv m h t = ∫ u : ℝ, (2 * ↑Real.pi * Complex.I * ↑u) ^ m * (𝓕 h) u *
      Complex.exp (2 * ↑Real.pi * Complex.I * ↑u * ↑t) := by
  -- `h` has compact support, hence (being smooth) is a Schwartz function.
  obtain ⟨R, hR⟩ := hsupp
  have hcs : HasCompactSupport h := by
    apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-R) R) isCompact_Icc
    intro x hx
    simp only [Function.mem_support] at hx
    rw [Set.mem_Icc, ← abs_le]
    by_contra hcon
    exact hx (hR x (le_of_lt (lt_of_not_ge hcon)))
  let hS : SchwartzMap ℝ ℂ := hcs.toSchwartzMap hh
  have hS_coe : ⇑hS = h := funext fun a => HasCompactSupport.toSchwartzMap_toFun hcs hh a
  -- All iterated derivatives of `h` are Schwartz functions.
  have g_coe : ∀ n : ℕ, ⇑((SchwartzMap.derivCLM ℂ ℂ)^[n] hS) = deriv^[n] h := by
    intro n
    induction n with
    | zero => simpa using hS_coe
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      funext x
      rw [SchwartzMap.derivCLM_apply, ih]
  have hint : ∀ n : ℕ, Integrable (iteratedDeriv n h) := by
    intro n
    rw [iteratedDeriv_eq_iterate, ← g_coe n]
    exact SchwartzMap.integrable _
  -- Fourier transform of the `m`-th derivative.
  have hF := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) (f := h) (n := m) hh
    (fun n _ => hint n) le_top
  have hcont : Continuous (iteratedDeriv m h) := by
    rw [iteratedDeriv_eq_iterate, ← g_coe m]
    exact SchwartzMap.continuous _
  -- The Fourier transform of the `m`-th derivative is integrable (it is Schwartz).
  have hFint : Integrable (𝓕 (iteratedDeriv m h)) := by
    have key := SchwartzMap.fourier_coe ((SchwartzMap.derivCLM ℂ ℂ)^[m] hS)
    have heq : 𝓕 (iteratedDeriv m h) = 𝓕 ⇑((SchwartzMap.derivCLM ℂ ℂ)^[m] hS) := by
      rw [g_coe m, iteratedDeriv_eq_iterate]
    rw [heq, ← key]
    exact (𝓕 ((SchwartzMap.derivCLM ℂ ℂ)^[m] hS) : SchwartzMap ℝ ℂ).integrable
  -- Fourier inversion.
  have hinv := Continuous.fourierInv_fourier_eq hcont (hint m) hFint
  rw [← congrFun hinv t]
  rw [Real.fourierInv_eq']
  simp only [hF]
  apply integral_congr_ae
  filter_upwards with v
  rw [Real.inner_apply]
  rw [smul_eq_mul, smul_eq_mul]
  have hexp : Complex.exp (↑(2 * Real.pi * (v * t)) * Complex.I) =
      Complex.exp (2 * ↑Real.pi * Complex.I * ↑v * ↑t) := by
    congr 1
    push_cast
    ring
  rw [hexp]
  exact mul_comm _ _

end Work.Radial
