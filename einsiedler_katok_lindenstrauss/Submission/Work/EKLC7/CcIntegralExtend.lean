import Mathlib
import Submission.Work.EKLC7.lintegral_ofReal_lt_top_of_integrable
import Submission.Work.EKLC7.toReal_iSup_eq_of_approx

/-!
# C7: extending the equality of integrals from `C_c` to bounded continuous functions

If two measures `μ`, `ν` on a topological space `X` (with `ν` finite on compacts) give the
same value to `∫ f dμ` and `∫ f dν` for every compactly supported continuous `f`, and if
`φ n` is an increasing sequence of compactly supported continuous functions `0 ≤ φ n ≤ 1`
which is eventually equal to `1` at every point, then for every bounded continuous `g` the
(non-negative part) integrals of `g` against `μ` and `ν` agree:

`(∫⁻ x, ENNReal.ofReal (g x) ∂μ).toReal = (∫⁻ x, ENNReal.ofReal (g x) ∂ν).toReal`.

The proof writes `g⁺ = max g 0`, observes that `ψ n := φ n · g⁺` is compactly supported and
continuous with `ψ n ⟶ g⁺` pointwise, so that by two applications of monotone convergence

`∫⁻ ENNReal.ofReal (g⁺) ∂μ = ⨆ n, ∫⁻ ENNReal.ofReal (ψ n) ∂μ` (and the same for `ν`),

and the hypothesis gives `∫ ψ n ∂μ = ∫ ψ n ∂ν` for every `n`.  For `ν` the functions `ψ n`
are integrable (compact support, `ν` finite on compacts), so
`∫⁻ ENNReal.ofReal (ψ n) ∂ν = ENNReal.ofReal (∫ ψ n ∂ν)` is finite; for `μ` the lintegral is
either finite — hence equal to `ENNReal.ofReal (∫ ψ n ∂μ)`, which is the `ν` value — or it is
`⊤`, in which case the real integral `∫ ψ n ∂μ` (which equals `∫ ψ n ∂ν`) vanishes.  The
arithmetic bookkeeping relating the two suprema is `toReal_iSup_eq_of_approx`.
-/

namespace Work.EKLC7

open MeasureTheory
open scoped ENNReal

theorem CcIntegralExtend {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (μ ν : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasureOnCompacts ν] (φ : ℕ → CompactlySupportedContinuousMap X ℝ) (hφ0 : ∀ n x, 0 ≤ φ n x) (hφ1 : ∀ n x, φ n x ≤ 1) (hφmono : ∀ n m, n ≤ m → ∀ x, φ n x ≤ φ m x) (hφtop : ∀ x, ∃ N, ∀ n, N ≤ n → φ n x = 1) (h : ∀ f : CompactlySupportedContinuousMap X ℝ, ∫ x, (f : X → ℝ) x ∂μ = ∫ x, (f : X → ℝ) x ∂ν) : ∀ g : X → ℝ, Continuous g → (∃ C : ℝ, ∀ x, |g x| ≤ C) → (∫⁻ x, ENNReal.ofReal (g x) ∂μ).toReal = (∫⁻ x, ENNReal.ofReal (g x) ∂ν).toReal := by
  intro g hg _
  -- the positive part of `g`, whose `ENNReal.ofReal` is that of `g`
  let gp : X → ℝ := fun x => max (g x) 0
  have hgpc : Continuous gp := hg.max continuous_const
  have hgp0 : ∀ x, 0 ≤ gp x := fun x => le_max_right _ _
  have hofReal : ∀ x, ENNReal.ofReal (g x) = ENNReal.ofReal (gp x) := by
    intro x; simp [gp]
  -- the compactly supported approximations `ψ n = φ n · g⁺`
  let ψ : ℕ → CompactlySupportedContinuousMap X ℝ := fun n => (⟨gp, hgpc⟩ : C(X, ℝ)) • φ n
  have hψapply : ∀ n x, ψ n x = gp x * φ n x := by
    intro n x
    show ((⟨gp, hgpc⟩ : C(X, ℝ)) • φ n) x = gp x * φ n x
    rw [CompactlySupportedContinuousMap.smulc_apply, smul_eq_mul]
    rfl
  have hψ0 : ∀ n x, 0 ≤ ψ n x := fun n x => by
    rw [hψapply n x]; exact mul_nonneg (hgp0 x) (hφ0 n x)
  have hψle : ∀ n x, ψ n x ≤ gp x := fun n x => by
    rw [hψapply n x]
    simpa using mul_le_mul_of_nonneg_left (hφ1 n x) (hgp0 x)
  have hψmono : ∀ n m, n ≤ m → ∀ x, ψ n x ≤ ψ m x := fun n m hnm x => by
    rw [hψapply n x, hψapply m x]
    exact mul_le_mul_of_nonneg_left (hφmono n m hnm x) (hgp0 x)
  have hψev : ∀ x, ∃ N, ∀ n, N ≤ n → ψ n x = gp x := fun x => by
    obtain ⟨N, hN⟩ := hφtop x
    exact ⟨N, fun n hn => by rw [hψapply n x, hN n hn, mul_one]⟩
  -- the hypothesis `h` at the test functions `ψ n`
  have hInt : ∀ n, ∫ x, ψ n x ∂μ = ∫ x, ψ n x ∂ν := fun n => h (ψ n)
  have hAtoReal : ∀ n, ∫ x, ψ n x ∂μ
      = (∫⁻ x, ENNReal.ofReal (ψ n x) ∂μ).toReal := fun n =>
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (hψ0 n))
      ((ψ n).continuous.aestronglyMeasurable)
  -- on the `ν` side the `ψ n` are integrable, so the lintegral is finite and equal to
  -- `ENNReal.ofReal` of the integral
  have hD2 : ∀ n, (∫⁻ x, ENNReal.ofReal (ψ n x) ∂ν) < ⊤ ∧
      (∫⁻ x, ENNReal.ofReal (ψ n x) ∂ν) = ENNReal.ofReal (∫ x, ψ n x ∂ν) :=
    fun n => lintegral_ofReal_lt_top_of_integrable ν (ψ n) (hψ0 n)
  have hBtop : ∀ n, (∫⁻ x, ENNReal.ofReal (ψ n x) ∂ν) ≠ ⊤ := fun n => ne_of_lt (hD2 n).1
  -- the dichotomy for the two lintegrals of `ψ n`
  have hAB : ∀ n, (∫⁻ x, ENNReal.ofReal (ψ n x) ∂μ) = (∫⁻ x, ENNReal.ofReal (ψ n x) ∂ν) ∨
      ((∫⁻ x, ENNReal.ofReal (ψ n x) ∂μ) = ⊤ ∧ (∫⁻ x, ENNReal.ofReal (ψ n x) ∂ν) = 0) := by
    intro n
    by_cases htop : (∫⁻ x, ENNReal.ofReal (ψ n x) ∂μ) = ⊤
    · right
      refine ⟨htop, ?_⟩
      have hc0 : ∫ x, ψ n x ∂μ = 0 := by rw [hAtoReal n, htop, ENNReal.toReal_top]
      rw [(hD2 n).2, ← hInt n, hc0, ENNReal.ofReal_zero]
    · left
      have hAeq : (∫⁻ x, ENNReal.ofReal (ψ n x) ∂μ)
          = ENNReal.ofReal (∫ x, ψ n x ∂μ) := by
        rw [hAtoReal n, ENNReal.ofReal_toReal htop]
      rw [hAeq, (hD2 n).2, hInt n]
  -- monotone convergence
  have hmeas : ∀ n, Measurable (fun x => ENNReal.ofReal (ψ n x)) :=
    fun n => ((ψ n).continuous.measurable).ennreal_ofReal
  have hFmono : Monotone (fun n : ℕ => fun x => ENNReal.ofReal (ψ n x)) :=
    fun n m hnm x => ENNReal.ofReal_le_ofReal (hψmono n m hnm x)
  have hsup : (fun x => ENNReal.ofReal (gp x)) = fun x => ⨆ n, ENNReal.ofReal (ψ n x) := by
    funext x
    refine le_antisymm ?_ ?_
    · obtain ⟨N, hN⟩ := hψev x
      rw [← hN N le_rfl]
      exact le_iSup (fun n => ENNReal.ofReal (ψ n x)) N
    · refine iSup_le fun n => ENNReal.ofReal_le_ofReal (hψle n x)
  have hmonoA : Monotone (fun n => ∫⁻ x, ENNReal.ofReal (ψ n x) ∂μ) :=
    fun n m hnm => lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hψmono n m hnm x))
  have hmonoB : Monotone (fun n => ∫⁻ x, ENNReal.ofReal (ψ n x) ∂ν) :=
    fun n m hnm => lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hψmono n m hnm x))
  have hLμ : ∫⁻ x, ENNReal.ofReal (gp x) ∂μ
      = ⨆ n, ∫⁻ x, ENNReal.ofReal (ψ n x) ∂μ := by
    rw [hsup, MeasureTheory.lintegral_iSup hmeas hFmono]
  have hLν : ∫⁻ x, ENNReal.ofReal (gp x) ∂ν
      = ⨆ n, ∫⁻ x, ENNReal.ofReal (ψ n x) ∂ν := by
    rw [hsup, MeasureTheory.lintegral_iSup hmeas hFmono]
  calc (∫⁻ x, ENNReal.ofReal (g x) ∂μ).toReal
      = (∫⁻ x, ENNReal.ofReal (gp x) ∂μ).toReal := by rw [lintegral_congr hofReal]
    _ = (⨆ n, ∫⁻ x, ENNReal.ofReal (ψ n x) ∂μ).toReal := by rw [hLμ]
    _ = (⨆ n, ∫⁻ x, ENNReal.ofReal (ψ n x) ∂ν).toReal :=
        toReal_iSup_eq_of_approx hBtop hmonoA hmonoB hAB
    _ = (∫⁻ x, ENNReal.ofReal (gp x) ∂ν).toReal := by rw [hLν]
    _ = (∫⁻ x, ENNReal.ofReal (g x) ∂ν).toReal := by rw [lintegral_congr hofReal]

end Work.EKLC7
