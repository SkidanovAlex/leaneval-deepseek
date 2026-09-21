import Mathlib
import Submission.Work.OddRadon.Abel
import Submission.Work.OddRadon.abelReduceIter_abelTrans
import Submission.Work.OddRadon.abel_integral_trig_substitution
import Submission.Work.OddRadon.abelReduceIter_contDiff_eqOn
import Submission.Work.Analysis.Calculus.contDiff_intervalIntegral_fixed
import Submission.Commons.Geometry.Ulam.even_profile_perturbation_from_smooth_bump_aux_independent_core

/-!
# Smoothness of the odd-dimensional Radon inverse

The inverse `radonInverse n F` of the one-variable `(2n+1)`-dimensional spherical Radon
transform, applied to a datum `F` which is smooth on `[0,1]`, is smooth on `(0,1).

The proof is in three steps, all of which are formalised below for a fixed order `M`:

* the datum `c ↦ (2 |S^{2n-2}|)⁻¹ c^{2n-2} F c` is extended to a globally `C^K` function
  (`taylorExtend`), which agrees with it on `(0,1)`;
* the `(n-1)`-fold exponent reduction `abelReduceIter` turns that global `C^K` function into a
  `C^{K-(n-1)}` function `Θ` agreeing with the reduced datum on `(0,1)` (the divisions by `c`
  are harmless because the datum vanishes to order `2n-2` at `0`);
* the singular Abel integral `∫_0^u c Φ c /√(u²-c²) dc` is rewritten, by the change of
  variables `c = u sin θ`, as the smooth trigonometric integral `∫_0^{π/2} u sin θ Φ(u sin θ)`,
  in which `Φ` may be replaced by `Θ`.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace Pointwise Interval Topology ContDiff

namespace Work.OddRadon

/-- The Abel datum of a one-variable profile `F`: `c ↦ (2 |S^{2n-2}|)⁻¹ c^{2n-2} F c`,
the function whose `(n-1)`-fold exponent reduction is the integrand of `radonInverse n F`. -/
def abelDatum (n : ℕ) (F : ℝ → ℝ) : ℝ → ℝ :=
  fun c => (2 * sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) * F c

lemma radonInverse_eq (n : ℕ) (F : ℝ → ℝ) (u : ℝ) :
    radonInverse n F u = (2 / Real.pi) * deriv (fun v : ℝ => ∫ c in (0:ℝ)..v,
      c * abelReduceIter ((n : ℝ) - 3 / 2) (n - 1) (abelDatum n F) c
        / Real.sqrt (v ^ 2 - c ^ 2)) u := rfl

theorem contDiffOn_radonInverse (n : ℕ) (hn : 1 ≤ n) {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) F (Set.Icc 0 1)) :
    ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (radonInverse n F) (Set.Ioo 0 1) := by
  rw [contDiffOn_infty]
  intro M
  -- choose a large extension order
  obtain ⟨K, hK⟩ : ∃ K : ℕ, M + 1 + (n - 1) ≤ K := ⟨M + 1 + (n - 1), le_rfl⟩
  have hKle : M + 1 ≤ K - (n - 1) := by omega
  have hFK : ContDiffOn ℝ K F (Set.Icc (0:ℝ) 1) :=
    hF.of_le (by exact_mod_cast (le_top : (K : ℕ∞) ≤ (⊤ : ℕ∞)))
  -- a global `C^K` extension of `F` which agrees with it on `[0,1]`
  set G : ℝ → ℝ := Commons.Analysis.Calculus.taylorExtend F K 0 1 with hG
  have hGsm : ContDiff ℝ K G := by
    rw [hG]
    exact Commons.Analysis.Calculus.contDiff_taylorExtend K (by norm_num) hFK
  have hGeq : Set.EqOn G F (Set.Icc (0:ℝ) 1) := by
    rw [hG]
    exact Commons.Analysis.Calculus.taylorExtend_eqOn_Icc
  -- the datum, its extension, and the reduced integrand
  set Ψ : ℝ → ℝ := abelDatum n F with hΨ
  set ΨG : ℝ → ℝ := abelDatum n G with hΨG
  have hΨeq : Set.EqOn Ψ ΨG (Set.Ioo (0:ℝ) 1) := by
    intro c hc
    simp only [hΨ, hΨG, abelDatum]
    rw [hGeq ⟨hc.1.le, hc.2.le⟩]
  have hg_sm : ContDiff ℝ K ΨG := by
    rw [hΨG]
    unfold abelDatum
    fun_prop
  have hh_sm : ContDiff ℝ K (fun c => (2 * sphereArea (2 * n - 2))⁻¹ * G c) :=
    contDiff_const.mul hGsm
  have hgm : ∀ c, ΨG c = c ^ (2 * n - 2) * ((2 * sphereArea (2 * n - 2))⁻¹ * G c) := by
    intro c
    rw [hΨG]
    simp only [abelDatum]
    ring
  have h2k : 2 * (n - 1) ≤ 2 * n - 2 := by omega
  have hkN : n - 1 ≤ K := by omega
  obtain ⟨Θ, h', hΘsm, hh'sm, hΘdiv, hΘeq⟩ :=
    abelReduceIter_contDiff_eqOn ((n : ℝ) - 3 / 2) (n - 1) hg_sm hh_sm hgm h2k hkN
  -- the reduced datum agrees with `Θ` on `(0,1)`
  set Φ : ℝ → ℝ := abelReduceIter ((n : ℝ) - 3 / 2) (n - 1) Ψ with hΦ
  have hΦΘ : Set.EqOn Φ Θ (Set.Ioo (0:ℝ) 1) := by
    intro c hc
    rw [hΦ]
    exact (abelReduceIter_congr hΨeq ((n : ℝ) - 3 / 2) (n - 1) hc).trans (hΘeq hc)
  have hΘsm' : ContDiff ℝ (M + 1) Θ := by
    have h2 : ((K - (n - 1) : ℕ) : ℕ∞ω) = (K : ℕ∞ω) - ((n - 1 : ℕ) : ℕ∞ω) := by norm_cast
    refine hΘsm.of_le ?_
    rw [← h2]
    exact_mod_cast hKle
  obtain ⟨Cb, hCb⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hΘsm'.continuous.continuousOn (s := Set.Icc (0:ℝ) 1))
  have hΦcont : ContinuousOn Φ (Set.Ioo (0:ℝ) 1) :=
    hΘsm'.continuous.continuousOn.congr (fun c hc => hΦΘ hc)
  have hΦbdd : ∀ c ∈ Set.Ioo (0:ℝ) 1, ‖Φ c‖ ≤ Cb := by
    intro c hc
    rw [hΦΘ hc]
    exact hCb c ⟨hc.1.le, hc.2.le⟩
  -- the smooth trigonometric candidate
  set Kf : ℝ → ℝ := fun u => ∫ θ in (0:ℝ)..(Real.pi / 2), u * Real.sin θ * Θ (u * Real.sin θ)
    with hKf
  have hKfsm : ContDiff ℝ (M + 1) Kf := by
    rw [hKf]
    apply Work.Analysis.Calculus.contDiff_intervalIntegral_fixed (M + 1)
    have h1 : ContDiff ℝ (M + 1) (fun p : ℝ × ℝ => p.1 * Real.sin p.2) := by fun_prop
    exact h1.mul (hΘsm'.comp h1)
  have hderivsm : ContDiff ℝ M (deriv Kf) := hKfsm.deriv'
  -- the Abel integral coincides with `Kf` on `(0,1)`
  set I : ℝ → ℝ := fun v => ∫ c in (0:ℝ)..v, c * Φ c / Real.sqrt (v ^ 2 - c ^ 2) with hI
  have hfinsm : ContDiffOn ℝ M (fun u => (2 / Real.pi) * deriv Kf u) (Set.Ioo (0:ℝ) 1) :=
    (contDiff_const.mul hderivsm).contDiffOn
  refine hfinsm.congr (fun u hu => ?_)
  have hIK : I =ᶠ[𝓝 u] Kf := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
    have hv0 : 0 < v := hv.1
    have hv1 : v < 1 := hv.2
    have hsub := abel_integral_trig_substitution (Φ := Φ) hv0 hv1 hΦcont hΦbdd
    have hcongr : (∫ θ in (0:ℝ)..(Real.pi / 2), v * Real.sin θ * Φ (v * Real.sin θ))
        = ∫ θ in (0:ℝ)..(Real.pi / 2), v * Real.sin θ * Θ (v * Real.sin θ) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      beta_reduce
      rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi / 2)] at hθ
      by_cases hsin0 : Real.sin θ = 0
      · simp [hsin0]
      · have hsin_nn : 0 ≤ Real.sin θ :=
          Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
        have hsinpos : 0 < Real.sin θ := lt_of_le_of_ne hsin_nn (Ne.symm hsin0)
        have hmem : v * Real.sin θ ∈ Set.Ioo (0:ℝ) 1 := by
          refine ⟨mul_pos hv0 hsinpos, ?_⟩
          have h1 : v * Real.sin θ ≤ v * 1 :=
            mul_le_mul_of_nonneg_left (Real.sin_le_one θ) hv0.le
          linarith
        rw [hΦΘ hmem]
    show (∫ c in (0:ℝ)..v, c * Φ c / Real.sqrt (v ^ 2 - c ^ 2))
        = ∫ θ in (0:ℝ)..(Real.pi / 2), v * Real.sin θ * Θ (v * Real.sin θ)
    rw [hsub, hcongr]
  have hderiveq : deriv I u = deriv Kf u := hIK.deriv_eq
  rw [radonInverse_eq, hderiveq]

end Work.OddRadon
