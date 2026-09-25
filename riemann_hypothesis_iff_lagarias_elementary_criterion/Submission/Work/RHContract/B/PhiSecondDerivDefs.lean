import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.B.Phi_analyticOn

/-!
# Auxiliary functions for the identity `Φ'' = h₂ − h₂′`

`Work.RHContract.Landau.Phi` is the Mellin transform

`Φ(s) = ∫_2^∞ (ψ t − t) k(t) t^{−s} dt`,   `k(t) = (log t + 1) / (t² log² t)`,

and the Landau step of the route needs the second derivative of `Φ` on `Re s > 0`:

`Φ''(s) = ∫_2^∞ (ψ t − t) (1 + log t) t^{−s−2} dt = h₂(s) − h₂′(s)`.

The point of the present module is to package the two cut-off correlation functions that
appear on the right-hand side:

* `psiSubIdCut t = 1_{t > 2} (ψ t − t)`, whose Mellin transform `mellin psiSubIdCut (−s−1)` is
  exactly `h₂(s) = ∫_2^∞ (ψ t − t) t^{−s−2} dt`;
* `psiSubIdLogCut t = 1_{t > 2} (ψ t − t)(1 + log t)`, whose Mellin transform
  `mellin psiSubIdLogCut (−s−1) = ∫_2^∞ (ψ t − t)(1 + log t) t^{−s−2} dt` is the right-hand side
  of the identity above.

Besides the definitions we record the elementary analytic facts about `psiSubIdCut` (vanishing
below `2`, measurability, local integrability on `(0, ∞)`, and the Chebyshev growth bound
`ψ t − t = O(t)`), together with their logarithmic upgrades.
-/

open MeasureTheory Filter Asymptotics
open scoped Topology

namespace Work.RHContract.B

noncomputable section

/-- `t ↦ (ψ t − t)` cut down to `t > 2`. -/
def psiSubIdCut : ℝ → ℂ :=
  (Set.Ioi 2).indicator (fun t : ℝ => ((Chebyshev.psi t - t : ℝ) : ℂ))

/-- `t ↦ (ψ t − t)(1 + log t)` cut down to `t > 2`. -/
def psiSubIdLogCut : ℝ → ℂ :=
  (Set.Ioi 2).indicator (fun t : ℝ => ((((Chebyshev.psi t - t) * (1 + Real.log t)) : ℝ) : ℂ))

lemma psiSubIdCut_apply_of_le {t : ℝ} (ht : t ≤ 2) : psiSubIdCut t = 0 := by
  rw [psiSubIdCut, Set.indicator_of_notMem]
  simpa only [Set.mem_Ioi, not_lt] using ht

lemma psiSubIdCut_apply_of_gt {t : ℝ} (ht : 2 < t) :
    psiSubIdCut t = ((Chebyshev.psi t - t : ℝ) : ℂ) := by
  rw [psiSubIdCut, Set.indicator_of_mem (Set.mem_Ioi.mpr ht)]

lemma psiSubIdLogCut_apply_of_le {t : ℝ} (ht : t ≤ 2) : psiSubIdLogCut t = 0 := by
  rw [psiSubIdLogCut, Set.indicator_of_notMem]
  simpa only [Set.mem_Ioi, not_lt] using ht

lemma psiSubIdLogCut_apply_of_gt {t : ℝ} (ht : 2 < t) :
    psiSubIdLogCut t = ((((Chebyshev.psi t - t) * (1 + Real.log t)) : ℝ) : ℂ) := by
  rw [psiSubIdLogCut, Set.indicator_of_mem (Set.mem_Ioi.mpr ht)]

lemma measurable_psiSubIdCut : Measurable psiSubIdCut := by
  have h : Measurable (fun t : ℝ => ((Chebyshev.psi t - t : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (Chebyshev.psi_mono.measurable.sub measurable_id)
  exact h.indicator measurableSet_Ioi

/-- `psiSubIdCut` is integrable on a compact interval contained in `(0, ∞)`. -/
lemma integrableOn_Icc_psiSubIdCut {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn psiSubIdCut (Set.Icc a b) := by
  refine Measure.integrableOn_of_bounded (s := Set.Icc a b) (M := Chebyshev.psi b + b)
    measure_Icc_lt_top.ne measurable_psiSubIdCut.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  apply ae_of_all
  intro t ht
  by_cases h2 : 2 < t
  · rw [psiSubIdCut_apply_of_gt h2, norm_ofReal]
    have htb : t ≤ b := ht.2
    have hpsi : Chebyshev.psi t ≤ Chebyshev.psi b := Chebyshev.psi_mono htb
    have hpsi0 : 0 ≤ Chebyshev.psi t := Chebyshev.psi_nonneg t
    have h1 : |Chebyshev.psi t - t| ≤ Chebyshev.psi t + t := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith, by linarith⟩
    linarith
  · rw [psiSubIdCut_apply_of_le (not_lt.mp h2), norm_zero]
    linarith [Chebyshev.psi_nonneg b]

lemma locallyIntegrableOn_psiSubIdCut : LocallyIntegrableOn psiSubIdCut (Set.Ioi 0) := by
  intro x0 hx0
  have hx0pos : 0 < x0 := hx0
  refine ⟨Metric.ball x0 (x0 / 2), ?_, ?_⟩
  · exact mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x0 (by linarith))
  · refine (integrableOn_Icc_psiSubIdCut (a := x0 - x0 / 2) (b := x0 + x0 / 2)
      (by linarith) (by linarith)).mono_set ?_
    intro y hy
    have hyr : |y - x0| < x0 / 2 := by simpa [Real.dist_eq] using hy
    exact ⟨by linarith [(abs_lt.mp hyr).1], by linarith [(abs_lt.mp hyr).2]⟩

/-- Chebyshev's bound gives `psiSubIdCut = O(t)` at infinity. -/
lemma psiSubIdCut_isBigO_atTop :
    psiSubIdCut =O[atTop] (fun x : ℝ => x ^ (1 : ℝ)) := by
  rw [isBigO_iff]
  refine ⟨Real.log 4 + 4, ?_⟩
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
  rw [psiSubIdCut_apply_of_gt hx, norm_ofReal, Real.rpow_one, Real.norm_eq_abs,
    abs_of_pos (by linarith : (0 : ℝ) < x)]
  exact abs_psi_sub_id_le (by linarith)

/-- `psiSubIdCut` vanishes on a neighbourhood of `0`, hence is `O(x ^ (-b))` there for every `b`. -/
lemma psiSubIdCut_isBigO_nhdsGT (b : ℝ) :
    psiSubIdCut =O[𝓝[>] 0] (fun x : ℝ => x ^ (-b)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [show Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) from Ioo_mem_nhdsGT zero_lt_one]
    with t ht
  rw [psiSubIdCut_apply_of_le (by linarith [ht.2] : t ≤ 2), norm_zero]
  positivity

lemma locallyIntegrableOn_log_psiSubIdCut :
    LocallyIntegrableOn (fun t : ℝ => Real.log t • psiSubIdCut t) (Set.Ioi 0) :=
  locallyIntegrableOn_psiSubIdCut.continuousOn_smul isOpen_Ioi.isLocallyClosed
    (Real.continuousOn_log.mono (fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (by simpa using ht)))

/-- The logarithmic version of the Chebyshev bound: `log • psiSubIdCut = O(x ^ (-b))` at infinity
for every `b < -1`. -/
lemma log_psiSubIdCut_isBigO_atTop {b : ℝ} (hb : b < -1) :
    (fun t : ℝ => Real.log t • psiSubIdCut t) =O[atTop] (fun x : ℝ => x ^ (-b)) := by
  have h := isBigO_rpow_top_log_smul (a := -1) (b := b) hb (by
    simpa using psiSubIdCut_isBigO_atTop)
  simpa using h

lemma log_psiSubIdCut_isBigO_nhdsGT (b : ℝ) :
    (fun t : ℝ => Real.log t • psiSubIdCut t) =O[𝓝[>] 0] (fun x : ℝ => x ^ (-b)) := by
  have h := isBigO_rpow_zero_log_smul (a := b - 1) (b := b) (by linarith)
    (psiSubIdCut_isBigO_nhdsGT (b - 1))
  simpa using h

end

end Work.RHContract.B
