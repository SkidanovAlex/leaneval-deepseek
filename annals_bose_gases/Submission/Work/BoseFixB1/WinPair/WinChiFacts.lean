import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.WinPair.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WinPair.WinChiFacts` — elementary facts about the box-restricted window

Small shared chapter of the windowed-pairing chain:

* `exists_abs_winChi_le` — a continuous window is bounded on the (compact) box, hence
  `winChi s χ` is bounded everywhere;
* `chi_eq_winChi_of_mem_abox` — on the `N`-particle box the window agrees coordinatewise
  with `winChi` (this is what allows the pairing word `winPairForm` — whose window factor
  is the *plain* `χ` — to be written with `winChi`, as the relative-coordinate machinery
  requires);
* `aestronglyMeasurable_pairFibreFun_shift` — the shifted peeled pair fibre
  `(y,u) ↦ Q_{ij}(y, y−u)` is a.e. strongly measurable (the measurability input of the
  relative-coordinate integrability of `q4_subst_integrable`, isolated here).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.WinPair

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- A continuous window is bounded on the box, hence `winChi s χ` is bounded. -/
lemma exists_abs_winChi_le {s : ℝ} (hs : 0 < s) {χ : E3 → ℝ} (hχ : Continuous χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E3, |winChi s χ z| ≤ C := by
  obtain ⟨C, hC⟩ := (acube_compact hs).exists_bound_of_continuousOn hχ.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  by_cases hz : z ∈ acube s
  · rw [winChi_of_mem hz]
    exact le_trans (by simpa [Real.norm_eq_abs] using hC z hz) (le_max_left _ _)
  · rw [winChi_eq_zero hz, abs_zero]
    exact le_max_right _ _

/-- On the `N`-particle box the window agrees coordinatewise with `winChi`. -/
lemma chi_eq_winChi_of_mem_abox {N : ℕ} {s : ℝ} {χ : E3 → ℝ} {x : X N}
    (hx : x ∈ abox N s) (i : Fin N) : χ (x i) = winChi s χ (x i) :=
  (winChi_of_mem ((mem_abox_iff N s x).mp hx i)).symm

/-- A measurable window gives a measurable `winChi`. -/
lemma measurable_winChi_of_measurable {s : ℝ} {χ : E3 → ℝ} (hχ : Measurable χ) :
    Measurable (winChi s χ) := measurable_winChi hχ

/-- **The shifted peeled pair fibre is a.e. strongly measurable.** -/
lemma aestronglyMeasurable_pairFibreFun_shift {N : ℕ} {s : ℝ} (hs : 0 < s)
    {Ψ : X (N + 2) → ℝ} (hΨc : Continuous Ψ) {i j : Fin (N + 2)} (hij : i ≠ j) :
    AEStronglyMeasurable (fun q : E3 × E3 => pairFibreFun s Ψ i j q.1 (q.1 - q.2))
      (volume.prod volume) := by
  set j' := sucAboveInv i j hij with hj'def
  have hR2 : Measurable (fun q : (E3 × E3) × X N => rest2 i j' q.2) := by
    have hj : Continuous (fun q : (E3 × E3) × X N =>
        kcInsN N j' ((0 : E3), q.2)) :=
      (kcInsN_cont j').comp (by fun_prop)
    exact ((kcInsN_cont (i : Fin (N + 2))).comp
      (continuous_const.prodMk hj)).measurable
  have hIns : Measurable (fun q : (E3 × E3) × X N =>
      ins2 i j' q.1.1 (q.1.1 - q.1.2) q.2) := by
    have h1 : Continuous (fun q : (E3 × E3) × X N =>
        kcInsN N j' (q.1.1 - q.1.2, q.2)) :=
      (kcInsN_cont j').comp (by fun_prop)
    exact ((kcInsN_cont (i : Fin (N + 2))).comp (by fun_prop)).measurable
  have hmeasm : Measurable (fun q : (E3 × E3) × X N =>
      (aP s i (aP s j Ψ) (rest2 i j' q.2)
        * aQ s j (aQ s i Ψ)
            (ins2 i j' q.1.1 (q.1.1 - q.1.2) q.2) : ℝ)) :=
    ((aP_continuous hs i (aP_continuous hs j hΨc)).measurable.comp hR2).mul
      ((aQ_continuous hs j (aQ_continuous hs i hΨc)).measurable.comp hIns)
  have hQaesm : AEStronglyMeasurable (fun q : E3 × E3 =>
      pairFibreFun s Ψ i j q.1 (q.1 - q.2)) (volume.prod volume) := by
    have := hmeasm.aestronglyMeasurable.integral_prod_right'
      (μ := volume.prod volume) (ν := (volume : Measure (X N)).restrict (abox N s))
    simpa only [pairFibreFun, dif_pos hij, hj'def] using this
  exact hQaesm

end Work.BoseFixB1.WinPair
