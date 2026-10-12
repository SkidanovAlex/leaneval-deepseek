import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixKin.Assembly.assembly_fs
import Submission.Work.BoseFixKin.Kinetic.kinetic_localisation_core
import Submission.Work.BoseKinLoc.Kinetic.kinetic_localisation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixKin.Kinetic.kinetic_localisation_fs` — FS `lem:LocKinEn` on the coupled regime

Node N3b of `BOSE_BCLASH_LEAD.md`: the headline of the D2 repair.

`momBound_rescale` turns the **crude, already-proved** momentum bound `MomBound` (whose threshold
`b₀` is existential and `≪ 1/16`) into the `K`-form used by `kinetic_localisation_core`:
for `K := 1/(16 b₀)` and any `0 < b ≤ 1/16`,

`b ∫_u momForm ℓ d u ψ ≤ (1/2) K raFrac ℓ d ψ`.

`kinetic_localisation_fs` then assembles:

* `GapBound (1/2)` — `Work.BoseKinLoc.Gap.gapBound_general`, proved;
* `NeumannBound` — `Work.BoseKinLoc.NeuFrac.neumann_bound`, proved;
* `MomBound` — `Work.BoseKinLoc.Kinetic.momBound_of_u_average` composed with
  `Work.BoseKinLoc.Momentum.momForm_u_integral_alt`, proved;
* `TprimeBound C` — `Work.BoseKinLoc.Tprime.tprime_two_regime`, proved (with `C`, `s₀`);
* the momentum budget — `Work.BoseFixKin.Assembly.assembly_fs` at `cFS K C` (nodes N1, N2);

giving `∃ c₀ > 0, KineticLocalisationFS c₀` with the explicit
`c₀ = min (cFS K C) (s₀/2)`.  No `χ`-numeric constant and no `momBound_at_sixteenth` is used;
`b = bValue = 1/16` is admissible because the regime `KinRegimeFS` keeps `s` and `ε_T` small
and couples them to `d` through `ε_T s ≤ c₀ d`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixKin.Kinetic

open Work.BoseKinLoc

/-- **`MomBound` at its own `b₀` gives the `K`-form for every `0 < b ≤ 1/16`**, with
`K = 1/(16 b₀)`: `b ∫ momForm ≤ (1/2) K raFrac`.  The only input besides `MomBound` is
`raFrac ≥ 0`. -/
theorem momBound_rescale {b₀ : ℝ} (hb₀ : 0 < b₀)
    (hmom : ∀ b : ℝ, 0 < b → b ≤ b₀ → ∀ ψ : ℝ³ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∀ ℓ d : ℝ, 0 < ℓ → 0 < d → d ≤ 1 → Integrable (fun u : ℝ³ => momForm ℓ d u ψ) →
        b * (∫ u : ℝ³, momForm ℓ d u ψ) ≤ (1 / 2) * raFrac ℓ d ψ)
    {b ℓ d : ℝ} (hb : 0 < b) (hb16 : b ≤ 1 / 16) (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1)
    (ψ : ℝ³ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcs : HasCompactSupport ψ)
    (hint : Integrable (fun u : ℝ³ => momForm ℓ d u ψ)) :
    b * (∫ u : ℝ³, momForm ℓ d u ψ) ≤ (1 / 2) * (1 / (16 * b₀)) * raFrac ℓ d ψ := by
  have h0 := hmom b₀ hb₀ le_rfl ψ hψ hcs ℓ d hℓ hd hd1 hint
  have hra : 0 ≤ raFrac ℓ d ψ := by
    unfold raFrac
    refine mul_nonneg (by positivity) (integral_nonneg fun p => mul_nonneg ?_ (sq_nonneg _))
    unfold raSym; positivity
  have e : b * (∫ u : ℝ³, momForm ℓ d u ψ) = (b / b₀) * (b₀ * ∫ u : ℝ³, momForm ℓ d u ψ) := by
    field_simp
  rw [e]
  calc (b / b₀) * (b₀ * ∫ u : ℝ³, momForm ℓ d u ψ) ≤ (b / b₀) * ((1 / 2) * raFrac ℓ d ψ) :=
        mul_le_mul_of_nonneg_left h0 (by positivity)
    _ ≤ (1 / (16 * b₀)) * ((1 / 2) * raFrac ℓ d ψ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [div_le_div_iff₀ hb₀ (by positivity)]; nlinarith
    _ = _ := by ring

/-- **FS `lem:LocKinEn` on the coupled regime** (node N3b): there is an absolute `c₀ > 0` with
`KineticLocalisationFS c₀`. -/
theorem kinetic_localisation_fs : ∃ c₀ : ℝ, 0 < c₀ ∧ KineticLocalisationFS c₀ := by
  obtain ⟨C, hC, s₀, hs₀, htpr⟩ := Work.BoseKinLoc.Tprime.tprime_two_regime
  have hgap : GapBound (1 / 2) := Work.BoseKinLoc.Gap.gapBound_general (1 / 2) (by norm_num) le_rfl
  have hmomB : MomBound :=
    Work.BoseKinLoc.Kinetic.momBound_of_u_average fun ψ hψ hcs ℓ d hℓ hd =>
      Work.BoseKinLoc.Momentum.momForm_u_integral_alt ψ hψ hcs ℓ d hℓ hd
  obtain ⟨b₀, hb₀, hmom⟩ := hmomB
  set K : ℝ := 1 / (16 * b₀) with hKdef
  have hK : 0 ≤ K := by positivity
  have hcF : 0 < cFS K C := by unfold cFS; exact lt_min (by norm_num) (by positivity)
  have hcF4 : cFS K C ≤ 1 / 4 := min_le_left _ _
  refine ⟨min (cFS K C) (s₀ / 2), lt_min hcF (by positivity), ?_⟩
  intro ℓ d s εT b hreg ψ hψ hcs hint
  obtain ⟨hℓ, hd, hd1, hs, hsc, hεT, hεTc, hcpl, hb, hb16⟩ := hreg
  have hm1 : min (cFS K C) (s₀ / 2) ≤ cFS K C := min_le_left _ _
  have hm2 : min (cFS K C) (s₀ / 2) ≤ s₀ / 2 := min_le_right _ _
  have hregF : KinRegimeFS (cFS K C) ℓ d s εT b :=
    ⟨hℓ, hd, hd1, hs, hsc.trans hm1, hεT, hεTc.trans hm1,
      hcpl.trans (mul_le_mul_of_nonneg_right hm1 hd.le), hb, hb16⟩
  refine kinetic_localisation_core (β := 1 / 2) (by norm_num) hC hK hℓ hd hd1 hs hεT
    (by linarith [hεTc.trans hm1]) hb hgap Work.BoseKinLoc.NeuFrac.neumann_bound
    (fun ψ hψ hcs hint => by
      rw [hKdef]
      exact momBound_rescale hb₀ hmom hb hb16 hℓ hd hd1 ψ hψ hcs hint)
    ?_ (Work.BoseFixKin.Assembly.assembly_fs hK hC ℓ d s εT b hregF) ψ hψ hcs hint
  rintro σ (rfl | rfl) ψ hψ hcs hint
  · exact htpr _ (by positivity) (by linarith) ψ hψ hcs ℓ hℓ hint
  · refine htpr _ (by positivity) ?_ ψ hψ hcs ℓ hℓ hint
    nlinarith [mul_le_mul_of_nonneg_right hd1 hs.le]

end Work.BoseFixKin.Kinetic
