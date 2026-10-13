import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The truncation principle for integrals with a singular left endpoint

Two reusable lemmas that turn a *uniform bound on the truncated integrals*
`∫_{(δ,ε]} f` (for every `δ ∈ (0,ε)`) into a statement about the whole interval `(0,ε)`.

They are the measure-theoretic workhorses of the weighted Hardy inequalities with a
singular left endpoint (`powerHardySecond` and friends): the analytic content of such a
statement is always proved on the compact subintervals `[δ,ε]` (where the derivatives are
continuous), and these lemmas pass the result to the singular endpoint by monotone
convergence.

* `lintegral_Ioc_le_of_forall_Ioc` — the `lintegral` form: if `f ≥ 0` a.e. and all
  truncated integrals are `≤ C`, then `∫⁻_{x ∈ (0,ε]} f x ≤ C`.
* `integrableOn_of_forall_Ioc_le` — the `IntegrableOn` form for a continuous `f`: the same
  hypotheses (plus continuity on `(0,ε)`) give `IntegrableOn f (Ioo 0 ε)`.

Note that the hypotheses are only imposed for `δ ∈ (0,ε)` and that nonnegativity is
required only a.e. with the *truncated* form `x ∈ (0,ε] → 0 ≤ f x`; this is because the
value of `f` at the upper endpoint `ε` is not controlled by the typical hypotheses (a
function can be `C²` on `(0,ε)` and jump at `ε`).

The proof truncates by the increasing family of intervals `(ε/2^{n+1}, ε]`, whose union is
`(0,ε]`, and applies `MeasureTheory.lintegral_iSup'` together with
`MeasureTheory.ofReal_integral_eq_lintegral_ofReal` on each truncation.
-/

namespace Work.FTS.EllSol.VthAux.traceAux

open MeasureTheory Set Filter
open scoped Topology

/-- **Truncation principle, `lintegral` form.**

Let `0 < ε`, let `f : ℝ → ℝ` be nonnegative a.e. on `(0,ε]` and integrable on each truncated
interval `(δ,ε]` (`0 < δ < ε`) with `∫_{(δ,ε]} f ≤ C` uniformly in `δ`. Then
`∫⁻_{x ∈ (0,ε]} f x ≤ C`.

The truncating family is `Ioc (ε/2^{n+1}) ε`, increasing with union `Ioc 0 ε`. -/
theorem lintegral_Ioc_le_of_forall_Ioc {ε C : ℝ} (hε : 0 < ε) {f : ℝ → ℝ}
    (hf_int : ∀ δ ∈ Set.Ioo 0 ε, MeasureTheory.IntegrableOn f (Set.Ioc δ ε))
    (hf_nn : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioc 0 ε → 0 ≤ f x)
    (hb : ∀ δ ∈ Set.Ioo 0 ε, ∫ x in Set.Ioc δ ε, f x ≤ C) :
    ∫⁻ x in Set.Ioc 0 ε, ENNReal.ofReal (f x) ≤ ENNReal.ofReal C := by
  classical
  set g : ℝ → ENNReal := fun x => ENNReal.ofReal (f x) with hgdef
  have hδpos : ∀ n : ℕ, 0 < ε / 2 ^ (n + 1) := fun n => div_pos hε (by positivity)
  have h2le : ∀ n : ℕ, (2 : ℝ) ≤ 2 ^ (n + 1) := by
    intro n
    calc (2:ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n+1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hδlt : ∀ n : ℕ, ε / 2 ^ (n + 1) < ε := by
    intro n
    have h2 := h2le n
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hδmem : ∀ n : ℕ, ε / 2 ^ (n + 1) ∈ Set.Ioo 0 ε := fun n => ⟨hδpos n, hδlt n⟩
  have hmono_set : ∀ n : ℕ, Set.Ioc (ε / 2 ^ (n + 1)) ε ⊆ Set.Ioc (ε / 2 ^ (n + 1 + 1)) ε := by
    intro n x hx
    have hle : ε / 2 ^ (n + 1 + 1) ≤ ε / 2 ^ (n + 1) := by
      refine div_le_div_of_nonneg_left hε.le (by positivity) ?_
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    exact ⟨lt_of_le_of_lt hle hx.1, hx.2⟩
  have hunion : (⋃ n : ℕ, Set.Ioc (ε / 2 ^ (n + 1)) ε) = Set.Ioc 0 ε := by
    ext x; constructor
    · intro hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      exact ⟨lt_trans (hδpos n) hn.1, hn.2⟩
    · intro hx
      have hlim : Tendsto (fun n : ℕ => ε / 2 ^ (n + 1)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop
          ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)).comp
            (tendsto_add_atTop_nat 1))
      obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds hx.1)).exists
      exact Set.mem_iUnion.mpr ⟨n, ⟨hn, hx.2⟩⟩
  have hpoint : ∀ x, (⨆ n : ℕ, (Set.Ioc (ε / 2 ^ (n + 1)) ε).indicator g x)
      = (Set.Ioc 0 ε).indicator g x := by
    intro x
    by_cases hx : x ∈ Set.Ioc 0 ε
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hunion ▸ hx)
      rw [Set.indicator_of_mem hx]
      refine le_antisymm (iSup_le (fun m => ?_)) ?_
      · by_cases hxm : x ∈ Set.Ioc (ε / 2 ^ (m + 1)) ε
        · rw [Set.indicator_of_mem hxm]
        · rw [Set.indicator_of_notMem hxm]
          exact zero_le
      · rw [← Set.indicator_of_mem hn g]
        exact le_iSup (fun m : ℕ => (Set.Ioc (ε / 2 ^ (m + 1)) ε).indicator g x) n
    · have hzero : ∀ m : ℕ, (Set.Ioc (ε / 2 ^ (m + 1)) ε).indicator g x = 0 := fun m =>
        Set.indicator_of_notMem (fun hcon => hx (hunion ▸ Set.mem_iUnion.mpr ⟨m, hcon⟩)) g
      rw [Set.indicator_of_notMem hx]
      simp [hzero]
  have hmeas : ∀ n : ℕ, AEMeasurable ((Set.Ioc (ε / 2 ^ (n + 1)) ε).indicator g) volume := by
    intro n
    rw [aemeasurable_indicator_iff measurableSet_Ioc]
    exact ((hf_int _ (hδmem n)).aestronglyMeasurable.aemeasurable).ennreal_ofReal
  have hmono_u : ∀ᵐ x ∂(volume : Measure ℝ),
      Monotone (fun n : ℕ => (Set.Ioc (ε / 2 ^ (n + 1)) ε).indicator g x) :=
    Filter.Eventually.of_forall (fun x => by
      refine monotone_nat_of_le_succ (fun n => ?_)
      by_cases hxn : x ∈ Set.Ioc (ε / 2 ^ (n + 1)) ε
      · rw [Set.indicator_of_mem hxn, Set.indicator_of_mem (hmono_set n hxn)]
      · rw [Set.indicator_of_notMem hxn]
        exact zero_le)
  have hnn_n : ∀ n : ℕ, 0 ≤ᵐ[volume.restrict (Set.Ioc (ε / 2 ^ (n + 1)) ε)] f := by
    intro n
    change ∀ᵐ x ∂(volume.restrict (Set.Ioc (ε / 2 ^ (n + 1)) ε)), 0 ≤ f x
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hf_nn] with x hx hxs
    exact hx ⟨lt_trans (hδpos n) hxs.1, hxs.2⟩
  calc ∫⁻ x in Set.Ioc 0 ε, g x
      = ∫⁻ x, (Set.Ioc 0 ε).indicator g x := (lintegral_indicator measurableSet_Ioc g).symm
    _ = ∫⁻ x, ⨆ n : ℕ, (Set.Ioc (ε / 2 ^ (n + 1)) ε).indicator g x := by
          simp only [hpoint]
    _ = ⨆ n : ℕ, ∫⁻ x, (Set.Ioc (ε / 2 ^ (n + 1)) ε).indicator g x :=
          lintegral_iSup' hmeas hmono_u
    _ = ⨆ n : ℕ, ENNReal.ofReal (∫ x in Set.Ioc (ε / 2 ^ (n + 1)) ε, f x) := by
          refine iSup_congr (fun n => ?_)
          rw [lintegral_indicator measurableSet_Ioc]
          exact (ofReal_integral_eq_lintegral_ofReal (hf_int _ (hδmem n)) (hnn_n n)).symm
    _ ≤ ENNReal.ofReal C := iSup_le (fun n => ENNReal.ofReal_le_ofReal (hb _ (hδmem n)))

/-- **Truncation principle, `IntegrableOn` form.**

Let `0 < ε`, let `f` be continuous and nonnegative a.e. on `(0,ε)`, integrable on every
truncated interval `(δ,ε]` with `∫_{(δ,ε]} f ≤ C` uniformly in `δ`. Then `f` is
`IntegrableOn (0,ε)`. -/
theorem integrableOn_of_forall_Ioc_le {ε C : ℝ} (hε : 0 < ε) {f : ℝ → ℝ}
    (hf_int : ∀ δ ∈ Set.Ioo 0 ε, MeasureTheory.IntegrableOn f (Set.Ioc δ ε))
    (hf_cont : ContinuousOn f (Set.Ioo 0 ε))
    (hf_nn : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioc 0 ε → 0 ≤ f x)
    (hb : ∀ δ ∈ Set.Ioo 0 ε, ∫ x in Set.Ioc δ ε, f x ≤ C) :
    MeasureTheory.IntegrableOn f (Set.Ioo 0 ε) := by
  have h := lintegral_Ioc_le_of_forall_Ioc hε hf_int hf_nn hb
  have h1 : ∫⁻ x in Set.Ioo 0 ε, ENNReal.ofReal (f x)
      = ∫⁻ x in Set.Ioc 0 ε, ENNReal.ofReal (f x) := by
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  have hnn_ae : 0 ≤ᵐ[volume.restrict (Set.Ioo 0 ε)] f := by
    change ∀ᵐ x ∂(volume.restrict (Set.Ioo 0 ε)), 0 ≤ f x
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hf_nn] with x hx hxs
    exact hx ⟨hxs.1, hxs.2.le⟩
  refine ⟨hf_cont.aestronglyMeasurable measurableSet_Ioo, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hnn_ae, h1]
  exact lt_of_le_of_lt h ENNReal.ofReal_lt_top

end Work.FTS.EllSol.VthAux.traceAux
