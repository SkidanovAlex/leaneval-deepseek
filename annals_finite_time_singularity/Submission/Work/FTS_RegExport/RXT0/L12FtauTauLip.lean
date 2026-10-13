import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.Standing
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.majorant_tail
import Submission.Work.Construction.Defs
import Submission.Work.FTS.RegExportIface.RXT.Leaves

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `RXT0.L12FtauTauLip`

The `τ`-Lipschitz bound for `L₁₂(F(τ))` on a compact radial interval `[a,b]`, `a > 0`,
deduced from the *density* Lipschitz bound

  `|L12dens (F τ) r − L12dens (F τ') r| ≤ C · (SW r / r) · |τ − τ'|   (r > 0)`

together with the integrability of the densities on `(z,∞)`.

The only analytic input is the tail bound `∫_{(z,∞)} SW r / r ≤ 3` (i.e.
`∫_{(z,∞)} r^{1/2}/(1+r)² ≤ 3`, the module `majorant_tail`), which is what turns a
pointwise Lipschitz bound of the density into a Lipschitz bound of the tail integral
`L₁₂`: on `(z,∞) ⊆ (a,∞)` the integral of the majorant is bounded by `3`.

The general statement is isolated as `L12_lip_of_dens_lip` (no hypothesis on `f`, `g`
beyond the two integrability clauses, so it is reusable for any family).
-/

namespace Work.FTS_RegExport.RXT0

open MeasureTheory Set Filter
open scoped Real Topology

/-- `SW s / s = s^{1/2}/(1+s)²`. -/
private theorem SW_div' (s : ℝ) (hs : 0 < s) :
    Work.FTS_RegExport.RXT.Sys.L12FKaux.SW s / s = s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 := by
  have h := Work.FTS_RegExport.RXT.L12Iter.Rwt_div s hs
  simpa only [Work.FTS_RegExport.RXT.Sys.L12FKaux.SW,
    Work.FTS_RegExport.RXT.L12Iter.Rwt] using h

/-- The tail bound `∫_{(z,∞)} SW r / r ≤ 3` and the integrability of the integrand. -/
private theorem SW_div_tail {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun r : ℝ => Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r) (Set.Ioi z) ∧
      ∫ r in Set.Ioi z, Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r ≤ 3 := by
  obtain ⟨hint, hval⟩ := Work.FTS_RegExport.RXT.Sys.L12FKaux.majorant_tail hz
  have hcongr : ∀ r ∈ Set.Ioi z,
      (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) r
        = (fun r : ℝ => Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r) r :=
    fun r hr => (SW_div' r (lt_trans hz hr)).symm
  refine ⟨hint.congr ?_, ?_⟩
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
    exact hcongr r hr
  · rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun r hr => (hcongr r hr).symm)]
    exact hval

/-- **The `L₁₂`-difference bound from a density bound.**  If the density of `L₁₂ f`
differs from that of `L₁₂ g` pointwise by at most `C · (SW r / r) · c` and both densities
are integrable on `(z,∞)`, then on every compact interval `[a,b]` with `a > 0` the values
of `L₁₂` differ by at most `3 C c`.  (No regularity of `f`, `g` is needed; the number `3`
is the tail bound `∫_{(z,∞)} SW r/r ≤ 3`.) -/
theorem L12_lip_of_dens_lip {f g : ℝ → ℝ → ℝ} {C c : ℝ} (hC0 : 0 ≤ C) (hc : 0 ≤ c)
    (hlip : ∀ r : ℝ, 0 < r →
      |Work.Construction.L12dens f r - Work.Construction.L12dens g r|
        ≤ C * (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r) * c)
    (hf : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (Work.Construction.L12dens f) (Set.Ioi z))
    (hg : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (Work.Construction.L12dens g) (Set.Ioi z)) :
    ∀ a b : ℝ, 0 < a → a ≤ b → ∀ z ∈ Set.Icc a b,
      |Work.Construction.L12 f z - Work.Construction.L12 g z| ≤ C * 3 * c := by
  intro a b ha hab z hz
  have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
  have hFint : Integrable (Work.Construction.L12dens f) (volume.restrict (Set.Ioi z)) := hf z hz0
  have hGint : Integrable (Work.Construction.L12dens g) (volume.restrict (Set.Ioi z)) := hg z hz0
  have hL12 : Work.Construction.L12 f z
      = ∫ r in Set.Ioi z, Work.Construction.L12dens f r := rfl
  have hL12' : Work.Construction.L12 g z
      = ∫ r in Set.Ioi z, Work.Construction.L12dens g r := rfl
  have hsub : (∫ r in Set.Ioi z, Work.Construction.L12dens f r)
        - (∫ r in Set.Ioi z, Work.Construction.L12dens g r)
      = ∫ r in Set.Ioi z, (Work.Construction.L12dens f r - Work.Construction.L12dens g r) :=
    (MeasureTheory.integral_sub hFint hGint).symm
  have habs : ∀ r ∈ Set.Ioi z,
      |Work.Construction.L12dens f r - Work.Construction.L12dens g r|
        ≤ C * (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r) * c :=
    fun r hr => hlip r (lt_trans hz0 hr)
  have hInt1 : Integrable
      (fun r => |Work.Construction.L12dens f r - Work.Construction.L12dens g r|)
      (volume.restrict (Set.Ioi z)) := (hFint.sub hGint).abs
  have hInt2 : Integrable
      (fun r => C * c * (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r))
      (volume.restrict (Set.Ioi z)) :=
    (SW_div_tail hz0).1.const_mul (C * c)
  have hmono : ∫ r in Set.Ioi z,
        |Work.Construction.L12dens f r - Work.Construction.L12dens g r|
      ≤ ∫ r in Set.Ioi z, C * c * (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r) := by
    refine MeasureTheory.integral_mono_ae hInt1 hInt2 ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
    simpa only [mul_assoc, mul_comm, mul_left_comm] using habs r hr
  have hconst : ∫ r in Set.Ioi z, C * c * (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r)
      = C * c * ∫ r in Set.Ioi z, Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r :=
    MeasureTheory.integral_const_mul _ _
  have htail : ∫ r in Set.Ioi z, Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r ≤ 3 :=
    (SW_div_tail hz0).2
  rw [hL12, hL12', hsub]
  calc |∫ r in Set.Ioi z, (Work.Construction.L12dens f r - Work.Construction.L12dens g r)|
      ≤ ∫ r in Set.Ioi z, |Work.Construction.L12dens f r - Work.Construction.L12dens g r| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ r in Set.Ioi z, C * c * (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r) := hmono
    _ = C * c * ∫ r in Set.Ioi z, Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r := hconst
    _ ≤ C * c * 3 := mul_le_mul_of_nonneg_left htail (mul_nonneg hC0 hc)
    _ = C * 3 * c := by ring

theorem L12FtauTauLip {g : Work.FTS.Galerkin.Fam} {α : ℝ} (S : ℝ) (hS : 0 < S)
    (hQ : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      ∀ r : ℝ, 0 < r →
        |Work.Construction.L12dens (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) r
          - Work.Construction.L12dens (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ') r|
        ≤ C * (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r) * |τ - τ'|)
    (hint : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (Work.Construction.L12dens
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi z)) :
    ∀ a b : ℝ, 0 < a → a ≤ b → ∃ C : ℝ, 0 ≤ C ∧
      ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S, ∀ z ∈ Set.Icc a b,
        |Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) z
          - Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ') z| ≤ C * |τ - τ'| := by
  obtain ⟨C, hC0, hC⟩ := hQ
  intro a b ha hab
  refine ⟨C * 3, by linarith [hS], ?_⟩
  intro τ hτ τ' hτ' z hz
  exact L12_lip_of_dens_lip
      (f := Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ)
      (g := Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ')
      (C := C) (c := |τ - τ'|) hC0 (abs_nonneg _)
      (fun r hr => hC τ hτ τ' hτ' r hr)
      (fun z hz => hint τ hτ z hz) (fun z hz => hint τ' hτ' z hz) a b ha hab z hz

end Work.FTS_RegExport.RXT0
