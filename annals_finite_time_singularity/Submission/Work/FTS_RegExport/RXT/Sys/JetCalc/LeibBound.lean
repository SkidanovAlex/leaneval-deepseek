import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.CoeffJetsDefs
import Submission.Work.FTS_RegExport.RXT.loc_sup4
import Submission.Work.FTS_RegExport.RXT.MixedUniform
import Submission.Work.FTS_RegExport.RXT.slice_space_lip
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS.RegPkgGal.Sup.DthIter_DzIter_comm_fin
import Submission.Work.FTS_RegExport.RXT.C2Psi
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
import Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.mixed_mul_fin

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.JetCalc.LeibBound` — the bounded Leibniz expansion

`|D_z^jD_θ^i(f·h)| ≤ 2^{j+i}·(C_f·C_g)` at a point of an open set where `f`, `h` are `C^{j+i}`
and their mixed jets of order `≤ j+i` are bounded by `C_f`, `C_g`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 1000000
theorem abs_mixed_mul_bound {j i : ℕ} {f h : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hf : ContDiffOn ℝ (j + i) (Function.uncurry f) V)
    (hh : ContDiffOn ℝ (j + i) (Function.uncurry h) V)
    {p : ℝ × ℝ} (hp : p ∈ V) {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hbf : ∀ a b : ℕ, a + b ≤ j + i → |Work.Spaces.mixed b a f p.1 p.2| ≤ Cf)
    (hbh : ∀ a b : ℕ, a + b ≤ j + i → |Work.Spaces.mixed b a h p.1 p.2| ≤ Cg) :
    |Work.Spaces.mixed j i (fun z θ => f z θ * h z θ) p.1 p.2|
      ≤ (2 : ℝ) ^ (j + i) * (Cf * Cg) := by
  rw [Work.FTS_RegExport.RXT.Sys.JetCalc.mixed_mul_fin hV hf hh p.1 p.2 hp]
  have hsumi : ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) = (2 : ℝ) ^ i := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
    norm_num
  have hsumj : ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) = (2 : ℝ) ^ j := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
    norm_num
  have hK : 0 ≤ Cf * Cg := mul_nonneg hCf hCg
  -- the double sum of the absolute values
  have hstep1 : |∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a f p.1 p.2 * Work.Spaces.mixed (j - b) (i - a) h p.1 p.2)|
      ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ)) * (Cf * Cg) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun a ha => le_trans (Finset.abs_sum_le_sum_abs _ _) ?_)
    refine Finset.sum_le_sum (fun b hb => ?_)
    have ha' : a ≤ i := by have := Finset.mem_range.mp ha; omega
    have hb' : b ≤ j := by have := Finset.mem_range.mp hb; omega
    have hX : |Work.Spaces.mixed b a f p.1 p.2| ≤ Cf := hbf a b (by omega)
    have hY : |Work.Spaces.mixed (j - b) (i - a) h p.1 p.2| ≤ Cg := hbh (i - a) (j - b) (by omega)
    have hc : 0 ≤ (i.choose a : ℝ) * (j.choose b : ℝ) := by positivity
    have hXY : |Work.Spaces.mixed b a f p.1 p.2|
        * |Work.Spaces.mixed (j - b) (i - a) h p.1 p.2| ≤ Cf * Cg :=
      mul_le_mul hX hY (abs_nonneg _) hCf
    calc |((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a f p.1 p.2 * Work.Spaces.mixed (j - b) (i - a) h p.1 p.2)|
        = ((i.choose a : ℝ) * (j.choose b : ℝ))
          * |Work.Spaces.mixed b a f p.1 p.2 * Work.Spaces.mixed (j - b) (i - a) h p.1 p.2| := by
          rw [abs_mul, abs_of_nonneg hc]
      _ = ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (|Work.Spaces.mixed b a f p.1 p.2| * |Work.Spaces.mixed (j - b) (i - a) h p.1 p.2|) := by
          rw [abs_mul]
      _ ≤ ((i.choose a : ℝ) * (j.choose b : ℝ)) * (Cf * Cg) :=
          mul_le_mul_of_nonneg_left hXY hc
  have hstep2 : ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ)) * (Cf * Cg)
      = (2 : ℝ) ^ (j + i) * (Cf * Cg) := by
    have houter : ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ)) * (Cf * Cg)
        = (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (i.choose a : ℝ) * (j.choose b : ℝ)) * (Cf * Cg) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_mul]
    rw [houter, ← Finset.sum_mul_sum, hsumi, hsumj, ← pow_add, Nat.add_comm]
  exact le_trans hstep1 (le_of_eq hstep2)

end Work.FTS_RegExport.RXT.Sys
