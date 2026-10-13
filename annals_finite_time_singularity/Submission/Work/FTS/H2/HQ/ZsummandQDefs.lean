/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `Cf`/`Cg`-weighted `D_z`-summand toolkit for the interior product rule

`Work.FTS.H2.HQ.ZsummandQ` needs the `RegQ`-analogue of the `Work.Spaces.HPRZ` toolkit of
`Submission/Work/Spaces/HProductRule_Zsummand.lean`: the pointwise `L^∞`-bound of order `≤ 2`
is supplied abstractly by `Work.FTS.H2.HQ.PwBd` (whose constant is `Cf`, resp. `Cg`, *not*
the fixed `100` of `MixedSqPointwiseBound`, which needs the unusable class `SmoothNbhd`).

This file contains only the definitions and the elementary bookkeeping lemmas; the pointwise
estimate itself is `ZsummandQptwise` and the `L²`-assembly is `ZsummandQ`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.HQ.Glue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.HQ

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

/-! ## The auxiliary data of the `Z`-summand

For the Leibniz expansion `D_z^i (f·g) = ∑_{b≤i} C(i,b) D_z^b f · D_z^{i-b} g` we keep, for
each `b ≤ i`, the factor with index `> 2` (in `L²`, with the light weight `w/sin(2θ)^{η/2}`)
and bound the other factor pointwise by `PwBd` (`b ≤ 2`: the factor is `D_z^b f`, bounded by
`Cf`; `b > 2`: the factor is `D_z^{i-b} g` with `i - b ≤ 2`, bounded by `Cg`). -/

/-- The square of the `L^∞`-bound of the factor kept by the pointwise estimate:
`Cf/(γ-1)·|f|²_{ℋ⁴}` when `b ≤ 2` (the factor `D_z^b f` is bounded by it) and
`Cg/(γ-1)·|g|²_{ℋ⁴}` otherwise. -/
def zsGamQ (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (b : ℕ) : ℝ :=
  if b ≤ 2 then (Cf / (gam α - 1)) * HkSq α 4 f else (Cg / (gam α - 1)) * HkSq α 4 g

/-- The function whose weighted `D_z`-iterate is kept in the `L²`-norm. -/
def zsFunQ (f g : ℝ → ℝ → ℝ) (b : ℕ) : ℝ → ℝ → ℝ := if b ≤ 2 then g else f

/-- The order of the weighted `D_z`-iterate kept in the `L²`-norm. -/
def zsIdxQ (i b : ℕ) : ℕ := if b ≤ 2 then i - b else b

/-- The summand of the majorant: the absolute value of the retained weighted derivative. -/
def zsFbQ (f g : ℝ → ℝ → ℝ) (i b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => |DzIter (zsIdxQ i b) (zsFunQ f g b) z θ
    * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|

/-- The coefficient of the summand `zsFbQ f g i b` in the majorant. -/
def zsAAQ (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (i b : ℕ) : ℝ :=
  |(i.choose b : ℝ)| * Real.sqrt (zsGamQ α f g Cf Cg b)

/-- The majorant: the value of the pointwise estimate for the Leibniz expansion. -/
def zsVQ (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (i : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => ∑ b ∈ Finset.range (i + 1), zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ

/-! ## Definitional unfolding lemmas -/

theorem zsGamQ_apply (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (b : ℕ) :
    zsGamQ α f g Cf Cg b
      = if b ≤ 2 then (Cf / (gam α - 1)) * HkSq α 4 f
        else (Cg / (gam α - 1)) * HkSq α 4 g := rfl

theorem zsFunQ_apply (f g : ℝ → ℝ → ℝ) (b : ℕ) :
    zsFunQ f g b = if b ≤ 2 then g else f := rfl

theorem zsIdxQ_apply (i b : ℕ) : zsIdxQ i b = if b ≤ 2 then i - b else b := rfl

theorem zsFbQ_apply (f g : ℝ → ℝ → ℝ) (i b : ℕ) (z θ : ℝ) :
    zsFbQ f g i b z θ = |DzIter (zsIdxQ i b) (zsFunQ f g b) z θ
      * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := rfl

theorem zsAAQ_apply (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (i b : ℕ) :
    zsAAQ α f g Cf Cg i b = |(i.choose b : ℝ)| * Real.sqrt (zsGamQ α f g Cf Cg b) := rfl

theorem zsVQ_apply (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (i : ℕ) (z θ : ℝ) :
    zsVQ α f g Cf Cg i z θ
      = ∑ b ∈ Finset.range (i + 1), zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ := rfl

/-! ## Elementary properties -/

theorem zsGamQ_eq (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (b : ℕ) (hb2 : b ≤ 2) :
    zsGamQ α f g Cf Cg b = (Cf / (gam α - 1)) * HkSq α 4 f := by
  rw [zsGamQ_apply]; exact if_pos hb2

theorem zsGamQ_eq' (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (b : ℕ) (hb2 : ¬ b ≤ 2) :
    zsGamQ α f g Cf Cg b = (Cg / (gam α - 1)) * HkSq α 4 g := by
  rw [zsGamQ_apply]; exact if_neg hb2

theorem zsFunQ_eq (f g : ℝ → ℝ → ℝ) (b : ℕ) (hb2 : b ≤ 2) : zsFunQ f g b = g := by
  rw [zsFunQ_apply]; exact if_pos hb2

theorem zsFunQ_eq' (f g : ℝ → ℝ → ℝ) (b : ℕ) (hb2 : ¬ b ≤ 2) : zsFunQ f g b = f := by
  rw [zsFunQ_apply]; exact if_neg hb2

theorem zsIdxQ_eq (i b : ℕ) (hb2 : b ≤ 2) : zsIdxQ i b = i - b := by
  rw [zsIdxQ_apply]; exact if_pos hb2

theorem zsIdxQ_eq' (i b : ℕ) (hb2 : ¬ b ≤ 2) : zsIdxQ i b = b := by
  rw [zsIdxQ_apply]; exact if_neg hb2

theorem zsFbQ_eq (f g : ℝ → ℝ → ℝ) (i b : ℕ) (hb2 : b ≤ 2) :
    zsFbQ f g i b = fun z θ => |DzIter (i - b) g z θ
      * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := by
  funext z θ
  simp only [zsFbQ_apply, zsIdxQ_eq i b hb2, zsFunQ_eq f g b hb2]

theorem zsFbQ_eq' (f g : ℝ → ℝ → ℝ) (i b : ℕ) (hb2 : ¬ b ≤ 2) :
    zsFbQ f g i b = fun z θ => |DzIter b f z θ
      * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := by
  funext z θ
  simp only [zsFbQ_apply, zsIdxQ_eq' i b hb2, zsFunQ_eq' f g b hb2]

theorem zsAAQ_mul_zsFbQ_eq (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (i b : ℕ) (z θ : ℝ)
    (hb2 : b ≤ 2) :
    zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ
      = |(i.choose b : ℝ)| * Real.sqrt ((Cf / (gam α - 1)) * HkSq α 4 f)
        * |DzIter (i - b) g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := by
  simp only [zsAAQ_apply, zsGamQ_eq α f g Cf Cg b hb2, zsFbQ_apply, zsIdxQ_eq i b hb2,
    zsFunQ_eq f g b hb2]

theorem zsAAQ_mul_zsFbQ_eq' (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (i b : ℕ) (z θ : ℝ)
    (hb2 : ¬ b ≤ 2) :
    zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ
      = |(i.choose b : ℝ)| * Real.sqrt ((Cg / (gam α - 1)) * HkSq α 4 g)
        * |DzIter b f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := by
  simp only [zsAAQ_apply, zsGamQ_eq' α f g Cf Cg b hb2, zsFbQ_apply, zsIdxQ_eq' i b hb2,
    zsFunQ_eq' f g b hb2]

theorem zsGamQ_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (hγ : 0 < gam α - 1)
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (b : ℕ) : 0 ≤ zsGamQ α f g Cf Cg b := by
  rw [zsGamQ_apply]
  split_ifs with h
  · exact mul_nonneg (div_nonneg hCf hγ.le) (HkSq_nonneg α 4 f)
  · exact mul_nonneg (div_nonneg hCg hγ.le) (HkSq_nonneg α 4 g)

theorem zsAAQ_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (i b : ℕ) :
    0 ≤ zsAAQ α f g Cf Cg i b := by
  rw [zsAAQ_apply]
  exact mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

theorem zsFbQ_nonneg (f g : ℝ → ℝ → ℝ) (i b : ℕ) (z θ : ℝ) :
    0 ≤ zsFbQ f g i b z θ := by
  rw [zsFbQ_apply]
  exact abs_nonneg _

theorem zsVQ_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (i : ℕ) (z θ : ℝ) :
    0 ≤ zsVQ α f g Cf Cg i z θ := by
  rw [zsVQ_apply]
  exact Finset.sum_nonneg fun b _ => mul_nonneg (zsAAQ_nonneg α f g Cf Cg i b)
    (zsFbQ_nonneg f g i b z θ)

/-- The `γ - 1 = α/10` of the paper is positive for `α > 0`. -/
theorem gam_sub_one_pos {α : ℝ} (hα : 0 < α) : 0 < gam α - 1 := by
  rw [gam_sub_one]; linarith

/-- The light weight vanishes on the two degenerate lines of the quadrant: at `z = 0` and
where `sin(2θ) = 0`. -/
theorem light_eq_zero_of_sin {z θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    w z / (Real.sin (2 * θ)) ^ (eta / 2) = 0 := by
  rw [h, Real.zero_rpow (by norm_num [eta]), div_zero]

/-- The light weight vanishes at `z = 0`. -/
theorem light_eq_zero_of_z {θ : ℝ} : w 0 / (Real.sin (2 * θ)) ^ (eta / 2) = 0 := by
  simp [w]

end Work.FTS.H2.HQ
