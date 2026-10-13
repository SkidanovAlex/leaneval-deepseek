/-
# `ptBoundDz` tools: the majorant and the Agmon input

Part of the `ptBoundDz` development (see `Tools/ptBoundDz.lean` for the statement and the
overall route).  Everything here lives in the sub-namespace `...Tools.PtB`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
import Submission.Work.FTS.H2.STSigma
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6.ProdDefs6
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.StrongEps.H5.LevelShift
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools
namespace PtB

open Function Set

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
/-! ## The majorant and elementary facts about it -/

/-- The weight `w z / sin(2θ)^{η/2}` carried by the pure `D_z`-slots of `HkIntegrand`. -/
abbrev Hv (z θ : ℝ) : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)

/-- The `MA²·I⁷_f` block: the undifferentiated coefficient paired with the top slot of `f`. -/
def Maj1 (α : ℝ) (f : ℝ → ℝ → ℝ) (MA z θ : ℝ) : ℝ :=
  MA ^ 2 * Work.Spaces.HkIntegrand α 7 f z θ

/-- The `(γ-1)⁻¹`-block: the two factors priced by the two `ℋ⁶`-norms. -/
def Maj2 (α : ℝ) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (1 + (Work.Spaces.gam α - 1)⁻¹ * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
    * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)

/-- The `KA²·I⁶_f` block: the `∂_θA`-bound paired with the order-`6` slot of `f`. -/
def Maj3 (α : ℝ) (f : ℝ → ℝ → ℝ) (KA z θ : ℝ) : ℝ :=
  KA ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ

/-- The exceptional slot `D_z⁵A · D_θ²f`. -/
def Maj4 (α : ℝ) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 1 1 f z θ * Work.Spaces.Wt α z θ) ^ 2

/-- The exceptional slot `D_zD_θA · D_z⁵f`. -/
def Maj5 (α : ℝ) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.mixed 1 1 A z θ * Work.Spaces.DzIter 5 f z θ * Work.Spaces.Wt α z θ) ^ 2

/-- The exceptional slot `D_θA · D_z⁵f`. -/
def Maj6 (α : ℝ) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.Dth A z θ * Work.Spaces.DzIter 5 f z θ * Work.Spaces.Wt α z θ) ^ 2

/-- The exceptional slot `D_θ²A · D_z⁵f`. -/
def Maj7 (α : ℝ) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.DthIter 2 A z θ * Work.Spaces.DzIter 5 f z θ * Work.Spaces.Wt α z θ) ^ 2

/-- The majorant of the statement (without the constant). -/
def Maj (α : ℝ) (A f : ℝ → ℝ → ℝ) (MA KA z θ : ℝ) : ℝ :=
  Maj1 α f MA z θ + Maj2 α A f z θ + Maj3 α f KA z θ + Maj4 α A f z θ
    + Maj5 α A f z θ + Maj6 α A f z θ + Maj7 α A f z θ

theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

theorem gam_sub_one_pos_ptb {α : ℝ} (hα : 0 < α) : 0 < Work.Spaces.gam α - 1 := by
  rw [Work.Spaces.gam_sub_one]; linarith

theorem gam_sub_one_nonneg_ptb {α : ℝ} (hα : 0 < α) : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ :=
  inv_nonneg.mpr (gam_sub_one_pos_ptb hα).le

/-- Monotonicity of the angular `rpow` weights: on `(0,π/2)`, `sin(2θ)^{a} ≤ sin(2θ)^{b}`
whenever `b ≤ a`. -/
theorem sin_rpow_mono {θ a b : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hb : b ≤ a) :
    (Real.sin (2 * θ)) ^ a ≤ (Real.sin (2 * θ)) ^ b :=
  Real.rpow_le_rpow_of_exponent_ge (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hθ)
    (Real.sin_le_one _) hb

theorem gam_le_two_add_eta {α : ℝ} (hα1 : α ≤ 1) :
    Work.Spaces.gam α ≤ 2 + Work.Spaces.eta := by
  rw [Work.Spaces.gam, Work.Spaces.eta]; linarith

/-- The square of the angular weight of the mixed slots. -/
theorem Wt_sq_eq {α z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hθ
  have key : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    ring
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, key]

/-- The square of the angular weight of the pure `D_z`-slots. -/
theorem Hv_sq_eq {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Hv z θ) ^ 2 = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hθ
  have hHv : Hv z θ = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
    rw [Hv, div_eq_mul_inv, ← Real.rpow_neg hs.le]
  rw [hHv, mul_pow]
  congr 1
  rw [pow_two, ← Real.rpow_add hs]
  congr 1
  ring

theorem Maj1_nonneg (α : ℝ) (f : ℝ → ℝ → ℝ) (MA z θ : ℝ) : 0 ≤ Maj1 α f MA z θ := by
  rw [Maj1]; exact mul_nonneg (sq_nonneg _) (Work.Spaces.HkIntegrand_nonneg α 7 f z θ)

theorem Maj2_nonneg {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Maj2 α A f z θ := by
  rw [Maj2]
  refine mul_nonneg (add_nonneg zero_le_one (mul_nonneg (gam_sub_one_nonneg_ptb hα) ?_)) ?_
  · exact add_nonneg (Work.Spaces.HkSq_nonneg α 6 A) (Work.Spaces.HkSq_nonneg α 6 f)
  · exact add_nonneg (Work.Spaces.HkIntegrand_nonneg α 6 A z θ)
      (Work.Spaces.HkIntegrand_nonneg α 6 f z θ)

theorem Maj3_nonneg (α : ℝ) (f : ℝ → ℝ → ℝ) (KA z θ : ℝ) : 0 ≤ Maj3 α f KA z θ := by
  rw [Maj3]; exact mul_nonneg (sq_nonneg _) (Work.Spaces.HkIntegrand_nonneg α 6 f z θ)

theorem Maj4_nonneg (α : ℝ) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ Maj4 α A f z θ := by
  rw [Maj4]; exact sq_nonneg _

theorem Maj5_nonneg (α : ℝ) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ Maj5 α A f z θ := by
  rw [Maj5]; exact sq_nonneg _

theorem Maj6_nonneg (α : ℝ) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ Maj6 α A f z θ := by
  rw [Maj6]; exact sq_nonneg _

theorem Maj7_nonneg (α : ℝ) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ Maj7 α A f z θ := by
  rw [Maj7]; exact sq_nonneg _

theorem Maj_nonneg {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA KA z θ : ℝ) :
    0 ≤ Maj α A f MA KA z θ := by
  have h1 := Maj1_nonneg α f MA z θ
  have h2 := Maj2_nonneg hα A f z θ
  have h3 := Maj3_nonneg α f KA z θ
  have h4 := Maj4_nonneg α A f z θ
  have h5 := Maj5_nonneg α A f z θ
  have h6 := Maj6_nonneg α A f z θ
  have h7 := Maj7_nonneg α A f z θ
  simp only [Maj]; linarith

theorem Maj1_le_Maj {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA KA z θ : ℝ) :
    Maj1 α f MA z θ ≤ Maj α A f MA KA z θ := by
  have h2 := Maj2_nonneg hα A f z θ
  have h3 := Maj3_nonneg α f KA z θ
  have h4 := Maj4_nonneg α A f z θ
  have h5 := Maj5_nonneg α A f z θ
  have h6 := Maj6_nonneg α A f z θ
  have h7 := Maj7_nonneg α A f z θ
  simp only [Maj]; linarith

theorem Maj2_le_Maj {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA KA z θ : ℝ) :
    Maj2 α A f z θ ≤ Maj α A f MA KA z θ := by
  have h1 := Maj1_nonneg α f MA z θ
  have h3 := Maj3_nonneg α f KA z θ
  have h4 := Maj4_nonneg α A f z θ
  have h5 := Maj5_nonneg α A f z θ
  have h6 := Maj6_nonneg α A f z θ
  have h7 := Maj7_nonneg α A f z θ
  simp only [Maj]; linarith

theorem Maj3_le_Maj {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA KA z θ : ℝ) :
    Maj3 α f KA z θ ≤ Maj α A f MA KA z θ := by
  have h1 := Maj1_nonneg α f MA z θ
  have h2 := Maj2_nonneg hα A f z θ
  have h4 := Maj4_nonneg α A f z θ
  have h5 := Maj5_nonneg α A f z θ
  have h6 := Maj6_nonneg α A f z θ
  have h7 := Maj7_nonneg α A f z θ
  simp only [Maj]; linarith

theorem Maj4_le_Maj {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA KA z θ : ℝ) :
    Maj4 α A f z θ ≤ Maj α A f MA KA z θ := by
  have h1 := Maj1_nonneg α f MA z θ
  have h2 := Maj2_nonneg hα A f z θ
  have h3 := Maj3_nonneg α f KA z θ
  have h5 := Maj5_nonneg α A f z θ
  have h6 := Maj6_nonneg α A f z θ
  have h7 := Maj7_nonneg α A f z θ
  simp only [Maj]; linarith

theorem Maj5_le_Maj {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA KA z θ : ℝ) :
    Maj5 α A f z θ ≤ Maj α A f MA KA z θ := by
  have h1 := Maj1_nonneg α f MA z θ
  have h2 := Maj2_nonneg hα A f z θ
  have h3 := Maj3_nonneg α f KA z θ
  have h4 := Maj4_nonneg α A f z θ
  have h6 := Maj6_nonneg α A f z θ
  have h7 := Maj7_nonneg α A f z θ
  simp only [Maj]; linarith

theorem Maj6_le_Maj {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA KA z θ : ℝ) :
    Maj6 α A f z θ ≤ Maj α A f MA KA z θ := by
  have h1 := Maj1_nonneg α f MA z θ
  have h2 := Maj2_nonneg hα A f z θ
  have h3 := Maj3_nonneg α f KA z θ
  have h4 := Maj4_nonneg α A f z θ
  have h5 := Maj5_nonneg α A f z θ
  have h7 := Maj7_nonneg α A f z θ
  simp only [Maj]; linarith

theorem Maj7_le_Maj {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA KA z θ : ℝ) :
    Maj7 α A f z θ ≤ Maj α A f MA KA z θ := by
  have h1 := Maj1_nonneg α f MA z θ
  have h2 := Maj2_nonneg hα A f z θ
  have h3 := Maj3_nonneg α f KA z θ
  have h4 := Maj4_nonneg α A f z θ
  have h5 := Maj5_nonneg α A f z θ
  have h6 := Maj6_nonneg α A f z θ
  simp only [Maj]; linarith

/-- The pointwise Agmon bound of `PwAny6` for mixed derivatives of order `≤ 4`, bundled. -/
def SupPw (α CPw : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ b a : ℕ, a + b ≤ 4 → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
    (Work.Spaces.mixed b a u z θ) ^ 2 ≤ CPw / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 u


end

end PtB

end Work.FTS.StrongEps.E4R3.Nblock6.Tools
