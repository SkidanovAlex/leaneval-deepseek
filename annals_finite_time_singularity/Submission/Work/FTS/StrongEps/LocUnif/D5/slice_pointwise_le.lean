import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif.D5

open MeasureTheory Set Filter
open scoped Topology

theorem slice_pointwise_le {a b h δ : ℝ} (hab : a ≤ b) (hh : 0 < h) {P G G' : ℝ → ℝ}
    (hP : ∀ x ∈ Set.Icc a (b + h), |P x| ≤ δ)
    (hG : ∀ x ∈ Set.Icc a (b + h), HasDerivAt P (G x) x)
    (hG2 : ∀ x ∈ Set.Icc a (b + h), HasDerivAt G (G' x) x)
    (hG2c : ContinuousOn G' (Set.Icc a (b + h))) :
    ∀ z ∈ Set.Icc a b, |G z| ≤ 2 * δ / h + ∫ u in z..(z + h), |G' u| := by
  have _ := hab
  intro z hz
  have hz1 : a ≤ z := hz.1
  have hz2 : z ≤ b := hz.2
  have hzh : z < z + h := by linarith
  -- the window `[z, z+h]` lies inside `[a, b+h]`
  have hsub : Set.Icc z (z + h) ⊆ Set.Icc a (b + h) := by
    intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- mean value theorem on `[z, z+h]`: a point `c` where `G c` is the slope of `P`
  have hcont : ContinuousOn P (Set.Icc z (z + h)) :=
    fun x hx => (hG x (hsub hx)).continuousAt.continuousWithinAt
  obtain ⟨c, hcIoo, hcval⟩ := exists_hasDerivAt_eq_slope P G hzh hcont
    (fun x hx => hG x (hsub (Set.Ioo_subset_Icc_self hx)))
  have hcge : z ≤ c := hcIoo.1.le
  have hcle : c ≤ z + h := hcIoo.2.le
  have hsub' : Set.Icc z c ⊆ Set.Icc a (b + h) := by
    intro x hx; exact hsub ⟨hx.1, le_trans hx.2 hcle⟩
  have hc_eq : G c = (P (z + h) - P z) / h := by
    rw [hcval, add_sub_cancel_left]
  -- `|G c| ≤ 2 δ / h`
  have hP1 : |P z| ≤ δ := hP z ⟨hz1, by linarith⟩
  have hP2 : |P (z + h)| ≤ δ := hP (z + h) ⟨by linarith, by linarith⟩
  have hbound : |P (z + h) - P z| ≤ 2 * δ := by
    have hsplit : P (z + h) - P z = P (z + h) + -P z := by ring
    calc |P (z + h) - P z| = |P (z + h) + -P z| := congrArg abs hsplit
      _ ≤ |P (z + h)| + |-P z| := abs_add_le _ _
      _ = |P (z + h)| + |P z| := by rw [abs_neg]
      _ ≤ δ + δ := add_le_add hP2 hP1
      _ = 2 * δ := by ring
  have hGc : |G c| ≤ 2 * δ / h := by
    rw [hc_eq, abs_div, abs_of_pos hh]
    exact div_le_div_of_nonneg_right hbound hh.le
  -- fundamental theorem of calculus on `[z, c]`
  have hIntG' : IntervalIntegrable G' volume z c :=
    (hG2c.mono hsub').intervalIntegrable_of_Icc hcge
  have hFTC : ∫ u in z..c, G' u = G c - G z :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => by
        rw [Set.uIcc_of_le hcge] at hx
        exact hG2 x (hsub' hx)) hIntG'
  have hGz : G z - G c = -∫ u in z..c, G' u := by rw [hFTC]; ring
  have hIntAbs : IntervalIntegrable (fun u => |G' u|) volume z (z + h) :=
    ((continuous_abs.comp_continuousOn (hG2c.mono hsub))).intervalIntegrable_of_Icc
      (by linarith)
  have h2 : |G z - G c| ≤ ∫ u in z..(z + h), |G' u| := by
    have he : |G z - G c| = |∫ u in z..c, G' u| := by rw [hGz, abs_neg]
    rw [he]
    calc |∫ u in z..c, G' u| ≤ ∫ u in z..c, |G' u| :=
          intervalIntegral.abs_integral_le_integral_abs hcge
      _ ≤ ∫ u in z..(z + h), |G' u| :=
          intervalIntegral.integral_mono_interval le_rfl hcge hcle
            (Filter.Eventually.of_forall fun x => abs_nonneg (G' x)) hIntAbs
  have h1 : |G z| ≤ |G c| + |G z - G c| := by
    have hsplit : G z = G c + (G z - G c) := by ring
    calc |G z| = |G c + (G z - G c)| := congrArg abs hsplit
      _ ≤ |G c| + |G z - G c| := abs_add_le _ _
  linarith

end Work.FTS.StrongEps.LocUnif.D5
