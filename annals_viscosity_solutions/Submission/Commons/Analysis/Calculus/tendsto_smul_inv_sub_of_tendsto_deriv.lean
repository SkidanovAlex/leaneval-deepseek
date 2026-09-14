import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Calculus

open Filter Set
open scoped Topology

/-- If `f` is differentiable on `[T, ∞)` with derivative `f'`, and `f' → l` as `t → ∞`,
then the "average slope" `t⁻¹ • (f t - f T)` tends to `l`.

This is the L'Hôpital/Stolz-type statement that when the derivative of a function
has a limit at infinity, the function is asymptotically linear with that slope:
`f t = t • l + o(t)`. The proof uses only the mean value theorem: subtracting the
affine comparison function `s ↦ (s - T) • l` makes the derivative tend to `0`, and
a uniform bound on the derivative on `[M, t]` (from the mean value inequality
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`) gives the estimate. -/
theorem tendsto_smul_inv_sub_of_tendsto_deriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f f' : ℝ → E} {l : E} {T : ℝ}
    (hf : ∀ t ∈ Set.Ici T, HasDerivAt f (f' t) t)
    (hl : Filter.Tendsto f' Filter.atTop (𝓝 l)) :
    Filter.Tendsto (fun t : ℝ => t⁻¹ • (f t - f T)) Filter.atTop (𝓝 l) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ε' : ℝ := ε / 2 with hε'def
  have hε'pos : 0 < ε' := by rw [hε'def]; linarith
  have hε'eq : ε' + ε' = ε := by rw [hε'def]; ring
  have hev1 : ∀ᶠ x in atTop, ‖f' x - l‖ < ε' := by
    have h := (Metric.tendsto_nhds.mp hl) ε' hε'pos
    filter_upwards [h] with x hx
    rwa [dist_eq_norm] at hx
  obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.mp hev1
  set M : ℝ := max M0 (max T 1) with hMdef
  have hM0M : M0 ≤ M := le_max_left _ _
  have hTM : T ≤ M := le_trans (le_max_left T 1) (le_max_right M0 (max T 1))
  have h1M : (1 : ℝ) ≤ M := le_trans (le_max_right T 1) (le_max_right M0 (max T 1))
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one h1M
  have hMnn : 0 ≤ M := le_of_lt hMpos
  have hM0le : ∀ x, M ≤ x → ‖f' x - l‖ < ε' := fun x hx => hM0 x (le_trans hM0M hx)
  let G : ℝ → E := fun s => f s - f T - (s - T) • l
  have hGderiv : ∀ x, T ≤ x → HasDerivAt G (f' x - l) x := by
    intro x hx
    have hfx : HasDerivAt f (f' x) x := hf x hx
    have hconst : HasDerivAt (fun _ : ℝ => f T) 0 x := hasDerivAt_const x (f T)
    have hlin : HasDerivAt (fun s : ℝ => (s - T) • l) l x := by
      have h1 : HasDerivAt (fun s : ℝ => s - T) (1 : ℝ) x :=
        HasDerivAt.sub_const T (hasDerivAt_id x)
      have h2 := h1.smul_const l
      simpa using h2
    have h3 := (hfx.sub hconst).sub hlin
    have hfun : ((fun y : ℝ => f y) - (fun _ : ℝ => f T) - (fun s : ℝ => (s - T) • l)) = G := by
      funext s
      simp only [G, Pi.sub_apply]
    rw [hfun] at h3
    simpa using h3
  have hbound : ∀ t, M ≤ t → ‖G t - G M‖ ≤ ε' * (t - M) := by
    intro t ht
    have hderiv : ∀ x ∈ Set.Icc M t, HasDerivWithinAt G (f' x - l) (Set.Icc M t) x := by
      intro x hx
      have hxT : T ≤ x := le_trans hTM (Set.mem_Icc.mp hx).1
      exact (hGderiv x hxT).hasDerivWithinAt
    have hbnd : ∀ x ∈ Set.Icc M t, ‖f' x - l‖ ≤ ε' := by
      intro x hx
      exact le_of_lt (hM0le x (Set.mem_Icc.mp hx).1)
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbnd
      (convex_Icc M t) (right_mem_Icc.mpr ht) (left_mem_Icc.mpr ht)
    have hnorm : ‖M - t‖ = t - M := by
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    rw [norm_sub_rev, hnorm] at hmvt
    exact hmvt
  have hmain : ∀ t, M ≤ t →
      ‖t⁻¹ • (f t - f T) - l‖ ≤ ε' + t⁻¹ * (‖G M‖ + |T| * ‖l‖) := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hMpos ht
    have htne : t ≠ 0 := ne_of_gt htpos
    have htnn : 0 ≤ t := le_of_lt htpos
    have hGexpr : G t + (t - T) • l = f t - f T := by
      simp only [G]
      abel
    have hdecomp : t⁻¹ • (f t - f T) = t⁻¹ • G t + (t⁻¹ * (t - T)) • l := by
      rw [← hGexpr, smul_add, smul_smul]
    have herr : t⁻¹ • (f t - f T) - l = t⁻¹ • G t + (t⁻¹ * (t - T) - 1) • l := by
      rw [hdecomp]
      have hsub : (t⁻¹ * (t - T)) • l - l = ((t⁻¹ * (t - T)) - 1) • l := by
        calc (t⁻¹ * (t - T)) • l - l
            = (t⁻¹ * (t - T)) • l - (1 : ℝ) • l := by rw [one_smul]
          _ = ((t⁻¹ * (t - T)) - 1) • l := by rw [sub_smul]
      rw [← hsub]
      abel
    have hcoef : t⁻¹ * (t - T) - 1 = -T * t⁻¹ := by
      field_simp
      ring
    have htM1 : t⁻¹ * (t - M) = 1 - M * t⁻¹ := by
      field_simp
    have hGt : ‖G t‖ ≤ ε' * (t - M) + ‖G M‖ := by
      calc ‖G t‖ = ‖(G t - G M) + G M‖ := by rw [sub_add_cancel]
        _ ≤ ‖G t - G M‖ + ‖G M‖ := norm_add_le _ _
        _ ≤ ε' * (t - M) + ‖G M‖ := by
              have := hbound t ht
              linarith [norm_nonneg (G M)]
    have h1 : ‖t⁻¹ • G t‖ ≤ ε' + t⁻¹ * ‖G M‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr htnn)]
      have hstep : ε' * (t⁻¹ * (t - M)) ≤ ε' := by
        calc ε' * (t⁻¹ * (t - M)) ≤ ε' * 1 := by
                apply mul_le_mul_of_nonneg_left _ (le_of_lt hε'pos)
                rw [htM1]
                have hnm : 0 ≤ M * t⁻¹ := mul_nonneg hMnn (inv_nonneg.mpr htnn)
                linarith
          _ = ε' := mul_one ε'
      calc t⁻¹ * ‖G t‖ ≤ t⁻¹ * (ε' * (t - M) + ‖G M‖) :=
              mul_le_mul_of_nonneg_left hGt (inv_nonneg.mpr htnn)
        _ = ε' * (t⁻¹ * (t - M)) + t⁻¹ * ‖G M‖ := by ring
        _ ≤ ε' + t⁻¹ * ‖G M‖ := add_le_add hstep (le_refl _)
    have h2 : ‖(t⁻¹ * (t - T) - 1) • l‖ ≤ |T| * t⁻¹ * ‖l‖ := by
      rw [norm_smul, Real.norm_eq_abs, hcoef]
      have habs : |(-T) * t⁻¹| = |T| * t⁻¹ := by
        rw [abs_mul, abs_neg, abs_inv, abs_of_nonneg htnn]
      rw [habs]
    rw [herr]
    calc ‖t⁻¹ • G t + (t⁻¹ * (t - T) - 1) • l‖
        ≤ ‖t⁻¹ • G t‖ + ‖(t⁻¹ * (t - T) - 1) • l‖ := norm_add_le _ _
      _ ≤ (ε' + t⁻¹ * ‖G M‖) + |T| * t⁻¹ * ‖l‖ := add_le_add h1 h2
      _ = ε' + t⁻¹ * (‖G M‖ + |T| * ‖l‖) := by ring
  have htendinv : Tendsto (fun t : ℝ => t⁻¹ * (‖G M‖ + |T| * ‖l‖)) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).mul_const (‖G M‖ + |T| * ‖l‖)
    simpa using h
  have hev2 : ∀ᶠ t in atTop, t⁻¹ * (‖G M‖ + |T| * ‖l‖) < ε' :=
    htendinv.eventually (Iio_mem_nhds hε'pos)
  filter_upwards [Filter.eventually_ge_atTop M, hev2] with t htM hsmall
  rw [dist_eq_norm]
  calc ‖t⁻¹ • (f t - f T) - l‖ ≤ ε' + t⁻¹ * (‖G M‖ + |T| * ‖l‖) := hmain t htM
    _ < ε' + ε' := by linarith
    _ = ε := hε'eq

end Commons.Analysis.Calculus