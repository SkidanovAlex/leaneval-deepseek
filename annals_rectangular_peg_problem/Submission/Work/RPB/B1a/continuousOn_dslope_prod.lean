import Mathlib

/-!
# Joint continuity of `dslope` on `U × U` for holomorphic `f`

For a holomorphic function `f` on an open set `U ⊆ ℂ`, the two-variable function

`(a, b) ↦ dslope f a b`

is continuous on `U × U`.  Here `dslope f a b` is the slope `(f b - f a) / (b - a)` when
`a ≠ b` and the derivative `deriv f a` when `a = b`.

Off the diagonal this is immediate from the algebra of continuous functions.  On the
diagonal one cannot use mere differentiability (for real functions the corresponding
statement is false); holomorphy gives `C^1`, hence a *strict* derivative at each point,
which yields the needed uniform bound on the difference quotients.
-/

open Filter Set
open scoped Topology

namespace Work.RPB.B1a

/-- On the diagonal, `(a, b) ↦ dslope f a b` tends to `deriv f z` as `(a, b) → (z, z)`.

We use that `f` is `C^1` around `z`, so that `deriv f z` is a *strict* derivative of `f` at `z`:
this gives the uniform remainder estimate `f b - f a - (b - a) * deriv f z = o(b - a)`.  Dividing
by `b - a` bounds the slope off the diagonal, while on the diagonal `dslope f a a = deriv f a`
converges to `deriv f z` by continuity of `deriv f`. -/
private theorem tendsto_dslope_diag {f : ℂ → ℂ} {U : Set ℂ} (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {z : ℂ} (hz : z ∈ U) :
    Tendsto (fun p : ℂ × ℂ => dslope f p.1 p.2) (𝓝 (z, z)) (𝓝 (deriv f z)) := by
  have hdcont : ContinuousAt (deriv f) z :=
    ((hf.deriv hUo).continuousOn z hz).continuousAt (hUo.mem_nhds hz)
  have hsc : HasStrictDerivAt f (deriv f z) z :=
    ((hf.contDiffOn hUo).contDiffAt (hUo.mem_nhds hz)).hasStrictDerivAt (n := ⊤) (by simp)
  have hLO : (fun p : ℂ × ℂ => f p.1 - f p.2 - (p.1 - p.2) • (deriv f z))
      =o[𝓝 (z, z)] (fun p : ℂ × ℂ => p.1 - p.2) :=
    hasDerivAtFilter_iff_isLittleO.mp hsc
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hdiag : ∀ᶠ (p : ℂ × ℂ) in 𝓝 (z, z), dist (deriv f p.1) (deriv f z) < ε := by
    have hb : ∀ᶠ w in 𝓝 z, dist (deriv f w) (deriv f z) < ε :=
      (Metric.tendsto_nhds.mp hdcont) ε hε
    exact Filter.Tendsto.eventually (f := Prod.fst) (l₁ := 𝓝 (z, z)) (l₂ := 𝓝 z)
      (continuousAt_fst : Tendsto Prod.fst (𝓝 (z, z)) (𝓝 z)) hb
  have hoff : ∀ᶠ (p : ℂ × ℂ) in 𝓝 (z, z),
      p.1 ≠ p.2 → dist (dslope f p.1 p.2) (deriv f z) < ε := by
    filter_upwards [hLO.bound hε2] with p hp hne
    have hne' : p.2 - p.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    rw [dslope_of_ne f (Ne.symm hne), slope_def_module, dist_eq_norm]
    have key : (p.2 - p.1)⁻¹ • (f p.2 - f p.1) - deriv f z
        = - (f p.1 - f p.2 - (p.1 - p.2) • (deriv f z)) / (p.2 - p.1) := by
      rw [smul_eq_mul, inv_mul_eq_div]
      field_simp
      ring
    rw [key, norm_div, norm_neg]
    have hnormeq : ‖p.2 - p.1‖ = ‖p.1 - p.2‖ := by rw [← norm_neg]; simp
    rw [div_lt_iff₀ (norm_pos_iff.mpr hne'), hnormeq]
    calc ‖f p.1 - f p.2 - (p.1 - p.2) • (deriv f z)‖
        ≤ ε / 2 * ‖p.1 - p.2‖ := hp
      _ < ε * ‖p.1 - p.2‖ := by
          apply mul_lt_mul_of_pos_right (by linarith) (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  filter_upwards [hdiag, hoff] with p hp1 hp2
  rcases eq_or_ne p.1 p.2 with h | h
  · rw [← h, dslope_same]; exact hp1
  · exact hp2 h

/-- Off the diagonal, `(a, b) ↦ dslope f a b` is continuous at `(a, b)`: nearby `a ≠ b`, so
`dslope` agrees with the explicit quotient `(f b - f a) / (b - a)`, which is continuous by
continuity of `f`. -/
private theorem continuousAt_dslope_prod_of_ne {f : ℂ → ℂ} {U : Set ℂ} (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) (hne : b ≠ a) :
    ContinuousAt (fun p : ℂ × ℂ => dslope f p.1 p.2) (a, b) := by
  have hfa : ContinuousAt f a := (hf.continuousOn a ha).continuousAt (hUo.mem_nhds ha)
  have hfb : ContinuousAt f b := (hf.continuousOn b hb).continuousAt (hUo.mem_nhds hb)
  have hslope : ContinuousAt (fun p : ℂ × ℂ => (f p.2 - f p.1) / (p.2 - p.1)) (a, b) := by
    refine ContinuousAt.div ((hfb.comp continuousAt_snd).sub (hfa.comp continuousAt_fst)) ?_ ?_
    · exact continuousAt_snd.sub continuousAt_fst
    · simpa using sub_ne_zero.mpr hne
  refine hslope.congr ?_
  have hmem : (fun p : ℂ × ℂ => p.2 - p.1) ⁻¹' {0}ᶜ ∈ 𝓝 (a, b) :=
    (isOpen_compl_singleton.preimage (continuous_snd.sub continuous_fst)).mem_nhds
      (by simpa using sub_ne_zero.mpr hne)
  filter_upwards [hmem] with p hp
  rw [dslope_of_ne f (sub_ne_zero.mp hp), slope_def_module, smul_eq_mul, inv_mul_eq_div]

theorem continuousOn_dslope_prod {U : Set ℂ} (hUo : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fun p : ℂ × ℂ => dslope f p.1 p.2) (U ×ˢ U) := by
  rintro ⟨a, b⟩ hp
  obtain ⟨ha, hb⟩ := Set.mem_prod.mp hp
  rcases eq_or_ne b a with h | h
  · rw [h]
    have hca : ContinuousAt (fun p : ℂ × ℂ => dslope f p.1 p.2) (a, a) := by
      show Tendsto (fun p : ℂ × ℂ => dslope f p.1 p.2) (𝓝 (a, a)) (𝓝 (dslope f a a))
      rw [dslope_same]
      exact tendsto_dslope_diag hUo hf ha
    exact hca.continuousWithinAt
  · exact (continuousAt_dslope_prod_of_ne hUo hf ha hb h).continuousWithinAt

end Work.RPB.B1a
