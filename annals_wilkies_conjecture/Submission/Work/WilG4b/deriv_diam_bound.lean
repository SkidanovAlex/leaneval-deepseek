import Mathlib

namespace Work.WilG4b

/-- If `C` is preconnected (hence an interval in `ℝ`), `G` is bounded between `a` and `b` on `C`,
and `|deriv G t| > K > 0` for all `t ∈ C`, then any two points `u < v` of `C` are at distance at
most `(b - a) / K`.

The proof is the Mean Value Theorem on `[u, v] ⊆ C`: since `|deriv G| > K > 0` everywhere on `C`,
`deriv G` never vanishes on `C`, hence `G` is differentiable (and a fortiori continuous) at every
point of `[u, v]`.  MVT then gives a point `c ∈ (u, v)` with `deriv G c = (G v - G u)/(v - u)`, so
`K * (v - u) < |deriv G c| * (v - u) = |G v - G u| ≤ b - a`. -/
lemma deriv_diam_bound {K a b : ℝ} (hK : 0 < K)
    {G : ℝ → ℝ} {C : Set ℝ} (hC : IsPreconnected C)
    (hGl : ∀ t ∈ C, a ≤ G t) (hGu : ∀ t ∈ C, G t ≤ b)
    (hGd : ∀ t ∈ C, K < |deriv G t|) :
    ∀ u ∈ C, ∀ v ∈ C, u < v → v - u ≤ (b - a) / K := by
  have hord : C.OrdConnected := hC.ordConnected
  intro u hu v hv huv
  -- `[u, v] ⊆ C` because `C` is order-connected.
  have hsub : Set.Icc u v ⊆ C := hord.out hu hv
  -- `G` is differentiable at every point of `[u, v]`, since there `|deriv G| > K > 0`.
  have hdiffAt : ∀ t ∈ Set.Icc u v, DifferentiableAt ℝ G t := by
    intro t ht
    have htC : t ∈ C := hsub ht
    have h1 : K < |deriv G t| := hGd t htC
    exact differentiableAt_of_deriv_ne_zero (abs_pos.mp (lt_trans hK h1))
  have hdiffOnIcc : DifferentiableOn ℝ G (Set.Icc u v) :=
    fun t ht => (hdiffAt t ht).differentiableWithinAt
  have hcont : ContinuousOn G (Set.Icc u v) := hdiffOnIcc.continuousOn
  have hdiffOn : DifferentiableOn ℝ G (Set.Ioo u v) :=
    fun t ht => (hdiffAt t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).differentiableWithinAt
  -- Mean Value Theorem.
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope' G huv hcont hdiffOn
  have hcd' : deriv G c = (G v - G u) / (v - u) := by
    rw [slope_def_field] at hcd; exact hcd
  have hd : 0 < v - u := sub_pos.mpr huv
  have hne : v - u ≠ 0 := ne_of_gt hd
  have hmul : G v - G u = deriv G c * (v - u) := by
    rw [hcd', div_mul_cancel₀ _ hne]
  have habs : |G v - G u| = |deriv G c| * (v - u) := by
    rw [hmul, abs_mul, abs_of_pos hd]
  have hcC : c ∈ C := hsub ⟨le_of_lt hc.1, le_of_lt hc.2⟩
  have hKlt : K * (v - u) < |deriv G c| * (v - u) :=
    mul_lt_mul_of_pos_right (hGd c hcC) hd
  have hKabs : K * (v - u) < |G v - G u| := by rw [habs]; exact hKlt
  -- Bounds `a ≤ G u`, `G v ≤ b` give `|G v - G u| ≤ b - a`.
  have hbnd : |G v - G u| ≤ b - a := by
    rw [abs_le]
    exact ⟨by linarith [sub_le_sub (hGu u hu) (hGl v hv)],
           sub_le_sub (hGu v hv) (hGl u hu)⟩
  have hKv : K * (v - u) < b - a := lt_of_lt_of_le hKabs hbnd
  have hKv' : (v - u) * K < b - a := by simpa [mul_comm] using hKv
  have : v - u < (b - a) / K := by
    rw [lt_div_iff₀ hK]; exact hKv'
  exact le_of_lt this

end Work.WilG4b
