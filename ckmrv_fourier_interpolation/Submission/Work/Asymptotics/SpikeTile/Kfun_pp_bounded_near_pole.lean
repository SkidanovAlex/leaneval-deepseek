/-
# Boundedness of the principal part of the kernel near the translate poles

This file proves `Work.Asymptotics.SpikeTile.Kfun_pp_bounded_near_pole`: for `n = ±1`, a point
`w ∈ ℍ` with `j'(w) ≠ 0` and `ζ` near `w`, the second-variable slice

  `ζ ↦ K^{(d)}((n : ℝ) +ᵥ w, ζ)`

of the CKMRV kernel has a simple pole at `ζ = w` with residue `n/(2π)` and *bounded* remainder:

  `‖K^{(d)}(n + w, ζ) - (n/2π)(ζ - w)⁻¹‖ ≤ B`  for `0 < ‖ζ - w‖ < δ`.

## Structure of the proof

The main work is the auxiliary `Work.Asymptotics.SpikeTile.exists_bound_Kfun_residue_snd`, which is
the *general local* statement: if `j τ = j z₀` and `j'(z₀) ≠ 0`, and `c` is any constant with

  `AfunFun ℓ d τ z₀ = -c · j'(z₀)`     (`AfunFun τ z = (AfunPlus d z τ + AfunMinus ℓ d z τ)/2`),

then the holomorphic remainder of `ζ ↦ K(τ,ζ)` at `z₀` is bounded, with residue `c`.  The proof
puts everything on the chart `u ↦ ofComplex u` and uses the elementary identity

  `(u - u₀) K(τ, ζ(u)) = Φ u`,     `Φ u = -A(u) / (dslope J u₀ u)`,

where `A(u) = AfunFun τ (ofComplex u)`, `J(u) = j (ofComplex u)` and `dslope J u₀` is the slope
of `J` at `u₀`: indeed `dslope J u₀ u = (u-u₀)⁻¹ (j ζ - j τ)`, and the master identity
`K(τ,ζ)(j τ - j ζ) = AfunFun τ ζ` (`Work.Asymptotics.Kfun_mul_slope_eq_AfunFun`) converts one
into the other.  Because `j'(z₀) = deriv J u₀ ≠ 0`, the denominator `dslope J u₀ u` does not
vanish near `u₀`, so `Φ` is holomorphic on a neighbourhood of `u₀` (`Complex.differentiableOn_dslope`)
and `Φ u₀ = -A(u₀)/j'(z₀) = c` by the hypothesis on `c`.  Hence the difference

  `K(τ,ζ) - c(ζ-w)⁻¹ = dslope Φ u₀ u`

is the slope of a function holomorphic at `u₀`; by
`continuousAt_dslope_same` it is continuous at `u₀`, hence bounded on a neighbourhood.

(The vanishing of `j(u) - j(u₀)` to second order at `u₀` — the "double zero" that the paper's
principal-part computations single out — is exactly what makes the *slope* `dslope Φ u₀`
continuous at `u₀`, i.e. `Φ` holomorphic.)

The target theorem is then the specialisation `τ = (n : ℝ) +ᵥ w`, `z₀ = w`, `c = n/(2π)`, where
`AfunFun ℓ d ((n:ℝ) +ᵥ w) w = -(n/2π)·j'(w)` is `Work.Asymptotics.AfunFun_vadd_int_of` and
`j((n:ℝ) +ᵥ w) = j w` is the `T`-periodicity of `j`.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Kaxis_principal_part_bound

noncomputable section

open UpperHalfPlane Filter
open scoped Topology

namespace Work.Asymptotics.SpikeTile

/-- **The general local residue bound for the kernel in its second variable.**

Let `τ, z₀ ∈ ℍ` with `j τ = j z₀`, `j'(z₀) ≠ 0`, and let `c : ℂ` satisfy
`AfunFun ℓ d τ z₀ = -c · j'(z₀)`.  Then near `z₀` the slice `ζ ↦ K^{(d)}(τ,ζ)` has principal
part `c (ζ - z₀)⁻¹`, with a bounded remainder. -/
lemma exists_bound_Kfun_residue_snd (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ z₀ : UpperHalfPlane) (c : ℂ)
    (hj : Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun z₀)
    (hjp : Work.Residues.jprime z₀ ≠ 0)
    (hc : Work.Asymptotics.AfunFun ℓ d τ z₀ = -c * Work.Residues.jprime z₀) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 ≤ B ∧ ∀ ζ : UpperHalfPlane,
      ‖(ζ : ℂ) - (z₀ : ℂ)‖ < δ → ζ ≠ z₀ →
      ‖Work.Kernels.Kfun ℓ d τ ζ - c * (((ζ : ℂ) - (z₀ : ℂ))⁻¹)‖ ≤ B := by
  set u₀ : ℂ := (z₀ : ℂ) with hu₀
  set A : ℂ → ℂ := fun u => Work.Asymptotics.AfunFun ℓ d τ (UpperHalfPlane.ofComplex u) with hA
  set J : ℂ → ℂ := fun u => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex u) with hJ
  have hu₀im : 0 < u₀.im := by rw [hu₀, UpperHalfPlane.coe_im]; exact z₀.im_pos
  -- holomorphy of the two chart functions
  have hA_diff : DifferentiableOn ℂ A {u : ℂ | 0 < u.im} := by
    have h := (UpperHalfPlane.mdifferentiable_iff (f := fun w : UpperHalfPlane =>
      Work.Asymptotics.AfunFun ℓ d τ w)).mp (Work.Asymptotics.mdifferentiable_AfunFun_snd ℓ d hd τ)
    simpa [hA, Function.comp_def] using h
  have hJ_diff : DifferentiableOn ℂ J {u : ℂ | 0 < u.im} := by
    have h := (UpperHalfPlane.mdifferentiable_iff (f := Work.Kernels.jInvariantFun)).mp
      Work.Asymptotics.mdifferentiable_jInvariantFun
    simpa [hJ, Function.comp_def] using h
  -- a ball around `u₀` inside the upper half plane
  obtain ⟨r, hr, hrsub⟩ : ∃ r : ℝ, 0 < r ∧ Metric.ball u₀ r ⊆ {u : ℂ | 0 < u.im} := by
    refine ⟨u₀.im / 2, by linarith, ?_⟩
    intro u hu
    rw [Metric.mem_ball, dist_eq_norm] at hu
    have h1 : |u.im - u₀.im| ≤ ‖u - u₀‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (u - u₀)
    have h2 := (abs_lt.mp (lt_of_le_of_lt h1 hu)).1
    simp only [Set.mem_ofPred_eq]; linarith
  have hA_ball : DifferentiableOn ℂ A (Metric.ball u₀ r) := hA_diff.mono hrsub
  have hJ_ball : DifferentiableOn ℂ J (Metric.ball u₀ r) := hJ_diff.mono hrsub
  -- the slope `dslope J u₀` of `J` at `u₀`
  have hg_diff : DifferentiableOn ℂ (dslope J u₀) (Metric.ball u₀ r) :=
    (Complex.differentiableOn_dslope (Metric.ball_mem_nhds u₀ hr)).mpr hJ_ball
  have hg_cont : ContinuousAt (dslope J u₀) u₀ :=
    hg_diff.continuousOn.continuousAt (Metric.ball_mem_nhds u₀ hr)
  have hg_deriv : deriv J u₀ = Work.Residues.jprime z₀ := by
    rw [hu₀]
    simpa only [hJ, Function.comp_def] using Work.Asymptotics.deriv_jInvariantFun_ofComplex z₀
  have hg_ne₀ : dslope J u₀ u₀ ≠ 0 := by rw [dslope_same, hg_deriv]; exact hjp
  have hev : ∀ᶠ u in 𝓝 u₀, dslope J u₀ u ≠ 0 := hg_cont.eventually_ne hg_ne₀
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hev
  set R : ℝ := min r δ₀ / 2 with hR
  have hRpos : 0 < R := by rw [hR]; have := lt_min hr hδ₀pos; linarith
  have hRr : R ≤ r := by rw [hR]; linarith [min_le_left r δ₀]
  have hRδ : R ≤ δ₀ := by rw [hR]; linarith [min_le_right r δ₀]
  have hg_ne_ball : ∀ u ∈ Metric.ball u₀ R, dslope J u₀ u ≠ 0 := by
    intro u hu
    rw [Metric.mem_ball] at hu
    exact hδ₀ (show dist u u₀ < δ₀ from by linarith)
  -- the holomorphic function `Φ` whose slope at `u₀` is the remainder
  set Φ : ℂ → ℂ := fun u => -(A u) / (dslope J u₀ u) with hΦ
  have hΦ_diff : DifferentiableOn ℂ Φ (Metric.ball u₀ R) := by
    rw [hΦ]
    exact ((hA_ball.mono (Metric.ball_subset_ball hRr)).neg).div
      (hg_diff.mono (Metric.ball_subset_ball hRr)) (fun u hu => hg_ne_ball u hu)
  have hΦ_at : DifferentiableAt ℂ Φ u₀ := hΦ_diff.differentiableAt (Metric.ball_mem_nhds u₀ hRpos)
  have hA_u₀ : A u₀ = Work.Asymptotics.AfunFun ℓ d τ z₀ := by
    rw [hu₀]; simp only [hA, UpperHalfPlane.ofComplex_apply]
  have hΦu₀ : Φ u₀ = c := by
    show -(A u₀) / (dslope J u₀ u₀) = c
    rw [hA_u₀, show dslope J u₀ u₀ = Work.Residues.jprime z₀ from by rw [dslope_same, hg_deriv]]
    rw [hc]
    field_simp
  have hΦdslope_cont : ContinuousAt (dslope Φ u₀) u₀ := continuousAt_dslope_same.mpr hΦ_at
  -- the slope of `Φ` at `u₀` is bounded near `u₀`
  have hev2 : ∀ᶠ u in 𝓝 u₀, ‖dslope Φ u₀ u‖ ≤ ‖deriv Φ u₀‖ + 1 := by
    have h1 : ∀ᶠ u in 𝓝 u₀, dist (dslope Φ u₀ u) (dslope Φ u₀ u₀) < 1 :=
      (Metric.continuousAt_iff'.mp hΦdslope_cont) 1 (by norm_num)
    filter_upwards [h1] with u hu
    rw [dslope_same] at hu
    have h3 : ‖dslope Φ u₀ u - deriv Φ u₀‖ < 1 := by rwa [dist_eq_norm] at hu
    have h4 : ‖dslope Φ u₀ u‖ = ‖(dslope Φ u₀ u - deriv Φ u₀) + deriv Φ u₀‖ := by ring_nf
    calc ‖dslope Φ u₀ u‖ = ‖(dslope Φ u₀ u - deriv Φ u₀) + deriv Φ u₀‖ := h4
      _ ≤ ‖dslope Φ u₀ u - deriv Φ u₀‖ + ‖deriv Φ u₀‖ := norm_add_le _ _
      _ ≤ ‖deriv Φ u₀‖ + 1 := by linarith
  rw [Metric.eventually_nhds_iff] at hev2
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hev2
  set δ : ℝ := min δ₁ R with hδ
  have hδpos : 0 < δ := lt_min hδ₁pos hRpos
  have hδR : δ ≤ R := min_le_right _ _
  have hδδ₁ : δ ≤ δ₁ := min_le_left _ _
  refine ⟨δ, ‖deriv Φ u₀‖ + 1, hδpos, by positivity, ?_⟩
  intro ζ hζ hζne
  set u : ℂ := (ζ : ℂ) with hu
  have hu_ne : u ≠ u₀ := by
    intro h
    exact hζne (UpperHalfPlane.ext (by rw [hu, hu₀] at h; exact h))
  have huR : ‖u - u₀‖ < R := by rw [hu, hu₀]; linarith
  have hu_ball : u ∈ Metric.ball u₀ R := by rw [Metric.mem_ball, dist_eq_norm]; exact huR
  have hg_ne_u : dslope J u₀ u ≠ 0 := hg_ne_ball u hu_ball
  -- the slope of `J` is the logarithmic derivative of the divisor
  have hg_u : dslope J u₀ u
      = (u - u₀)⁻¹ * (Work.Kernels.jInvariantFun ζ - Work.Kernels.jInvariantFun τ) := by
    rw [dslope_of_ne _ hu_ne, slope_def_field, div_eq_inv_mul]
    simp only [hJ, hu, hu₀, UpperHalfPlane.ofComplex_apply]
    rw [hj]
  have hj_ne : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ := by
    intro h
    exact hg_ne_u (by rw [hg_u, h, sub_self, mul_zero])
  have hA_u : A u = Work.Asymptotics.AfunFun ℓ d τ ζ := by
    rw [hu]; simp only [hA, UpperHalfPlane.ofComplex_apply]
  have hmaster := Work.Asymptotics.Kfun_mul_slope_eq_AfunFun ℓ d hd τ ζ hj_ne
  -- `Φ u = (u - u₀) K(τ,ζ)`
  have hΦu : Φ u = (u - u₀) * Work.Kernels.Kfun ℓ d τ ζ := by
    have hKfun_eq : Work.Kernels.Kfun ℓ d τ ζ
        = A u / (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ) := by
      rw [eq_div_iff (sub_ne_zero.mpr hj_ne), hA_u]
      exact hmaster
    show -(A u) / (dslope J u₀ u) = (u - u₀) * Work.Kernels.Kfun ℓ d τ ζ
    rw [hg_u, hKfun_eq]
    have h2 : u - u₀ ≠ 0 := sub_ne_zero.mpr hu_ne
    have h3 : Work.Kernels.jInvariantFun ζ - Work.Kernels.jInvariantFun τ ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm hj_ne)
    field_simp
    ring
  have hfinal : dslope Φ u₀ u
      = Work.Kernels.Kfun ℓ d τ ζ - c * ((u - u₀)⁻¹) := by
    rw [dslope_of_ne _ hu_ne, slope_def_field, div_eq_inv_mul, hΦu, hΦu₀]
    have h2 : u - u₀ ≠ 0 := sub_ne_zero.mpr hu_ne
    field_simp
  have hb : ‖dslope Φ u₀ u‖ ≤ ‖deriv Φ u₀‖ + 1 :=
    hδ₁ (show dist u u₀ < δ₁ from by rw [dist_eq_norm]; linarith)
  rw [hfinal] at hb
  simpa only [hu, hu₀] using hb

/-- **Boundedness of the principal part of the kernel at the translate poles `(n:ℝ) +ᵥ w`.**

For `n = ±1`, `w ∈ ℍ` with `j'(w) ≠ 0`, the slice `ζ ↦ K^{(d)}((n:ℝ) +ᵥ w, ζ)` has a simple
pole at `ζ = w` with residue `n/(2π)` and a bounded remainder: there are `δ > 0` and `B ≥ 0`
with

  `‖K^{(d)}((n:ℝ) +ᵥ w, ζ) - (n/2π)(ζ - w)⁻¹‖ ≤ B`

for every `ζ ∈ ℍ` with `0 < ‖ζ - w‖ < δ`. -/
theorem Kfun_pp_bounded_near_pole (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (w : UpperHalfPlane) (n : ℤ) (hn : n = 1 ∨ n = -1)
    (hjp : Work.Residues.jprime w ≠ 0) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 ≤ B ∧ ∀ ζ : UpperHalfPlane,
      ‖(ζ : ℂ) - (w : ℂ)‖ < δ → ζ ≠ w →
      ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
          - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((ζ : ℂ) - (w : ℂ))⁻¹)‖ ≤ B := by
  rcases hn with rfl | rfl
  · refine exists_bound_Kfun_residue_snd ℓ d hd _ w _ ?_ hjp ?_
    · simpa using Work.Kernels.KernelFacts.jInvariantFun_vadd_one w
    · simpa using Work.Asymptotics.AfunFun_vadd_int_of ℓ d hd 1 (Or.inl rfl) w
  · refine exists_bound_Kfun_residue_snd ℓ d hd _ w _ ?_ hjp ?_
    · simpa using Work.Residues.jInvariantFun_vadd_neg_one w
    · simpa using Work.Asymptotics.AfunFun_vadd_int_of ℓ d hd (-1) (Or.inr rfl) w

end Work.Asymptotics.SpikeTile
