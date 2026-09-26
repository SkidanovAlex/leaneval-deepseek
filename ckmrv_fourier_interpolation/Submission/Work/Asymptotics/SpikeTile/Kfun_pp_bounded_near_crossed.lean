import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Kaxis_principal_part_bound

namespace Work.Asymptotics.SpikeTile

open UpperHalfPlane

noncomputable section

/-!
# Boundedness of the kernel near a crossed orbit point

The CKMRV kernel `z ↦ K^{(d)}(τ,z)` (with `τ = n +ᵥ w`, `n = ±1`) has a simple pole at every
point `ζ` of the modular orbit of `τ`, i.e. at every `ζ` with `j ζ = j τ`; the residue there is
`-AfunFun ℓ d τ ζ / j' ζ` (`Work.Residues.hasResidue_of_cleared`).  At a *crossed* orbit point
`ζc ≠ τ` this residue vanishes (`Work.Asymptotics.AfunFun_crossed_vanish`), so the pole is
removable and the kernel is bounded near `ζc`.  Since the principal part
`(n/2π)(· - w)⁻¹` subtracted in the tile window is holomorphic near `ζc` (because `ζc ≠ w`),
the difference is bounded as well — which is the statement of `Kfun_pp_bounded_near_crossed`.

The proof is the quantitative version of "the residue vanishes": writing everything through the
chart `u ↦ u` of `ℂ` via `UpperHalfPlane.ofComplex`,

* `A(u) = AfunFun ℓ d τ (ofComplex u)` is holomorphic at `uc = (ζc : ℂ)` with `A uc = 0`, so
  `‖A u‖ ≤ L ‖u - uc‖` there (a strict derivative gives a local Lipschitz bound);
* `J(u) = j (ofComplex u)` is holomorphic at `uc` with `J' uc = jprime ζc ≠ 0`, so
  `c ‖u - uc‖ ≤ ‖J u - J uc‖` there (`exists_lipschitz_lower_bound_of_hasStrictDerivAt`);

and the master identity `K(τ,z)·(j τ - j z) = AfunFun ℓ d τ z` off the divisor identifies
`K(τ,ζ)` with `-A(ζ)/(J(ζ) - J(ζc))`, whose norm is at most `L/c`.
-/

/-- **A strict derivative gives a local Lipschitz upper bound.**  If `f : ℂ → ℂ` is strictly
differentiable at `x`, then near `x` the increment `f y - f x` is dominated by `‖y - x‖`. -/
lemma exists_lipschitz_upper_bound_of_hasStrictDerivAt {f : ℂ → ℂ} {x f' : ℂ}
    (h : HasStrictDerivAt f f' x) :
    ∃ ρ L : ℝ, 0 < ρ ∧ 0 ≤ L ∧ ∀ y : ℂ, ‖y - x‖ < ρ → ‖f y - f x‖ ≤ L * ‖y - x‖ := by
  have hlo := h.hasStrictFDerivAt.isLittleO
  obtain ⟨ρ, hρ, hb⟩ :=
    Metric.eventually_nhds_iff.mp (hlo.bound (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨ρ, ‖f'‖ + 1 / 2, hρ, by positivity, fun y hy => ?_⟩
  have hp : dist (y, x) (x, x) < ρ := by
    rw [Prod.dist_eq]
    refine max_lt ?_ ?_
    · rwa [dist_eq_norm]
    · rw [dist_eq_norm, sub_self, norm_zero]; exact hρ
  have h1 := hb hp
  have h2 : ‖(ContinuousLinearMap.toSpanSingleton ℂ f') (y - x)‖ = ‖f'‖ * ‖y - x‖ := by
    rw [ContinuousLinearMap.toSpanSingleton_apply, norm_smul, mul_comm]
  have h3 : ‖f y - f x‖ ≤ ‖f y - f x - (ContinuousLinearMap.toSpanSingleton ℂ f') (y - x)‖
      + ‖(ContinuousLinearMap.toSpanSingleton ℂ f') (y - x)‖ := by
    have h4 := norm_add_le (f y - f x - (ContinuousLinearMap.toSpanSingleton ℂ f') (y - x))
      ((ContinuousLinearMap.toSpanSingleton ℂ f') (y - x))
    rw [show f y - f x - (ContinuousLinearMap.toSpanSingleton ℂ f') (y - x)
        + (ContinuousLinearMap.toSpanSingleton ℂ f') (y - x) = f y - f x from by ring] at h4
    exact h4
  rw [h2] at h3
  have h5 : ‖f y - f x - (ContinuousLinearMap.toSpanSingleton ℂ f') (y - x)‖
      ≤ 1 / 2 * ‖y - x‖ := h1
  nlinarith [norm_nonneg (y - x), norm_nonneg f']

theorem Kfun_pp_bounded_near_crossed (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (w : UpperHalfPlane) (n : ℤ) (hn : n = 1 ∨ n = -1)
    (ζc : UpperHalfPlane)
    (hj : Work.Kernels.jInvariantFun ζc = Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w))
    (hAf : Work.Asymptotics.AfunFun ℓ d ((n : ℝ) +ᵥ w) ζc = 0)
    (hjp : Work.Residues.jprime ζc ≠ 0) (hne : ζc ≠ w) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 ≤ B ∧ ∀ ζ : UpperHalfPlane,
      ‖(ζ : ℂ) - (ζc : ℂ)‖ < δ → ζ ≠ ζc →
      ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
          - ((n : ℂ) / (2 * (Real.pi : ℂ))) * (((ζ : ℂ) - (w : ℂ))⁻¹)‖ ≤ B := by
  classical
  set τ : UpperHalfPlane := (n : ℝ) +ᵥ w with hτ
  have hAfτ : Work.Asymptotics.AfunFun ℓ d τ ζc = 0 := by rw [hτ]; exact hAf
  have hjτ : Work.Kernels.jInvariantFun ζc = Work.Kernels.jInvariantFun τ := by
    rw [hτ]; exact hj
  set A : ℂ → ℂ := Work.Asymptotics.AfunFun ℓ d τ ∘ (⇑UpperHalfPlane.ofComplex) with hAdef
  set J : ℂ → ℂ := Work.Kernels.jInvariantFun ∘ (⇑UpperHalfPlane.ofComplex) with hJdef
  set uc : ℂ := (ζc : ℂ) with huc
  have hucim : 0 < uc.im := by rw [huc, UpperHalfPlane.coe_im]; exact ζc.im_pos
  -- Analyticity of the two chart functions
  have hAan : AnalyticAt ℂ A uc := by
    have hdA : DifferentiableOn ℂ A {z : ℂ | 0 < z.im} :=
      (UpperHalfPlane.mdifferentiable_iff
        (f := fun z : ℍ => Work.Asymptotics.AfunFun ℓ d τ z)).mp
        (Work.Asymptotics.mdifferentiable_AfunFun_snd ℓ d hd τ)
    exact (hdA.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet) uc
      (by simpa using hucim)
  have hJan : AnalyticAt ℂ J uc := by
    have hdJ : DifferentiableOn ℂ J {z : ℂ | 0 < z.im} :=
      (UpperHalfPlane.mdifferentiable_iff
        (f := fun z : ℍ => Work.Kernels.jInvariantFun z)).mp
        Work.Asymptotics.mdifferentiable_jInvariantFun
    exact (hdJ.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet) uc
      (by simpa using hucim)
  have hJderiv : deriv J uc ≠ 0 := by
    rw [hJdef, huc, Work.Asymptotics.deriv_jInvariantFun_ofComplex ζc]
    exact hjp
  -- the two local bounds
  obtain ⟨ρA, LA, hρA, hLA, hAb⟩ :=
    exists_lipschitz_upper_bound_of_hasStrictDerivAt hAan.hasStrictDerivAt
  obtain ⟨ρJ, hρJ, cJ, hcJ, hJb⟩ :=
    Work.Asymptotics.MiddleRange.exists_lipschitz_lower_bound_of_hasStrictDerivAt
      hJan.hasStrictDerivAt hJderiv
  -- `ζc ≠ w`
  have hsep : 0 < ‖uc - (w : ℂ)‖ := by
    rw [norm_pos_iff]
    intro h
    have h1 : (ζc : ℂ) = (w : ℂ) := by rw [← huc]; exact sub_eq_zero.mp h
    exact hne (UpperHalfPlane.ext h1)
  set c₀ : ℂ := (n : ℂ) / (2 * (Real.pi : ℂ)) with hc₀def
  refine ⟨min (min ρA ρJ) (‖uc - (w : ℂ)‖ / 2),
    LA / cJ + ‖c₀‖ * (2 / ‖uc - (w : ℂ)‖), ?_, ?_, ?_⟩
  · exact lt_min (lt_min hρA hρJ) (by positivity)
  · exact add_nonneg (div_nonneg hLA hcJ.le)
      (mul_nonneg (norm_nonneg _) (div_nonneg (by norm_num) hsep.le))
  -- the chart evaluations
  have hAcoe : ∀ ζ : ℍ, A (ζ : ℂ) = Work.Asymptotics.AfunFun ℓ d τ ζ := by
    intro ζ
    simp only [hAdef, Function.comp_apply, UpperHalfPlane.ofComplex_apply]
  have hAuc : A uc = 0 := by
    rw [huc]
    simp only [hAdef, Function.comp_apply, UpperHalfPlane.ofComplex_apply]
    exact hAfτ
  have hJcoe : ∀ ζ : ℍ, J (ζ : ℂ) = Work.Kernels.jInvariantFun ζ := by
    intro ζ
    simp only [hJdef, Function.comp_apply, UpperHalfPlane.ofComplex_apply]
  have hJuc : J uc = Work.Kernels.jInvariantFun τ := by
    rw [huc]
    simp only [hJdef, Function.comp_apply, UpperHalfPlane.ofComplex_apply]
    exact hjτ
  intro ζ hζ hneζ
  have hζA : ‖(ζ : ℂ) - uc‖ < ρA :=
    lt_of_lt_of_le hζ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hζJ : ‖(ζ : ℂ) - uc‖ < ρJ :=
    lt_of_lt_of_le hζ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hζw : ‖(ζ : ℂ) - uc‖ < ‖uc - (w : ℂ)‖ / 2 :=
    lt_of_lt_of_le hζ (min_le_right _ _)
  have hζne : (ζ : ℂ) ≠ uc := by
    intro h
    rw [huc] at h
    exact hneζ (UpperHalfPlane.ext h)
  have hposnorm : 0 < ‖(ζ : ℂ) - uc‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζne)
  -- the numerator bound
  have hnum : ‖Work.Asymptotics.AfunFun ℓ d τ ζ‖ ≤ LA * ‖(ζ : ℂ) - uc‖ := by
    have h := hAb (ζ : ℂ) hζA
    rwa [hAcoe ζ, hAuc, sub_zero] at h
  -- the denominator bound
  have hden : cJ * ‖(ζ : ℂ) - uc‖ ≤
      ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖ := by
    have h := hJb (ζ : ℂ) uc hζJ (by rw [sub_self, norm_zero]; exact hρJ)
    rw [hJcoe ζ, hJuc,
      norm_sub_rev (Work.Kernels.jInvariantFun ζ) (Work.Kernels.jInvariantFun τ)] at h
    exact h
  have hjnz : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ := by
    intro h0
    have h1 : ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖ = 0 := by
      rw [h0, sub_self, norm_zero]
    have h2 := mul_pos hcJ hposnorm
    linarith [hden]
  -- the master identity, solved for the kernel
  have hKval : Work.Kernels.Kfun ℓ d τ ζ =
      Work.Asymptotics.AfunFun ℓ d τ ζ
        / (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ) := by
    rw [eq_div_iff (sub_ne_zero.mpr hjnz)]
    exact Work.Asymptotics.Kfun_mul_slope_eq_AfunFun ℓ d hd τ ζ hjnz
  have hKbound : ‖Work.Kernels.Kfun ℓ d τ ζ‖ ≤ LA / cJ := by
    have hdenpos : 0 < ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖ := by
      have h2 := mul_pos hcJ hposnorm
      linarith [hden]
    rw [hKval, norm_div, div_le_iff₀ hdenpos]
    have hstep : ‖(ζ : ℂ) - uc‖ ≤
        ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖ / cJ := by
      rw [le_div_iff₀ hcJ]
      calc ‖(ζ : ℂ) - uc‖ * cJ = cJ * ‖(ζ : ℂ) - uc‖ := by ring
        _ ≤ _ := hden
    calc ‖Work.Asymptotics.AfunFun ℓ d τ ζ‖ ≤ LA * ‖(ζ : ℂ) - uc‖ := hnum
      _ ≤ LA * (‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖ / cJ) :=
          mul_le_mul_of_nonneg_left hstep hLA
      _ = (LA / cJ) * ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ‖ := by ring
  -- the principal part term is bounded near `ζc`
  have hpp : ‖c₀ * ((ζ : ℂ) - (w : ℂ))⁻¹‖ ≤ ‖c₀‖ * (2 / ‖uc - (w : ℂ)‖) := by
    have hnormζw : ‖uc - (w : ℂ)‖ / 2 ≤ ‖(ζ : ℂ) - (w : ℂ)‖ := by
      have h1 : ‖uc - (w : ℂ)‖ ≤ ‖uc - (ζ : ℂ)‖ + ‖(ζ : ℂ) - (w : ℂ)‖ := by
        have h := norm_add_le (uc - (ζ : ℂ)) ((ζ : ℂ) - (w : ℂ))
        rwa [show uc - (ζ : ℂ) + ((ζ : ℂ) - (w : ℂ)) = uc - (w : ℂ) from by ring] at h
      have h2 : ‖uc - (ζ : ℂ)‖ = ‖(ζ : ℂ) - uc‖ := norm_sub_rev _ _
      linarith [hζw]
    have hposζw : 0 < ‖(ζ : ℂ) - (w : ℂ)‖ := lt_of_lt_of_le (half_pos hsep) hnormζw
    rw [norm_mul, norm_inv]
    have hinv : (‖(ζ : ℂ) - (w : ℂ)‖)⁻¹ ≤ (‖uc - (w : ℂ)‖ / 2)⁻¹ :=
      (inv_le_inv₀ hposζw (by positivity)).mpr hnormζw
    calc ‖c₀‖ * (‖(ζ : ℂ) - (w : ℂ)‖)⁻¹
        ≤ ‖c₀‖ * (‖uc - (w : ℂ)‖ / 2)⁻¹ := mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
      _ = ‖c₀‖ * (2 / ‖uc - (w : ℂ)‖) := by rw [inv_div]
  calc ‖Work.Kernels.Kfun ℓ d τ ζ - c₀ * ((ζ : ℂ) - (w : ℂ))⁻¹‖
      ≤ ‖Work.Kernels.Kfun ℓ d τ ζ‖ + ‖c₀ * ((ζ : ℂ) - (w : ℂ))⁻¹‖ := norm_sub_le _ _
    _ ≤ LA / cJ + ‖c₀‖ * (2 / ‖uc - (w : ℂ)‖) := add_le_add hKbound hpp

end

end Work.Asymptotics.SpikeTile
