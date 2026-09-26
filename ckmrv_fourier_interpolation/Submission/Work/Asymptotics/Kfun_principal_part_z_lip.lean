/-
# The principal part of the CKMRV kernel in the second variable, at the translate pole

This file proves `Work.Asymptotics.Kfun_principal_part_z_lip`: for `n = ±1` and `τ` near
`n + i s₀` (`s₀ > 0`), the function `z ↦ K^{(d)}(τ,z)` has at the point `z₀ = τ - n` a simple
pole with residue exactly `n/(2π)` whose holomorphic remainder is *bounded*:

  `‖K^{(d)}(τ,z)·(z - z₀) - n/(2π)‖ ≤ C‖z - z₀‖`

with `C` uniform in `τ` in a neighbourhood of the two "bad lines" `Re τ = ±1`.

## Structure of the proof

* `Work.Asymptotics.AfunFun` and the master identity
  `K^{(d)}(τ,z)·(j τ - j z) = AfunFun τ z = (AfunPlus d z τ + AfunMinus ℓ d z τ)/2` off the
  divisor.
* The *value identity* `AfunFun τ (τ - n) = -(n/2π)·j'(τ - n)` for `n = ±1`; for `n = 1` this is
  `AfunPlus_vadd_one_eq` (the files are imported here) and for `n = -1` it is the `T⁻¹`
  companion `Work.Residues.AfunPlus_neg_one`/`AfunMinus_neg_one`.
* `norm_le_of_deriv_eq_zero`: a holomorphic function with a double zero at `c` is `O(‖u-c‖²)`
  (Cauchy's estimate, proved with `Complex.dslope` and the maximum modulus principle).
* The function `M(u) = A(τ,u)(u - z₀) + (n/2π)(j u - j z₀)` has a double zero at `z₀`
  (`M(z₀) = 0` and `deriv M z₀ = 0` by the value identity), and on the circle `‖u - z₀‖ = δ`
  it is bounded by `(C_A + L/2π)δ` using the joint continuity of `AfunFun`
  (`Work.Asymptotics.continuous_AfunFun`) and the local Lipschitz continuity of `j`
  (`Work.Asymptotics.lipschitz_jInvariantFun_local`).
* Finally `K^{(d)}(τ,z)(z - z₀) - n/(2π) = -M(z)/(j z - j z₀)`, and
  `Work.Asymptotics.exists_lower_bound_jDiff` provides the uniform lower bound
  `c₀‖z - z₀‖ ≤ ‖j z - j τ‖` on the region, which is the quantitative shadow of the fact that
  the pole is simple.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Residues.ResidueKernel
import Submission.Work.Residues.ResidueTheoremMinus
import Submission.Work.Residues.normalizedDeriv_jInvariantFun
import Submission.Work.Asymptotics.MiddleRange.exists_diffQuotient_lower
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Asymptotics.exists_lower_bound_jDiff
import Submission.Work.Asymptotics.continuous_AfunFun
import Submission.Work.Asymptotics.lipschitz_jInvariantFun_local
import Submission.Work.Residues.AfunPlus_neg_one
import Submission.Work.Residues.AfunMinus_neg_one

noncomputable section
open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle
open Filter
open scoped Topology

namespace Work.Asymptotics
open Work.Kernels Work.Residues

/-- `(1:ℝ) +ᵥ ((-1:ℝ) +ᵥ τ) = τ`. -/
lemma vadd_one_vadd_neg (τ : ℍ) : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_vadd]
  push_cast
  ring

/-- `(-1:ℝ) +ᵥ ((1:ℝ) +ᵥ τ) = τ`. -/
lemma vadd_neg_vadd_one (τ : ℍ) : (-1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ) = τ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_vadd]
  push_cast
  ring

/-- `j` is unchanged when the argument is shifted by `n = ±1`. -/
lemma jInvariantFun_neg_vadd (τ : ℍ) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    jInvariantFun ((-(n : ℝ)) +ᵥ τ) = jInvariantFun τ := by
  rcases hn with rfl | rfl
  · have h : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ := vadd_one_vadd_neg τ
    rw [show ((-(1 : ℤ) : ℝ)) = (-1 : ℝ) by norm_num]
    rw [← KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ τ), h]
  · rw [show ((-(-1 : ℤ) : ℝ)) = (1 : ℝ) by norm_num]
    exact KernelFacts.jInvariantFun_vadd_one τ

end Work.Asymptotics

namespace Work.Asymptotics
open Work.Kernels Work.Residues

lemma mdifferentiable_jInvariantFun : MDiff jInvariantFun :=
  ((ModularFormClass.holo ModularForm.E₄).pow 3).div (CuspFormClass.holo CuspForm.discriminant)
    (fun z => ClassicalFacts.DeltaFun_ne_zero z)

lemma mdifferentiableAt_AfunPlus_snd (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : ℍ) (z : ℍ) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun w : ℍ => AfunPlus d w τ) z := by
  have hK : MDiff (fun w : ℍ => KPlusClear d τ w) := (KernelGrowth.KPlusClear_growth_z d hd τ).1
  have hD : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun w : ℍ => DeltaFun τ * DeltaFun w ^ dpow d) z :=
    mdifferentiableAt_const.mul ((ClassicalFacts.DeltaFun_mem_InP.1 z).pow _)
  refine MDifferentiableAt.div ?_ ?_ ?_
  · exact hK z
  · exact hD
  · exact mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero τ)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero z))

lemma mdifferentiableAt_AfunMinus_snd (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) (z : ℍ) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun w : ℍ => AfunMinus ℓ d w τ) z := by
  have hK : MDiff (fun w : ℍ => KMinusClear ℓ d τ w) :=
    (KernelGrowth.KMinusClear_growth_z ℓ d hd τ).1
  have hD : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun w : ℍ => DeltaFun τ * DeltaFun w ^ dpow d) z :=
    mdifferentiableAt_const.mul ((ClassicalFacts.DeltaFun_mem_InP.1 z).pow _)
  refine MDifferentiableAt.div ?_ ?_ ?_
  · exact hK z
  · exact hD
  · exact mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero τ)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero z))

lemma mdifferentiable_AfunFun_snd (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : ℍ) :
    MDiff (fun w : ℍ => AfunFun ℓ d τ w) := by
  intro z
  have h1 := mdifferentiableAt_AfunPlus_snd d hd τ z
  have h2 := mdifferentiableAt_AfunMinus_snd ℓ d hd τ z
  have h3 : (fun w : ℍ => AfunFun ℓ d τ w)
      = fun w : ℍ => (AfunPlus d w τ + AfunMinus ℓ d w τ) / 2 := rfl
  rw [h3]
  exact (h1.add h2).div mdifferentiableAt_const (by norm_num)

end Work.Asymptotics

namespace Work.Asymptotics
open Work.Kernels Work.Residues

lemma dslope_self_eq' {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f : 𝕜 → E) (a : 𝕜) :
    dslope f a a = deriv f a := by
  simp [dslope]

theorem norm_le_of_deriv_eq_zero {c : ℂ} {R B : ℝ} {M : ℂ → ℂ} (hR : 0 < R)
    (hM : DifferentiableOn ℂ M (Metric.ball c (2 * R)))
    (h0 : M c = 0) (h1 : deriv M c = 0)
    (hB : ∀ w : ℂ, ‖w - c‖ = R → ‖M w‖ ≤ B) :
    ∀ u : ℂ, ‖u - c‖ ≤ R → ‖M u‖ ≤ B * ‖u - c‖ ^ 2 / R ^ 2 := by
  have hmem : Metric.ball c (2 * R) ∈ nhds c :=
    Metric.isOpen_ball.mem_nhds (by simp [hR])
  have hd1 : DifferentiableOn ℂ (dslope M c) (Metric.ball c (2 * R)) :=
    (Complex.differentiableOn_dslope (f := M) (s := Metric.ball c (2*R)) hmem).mpr hM
  have hd2 : DifferentiableOn ℂ (dslope (dslope M c) c) (Metric.ball c (2 * R)) :=
    (Complex.differentiableOn_dslope (f := dslope M c) (s := Metric.ball c (2*R)) hmem).mpr hd1
  set g : ℂ → ℂ := dslope (dslope M c) c with hg
  have hg_diff : DifferentiableOn ℂ g (Metric.ball c (2*R)) := hd2
  have hg_diff_R : DifferentiableOn ℂ g (Metric.ball c R) :=
    hg_diff.mono (Metric.ball_subset_ball (by linarith))
  have hcont : ContinuousOn g (closure (Metric.ball c R)) := by
    refine hg_diff.continuousOn.mono ?_
    rw [closure_ball c hR.ne']
    exact Metric.closedBall_subset_ball (by linarith)
  have hdcl : DiffContOnCl ℂ g (Metric.ball c R) := ⟨hg_diff_R, hcont⟩
  have hfr : ∀ w ∈ frontier (Metric.ball c R), ‖g w‖ ≤ B / R ^ 2 := by
    rw [frontier_ball c hR.ne']
    intro w hw
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    have hwne : w ≠ c := by
      intro h; rw [h] at hw; simp at hw; linarith
    have hgw : g w = (w - c)⁻¹ * ((w-c)⁻¹ * M w) := by
      rw [hg]
      rw [dslope_of_ne _ hwne, slope_def_field]
      rw [dslope_of_ne _ hwne, slope_def_field, h0]
      simp only [sub_zero]
      rw [dslope_self_eq', h1]
      ring
    have hBw := hB w hw
    have hpos : (0:ℝ) < R ^ 2 := by positivity
    rw [hgw, norm_mul, norm_mul, norm_inv, hw]
    rw [div_eq_mul_inv]
    have h1' : R⁻¹ * (R⁻¹ * ‖M w‖) = ‖M w‖ / R ^ 2 := by
      field_simp
    rw [h1']
    exact div_le_div_of_nonneg_right hBw hpos.le
  intro u hu
  have hgu : ‖g u‖ ≤ B / R ^ 2 := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdcl hfr ?_
    rw [closure_ball c hR.ne', Metric.mem_closedBall, dist_eq_norm]
    exact hu
  have hds : dslope M c c = 0 := by rw [dslope_self_eq', h1]
  have hMu : M u = (u - c)^2 * g u := by
    rcases eq_or_ne u c with rfl | hne
    · rw [h0]; simp [hg]
    · have hA : dslope M c u = (M u - M c) / (u - c) := by
        rw [dslope_of_ne _ hne, slope_def_field]
      have hB : dslope (dslope M c) c u = (dslope M c u - dslope M c c) / (u - c) := by
        rw [dslope_of_ne _ hne, slope_def_field]
      rw [hg, hB, hA, h0, hds, sub_zero]
      field_simp
      ring
  rw [hMu, norm_mul, norm_pow, div_eq_mul_inv]
  calc ‖u - c‖ ^ 2 * ‖g u‖ ≤ ‖u - c‖ ^ 2 * (B / R ^ 2) :=
        mul_le_mul_of_nonneg_left hgu (by positivity)
    _ = B * ‖u - c‖ ^ 2 * (R ^ 2)⁻¹ := by ring

end Work.Asymptotics

namespace Work.Asymptotics
open Work.Kernels Work.Residues

/-- The value identity at the pole `z₀ = τ - n`, `n = ±1`: `AfunFun τ (τ - n) = -(n/2π) j'(τ - n)`. -/
lemma AfunFun_neg_vadd (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : ℍ) (n : ℤ)
    (hn : n = 1 ∨ n = -1)
    (hP : ∀ z : ℍ, AfunPlus d z ((-1 : ℝ) +ᵥ z) = (1 / (2 * Real.pi)) * jprime z)
    (hM : ∀ z : ℍ, AfunMinus ℓ d z ((-1 : ℝ) +ᵥ z) = (1 / (2 * Real.pi)) * jprime z) :
    AfunFun ℓ d τ ((-(n : ℝ)) +ᵥ τ) = -((n : ℂ) / (2 * Real.pi)) * jprime ((-(n : ℝ)) +ᵥ τ) := by
  rcases hn with rfl | rfl
  · rw [show ((-(1 : ℤ) : ℝ)) = (-1 : ℝ) by norm_num]
    have h1 := AfunFun_vadd_one ℓ d hd ((-1 : ℝ) +ᵥ τ)
    rw [vadd_one_vadd_neg] at h1
    rw [h1]
    norm_num
  · rw [show ((-(-1 : ℤ) : ℝ)) = (1 : ℝ) by norm_num]
    have h1 : AfunPlus d ((1 : ℝ) +ᵥ τ) τ = (1 / (2 * Real.pi)) * jprime ((1 : ℝ) +ᵥ τ) := by
      have := hP ((1 : ℝ) +ᵥ τ)
      rwa [vadd_neg_vadd_one] at this
    have h2 : AfunMinus ℓ d ((1 : ℝ) +ᵥ τ) τ = (1 / (2 * Real.pi)) * jprime ((1 : ℝ) +ᵥ τ) := by
      have := hM ((1 : ℝ) +ᵥ τ)
      rwa [vadd_neg_vadd_one] at this
    rw [AfunFun, h1, h2]
    push_cast
    field_simp
    ring

end Work.Asymptotics


namespace Work.Asymptotics
open Work.Kernels Work.Residues

/-- The continuity of `ofComplex` on the upper half plane. -/
lemma continuousOn_ofComplex_im_pos :
    ContinuousOn (fun z : ℂ => UpperHalfPlane.ofComplex z) {z : ℂ | 0 < z.im} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : ({z : ℂ | 0 < z.im}.domRestrict (fun z : ℂ => UpperHalfPlane.ofComplex z))
      = fun z : {z : ℂ | 0 < z.im} => (⟨(z : ℂ), z.2⟩ : ℍ) := by
    funext z
    exact UpperHalfPlane.ofComplex_apply_of_im_pos z.2
  rw [h]
  exact continuous_subtype_val.upperHalfPlaneMk (fun z => z.2)

end Work.Asymptotics


namespace Work.Asymptotics
open Work.Kernels Work.Residues


lemma norm_le_re_im (a b : ℝ) : ‖(a : ℂ) + (b : ℂ) * Complex.I‖ ≤ |a| + |b| := by
  have := Complex.norm_le_abs_re_add_abs_im ((a:ℂ) + (b:ℂ)*Complex.I)
  simpa using this

lemma coe_sub_eq (τ : ℍ) (n : ℤ) (s₀ : ℝ) :
    (τ : ℂ) - ((n : ℂ) + (s₀ : ℂ) * Complex.I)
      = ((τ.re - (n : ℝ) : ℝ) : ℂ) + ((τ.im - s₀ : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] <;> ring

lemma coe_sub_eq' (τ : ℍ) (s₀ : ℝ) :
    (τ : ℂ) - (s₀ : ℂ) * Complex.I = ((τ.re : ℝ) : ℂ) + ((τ.im - s₀ : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im] <;> ring

theorem Kfun_principal_part_z_lip_of (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {s₀ : ℝ} (hs₀ : 0 < s₀)
    (hLB : ∃ δmax : ℝ, 0 < δmax ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δmax → ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (τ z : ℍ) (n : ℤ), (n = 1 ∨ n = -1) →
        |τ.im - s₀| < δ → |τ.re - (n : ℝ)| < δ →
        ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ < δ →
        (∃ c : ℝ, 0 < c ∧ ∀ ζ : ℍ,
          ‖(ζ : ℂ) - ((τ : ℂ) - (n : ℂ))‖ < δ → c ≤ ‖jprime ζ‖) →
        c₀ * ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ ≤ ‖jInvariantFun z - jInvariantFun τ‖)
    (hcont : Continuous (fun p : ℍ × ℍ => AfunFun ℓ d p.1 p.2))
    (hLipall : ∀ x : ℍ, ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ∀ y z : ℍ,
      ‖(y : ℂ) - (x : ℂ)‖ < r → ‖(z : ℂ) - (x : ℂ)‖ < r →
      ‖jInvariantFun y - jInvariantFun z‖ ≤ L * ‖(y : ℂ) - (z : ℂ)‖)
    (hP : ∀ z : ℍ, AfunPlus d z ((-1 : ℝ) +ᵥ z) = (1 / (2 * Real.pi)) * jprime z)
    (hM : ∀ z : ℍ, AfunMinus ℓ d z ((-1 : ℝ) +ᵥ z) = (1 / (2 * Real.pi)) * jprime z) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ (τ z : UpperHalfPlane) (n : ℤ),
      (n = 1 ∨ n = -1) → |τ.im - s₀| < δ → |τ.re - (n : ℝ)| < δ →
      ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ < δ →
      (∃ c : ℝ, 0 < c ∧ ∀ ζ : UpperHalfPlane, ‖(ζ : ℂ) - ((τ : ℂ) - (n : ℂ))‖ < δ →
        c ≤ ‖jprime ζ‖) →
      jInvariantFun τ ≠ jInvariantFun z →
      ‖Kfun ℓ d τ z * ((z : ℂ) - ((τ : ℂ) - (n : ℂ))) - (n : ℂ) / (2 * Real.pi)‖
        ≤ C * ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ := by
  obtain ⟨δLB, hδLBpos, hLB'⟩ := hLB
  set x₀ : ℍ := imagAxis s₀ hs₀ with hx₀def
  obtain ⟨rL, L, hrLpos, hLnn, hLip⟩ := hLipall x₀
  set d₀ : ℝ := min (min s₀ 1) rL / 64 with hd₀def
  have hminpos : 0 < min (min s₀ 1) rL := lt_min (lt_min hs₀ one_pos) hrLpos
  have hd₀pos : 0 < d₀ := by rw [hd₀def]; exact div_pos hminpos (by norm_num)
  have hd₀le : d₀ ≤ min (min s₀ 1) rL := by
    rw [hd₀def, div_le_iff₀ (by norm_num : (0:ℝ) < 64)]
    nlinarith [hminpos]
  have hd₀s : d₀ ≤ s₀ := le_trans hd₀le (le_trans (min_le_left _ _) (min_le_left _ _))
  have hd₀1 : d₀ ≤ 1 := le_trans hd₀le (le_trans (min_le_left _ _) (min_le_right _ _))
  have hd₀rL : d₀ ≤ rL := le_trans hd₀le (min_le_right _ _)
  -- the compact set
  set x₀c : ℂ := (s₀ : ℂ) * Complex.I with hx₀cdef
  have hx₀coe : (x₀ : ℂ) = x₀c := by rw [hx₀def, hx₀cdef]; rfl
  set Kc : Set ℂ := Metric.closedBall x₀c 4 ∩ {z : ℂ | s₀ / 2 ≤ z.im} with hKcdef
  have hKc_compact : IsCompact Kc := by
    rw [hKcdef]
    exact IsCompact.of_isClosed_subset (isCompact_closedBall x₀c 4)
      (Metric.isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im))
      Set.inter_subset_left
  have hofc : ContinuousOn (fun z : ℂ => UpperHalfPlane.ofComplex z) Kc :=
    continuousOn_ofComplex_im_pos.mono (fun z hz => by
      rw [hKcdef] at hz
      have h2 : s₀ / 2 ≤ z.im := hz.2
      have h3 : (0:ℝ) < s₀ / 2 := by linarith
      exact lt_of_lt_of_le h3 h2)
  have hpair : ContinuousOn (fun p : ℂ × ℂ =>
      (UpperHalfPlane.ofComplex p.1, UpperHalfPlane.ofComplex p.2)) (Kc ×ˢ Kc) :=
    (hofc.comp continuous_fst.continuousOn (fun (p : ℂ × ℂ) (hp : p ∈ Kc ×ˢ Kc) => hp.1)).prodMk
      (hofc.comp continuous_snd.continuousOn (fun (p : ℂ × ℂ) (hp : p ∈ Kc ×ˢ Kc) => hp.2))
  obtain ⟨C_A₀, hC_A₀⟩ := (hKc_compact.prod hKc_compact).exists_bound_of_continuousOn
    (hcont.continuousOn.comp hpair (fun p hp => Set.mem_univ _))
  set C_A : ℝ := max C_A₀ 0 with hC_Adef
  have hC_A : ∀ τ w : ℍ, (τ : ℂ) ∈ Kc → (w : ℂ) ∈ Kc → ‖AfunFun ℓ d τ w‖ ≤ C_A := by
    intro τ w hτ hw
    have h0 := hC_A₀ ((τ : ℂ), (w : ℂ)) ⟨hτ, hw⟩
    have h2 : ‖AfunFun ℓ d τ w‖
        = ‖AfunFun ℓ d (UpperHalfPlane.ofComplex (τ : ℂ)) (UpperHalfPlane.ofComplex (w : ℂ))‖ := by
      rw [UpperHalfPlane.ofComplex_apply, UpperHalfPlane.ofComplex_apply]
    rw [h2]
    exact le_trans h0 (le_max_left _ _)
  -- the small δ
  set δ : ℝ := min (min d₀ δLB) (min rL s₀) / 64 with hδdef
  have hmpos : 0 < min (min d₀ δLB) (min rL s₀) :=
    lt_min (lt_min hd₀pos hδLBpos) (lt_min hrLpos hs₀)
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos hmpos (by norm_num)
  have hδle : δ ≤ min (min d₀ δLB) (min rL s₀) := by
    rw [hδdef, div_le_iff₀ (by norm_num : (0:ℝ) < 64)]
    nlinarith [hmpos]
  have hδd₀ : δ ≤ d₀ := le_trans hδle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδδLB : δ ≤ δLB := le_trans hδle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδrL : δ ≤ rL := le_trans hδle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδrL64 : δ ≤ rL / 64 := by
    rw [hδdef]
    exact div_le_div_of_nonneg_right (le_trans (min_le_right _ _) (min_le_left _ _)) (by norm_num)
  have hδs₀ : δ ≤ s₀ := le_trans hδle (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨c₀, hc₀pos, hc₀bd⟩ := hLB' δ hδpos hδδLB
  refine ⟨δ, (C_A + L / (2 * Real.pi)) / (c₀ * δ), hδpos, ?_, ?_⟩
  · positivity
  · intro τ z n hn hτim hτre hz hhyp hjne
    -- basic facts about the pole
    let z₀ : ℍ := (-(n : ℝ)) +ᵥ τ
    have hz₀coe : (z₀ : ℂ) = (τ : ℂ) - (n : ℂ) := by
      show (((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ) = (τ : ℂ) - (n : ℂ)
      rw [UpperHalfPlane.coe_vadd]
      push_cast
      ring
    have hx0eq : (x₀ : ℂ) = (s₀ : ℂ) * Complex.I := by rw [hx₀coe, hx₀cdef]
    rw [hz₀coe.symm]
    let zc : ℂ := (τ : ℂ) - ((n : ℂ) + (s₀ : ℂ) * Complex.I)
    have hz0x : (z₀ : ℂ) - ((s₀ : ℂ) * Complex.I) = zc := by
      rw [show zc = (τ : ℂ) - ((n : ℂ) + (s₀ : ℂ) * Complex.I) from rfl]
      rw [hz₀coe]; ring
    have hzc_norm : ‖zc‖ < 2*δ := by
      rw [show zc = (τ : ℂ) - ((n : ℂ) + (s₀ : ℂ) * Complex.I) from rfl, coe_sub_eq τ n s₀]
      have h4 := norm_le_re_im (τ.re - (n : ℝ)) (τ.im - s₀)
      linarith [h4, hτre, hτim]
    have htaux : (τ : ℂ) - ((s₀ : ℂ) * Complex.I) = zc + (n : ℂ) := by
      rw [show zc = (τ : ℂ) - ((n : ℂ) + (s₀ : ℂ) * Complex.I) from rfl]
      ring
    have hjτ : jInvariantFun τ = jInvariantFun z₀ := (jInvariantFun_neg_vadd τ n hn).symm
    have hjne' : jInvariantFun z ≠ jInvariantFun z₀ := by
      intro h; exact hjne (by rw [hjτ, h])
    have hz' : ‖(z : ℂ) - (z₀ : ℂ)‖ < δ := by rw [hz₀coe]; exact hz
    have hhyp' : ∃ c' : ℝ, 0 < c' ∧ ∀ ζ : ℍ, ‖(ζ : ℂ) - (z₀ : ℂ)‖ < δ → c' ≤ ‖jprime ζ‖ := by
      obtain ⟨c', hc', hc''⟩ := hhyp
      refine ⟨c', hc', fun ζ hζ => hc'' ζ ?_⟩
      rw [hz₀coe] at hζ; exact hζ
    have hval := AfunFun_neg_vadd ℓ d hd τ n hn hP hM
    have hz₀im : z₀.im = τ.im := by
      show ((((-(n : ℝ)) +ᵥ τ : ℍ) : ℂ).im) = τ.im
      rw [UpperHalfPlane.coe_vadd]
      simp [Complex.add_im]
    have hτim' : s₀ - δ < τ.im := by
      have h := (abs_lt.mp hτim).1; linarith
    have hτre' : |τ.re| < 1 + δ := by
      have h1 : |((n : ℝ))| = 1 := by rcases hn with h | h <;> rw [h] <;> norm_num
      have h2 : |τ.re| ≤ |τ.re - (n : ℝ)| + |(n : ℝ)| := by
        have := abs_add_le (τ.re - (n : ℝ)) (n : ℝ)
        rwa [sub_add_cancel] at this
      rw [h1] at h2; linarith
    have hd₀s64 : d₀ ≤ s₀ / 64 := by
      rw [hd₀def]
      exact div_le_div_of_nonneg_right (le_trans (min_le_left _ _) (min_le_left _ _)) (by norm_num)
    have hτ_im2 : s₀ / 2 < τ.im := by linarith [hτim', hδd₀, hd₀s64, hs₀]
    have hδsmall3 : 3 * δ < s₀ := by linarith [hδd₀, hd₀s64, hs₀]
    have hn1 : ‖(n : ℂ)‖ = 1 := by rcases hn with h | h <;> rw [h] <;> norm_num
    have hτKc : (τ : ℂ) ∈ Kc := by
      rw [hKcdef, Set.mem_inter_iff, Metric.mem_closedBall, dist_eq_norm]
      refine ⟨?_, ?_⟩
      · rw [htaux]
        have h4 : ‖zc + (n : ℂ)‖ ≤ ‖zc‖ + ‖(n : ℂ)‖ := norm_add_le _ _
        linarith [h4, hzc_norm, hn1, hδd₀, hd₀1]
      · simp only [Set.mem_ofPred_eq, UpperHalfPlane.coe_im]
        linarith [hτ_im2]
    have hz0Kc : (z₀ : ℂ) ∈ Kc := by
      rw [hKcdef, Set.mem_inter_iff, Metric.mem_closedBall, dist_eq_norm]
      refine ⟨?_, ?_⟩
      · rw [hz0x]
        linarith [hzc_norm, hδd₀, hd₀1]
      · simp only [Set.mem_ofPred_eq, UpperHalfPlane.coe_im, hz₀im]
        linarith [hτ_im2]
    -- the analytic functions
    set A : ℂ → ℂ := fun u => AfunFun ℓ d τ (UpperHalfPlane.ofComplex u) with hAdef
    set J : ℂ → ℂ := fun u => jInvariantFun (UpperHalfPlane.ofComplex u) with hJdef
    set M : ℂ → ℂ := fun u => A u * (u - (z₀ : ℂ))
        + ((n : ℂ) / (2 * Real.pi)) * (J u - J (z₀ : ℂ)) with hMdef
    have hz₀cim : (z₀ : ℂ).im = τ.im := by rw [hz₀coe]; simp [Complex.sub_im]
    have hδsmall : 2 * δ < s₀ / 2 := by linarith [hδd₀, hd₀s64, hs₀]
    have hball : Metric.ball (z₀ : ℂ) (2*δ) ⊆ {u : ℂ | 0 < u.im} := by
      intro u hu
      have h1 : dist u (z₀ : ℂ) < 2*δ := hu
      rw [dist_eq_norm] at h1
      have h2 : -‖u - (z₀ : ℂ)‖ ≤ (u - (z₀ : ℂ)).im := by
        have := Complex.abs_im_le_norm (u - (z₀ : ℂ))
        linarith [neg_le_of_abs_le this]
      simp only [Complex.sub_im] at h2
      rw [hz₀cim] at h2
      have h4 : τ.im - ‖u - (z₀ : ℂ)‖ ≤ u.im := by linarith [h2]
      have h5 : s₀ - 3*δ ≤ τ.im - ‖u - (z₀ : ℂ)‖ := by linarith [h1, hτim']
      have h6 : s₀ - 3*δ ≤ u.im := le_trans h5 h4
      have h7 : 0 < s₀ - 3*δ := by linarith [hδsmall3]
      exact lt_of_lt_of_le h7 h6
    have hA_holo : DifferentiableOn ℂ A {u : ℂ | 0 < u.im} := by
      have h := (UpperHalfPlane.mdifferentiable_iff (f := fun w : ℍ => AfunFun ℓ d τ w)).mp
        (mdifferentiable_AfunFun_snd ℓ d hd τ)
      simpa [hAdef, Function.comp_def] using h
    have hJ_holo : DifferentiableOn ℂ J {u : ℂ | 0 < u.im} := by
      have h := (UpperHalfPlane.mdifferentiable_iff (f := jInvariantFun)).mp
        mdifferentiable_jInvariantFun
      simpa [hJdef, Function.comp_def] using h
    have hA_diff : DifferentiableOn ℂ A (Metric.ball (z₀ : ℂ) (2*δ)) := hA_holo.mono hball
    have hJ_diff : DifferentiableOn ℂ J (Metric.ball (z₀ : ℂ) (2*δ)) := hJ_holo.mono hball
    have hM_diff : DifferentiableOn ℂ M (Metric.ball (z₀ : ℂ) (2*δ)) := by
      rw [hMdef]
      refine (hA_diff.mul ?_).add ((hJ_diff.sub ?_).const_mul ((n : ℂ) / (2 * Real.pi)))
      · exact (differentiableOn_id : DifferentiableOn ℂ (fun u : ℂ => u) _).sub
          (differentiableOn_const (z₀ : ℂ))
      · exact differentiableOn_const (J (z₀ : ℂ))
    have hM0 : M (z₀ : ℂ) = 0 := by rw [hMdef]; simp
    have hcball : (z₀ : ℂ) ∈ Metric.ball (z₀ : ℂ) (2*δ) := by
      rw [Metric.mem_ball, dist_self]; positivity
    have hcball_nhds : Metric.ball (z₀ : ℂ) (2*δ) ∈ nhds (z₀ : ℂ) :=
      Metric.isOpen_ball.mem_nhds hcball
    have hAz : A (z : ℂ) = AfunFun ℓ d τ z := by
      simp only [hAdef, UpperHalfPlane.ofComplex_apply]
    have hA_z0 : A (z₀ : ℂ) = -((n : ℂ) / (2 * Real.pi)) * jprime z₀ := by
      simp only [hAdef, UpperHalfPlane.ofComplex_apply]
      exact hval
    have hJ_z0 : deriv J (z₀ : ℂ) = jprime z₀ := deriv_jInvariantFun_ofComplex z₀
    have hMderiv : deriv M (z₀ : ℂ) = 0 := by
      have h1 : HasDerivAt (fun u : ℂ => A u * (u - (z₀ : ℂ))) (A (z₀ : ℂ)) (z₀ : ℂ) := by
        have h0 := (hA_diff.differentiableAt hcball_nhds).hasDerivAt.mul
          ((hasDerivAt_id (z₀ : ℂ)).sub_const (z₀ : ℂ))
        have hv : deriv A (z₀ : ℂ) * (id (z₀ : ℂ) - (z₀ : ℂ)) + A (z₀ : ℂ) * 1 = A (z₀ : ℂ) := by
          simp
        rw [hv] at h0
        exact h0
      have h2 : HasDerivAt (fun u : ℂ => ((n : ℂ) / (2 * Real.pi)) * (J u - J (z₀ : ℂ)))
          (((n : ℂ) / (2 * Real.pi)) * deriv J (z₀ : ℂ)) (z₀ : ℂ) := by
        exact ((hJ_diff.differentiableAt hcball_nhds).hasDerivAt.sub_const (J (z₀ : ℂ))).const_mul
          ((n : ℂ) / (2 * Real.pi))
      have hsum : HasDerivAt M (A (z₀ : ℂ) + ((n : ℂ) / (2 * Real.pi)) * deriv J (z₀ : ℂ))
          (z₀ : ℂ) := by
        rw [hMdef]; exact h1.add h2
      rw [hsum.deriv, hA_z0, hJ_z0]
      ring
    -- the bound on the circle
    have hLip_c : ∀ w : ℂ, ‖w - (z₀ : ℂ)‖ = δ → ‖J w - J (z₀ : ℂ)‖ ≤ L * δ := by
      intro w hw
      have hwim : 0 < w.im := by
        have h1 : -‖w - (z₀ : ℂ)‖ ≤ (w - (z₀ : ℂ)).im := by
          have := Complex.abs_im_le_norm (w - (z₀ : ℂ))
          linarith [neg_le_of_abs_le this]
        simp only [Complex.sub_im] at h1
        rw [hz₀cim] at h1
        rw [hw] at h1
        linarith [hτim', h1, hδsmall3]
      have hzcim : 0 < (z₀ : ℂ).im := by rw [hz₀cim]; linarith [hτim']
      have hw' : (UpperHalfPlane.ofComplex w : ℂ) = w := by
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos hwim, UpperHalfPlane.coe_mk]
      have hz0' : (UpperHalfPlane.ofComplex (z₀ : ℂ) : ℂ) = (z₀ : ℂ) := by
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos hzcim, UpperHalfPlane.coe_mk]
      have h1 : ‖(UpperHalfPlane.ofComplex w : ℂ) - (x₀ : ℂ)‖ < rL := by
        rw [hw', hx0eq]
        change ‖w - x₀c‖ < rL
        have h2 : ‖w - x₀c‖ ≤ ‖w - (z₀ : ℂ)‖ + ‖(z₀ : ℂ) - x₀c‖ := by
          calc ‖w - x₀c‖ = ‖(w - (z₀ : ℂ)) + ((z₀ : ℂ) - x₀c)‖ := by
                rw [show w - x₀c = (w - (z₀ : ℂ)) + ((z₀ : ℂ) - x₀c) by ring]
            _ ≤ _ := norm_add_le _ _
        rw [hz0x] at h2
        linarith [h2, hzc_norm, hw, hδrL64]
      have h2 : ‖(UpperHalfPlane.ofComplex (z₀ : ℂ) : ℂ) - (x₀ : ℂ)‖ < rL := by
        rw [hz0', hx0eq]
        change ‖(z₀ : ℂ) - x₀c‖ < rL
        rw [hz0x]
        linarith [hzc_norm, hδrL64]
      have h3 := hLip (UpperHalfPlane.ofComplex w) (UpperHalfPlane.ofComplex (z₀ : ℂ)) h1 h2
      rw [hw', hz0'] at h3
      rw [hw] at h3
      rw [hJdef]
      exact h3
    have hMbound : ∀ w : ℂ, ‖w - (z₀ : ℂ)‖ = δ →
        ‖M w‖ ≤ (C_A + L / (2*Real.pi)) * δ := by
      intro w hw
      have hwim : 0 < w.im := by
        have h1 : -‖w - (z₀ : ℂ)‖ ≤ (w - (z₀ : ℂ)).im := by
          have := Complex.abs_im_le_norm (w - (z₀ : ℂ))
          linarith [neg_le_of_abs_le this]
        simp only [Complex.sub_im] at h1
        rw [hz₀cim] at h1
        rw [hw] at h1
        linarith [hτim', h1, hδsmall3]
      have hwKc : w ∈ Kc := by
        rw [hKcdef, Set.mem_inter_iff, Metric.mem_closedBall, dist_eq_norm]
        refine ⟨?_, ?_⟩
        · have h2 : ‖w - x₀c‖ ≤ ‖w - (z₀ : ℂ)‖ + ‖(z₀ : ℂ) - x₀c‖ := by
            calc ‖w - x₀c‖ = ‖(w - (z₀ : ℂ)) + ((z₀ : ℂ) - x₀c)‖ := by
                  rw [show w - x₀c = (w - (z₀ : ℂ)) + ((z₀ : ℂ) - x₀c) by ring]
              _ ≤ _ := norm_add_le _ _
          rw [hz0x] at h2
          linarith [h2, hzc_norm, hw, hδd₀, hd₀1]
        · simp only [Set.mem_ofPred_eq]
          have h1 : -‖w - (z₀ : ℂ)‖ ≤ (w - (z₀ : ℂ)).im := by
            have := Complex.abs_im_le_norm (w - (z₀ : ℂ))
            linarith [neg_le_of_abs_le this]
          simp only [Complex.sub_im] at h1
          rw [hz₀cim] at h1
          rw [hw] at h1
          linarith [hτim', h1, hδsmall3]
      have hwA : ‖A w‖ ≤ C_A := by
        change ‖AfunFun ℓ d τ (UpperHalfPlane.ofComplex w)‖ ≤ C_A
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos hwim]
        exact hC_A τ ⟨w, hwim⟩ hτKc (by rw [UpperHalfPlane.coe_mk]; exact hwKc)
      have hwJ : ‖J w - J (z₀ : ℂ)‖ ≤ L * δ := hLip_c w hw
      rw [hMdef]
      have h1 : ‖A w * (w - (z₀ : ℂ)) + ((n : ℂ) / (2 * Real.pi)) * (J w - J (z₀ : ℂ))‖
          ≤ ‖A w‖ * ‖w - (z₀ : ℂ)‖ + ‖((n : ℂ) / (2 * Real.pi))‖ * ‖J w - J (z₀ : ℂ)‖ := by
        calc ‖A w * (w - (z₀ : ℂ)) + ((n : ℂ) / (2 * Real.pi)) * (J w - J (z₀ : ℂ))‖
            ≤ ‖A w * (w - (z₀ : ℂ))‖
              + ‖((n : ℂ) / (2 * Real.pi)) * (J w - J (z₀ : ℂ))‖ := norm_add_le _ _
          _ = ‖A w‖ * ‖w - (z₀ : ℂ)‖
              + ‖((n : ℂ) / (2 * Real.pi))‖ * ‖J w - J (z₀ : ℂ)‖ := by rw [norm_mul, norm_mul]
      have hnCn : ‖((n : ℂ) / (2 * Real.pi))‖ = 1 / (2 * Real.pi) := by
        rw [norm_div, hn1]
        have h2 : ‖((2 : ℂ) * (Real.pi : ℂ))‖ = 2 * Real.pi := by
          rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos]
        rw [h2]
      calc ‖A w * (w - (z₀ : ℂ)) + ((n : ℂ) / (2 * Real.pi)) * (J w - J (z₀ : ℂ))‖
          ≤ ‖A w‖ * ‖w - (z₀ : ℂ)‖ + ‖((n : ℂ) / (2 * Real.pi))‖ * ‖J w - J (z₀ : ℂ)‖ := h1
        _ ≤ C_A * δ + (1 / (2*Real.pi)) * (L * δ) := by
            rw [hnCn, hw]
            exact add_le_add (mul_le_mul_of_nonneg_right hwA (le_of_lt hδpos))
              (mul_le_mul_of_nonneg_left hwJ (by positivity))
        _ = (C_A + L / (2*Real.pi)) * δ := by ring
    -- the value identity on the diagonal and the final estimate
    have hMval : M (z : ℂ) = AfunFun ℓ d τ z * ((z : ℂ) - (z₀ : ℂ))
        + ((n : ℂ) / (2 * Real.pi)) * (jInvariantFun z - jInvariantFun z₀) := by
      have h1 : UpperHalfPlane.ofComplex (z : ℂ) = z := UpperHalfPlane.ofComplex_apply z
      have h2 : UpperHalfPlane.ofComplex (z₀ : ℂ) = z₀ := UpperHalfPlane.ofComplex_apply z₀
      simp only [hMdef, hAdef, hJdef, h1, h2]
    have hmB := norm_le_of_deriv_eq_zero hδpos hM_diff hM0 hMderiv hMbound (z : ℂ) (le_of_lt hz')
    have hkey : Kfun ℓ d τ z * ((z : ℂ) - (z₀ : ℂ)) - ((n : ℂ) / (2 * Real.pi))
        = - M (z : ℂ) / (jInvariantFun z - jInvariantFun z₀) := by
      have hmas' : Kfun ℓ d τ z * (jInvariantFun z₀ - jInvariantFun z) = A (z : ℂ) := by
        have hmas := Kfun_mul_slope_eq_AfunFun ℓ d hd τ z hjne
        rw [hjτ] at hmas
        rw [hAdef]
        simpa [UpperHalfPlane.ofComplex_apply] using hmas
      have hd1 : jInvariantFun z₀ - jInvariantFun z ≠ 0 := sub_ne_zero.mpr (Ne.symm hjne')
      have hd2 : jInvariantFun z - jInvariantFun z₀ ≠ 0 := sub_ne_zero.mpr hjne'
      have hKfun : Kfun ℓ d τ z = A (z : ℂ) / (jInvariantFun z₀ - jInvariantFun z) := by
        rw [eq_div_iff hd1]; exact hmas'
      rw [hKfun, hMval, hAz, eq_div_iff hd2]
      field_simp
      ring
    rw [hkey, norm_div, norm_neg]
    have hden : c₀ * ‖(z : ℂ) - (z₀ : ℂ)‖ ≤ ‖jInvariantFun z - jInvariantFun z₀‖ := by
      have h1 := hc₀bd τ z n hn hτim hτre hz hhyp
      rw [← hz₀coe] at h1
      rw [hjτ] at h1
      exact h1
    have hd2 : jInvariantFun z - jInvariantFun z₀ ≠ 0 := sub_ne_zero.mpr hjne'
    have hdenpos : 0 < ‖jInvariantFun z - jInvariantFun z₀‖ := by
      rw [norm_pos_iff]; exact hd2
    have hstep : ‖M (z : ℂ)‖ ≤ (C_A + L / (2*Real.pi)) * ‖(z : ℂ) - (z₀ : ℂ)‖^2 / δ := by
      have h1 : (C_A + L / (2*Real.pi)) * δ * ‖(z : ℂ) - (z₀ : ℂ)‖ ^ 2 / δ ^ 2
          = (C_A + L / (2*Real.pi)) * ‖(z : ℂ) - (z₀ : ℂ)‖ ^ 2 / δ := by
        field_simp
      rw [h1] at hmB
      exact hmB
    have hcδpos : 0 < c₀ * δ := mul_pos hc₀pos hδpos
    rw [div_le_iff₀ hdenpos]
    calc ‖M (z : ℂ)‖ ≤ (C_A + L / (2*Real.pi)) * ‖(z : ℂ) - (z₀ : ℂ)‖ ^ 2 / δ := hstep
      _ = (C_A + L / (2*Real.pi)) / (c₀ * δ) * ‖(z : ℂ) - (z₀ : ℂ)‖
            * (c₀ * ‖(z : ℂ) - (z₀ : ℂ)‖) := by
          field_simp
      _ ≤ (C_A + L / (2*Real.pi)) / (c₀ * δ) * ‖(z : ℂ) - (z₀ : ℂ)‖
            * ‖jInvariantFun z - jInvariantFun z₀‖ := by
          exact mul_le_mul_of_nonneg_left hden (by positivity)

end Work.Asymptotics


namespace Work.Asymptotics

open Work.Kernels Work.Residues

/-- **The principal part of the CKMRV kernel in the second variable, at the translate pole,
with Lipschitz remainder.** -/
theorem Kfun_principal_part_z_lip (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {s₀ : ℝ} (hs₀ : 0 < s₀) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ (τ z : UpperHalfPlane) (n : ℤ),
      (n = 1 ∨ n = -1) → |τ.im - s₀| < δ → |τ.re - (n : ℝ)| < δ →
      ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ < δ →
      (∃ c : ℝ, 0 < c ∧ ∀ ζ : UpperHalfPlane, ‖(ζ : ℂ) - ((τ : ℂ) - (n : ℂ))‖ < δ →
        c ≤ ‖Work.Residues.jprime ζ‖) →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
      ‖Work.Kernels.Kfun ℓ d τ z * ((z : ℂ) - ((τ : ℂ) - (n : ℂ))) - (n : ℂ) / (2 * Real.pi)‖
        ≤ C * ‖(z : ℂ) - ((τ : ℂ) - (n : ℂ))‖ :=
  Kfun_principal_part_z_lip_of ℓ d hd hs₀
    (exists_lower_bound_jDiff s₀ hs₀)
    (continuous_AfunFun ℓ d)
    (fun x => lipschitz_jInvariantFun_local x)
    (fun z => AfunPlus_neg_one d hd z)
    (fun z => AfunMinus_neg_one ℓ d hd z)

end Work.Asymptotics
