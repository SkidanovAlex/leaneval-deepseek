import Mathlib
import Submission.Work.Asymptotics.Tile.tileStripOffCoincDefs
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Tile.tileFarTools
import Submission.Work.Asymptotics.Tile.tileWindowRestricted_strip
import Submission.Work.Asymptotics.SpikeCircle.divisorLowerDisc
import Submission.Work.Analysis.ThreeZeros.three_zeros_bound_ball
import Submission.Work.Asymptotics.Kfun_principal_part_z_lip
import Submission.Work.Asymptotics.KfunAuxDefs

/-!
# The endgame of the resonant strip off the coincidences

Given the *cleared* deviation bound on the ball of radius `29/20` around `σ = S • w`
(the hypothesis `hball`), we prove the strip bound `TileBelowPoleStripOffCoinc`.

The proof is the three-zeros endgame:

* `F(ζ) = -2 Δ(ζ) AfunFun τ ζ - 2 Sh τ ζ · Gfun τ ζ` is the holomorphic representative of the
  cleared numerator `N(ζ) = 2 Sh τ ζ (Kfun τ ζ - Gfun τ ζ)`, and it agrees with `N` on the ball;
* `N` vanishes at the three orbit points `σ - 1, σ, σ + 1` (`AfunFun_strip_zeros`,
  `Sh_strip_zeros`), so `three_zeros_bound_ball` bounds `F` on the ball by `(M/δ)` times the
  product of the three distances;
* the divisor lower bound `Sh_axis_lower_bound` bounds `‖Sh τ (i t)‖` from below by the *same*
  product, cancelling it;
* `‖Kfun τ (i t) - Gfun τ (i t)‖ = ‖F (i t)‖ / (2 ‖Sh τ (i t)‖)`.
-/

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Manifold

noncomputable section

/-- `j (-1 +ᵥ σ) = j σ`. -/
private lemma j_vadd_neg_one (σ : UpperHalfPlane) :
    Work.Kernels.jInvariantFun ((-1 : ℝ) +ᵥ σ) = Work.Kernels.jInvariantFun σ := by
  have h := Work.Kernels.KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ σ)
  rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ σ) = σ by rw [← add_vadd]; norm_num] at h
  exact h.symm

/-- `j (n +ᵥ w) = j (S • w)` for `n = ±1`. -/
private lemma j_vadd_int_eq_j_S (n : ℤ) (hn : n = 1 ∨ n = -1) (w : UpperHalfPlane) :
    Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
      = Work.Kernels.jInvariantFun (ModularGroup.S • w) := by
  rw [Work.Asymptotics.Tile.jInvariantFun_vadd_int' n hn w,
    Work.Kernels.KernelFacts.jInvariantFun_S_smul]

theorem tileStripOffCoincEndgame (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hball : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ (n : ℤ), (n = 1 ∨ n = -1) →
        ∀ ζ : UpperHalfPlane,
          ‖(ζ : ℂ) - ((ModularGroup.S • w : UpperHalfPlane) : ℂ)‖ ≤ 29 / 20 →
          ‖2 * (Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
              * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
                  - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))‖
          ≤ C * (Work.Kernels.scale w) ^ N) :
    Work.Asymptotics.Tile.TileBelowPoleStripOffCoinc ℓ d := by
  obtain ⟨Ch, Nh, hCh, hNh, hballb⟩ := hball
  obtain ⟨cd, hcd, hdivb⟩ := Sh_axis_lower_bound
  set ρ : ℝ := 29 / 20 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; norm_num
  set δ : ℝ := ρ * (9 / 20) * (9 / 20) with hδdef
  have hδpos : 0 < δ := by rw [hδdef, hρdef]; norm_num
  refine ⟨Ch * Real.exp (2 * Real.pi) / (2 * δ * cd) + 1, Nh, 0,
    by positivity, hNh, le_refl 0, ?_⟩
  intro w n hn hw t ht ht1 ht2 hne
  rw [Work.Kernels.Kaxis, dif_pos ht, Aexp_Gcusp_eq_Gfun' ℓ d hd ((n : ℝ) +ᵥ w) t ht]
  set σ : UpperHalfPlane := ModularGroup.S • w with hσdef
  set τ : UpperHalfPlane := (n : ℝ) +ᵥ w with hτdef
  set ζ : UpperHalfPlane := Work.Kernels.imagAxis t ht with hζdef
  have hσD : σ ∈ Work.Asymptotics.DomainD := by
    rw [hσdef]; exact Work.Asymptotics.S_smul_mem_DomainD hw.1
  have hσim : (2 : ℝ) ≤ σ.im := by rw [hσdef]; exact hw.2
  have hσre : |σ.re| < 1 := by
    obtain ⟨h1, h2⟩ := Work.Asymptotics.re_bounds_of_mem_DomainD hσD
    rw [abs_lt]; exact ⟨h1, h2⟩
  have hζcoe : (ζ : ℂ) = (t : ℂ) * Complex.I := by rw [hζdef]; rfl
  have hτσ : Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun σ := by
    show Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
      = Work.Kernels.jInvariantFun (ModularGroup.S • w)
    exact j_vadd_int_eq_j_S n hn w
  -- the axis point is strictly inside the ball
  have hdistlt : ‖(ζ : ℂ) - (σ : ℂ)‖ < ρ := by
    have hsq : ‖(ζ : ℂ) - (σ : ℂ)‖ ^ 2 = σ.re ^ 2 + (t - σ.im) ^ 2 := by
      rw [hζcoe, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im]
      ring
    have h1 : σ.re ^ 2 < 1 := by
      have h := hσre
      rw [abs_lt] at h
      nlinarith [h.1, h.2, mul_pos (by linarith : (0:ℝ) < 1 - σ.re)
        (by linarith : (0:ℝ) < 1 + σ.re)]
    have h2 : (t - σ.im) ^ 2 ≤ 1 := by
      have hh : |t - σ.im| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      nlinarith [hh, sq_abs (t - σ.im)]
    have h3 : ‖(ζ : ℂ) - (σ : ℂ)‖ ^ 2 < (29 / 20 : ℝ) ^ 2 := by
      rw [hsq]; nlinarith
    have h4 : |‖(ζ : ℂ) - (σ : ℂ)‖| < |(29 / 20 : ℝ)| := by
      rw [← sq_lt_sq]; simpa using h3
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 29 / 20)] at h4
    rw [abs_of_nonneg (norm_nonneg _)] at h4
    rwa [hρdef]
  have hζball : (ζ : ℂ) ∈ Metric.ball ((σ : ℂ)) ρ :=
    Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hdistlt)
  have hζballc : (ζ : ℂ) ∈ Metric.closedBall ((σ : ℂ)) ρ :=
    Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact le_of_lt hdistlt)
  -- the closed ball lies in the upper half plane
  have hclosed : Metric.closedBall ((σ : ℂ)) ρ ⊆ {u : ℂ | 0 < u.im} := by
    intro u hu
    have h1 : ‖u - (σ : ℂ)‖ ≤ ρ := by
      have := Metric.mem_closedBall.mp hu; rwa [dist_eq_norm] at this
    have him : |u.im - σ.im| ≤ ρ := by
      have h2 : |(u - (σ : ℂ)).im| ≤ ‖u - (σ : ℂ)‖ := Complex.abs_im_le_norm _
      have h3 : (u - (σ : ℂ)).im = u.im - σ.im := by
        rw [Complex.sub_im, UpperHalfPlane.coe_im]
      rw [h3] at h2
      linarith
    have h4 : -(ρ) ≤ u.im - σ.im := (abs_le.mp him).1
    show 0 < u.im
    have h5 : σ.im - ρ ≤ u.im := by linarith
    have h6 : 0 < σ.im - ρ := by rw [hρdef]; linarith
    linarith
  -- ## the holomorphic representative
  set F : ℂ → ℂ := fun u => -2 * (Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex u)
        * Work.Asymptotics.AfunFun ℓ d τ (UpperHalfPlane.ofComplex u))
      - 2 * (Work.Asymptotics.Compact.Sh τ (UpperHalfPlane.ofComplex u)
        * Work.Asymptotics.Compact.Gfun d ℓ τ (UpperHalfPlane.ofComplex u)) with hFdef
  have hFval : ∀ u : ℂ, F u = -2 * (Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex u)
        * Work.Asymptotics.AfunFun ℓ d τ (UpperHalfPlane.ofComplex u))
      - 2 * (Work.Asymptotics.Compact.Sh τ (UpperHalfPlane.ofComplex u)
        * Work.Asymptotics.Compact.Gfun d ℓ τ (UpperHalfPlane.ofComplex u)) := fun u => by
    rw [hFdef]
  have hΔdiff : DifferentiableOn ℂ
      (fun u : ℂ => Work.Kernels.DeltaFun (UpperHalfPlane.ofComplex u)) {u : ℂ | 0 < u.im} :=
    (UpperHalfPlane.mdifferentiable_iff).mp Work.Kernels.ClassicalFacts.DeltaFun_mem_InP.1
  have hAfdiff : DifferentiableOn ℂ
      (fun u : ℂ => Work.Asymptotics.AfunFun ℓ d τ (UpperHalfPlane.ofComplex u))
      {u : ℂ | 0 < u.im} :=
    (UpperHalfPlane.mdifferentiable_iff).mp (Work.Asymptotics.mdifferentiable_AfunFun_snd ℓ d hd τ)
  have hShmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : ℍ => Work.Asymptotics.Compact.Sh τ z) := by
    have h : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : ℍ => Work.Kernels.E4Fun z ^ 3
        - Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ) :=
      (Work.Kernels.ClassicalFacts.E4Fun_mem_InP.1.pow 3).sub
        (Work.Kernels.ClassicalFacts.DeltaFun_mem_InP.1.mul mdifferentiable_const)
    simpa [Work.Asymptotics.Compact.Sh] using h
  have hShdiff : DifferentiableOn ℂ
      (fun u : ℂ => Work.Asymptotics.Compact.Sh τ (UpperHalfPlane.ofComplex u))
      {u : ℂ | 0 < u.im} :=
    (UpperHalfPlane.mdifferentiable_iff).mp hShmd
  have hGfdiff : DifferentiableOn ℂ
      (fun u : ℂ => Work.Asymptotics.Compact.Gfun d ℓ τ (UpperHalfPlane.ofComplex u))
      {u : ℂ | 0 < u.im} := differentiableOn_Gfun ℓ d τ
  have hFdiff : DifferentiableOn ℂ F {u : ℂ | 0 < u.im} := by
    rw [hFdef]
    exact ((hΔdiff.mul hAfdiff).const_mul (-2)).sub ((hShdiff.mul hGfdiff).const_mul 2)
  have hF : DiffContOnCl ℂ F (Metric.ball ((σ : ℂ)) ρ) := hFdiff.diffContOnCl_ball hclosed
  -- ## `F` agrees with the cleared numerator on the ball
  have hFN : ∀ u ∈ Metric.closedBall ((σ : ℂ)) ρ,
      F u = 2 * (Work.Asymptotics.Compact.Sh τ (UpperHalfPlane.ofComplex u)
          * (Work.Kernels.Kfun ℓ d τ (UpperHalfPlane.ofComplex u)
              - Work.Asymptotics.Compact.Gfun d ℓ τ (UpperHalfPlane.ofComplex u))) := by
    intro u hu
    have huim : 0 < u.im := hclosed hu
    by_cases hjj : Work.Kernels.jInvariantFun τ
        = Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex u)
    · -- coincidence: the point is one of `σ-1, σ, σ+1`
      have hdist : ‖((UpperHalfPlane.ofComplex u : ℍ) : ℂ) - (σ : ℂ)‖ ≤ ρ := by
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos huim]
        have := Metric.mem_closedBall.mp hu; rwa [dist_eq_norm] at this
      have hjeq : Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex u)
          = Work.Kernels.jInvariantFun σ := hjj ▸ hτσ
      obtain h1 | h1 | h1 :=
        Work.Asymptotics.SpikeCircle.fiber_orbit_gap σ (UpperHalfPlane.ofComplex u)
          hσim hdist hjeq
      · -- `ofComplex u = σ - 1`
        have hAu : UpperHalfPlane.ofComplex u = ((-1 : ℤ) : ℝ) +ᵥ (ModularGroup.S • w) := by
          apply UpperHalfPlane.ext
          rw [h1, UpperHalfPlane.coe_vadd]
          push_cast
          ring
        have hSh0 : Work.Asymptotics.Compact.Sh τ (UpperHalfPlane.ofComplex u) = 0 := by
          rw [hAu]; exact Sh_strip_zeros w n hn (-1) (Or.inl rfl)
        have hAf0 : Work.Asymptotics.AfunFun ℓ d τ (UpperHalfPlane.ofComplex u) = 0 := by
          rw [hAu]; exact AfunFun_strip_zeros ℓ d hd w n hn (-1) (Or.inl rfl)
        rw [hFval u, hSh0, hAf0]; ring
      · -- `ofComplex u = σ`
        have hAu : UpperHalfPlane.ofComplex u = ((0 : ℤ) : ℝ) +ᵥ (ModularGroup.S • w) := by
          apply UpperHalfPlane.ext
          rw [h1, UpperHalfPlane.coe_vadd]
          push_cast
          ring
        have hSh0 : Work.Asymptotics.Compact.Sh τ (UpperHalfPlane.ofComplex u) = 0 := by
          rw [hAu]; exact Sh_strip_zeros w n hn 0 (Or.inr (Or.inl rfl))
        have hAf0 : Work.Asymptotics.AfunFun ℓ d τ (UpperHalfPlane.ofComplex u) = 0 := by
          rw [hAu]; exact AfunFun_strip_zeros ℓ d hd w n hn 0 (Or.inr (Or.inl rfl))
        rw [hFval u, hSh0, hAf0]; ring
      · -- `ofComplex u = σ + 1`
        have hAu : UpperHalfPlane.ofComplex u = ((1 : ℤ) : ℝ) +ᵥ (ModularGroup.S • w) := by
          apply UpperHalfPlane.ext
          rw [h1, UpperHalfPlane.coe_vadd]
          push_cast
          ring
        have hSh0 : Work.Asymptotics.Compact.Sh τ (UpperHalfPlane.ofComplex u) = 0 := by
          rw [hAu]; exact Sh_strip_zeros w n hn 1 (Or.inr (Or.inr rfl))
        have hAf0 : Work.Asymptotics.AfunFun ℓ d τ (UpperHalfPlane.ofComplex u) = 0 := by
          rw [hAu]; exact AfunFun_strip_zeros ℓ d hd w n hn 1 (Or.inr (Or.inr rfl))
        rw [hFval u, hSh0, hAf0]; ring
    · -- non-coincidence: `tileNum_eq_hol`
      have h := tileNum_eq_hol ℓ d hd w n (UpperHalfPlane.ofComplex u) hjj
      rw [hFval u]
      exact h.symm
  -- ## the three zeros
  have hz1 : F ((σ : ℂ)) = 0 := by
    have hSh0 : Work.Asymptotics.Compact.Sh τ σ = 0 := by
      have h := Sh_strip_zeros w n hn 0 (Or.inr (Or.inl rfl))
      have hpt : (((0 : ℤ) : ℝ) +ᵥ (ModularGroup.S • w)) = σ := by rw [hσdef]; simp
      rwa [hpt] at h
    have hAf0 : Work.Asymptotics.AfunFun ℓ d τ σ = 0 := by
      have h := AfunFun_strip_zeros ℓ d hd w n hn 0 (Or.inr (Or.inl rfl))
      have hpt : (((0 : ℤ) : ℝ) +ᵥ (ModularGroup.S • w)) = σ := by rw [hσdef]; simp
      rwa [hpt] at h
    rw [hFval, UpperHalfPlane.ofComplex_apply, hSh0, hAf0]; ring
  have hz2 : F ((σ : ℂ) - 1) = 0 := by
    have him : 0 < (((σ : ℂ) - 1)).im := by
      rw [Complex.sub_im]; simp; exact σ.im_pos
    have hcoe : UpperHalfPlane.ofComplex ((σ : ℂ) - 1)
        = ((-1 : ℤ) : ℝ) +ᵥ (ModularGroup.S • w) := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos him, UpperHalfPlane.coe_vadd]
      push_cast
      ring
    have hSh0 : Work.Asymptotics.Compact.Sh τ (((-1 : ℤ) : ℝ) +ᵥ (ModularGroup.S • w)) = 0 :=
      Sh_strip_zeros w n hn (-1) (Or.inl rfl)
    have hAf0 : Work.Asymptotics.AfunFun ℓ d τ (((-1 : ℤ) : ℝ) +ᵥ (ModularGroup.S • w)) = 0 :=
      AfunFun_strip_zeros ℓ d hd w n hn (-1) (Or.inl rfl)
    rw [hFval ((σ : ℂ) - 1), hcoe, hSh0, hAf0]; ring
  have hz3 : F ((σ : ℂ) + 1) = 0 := by
    have him : 0 < (((σ : ℂ) + 1)).im := by
      rw [Complex.add_im]; simp; exact σ.im_pos
    have hcoe : UpperHalfPlane.ofComplex ((σ : ℂ) + 1)
        = ((1 : ℤ) : ℝ) +ᵥ (ModularGroup.S • w) := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos him, UpperHalfPlane.coe_vadd]
      push_cast
      ring
    have hSh0 : Work.Asymptotics.Compact.Sh τ (((1 : ℤ) : ℝ) +ᵥ (ModularGroup.S • w)) = 0 :=
      Sh_strip_zeros w n hn 1 (Or.inr (Or.inr rfl))
    have hAf0 : Work.Asymptotics.AfunFun ℓ d τ (((1 : ℤ) : ℝ) +ᵥ (ModularGroup.S • w)) = 0 :=
      AfunFun_strip_zeros ℓ d hd w n hn 1 (Or.inr (Or.inr rfl))
    rw [hFval ((σ : ℂ) + 1), hcoe, hSh0, hAf0]; ring
  have hz12 : (σ : ℂ) ≠ (σ : ℂ) - 1 := by
    intro h
    have h' : (1 : ℂ) = 0 := by linear_combination h
    exact one_ne_zero h'
  have hz13 : (σ : ℂ) ≠ (σ : ℂ) + 1 := by
    intro h
    have h' : (1 : ℂ) = 0 := by linear_combination -h
    exact one_ne_zero h'
  have hz23 : (σ : ℂ) - 1 ≠ (σ : ℂ) + 1 := by
    intro h
    have h' : (2 : ℂ) = 0 := by linear_combination -h
    norm_num at h'
  -- ## the boundary product
  have hsphere_le : ∀ u ∈ Metric.sphere ((σ : ℂ)) ρ, ‖u - (σ : ℂ)‖ = ρ := by
    intro u hu; rwa [Metric.mem_sphere, dist_eq_norm] at hu
  have hsphere_prod : ∀ u ∈ Metric.sphere ((σ : ℂ)) ρ,
      δ ≤ ‖u - (σ : ℂ)‖ * ‖u - ((σ : ℂ) - 1)‖ * ‖u - ((σ : ℂ) + 1)‖ := by
    intro u hu
    have hu' := hsphere_le u hu
    have h1 : (9 / 20 : ℝ) ≤ ‖u - ((σ : ℂ) + 1)‖ := by
      have h := abs_norm_sub_norm_le (u - (σ : ℂ)) (1 : ℂ)
      have h2 : (u - (σ : ℂ)) - 1 = u - ((σ : ℂ) + 1) := by ring
      rw [h2, hu', norm_one] at h
      have h3 : |ρ - 1| = 9 / 20 := by rw [hρdef]; norm_num
      rw [h3] at h; exact h
    have h4 : (9 / 20 : ℝ) ≤ ‖u - ((σ : ℂ) - 1)‖ := by
      have h := abs_norm_sub_norm_le (u - (σ : ℂ)) (-1 : ℂ)
      have h2 : (u - (σ : ℂ)) - (-1) = u - ((σ : ℂ) - 1) := by ring
      rw [h2, hu', norm_neg, norm_one] at h
      have h3 : |ρ - 1| = 9 / 20 := by rw [hρdef]; norm_num
      rw [h3] at h; exact h
    rw [hδdef, hu']
    have step1 : ρ * (9 / 20) ≤ ρ * ‖u - ((σ : ℂ) + 1)‖ :=
      mul_le_mul_of_nonneg_left h1 hρpos.le
    have step2 : ρ * (9 / 20) * (9 / 20)
        ≤ (ρ * ‖u - ((σ : ℂ) + 1)‖) * ‖u - ((σ : ℂ) - 1)‖ :=
      mul_le_mul step1 h4 (by norm_num) (by positivity)
    calc ρ * (9 / 20) * (9 / 20)
        = ρ * (9 / 20) * (9 / 20) := rfl
      _ ≤ (ρ * ‖u - ((σ : ℂ) + 1)‖) * ‖u - ((σ : ℂ) - 1)‖ := step2
      _ = ρ * ‖u - ((σ : ℂ) - 1)‖ * ‖u - ((σ : ℂ) + 1)‖ := by ring
  -- ## the ball bound for `F`
  have hMh_nn : 0 ≤ Ch * (Work.Kernels.scale w) ^ Nh :=
    mul_nonneg hCh.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
  have hbdball : ∀ u ∈ Metric.ball ((σ : ℂ)) ρ,
      ‖F u‖ ≤ Ch * (Work.Kernels.scale w) ^ Nh := by
    intro u hu
    have huc : u ∈ Metric.closedBall ((σ : ℂ)) ρ := Metric.ball_subset_closedBall hu
    have huim : 0 < u.im := hclosed huc
    rw [hFN u huc]
    exact hballb w hw n hn (UpperHalfPlane.ofComplex u) (by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos huim]
      have := Metric.mem_closedBall.mp huc
      rwa [dist_eq_norm, hρdef] at this)
  -- ## three zeros estimate
  have h3z := Work.Analysis.ThreeZeros.three_zeros_bound_ball (f := F) (c := ((σ : ℂ))) (ρ := ρ)
    (M := Ch * (Work.Kernels.scale w) ^ Nh) (δ := δ)
    hρpos hMh_nn hδpos hF hbdball hz12 hz13 hz23 hz1 hz2 hz3 hsphere_prod
  have hFζ : F (ζ : ℂ) = 2 * (Work.Asymptotics.Compact.Sh τ ζ
        * (Work.Kernels.Kfun ℓ d τ ζ - Work.Asymptotics.Compact.Gfun d ℓ τ ζ)) := by
    have h := hFN (ζ : ℂ) hζballc
    rwa [UpperHalfPlane.ofComplex_apply] at h
  -- ## the products
  set P : ℝ := ‖((ζ : ℂ) - (σ : ℂ)) * ((ζ : ℂ) - ((σ : ℂ) - 1))
      * ((ζ : ℂ) - ((σ : ℂ) + 1))‖ with hPdef
  set E : ℝ := Real.exp (2 * Real.pi * (σ.im - t)) with hEdef
  set Mh : ℝ := Ch * (Work.Kernels.scale w) ^ Nh with hMhdef
  have hPpos : 0 < P := by
    rw [hPdef, norm_pos_iff]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · -- `ζ ≠ σ`
      intro h
      have hζσ : ζ = σ := UpperHalfPlane.ext (sub_eq_zero.mp h)
      exact hne (by rw [hζσ, ← hτσ])
    · -- `ζ ≠ σ - 1`
      intro h
      have hζm : ζ = (-1 : ℝ) +ᵥ σ := by
        apply UpperHalfPlane.ext
        rw [UpperHalfPlane.coe_vadd]
        have h' : (ζ : ℂ) = (σ : ℂ) - 1 := sub_eq_zero.mp h
        push_cast
        rw [h']; ring
      exact hne (by rw [hζm, j_vadd_neg_one, ← hτσ])
    · -- `ζ ≠ σ + 1`
      intro h
      have hζp : ζ = (1 : ℝ) +ᵥ σ := by
        apply UpperHalfPlane.ext
        rw [UpperHalfPlane.coe_vadd]
        have h' : (ζ : ℂ) = (σ : ℂ) + 1 := sub_eq_zero.mp h
        push_cast
        rw [h']; ring
      exact hne (by rw [hζp, Work.Kernels.KernelFacts.jInvariantFun_vadd_one, ← hτσ])
  have hFζle : ‖F (ζ : ℂ)‖ ≤ (Mh / δ) * P := by
    have h := h3z (ζ : ℂ) hζball
    have hnorm : ‖(ζ : ℂ) - (σ : ℂ)‖ * ‖(ζ : ℂ) - ((σ : ℂ) - 1)‖ * ‖(ζ : ℂ) - ((σ : ℂ) + 1)‖
        = P := by
      rw [hPdef, norm_mul, norm_mul]
    calc ‖F (ζ : ℂ)‖ ≤ (Mh / δ) * ‖(ζ : ℂ) - (σ : ℂ)‖ * ‖(ζ : ℂ) - ((σ : ℂ) - 1)‖
            * ‖(ζ : ℂ) - ((σ : ℂ) + 1)‖ := h
      _ = (Mh / δ) * P := by rw [← hnorm]; ring
  have hdivζ : cd * (E * P) ≤ ‖Work.Asymptotics.Compact.Sh τ ζ‖ := by
    have h := hdivb w hw n hn t ht ht1 ht2
    rw [hEdef, hPdef]
    exact h
  -- ## the final combination
  have hFζnorm : ‖F (ζ : ℂ)‖ = 2 * ‖Work.Asymptotics.Compact.Sh τ ζ‖
      * ‖Work.Kernels.Kfun ℓ d τ ζ - Work.Asymptotics.Compact.Gfun d ℓ τ ζ‖ := by
    rw [hFζ, norm_mul, norm_mul, Complex.norm_ofNat]
    ring
  have hmain : 2 * (cd * (E * P)) * ‖Work.Kernels.Kfun ℓ d τ ζ
        - Work.Asymptotics.Compact.Gfun d ℓ τ ζ‖ ≤ (Mh / δ) * P := by
    calc 2 * (cd * (E * P)) * ‖Work.Kernels.Kfun ℓ d τ ζ
            - Work.Asymptotics.Compact.Gfun d ℓ τ ζ‖
        ≤ 2 * ‖Work.Asymptotics.Compact.Sh τ ζ‖
            * ‖Work.Kernels.Kfun ℓ d τ ζ - Work.Asymptotics.Compact.Gfun d ℓ τ ζ‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left hdivζ (by norm_num)
      _ = ‖F (ζ : ℂ)‖ := hFζnorm.symm
      _ ≤ (Mh / δ) * P := hFζle
  have hEge : Real.exp (-(2 * Real.pi)) ≤ E := by
    rw [hEdef]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, ht2]
  have hkey : (2 * cd * Real.exp (-(2 * Real.pi))) * ‖Work.Kernels.Kfun ℓ d τ ζ
        - Work.Asymptotics.Compact.Gfun d ℓ τ ζ‖ ≤ Mh / δ := by
    have h1 : (2 * cd * Real.exp (-(2 * Real.pi))) * ‖Work.Kernels.Kfun ℓ d τ ζ
          - Work.Asymptotics.Compact.Gfun d ℓ τ ζ‖
        ≤ (2 * cd * E) * ‖Work.Kernels.Kfun ℓ d τ ζ
            - Work.Asymptotics.Compact.Gfun d ℓ τ ζ‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_left hEge (by positivity)
    have h2 : (2 * cd * E) * ‖Work.Kernels.Kfun ℓ d τ ζ
          - Work.Asymptotics.Compact.Gfun d ℓ τ ζ‖ ≤ Mh / δ := by
      have h2' : (2 * cd * E * ‖Work.Kernels.Kfun ℓ d τ ζ
            - Work.Asymptotics.Compact.Gfun d ℓ τ ζ‖) * P ≤ (Mh / δ) * P := by
        calc (2 * cd * E * ‖Work.Kernels.Kfun ℓ d τ ζ
              - Work.Asymptotics.Compact.Gfun d ℓ τ ζ‖) * P
            = 2 * (cd * (E * P)) * ‖Work.Kernels.Kfun ℓ d τ ζ
                - Work.Asymptotics.Compact.Gfun d ℓ τ ζ‖ := by ring
          _ ≤ (Mh / δ) * P := hmain
      exact le_of_mul_le_mul_right h2' hPpos
    exact le_trans h1 h2
  have hdev : ‖Work.Kernels.Kfun ℓ d τ ζ - Work.Asymptotics.Compact.Gfun d ℓ τ ζ‖
      ≤ Mh * Real.exp (2 * Real.pi) / (2 * δ * cd) := by
    have hden : 0 < δ * (2 * cd * Real.exp (-(2 * Real.pi))) := by positivity
    have hA : ‖Work.Kernels.Kfun ℓ d τ ζ - Work.Asymptotics.Compact.Gfun d ℓ τ ζ‖
        ≤ Mh / (δ * (2 * cd * Real.exp (-(2 * Real.pi)))) := by
      rw [le_div_iff₀ hden]
      have hrw : ‖Work.Kernels.Kfun ℓ d τ ζ - Work.Asymptotics.Compact.Gfun d ℓ τ ζ‖
            * (δ * (2 * cd * Real.exp (-(2 * Real.pi))))
          = δ * ((2 * cd * Real.exp (-(2 * Real.pi)))
              * ‖Work.Kernels.Kfun ℓ d τ ζ - Work.Asymptotics.Compact.Gfun d ℓ τ ζ‖) := by ring
      rw [hrw]
      calc δ * ((2 * cd * Real.exp (-(2 * Real.pi)))
            * ‖Work.Kernels.Kfun ℓ d τ ζ - Work.Asymptotics.Compact.Gfun d ℓ τ ζ‖)
          ≤ δ * (Mh / δ) := mul_le_mul_of_nonneg_left hkey hδpos.le
        _ = Mh := by field_simp
    have hB : Mh / (δ * (2 * cd * Real.exp (-(2 * Real.pi))))
        = Mh * Real.exp (2 * Real.pi) / (2 * δ * cd) := by
      rw [Real.exp_neg]
      field_simp
    rwa [hB] at hA
  -- ## conclusion
  calc ‖Work.Kernels.Kfun ℓ d τ ζ - Work.Asymptotics.Compact.Gfun d ℓ τ ζ‖
      ≤ Mh * Real.exp (2 * Real.pi) / (2 * δ * cd) := hdev
    _ = (Ch * (Work.Kernels.scale w) ^ Nh) * Real.exp (2 * Real.pi) / (2 * δ * cd) := by
        rw [hMhdef]
    _ ≤ (Ch * Real.exp (2 * Real.pi) / (2 * δ * cd) + 1) * (Work.Kernels.scale w) ^ Nh
          * t ^ (0 : ℝ) := by
        rw [Real.rpow_zero, mul_one]
        have hs0 : 0 ≤ (Work.Kernels.scale w) ^ Nh :=
          Real.rpow_nonneg (Work.Kernels.scale_pos w).le _
        have hcoef : Ch * Real.exp (2 * Real.pi) / (2 * δ * cd)
            ≤ Ch * Real.exp (2 * Real.pi) / (2 * δ * cd) + 1 := le_add_of_nonneg_right zero_le_one
        calc Ch * (Work.Kernels.scale w) ^ Nh * Real.exp (2 * Real.pi) / (2 * δ * cd)
            = (Ch * Real.exp (2 * Real.pi) / (2 * δ * cd)) * (Work.Kernels.scale w) ^ Nh := by ring
          _ ≤ (Ch * Real.exp (2 * Real.pi) / (2 * δ * cd) + 1) * (Work.Kernels.scale w) ^ Nh :=
              mul_le_mul_of_nonneg_right hcoef hs0

end

end Work.Asymptotics.Tile
