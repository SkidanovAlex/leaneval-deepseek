import Mathlib
import Submission.Work.ZeroDensity.LogFree.poleLSDefs
import Submission.Work.ZeroDensity.TrapKDefs
import Submission.Work.ZeroDensity.TrapKNormLe

/-!
# The sharp mean value theorem for `1/δ`-separated frequencies (Heath-Brown §11, L4)

`Work.ZeroDensity.HB7MvtMul` supplies the constant `C` of the interface
`Work.ZeroDensity.LogFree.MvtMul`:

`∫_{Y₁}^{Y₂} ‖∑_i ζ_i y^{-i γ_i}‖² dy/y ≤ (log (Y₂/Y₁) + C/δ) ∑_i ‖ζ_i‖²`

for every `δ > 0` and every `δ`-separated family of real frequencies `γ`.

This is the classical Montgomery--Vaughan mean value theorem.  The coefficient of
`log (Y₂/Y₁)` must be exactly `1` (it is an equality for a single frequency), so the proof may
not lose a constant on the length of the interval; the constant in front of `1/δ` is free, and
we take the crude one.

The argument is the "averaged interval" (spreading) device, in the sharp form which needs no
Fourier inversion:

* substitute `y = e^{2πs}`; the statement becomes the additive mean value theorem
  `∫_a^b ‖∑_i ζ_i e^{-2πi γ_i s}‖² ds ≤ ((b-a) + C'/δ) ∑ ‖ζ_i‖²`;
* for `δ > 0` put `W = 1/δ`, `L = (b-a) + W`, `u₀ = a - W`; then `[a,b] ⊆ [u, u+L]` for every
  `u ∈ [u₀, u₀+W]`, so
  `∫_a^b ‖F‖² ≤ W⁻¹ ∫_{u₀}^{u₀+W} ∫_u^{u+L} ‖F‖²`;
* expanding `‖F‖²` as a double sum and integrating term by term, the right side becomes
  `∑_{i,j} ζ_i \bar ζ_j e^{-2πi(γ_i-γ_j)u₀} trapK L W (γ_i - γ_j)`, whose `(i,i)` entries are `L`
  (giving the sharp coefficient of the length) while the `(i,j)` entries, `i ≠ j`, are
  `≤ 1/(W π² (γ_i-γ_j)²)`; the separation hypothesis makes the resulting Schur row/column sums
  `O(1/δ)`.
-/

open scoped BigOperators

noncomputable section

namespace Work.ZeroDensity

/-- `trapK L W 0 = L`: the value of the kernel at frequency zero, i.e. the total mass of the
trapezoid weight. -/
lemma trapK_zero (L W : ℝ) (hW : W ≠ 0) : trapK L W 0 = (L : ℂ) := by
  have hinner : ∀ s : ℝ,
      (∫ t in s..(s + L),
        Complex.exp (-(2 * Real.pi * Complex.I * (((0 : ℝ)) : ℂ) * (t : ℂ)))) = (L : ℂ) := by
    intro s
    have hfun : (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * (((0 : ℝ)) : ℂ) * (t : ℂ))))
        = fun _ : ℝ => (1 : ℂ) := by
      funext t; simp
    rw [hfun]
    rw [intervalIntegral.integral_const]
    simp
  rw [trapK]
  simp only [hinner]
  rw [intervalIntegral.integral_const, Complex.real_smul]
  have hWc : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  rw [show (W - 0 : ℝ) = W by ring, ← mul_assoc, inv_mul_cancel₀ hWc, one_mul]

/-- The kernel is the product of the two elementary integrals over `[0,L]` and `[0,W]`. -/
lemma trapK_factor (L W ν : ℝ) :
    trapK L W ν = ((W : ℂ))⁻¹ *
      ((∫ t in (0 : ℝ)..L, Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (t : ℂ))))
        * (∫ s in (0 : ℝ)..W, Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (s : ℂ))))) := by
  have hshift : ∀ s : ℝ,
      (∫ t in s..(s + L), Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (t : ℂ))))
        = Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (s : ℂ))) *
          (∫ t in (0 : ℝ)..L, Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (t : ℂ)))) := by
    intro s
    have h := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := L)
      (f := fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (t : ℂ)))) s
    rw [zero_add] at h
    rw [show s + L = L + s by ring, ← h]
    have h2 : ∀ x : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * ((x + s : ℝ) : ℂ)))
        = Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (s : ℂ))) *
          Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (x : ℂ))) := by
      intro x
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [h2]
    rw [intervalIntegral.integral_const_mul]
  rw [trapK]
  rw [show (∫ s in (0 : ℝ)..W, ∫ t in s..(s + L),
        Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (t : ℂ))))
      = ∫ s in (0 : ℝ)..W, Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (s : ℂ))) *
          (∫ t in (0 : ℝ)..L, Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (t : ℂ)))) from
    intervalIntegral.integral_congr fun s _ => hshift s]
  rw [intervalIntegral.integral_mul_const]
  ring

/-- The averaged-interval integral of a single character; the substitution `u = u₀ + s`,
`t = u₀ + r` produces the phase `e^{-2πiνu₀}` and the unshifted kernel. -/
lemma trapK_shift (L W u₀ ν : ℝ) :
    (∫ u in u₀..(u₀ + W),
        ∫ t in u..(u + L), Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (t : ℂ))))
      = Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (u₀ : ℂ))) *
        (((∫ t in (0 : ℝ)..L, Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (t : ℂ))))
          * (∫ s in (0 : ℝ)..W, Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (s : ℂ)))))) := by
  have hinner : ∀ u : ℝ,
      (∫ t in u..(u + L), Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (t : ℂ))))
        = Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (u : ℂ))) *
          (∫ t in (0 : ℝ)..L, Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (t : ℂ)))) := by
    intro u
    have h := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := L)
      (f := fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (t : ℂ)))) u
    rw [zero_add] at h
    rw [show u + L = L + u by ring, ← h]
    have h2 : ∀ x : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * ((x + u : ℝ) : ℂ)))
        = Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (u : ℂ))) *
          Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (x : ℂ))) := by
      intro x
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [h2]
    rw [intervalIntegral.integral_const_mul]
  have houter :
      (∫ u in u₀..(u₀ + W), Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (u : ℂ))))
        = Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (u₀ : ℂ))) *
          (∫ s in (0 : ℝ)..W, Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (s : ℂ)))) := by
    have h := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := W)
      (f := fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (t : ℂ)))) u₀
    rw [zero_add] at h
    rw [show u₀ + W = W + u₀ by ring, ← h]
    have h2 : ∀ x : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * ((x + u₀ : ℝ) : ℂ)))
        = Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (u₀ : ℂ))) *
          Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (x : ℂ))) := by
      intro x
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [h2]
    rw [intervalIntegral.integral_const_mul]
  rw [show (∫ u in u₀..(u₀ + W),
        ∫ t in u..(u + L), Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (t : ℂ))))
      = ∫ u in u₀..(u₀ + W), Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (u : ℂ))) *
          (∫ t in (0 : ℝ)..L, Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (t : ℂ)))) from
    intervalIntegral.integral_congr fun u _ => hinner u]
  rw [intervalIntegral.integral_mul_const, houter]
  ring

/-- Continuity, in `u`, of the integral of a fixed continuous function over the moving window
`[u, u+L]`. -/
lemma continuous_intervalIntegral_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (g : ℝ → E) (hg : Continuous g) (L : ℝ) :
    Continuous (fun u : ℝ => ∫ t in u..(u + L), g t) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable g MeasureTheory.volume a b :=
    fun a b => hg.intervalIntegrable a b
  have h1 : Continuous (fun u : ℝ => ∫ t in (0 : ℝ)..(u + L), g t) :=
    (intervalIntegral.continuous_primitive hint 0).comp (continuous_id.add_const L)
  have h2 : Continuous (fun u : ℝ => ∫ t in (0 : ℝ)..u, g t) :=
    intervalIntegral.continuous_primitive hint 0
  have hsub : (fun u : ℝ => ∫ t in u..(u + L), g t)
      = fun u : ℝ => (∫ t in (0 : ℝ)..(u + L), g t) - (∫ t in (0 : ℝ)..u, g t) := by
    funext u
    rw [← intervalIntegral.integral_interval_sub_left (hint 0 (u + L)) (hint 0 u)]
  rw [hsub]
  exact h1.sub h2

/-- Expanding `‖∑ᵢ ζᵢ e^{-2πiγᵢt}‖²` as the double sum over pairs. -/
lemma normSq_expansion (m : ℕ) (γ : Fin m → ℝ) (ζ : Fin m → ℂ) (t : ℝ) :
    ((‖∑ i, ζ i * Complex.exp (-(2 * Real.pi * Complex.I * (γ i : ℂ) * (t : ℂ)))‖ ^ 2 : ℝ) : ℂ)
      = ∑ i, ∑ j, ζ i * star (ζ j) *
          Complex.exp (-(2 * Real.pi * Complex.I * (((γ i - γ j : ℝ)) : ℂ) * (t : ℂ))) := by
  set F : ℂ := ∑ i, ζ i * Complex.exp (-(2 * Real.pi * Complex.I * (γ i : ℂ) * (t : ℂ))) with hF
  have h1 : ((‖F‖ ^ 2 : ℝ) : ℂ) = F * star F := by
    rw [← Complex.normSq_eq_norm_sq]
    exact (Complex.mul_conj F).symm
  rw [h1, hF, star_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [star_mul]
  have hconj : star (Complex.exp (-(2 * Real.pi * Complex.I * (γ j : ℂ) * (t : ℂ))))
      = Complex.exp (2 * Real.pi * Complex.I * (γ j : ℂ) * (t : ℂ)) := by
    have h1 : star (Complex.exp (-(2 * Real.pi * Complex.I * (γ j : ℂ) * (t : ℂ))))
        = Complex.exp (star (-(2 * Real.pi * Complex.I * (γ j : ℂ) * (t : ℂ)))) := by
      rw [Complex.star_def, ← Complex.exp_conj]
    rw [h1]
    congr 1
    simp [Complex.conj_I]
  rw [hconj]
  rw [show -(2 * Real.pi * Complex.I * (((γ i - γ j : ℝ)) : ℂ) * (t : ℂ))
      = -(2 * Real.pi * Complex.I * (γ i : ℂ) * (t : ℂ))
        + 2 * Real.pi * Complex.I * (γ j : ℂ) * (t : ℂ) by
    push_cast; ring]
  rw [Complex.exp_add]
  ring

/-- The double interval integral of `‖∑ᵢ ζᵢ e^{-2πiγᵢt}‖²` over the averaged interval, expanded
into the pair sum of the elementary double integrals. -/
lemma trap_expansion_aux (m : ℕ) (γ : Fin m → ℝ) (ζ : Fin m → ℂ) (L W u₀ : ℝ) :
    ((∫ u in u₀..(u₀ + W), ∫ t in u..(u + L),
        ‖∑ i, ζ i * Complex.exp (-(2 * Real.pi * Complex.I * (γ i : ℂ) * (t : ℂ)))‖ ^ 2 : ℝ) : ℂ)
      = ∑ i, ∑ j, ζ i * star (ζ j) *
          (∫ u in u₀..(u₀ + W), ∫ t in u..(u + L),
            Complex.exp (-(2 * Real.pi * Complex.I * (((γ i - γ j : ℝ)) : ℂ) * (t : ℂ)))) := by
  rw [← intervalIntegral.integral_ofReal]
  have hstep : ∀ u : ℝ,
      ((∫ t in u..(u + L),
        ‖∑ i, ζ i * Complex.exp (-(2 * Real.pi * Complex.I * (γ i : ℂ) * (t : ℂ)))‖ ^ 2 : ℝ) : ℂ)
        = ∑ i, ∑ j, ζ i * star (ζ j) *
            (∫ t in u..(u + L),
              Complex.exp (-(2 * Real.pi * Complex.I * (((γ i - γ j : ℝ)) : ℂ) * (t : ℂ)))) := by
    intro u
    rw [← intervalIntegral.integral_ofReal]
    rw [show (∫ t in u..(u + L),
          ((‖∑ i, ζ i * Complex.exp (-(2 * Real.pi * Complex.I * (γ i : ℂ) * (t : ℂ)))‖ ^ 2 : ℝ) : ℂ))
        = ∫ t in u..(u + L), ∑ i, ∑ j, ζ i * star (ζ j) *
            Complex.exp (-(2 * Real.pi * Complex.I * (((γ i - γ j : ℝ)) : ℂ) * (t : ℂ))) from
      intervalIntegral.integral_congr fun t _ => normSq_expansion m γ ζ t]
    have hint : ∀ i : Fin m,
        IntervalIntegrable (fun t : ℝ => ∑ j, ζ i * star (ζ j) *
          Complex.exp (-(2 * Real.pi * Complex.I * (((γ i - γ j : ℝ)) : ℂ) * (t : ℂ))))
          MeasureTheory.volume u (u + L) := fun i =>
      (by fun_prop : Continuous (fun t : ℝ => ∑ j, ζ i * star (ζ j) *
        Complex.exp (-(2 * Real.pi * Complex.I * (((γ i - γ j : ℝ)) : ℂ) * (t : ℂ))))).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
      (f := fun i t => ∑ j, ζ i * star (ζ j) *
        Complex.exp (-(2 * Real.pi * Complex.I * (((γ i - γ j : ℝ)) : ℂ) * (t : ℂ))))
      (fun i _ => hint i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
      (f := fun j t => ζ i * star (ζ j) *
        Complex.exp (-(2 * Real.pi * Complex.I * (((γ i - γ j : ℝ)) : ℂ) * (t : ℂ))))
      (fun j _ => (by fun_prop : Continuous (fun t : ℝ => ζ i * star (ζ j) *
        Complex.exp (-(2 * Real.pi * Complex.I * (((γ i - γ j : ℝ)) : ℂ) * (t : ℂ))))).intervalIntegrable _ _)]
    exact Finset.sum_congr rfl (fun j _ => intervalIntegral.integral_const_mul _ _)
  rw [show (∫ u in u₀..(u₀ + W),
        ((∫ t in u..(u + L),
          ‖∑ i, ζ i * Complex.exp (-(2 * Real.pi * Complex.I * (γ i : ℂ) * (t : ℂ)))‖ ^ 2 : ℝ) : ℂ))
      = ∫ u in u₀..(u₀ + W), ∑ i, ∑ j, ζ i * star (ζ j) *
          (∫ t in u..(u + L),
            Complex.exp (-(2 * Real.pi * Complex.I * (((γ i - γ j : ℝ)) : ℂ) * (t : ℂ)))) from
    intervalIntegral.integral_congr fun u _ => hstep u]
  have hcont : ∀ i : Fin m, Continuous (fun u : ℝ => ∑ j, ζ i * star (ζ j) *
      (∫ t in u..(u + L),
        Complex.exp (-(2 * Real.pi * Complex.I * (((γ i - γ j : ℝ)) : ℂ) * (t : ℂ))))) := by
    intro i
    refine continuous_finsetSum Finset.univ (fun j _ => ?_)
    exact continuous_const.mul (continuous_intervalIntegral_shift _ (by fun_prop) L)
  have hint2 : ∀ i : Fin m,
      IntervalIntegrable (fun u : ℝ => ∑ j, ζ i * star (ζ j) *
        (∫ t in u..(u + L),
          Complex.exp (-(2 * Real.pi * Complex.I * (((γ i - γ j : ℝ)) : ℂ) * (t : ℂ)))))
        MeasureTheory.volume u₀ (u₀ + W) := fun i => (hcont i).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
    (f := fun i u => ∑ j, ζ i * star (ζ j) *
      (∫ t in u..(u + L),
        Complex.exp (-(2 * Real.pi * Complex.I * (((γ i - γ j : ℝ)) : ℂ) * (t : ℂ)))))
    (fun i _ => hint2 i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
    (f := fun j u => ζ i * star (ζ j) *
      (∫ t in u..(u + L),
        Complex.exp (-(2 * Real.pi * Complex.I * (((γ i - γ j : ℝ)) : ℂ) * (t : ℂ)))))
    (fun j _ => (continuous_const.mul (continuous_intervalIntegral_shift _ (by fun_prop) L)).intervalIntegrable _ _)]
  exact Finset.sum_congr rfl (fun j _ => intervalIntegral.integral_const_mul _ _)

/-- The full expansion of the averaged double integral into the kernel: this is the sharp
"spreading" identity. -/
lemma trapK_expansion (m : ℕ) (γ : Fin m → ℝ) (ζ : Fin m → ℂ) (L W u₀ : ℝ) :
    (((W⁻¹ * ∫ u in u₀..(u₀ + W), ∫ t in u..(u + L),
        ‖∑ i, ζ i * Complex.exp (-(2 * Real.pi * Complex.I * (γ i : ℂ) * (t : ℂ)))‖ ^ 2 : ℝ) : ℂ))
      = ∑ i, ∑ j, ζ i * star (ζ j) *
          (Complex.exp (-(2 * Real.pi * Complex.I * (((γ i - γ j : ℝ)) : ℂ) * (u₀ : ℂ)))
            * trapK L W (γ i - γ j)) := by
  rw [Complex.ofReal_mul, Complex.ofReal_inv, trap_expansion_aux]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [trapK_shift, trapK_factor]
  ring


/-- Two-sided Schur bound: if all row sums and all column sums of the norm matrix `w` are at most
`C`, then the sesquilinear form `∑ᵢ∑ⱼ zᵢ conj(zⱼ) wᵢⱼ` is bounded by `C ∑ᵢ ‖zᵢ‖²`. -/
lemma schurQuad {ι : Type*} [Fintype ι] (z : ι → ℂ) (w : ι → ι → ℂ) (C : ℝ)
    (hrow : ∀ i, ∑ j, ‖w i j‖ ≤ C) (hcol : ∀ j, ∑ i, ‖w i j‖ ≤ C) :
    ‖∑ i, ∑ j, z i * star (z j) * w i j‖ ≤ C * ∑ i, ‖z i‖ ^ 2 := by
  have h1 : ‖∑ i, ∑ j, z i * star (z j) * w i j‖ ≤ ∑ i, ∑ j, ‖z i‖ * ‖z j‖ * ‖w i j‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    rw [norm_mul, norm_mul, norm_star]
  have hpt : ∀ i j, ‖z i‖ * ‖z j‖ * ‖w i j‖
      ≤ (1 / 2) * (‖z i‖ ^ 2 * ‖w i j‖) + (1 / 2) * (‖z j‖ ^ 2 * ‖w i j‖) := by
    intro i j
    have hw := norm_nonneg (w i j)
    nlinarith [sq_nonneg (‖z i‖ - ‖z j‖), mul_nonneg (norm_nonneg (z i)) hw,
      mul_nonneg (norm_nonneg (z j)) hw]
  have hA : ∑ i, ∑ j, (1 / 2) * (‖z i‖ ^ 2 * ‖w i j‖)
      = (1 / 2) * (∑ i, ‖z i‖ ^ 2 * (∑ j, ‖w i j‖)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
  have hB : ∑ i, ∑ j, (1 / 2) * (‖z j‖ ^ 2 * ‖w i j‖)
      = (1 / 2) * (∑ j, ‖z j‖ ^ 2 * (∑ i, ‖w i j‖)) := by
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
  have h2 : ∑ i, ∑ j, ‖z i‖ * ‖z j‖ * ‖w i j‖
      ≤ (1 / 2) * (∑ i, ‖z i‖ ^ 2 * (∑ j, ‖w i j‖))
        + (1 / 2) * (∑ j, ‖z j‖ ^ 2 * (∑ i, ‖w i j‖)) := by
    calc ∑ i, ∑ j, ‖z i‖ * ‖z j‖ * ‖w i j‖
        ≤ ∑ i, ∑ j, ((1 / 2) * (‖z i‖ ^ 2 * ‖w i j‖)
            + (1 / 2) * (‖z j‖ ^ 2 * ‖w i j‖)) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpt i j))
      _ = ∑ i, ((∑ j, (1 / 2) * (‖z i‖ ^ 2 * ‖w i j‖))
            + (∑ j, (1 / 2) * (‖z j‖ ^ 2 * ‖w i j‖))) :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib)
      _ = (∑ i, ∑ j, (1 / 2) * (‖z i‖ ^ 2 * ‖w i j‖))
            + (∑ i, ∑ j, (1 / 2) * (‖z j‖ ^ 2 * ‖w i j‖)) := Finset.sum_add_distrib
      _ = (1 / 2) * (∑ i, ‖z i‖ ^ 2 * (∑ j, ‖w i j‖))
            + (1 / 2) * (∑ j, ‖z j‖ ^ 2 * (∑ i, ‖w i j‖)) := by rw [hA, hB]
  have hA' : ∑ i, ‖z i‖ ^ 2 * (∑ j, ‖w i j‖) ≤ C * ∑ i, ‖z i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [mul_comm (‖z i‖ ^ 2)]
    exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
  have hB' : ∑ j, ‖z j‖ ^ 2 * (∑ i, ‖w i j‖) ≤ C * ∑ j, ‖z j‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [mul_comm (‖z j‖ ^ 2)]
    exact mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
  have h3 : (1 / 2) * (∑ i, ‖z i‖ ^ 2 * (∑ j, ‖w i j‖))
      + (1 / 2) * (∑ j, ‖z j‖ ^ 2 * (∑ i, ‖w i j‖)) ≤ C * ∑ i, ‖z i‖ ^ 2 := by
    have h2' : (1 / 2) * (∑ j, ‖z j‖ ^ 2 * (∑ i, ‖w i j‖)) ≤ (1 / 2) * (C * ∑ i, ‖z i‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hB' (by norm_num)
    have h1' : (1 / 2) * (∑ i, ‖z i‖ ^ 2 * (∑ j, ‖w i j‖)) ≤ (1 / 2) * (C * ∑ i, ‖z i‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hA' (by norm_num)
    linarith
  exact h1.trans (h2.trans h3)

/-- `∑_{n ∈ s} 1/n² ≤ 2` for a finset of positive naturals (crude Basel bound). -/
lemma sum_inv_sq_le_two (s : Finset ℕ) (h : ∀ n ∈ s, 1 ≤ n) :
    ∑ n ∈ s, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 2 := by
  have hsumm : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := hasSum_zeta_two.summable
  have h1 : ∑ n ∈ s, (1 : ℝ) / (n : ℝ) ^ 2 ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 :=
    hsumm.sum_le_tsum s (fun n _ => by positivity)
  rw [hasSum_zeta_two.tsum_eq] at h1
  nlinarith [h1, Real.pi_lt_d2, Real.pi_pos]

/-- One side of the separation-sum bound: if for all `j ∈ s` one has `j ≠ i` and `γ i < γ j`,
then `∑_{j∈s} 1/(γ i - γ j)² ≤ 4/δ²`.  The proof injects `s` into the positive integers via
`j ↦ ⌊(γ j - γ i)/δ⌋₊`. -/
lemma sepSum_gt_le {m : ℕ} (γ : Fin m → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ a b : Fin m, a ≠ b → δ ≤ |γ a - γ b|) (i : Fin m) (s : Finset (Fin m))
    (hs : ∀ j ∈ s, j ≠ i ∧ γ i < γ j) :
    ∑ j ∈ s, (1 : ℝ) / (γ i - γ j) ^ 2 ≤ 4 / δ ^ 2 := by
  have hxge : ∀ j ∈ s, δ ≤ γ j - γ i := by
    intro j hj
    obtain ⟨hji, hjlt⟩ := hs j hj
    have hxpos : 0 < γ j - γ i := by linarith
    have h := hsep i j (Ne.symm hji)
    rw [abs_sub_comm, abs_of_pos hxpos] at h
    exact h
  have hpt : ∀ j ∈ s, (1 : ℝ) / (γ i - γ j) ^ 2
      ≤ (1 / δ ^ 2) * (1 / ((⌊(γ j - γ i) / δ⌋₊ : ℝ)) ^ 2) := by
    intro j hj
    have hge := hxge j hj
    have hF1 : 1 ≤ ⌊(γ j - γ i) / δ⌋₊ := by
      rw [Nat.one_le_floor_iff, one_le_div hδ]
      exact hge
    have hFle : (⌊(γ j - γ i) / δ⌋₊ : ℝ) * δ ≤ γ j - γ i := by
      have h := Nat.floor_le (div_nonneg (by linarith : (0:ℝ) ≤ γ j - γ i) (le_of_lt hδ))
      have h2 := mul_le_mul_of_nonneg_right h (le_of_lt hδ)
      rwa [div_mul_cancel₀ _ hδ.ne'] at h2
    have hFpos : (0 : ℝ) < (⌊(γ j - γ i) / δ⌋₊ : ℝ) := by
      exact_mod_cast (by omega : 0 < ⌊(γ j - γ i) / δ⌋₊)
    have hmain : (1 : ℝ) / (γ j - γ i) ^ 2
        ≤ (1 : ℝ) / (((⌊(γ j - γ i) / δ⌋₊ : ℝ)) ^ 2 * δ ^ 2) := by
      apply one_div_le_one_div_of_le (mul_pos (pow_pos hFpos 2) (pow_pos hδ 2))
      have hFsq : ((⌊(γ j - γ i) / δ⌋₊ : ℝ) * δ) ^ 2 ≤ (γ j - γ i) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hFle 2
      nlinarith [hFsq]
    calc (1 : ℝ) / (γ i - γ j) ^ 2 = (1 : ℝ) / (γ j - γ i) ^ 2 := by
          rw [show γ i - γ j = -(γ j - γ i) by ring, neg_sq]
      _ ≤ (1 : ℝ) / (((⌊(γ j - γ i) / δ⌋₊ : ℝ)) ^ 2 * δ ^ 2) := hmain
      _ = (1 / δ ^ 2) * (1 / ((⌊(γ j - γ i) / δ⌋₊ : ℝ)) ^ 2) := by
          rw [div_mul_div_comm]
          ring
  have hinj : ∀ x ∈ s, ∀ y ∈ s, ⌊(γ x - γ i) / δ⌋₊ = ⌊(γ y - γ i) / δ⌋₊ → x = y := by
    intro x hx y hy hxy
    obtain ⟨hxi, hxlt⟩ := hs x hx
    obtain ⟨hyi, hylt⟩ := hs y hy
    by_contra hne
    have hgne : γ x ≠ γ y := by
      intro h
      have h2 := hsep x y hne
      rw [h, sub_self, abs_zero] at h2
      linarith
    rcases lt_or_gt_of_ne hgne with hlt | hgt
    · have hstep : δ ≤ γ y - γ x := by
        have h := hsep x y hne
        rw [abs_of_neg (by linarith : γ x - γ y < 0)] at h
        linarith
      have hle : (γ x - γ i) / δ + 1 ≤ (γ y - γ i) / δ := by
        rw [div_add_one hδ.ne', div_le_div_iff₀ hδ hδ]
        nlinarith
      have hxnn : 0 ≤ (γ x - γ i) / δ := by positivity
      have hfl : ⌊(γ x - γ i) / δ⌋₊ + 1 ≤ ⌊(γ y - γ i) / δ⌋₊ := by
        calc ⌊(γ x - γ i) / δ⌋₊ + 1 = ⌊(γ x - γ i) / δ + 1⌋₊ := (Nat.floor_add_one hxnn).symm
          _ ≤ ⌊(γ y - γ i) / δ⌋₊ := Nat.floor_mono hle
      omega
    · have hstep : δ ≤ γ x - γ y := by
        have h := hsep x y hne
        rw [abs_of_pos (by linarith : 0 < γ x - γ y)] at h
        linarith
      have hle : (γ y - γ i) / δ + 1 ≤ (γ x - γ i) / δ := by
        rw [div_add_one hδ.ne', div_le_div_iff₀ hδ hδ]
        nlinarith
      have hynn : 0 ≤ (γ y - γ i) / δ := by positivity
      have hfl : ⌊(γ y - γ i) / δ⌋₊ + 1 ≤ ⌊(γ x - γ i) / δ⌋₊ := by
        calc ⌊(γ y - γ i) / δ⌋₊ + 1 = ⌊(γ y - γ i) / δ + 1⌋₊ := (Nat.floor_add_one hynn).symm
          _ ≤ ⌊(γ x - γ i) / δ⌋₊ := Nat.floor_mono hle
      omega
  have himg : ∑ j ∈ s, (1 / ((⌊(γ j - γ i) / δ⌋₊ : ℝ)) ^ 2)
      = ∑ n ∈ s.image (fun j => ⌊(γ j - γ i) / δ⌋₊), (1 / (n : ℝ) ^ 2) := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact hinj x hx y hy hxy
  have hnonzero : ∀ n ∈ s.image (fun j => ⌊(γ j - γ i) / δ⌋₊), 1 ≤ n := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    rw [Nat.one_le_floor_iff, one_le_div hδ]
    exact hxge j hj
  calc ∑ j ∈ s, (1 : ℝ) / (γ i - γ j) ^ 2
      ≤ ∑ j ∈ s, (1 / δ ^ 2) * (1 / ((⌊(γ j - γ i) / δ⌋₊ : ℝ)) ^ 2) := Finset.sum_le_sum hpt
    _ = (1 / δ ^ 2) * ∑ j ∈ s, (1 / ((⌊(γ j - γ i) / δ⌋₊ : ℝ)) ^ 2) := by
        rw [Finset.mul_sum]
    _ = (1 / δ ^ 2) * ∑ n ∈ s.image (fun j => ⌊(γ j - γ i) / δ⌋₊), (1 / (n : ℝ) ^ 2) := by
        rw [himg]
    _ ≤ (1 / δ ^ 2) * 2 :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_le_two _ hnonzero) (by positivity)
    _ ≤ 4 / δ ^ 2 := by
        rw [show (1:ℝ) / δ ^ 2 * 2 = 2 / δ ^ 2 by ring]
        rw [div_le_div_iff₀ (pow_pos hδ 2) (pow_pos hδ 2)]
        nlinarith [sq_nonneg δ]

/-- The separation-sum bound: for a `δ`-separated family, the sum of the reciprocal squares of the
distances from a fixed point is `O(1/δ²)`. -/
theorem sepSum_invSq_le {m : ℕ} (γ : Fin m → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i j : Fin m, i ≠ j → δ ≤ |γ i - γ j|) (i : Fin m) :
    ∑ j ∈ Finset.univ.erase i, (1 : ℝ) / (γ i - γ j) ^ 2 ≤ 8 / δ ^ 2 := by
  have hsplit : ∑ j ∈ Finset.univ.erase i, (1 : ℝ) / (γ i - γ j) ^ 2
      = ∑ j ∈ (Finset.univ.erase i).filter (fun j => γ i < γ j), (1 : ℝ) / (γ i - γ j) ^ 2
        + ∑ j ∈ (Finset.univ.erase i).filter (fun j => ¬ γ i < γ j), (1 : ℝ) / (γ i - γ j) ^ 2 :=
    (Finset.sum_filter_add_sum_filter_not (Finset.univ.erase i) (fun j : Fin m => γ i < γ j)
      (fun j => (1 : ℝ) / (γ i - γ j) ^ 2)).symm
  rw [hsplit]
  have hgt : ∑ j ∈ (Finset.univ.erase i).filter (fun j => γ i < γ j), (1 : ℝ) / (γ i - γ j) ^ 2
      ≤ 4 / δ ^ 2 := by
    refine sepSum_gt_le γ δ hδ hsep i _ (fun j hj => ?_)
    obtain ⟨hjm, hjl⟩ := Finset.mem_filter.mp hj
    exact ⟨(Finset.mem_erase.mp hjm).1, hjl⟩
  have hlt : ∑ j ∈ (Finset.univ.erase i).filter (fun j => ¬ γ i < γ j), (1 : ℝ) / (γ i - γ j) ^ 2
      ≤ 4 / δ ^ 2 := by
    have hsep' : ∀ a b : Fin m, a ≠ b → δ ≤ |(-γ a) - (-γ b)| := by
      intro a b hab
      have h := hsep a b hab
      rwa [show -γ a - -γ b = -(γ a - γ b) by ring, abs_neg]
    have hmain := sepSum_gt_le (fun j : Fin m => -γ j) δ hδ hsep' i
      ((Finset.univ.erase i).filter (fun j => ¬ γ i < γ j))
      (fun j hj => by
        obtain ⟨hjm, hjl⟩ := Finset.mem_filter.mp hj
        have hji : j ≠ i := (Finset.mem_erase.mp hjm).1
        have hle : γ j ≤ γ i := not_lt.mp hjl
        have hne : γ j ≠ γ i := by
          intro h
          have h2 := hsep i j (Ne.symm hji)
          rw [h, sub_self, abs_zero] at h2
          linarith
        have hltji : γ j < γ i := lt_of_le_of_ne hle hne
        exact ⟨hji, by show -γ i < -γ j; linarith⟩)
    simpa only [show ∀ j : Fin m, (1 : ℝ) / (-γ i - -γ j) ^ 2 = (1 : ℝ) / (γ i - γ j) ^ 2 by
      intro j; rw [show -γ i - -γ j = -(γ i - γ j) by ring, neg_sq]] using hmain
  have hadd : (4 : ℝ) / δ ^ 2 + 4 / δ ^ 2 = 8 / δ ^ 2 := by rw [← add_div]; norm_num
  linarith [hgt, hlt]

/-- The additive (sharp) Montgomery--Vaughan mean value theorem: for `δ`-separated frequencies the
mean square of `∑ᵢ ζᵢ e^{-2πiγᵢt}` over an interval of length `b - a` is at most
`((b-a) + 2/δ) ∑ᵢ ‖ζᵢ‖²`. -/
theorem additiveMvt (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (γ : Fin m → ℝ) (ζ : Fin m → ℂ)
    (a b : ℝ) (hab : a ≤ b) (hsep : ∀ i j, i ≠ j → δ ≤ |γ i - γ j|) :
    (∫ t in a..b, ‖∑ i, ζ i * Complex.exp (-(2 * Real.pi * Complex.I * (γ i : ℂ) * (t : ℂ)))‖ ^ 2)
      ≤ ((b - a) + 2 / δ) * ∑ i, ‖ζ i‖ ^ 2 := by
  set W : ℝ := δ⁻¹ with hWdef
  have hWpos : 0 < W := by rw [hWdef]; exact inv_pos.mpr hδ
  have hWne : W ≠ 0 := hWpos.ne'
  set L : ℝ := (b - a) + W with hLdef
  have hLpos : 0 < L := by rw [hLdef]; linarith
  set u₀ : ℝ := a - W with hu₀def
  have hu₀W : u₀ + W = a := by rw [hu₀def]; ring
  have hu₀L : u₀ + L = b := by rw [hu₀def, hLdef]; ring
  set F : ℝ → ℂ := fun t => ∑ i, ζ i * Complex.exp (-(2 * Real.pi * Complex.I * (γ i : ℂ) * (t : ℂ))) with hF
  have hFcont : Continuous F := by
    rw [hF]; fun_prop
  set w : Fin m → Fin m → ℂ := fun i j =>
      Complex.exp (-(2 * Real.pi * Complex.I * (((γ i - γ j : ℝ)) : ℂ) * (u₀ : ℂ)))
        * trapK L W (γ i - γ j) with hw
  have hstep1 : (∫ t in a..b, ‖F t‖ ^ 2) ≤ W⁻¹ * ∫ u in u₀..(u₀ + W), ∫ t in u..(u + L), ‖F t‖ ^ 2 := by
    have hmono : ∀ u ∈ Set.Icc u₀ (u₀ + W), (∫ t in a..b, ‖F t‖ ^ 2) ≤ ∫ t in u..(u + L), ‖F t‖ ^ 2 := by
      intro u hu
      obtain ⟨h1, h2⟩ := hu
      have hua : u ≤ a := by rw [← hu₀W]; exact h2
      have hbL : b ≤ u + L := by
        have h3 : u₀ + L ≤ u + L := by linarith
        rw [hu₀L] at h3
        exact h3
      refine intervalIntegral.integral_mono_interval hua hab hbL ?_ ?_
      · exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
      · exact (hFcont.norm.pow 2).intervalIntegrable _ _
    have hcont2 : Continuous (fun u : ℝ => ∫ t in u..(u + L), ‖F t‖ ^ 2) :=
      continuous_intervalIntegral_shift (fun t => ‖F t‖ ^ 2) (hFcont.norm.pow 2) L
    have h1 : (∫ u in u₀..(u₀ + W), (∫ t in a..b, ‖F t‖ ^ 2))
        ≤ ∫ u in u₀..(u₀ + W), ∫ t in u..(u + L), ‖F t‖ ^ 2 := by
      refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        (hcont2.intervalIntegrable _ _) hmono
    have h2 : W * (∫ t in a..b, ‖F t‖ ^ 2) ≤ ∫ u in u₀..(u₀ + W), ∫ t in u..(u + L), ‖F t‖ ^ 2 := by
      rwa [intervalIntegral.integral_const, smul_eq_mul,
        show u₀ + W - u₀ = W by ring] at h1
    have h3 : (∫ t in a..b, ‖F t‖ ^ 2) = W⁻¹ * (W * (∫ t in a..b, ‖F t‖ ^ 2)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hWne, one_mul]
    rw [h3]
    exact mul_le_mul_of_nonneg_left h2 (le_of_lt (inv_pos.mpr hWpos))
  have hdiagval : ∀ i, w i i = (L : ℂ) := by
    intro i
    have he : (2 * Real.pi * Complex.I * (((γ i - γ i : ℝ)) : ℂ) * (u₀ : ℂ)) = 0 := by
      rw [sub_self, Complex.ofReal_zero]
      ring
    rw [hw]
    simp only [he, neg_zero, Complex.exp_zero, one_mul]
    rw [show (γ i - γ i : ℝ) = 0 by ring, trapK_zero L W hWne]
  have hdiag : ∀ i, ‖w i i‖ ≤ L := by
    intro i
    rw [hdiagval i]
    simp [abs_of_pos hLpos]
  have hoffnorm : ∀ i j, i ≠ j → ‖w i j‖ ≤ (1 / (W * Real.pi ^ 2)) * (1 / (γ i - γ j) ^ 2) := by
    intro i j hij
    have hne : γ i - γ j ≠ 0 := by
      intro h
      have h2 := hsep i j hij
      rw [h, abs_zero] at h2
      linarith
    have hexpnorm : ‖Complex.exp (-(2 * Real.pi * Complex.I * (((γ i - γ j : ℝ)) : ℂ) * (u₀ : ℂ)))‖ = 1 := by
      rw [show -(2 * Real.pi * Complex.I * (((γ i - γ j : ℝ)) : ℂ) * (u₀ : ℂ))
          = ((-(2 * Real.pi * (γ i - γ j) * u₀) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have h1 : ‖w i j‖ = ‖trapK L W (γ i - γ j)‖ := by
      rw [hw]
      simp only
      rw [norm_mul, hexpnorm, one_mul]
    rw [h1]
    calc ‖trapK L W (γ i - γ j)‖ ≤ 1 / (W * Real.pi ^ 2 * (γ i - γ j) ^ 2) :=
          TrapKNormLe L W (γ i - γ j) hWpos hne
      _ = (1 / (W * Real.pi ^ 2)) * (1 / (γ i - γ j) ^ 2) := by
          rw [div_mul_div_comm]
          ring
  have hrow : ∀ i, ∑ j, ‖w i j‖ ≤ L + 8 / (Real.pi ^ 2 * δ) := by
    intro i
    have hsplit : ∑ j, ‖w i j‖ = ‖w i i‖ + ∑ j ∈ Finset.univ.erase i, ‖w i j‖ := by
      have h := Finset.sum_erase_add Finset.univ (fun j => ‖w i j‖) (Finset.mem_univ i)
      linarith [h]
    have hoff : ∑ j ∈ Finset.univ.erase i, ‖w i j‖
        ≤ (1 / (W * Real.pi ^ 2)) * ∑ j ∈ Finset.univ.erase i, (1 / (γ i - γ j) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun j hj => ?_)
      exact hoffnorm i j (Ne.symm (Finset.mem_erase.mp hj).1)
    have hgeom : (1 / (W * Real.pi ^ 2)) * (8 / δ ^ 2) = 8 / (Real.pi ^ 2 * δ) := by
      rw [hWdef]
      field_simp
    calc ∑ j, ‖w i j‖ = ‖w i i‖ + ∑ j ∈ Finset.univ.erase i, ‖w i j‖ := hsplit
      _ ≤ L + (1 / (W * Real.pi ^ 2)) * ∑ j ∈ Finset.univ.erase i, (1 / (γ i - γ j) ^ 2) :=
          add_le_add (hdiag i) hoff
      _ ≤ L + (1 / (W * Real.pi ^ 2)) * (8 / δ ^ 2) := by
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by positivity))
          exact sepSum_invSq_le γ δ hδ hsep i
      _ = L + 8 / (Real.pi ^ 2 * δ) := by rw [hgeom]
  have hcol : ∀ j, ∑ i, ‖w i j‖ ≤ L + 8 / (Real.pi ^ 2 * δ) := by
    intro j
    have hsplit : ∑ i, ‖w i j‖ = ‖w j j‖ + ∑ i ∈ Finset.univ.erase j, ‖w i j‖ := by
      have h := Finset.sum_erase_add Finset.univ (fun i => ‖w i j‖) (Finset.mem_univ j)
      linarith [h]
    have hoff : ∑ i ∈ Finset.univ.erase j, ‖w i j‖
        ≤ (1 / (W * Real.pi ^ 2)) * ∑ i ∈ Finset.univ.erase j, (1 / (γ i - γ j) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun i hi => ?_)
      exact hoffnorm i j (Finset.mem_erase.mp hi).1
    have hswap : ∑ i ∈ Finset.univ.erase j, (1 / (γ i - γ j) ^ 2)
        = ∑ i ∈ Finset.univ.erase j, (1 / (γ j - γ i) ^ 2) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [show γ i - γ j = -(γ j - γ i) by ring, neg_sq]
    have hgeom : (1 / (W * Real.pi ^ 2)) * (8 / δ ^ 2) = 8 / (Real.pi ^ 2 * δ) := by
      rw [hWdef]
      field_simp
    calc ∑ i, ‖w i j‖ = ‖w j j‖ + ∑ i ∈ Finset.univ.erase j, ‖w i j‖ := hsplit
      _ ≤ L + (1 / (W * Real.pi ^ 2)) * ∑ i ∈ Finset.univ.erase j, (1 / (γ i - γ j) ^ 2) :=
          add_le_add (hdiag j) hoff
      _ = L + (1 / (W * Real.pi ^ 2)) * ∑ i ∈ Finset.univ.erase j, (1 / (γ j - γ i) ^ 2) := by
          rw [hswap]
      _ ≤ L + (1 / (W * Real.pi ^ 2)) * (8 / δ ^ 2) := by
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by positivity))
          exact sepSum_invSq_le γ δ hδ hsep j
      _ = L + 8 / (Real.pi ^ 2 * δ) := by rw [hgeom]
  have hschur := schurQuad ζ w (L + 8 / (Real.pi ^ 2 * δ)) hrow hcol
  have hexp : ((W⁻¹ * ∫ u in u₀..(u₀ + W), ∫ t in u..(u + L), ‖F t‖ ^ 2 : ℝ) : ℂ)
      = ∑ i, ∑ j, ζ i * star (ζ j) * w i j := by
    rw [hF]
    conv_rhs => rw [hw]
    exact trapK_expansion m γ ζ L W u₀
  have hI : W⁻¹ * ∫ u in u₀..(u₀ + W), ∫ t in u..(u + L), ‖F t‖ ^ 2
      ≤ (L + 8 / (Real.pi ^ 2 * δ)) * ∑ i, ‖ζ i‖ ^ 2 := by
    have hnn : 0 ≤ W⁻¹ * ∫ u in u₀..(u₀ + W), ∫ t in u..(u + L), ‖F t‖ ^ 2 := by
      have h1 : 0 ≤ ∫ u in u₀..(u₀ + W), ∫ t in u..(u + L), ‖F t‖ ^ 2 :=
        intervalIntegral.integral_nonneg (by linarith) (fun u _ =>
          intervalIntegral.integral_nonneg (by linarith) (fun t _ => sq_nonneg _))
      exact mul_nonneg (le_of_lt (inv_pos.mpr hWpos)) h1
    calc W⁻¹ * ∫ u in u₀..(u₀ + W), ∫ t in u..(u + L), ‖F t‖ ^ 2
        = ‖((W⁻¹ * ∫ u in u₀..(u₀ + W), ∫ t in u..(u + L), ‖F t‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
      _ = ‖∑ i, ∑ j, ζ i * star (ζ j) * w i j‖ := by rw [hexp]
      _ ≤ (L + 8 / (Real.pi ^ 2 * δ)) * ∑ i, ‖ζ i‖ ^ 2 := hschur
  have harith : L + 8 / (Real.pi ^ 2 * δ) ≤ (b - a) + 2 / δ := by
    have hπ2 : (8 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have h1 : 8 / (Real.pi ^ 2 * δ) ≤ 1 / δ := by
      rw [div_le_div_iff₀ (mul_pos (by positivity) hδ) hδ]
      nlinarith [hπ2, hδ]
    calc L + 8 / (Real.pi ^ 2 * δ)
        = (b - a) + 1 / δ + 8 / (Real.pi ^ 2 * δ) := by rw [hLdef, hWdef]; ring
      _ ≤ (b - a) + 1 / δ + 1 / δ := add_le_add le_rfl h1
      _ = (b - a) + 2 / δ := by ring
  have hsum_nonneg : 0 ≤ ∑ i, ‖ζ i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  calc (∫ t in a..b, ‖∑ i, ζ i * Complex.exp (-(2 * Real.pi * Complex.I * (γ i : ℂ) * (t : ℂ)))‖ ^ 2)
      = ∫ t in a..b, ‖F t‖ ^ 2 := by rw [hF]
    _ ≤ W⁻¹ * ∫ u in u₀..(u₀ + W), ∫ t in u..(u + L), ‖F t‖ ^ 2 := hstep1
    _ ≤ (L + 8 / (Real.pi ^ 2 * δ)) * ∑ i, ‖ζ i‖ ^ 2 := hI
    _ ≤ ((b - a) + 2 / δ) * ∑ i, ‖ζ i‖ ^ 2 :=
        mul_le_mul_of_nonneg_right harith hsum_nonneg

/-- The power identity used to pass from the multiplicative variable `y` to `s = log y / 2π`. -/
lemma ofReal_exp_cpow (s γ : ℝ) :
    (((Real.exp (2 * Real.pi * s) : ℝ)) : ℂ) ^ (-(γ : ℂ) * Complex.I)
      = Complex.exp (-(2 * Real.pi * Complex.I * (γ : ℂ) * (s : ℂ))) := by
  have hpos : (0 : ℝ) < Real.exp (2 * Real.pi * s) := Real.exp_pos _
  have hne : (((Real.exp (2 * Real.pi * s) : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact ne_of_gt hpos
  rw [Complex.cpow_def_of_ne_zero hne]
  have hlog : Complex.log (((Real.exp (2 * Real.pi * s) : ℝ)) : ℂ) = ((2 * Real.pi * s : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log (le_of_lt hpos), Real.log_exp]
  rw [hlog]
  congr 1
  push_cast
  ring

/-- The substitution `y = e^{2πs}` for the multiplicative measure `dy/y`. -/
theorem integral_div_comp_exp {g : ℝ → ℝ} (Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₁₂ : Y₁ ≤ Y₂)
    (hg : ContinuousOn (fun y : ℝ => g y / y) (Set.Icc Y₁ Y₂)) :
    (∫ y in Y₁..Y₂, g y / y)
      = 2 * Real.pi * ∫ s in (Real.log Y₁ / (2 * Real.pi))..(Real.log Y₂ / (2 * Real.pi)),
          g (Real.exp (2 * Real.pi * s)) := by
  set a : ℝ := Real.log Y₁ / (2 * Real.pi) with hadef
  set b : ℝ := Real.log Y₂ / (2 * Real.pi) with hbdef
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hY₂pos : 0 < Y₂ := lt_of_lt_of_le hY₁ hY₁₂
  have hab : a ≤ b := by
    rw [hadef, hbdef]
    exact div_le_div_of_nonneg_right (Real.log_le_log hY₁ hY₁₂) (le_of_lt hπ)
  have hexpa : Real.exp (2 * Real.pi * a) = Y₁ := by
    rw [hadef, mul_div_cancel₀ _ hπ.ne', Real.exp_log hY₁]
  have hexpb : Real.exp (2 * Real.pi * b) = Y₂ := by
    rw [hbdef, mul_div_cancel₀ _ hπ.ne', Real.exp_log hY₂pos]
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun s : ℝ => Real.exp (2 * Real.pi * s))
      (2 * Real.pi * Real.exp (2 * Real.pi * x)) x := by
    intro x hx
    have h1 : HasDerivAt (fun s : ℝ => 2 * Real.pi * s) (2 * Real.pi) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * Real.pi)
    have h2 := (Real.hasDerivAt_exp (2 * Real.pi * x)).comp x h1
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using h2
  have hcont : ContinuousOn (fun s : ℝ => 2 * Real.pi * Real.exp (2 * Real.pi * s))
      (Set.uIcc a b) := by fun_prop
  have himg : (fun s : ℝ => Real.exp (2 * Real.pi * s)) '' Set.uIcc a b ⊆ Set.Icc Y₁ Y₂ := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := hy
    rw [Set.uIcc_of_le hab] at hs
    refine ⟨?_, ?_⟩
    · calc Y₁ = Real.exp (2 * Real.pi * a) := hexpa.symm
        _ ≤ Real.exp (2 * Real.pi * s) := Real.exp_le_exp.mpr (by nlinarith [hs.1, hπ])
    · calc Real.exp (2 * Real.pi * s)
          ≤ Real.exp (2 * Real.pi * b) := Real.exp_le_exp.mpr (by nlinarith [hs.2, hπ])
        _ = Y₂ := hexpb
  have hkey := intervalIntegral.integral_comp_mul_deriv' hderiv hcont (hg.mono himg)
  rw [hexpa, hexpb] at hkey
  have hsimp : ∀ x : ℝ,
      ((fun y : ℝ => g y / y) ∘ (fun s : ℝ => Real.exp (2 * Real.pi * s))) x
        * (2 * Real.pi * Real.exp (2 * Real.pi * x))
      = 2 * Real.pi * g (Real.exp (2 * Real.pi * x)) := by
    intro x
    simp only [Function.comp_apply]
    field_simp
  rw [intervalIntegral.integral_congr (fun x _ => hsimp x)] at hkey
  rw [intervalIntegral.integral_const_mul] at hkey
  exact hkey.symm

/-- **The multiplicative Montgomery--Vaughan mean value theorem**, with the constant `100`. -/
theorem mvtMul_100 : Work.ZeroDensity.LogFree.MvtMul 100 := by
  intro δ hδ m γ ζ Y₁ Y₂ hY₁ hY₁₂ hsep
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hY₂pos : 0 < Y₂ := lt_of_lt_of_le hY₁ hY₁₂
  set a : ℝ := Real.log Y₁ / (2 * Real.pi) with hadef
  set b : ℝ := Real.log Y₂ / (2 * Real.pi) with hbdef
  have hab : a ≤ b := by
    rw [hadef, hbdef]
    exact div_le_div_of_nonneg_right (Real.log_le_log hY₁ hY₁₂) (le_of_lt hπ)
  have hcpow : ∀ c : ℂ, ContinuousOn (fun y : ℝ => (y : ℂ) ^ c) (Set.Icc Y₁ Y₂) := by
    intro c
    refine ContinuousOn.cpow Complex.continuous_ofReal.continuousOn continuousOn_const ?_
    intro y hy
    exact Or.inl (lt_of_lt_of_le hY₁ hy.1)
  have hg : ContinuousOn (fun y : ℝ => ‖∑ i, ζ i * (y : ℂ) ^ (-(γ i : ℂ) * Complex.I)‖ ^ 2)
      (Set.Icc Y₁ Y₂) := by
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.norm ?_
    refine continuousOn_finsetSum _ (fun i _ => ?_)
    exact ContinuousOn.mul continuousOn_const (hcpow (-(γ i : ℂ) * Complex.I))
  have hcontdiv : ContinuousOn (fun y : ℝ => ‖∑ i, ζ i * (y : ℂ) ^ (-(γ i : ℂ) * Complex.I)‖ ^ 2 / y)
      (Set.Icc Y₁ Y₂) := by
    refine ContinuousOn.div hg continuousOn_id ?_
    intro y hy
    exact ne_of_gt (lt_of_lt_of_le hY₁ hy.1)
  have hsub := integral_div_comp_exp Y₁ Y₂ hY₁ hY₁₂ hcontdiv
  have hpoint : ∀ s : ℝ,
      ‖∑ i, ζ i * (((Real.exp (2 * Real.pi * s)) : ℝ) : ℂ) ^ (-(γ i : ℂ) * Complex.I)‖ ^ 2
        = ‖∑ i, ζ i * Complex.exp (-(2 * Real.pi * Complex.I * (γ i : ℂ) * (s : ℂ)))‖ ^ 2 := by
    intro s
    have h : ∑ i, ζ i * (((Real.exp (2 * Real.pi * s)) : ℝ) : ℂ) ^ (-(γ i : ℂ) * Complex.I)
        = ∑ i, ζ i * Complex.exp (-(2 * Real.pi * Complex.I * (γ i : ℂ) * (s : ℂ))) :=
      Finset.sum_congr rfl (fun i _ => by rw [ofReal_exp_cpow])
    rw [h]
  have hsub2 : (∫ s in a..b,
        ‖∑ i, ζ i * (((Real.exp (2 * Real.pi * s)) : ℝ) : ℂ) ^ (-(γ i : ℂ) * Complex.I)‖ ^ 2)
      = ∫ s in a..b,
        ‖∑ i, ζ i * Complex.exp (-(2 * Real.pi * Complex.I * (γ i : ℂ) * (s : ℂ)))‖ ^ 2 :=
    intervalIntegral.integral_congr (fun s _ => hpoint s)
  have hadd := additiveMvt δ hδ m γ ζ a b hab hsep
  have hS : 0 ≤ ∑ i, ‖ζ i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have harith : 2 * Real.pi * ((b - a) + 2 / δ) ≤ Real.log (Y₂ / Y₁) + 100 / δ := by
    have h1 : 2 * Real.pi * (b - a) = Real.log (Y₂ / Y₁) := by
      rw [hbdef, hadef,
        Real.log_div (x := Y₂) (y := Y₁) (ne_of_gt hY₂pos) (ne_of_gt hY₁)]
      field_simp
    have h2 : 2 * Real.pi * (2 / δ) ≤ 100 / δ := by
      rw [show 2 * Real.pi * (2 / δ) = 4 * Real.pi / δ by ring,
        div_le_div_iff₀ hδ hδ]
      nlinarith [Real.pi_lt_four, Real.pi_pos, hδ]
    have hdist : 2 * Real.pi * ((b - a) + 2 / δ)
        = 2 * Real.pi * (b - a) + 2 * Real.pi * (2 / δ) := by ring
    rw [hdist]
    linarith
  calc (∫ y in Y₁..Y₂, ‖∑ i, ζ i * (y : ℂ) ^ (-(γ i : ℂ) * Complex.I)‖ ^ 2 / y)
      = 2 * Real.pi * ∫ s in a..b,
          ‖∑ i, ζ i * (((Real.exp (2 * Real.pi * s)) : ℝ) : ℂ) ^ (-(γ i : ℂ) * Complex.I)‖ ^ 2 :=
        hsub
    _ = 2 * Real.pi * ∫ s in a..b,
          ‖∑ i, ζ i * Complex.exp (-(2 * Real.pi * Complex.I * (γ i : ℂ) * (s : ℂ)))‖ ^ 2 := by
        rw [hsub2]
    _ ≤ 2 * Real.pi * (((b - a) + 2 / δ) * ∑ i, ‖ζ i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hadd (by positivity)
    _ ≤ (Real.log (Y₂ / Y₁) + 100 / δ) * ∑ i, ‖ζ i‖ ^ 2 := by
        rw [show 2 * Real.pi * (((b - a) + 2 / δ) * ∑ i, ‖ζ i‖ ^ 2)
            = (2 * Real.pi * ((b - a) + 2 / δ)) * ∑ i, ‖ζ i‖ ^ 2 by ring]
        exact mul_le_mul_of_nonneg_right harith hS

/-- **Heath-Brown §11, L4**: the mean value theorem for `1/δ`-separated frequencies, as used by
the damped pole bound.  The constant `100` is that of the interface `LogFree.MvtMul`. -/
theorem HB7MvtMul : ∃ C : ℝ, 0 < C ∧ Work.ZeroDensity.LogFree.MvtMul C :=
  ⟨100, by norm_num, mvtMul_100⟩

end Work.ZeroDensity
