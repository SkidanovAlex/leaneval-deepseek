import Mathlib
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Residues.ResidueTheoremK

open MeasureTheory UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics

open Work.Kernels

/-! ## The two ingredients

The recurrence `T2op (kernelTransform K · r) = 0` is the combination of two facts:

* the *pointwise* kernel identity `K(·,it)|^τ_{d/2}(T-I)² = 0` of CKMRV Theorem 4.9(2), i.e.
  `T2op (fun σ ↦ Kaxis K σ t) = 0` for every `t` (`Kaxis_Kfun_T2` below, from
  `Work.Residues.Kfun_T2` and the definition of `Kaxis`);
* the *linearity* of the Bochner integral, which allows the three contour integrals at `τ`,
  `τ+1`, `τ+2` to be recombined into the single integral of the `(T-I)²`-defect of the
  integrand (`T2op_const_mul_integral` below).  This is where the three Bochner
  integrability hypotheses of the statement are consumed. -/

/-- The pointwise kernel identity behind the `(T-I)²`-recurrence, in the `t`-variable of the
contour integral: the function `σ ↦ Kaxis K σ t` is annihilated by `(T-I)²`, for every real
`t` (including `t ≤ 0`, where `Kaxis` is `0` by definition). -/
lemma Kaxis_Kfun_T2 (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (t : ℝ) :
    T2op (fun σ : ℍ => Kaxis (Kfun ℓ d) σ t) = 0 := by
  by_cases ht : 0 < t
  · rw [show (fun σ : ℍ => Kaxis (Kfun ℓ d) σ t) = (fun σ : ℍ => Kfun ℓ d σ (imagAxis t ht))
        from by funext σ; simp only [Kaxis, dif_pos ht]]
    exact Work.Residues.Kfun_T2 ℓ d hd (imagAxis t ht)
  · rw [show (fun σ : ℍ => Kaxis (Kfun ℓ d) σ t) = (fun _ : ℍ => (0:ℂ))
        from by funext σ; simp only [Kaxis, dif_neg ht]]
    funext τ
    simp only [T2op, Pi.zero_apply]
    ring

/-- **The `(T-I)²`-recurrence for a contour integral.**  If the kernel `K` is annihilated by
`(T-I)²` in its first variable on the imaginary axis (`hpoint`) and the three contour
integrands at `τ`, `τ+1`, `τ+2` are Bochner integrable (`h0`, `h1`, `h2`), then the contour
integral `σ ↦ s · ∫_0^∞ K(σ,it) c(t) dt` is annihilated by `(T-I)²` at `τ`.

The three integrability hypotheses are exactly what is needed to split the Bochner integral
`∫_0^∞ (K(τ+2,it) - 2K(τ+1,it) + K(τ,it)) c(t) dt` into the three integrals at `τ+2`,
`τ+1`, `τ` (and conversely); the integrand of that combined integral is then pointwise `0`
by `hpoint`. -/
lemma T2op_const_mul_integral (K : ℍ → ℍ → ℂ) (c : ℝ → ℂ) (s : ℂ) (τ : ℍ)
    (hpoint : ∀ t : ℝ, T2op (fun σ : ℍ => Kaxis K σ t) τ = 0)
    (h0 : IntegrableOn (fun t : ℝ => Kaxis K τ t * c t) (Set.Ioi 0))
    (h1 : IntegrableOn (fun t : ℝ => Kaxis K (((1:ℝ)+ᵥτ)) t * c t) (Set.Ioi 0))
    (h2 : IntegrableOn (fun t : ℝ => Kaxis K (((2:ℝ)+ᵥτ)) t * c t) (Set.Ioi 0)) :
    T2op (fun σ : ℍ => s * ∫ t in Set.Ioi 0, Kaxis K σ t * c t) τ = 0 := by
  have hA : IntegrableOn (fun t : ℝ => Kaxis K (((2:ℝ)+ᵥτ)) t * c t
      - 2 * (Kaxis K (((1:ℝ)+ᵥτ)) t * c t)) (Set.Ioi 0) :=
    h2.sub (MeasureTheory.Integrable.const_mul h1 2)
  have hcm : (∫ t in Set.Ioi 0, (2:ℂ) * (Kaxis K (((1:ℝ)+ᵥτ)) t * c t))
      = 2 * (∫ t in Set.Ioi 0, Kaxis K (((1:ℝ)+ᵥτ)) t * c t) :=
    MeasureTheory.integral_const_mul 2 _
  have hsub : (∫ t in Set.Ioi 0, Kaxis K (((2:ℝ)+ᵥτ)) t * c t)
      - 2 * (∫ t in Set.Ioi 0, Kaxis K (((1:ℝ)+ᵥτ)) t * c t)
      = ∫ t in Set.Ioi 0, (Kaxis K (((2:ℝ)+ᵥτ)) t * c t
          - 2 * (Kaxis K (((1:ℝ)+ᵥτ)) t * c t)) := by
    rw [← hcm]
    exact (MeasureTheory.integral_sub h2 (MeasureTheory.Integrable.const_mul h1 2)).symm
  have hadd : (∫ t in Set.Ioi 0, (Kaxis K (((2:ℝ)+ᵥτ)) t * c t
        - 2 * (Kaxis K (((1:ℝ)+ᵥτ)) t * c t)))
      + (∫ t in Set.Ioi 0, Kaxis K τ t * c t)
      = ∫ t in Set.Ioi 0, (Kaxis K (((2:ℝ)+ᵥτ)) t * c t
        - 2 * (Kaxis K (((1:ℝ)+ᵥτ)) t * c t) + Kaxis K τ t * c t) :=
    (MeasureTheory.integral_add hA h0).symm
  have hz : (fun t : ℝ => Kaxis K (((2:ℝ)+ᵥτ)) t * c t
        - 2 * (Kaxis K (((1:ℝ)+ᵥτ)) t * c t) + Kaxis K τ t * c t)
      = fun _ : ℝ => (0:ℂ) := by
    funext t
    have h := hpoint t
    simp only [T2op] at h
    have h' : Kaxis K (((2:ℝ)+ᵥτ)) t * c t - 2 * (Kaxis K (((1:ℝ)+ᵥτ)) t * c t)
        + Kaxis K τ t * c t
        = (Kaxis K (((2:ℝ)+ᵥτ)) t - 2 * Kaxis K (((1:ℝ)+ᵥτ)) t + Kaxis K τ t) * c t := by
      ring
    rw [h', h, zero_mul]
  have hmain : (∫ t in Set.Ioi 0, Kaxis K (((2:ℝ)+ᵥτ)) t * c t)
      - 2 * (∫ t in Set.Ioi 0, Kaxis K (((1:ℝ)+ᵥτ)) t * c t)
      + (∫ t in Set.Ioi 0, Kaxis K τ t * c t) = 0 := by
    rw [hsub, hadd, hz]
    simp
  simp only [T2op]
  have hfac : s * (∫ t in Set.Ioi 0, Kaxis K (((2:ℝ)+ᵥτ)) t * c t)
      - 2 * (s * (∫ t in Set.Ioi 0, Kaxis K (((1:ℝ)+ᵥτ)) t * c t))
      + s * (∫ t in Set.Ioi 0, Kaxis K τ t * c t)
      = s * ((∫ t in Set.Ioi 0, Kaxis K (((2:ℝ)+ᵥτ)) t * c t)
        - 2 * (∫ t in Set.Ioi 0, Kaxis K (((1:ℝ)+ᵥτ)) t * c t)
        + (∫ t in Set.Ioi 0, Kaxis K τ t * c t)) := by
    ring
  rw [hfac, hmain, mul_zero]

/-- The `(T-I)²`-recurrence for the naive contour integral, on the region where that integral
converges (declare in namespace `Work.Asymptotics`).  This is the *intermediate* step of CKMRV
Proposition 4.6 / Corollary 4.1, and it is **not** the paper's `h5a`: the paper's `F₂` is the
analytic continuation of the integral past the lines `Re τ = ±1`, and the two differ by the
residue correction `4 e^{πir²(τ-1)}sin²(πr²/2)` of `(matchF2sharp)`, so that
`T2op F₂ = -T2op (gaussTerm · r) ≠ 0` while `T2op` of the integral vanishes.  Pointwise the
statement is the kernel identity `K(·,it)|^τ_{d/2}(T-I)² = 0` of Theorem 4.9(2)
(`Work.Kernels.KPlus_slash_T2`, `Work.Kernels.KMinus_slash_T2`) integrated against `e^{-πr²t}`;
the three hypotheses say that the three contour integrands (at `τ`, `τ+1`, `τ+2`) are Bochner
integrable, exactly the shape in which the companion
`Work.Residues.slash_Kfun_kernelTransform_eq_zero` states `h5b`. -/
theorem T2op_kernelTransform (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) (τ : UpperHalfPlane)
    (h0 : MeasureTheory.IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t *
      Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0))
    (h1 : MeasureTheory.IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d)
      (((1 : ℝ) +ᵥ τ)) t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0))
    (h2 : MeasureTheory.IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d)
      (((2 : ℝ) +ᵥ τ)) t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0)) :
    Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.kernelTransform
      (Work.Kernels.Kfun ℓ d) σ r) τ = 0 := by
  refine T2op_const_mul_integral (Kfun ℓ d)
    (fun t : ℝ => Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
    (4 * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2) τ (fun t => ?_) h0 h1 h2
  exact congr_fun (Kaxis_Kfun_T2 ℓ d hd t) τ

end Work.Asymptotics
