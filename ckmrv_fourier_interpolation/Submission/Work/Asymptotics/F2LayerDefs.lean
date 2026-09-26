/-
# The CKMRV layer `F₂` on the fundamental domain `𝒟`: definitions

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, *Universal optimality of the `E₈` and
Leech lattices and interpolation formulas*, Ann. of Math. 196 (2022)) define, in (5.2)--(5.3),
the generating function `F₂` on the fundamental domain

  `𝒟 = {z ∈ ℍ : -1 < Re z < 1, |z - 1/2| > 1/2, |z + 1/2| > 1/2}`

of `Γ(2)` by the `low + trunc + high` decomposition of the contour integral

  `4 sin²(πr²/2) ∫_0^∞ K(τ,it) e^{-πr²t} dt`.

* `low` is the piece of the contour over `(0,1]`;
* `trunc` is the piece over `[1,∞)` with the non-decaying part `𝒢(τ,it)` of the kernel
  subtracted (this is absolutely convergent for every `r`);
* `high` is the *closed form* of `4 sin²(πr²/2) ∫_1^∞ 𝒢(τ,it) e^{-πr²t} dt`, which is where
  the extension to all `r ∈ ℝ` comes from: the apparent poles at `λ = πr² = 0` and
  `μ = πr² - 2π = 0` are cancelled by the double zeros of `2 - 2cos(πr²) = 4 sin²(πr²/2)`.

The non-decaying part `𝒢` of the kernel along the contour is (CKMRV, Section 4.5)

  `𝒢(τ,z) = Σ_{k=-1}^{0} Σ_{j=0}^{1} z^j e^{2πikz} 𝒢_{k,j}(τ)`,  i.e. at `z = it`,

  `A(τ,t) = G_{0,0}(τ) + it·G_{0,1}(τ) + e^{2πt}·(G_{-1,0}(τ) + it·G_{-1,1}(τ))`,

with coefficient functions `𝒢_{k,j}` of moderate growth on `𝒟`; for `d = 8` one has
`𝒢^{(8)}_{-1,j} = 0`, which is exactly why in eight dimensions the integral converges for every
`r ≠ 0` while in twenty-four dimensions it needs `|r| > √2`.

The existence of the coefficients `G i j` and the two asymptotic facts (flatness at the cusp
`0` and the expansion at the cusp `∞`) are the two analytic inputs of the whole chapter; they
are *not* proved here.  Everything in this file is the interface: the definitions and the
elementary properties of the regularising factor `psi1`.

## Main definitions

* `Work.Asymptotics.psi1 x = 2(1 - cos x)/x²` (continued by its integral representation);
* `Work.Asymptotics.Aexp G τ t` — the non-decaying part `𝒢(τ,it)` of the kernel, given the
  coefficient functions `G`;
* `Work.Asymptotics.highPart G τ r` — the closed form of `4 sin²(πr²/2) ∫_1^∞ 𝒢(τ,it) e^{-πr²t}dt`;
* `Work.Asymptotics.layerLow`, `Work.Asymptotics.layerTrunc`, `Work.Asymptotics.paperLayer` —
  the paper's decomposition (5.3), and the layer itself;
* `Work.Asymptotics.layer` — `paperLayer` with the single value at `r = 0` replaced by `0`; this
  is the function whose `r`-seminorms are bounded, and which agrees with the Bochner integral
  `Work.Kernels.kernelTransform` everywhere the latter is determined.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.Basic
import Submission.Work.Kernels.ModerateGrowth

noncomputable section

open MeasureTheory UpperHalfPlane
open scoped Topology

namespace Work.Asymptotics

open Work.Kernels

/-- The regularising factor `psi1 x = 2(1 - cos x)/x²`, extended to `x = 0` by its integral
representation `2 ∫_0^1 (1-s) cos(s x) ds`.  It is smooth, equals `1` at `0`, and satisfies
`x² * psi1 x = 2 - 2 cos x`; the zero of `2 - 2cos(πr²) = 4 sin²(πr²/2)` at `λ = πr² = 0`
is therefore double, which is what regularises the `high` part of the layer. -/
def psi1 (x : ℝ) : ℝ := 2 * ∫ s in (0 : ℝ)..1, (1 - s) * Real.cos (s * x)

/-- The elementary integral `∫_0^1 (1-s) cos(s x) ds = (1 - cos x)/x²` for `x ≠ 0`
(integration by parts with the primitive `s ↦ (1-s) sin(s x)/x`). -/
theorem integral_one_sub_mul_cos {x : ℝ} (hx : x ≠ 0) :
    ∫ s in (0 : ℝ)..1, (1 - s) * Real.cos (s * x) = (1 - Real.cos x) / x ^ 2 := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => (1 - s) * (Real.sin (s * x) / x))
        ((1 - s) * Real.cos (s * x) - Real.sin (s * x) / x) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1 : ℝ) s := by
      simpa using (hasDerivAt_id s).const_sub (1 : ℝ)
    have h2 : HasDerivAt (fun s : ℝ => Real.sin (s * x) / x) (Real.cos (s * x)) s := by
      have h3 : HasDerivAt (fun s : ℝ => Real.sin (s * x)) (Real.cos (s * x) * x) s := by
        simpa [Function.comp_def] using
          (Real.hasDerivAt_sin (s * x)).comp s (hasDerivAt_mul_const x)
      have h4 : HasDerivAt (fun s : ℝ => Real.sin (s * x) / x) ((Real.cos (s * x) * x) / x) s :=
        h3.div_const x
      rw [mul_div_cancel_right₀ _ hx] at h4
      exact h4
    exact (h1.mul h2).congr_deriv (by ring)
  have hcont : Continuous fun s : ℝ =>
      (1 - s) * Real.cos (s * x) - Real.sin (s * x) / x := by fun_prop
  have hkey := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable 0 1)
  have hzero : (fun s : ℝ => (1 - s) * (Real.sin (s * x) / x)) 1
      - (fun s : ℝ => (1 - s) * (Real.sin (s * x) / x)) 0 = 0 := by
    simp
  rw [hzero] at hkey
  have hc1 : IntervalIntegrable (fun s : ℝ => (1 - s) * Real.cos (s * x)) volume (0 : ℝ) 1 :=
    ((by fun_prop : Continuous fun s : ℝ => (1 - s) * Real.cos (s * x))).intervalIntegrable 0 1
  have hc2 : IntervalIntegrable (fun s : ℝ => Real.sin (s * x) / x) volume (0 : ℝ) 1 :=
    ((by fun_prop : Continuous fun s : ℝ => Real.sin (s * x) / x)).intervalIntegrable 0 1
  have hsplit : ∫ s in (0 : ℝ)..1, ((1 - s) * Real.cos (s * x) - Real.sin (s * x) / x)
      = (∫ s in (0 : ℝ)..1, (1 - s) * Real.cos (s * x))
        - ∫ s in (0 : ℝ)..1, Real.sin (s * x) / x :=
    intervalIntegral.integral_sub hc1 hc2
  rw [hsplit] at hkey
  have hsin0 : ∫ s in (0 : ℝ)..1, Real.sin (x * s) = x⁻¹ * (1 - Real.cos x) := by
    rw [intervalIntegral.integral_comp_mul_left (fun u : ℝ => Real.sin u) hx]
    rw [integral_sin]
    simp
  have hsin : ∫ s in (0 : ℝ)..1, Real.sin (s * x) / x = (1 - Real.cos x) / x ^ 2 := by
    rw [intervalIntegral.integral_div]
    have : (fun s : ℝ => Real.sin (s * x)) = fun s : ℝ => Real.sin (x * s) := by
      funext s; rw [mul_comm]
    rw [this, hsin0]
    field_simp
  linarith [hkey, hsin]

/-- `x ^ 2 * psi1 x = 2 - 2 cos x`. -/
theorem sq_mul_psi1 (x : ℝ) : x ^ 2 * psi1 x = 2 - 2 * Real.cos x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [psi1]
  · rw [psi1, integral_one_sub_mul_cos hx]
    field_simp

/-- `psi1 0 = 1`. -/
theorem psi1_zero : psi1 0 = 1 := by
  have hI : ∫ s in (0 : ℝ)..1, (1 - s) = 1 / 2 := by
    rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => u) 1]
    norm_num [integral_id]
  rw [psi1]
  simp only [mul_zero, Real.cos_zero, mul_one]
  rw [hI]
  norm_num

/-- The non-decaying part `𝒢(τ,it)` of the CKMRV kernel along the contour `z = i t`, in terms
of the coefficient functions `G i j` of the cusp-`i∞` expansion.  The first index selects the
exponential `e^{2πikz}` (`i = 0` corresponds to `k = 0`, i.e. `1`, and `i = 1` to `k = -1`,
i.e. `e^{2πt}` at `z = it`), the second the power `z^j` of the polynomial factor. -/
def Aexp (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (t : ℝ) : ℂ :=
  G 0 0 τ + ((t : ℂ) * Complex.I) * G 0 1 τ +
    Complex.exp (2 * Real.pi * t) * (G 1 0 τ + ((t : ℂ) * Complex.I) * G 1 1 τ)

/-- The closed form of `4 sin²(πr²/2) ∫_1^∞ 𝒢(τ,it) e^{-πr²t} dt`, written with the double zeros
at `λ = πr² = 0` and `μ = πr² - 2π = 0` regularised by `psi1`:

  `λ·psi1 λ·e^{-λ}G₀₀ + i·psi1 λ·(λ+1)e^{-λ}G₀₁ + μ·psi1 μ·e^{-μ}G₁₀ + i·psi1 μ·(μ+1)e^{-μ}G₁₁`. -/
def highPart (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (r : ℝ) : ℂ :=
  let l : ℂ := ((Real.pi * r ^ 2 : ℝ) : ℂ)
  let m : ℂ := ((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ)
  l * (psi1 (Real.pi * r ^ 2) : ℂ) * Complex.exp (-l) * G 0 0 τ +
    Complex.I * (psi1 (Real.pi * r ^ 2) : ℂ) * (l + 1) * Complex.exp (-l) * G 0 1 τ +
    m * (psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ) * Complex.exp (-m) * G 1 0 τ +
    Complex.I * (psi1 (Real.pi * r ^ 2 - 2 * Real.pi) : ℂ) * (m + 1) * Complex.exp (-m)
      * G 1 1 τ

/-- The `low` part of the layer: the contribution of the compact piece `(0,1]` of the contour. -/
def layerLow (ℓ : LogLambdaData) (d : ℕ) (τ : ℍ) (r : ℝ) : ℂ :=
  sinSq r * ∫ t in (0 : ℝ)..1,
    Kaxis (Kfun ℓ d) τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))

/-- The `trunc` part of the layer: the contribution of `[1,∞)` after subtracting the
non-decaying part `Aexp`. -/
def layerTrunc (G : Fin 2 → Fin 2 → ℍ → ℂ) (ℓ : LogLambdaData) (d : ℕ) (τ : ℍ) (r : ℝ) : ℂ :=
  sinSq r * ∫ t in Set.Ici (1 : ℝ),
    (Kaxis (Kfun ℓ d) τ t - Aexp G τ t) * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))

/-- **The CKMRV layer `F₂`**, defined for *all* `τ ∈ ℍ` and `r ∈ ℝ` by the `low + trunc + high`
decomposition (5.2)--(5.3).  It agrees with `4 sin²(πr²/2) ∫_0^∞ K(τ,it)e^{-πr²t}dt` wherever
that integral converges, and is a function of `λ = πr²` that is smooth in `r`. -/
def paperLayer (G : Fin 2 → Fin 2 → ℍ → ℂ) (ℓ : LogLambdaData) (d : ℕ) (τ : ℍ) (r : ℝ) : ℂ :=
  layerLow ℓ d τ r + layerTrunc G ℓ d τ r + highPart G τ r

/-- The layer fed to `Work.Asymptotics.kernelTransform_seminorm_of_layer`: the paper's `F₂`
with the single value at `r = 0` replaced by `0`.  Both `paperLayer` and
`Work.Kernels.kernelTransform` take the value `0` at `r = 0` after this replacement
(`Work.Kernels.kernelTransform K τ 0 = 4 sin²(0)·(junk) = 0`), while the paper's `F₂` has the
non-zero limit `i·𝒢_{0,1}(τ)` there; the seminorms with the weights `|r|^k`, `k ≥ 1`, are
unaffected. -/
def layer (G : Fin 2 → Fin 2 → ℍ → ℂ) (ℓ : LogLambdaData) (d : ℕ) (τ : ℍ) (r : ℝ) : ℂ :=
  if r = 0 then 0 else paperLayer G ℓ d τ r


/-- **The tail control of the cusp expansion of the kernel along the contour.**

The cusp-`i∞` expansion `K^{(d)}(τ,it) ≈ Aexp G τ t` is valid only in the region where `z = it`
lies above all the poles of `z ↦ K^{(d)}(τ,z)`, i.e. for `t > max { Im z : z ∈ SL(2,ℤ)·τ }`, a
`τ`-dependent threshold which is bounded by `(scale τ)^{N₀}`.  In the remaining window
`1 ≤ t ≤ (scale τ)^{N₀}` the *difference* `K - Aexp` is only polynomially bounded (it is *not*
exponentially small there: for `τ = iT`, `K(iT,it)` is exponentially small for `t < T` while
`Aexp(iT,t) ≈ T - t`), so the two regimes have to be recorded separately:

* a polynomial bound on all of `[1,∞)`;
* exponential decay `e^{-πt}` beyond the threshold `(scale τ)^{N₀}`.

This is exactly what is needed to bound the `trunc` piece of the layer: on `[p, (scale τ)^{N₀}]`
the integrand is polynomial, hence its contribution is `e^{-λ p}`-suppressed; beyond the threshold
the `e^{-πt}` decay makes the integral super-polynomially small in `λ`.

**WARNING (this predicate is FALSE for general `τ ∈ 𝒟`, and is recorded only as the shape of the
input).**  For fixed `z = iY` the map `τ ↦ K^{(d)}(τ,z)` has a simple pole at `τ = 1 + z` with
residue `-1/(2π) ≠ 0` (CKMRV Theorem 4.9(3); the workspace lemmas
`Work.Residues.hasResidue_KPlus_vadd_one`, `Work.Residues.hasResidue_KMinus_T`,
`Work.Residues.hasResidue_slash_Kfun` formalise it).  Hence for `τ_δ = (1-δ) + iY ∈ 𝒟` one has
`‖K^{(d)}(τ_δ, iY)‖ ≥ c/δ → ∞` while `scale τ_δ` stays bounded, so **no** bound with
`(scale τ)`-constants can hold for all `τ ∈ 𝒟` and all `t ≥ 1`; both conjuncts below fail.  The
correct statements are local: on a compact `K ⊆ 𝒟` the poles stay a positive distance away (see
`Work.Asymptotics.Kaxis_local_flat`, `Work.Asymptotics.paperLayer_local_seminorm`), and the global
statement must be obtained by the cusp reduction of CKMRV §5.2 (contour shift to the `α`-contours).
Do not expect to prove this predicate. -/
def TailBound (ℓ : LogLambdaData) (d : ℕ) (G : Fin 2 → Fin 2 → ℍ → ℂ) : Prop :=
  (∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ (τ : ℍ), τ ∈ DomainD → ∀ t : ℝ, 1 ≤ t →
    ‖Kaxis (Kfun ℓ d) τ t - Aexp G τ t‖ ≤ C * (scale τ) ^ N * (1 + t) ^ M) ∧
  (∃ N₀ C N M : ℝ, 0 ≤ N₀ ∧ 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ (τ : ℍ), τ ∈ DomainD → ∀ t : ℝ,
    (scale τ) ^ N₀ ≤ t →
    ‖Kaxis (Kfun ℓ d) τ t - Aexp G τ t‖ ≤ C * (scale τ) ^ N * t ^ M * Real.exp (-(Real.pi * t)))

end Work.Asymptotics

