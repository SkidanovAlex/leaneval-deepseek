import Mathlib
import Submission.Work.FunctionalEquations.Coefficients
import Submission.Work.FunctionalEquations.ExpansionFromFunctionalEquations
import Submission.Work.FunctionalEquations.SummableExpansionTerms
import Submission.Work.Sampling.rapidlyDecreasing_coeffs
import Submission.Work.FunctionalEquations.ParametricDerivBounds
import Submission.Work.FunctionalEquations.HasDerivAtParametricIntegral

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology MeasureTheory
open scoped FourierTransform SchwartzMap Interval

noncomputable section

/-!
# Term-by-term radial differentiation of the CKMRV Fourier expansions

...
-/

/-- The `a`-kernel at a general height `y > 0`: `F(τ,·) - τ (F(τ+1,·) - F(τ,·))` at `τ = u + i y`. -/
def heightKernel {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (y u : ℝ) (x : E n) : ℂ :=
  S.F ((u : ℂ) + (y : ℂ) * Complex.I) x
    - ((u : ℂ) + (y : ℂ) * Complex.I)
      * (S.F ((u : ℂ) + (y : ℂ) * Complex.I + 1) x - S.F ((u : ℂ) + (y : ℂ) * Complex.I) x)

/-- The `b`-kernel at a general height `y > 0`: `F(τ+1,·) - F(τ,·)` at `τ = u + i y`. -/
def heightBKernel {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (y u : ℝ) (x : E n) : ℂ :=
  S.F ((u : ℂ) + (y : ℂ) * Complex.I + 1) x - S.F ((u : ℂ) + (y : ℂ) * Complex.I) x

/-- The `a`-kernel at a general height `y > 0` for `F̃`. -/
def heightKernelT {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (y u : ℝ) (x : E n) : ℂ :=
  S.Ftilde ((u : ℂ) + (y : ℂ) * Complex.I) x
    - ((u : ℂ) + (y : ℂ) * Complex.I)
      * (S.Ftilde ((u : ℂ) + (y : ℂ) * Complex.I + 1) x
          - S.Ftilde ((u : ℂ) + (y : ℂ) * Complex.I) x)

/-- The `b`-kernel at a general height `y > 0` for `F̃`. -/
def heightBKernelT {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (y u : ℝ) (x : E n) : ℂ :=
  S.Ftilde ((u : ℂ) + (y : ℂ) * Complex.I + 1) x
    - S.Ftilde ((u : ℂ) + (y : ℂ) * Complex.I) x

/-- **The coefficient formula at any height `y > 0`.**  The `m`-th `a`-coefficient, defined as a
contour integral at height `1`, is also given by the contour integral at height `y`. -/
lemma aCoeff_eq_heightKernel {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (x : E n) {y : ℝ} (hy : 0 < y) :
    aCoeff S m x = ∫ u in (0 : ℝ)..1, heightKernel S y u x
      * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
          * ((u : ℂ) + (y : ℂ) * Complex.I))) := by
  obtain ⟨a, b, aT, bT, hA, hB, hAT, hBT, hbI, haI, hbtI, hatI⟩ :=
    ExpansionFromFunctionalEquations S x
  have hcoeff : aCoeff S m x = a m := by
    rw [haI m 1 (by norm_num : (0 : ℝ) < 1)]
    simp only [aCoeff, aKernel, heightKernel, Complex.ofReal_one, one_mul]
  rw [hcoeff]
  exact haI m y hy

/-- **The coefficient formula at any height `y > 0`, `b`-version.** -/
lemma bCoeff_eq_heightBKernel {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (x : E n) {y : ℝ} (hy : 0 < y) :
    bCoeff S m x = (2 * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ))⁻¹ *
      ∫ u in (0 : ℝ)..1, heightBKernel S y u x
        * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
            * ((u : ℂ) + (y : ℂ) * Complex.I))) := by
  obtain ⟨a, b, aT, bT, hA, hB, hAT, hBT, hbI, haI, hbtI, hatI⟩ :=
    ExpansionFromFunctionalEquations S x
  have hcoeff : bCoeff S m x = b m := by
    rw [hbI m 1 (by norm_num : (0 : ℝ) < 1)]
    simp only [bCoeff, bKernel, heightBKernel, Complex.ofReal_one, one_mul]
  rw [hcoeff]
  exact hbI m y hy

/-- **The coefficient formula at any height `y > 0`, `ã`-version.** -/
lemma aTildeCoeff_eq_heightKernelT {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (x : E n) {y : ℝ} (hy : 0 < y) :
    aTildeCoeff S m x = ∫ u in (0 : ℝ)..1, heightKernelT S y u x
      * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
          * ((u : ℂ) + (y : ℂ) * Complex.I))) := by
  obtain ⟨a, b, aT, bT, hA, hB, hAT, hBT, hbI, haI, hbtI, hatI⟩ :=
    ExpansionFromFunctionalEquations S x
  have hcoeff : aTildeCoeff S m x = aT m := by
    rw [hatI m 1 (by norm_num : (0 : ℝ) < 1)]
    simp only [aTildeCoeff, heightKernelT, Complex.ofReal_one, one_mul]
  rw [hcoeff]
  exact hatI m y hy

/-- **The coefficient formula at any height `y > 0`, `b̃`-version.** -/
lemma bTildeCoeff_eq_heightBKernelT {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (x : E n) {y : ℝ} (hy : 0 < y) :
    bTildeCoeff S m x = (2 * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ))⁻¹ *
      ∫ u in (0 : ℝ)..1, heightBKernelT S y u x
        * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
            * ((u : ℂ) + (y : ℂ) * Complex.I))) := by
  obtain ⟨a, b, aT, bT, hA, hB, hAT, hBT, hbI, haI, hbtI, hatI⟩ :=
    ExpansionFromFunctionalEquations S x
  have hcoeff : bTildeCoeff S m x = bT m := by
    rw [hbtI m 1 (by norm_num : (0 : ℝ) < 1)]
    simp only [bTildeCoeff, heightBKernelT, Complex.ofReal_one, one_mul]
  rw [hcoeff]
  exact hbtI m y hy

/-! ### The pointwise Dirichlet expansion with the explicit coefficients -/

/-- The Dirichlet expansion of `F(·,x)` with the coefficients `aCoeff`, `bCoeff` of the
contour-integral definition. -/
lemma expansion_F_pointwise {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (τ : ℂ) (hτ : 0 < τ.im) (x : E n) :
    S.F τ x = (∑' m : Set.Ici (1 : ℕ), aCoeff S m x * dirichletTerm m.1 τ)
      + (2 * (Real.pi : ℂ) * Complex.I * τ)
        * ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * bCoeff S m x * dirichletTerm m.1 τ := by
  obtain ⟨a, b, aT, bT, hA, hB, hAT, hBT, hbI, haI, hbtI, hatI⟩ :=
    ExpansionFromFunctionalEquations S x
  have ha : ∀ m, a m = aCoeff S m x := fun m => by
    rw [haI m 1 (by norm_num : (0 : ℝ) < 1)]
    simp only [aCoeff, aKernel, heightKernel, Complex.ofReal_one, one_mul]
  have hb : ∀ m, b m = bCoeff S m x := fun m => by
    rw [hbI m 1 (by norm_num : (0 : ℝ) < 1)]
    simp only [bCoeff, bKernel, heightBKernel, Complex.ofReal_one, one_mul]
  have hA' : HasSum (fun m : Set.Ici (1 : ℕ) => aCoeff S m x * dirichletTerm m.1 τ)
      (S.F τ x - τ * (S.F (τ + 1) x - S.F τ x)) :=
    (hA τ hτ).congr_fun (fun m => by rw [ha m])
  have hB' : HasSum (fun m : Set.Ici (1 : ℕ) =>
      (rate m.1 : ℂ) * bCoeff S m x * dirichletTerm m.1 τ)
      ((S.F (τ + 1) x - S.F τ x) / (2 * (Real.pi : ℂ) * Complex.I)) :=
    (hB τ hτ).congr_fun (fun m => by rw [hb m])
  set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * τ with hc
  have hB'' : HasSum (fun m : Set.Ici (1 : ℕ) =>
      c * ((rate m.1 : ℂ) * bCoeff S m x * dirichletTerm m.1 τ))
      (τ * (S.F (τ + 1) x - S.F τ x)) := by
    have h1 := (hB'.mul_left (2 * (Real.pi : ℂ) * Complex.I)).mul_left τ
    have hv : τ * ((2 * (Real.pi : ℂ) * Complex.I)
        * ((S.F (τ + 1) x - S.F τ x) / (2 * (Real.pi : ℂ) * Complex.I)))
        = τ * (S.F (τ + 1) x - S.F τ x) := by
      field_simp
    rw [hv] at h1
    refine h1.congr_fun (fun m => ?_)
    rw [hc]
    ring
  have hsum : HasSum (fun m : Set.Ici (1 : ℕ) =>
      (aCoeff S m x * dirichletTerm m.1 τ
        + c * ((rate m.1 : ℂ) * bCoeff S m x * dirichletTerm m.1 τ)))
      (S.F τ x) := by
    have h := hA'.add hB''
    have hv : (S.F τ x - τ * (S.F (τ + 1) x - S.F τ x)) + τ * (S.F (τ + 1) x - S.F τ x)
        = S.F τ x := by ring
    rw [hv] at h
    exact h
  rw [hc]
  rw [← hsum.tsum_eq]
  rw [Summable.tsum_add hA'.summable hB''.summable, tsum_mul_left]

/-- The Dirichlet expansion of `F̃(·,x)` with the coefficients `aTildeCoeff`, `bTildeCoeff`. -/
lemma expansion_Ftilde_pointwise {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (τ : ℂ) (hτ : 0 < τ.im) (x : E n) :
    S.Ftilde τ x = (∑' m : Set.Ici (1 : ℕ), aTildeCoeff S m x * dirichletTerm m.1 τ)
      + (2 * (Real.pi : ℂ) * Complex.I * τ)
        * ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * bTildeCoeff S m x * dirichletTerm m.1 τ := by
  obtain ⟨a, b, aT, bT, hA, hB, hAT, hBT, hbI, haI, hbtI, hatI⟩ :=
    ExpansionFromFunctionalEquations S x
  have ha : ∀ m, aT m = aTildeCoeff S m x := fun m => by
    rw [hatI m 1 (by norm_num : (0 : ℝ) < 1)]
    simp only [aTildeCoeff, heightKernelT, Complex.ofReal_one, one_mul]
  have hb : ∀ m, bT m = bTildeCoeff S m x := fun m => by
    rw [hbtI m 1 (by norm_num : (0 : ℝ) < 1)]
    simp only [bTildeCoeff, heightBKernelT, Complex.ofReal_one, one_mul]
  have hA' : HasSum (fun m : Set.Ici (1 : ℕ) => aTildeCoeff S m x * dirichletTerm m.1 τ)
      (S.Ftilde τ x - τ * (S.Ftilde (τ + 1) x - S.Ftilde τ x)) :=
    (hAT τ hτ).congr_fun (fun m => by rw [ha m])
  have hB' : HasSum (fun m : Set.Ici (1 : ℕ) =>
      (rate m.1 : ℂ) * bTildeCoeff S m x * dirichletTerm m.1 τ)
      ((S.Ftilde (τ + 1) x - S.Ftilde τ x) / (2 * (Real.pi : ℂ) * Complex.I)) :=
    (hBT τ hτ).congr_fun (fun m => by rw [hb m])
  set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * τ with hc
  have hB'' : HasSum (fun m : Set.Ici (1 : ℕ) =>
      c * ((rate m.1 : ℂ) * bTildeCoeff S m x * dirichletTerm m.1 τ))
      (τ * (S.Ftilde (τ + 1) x - S.Ftilde τ x)) := by
    have h1 := (hB'.mul_left (2 * (Real.pi : ℂ) * Complex.I)).mul_left τ
    have hv : τ * ((2 * (Real.pi : ℂ) * Complex.I)
        * ((S.Ftilde (τ + 1) x - S.Ftilde τ x) / (2 * (Real.pi : ℂ) * Complex.I)))
        = τ * (S.Ftilde (τ + 1) x - S.Ftilde τ x) := by
      field_simp
    rw [hv] at h1
    refine h1.congr_fun (fun m => ?_)
    rw [hc]
    ring
  have hsum : HasSum (fun m : Set.Ici (1 : ℕ) =>
      (aTildeCoeff S m x * dirichletTerm m.1 τ
        + c * ((rate m.1 : ℂ) * bTildeCoeff S m x * dirichletTerm m.1 τ)))
      (S.Ftilde τ x) := by
    have h := hA'.add hB''
    have hv : (S.Ftilde τ x - τ * (S.Ftilde (τ + 1) x - S.Ftilde τ x))
        + τ * (S.Ftilde (τ + 1) x - S.Ftilde τ x) = S.Ftilde τ x := by ring
    rw [hv] at h
    exact h
  rw [hc]
  rw [← hsum.tsum_eq]
  rw [Summable.tsum_add hA'.summable hB''.summable, tsum_mul_left]

/-! ### Radiality, evenness and the profile derivatives of the kernels -/

/-- The norm of a real number in `ℂ`. -/
lemma norm_ofReal_complex' (r : ℝ) : ‖(r : ℂ)‖ = |r| := RCLike.norm_ofReal r

/-- The kernel `heightKernel S y t` is radial in `x`. -/
lemma radial_heightKernel {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (y t : ℝ) :
    Radial (heightKernel S y t) := by
  intro e e' h
  simp only [heightKernel]
  rw [S.radial_F _ e e' h, S.radial_F _ e e' h]

/-- The `r`-profile of the kernel is even. -/
lemma even_heightKernel_profile {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (y t : ℝ) : Function.Even (fun r : ℝ => heightKernel S y t (realIncl (n := n) r)) := by
  intro r
  refine radial_heightKernel S y t _ _ ?_
  rw [Work.Sampling.realIncl_norm, Work.Sampling.realIncl_norm, abs_neg]

/-- For an even function, the norm of the `j`-th derivative at `r` agrees with that at `-r`. -/
lemma norm_iteratedDeriv_even_eq {g : ℝ → ℂ} (hg : Function.Even g) (j : ℕ) (r : ℝ) :
    ‖iteratedDeriv j g r‖ = ‖iteratedDeriv j g (-r)‖ := by
  have h1 : g =ᶠ[𝓝 r] (fun s : ℝ => g (-s)) := by
    filter_upwards with s
    exact (hg s).symm
  have h2 : iteratedDeriv j g r = iteratedDeriv j (fun s : ℝ => g (-s)) r :=
    (h1.iteratedDeriv j).eq_of_nhds
  rw [h2, iteratedDeriv_comp_neg]
  simp

/-- The `j`-th derivative of a linear combination, in the form used for the kernel profiles. -/
lemma iteratedDeriv_fun_lin {c d : ℂ} {f g : ℝ → ℂ} {j : ℕ} (x : ℝ)
    (hf : ContDiffAt ℝ (j : ℕ∞) f x) (hg : ContDiffAt ℝ (j : ℕ∞) g x) :
    iteratedDeriv j (fun s : ℝ => c * f s - d * g s) x
      = c * iteratedDeriv j f x - d * iteratedDeriv j g x := by
  have h1 : ContDiffAt ℝ (j : ℕ∞) (fun s : ℝ => c * f s) x :=
    (contDiffAt_const (x := x) (c := c)).mul hf
  have h2 : ContDiffAt ℝ (j : ℕ∞) (fun s : ℝ => d * g s) x :=
    (contDiffAt_const (x := x) (c := d)).mul hg
  rw [show (fun s : ℝ => c * f s - d * g s)
      = ((fun s : ℝ => c * f s) - fun s : ℝ => d * g s) from rfl,
    iteratedDeriv_sub h1 h2, iteratedDeriv_const_mul c hf, iteratedDeriv_const_mul d hg]

/-- The profile `s ↦ F(τ, realIncl s)` is smooth. -/
lemma contDiff_profile {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (τ : ℂ) :
    ContDiff ℝ ⊤ (fun s : ℝ => S.F τ (realIncl (n := n) s)) := by
  have h1 : ContDiff ℝ ⊤ (realIncl (n := n)) := by
    have h2 : (realIncl (n := n)) = fun s : ℝ => s • realIncl (n := n) 1 :=
      funext (fun s => Work.Sampling.realIncl_eq_smul (n := n) s)
    rw [h2]
    exact contDiff_id.smul contDiff_const
  exact (S.smooth_F τ).comp h1

/-- The profile `s ↦ F̃(τ, realIncl s)` is smooth. -/
lemma contDiff_profileT {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (τ : ℂ) :
    ContDiff ℝ ⊤ (fun s : ℝ => S.Ftilde τ (realIncl (n := n) s)) := by
  have h1 : ContDiff ℝ ⊤ (realIncl (n := n)) := by
    have h2 : (realIncl (n := n)) = fun s : ℝ => s • realIncl (n := n) 1 :=
      funext (fun s => Work.Sampling.realIncl_eq_smul (n := n) s)
    rw [h2]
    exact contDiff_id.smul contDiff_const
  exact (S.smooth_Ftilde τ).comp h1

/-- Along the nonnegative axis the iterated derivative of a profile is the radial derivative. -/
lemma iteratedDeriv_profile_eq_radialDeriv {n : ℕ} [NeZero n] {G : E n → ℂ}
    (j : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    iteratedDeriv j (fun s : ℝ => G (realIncl (n := n) s)) r = radialDeriv j G (realIncl r) := by
  rw [radialDeriv, Work.Sampling.realIncl_norm, abs_of_nonneg hr]

/-- The `r`-profile of a radial function is even. -/
lemma even_profile_of_radial {n : ℕ} [NeZero n] {G : E n → ℂ} (hG : Radial G) :
    Function.Even (fun r : ℝ => G (realIncl (n := n) r)) := by
  intro r
  refine hG _ _ ?_
  rw [Work.Sampling.realIncl_norm, Work.Sampling.realIncl_norm, abs_neg]

/-- **Bound for the profile derivatives of a linear combination of radial functions.**  If two
radial functions have radial-derivative bounds `B` of order `j`, then the `j`-th derivative of the
profile of any combination `c₁ G + c₂ H` with `‖c₁‖, ‖c₂‖ ≤ 3` is bounded by `6 B`, also at
negative arguments. -/
lemma bound_comb_profile {n : ℕ} [NeZero n] {G H : E n → ℂ} (hG : Radial G) (hH : Radial H)
    {j : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hcdG : ∀ r : ℝ, ContDiffAt ℝ (j : ℕ∞) (fun s : ℝ => G (realIncl (n := n) s)) r)
    (hcdH : ∀ r : ℝ, ContDiffAt ℝ (j : ℕ∞) (fun s : ℝ => H (realIncl (n := n) s)) r)
    (hGB : ∀ x : E n, ‖radialDeriv j G x‖ ≤ B) (hHB : ∀ x : E n, ‖radialDeriv j H x‖ ≤ B)
    {c1 c2 : ℂ} (hc1 : ‖c1‖ ≤ 3) (hc2 : ‖c2‖ ≤ 3) :
    ∀ r : ℝ, ‖iteratedDeriv j
        (fun s : ℝ => c1 * G (realIncl (n := n) s) + c2 * H (realIncl (n := n) s)) r‖ ≤ 6 * B := by
  have hevenG := even_profile_of_radial hG
  have hevenH := even_profile_of_radial hH
  have heven : Function.Even
      (fun s : ℝ => c1 * G (realIncl (n := n) s) + c2 * H (realIncl (n := n) s)) := by
    intro r
    simp only [hevenG r, hevenH r]
  have hmain : ∀ r : ℝ, 0 ≤ r → ‖iteratedDeriv j
      (fun s : ℝ => c1 * G (realIncl (n := n) s) + c2 * H (realIncl (n := n) s)) r‖ ≤ 6 * B := by
    intro r hr
    have hfun : (fun s : ℝ => c1 * G (realIncl (n := n) s) + c2 * H (realIncl (n := n) s))
        = (fun s : ℝ => c1 * G (realIncl (n := n) s) - (-c2) * H (realIncl (n := n) s)) := by
      funext s; ring
    rw [hfun, iteratedDeriv_fun_lin (c := c1) (d := -c2) (j := j) r (hcdG r) (hcdH r),
      iteratedDeriv_profile_eq_radialDeriv (n := n) (G := G) j hr,
      iteratedDeriv_profile_eq_radialDeriv (n := n) (G := H) j hr]
    calc ‖c1 * radialDeriv j G (realIncl r) - (-c2) * radialDeriv j H (realIncl r)‖
        ≤ ‖c1 * radialDeriv j G (realIncl r)‖ + ‖(-c2) * radialDeriv j H (realIncl r)‖ :=
          norm_sub_le _ _
      _ = ‖c1‖ * ‖radialDeriv j G (realIncl r)‖ + ‖c2‖ * ‖radialDeriv j H (realIncl r)‖ := by
          rw [norm_mul, norm_mul, norm_neg]
      _ ≤ 3 * B + 3 * B := by
          refine add_le_add (mul_le_mul hc1 (hGB (realIncl r)) (norm_nonneg _) (by norm_num))
            (mul_le_mul hc2 (hHB (realIncl r)) (norm_nonneg _) (by norm_num))
      _ ≤ 6 * B := by linarith
  intro r
  by_cases hr : 0 ≤ r
  · exact hmain r hr
  · rw [norm_iteratedDeriv_even_eq heven j r]
    exact hmain (-r) (by linarith [not_le.mp hr])

/-- The `j`-th radial derivative of `F τ` is bounded by `B := α y^{-β} + γ 3^δ` at height
`y ≤ 1`. -/
lemma radialDeriv_bound_at_height {n : ℕ} [NeZero n] {G : E n → ℂ} {α β γ δ : ℝ} {j : ℕ} (hγ : 0 ≤ γ)
    (hδ : 0 ≤ δ) {τ : ℂ} {y : ℝ} (hτim : τ.im = y) (hy : 0 < y) (hy1 : y ≤ 1) (hτnorm : ‖τ‖ ≤ 3)
    (hgr : ∀ (x : E n), ‖radialDeriv j G x‖ ≤ α * τ.im ^ (-β) + γ * ‖τ‖ ^ δ) :
    ∀ x : E n, ‖radialDeriv j G x‖ ≤ α * y ^ (-β) + γ * 3 ^ δ := by
  intro x
  have hrpow : ‖τ‖ ^ δ ≤ 3 ^ δ :=
    Real.rpow_le_rpow (norm_nonneg _) hτnorm hδ
  calc ‖radialDeriv j G x‖ ≤ α * τ.im ^ (-β) + γ * ‖τ‖ ^ δ := hgr x
    _ = α * y ^ (-β) + γ * ‖τ‖ ^ δ := by rw [hτim]
    _ ≤ α * y ^ (-β) + γ * 3 ^ δ :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hrpow hγ)

/-- `τ = t + i y` with `t ∈ [0,1]`, `y ≤ 1` has norm at most `2`. -/
lemma norm_tau_le {y t : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖(t : ℂ) + (y : ℂ) * Complex.I‖ ≤ 2 := by
  have htabs : |t| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
  calc ‖(t : ℂ) + (y : ℂ) * Complex.I‖ ≤ ‖(t : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |t| + y := by
          rw [norm_ofReal_complex', norm_mul, Complex.norm_I, mul_one, norm_ofReal_complex',
            abs_of_pos hy]
    _ ≤ 1 + 1 := add_le_add htabs hy1
    _ = 2 := by norm_num

/-- **Bound on the profile derivatives of the `a`-kernel.** -/
lemma bound_heightKernel_profile {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    {α β γ δ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ)
    (j : ℕ) (hgr : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      ‖radialDeriv j (S.F τ) x‖ ≤ α * τ.im ^ (-β) + γ * ‖τ‖ ^ δ)
    {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ r : ℝ, ‖iteratedDeriv j (fun s : ℝ => heightKernel S y t (realIncl (n := n) s)) r‖
      ≤ 6 * (α * y ^ (-β) + γ * 3 ^ δ) := by
  set τ : ℂ := (t : ℂ) + (y : ℂ) * Complex.I with hτ
  have hτim : τ.im = y := by simp [hτ]
  have hτnorm2 : ‖τ‖ ≤ 2 := by rw [hτ]; exact norm_tau_le hy hy1 ht
  have hτnorm : ‖τ‖ ≤ 3 := le_trans hτnorm2 (by norm_num)
  have him1 : (τ + 1).im = y := by simp [hτim]
  have hB0 : 0 ≤ α * y ^ (-β) + γ * 3 ^ δ :=
    add_nonneg (mul_nonneg hα (Real.rpow_nonneg hy.le _))
      (mul_nonneg hγ (Real.rpow_nonneg (by norm_num) _))
  have hfun : (fun s : ℝ => heightKernel S y t (realIncl (n := n) s))
      = (fun s : ℝ => (1 + τ) * S.F τ (realIncl s) + (-τ) * S.F (τ + 1) (realIncl s)) := by
    funext s
    simp only [heightKernel, hτ]
    ring
  rw [hfun]
  refine bound_comb_profile (G := S.F τ) (H := S.F (τ + 1)) (S.radial_F τ) (S.radial_F (τ + 1))
    hB0 (fun r => ((contDiff_profile S τ).contDiffAt).of_le le_top)
    (fun r => ((contDiff_profile S (τ + 1)).contDiffAt).of_le le_top)
    (radialDeriv_bound_at_height hγ hδ hτim hy hy1 hτnorm
      (fun x => hgr τ x (by rw [hτim]; exact hy)))
    (radialDeriv_bound_at_height hγ hδ (by simp [hτim]) hy hy1
      (by calc ‖τ + 1‖ ≤ ‖τ‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
            _ = ‖τ‖ + 1 := by rw [norm_one]
            _ ≤ 3 := by linarith)
      (fun x => hgr (τ + 1) x (by rw [him1]; exact hy)))
    (by calc ‖(1 : ℂ) + τ‖ ≤ ‖(1 : ℂ)‖ + ‖τ‖ := norm_add_le _ _
          _ = 1 + ‖τ‖ := by rw [norm_one]
          _ ≤ 3 := by linarith)
    (by rw [norm_neg]; exact le_trans hτnorm2 (by norm_num))

/-- **Bound on the profile derivatives of the `b`-kernel.** -/
lemma bound_heightBKernel_profile {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    {α β γ δ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ)
    (j : ℕ) (hgr : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      ‖radialDeriv j (S.F τ) x‖ ≤ α * τ.im ^ (-β) + γ * ‖τ‖ ^ δ)
    {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ r : ℝ, ‖iteratedDeriv j (fun s : ℝ => heightBKernel S y t (realIncl (n := n) s)) r‖
      ≤ 6 * (α * y ^ (-β) + γ * 3 ^ δ) := by
  set τ : ℂ := (t : ℂ) + (y : ℂ) * Complex.I with hτ
  have hτim : τ.im = y := by simp [hτ]
  have hτnorm2 : ‖τ‖ ≤ 2 := by rw [hτ]; exact norm_tau_le hy hy1 ht
  have hτnorm : ‖τ‖ ≤ 3 := le_trans hτnorm2 (by norm_num)
  have him1 : (τ + 1).im = y := by simp [hτim]
  have hB0 : 0 ≤ α * y ^ (-β) + γ * 3 ^ δ :=
    add_nonneg (mul_nonneg hα (Real.rpow_nonneg hy.le _))
      (mul_nonneg hγ (Real.rpow_nonneg (by norm_num) _))
  have hfun : (fun s : ℝ => heightBKernel S y t (realIncl (n := n) s))
      = (fun s : ℝ => (1 : ℂ) * S.F (τ + 1) (realIncl s) + (-1 : ℂ) * S.F τ (realIncl s)) := by
    funext s
    simp only [heightBKernel, hτ]
    ring
  rw [hfun]
  refine bound_comb_profile (G := S.F (τ + 1)) (H := S.F τ) (S.radial_F (τ + 1)) (S.radial_F τ)
    hB0 (fun r => ((contDiff_profile S (τ + 1)).contDiffAt).of_le le_top)
    (fun r => ((contDiff_profile S τ).contDiffAt).of_le le_top)
    (radialDeriv_bound_at_height hγ hδ (by simp [hτim]) hy hy1
      (by calc ‖τ + 1‖ ≤ ‖τ‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
            _ = ‖τ‖ + 1 := by rw [norm_one]
            _ ≤ 3 := by linarith)
      (fun x => hgr (τ + 1) x (by rw [him1]; exact hy)))
    (radialDeriv_bound_at_height hγ hδ hτim hy hy1 hτnorm
      (fun x => hgr τ x (by rw [hτim]; exact hy)))
    (by rw [norm_one]; norm_num) (by rw [norm_neg, norm_one]; norm_num)

/-- The kernel `heightKernelT S y t` is radial in `x`. -/
lemma radial_heightKernelT {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (y t : ℝ) :
    Radial (heightKernelT S y t) := by
  intro e e' h
  simp only [heightKernelT]
  rw [S.radial_Ftilde _ e e' h, S.radial_Ftilde _ e e' h]

/-- The kernel `heightBKernelT S y t` is radial in `x`. -/
lemma radial_heightBKernelT {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (y t : ℝ) :
    Radial (heightBKernelT S y t) := by
  intro e e' h
  simp only [heightBKernelT]
  rw [S.radial_Ftilde _ e e' h, S.radial_Ftilde _ e e' h]

/-- The profile `s ↦ F̃(τ, realIncl s)` has the same smoothness. -/
lemma contDiff_profileT' {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (τ : ℂ) :
    ContDiff ℝ ⊤ (fun s : ℝ => S.Ftilde τ (realIncl (n := n) s)) := contDiff_profileT S τ

/-- **Bound on the profile derivatives of the `a`-kernel of `F̃`.** -/
lemma bound_heightKernelT_profile {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    {α β γ δ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ)
    (j : ℕ) (hgr : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      ‖radialDeriv j (S.Ftilde τ) x‖ ≤ α * τ.im ^ (-β) + γ * ‖τ‖ ^ δ)
    {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ r : ℝ, ‖iteratedDeriv j (fun s : ℝ => heightKernelT S y t (realIncl (n := n) s)) r‖
      ≤ 6 * (α * y ^ (-β) + γ * 3 ^ δ) := by
  set τ : ℂ := (t : ℂ) + (y : ℂ) * Complex.I with hτ
  have hτim : τ.im = y := by simp [hτ]
  have hτnorm2 : ‖τ‖ ≤ 2 := by rw [hτ]; exact norm_tau_le hy hy1 ht
  have hτnorm : ‖τ‖ ≤ 3 := le_trans hτnorm2 (by norm_num)
  have him1 : (τ + 1).im = y := by simp [hτim]
  have hB0 : 0 ≤ α * y ^ (-β) + γ * 3 ^ δ :=
    add_nonneg (mul_nonneg hα (Real.rpow_nonneg hy.le _))
      (mul_nonneg hγ (Real.rpow_nonneg (by norm_num) _))
  have hfun : (fun s : ℝ => heightKernelT S y t (realIncl (n := n) s))
      = (fun s : ℝ => (1 + τ) * S.Ftilde τ (realIncl s) + (-τ) * S.Ftilde (τ + 1) (realIncl s)) := by
    funext s
    simp only [heightKernelT, hτ]
    ring
  rw [hfun]
  refine bound_comb_profile (G := S.Ftilde τ) (H := S.Ftilde (τ + 1)) (S.radial_Ftilde τ)
    (S.radial_Ftilde (τ + 1))
    hB0 (fun r => ((contDiff_profileT S τ).contDiffAt).of_le le_top)
    (fun r => ((contDiff_profileT S (τ + 1)).contDiffAt).of_le le_top)
    (radialDeriv_bound_at_height hγ hδ hτim hy hy1 hτnorm
      (fun x => hgr τ x (by rw [hτim]; exact hy)))
    (radialDeriv_bound_at_height hγ hδ (by simp [hτim]) hy hy1
      (by calc ‖τ + 1‖ ≤ ‖τ‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
            _ = ‖τ‖ + 1 := by rw [norm_one]
            _ ≤ 3 := by linarith)
      (fun x => hgr (τ + 1) x (by rw [him1]; exact hy)))
    (by calc ‖(1 : ℂ) + τ‖ ≤ ‖(1 : ℂ)‖ + ‖τ‖ := norm_add_le _ _
          _ = 1 + ‖τ‖ := by rw [norm_one]
          _ ≤ 3 := by linarith)
    (by rw [norm_neg]; exact le_trans hτnorm2 (by norm_num))

/-- **Bound on the profile derivatives of the `b`-kernel of `F̃`.** -/
lemma bound_heightBKernelT_profile {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    {α β γ δ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ)
    (j : ℕ) (hgr : ∀ (τ : ℂ) (x : E n), 0 < τ.im →
      ‖radialDeriv j (S.Ftilde τ) x‖ ≤ α * τ.im ^ (-β) + γ * ‖τ‖ ^ δ)
    {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ r : ℝ, ‖iteratedDeriv j (fun s : ℝ => heightBKernelT S y t (realIncl (n := n) s)) r‖
      ≤ 6 * (α * y ^ (-β) + γ * 3 ^ δ) := by
  set τ : ℂ := (t : ℂ) + (y : ℂ) * Complex.I with hτ
  have hτim : τ.im = y := by simp [hτ]
  have hτnorm2 : ‖τ‖ ≤ 2 := by rw [hτ]; exact norm_tau_le hy hy1 ht
  have hτnorm : ‖τ‖ ≤ 3 := le_trans hτnorm2 (by norm_num)
  have him1 : (τ + 1).im = y := by simp [hτim]
  have hB0 : 0 ≤ α * y ^ (-β) + γ * 3 ^ δ :=
    add_nonneg (mul_nonneg hα (Real.rpow_nonneg hy.le _))
      (mul_nonneg hγ (Real.rpow_nonneg (by norm_num) _))
  have hfun : (fun s : ℝ => heightBKernelT S y t (realIncl (n := n) s))
      = (fun s : ℝ => (1 : ℂ) * S.Ftilde (τ + 1) (realIncl s) + (-1 : ℂ) * S.Ftilde τ (realIncl s)) := by
    funext s
    simp only [heightBKernelT, hτ]
    ring
  rw [hfun]
  refine bound_comb_profile (G := S.Ftilde (τ + 1)) (H := S.Ftilde τ) (S.radial_Ftilde (τ + 1))
    (S.radial_Ftilde τ)
    hB0 (fun r => ((contDiff_profileT S (τ + 1)).contDiffAt).of_le le_top)
    (fun r => ((contDiff_profileT S τ).contDiffAt).of_le le_top)
    (radialDeriv_bound_at_height hγ hδ (by simp [hτim]) hy hy1
      (by calc ‖τ + 1‖ ≤ ‖τ‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
            _ = ‖τ‖ + 1 := by rw [norm_one]
            _ ≤ 3 := by linarith)
      (fun x => hgr (τ + 1) x (by rw [him1]; exact hy)))
    (radialDeriv_bound_at_height hγ hδ hτim hy hy1 hτnorm
      (fun x => hgr τ x (by rw [hτim]; exact hy)))
    (by rw [norm_one]; norm_num) (by rw [norm_neg, norm_one]; norm_num)

/-! ### Growth data and the coefficient families at the height `1/(m+1)` -/

/-- The height `y = 1/(m+1)` at which the `m`-th coefficient is read off. -/
def coeffHeight (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)

lemma coeffHeight_pos (m : ℕ) : 0 < coeffHeight m := by
  rw [coeffHeight]; positivity

lemma coeffHeight_le_one (m : ℕ) : coeffHeight m ≤ 1 := by
  rw [coeffHeight, div_le_one (by positivity)]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

lemma coeffHeight_rpow_neg (m : ℕ) (B : ℝ) : (coeffHeight m) ^ (-B) = ((m : ℝ) + 1) ^ B := by
  have hx : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  rw [coeffHeight, one_div, Real.inv_rpow hx, ← Real.rpow_neg hx, neg_neg]

lemma exp_coeffHeight_le (m : ℕ) :
    Real.exp (2 * Real.pi * (m : ℝ) * coeffHeight m) ≤ Real.exp (2 * Real.pi) := by
  refine Real.exp_le_exp.mpr ?_
  have hy1 : (m : ℝ) * (1 / ((m : ℝ) + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  calc 2 * Real.pi * (m : ℝ) * (1 / ((m : ℝ) + 1))
      = 2 * Real.pi * ((m : ℝ) * (1 / ((m : ℝ) + 1))) := by ring
    _ ≤ 2 * Real.pi * 1 := mul_le_mul_of_nonneg_left hy1 (by positivity)
    _ = 2 * Real.pi := by ring

/-- The growth data `(α, β, γ, δ)` for the `j`-th radial derivative of `F`, from hypothesis (iii). -/
lemma growthExists {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (j : ℕ) :
    ∃ p : ℝ × ℝ × ℝ × ℝ, 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2.1 ∧ 0 ≤ p.2.2.2 ∧
      ∀ (τ : ℂ) (x : E n), 0 < τ.im → ‖radialDeriv j (S.F τ) x‖
        ≤ p.1 * τ.im ^ (-p.2.1) + p.2.2.1 * ‖τ‖ ^ p.2.2.2 := by
  obtain ⟨α, β, γ, δ, h1, h2, h3, h4, h5⟩ := S.growth_F 0 j
  exact ⟨(α, β, γ, δ), h1, h2, h3, h4, fun τ x hτ => by simpa using h5 τ x hτ⟩

def growthData {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (j : ℕ) :
    ℝ × ℝ × ℝ × ℝ :=
  Classical.choose (growthExists S j)

lemma growthData_spec {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (j : ℕ) :
    0 ≤ (growthData S j).1 ∧ 0 ≤ (growthData S j).2.1 ∧ 0 ≤ (growthData S j).2.2.1
      ∧ 0 ≤ (growthData S j).2.2.2 ∧ ∀ (τ : ℂ) (x : E n), 0 < τ.im →
        ‖radialDeriv j (S.F τ) x‖
          ≤ (growthData S j).1 * τ.im ^ (-(growthData S j).2.1)
            + (growthData S j).2.2.1 * ‖τ‖ ^ (growthData S j).2.2.2 :=
  Classical.choose_spec (growthExists S j)

/-- The growth data for `F̃`. -/
lemma growthExistsT {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (j : ℕ) :
    ∃ p : ℝ × ℝ × ℝ × ℝ, 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2.1 ∧ 0 ≤ p.2.2.2 ∧
      ∀ (τ : ℂ) (x : E n), 0 < τ.im → ‖radialDeriv j (S.Ftilde τ) x‖
        ≤ p.1 * τ.im ^ (-p.2.1) + p.2.2.1 * ‖τ‖ ^ p.2.2.2 := by
  obtain ⟨α, β, γ, δ, h1, h2, h3, h4, h5⟩ := S.growth_Ftilde 0 j
  exact ⟨(α, β, γ, δ), h1, h2, h3, h4, fun τ x hτ => by simpa using h5 τ x hτ⟩

def growthDataT {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (j : ℕ) :
    ℝ × ℝ × ℝ × ℝ :=
  Classical.choose (growthExistsT S j)

lemma growthDataT_spec {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (j : ℕ) :
    0 ≤ (growthDataT S j).1 ∧ 0 ≤ (growthDataT S j).2.1 ∧ 0 ≤ (growthDataT S j).2.2.1
      ∧ 0 ≤ (growthDataT S j).2.2.2 ∧ ∀ (τ : ℂ) (x : E n), 0 < τ.im →
        ‖radialDeriv j (S.Ftilde τ) x‖
          ≤ (growthDataT S j).1 * τ.im ^ (-(growthDataT S j).2.1)
            + (growthDataT S j).2.2.1 * ‖τ‖ ^ (growthDataT S j).2.2.2 :=
  Classical.choose_spec (growthExistsT S j)

/-- The explicit bound `6 e^{2π} (α_j (m+1)^{β_j} + γ_j 3^{δ_j})` for the `j`-th derivative of a
kernel profile at height `1/(m+1)`. -/
def Cker (G : ℕ → ℝ × ℝ × ℝ × ℝ) (j m : ℕ) : ℝ :=
  6 * Real.exp (2 * Real.pi) *
    ((G j).1 * ((m : ℝ) + 1) ^ ((G j).2.1) + (G j).2.2.1 * 3 ^ ((G j).2.2.2))

lemma Cker_nonneg (G : ℕ → ℝ × ℝ × ℝ × ℝ) (hG : ∀ j, 0 ≤ (G j).1 ∧ 0 ≤ (G j).2.1
    ∧ 0 ≤ (G j).2.2.1 ∧ 0 ≤ (G j).2.2.2) (j m : ℕ) : 0 ≤ Cker G j m := by
  have h1 := hG j
  rw [Cker]
  exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
    (add_nonneg (mul_nonneg h1.1 (Real.rpow_nonneg (by positivity) _))
      (mul_nonneg h1.2.2.1 (Real.rpow_nonneg (by norm_num) _)))

/-- The weighted `a`-kernel family at height `1/(m+1)`, as a function of `(t, r)`. -/
def aFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (m : Set.Ici (1 : ℕ))
    (t r : ℝ) : ℂ :=
  heightKernel S (coeffHeight m.1) t (realIncl r)
    * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
        * ((t : ℂ) + (coeffHeight m.1 : ℂ) * Complex.I)))

/-- The weighted `b`-kernel family at height `1/(m+1)`. -/
def bFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (m : Set.Ici (1 : ℕ))
    (t r : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ))⁻¹ *
    (heightBKernel S (coeffHeight m.1) t (realIncl r)
      * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
          * ((t : ℂ) + (coeffHeight m.1 : ℂ) * Complex.I))))

/-- The weighted `a`-kernel family of `F̃` at height `1/(m+1)`. -/
def aTFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (m : Set.Ici (1 : ℕ))
    (t r : ℝ) : ℂ :=
  heightKernelT S (coeffHeight m.1) t (realIncl r)
    * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
        * ((t : ℂ) + (coeffHeight m.1 : ℂ) * Complex.I)))

/-- The weighted `b`-kernel family of `F̃` at height `1/(m+1)`. -/
def bTFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (m : Set.Ici (1 : ℕ))
    (t r : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ))⁻¹ *
    (heightBKernelT S (coeffHeight m.1) t (realIncl r)
      * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
          * ((t : ℂ) + (coeffHeight m.1 : ℂ) * Complex.I))))

/-- The exponential weight `e^{-2π i m (t + i y)}` at the height `y = 1/(m+1)`. -/
def coeffWeight (m : Set.Ici (1 : ℕ)) (t : ℝ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
    * ((t : ℂ) + (coeffHeight m.1 : ℂ) * Complex.I)))

/-- The normalising constant `(2π i √(2m))^{-1}` of the `b`-coefficients. -/
def coeffConst (m : Set.Ici (1 : ℕ)) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ))⁻¹

lemma norm_coeffWeight (m : Set.Ici (1 : ℕ)) (t : ℝ) :
    ‖coeffWeight m t‖ = Real.exp (2 * Real.pi * (m.1 : ℝ) * coeffHeight m.1) := by
  have h : coeffWeight m t
      = dirichletTerm m.1 (-((t : ℂ) + (coeffHeight m.1 : ℂ) * Complex.I)) := by
    simp only [coeffWeight, dirichletTerm]
    congr 1
    ring
  rw [h, normDirichletTermAux]
  congr 1
  simp [Complex.neg_im]

lemma norm_coeffConst_le_one (m : Set.Ici (1 : ℕ)) : ‖coeffConst m‖ ≤ 1 := by
  have hm1 : (1 : ℝ) ≤ (m.1 : ℝ) := by exact_mod_cast m.2
  have hrate : 1 ≤ rate m.1 := by
    rw [rate, Real.one_le_sqrt]
    linarith
  have hnorm : ‖(2 * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ))‖
      = 2 * Real.pi * rate m.1 := by
    have h1 : ‖(2 : ℂ)‖ = 2 := by norm_num [Complex.normSq]
    have h2 : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [norm_ofReal_complex', abs_of_pos Real.pi_pos]
    have h3 : ‖(rate m.1 : ℂ)‖ = rate m.1 := by
      have h3' : (0 : ℝ) ≤ rate m.1 := Real.sqrt_nonneg _
      rw [norm_ofReal_complex', abs_of_nonneg h3']
    rw [norm_mul, norm_mul, norm_mul, h1, h2, Complex.norm_I, mul_one, h3]
  rw [coeffConst, norm_inv, hnorm]
  refine inv_le_one_of_one_le₀ ?_
  nlinarith [Real.pi_gt_three, hrate]

/-- The profile of the `a`-kernel is smooth in `r`. -/
lemma contDiff_heightKernel_profile {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (y t : ℝ) : ContDiff ℝ ⊤ (fun s : ℝ => heightKernel S y t (realIncl (n := n) s)) := by
  set τ : ℂ := (t : ℂ) + (y : ℂ) * Complex.I with hτ
  have hcomp : (fun s : ℝ => heightKernel S y t (realIncl (n := n) s))
      = fun s : ℝ => (1 + τ) * S.F τ (realIncl s) + (-τ) * S.F (τ + 1) (realIncl s) := by
    funext s
    simp only [heightKernel, hτ]
    ring
  rw [hcomp]
  exact ((contDiff_const.mul (contDiff_profile S τ)).add
    (contDiff_const.mul (contDiff_profile S (τ + 1))))

/-- The profile of the `b`-kernel is smooth in `r`. -/
lemma contDiff_heightBKernel_profile {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (y t : ℝ) : ContDiff ℝ ⊤ (fun s : ℝ => heightBKernel S y t (realIncl (n := n) s)) := by
  set τ : ℂ := (t : ℂ) + (y : ℂ) * Complex.I with hτ
  have hcomp : (fun s : ℝ => heightBKernel S y t (realIncl (n := n) s))
      = fun s : ℝ => (1 : ℂ) * S.F (τ + 1) (realIncl s) + (-1 : ℂ) * S.F τ (realIncl s) := by
    funext s
    simp only [heightBKernel, hτ]
    ring
  rw [hcomp]
  exact ((contDiff_const.mul (contDiff_profile S (τ + 1))).add
    (contDiff_const.mul (contDiff_profile S τ)))

/-- The profile of the `a`-kernel of `F̃` is smooth in `r`. -/
lemma contDiff_heightKernelT_profile {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (y t : ℝ) : ContDiff ℝ ⊤ (fun s : ℝ => heightKernelT S y t (realIncl (n := n) s)) := by
  set τ : ℂ := (t : ℂ) + (y : ℂ) * Complex.I with hτ
  have hcomp : (fun s : ℝ => heightKernelT S y t (realIncl (n := n) s))
      = fun s : ℝ => (1 + τ) * S.Ftilde τ (realIncl s) + (-τ) * S.Ftilde (τ + 1) (realIncl s) := by
    funext s
    simp only [heightKernelT, hτ]
    ring
  rw [hcomp]
  exact ((contDiff_const.mul (contDiff_profileT S τ)).add
    (contDiff_const.mul (contDiff_profileT S (τ + 1))))

/-- The profile of the `b`-kernel of `F̃` is smooth in `r`. -/
lemma contDiff_heightBKernelT_profile {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (y t : ℝ) : ContDiff ℝ ⊤ (fun s : ℝ => heightBKernelT S y t (realIncl (n := n) s)) := by
  set τ : ℂ := (t : ℂ) + (y : ℂ) * Complex.I with hτ
  have hcomp : (fun s : ℝ => heightBKernelT S y t (realIncl (n := n) s))
      = fun s : ℝ => (1 : ℂ) * S.Ftilde (τ + 1) (realIncl s) + (-1 : ℂ) * S.Ftilde τ (realIncl s) := by
    funext s
    simp only [heightBKernelT, hτ]
    ring
  rw [hcomp]
  exact ((contDiff_const.mul (contDiff_profileT S (τ + 1))).add
    (contDiff_const.mul (contDiff_profileT S τ)))

/-- The four weighted families are smooth in `r`. -/
lemma contDiff_aFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (t : ℝ) : ContDiff ℝ ⊤ (aFamily S m t) :=
  (contDiff_heightKernel_profile S (coeffHeight m.1) t).mul contDiff_const

lemma contDiff_bFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (t : ℝ) : ContDiff ℝ ⊤ (bFamily S m t) :=
  contDiff_const.mul ((contDiff_heightBKernel_profile S (coeffHeight m.1) t).mul contDiff_const)

lemma contDiff_aTFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (t : ℝ) : ContDiff ℝ ⊤ (aTFamily S m t) :=
  (contDiff_heightKernelT_profile S (coeffHeight m.1) t).mul contDiff_const

lemma contDiff_bTFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (t : ℝ) : ContDiff ℝ ⊤ (bTFamily S m t) :=
  contDiff_const.mul ((contDiff_heightBKernelT_profile S (coeffHeight m.1) t).mul contDiff_const)

/-- Continuity in `t` of `t ↦ F(t + iy + c, x)` for `0 < y + Im c`. -/
lemma continuousAt_F_affine {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (x : E n)
    (y : ℝ) (c : ℂ) (hc : 0 < y + c.im) (t : ℝ) :
    ContinuousAt (fun u : ℝ => S.F ((u : ℂ) + (y : ℂ) * Complex.I + c) x) t := by
  have hτim : 0 < (((t : ℂ) + (y : ℂ) * Complex.I + c)).im := by
    simpa [Complex.add_im, Complex.mul_im] using hc
  have hopen : IsOpen {τ : ℂ | 0 < τ.im} := isOpen_lt continuous_const Complex.continuous_im
  have hcont : Tendsto (fun τ : ℂ => S.F τ x) (𝓝 ((t : ℂ) + (y : ℂ) * Complex.I + c))
      (𝓝 (S.F ((t : ℂ) + (y : ℂ) * Complex.I + c) x)) :=
    (S.holomorphic_F x).continuousOn.continuousAt (hopen.mem_nhds hτim)
  have haff : Continuous fun u : ℝ => (u : ℂ) + (y : ℂ) * Complex.I + c := by fun_prop
  have hc2 : Tendsto (fun u : ℝ => (u : ℂ) + (y : ℂ) * Complex.I + c) (𝓝 t)
      (𝓝 ((t : ℂ) + (y : ℂ) * Complex.I + c)) := haff.continuousAt
  have hres : Tendsto (fun u : ℝ => S.F ((u : ℂ) + (y : ℂ) * Complex.I + c) x) (𝓝 t)
      (𝓝 (S.F ((t : ℂ) + (y : ℂ) * Complex.I + c) x)) := by
    simpa [Function.comp_def] using hcont.comp hc2
  exact hres

/-- Continuity in `t` of `t ↦ F̃(t + iy + c, x)` for `0 < y + Im c`. -/
lemma continuousAt_Ftilde_affine {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (x : E n)
    (y : ℝ) (c : ℂ) (hc : 0 < y + c.im) (t : ℝ) :
    ContinuousAt (fun u : ℝ => S.Ftilde ((u : ℂ) + (y : ℂ) * Complex.I + c) x) t := by
  have hτim : 0 < (((t : ℂ) + (y : ℂ) * Complex.I + c)).im := by
    simpa [Complex.add_im, Complex.mul_im] using hc
  have hopen : IsOpen {τ : ℂ | 0 < τ.im} := isOpen_lt continuous_const Complex.continuous_im
  have hcont : Tendsto (fun τ : ℂ => S.Ftilde τ x) (𝓝 ((t : ℂ) + (y : ℂ) * Complex.I + c))
      (𝓝 (S.Ftilde ((t : ℂ) + (y : ℂ) * Complex.I + c) x)) :=
    (S.holomorphic_Ftilde x).continuousOn.continuousAt (hopen.mem_nhds hτim)
  have haff : Continuous fun u : ℝ => (u : ℂ) + (y : ℂ) * Complex.I + c := by fun_prop
  have hc2 : Tendsto (fun u : ℝ => (u : ℂ) + (y : ℂ) * Complex.I + c) (𝓝 t)
      (𝓝 ((t : ℂ) + (y : ℂ) * Complex.I + c)) := haff.continuousAt
  have hres : Tendsto (fun u : ℝ => S.Ftilde ((u : ℂ) + (y : ℂ) * Complex.I + c) x) (𝓝 t)
      (𝓝 (S.Ftilde ((t : ℂ) + (y : ℂ) * Complex.I + c) x)) := by
    simpa [Function.comp_def] using hcont.comp hc2
  exact hres

lemma continuousAt_heightKernel {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    {y : ℝ} (hy : 0 < y) (x : E n) (t : ℝ) :
    ContinuousAt (fun t : ℝ => heightKernel S y t x) t := by
  have h1 : ContinuousAt (fun u : ℝ => S.F ((u : ℂ) + (y : ℂ) * Complex.I) x) t := by
    simpa using continuousAt_F_affine S x y 0 (by simpa using hy) t
  have h2 : ContinuousAt (fun u : ℝ => S.F ((u : ℂ) + (y : ℂ) * Complex.I + 1) x) t :=
    continuousAt_F_affine S x y 1 (by simpa using hy) t
  have hτc : ContinuousAt (fun u : ℝ => (u : ℂ) + (y : ℂ) * Complex.I) t := by fun_prop
  have hfun : (fun t : ℝ => heightKernel S y t x)
      = fun u : ℝ => S.F ((u : ℂ) + (y : ℂ) * Complex.I) x - ((u : ℂ) + (y : ℂ) * Complex.I)
          * (S.F ((u : ℂ) + (y : ℂ) * Complex.I + 1) x - S.F ((u : ℂ) + (y : ℂ) * Complex.I) x) := by
    funext u; simp only [heightKernel]
  rw [hfun]
  exact h1.sub (hτc.mul (h2.sub h1))

lemma continuousAt_heightBKernel {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    {y : ℝ} (hy : 0 < y) (x : E n) (t : ℝ) :
    ContinuousAt (fun t : ℝ => heightBKernel S y t x) t := by
  have h1 : ContinuousAt (fun u : ℝ => S.F ((u : ℂ) + (y : ℂ) * Complex.I) x) t := by
    simpa using continuousAt_F_affine S x y 0 (by simpa using hy) t
  have h2 : ContinuousAt (fun u : ℝ => S.F ((u : ℂ) + (y : ℂ) * Complex.I + 1) x) t :=
    continuousAt_F_affine S x y 1 (by simpa using hy) t
  have hfun : (fun t : ℝ => heightBKernel S y t x)
      = fun u : ℝ => S.F ((u : ℂ) + (y : ℂ) * Complex.I + 1) x
          - S.F ((u : ℂ) + (y : ℂ) * Complex.I) x := by
    funext u; simp only [heightBKernel]
  rw [hfun]
  exact h2.sub h1

lemma continuousAt_heightKernelT {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    {y : ℝ} (hy : 0 < y) (x : E n) (t : ℝ) :
    ContinuousAt (fun t : ℝ => heightKernelT S y t x) t := by
  have h1 : ContinuousAt (fun u : ℝ => S.Ftilde ((u : ℂ) + (y : ℂ) * Complex.I) x) t := by
    simpa using continuousAt_Ftilde_affine S x y 0 (by simpa using hy) t
  have h2 : ContinuousAt (fun u : ℝ => S.Ftilde ((u : ℂ) + (y : ℂ) * Complex.I + 1) x) t :=
    continuousAt_Ftilde_affine S x y 1 (by simpa using hy) t
  have hτc : ContinuousAt (fun u : ℝ => (u : ℂ) + (y : ℂ) * Complex.I) t := by fun_prop
  have hfun : (fun t : ℝ => heightKernelT S y t x)
      = fun u : ℝ => S.Ftilde ((u : ℂ) + (y : ℂ) * Complex.I) x - ((u : ℂ) + (y : ℂ) * Complex.I)
          * (S.Ftilde ((u : ℂ) + (y : ℂ) * Complex.I + 1) x
            - S.Ftilde ((u : ℂ) + (y : ℂ) * Complex.I) x) := by
    funext u; simp only [heightKernelT]
  rw [hfun]
  exact h1.sub (hτc.mul (h2.sub h1))

lemma continuousAt_heightBKernelT {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    {y : ℝ} (hy : 0 < y) (x : E n) (t : ℝ) :
    ContinuousAt (fun t : ℝ => heightBKernelT S y t x) t := by
  have h1 : ContinuousAt (fun u : ℝ => S.Ftilde ((u : ℂ) + (y : ℂ) * Complex.I) x) t := by
    simpa using continuousAt_Ftilde_affine S x y 0 (by simpa using hy) t
  have h2 : ContinuousAt (fun u : ℝ => S.Ftilde ((u : ℂ) + (y : ℂ) * Complex.I + 1) x) t :=
    continuousAt_Ftilde_affine S x y 1 (by simpa using hy) t
  have hfun : (fun t : ℝ => heightBKernelT S y t x)
      = fun u : ℝ => S.Ftilde ((u : ℂ) + (y : ℂ) * Complex.I + 1) x
          - S.Ftilde ((u : ℂ) + (y : ℂ) * Complex.I) x := by
    funext u; simp only [heightBKernelT]
  rw [hfun]
  exact h2.sub h1

/-- The four weighted families are measurable in `t` at every `r`. -/
lemma measurable_aFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (r : ℝ) : Measurable fun t : ℝ => aFamily S m t r := by
  have h1 : Continuous (fun t : ℝ => heightKernel S (coeffHeight m.1) t (realIncl r)) :=
    continuous_iff_continuousAt.mpr
      (fun t => continuousAt_heightKernel S (coeffHeight_pos m.1) (realIncl r) t)
  have h2 : Continuous fun t : ℝ => coeffWeight m t := by
    simp only [coeffWeight]
    fun_prop
  have hf : (fun t : ℝ => aFamily S m t r)
      = fun t : ℝ => heightKernel S (coeffHeight m.1) t (realIncl r) * coeffWeight m t := rfl
  rw [hf]
  exact (h1.mul h2).measurable

lemma measurable_bFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (r : ℝ) : Measurable fun t : ℝ => bFamily S m t r := by
  have h1 : Continuous (fun t : ℝ => heightBKernel S (coeffHeight m.1) t (realIncl r)) :=
    continuous_iff_continuousAt.mpr
      (fun t => continuousAt_heightBKernel S (coeffHeight_pos m.1) (realIncl r) t)
  have h2 : Continuous fun t : ℝ => coeffWeight m t := by
    simp only [coeffWeight]
    fun_prop
  have hf : (fun t : ℝ => bFamily S m t r)
      = fun t : ℝ => coeffConst m
          * (heightBKernel S (coeffHeight m.1) t (realIncl r) * coeffWeight m t) := rfl
  rw [hf]
  exact (continuous_const.mul (h1.mul h2)).measurable

lemma measurable_aTFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (r : ℝ) : Measurable fun t : ℝ => aTFamily S m t r := by
  have h1 : Continuous (fun t : ℝ => heightKernelT S (coeffHeight m.1) t (realIncl r)) :=
    continuous_iff_continuousAt.mpr
      (fun t => continuousAt_heightKernelT S (coeffHeight_pos m.1) (realIncl r) t)
  have h2 : Continuous fun t : ℝ => coeffWeight m t := by
    simp only [coeffWeight]
    fun_prop
  have hf : (fun t : ℝ => aTFamily S m t r)
      = fun t : ℝ => heightKernelT S (coeffHeight m.1) t (realIncl r) * coeffWeight m t := rfl
  rw [hf]
  exact (h1.mul h2).measurable

lemma measurable_bTFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (r : ℝ) : Measurable fun t : ℝ => bTFamily S m t r := by
  have h1 : Continuous (fun t : ℝ => heightBKernelT S (coeffHeight m.1) t (realIncl r)) :=
    continuous_iff_continuousAt.mpr
      (fun t => continuousAt_heightBKernelT S (coeffHeight_pos m.1) (realIncl r) t)
  have h2 : Continuous fun t : ℝ => coeffWeight m t := by
    simp only [coeffWeight]
    fun_prop
  have hf : (fun t : ℝ => bTFamily S m t r)
      = fun t : ℝ => coeffConst m
          * (heightBKernelT S (coeffHeight m.1) t (realIncl r) * coeffWeight m t) := rfl
  rw [hf]
  exact (continuous_const.mul (h1.mul h2)).measurable

/-- The coefficient functions are the integrals of the families. -/
lemma aCoeff_eq_integral_aFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (r : ℝ) :
    aCoeff S m (realIncl r) = ∫ t in (0 : ℝ)..1, aFamily S m t r := by
  rw [aCoeff_eq_heightKernel S m (realIncl r) (coeffHeight_pos m.1)]
  rfl

lemma bCoeff_eq_integral_bFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (r : ℝ) :
    bCoeff S m (realIncl r) = ∫ t in (0 : ℝ)..1, bFamily S m t r := by
  rw [bCoeff_eq_heightBKernel S m (realIncl r) (coeffHeight_pos m.1)]
  rw [show (fun t : ℝ => bFamily S m t r) = fun t : ℝ => coeffConst m *
      (heightBKernel S (coeffHeight m.1) t (realIncl r) * coeffWeight m t) from rfl,
    intervalIntegral.integral_const_mul]
  rfl

lemma aTildeCoeff_eq_integral_aTFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (r : ℝ) :
    aTildeCoeff S m (realIncl r) = ∫ t in (0 : ℝ)..1, aTFamily S m t r := by
  rw [aTildeCoeff_eq_heightKernelT S m (realIncl r) (coeffHeight_pos m.1)]
  rfl

lemma bTildeCoeff_eq_integral_bTFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (r : ℝ) :
    bTildeCoeff S m (realIncl r) = ∫ t in (0 : ℝ)..1, bTFamily S m t r := by
  rw [bTildeCoeff_eq_heightBKernelT S m (realIncl r) (coeffHeight_pos m.1)]
  rw [show (fun t : ℝ => bTFamily S m t r) = fun t : ℝ => coeffConst m *
      (heightBKernelT S (coeffHeight m.1) t (realIncl r) * coeffWeight m t) from rfl,
    intervalIntegral.integral_const_mul]
  rfl

/-- **Bound on the `j`-th derivative of the `a`-family.** -/
lemma bound_aFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (j : ℕ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ r : ℝ,
      ‖iteratedDeriv j (aFamily S m t) r‖ ≤ Cker (growthData S) j m.1 := by
  intro t ht r
  have hspec := growthData_spec S j
  have hker := bound_heightKernel_profile S hspec.1 hspec.2.1 hspec.2.2.1 hspec.2.2.2.1 j
    (fun τ x hτ => hspec.2.2.2.2 τ x hτ) (coeffHeight_pos m.1) (coeffHeight_le_one m.1) ht r
  have hderiv : iteratedDeriv j (aFamily S m t) r
      = coeffWeight m t
        * iteratedDeriv j (fun s : ℝ => heightKernel S (coeffHeight m.1) t (realIncl s)) r := by
    have hfun : aFamily S m t = fun r : ℝ =>
        coeffWeight m t * heightKernel S (coeffHeight m.1) t (realIncl r) := by
      funext r; simp only [aFamily, coeffWeight]; ring
    rw [hfun]
    exact iteratedDeriv_const_mul _
      (((contDiff_heightKernel_profile S (coeffHeight m.1) t).contDiffAt).of_le le_top)
  rw [hderiv, norm_mul, norm_coeffWeight]
  have hw : Real.exp (2 * Real.pi * (m.1 : ℝ) * coeffHeight m.1) ≤ Real.exp (2 * Real.pi) :=
    exp_coeffHeight_le m.1
  have hpow : (coeffHeight m.1) ^ (-(growthData S j).2.1) = ((m.1 : ℝ) + 1) ^ ((growthData S j).2.1) :=
    coeffHeight_rpow_neg m.1 _
  have hker' : ‖iteratedDeriv j (fun s : ℝ => heightKernel S (coeffHeight m.1) t (realIncl s)) r‖
      ≤ 6 * ((growthData S j).1 * (coeffHeight m.1) ^ (-(growthData S j).2.1)
        + (growthData S j).2.2.1 * 3 ^ ((growthData S j).2.2.2)) := hker
  calc Real.exp (2 * Real.pi * (m.1 : ℝ) * coeffHeight m.1)
        * ‖iteratedDeriv j (fun s : ℝ => heightKernel S (coeffHeight m.1) t (realIncl s)) r‖
      ≤ Real.exp (2 * Real.pi)
          * (6 * ((growthData S j).1 * (coeffHeight m.1) ^ (-(growthData S j).2.1)
            + (growthData S j).2.2.1 * 3 ^ ((growthData S j).2.2.2))) :=
        mul_le_mul hw hker' (norm_nonneg _) (Real.exp_pos _).le
    _ = Cker (growthData S) j m.1 := by rw [Cker, hpow]; ring

/-- **Bound on the `j`-th derivative of the `b`-family.** -/
lemma bound_bFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (j : ℕ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ r : ℝ,
      ‖iteratedDeriv j (bFamily S m t) r‖ ≤ Cker (growthData S) j m.1 := by
  intro t ht r
  have hspec := growthData_spec S j
  have hker := bound_heightBKernel_profile S hspec.1 hspec.2.1 hspec.2.2.1 hspec.2.2.2.1 j
    (fun τ x hτ => hspec.2.2.2.2 τ x hτ) (coeffHeight_pos m.1) (coeffHeight_le_one m.1) ht r
  have hderiv : iteratedDeriv j (bFamily S m t) r
      = coeffConst m * (coeffWeight m t
        * iteratedDeriv j (fun s : ℝ => heightBKernel S (coeffHeight m.1) t (realIncl s)) r) := by
    have hfun : bFamily S m t = fun r : ℝ =>
        coeffConst m * (coeffWeight m t * heightBKernel S (coeffHeight m.1) t (realIncl r)) := by
      funext r; simp only [bFamily, coeffConst, coeffWeight]; ring
    have h2 : ContDiffAt ℝ (j : ℕ∞)
        (fun r : ℝ => coeffWeight m t * heightBKernel S (coeffHeight m.1) t (realIncl r)) r :=
      (contDiffAt_const (x := r) (c := coeffWeight m t)).mul
        (((contDiff_heightBKernel_profile S (coeffHeight m.1) t).contDiffAt).of_le le_top)
    have hinner : iteratedDeriv j (fun r : ℝ =>
          coeffWeight m t * heightBKernel S (coeffHeight m.1) t (realIncl r)) r
        = coeffWeight m t * iteratedDeriv j (fun s : ℝ =>
            heightBKernel S (coeffHeight m.1) t (realIncl s)) r :=
      iteratedDeriv_const_mul _
        (((contDiff_heightBKernel_profile S (coeffHeight m.1) t).contDiffAt).of_le le_top)
    have houter : iteratedDeriv j (fun r : ℝ => coeffConst m *
          (coeffWeight m t * heightBKernel S (coeffHeight m.1) t (realIncl r))) r
        = coeffConst m * iteratedDeriv j (fun r : ℝ =>
            coeffWeight m t * heightBKernel S (coeffHeight m.1) t (realIncl r)) r :=
      iteratedDeriv_const_mul _ h2
    rw [hfun, houter, hinner]
  rw [hderiv, norm_mul, norm_mul, norm_coeffWeight]
  have hw : Real.exp (2 * Real.pi * (m.1 : ℝ) * coeffHeight m.1) ≤ Real.exp (2 * Real.pi) :=
    exp_coeffHeight_le m.1
  have hpow : (coeffHeight m.1) ^ (-(growthData S j).2.1) = ((m.1 : ℝ) + 1) ^ ((growthData S j).2.1) :=
    coeffHeight_rpow_neg m.1 _
  have hker' : ‖iteratedDeriv j (fun s : ℝ => heightBKernel S (coeffHeight m.1) t (realIncl s)) r‖
      ≤ 6 * ((growthData S j).1 * (coeffHeight m.1) ^ (-(growthData S j).2.1)
        + (growthData S j).2.2.1 * 3 ^ ((growthData S j).2.2.2)) := hker
  have hC0 : 0 ≤ Cker (growthData S) j m.1 :=
    Cker_nonneg _ (fun j => ⟨(growthData_spec S j).1, (growthData_spec S j).2.1,
      (growthData_spec S j).2.2.1, (growthData_spec S j).2.2.2.1⟩) j m.1
  calc ‖coeffConst m‖ * (Real.exp (2 * Real.pi * (m.1 : ℝ) * coeffHeight m.1)
        * ‖iteratedDeriv j (fun s : ℝ => heightBKernel S (coeffHeight m.1) t (realIncl s)) r‖)
      ≤ ‖coeffConst m‖ * Cker (growthData S) j m.1 := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc Real.exp (2 * Real.pi * (m.1 : ℝ) * coeffHeight m.1)
              * ‖iteratedDeriv j (fun s : ℝ => heightBKernel S (coeffHeight m.1) t (realIncl s)) r‖
            ≤ Real.exp (2 * Real.pi)
                * (6 * ((growthData S j).1 * (coeffHeight m.1) ^ (-(growthData S j).2.1)
                  + (growthData S j).2.2.1 * 3 ^ ((growthData S j).2.2.2))) :=
              mul_le_mul hw hker' (norm_nonneg _) (Real.exp_pos _).le
          _ = Cker (growthData S) j m.1 := by rw [Cker, hpow]; ring
    _ ≤ Cker (growthData S) j m.1 := by
        calc ‖coeffConst m‖ * Cker (growthData S) j m.1
            ≤ 1 * Cker (growthData S) j m.1 :=
              mul_le_mul_of_nonneg_right (norm_coeffConst_le_one m) hC0
          _ = Cker (growthData S) j m.1 := one_mul _

/-- **Bound on the `j`-th derivative of the `a`-family of `F̃`.** -/
lemma bound_aTFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (j : ℕ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ r : ℝ,
      ‖iteratedDeriv j (aTFamily S m t) r‖ ≤ Cker (growthDataT S) j m.1 := by
  intro t ht r
  have hspec := growthDataT_spec S j
  have hker := bound_heightKernelT_profile S hspec.1 hspec.2.1 hspec.2.2.1 hspec.2.2.2.1 j
    (fun τ x hτ => hspec.2.2.2.2 τ x hτ) (coeffHeight_pos m.1) (coeffHeight_le_one m.1) ht r
  have hderiv : iteratedDeriv j (aTFamily S m t) r
      = coeffWeight m t
        * iteratedDeriv j (fun s : ℝ => heightKernelT S (coeffHeight m.1) t (realIncl s)) r := by
    have hfun : aTFamily S m t = fun r : ℝ =>
        coeffWeight m t * heightKernelT S (coeffHeight m.1) t (realIncl r) := by
      funext r; simp only [aTFamily, coeffWeight]; ring
    rw [hfun]
    exact iteratedDeriv_const_mul _
      (((contDiff_heightKernelT_profile S (coeffHeight m.1) t).contDiffAt).of_le le_top)
  rw [hderiv, norm_mul, norm_coeffWeight]
  have hw : Real.exp (2 * Real.pi * (m.1 : ℝ) * coeffHeight m.1) ≤ Real.exp (2 * Real.pi) :=
    exp_coeffHeight_le m.1
  have hpow : (coeffHeight m.1) ^ (-(growthDataT S j).2.1)
      = ((m.1 : ℝ) + 1) ^ ((growthDataT S j).2.1) := coeffHeight_rpow_neg m.1 _
  have hker' : ‖iteratedDeriv j (fun s : ℝ => heightKernelT S (coeffHeight m.1) t (realIncl s)) r‖
      ≤ 6 * ((growthDataT S j).1 * (coeffHeight m.1) ^ (-(growthDataT S j).2.1)
        + (growthDataT S j).2.2.1 * 3 ^ ((growthDataT S j).2.2.2)) := hker
  calc Real.exp (2 * Real.pi * (m.1 : ℝ) * coeffHeight m.1)
        * ‖iteratedDeriv j (fun s : ℝ => heightKernelT S (coeffHeight m.1) t (realIncl s)) r‖
      ≤ Real.exp (2 * Real.pi)
          * (6 * ((growthDataT S j).1 * (coeffHeight m.1) ^ (-(growthDataT S j).2.1)
            + (growthDataT S j).2.2.1 * 3 ^ ((growthDataT S j).2.2.2))) :=
        mul_le_mul hw hker' (norm_nonneg _) (Real.exp_pos _).le
    _ = Cker (growthDataT S) j m.1 := by rw [Cker, hpow]; ring

/-- **Bound on the `j`-th derivative of the `b`-family of `F̃`.** -/
lemma bound_bTFamily {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (m : Set.Ici (1 : ℕ)) (j : ℕ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ r : ℝ,
      ‖iteratedDeriv j (bTFamily S m t) r‖ ≤ Cker (growthDataT S) j m.1 := by
  intro t ht r
  have hspec := growthDataT_spec S j
  have hker := bound_heightBKernelT_profile S hspec.1 hspec.2.1 hspec.2.2.1 hspec.2.2.2.1 j
    (fun τ x hτ => hspec.2.2.2.2 τ x hτ) (coeffHeight_pos m.1) (coeffHeight_le_one m.1) ht r
  have hderiv : iteratedDeriv j (bTFamily S m t) r
      = coeffConst m * (coeffWeight m t
        * iteratedDeriv j (fun s : ℝ => heightBKernelT S (coeffHeight m.1) t (realIncl s)) r) := by
    have hfun : bTFamily S m t = fun r : ℝ =>
        coeffConst m * (coeffWeight m t * heightBKernelT S (coeffHeight m.1) t (realIncl r)) := by
      funext r; simp only [bTFamily, coeffConst, coeffWeight]; ring
    have h2 : ContDiffAt ℝ (j : ℕ∞)
        (fun r : ℝ => coeffWeight m t * heightBKernelT S (coeffHeight m.1) t (realIncl r)) r :=
      (contDiffAt_const (x := r) (c := coeffWeight m t)).mul
        (((contDiff_heightBKernelT_profile S (coeffHeight m.1) t).contDiffAt).of_le le_top)
    have hinner : iteratedDeriv j (fun r : ℝ =>
          coeffWeight m t * heightBKernelT S (coeffHeight m.1) t (realIncl r)) r
        = coeffWeight m t * iteratedDeriv j (fun s : ℝ =>
            heightBKernelT S (coeffHeight m.1) t (realIncl s)) r :=
      iteratedDeriv_const_mul _
        (((contDiff_heightBKernelT_profile S (coeffHeight m.1) t).contDiffAt).of_le le_top)
    have houter : iteratedDeriv j (fun r : ℝ => coeffConst m *
          (coeffWeight m t * heightBKernelT S (coeffHeight m.1) t (realIncl r))) r
        = coeffConst m * iteratedDeriv j (fun r : ℝ =>
            coeffWeight m t * heightBKernelT S (coeffHeight m.1) t (realIncl r)) r :=
      iteratedDeriv_const_mul _ h2
    rw [hfun, houter, hinner]
  rw [hderiv, norm_mul, norm_mul, norm_coeffWeight]
  have hw : Real.exp (2 * Real.pi * (m.1 : ℝ) * coeffHeight m.1) ≤ Real.exp (2 * Real.pi) :=
    exp_coeffHeight_le m.1
  have hpow : (coeffHeight m.1) ^ (-(growthDataT S j).2.1)
      = ((m.1 : ℝ) + 1) ^ ((growthDataT S j).2.1) := coeffHeight_rpow_neg m.1 _
  have hker' : ‖iteratedDeriv j (fun s : ℝ => heightBKernelT S (coeffHeight m.1) t (realIncl s)) r‖
      ≤ 6 * ((growthDataT S j).1 * (coeffHeight m.1) ^ (-(growthDataT S j).2.1)
        + (growthDataT S j).2.2.1 * 3 ^ ((growthDataT S j).2.2.2)) := hker
  have hC0 : 0 ≤ Cker (growthDataT S) j m.1 :=
    Cker_nonneg _ (fun j => ⟨(growthDataT_spec S j).1, (growthDataT_spec S j).2.1,
      (growthDataT_spec S j).2.2.1, (growthDataT_spec S j).2.2.2.1⟩) j m.1
  calc ‖coeffConst m‖ * (Real.exp (2 * Real.pi * (m.1 : ℝ) * coeffHeight m.1)
        * ‖iteratedDeriv j (fun s : ℝ => heightBKernelT S (coeffHeight m.1) t (realIncl s)) r‖)
      ≤ ‖coeffConst m‖ * Cker (growthDataT S) j m.1 := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc Real.exp (2 * Real.pi * (m.1 : ℝ) * coeffHeight m.1)
              * ‖iteratedDeriv j (fun s : ℝ => heightBKernelT S (coeffHeight m.1) t (realIncl s)) r‖
            ≤ Real.exp (2 * Real.pi)
                * (6 * ((growthDataT S j).1 * (coeffHeight m.1) ^ (-(growthDataT S j).2.1)
                  + (growthDataT S j).2.2.1 * 3 ^ ((growthDataT S j).2.2.2))) :=
              mul_le_mul hw hker' (norm_nonneg _) (Real.exp_pos _).le
          _ = Cker (growthDataT S) j m.1 := by rw [Cker, hpow]; ring
    _ ≤ Cker (growthDataT S) j m.1 := by
        calc ‖coeffConst m‖ * Cker (growthDataT S) j m.1
            ≤ 1 * Cker (growthDataT S) j m.1 :=
              mul_le_mul_of_nonneg_right (norm_coeffConst_le_one m) hC0
          _ = Cker (growthDataT S) j m.1 := one_mul _



/-- The combination of the delegated `ParametricDerivBounds` with the differentiability of the
parametric integrals: the iterated derivatives of the integral are the integrals of the iterated
derivatives, they are bounded by `C`, and each intermediate iterated derivative is differentiable
with the expected derivative. -/
lemma integral_rule {K : ℝ → ℝ → ℂ} {ℓ : ℕ}
    (hK : ∀ t, ContDiff ℝ ⊤ (K t)) (hmeas : ∀ r, Measurable fun t => K t r)
    (C : ℕ → ℝ) (hC0 : ∀ j, 0 ≤ C j)
    (hb : ∀ j ≤ ℓ + 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ r, ‖iteratedDeriv j (K t) r‖ ≤ C j) :
    (∀ j ≤ ℓ, ∀ r,
      iteratedDeriv j (fun r => ∫ t in (0 : ℝ)..1, K t r) r
        = ∫ t in (0 : ℝ)..1, iteratedDeriv j (K t) r) ∧
    (∀ j ≤ ℓ, ∀ r, ‖iteratedDeriv j (fun r => ∫ t in (0 : ℝ)..1, K t r) r‖ ≤ C j) ∧
    (∀ j ≤ ℓ, ∀ r, Measurable fun t => iteratedDeriv j (K t) r) ∧
    (∀ j < ℓ, ∀ r, HasDerivAt
        (fun r => iteratedDeriv j (fun r => ∫ t in (0 : ℝ)..1, K t r) r)
        (iteratedDeriv (j+1) (fun r => ∫ t in (0 : ℝ)..1, K t r) r) r) := by
  obtain ⟨hm, hform, hbnd⟩ := ParametricDerivBounds hK hmeas C hC0 hb
  refine ⟨hform, hbnd, hm, ?_⟩
  intro j hj r
  have hd := HasDerivAtParametricIntegral (K := K) (j := j) (r₀ := r) hK
    (fun r => hm j (le_of_lt hj) r) C hC0
    (fun i hi t ht r' => hb i (by omega) t ht r')
  rw [show (fun r : ℝ => iteratedDeriv j (fun r => ∫ t in (0 : ℝ)..1, K t r) r)
      = fun r : ℝ => ∫ t in (0 : ℝ)..1, iteratedDeriv j (K t) r from
        funext (fun r => hform j (le_of_lt hj) r),
    show iteratedDeriv (j+1) (fun r => ∫ t in (0 : ℝ)..1, K t r) r
      = ∫ t in (0 : ℝ)..1, iteratedDeriv (j+1) (K t) r from hform (j+1) (by omega) r]
  exact hd

/-- The growth-data nonnegativity in the form needed by `Cker_nonneg`. -/
lemma growthData_nonneg {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (k : ℕ) :
    0 ≤ (growthData S k).1 ∧ 0 ≤ (growthData S k).2.1 ∧ 0 ≤ (growthData S k).2.2.1
      ∧ 0 ≤ (growthData S k).2.2.2 :=
  ⟨(growthData_spec S k).1, (growthData_spec S k).2.1, (growthData_spec S k).2.2.1,
    (growthData_spec S k).2.2.2.1⟩

lemma growthDataT_nonneg {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (k : ℕ) :
    0 ≤ (growthDataT S k).1 ∧ 0 ≤ (growthDataT S k).2.1 ∧ 0 ≤ (growthDataT S k).2.2.1
      ∧ 0 ≤ (growthDataT S k).2.2.2 :=
  ⟨(growthDataT_spec S k).1, (growthDataT_spec S k).2.1, (growthDataT_spec S k).2.2.1,
    (growthDataT_spec S k).2.2.2.1⟩

/-- **The facts about the profile of `aCoeff S m`**: its iterated derivatives are the integrals of
the iterated derivatives of the family, they obey the bound `Cker`, and they are differentiable
with the expected derivative. -/
lemma facts_aCoeff {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (ℓ : ℕ) (m : Set.Ici (1 : ℕ)) :
    (∀ j ≤ ℓ, ∀ r : ℝ, iteratedDeriv j (fun r : ℝ => aCoeff S m (realIncl r)) r
        = ∫ t in (0 : ℝ)..1, iteratedDeriv j (aFamily S m t) r) ∧
    (∀ j ≤ ℓ, ∀ r : ℝ, ‖iteratedDeriv j (fun r : ℝ => aCoeff S m (realIncl r)) r‖
        ≤ Cker (growthData S) j m.1) ∧
    (∀ j < ℓ, ∀ r : ℝ,
      HasDerivAt (fun r : ℝ => iteratedDeriv j (fun r : ℝ => aCoeff S m (realIncl r)) r)
        (iteratedDeriv (j+1) (fun r : ℝ => aCoeff S m (realIncl r)) r) r) := by
  obtain ⟨hform, hbnd, hm, hder⟩ := integral_rule (contDiff_aFamily S m) (measurable_aFamily S m)
    (fun j => Cker (growthData S) j m.1)
    (fun j => Cker_nonneg _ (growthData_nonneg S) j m.1)
    (fun j _ t ht r => bound_aFamily S m j t ht r)
  have hid : (fun r : ℝ => ∫ t in (0 : ℝ)..1, aFamily S m t r)
      = fun r : ℝ => aCoeff S m (realIncl r) :=
    funext (fun r => (aCoeff_eq_integral_aFamily S m r).symm)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj r; rw [← hid]; exact hform j hj r
  · intro j hj r; rw [← hid]; exact hbnd j hj r
  · intro j hj r; rw [← hid]; exact hder j hj r

/-- The facts about the profile of `bCoeff S m`. -/
lemma facts_bCoeff {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (ℓ : ℕ) (m : Set.Ici (1 : ℕ)) :
    (∀ j ≤ ℓ, ∀ r : ℝ, iteratedDeriv j (fun r : ℝ => bCoeff S m (realIncl r)) r
        = ∫ t in (0 : ℝ)..1, iteratedDeriv j (bFamily S m t) r) ∧
    (∀ j ≤ ℓ, ∀ r : ℝ, ‖iteratedDeriv j (fun r : ℝ => bCoeff S m (realIncl r)) r‖
        ≤ Cker (growthData S) j m.1) ∧
    (∀ j < ℓ, ∀ r : ℝ,
      HasDerivAt (fun r : ℝ => iteratedDeriv j (fun r : ℝ => bCoeff S m (realIncl r)) r)
        (iteratedDeriv (j+1) (fun r : ℝ => bCoeff S m (realIncl r)) r) r) := by
  obtain ⟨hform, hbnd, hm, hder⟩ := integral_rule (contDiff_bFamily S m) (measurable_bFamily S m)
    (fun j => Cker (growthData S) j m.1)
    (fun j => Cker_nonneg _ (growthData_nonneg S) j m.1)
    (fun j _ t ht r => bound_bFamily S m j t ht r)
  have hid : (fun r : ℝ => ∫ t in (0 : ℝ)..1, bFamily S m t r)
      = fun r : ℝ => bCoeff S m (realIncl r) :=
    funext (fun r => (bCoeff_eq_integral_bFamily S m r).symm)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj r; rw [← hid]; exact hform j hj r
  · intro j hj r; rw [← hid]; exact hbnd j hj r
  · intro j hj r; rw [← hid]; exact hder j hj r

/-- The facts about the profile of `aTildeCoeff S m`. -/
lemma facts_aTildeCoeff {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (ℓ : ℕ) (m : Set.Ici (1 : ℕ)) :
    (∀ j ≤ ℓ, ∀ r : ℝ, iteratedDeriv j (fun r : ℝ => aTildeCoeff S m (realIncl r)) r
        = ∫ t in (0 : ℝ)..1, iteratedDeriv j (aTFamily S m t) r) ∧
    (∀ j ≤ ℓ, ∀ r : ℝ, ‖iteratedDeriv j (fun r : ℝ => aTildeCoeff S m (realIncl r)) r‖
        ≤ Cker (growthDataT S) j m.1) ∧
    (∀ j < ℓ, ∀ r : ℝ,
      HasDerivAt (fun r : ℝ => iteratedDeriv j (fun r : ℝ => aTildeCoeff S m (realIncl r)) r)
        (iteratedDeriv (j+1) (fun r : ℝ => aTildeCoeff S m (realIncl r)) r) r) := by
  obtain ⟨hform, hbnd, hm, hder⟩ := integral_rule (contDiff_aTFamily S m) (measurable_aTFamily S m)
    (fun j => Cker (growthDataT S) j m.1)
    (fun j => Cker_nonneg _ (growthDataT_nonneg S) j m.1)
    (fun j _ t ht r => bound_aTFamily S m j t ht r)
  have hid : (fun r : ℝ => ∫ t in (0 : ℝ)..1, aTFamily S m t r)
      = fun r : ℝ => aTildeCoeff S m (realIncl r) :=
    funext (fun r => (aTildeCoeff_eq_integral_aTFamily S m r).symm)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj r; rw [← hid]; exact hform j hj r
  · intro j hj r; rw [← hid]; exact hbnd j hj r
  · intro j hj r; rw [← hid]; exact hder j hj r

/-- The facts about the profile of `bTildeCoeff S m`. -/
lemma facts_bTildeCoeff {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (ℓ : ℕ) (m : Set.Ici (1 : ℕ)) :
    (∀ j ≤ ℓ, ∀ r : ℝ, iteratedDeriv j (fun r : ℝ => bTildeCoeff S m (realIncl r)) r
        = ∫ t in (0 : ℝ)..1, iteratedDeriv j (bTFamily S m t) r) ∧
    (∀ j ≤ ℓ, ∀ r : ℝ, ‖iteratedDeriv j (fun r : ℝ => bTildeCoeff S m (realIncl r)) r‖
        ≤ Cker (growthDataT S) j m.1) ∧
    (∀ j < ℓ, ∀ r : ℝ,
      HasDerivAt (fun r : ℝ => iteratedDeriv j (fun r : ℝ => bTildeCoeff S m (realIncl r)) r)
        (iteratedDeriv (j+1) (fun r : ℝ => bTildeCoeff S m (realIncl r)) r) r) := by
  obtain ⟨hform, hbnd, hm, hder⟩ := integral_rule (contDiff_bTFamily S m) (measurable_bTFamily S m)
    (fun j => Cker (growthDataT S) j m.1)
    (fun j => Cker_nonneg _ (growthDataT_nonneg S) j m.1)
    (fun j _ t ht r => bound_bTFamily S m j t ht r)
  have hid : (fun r : ℝ => ∫ t in (0 : ℝ)..1, bTFamily S m t r)
      = fun r : ℝ => bTildeCoeff S m (realIncl r) :=
    funext (fun r => (bTildeCoeff_eq_integral_bTFamily S m r).symm)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj r; rw [← hid]; exact hform j hj r
  · intro j hj r; rw [← hid]; exact hbnd j hj r
  · intro j hj r; rw [← hid]; exact hder j hj r



/-- **Polynomial growth of `Cker`.**  At height `1/(m+1)` the bound `Cker G j m` grows at most like
`(m+1)^⌈β⌉`. -/
lemma Cker_le_poly {G : ℕ → ℝ × ℝ × ℝ × ℝ}
    (hG : ∀ j, 0 ≤ (G j).1 ∧ 0 ≤ (G j).2.1 ∧ 0 ≤ (G j).2.2.1 ∧ 0 ≤ (G j).2.2.2)
    (j m : ℕ) :
    Cker G j m ≤ 6 * Real.exp (2 * Real.pi) *
      ((G j).1 + (G j).2.2.1 * 3 ^ ((G j).2.2.2)) * ((m : ℝ) + 1) ^ (Nat.ceil (G j).2.1) := by
  have hx1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have h : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hxN : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ (Nat.ceil (G j).2.1) := by
    rw [← Real.rpow_natCast]
    exact Real.one_le_rpow hx1 (Nat.cast_nonneg _)
  have hceil : (G j).2.1 ≤ ((Nat.ceil (G j).2.1 : ℕ) : ℝ) := Nat.le_ceil _
  have hC0 : 0 ≤ (G j).2.2.1 * 3 ^ ((G j).2.2.2) :=
    mul_nonneg (hG j).2.2.1 (Real.rpow_nonneg (by norm_num) _)
  have hsum : (G j).1 * ((m : ℝ) + 1) ^ ((G j).2.1) + (G j).2.2.1 * 3 ^ ((G j).2.2.2)
      ≤ ((G j).1 + (G j).2.2.1 * 3 ^ ((G j).2.2.2)) * ((m : ℝ) + 1) ^ (Nat.ceil (G j).2.1) := by
    have h1 : (G j).1 * ((m : ℝ) + 1) ^ ((G j).2.1)
        ≤ (G j).1 * ((m : ℝ) + 1) ^ (Nat.ceil (G j).2.1) := by
      refine mul_le_mul_of_nonneg_left ?_ (hG j).1
      calc ((m : ℝ) + 1) ^ ((G j).2.1) ≤ ((m : ℝ) + 1) ^ ((Nat.ceil (G j).2.1 : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx1 hceil
        _ = ((m : ℝ) + 1) ^ (Nat.ceil (G j).2.1) := Real.rpow_natCast _ _
    have h2 : (G j).2.2.1 * 3 ^ ((G j).2.2.2)
        ≤ (G j).2.2.1 * 3 ^ ((G j).2.2.2) * ((m : ℝ) + 1) ^ (Nat.ceil (G j).2.1) := by
      calc (G j).2.2.1 * 3 ^ ((G j).2.2.2) = (G j).2.2.1 * 3 ^ ((G j).2.2.2) * 1 := by ring
        _ ≤ (G j).2.2.1 * 3 ^ ((G j).2.2.2) * ((m : ℝ) + 1) ^ (Nat.ceil (G j).2.1) :=
            mul_le_mul_of_nonneg_left hxN hC0
    calc (G j).1 * ((m : ℝ) + 1) ^ ((G j).2.1) + (G j).2.2.1 * 3 ^ ((G j).2.2.2)
        ≤ (G j).1 * ((m : ℝ) + 1) ^ (Nat.ceil (G j).2.1)
          + (G j).2.2.1 * 3 ^ ((G j).2.2.2) * ((m : ℝ) + 1) ^ (Nat.ceil (G j).2.1) :=
          add_le_add h1 h2
      _ = ((G j).1 + (G j).2.2.1 * 3 ^ ((G j).2.2.2)) * ((m : ℝ) + 1) ^ (Nat.ceil (G j).2.1) := by
          ring
  calc Cker G j m
      = 6 * Real.exp (2 * Real.pi) * ((G j).1 * ((m : ℝ) + 1) ^ ((G j).2.1)
          + (G j).2.2.1 * 3 ^ ((G j).2.2.2)) := by rw [Cker]
    _ ≤ 6 * Real.exp (2 * Real.pi) * (((G j).1 + (G j).2.2.1 * 3 ^ ((G j).2.2.2))
          * ((m : ℝ) + 1) ^ (Nat.ceil (G j).2.1)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 6 * Real.exp (2 * Real.pi) * ((G j).1 + (G j).2.2.1 * 3 ^ ((G j).2.2.2))
          * ((m : ℝ) + 1) ^ (Nat.ceil (G j).2.1) := by ring

/-- The norm of `Cker` as a complex number. -/
lemma complex_ofReal_Cker (G : ℕ → ℝ × ℝ × ℝ × ℝ)
    (hG : ∀ j, 0 ≤ (G j).1 ∧ 0 ≤ (G j).2.1 ∧ 0 ≤ (G j).2.2.1 ∧ 0 ≤ (G j).2.2.2)
    (j m : ℕ) : ‖((Cker G j m : ℝ) : ℂ)‖ = Cker G j m := by
  rw [norm_ofReal_complex', abs_of_nonneg (Cker_nonneg G hG j m)]

/-- The polynomial growth of the complex sequence `Cker`. -/
lemma Cker_norm_le_poly (G : ℕ → ℝ × ℝ × ℝ × ℝ)
    (hG : ∀ j, 0 ≤ (G j).1 ∧ 0 ≤ (G j).2.1 ∧ 0 ≤ (G j).2.2.1 ∧ 0 ≤ (G j).2.2.2)
    (j : ℕ) : ∀ m : Set.Ici (1 : ℕ),
      ‖((Cker G j m.1 : ℝ) : ℂ)‖
        ≤ 6 * Real.exp (2 * Real.pi) * ((G j).1 + (G j).2.2.1 * 3 ^ ((G j).2.2.2))
            * ((m.1 : ℝ) + 1) ^ (Nat.ceil (G j).2.1) := by
  intro m
  rw [complex_ofReal_Cker G hG j m.1]
  exact Cker_le_poly hG j m.1

lemma poly_const_nonneg (G : ℕ → ℝ × ℝ × ℝ × ℝ)
    (hG : ∀ j, 0 ≤ (G j).1 ∧ 0 ≤ (G j).2.1 ∧ 0 ≤ (G j).2.2.1 ∧ 0 ≤ (G j).2.2.2) (j : ℕ) :
    0 ≤ 6 * Real.exp (2 * Real.pi) * ((G j).1 + (G j).2.2.1 * 3 ^ ((G j).2.2.2)) := by
  refine mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) (add_nonneg (hG j).1 ?_)
  exact mul_nonneg (hG j).2.2.1 (Real.rpow_nonneg (by norm_num) _)

/-- Summability of `Cker G k m · e^{2π i m τ}`. -/
lemma summable_Cker_dirichlet {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (k : ℕ)
    (τ : ℂ) (hτ : 0 < τ.im) :
    Summable fun m : Set.Ici (1 : ℕ) =>
      ((Cker (growthData S) k m.1 : ℝ) : ℂ) * dirichletTerm m.1 τ :=
  summable_mul_dirichletTerm (poly_const_nonneg (growthData S) (growthData_nonneg S) k)
    (Cker_norm_le_poly (growthData S) (growthData_nonneg S) k) τ hτ

/-- Summability of `Cker G k m · √(2m) · e^{2π i m τ}`. -/
lemma summable_Cker_rate_dirichlet {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (k : ℕ)
    (τ : ℂ) (hτ : 0 < τ.im) :
    Summable fun m : Set.Ici (1 : ℕ) =>
      ((Cker (growthData S) k m.1 : ℝ) : ℂ) * (rate m.1 : ℂ) * dirichletTerm m.1 τ :=
  (summable_rate_mul_dirichletTerm (poly_const_nonneg (growthData S) (growthData_nonneg S) k)
    (Cker_norm_le_poly (growthData S) (growthData_nonneg S) k) τ hτ).congr (fun m => by ring)

/-- Summability of `Cker G k m · e^{2π i m τ}` for `F̃`. -/
lemma summable_CkerT_dirichlet {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (k : ℕ)
    (τ : ℂ) (hτ : 0 < τ.im) :
    Summable fun m : Set.Ici (1 : ℕ) =>
      ((Cker (growthDataT S) k m.1 : ℝ) : ℂ) * dirichletTerm m.1 τ :=
  summable_mul_dirichletTerm (poly_const_nonneg (growthDataT S) (growthDataT_nonneg S) k)
    (Cker_norm_le_poly (growthDataT S) (growthDataT_nonneg S) k) τ hτ

/-- Summability of `Cker G k m · √(2m) · e^{2π i m τ}` for `F̃`. -/
lemma summable_CkerT_rate_dirichlet {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (k : ℕ)
    (τ : ℂ) (hτ : 0 < τ.im) :
    Summable fun m : Set.Ici (1 : ℕ) =>
      ((Cker (growthDataT S) k m.1 : ℝ) : ℂ) * (rate m.1 : ℂ) * dirichletTerm m.1 τ :=
  (summable_rate_mul_dirichletTerm (poly_const_nonneg (growthDataT S) (growthDataT_nonneg S) k)
    (Cker_norm_le_poly (growthDataT S) (growthDataT_nonneg S) k) τ hτ).congr (fun m => by ring)



/-- Summability of `Cker G k m · (m+1) · e^{2π i m τ}`. -/
lemma summable_Cker_addOne_dirichlet {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (k : ℕ)
    (τ : ℂ) (hτ : 0 < τ.im) :
    Summable fun m : Set.Ici (1 : ℕ) =>
      ((Cker (growthData S) k m.1 : ℝ) : ℂ) * ((m.1 : ℝ) + 1 : ℂ) * dirichletTerm m.1 τ := by
  refine summable_mul_dirichletTerm (N := Nat.ceil (growthData S k).2.1 + 1)
    (C := 6 * Real.exp (2 * Real.pi)
      * ((growthData S k).1 + (growthData S k).2.2.1 * 3 ^ ((growthData S k).2.2.2)))
    (poly_const_nonneg (growthData S) (growthData_nonneg S) k) (fun m => ?_) τ hτ
  have hc : ‖((Cker (growthData S) k m.1 : ℝ) : ℂ)‖ = Cker (growthData S) k m.1 :=
    complex_ofReal_Cker _ (growthData_nonneg S) k m.1
  have hm : ‖(((m.1 : ℝ) : ℂ) + 1)‖ = ((m.1 : ℝ) + 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, norm_ofReal_complex', abs_of_nonneg (by positivity)]
  rw [norm_mul, hc, hm]
  calc Cker (growthData S) k m.1 * ((m.1 : ℝ) + 1)
      ≤ 6 * Real.exp (2 * Real.pi) * ((growthData S k).1 + (growthData S k).2.2.1 * 3 ^ ((growthData S k).2.2.2))
          * ((m.1 : ℝ) + 1) ^ (Nat.ceil (growthData S k).2.1) * ((m.1 : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (Cker_le_poly (growthData_nonneg S) k m.1)
          (by positivity)
    _ = 6 * Real.exp (2 * Real.pi) * ((growthData S k).1 + (growthData S k).2.2.1 * 3 ^ ((growthData S k).2.2.2))
          * ((m.1 : ℝ) + 1) ^ (Nat.ceil (growthData S k).2.1 + 1) := by
        rw [pow_succ]; ring

/-- Summability of `Cker G k m · (m+1) · e^{2π i m τ}` for `F̃`. -/
lemma summable_CkerT_addOne_dirichlet {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (k : ℕ)
    (τ : ℂ) (hτ : 0 < τ.im) :
    Summable fun m : Set.Ici (1 : ℕ) =>
      ((Cker (growthDataT S) k m.1 : ℝ) : ℂ) * ((m.1 : ℝ) + 1 : ℂ) * dirichletTerm m.1 τ := by
  refine summable_mul_dirichletTerm (N := Nat.ceil (growthDataT S k).2.1 + 1)
    (C := 6 * Real.exp (2 * Real.pi)
      * ((growthDataT S k).1 + (growthDataT S k).2.2.1 * 3 ^ ((growthDataT S k).2.2.2)))
    (poly_const_nonneg (growthDataT S) (growthDataT_nonneg S) k) (fun m => ?_) τ hτ
  have hc : ‖((Cker (growthDataT S) k m.1 : ℝ) : ℂ)‖ = Cker (growthDataT S) k m.1 :=
    complex_ofReal_Cker _ (growthDataT_nonneg S) k m.1
  have hm : ‖(((m.1 : ℝ) : ℂ) + 1)‖ = ((m.1 : ℝ) + 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, norm_ofReal_complex', abs_of_nonneg (by positivity)]
  rw [norm_mul, hc, hm]
  calc Cker (growthDataT S) k m.1 * ((m.1 : ℝ) + 1)
      ≤ 6 * Real.exp (2 * Real.pi) * ((growthDataT S k).1 + (growthDataT S k).2.2.1 * 3 ^ ((growthDataT S k).2.2.2))
          * ((m.1 : ℝ) + 1) ^ (Nat.ceil (growthDataT S k).2.1) * ((m.1 : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (Cker_le_poly (growthDataT_nonneg S) k m.1)
          (by positivity)
    _ = 6 * Real.exp (2 * Real.pi) * ((growthDataT S k).1 + (growthDataT S k).2.2.1 * 3 ^ ((growthDataT S k).2.2.2))
          * ((m.1 : ℝ) + 1) ^ (Nat.ceil (growthDataT S k).2.1 + 1) := by
        rw [pow_succ]; ring



/-- The bound sequence for the termwise differentiation in the `F` case. -/
def vSeq {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (τ : ℂ) (k : ℕ)
    (m : Set.Ici (1 : ℕ)) : ℝ :=
  ‖dirichletTerm m.1 τ‖ * Cker (growthData S) k m.1
    + ‖(rate m.1 : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I * τ) * dirichletTerm m.1 τ)‖
        * Cker (growthData S) k m.1

/-- The bound sequence for the termwise differentiation in the `F̃` case. -/
def vSeqT {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (τ : ℂ) (k : ℕ)
    (m : Set.Ici (1 : ℕ)) : ℝ :=
  ‖dirichletTerm m.1 τ‖ * Cker (growthDataT S) k m.1
    + ‖(rate m.1 : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I * τ) * dirichletTerm m.1 τ)‖
        * Cker (growthDataT S) k m.1

lemma summable_vSeq {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (k : ℕ)
    (τ : ℂ) (hτ : 0 < τ.im) : Summable (vSeq S τ k) := by
  have h1 : Summable fun m : Set.Ici (1 : ℕ) =>
      ‖(((Cker (growthData S) k m.1 : ℝ)) : ℂ) * dirichletTerm m.1 τ‖ :=
    (summable_Cker_dirichlet S k τ hτ).norm
  have h2 : Summable fun m : Set.Ici (1 : ℕ) =>
      ‖2 * (Real.pi : ℂ) * Complex.I * τ‖
        * ‖(((Cker (growthData S) k m.1 : ℝ)) : ℂ) * (rate m.1 : ℂ) * dirichletTerm m.1 τ‖ :=
    ((summable_Cker_rate_dirichlet S k τ hτ).norm).mul_left _
  have hmain : Summable fun m : Set.Ici (1 : ℕ) =>
      ‖(((Cker (growthData S) k m.1 : ℝ)) : ℂ) * dirichletTerm m.1 τ‖
        + ‖2 * (Real.pi : ℂ) * Complex.I * τ‖
          * ‖(((Cker (growthData S) k m.1 : ℝ)) : ℂ) * (rate m.1 : ℂ) * dirichletTerm m.1 τ‖ :=
    h1.add h2
  refine hmain.congr (fun m => ?_)
  have hc : ‖((Cker (growthData S) k m.1 : ℝ) : ℂ)‖ = Cker (growthData S) k m.1 :=
    complex_ofReal_Cker _ (growthData_nonneg S) k m.1
  have hr : ‖(rate m.1 : ℂ)‖ = rate m.1 := by
    have hr' : (0 : ℝ) ≤ rate m.1 := Real.sqrt_nonneg _
    rw [norm_ofReal_complex', abs_of_nonneg hr']
  have key1 : ‖(((Cker (growthData S) k m.1 : ℝ)) : ℂ) * dirichletTerm m.1 τ‖
      = ‖dirichletTerm m.1 τ‖ * Cker (growthData S) k m.1 := by
    rw [norm_mul, hc]
    try ring
  have hL : ‖(((Cker (growthData S) k m.1 : ℝ)) : ℂ) * (rate m.1 : ℂ) * dirichletTerm m.1 τ‖
      = Cker (growthData S) k m.1 * rate m.1 * ‖dirichletTerm m.1 τ‖ := by
    rw [norm_mul, norm_mul, hc, hr]
    try ring
  have hR : ‖(rate m.1 : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I * τ) * dirichletTerm m.1 τ)‖
      = ‖2 * (Real.pi : ℂ) * Complex.I * τ‖ * (rate m.1 * ‖dirichletTerm m.1 τ‖) := by
    rw [show (rate m.1 : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I * τ) * dirichletTerm m.1 τ)
        = (2 * (Real.pi : ℂ) * Complex.I * τ) * ((rate m.1 : ℂ) * dirichletTerm m.1 τ) from by ring]
    simp only [norm_mul, hr]
    try ring
  simp only [vSeq]
  rw [key1, hL, hR]
  try ring

lemma summable_vSeqT {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) (k : ℕ)
    (τ : ℂ) (hτ : 0 < τ.im) : Summable (vSeqT S τ k) := by
  have h1 : Summable fun m : Set.Ici (1 : ℕ) =>
      ‖(((Cker (growthDataT S) k m.1 : ℝ)) : ℂ) * dirichletTerm m.1 τ‖ :=
    (summable_CkerT_dirichlet S k τ hτ).norm
  have h2 : Summable fun m : Set.Ici (1 : ℕ) =>
      ‖2 * (Real.pi : ℂ) * Complex.I * τ‖
        * ‖(((Cker (growthDataT S) k m.1 : ℝ)) : ℂ) * (rate m.1 : ℂ) * dirichletTerm m.1 τ‖ :=
    ((summable_CkerT_rate_dirichlet S k τ hτ).norm).mul_left _
  have hmain : Summable fun m : Set.Ici (1 : ℕ) =>
      ‖(((Cker (growthDataT S) k m.1 : ℝ)) : ℂ) * dirichletTerm m.1 τ‖
        + ‖2 * (Real.pi : ℂ) * Complex.I * τ‖
          * ‖(((Cker (growthDataT S) k m.1 : ℝ)) : ℂ) * (rate m.1 : ℂ) * dirichletTerm m.1 τ‖ :=
    h1.add h2
  refine hmain.congr (fun m => ?_)
  have hc : ‖((Cker (growthDataT S) k m.1 : ℝ) : ℂ)‖ = Cker (growthDataT S) k m.1 :=
    complex_ofReal_Cker _ (growthDataT_nonneg S) k m.1
  have hr : ‖(rate m.1 : ℂ)‖ = rate m.1 := by
    have hr' : (0 : ℝ) ≤ rate m.1 := Real.sqrt_nonneg _
    rw [norm_ofReal_complex', abs_of_nonneg hr']
  have key1 : ‖(((Cker (growthDataT S) k m.1 : ℝ)) : ℂ) * dirichletTerm m.1 τ‖
      = ‖dirichletTerm m.1 τ‖ * Cker (growthDataT S) k m.1 := by
    rw [norm_mul, hc]
    try ring
  have hL : ‖(((Cker (growthDataT S) k m.1 : ℝ)) : ℂ) * (rate m.1 : ℂ) * dirichletTerm m.1 τ‖
      = Cker (growthDataT S) k m.1 * rate m.1 * ‖dirichletTerm m.1 τ‖ := by
    rw [norm_mul, norm_mul, hc, hr]
    try ring
  have hR : ‖(rate m.1 : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I * τ) * dirichletTerm m.1 τ)‖
      = ‖2 * (Real.pi : ℂ) * Complex.I * τ‖ * (rate m.1 * ‖dirichletTerm m.1 τ‖) := by
    rw [show (rate m.1 : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I * τ) * dirichletTerm m.1 τ)
        = (2 * (Real.pi : ℂ) * Complex.I * τ) * ((rate m.1 : ℂ) * dirichletTerm m.1 τ) from by ring]
    simp only [norm_mul, hr]
    try ring
  simp only [vSeqT]
  rw [key1, hL, hR]
  try ring


/-- **Termwise radial differentiation of the expansion of `F`.** -/
lemma expansion_F_deriv {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (ℓ : ℕ) (τ : ℂ) (hτ : 0 < τ.im) :
    ∀ r : ℝ, iteratedDeriv ℓ (fun r : ℝ => S.F τ (realIncl r)) r =
      (∑' m : Set.Ici (1 : ℕ),
          iteratedDeriv ℓ (fun r : ℝ => aCoeff S m (realIncl r)) r * dirichletTerm m.1 τ)
      + (2 * (Real.pi : ℂ) * Complex.I * τ)
        * ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ)
            * iteratedDeriv ℓ (fun r : ℝ => bCoeff S m (realIncl r)) r * dirichletTerm m.1 τ := by
  have hA := fun m : Set.Ici (1 : ℕ) => facts_aCoeff S (ℓ + 1) m
  have hB := fun m : Set.Ici (1 : ℕ) => facts_bCoeff S (ℓ + 1) m
  set Ψ : Set.Ici (1 : ℕ) → ℝ → ℂ := fun m r =>
      (fun r : ℝ => aCoeff S m (realIncl r)) r * dirichletTerm m.1 τ
      + (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ) * dirichletTerm m.1 τ)
        * (fun r : ℝ => bCoeff S m (realIncl r)) r with hΨ
  have hform : ∀ (m : Set.Ici (1 : ℕ)) (k : ℕ), k ≤ ℓ → ∀ r : ℝ,
      iteratedDeriv k (Ψ m) r
        = iteratedDeriv k (fun r : ℝ => aCoeff S m (realIncl r)) r * dirichletTerm m.1 τ
          + (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ) * dirichletTerm m.1 τ)
            * iteratedDeriv k (fun r : ℝ => bCoeff S m (realIncl r)) r := by
    intro m k hk r
    have hcdA : ContDiff ℝ ℓ (fun r : ℝ => aCoeff S m (realIncl r)) :=
      contDiff_of_differentiable_iteratedDeriv (fun i hi => fun y =>
        ((hA m).2.2 i (by have h : i ≤ ℓ := WithTop.coe_le_coe.mp hi; omega) y).differentiableAt)
    have hcdB : ContDiff ℝ ℓ (fun r : ℝ => bCoeff S m (realIncl r)) :=
      contDiff_of_differentiable_iteratedDeriv (fun i hi => fun y =>
        ((hB m).2.2 i (by have h : i ≤ ℓ := WithTop.coe_le_coe.mp hi; omega) y).differentiableAt)
    have hkA : ContDiffAt ℝ (k : ℕ∞) (fun r : ℝ => aCoeff S m (realIncl r)) r :=
      (hcdA.contDiffAt).of_le (by exact_mod_cast hk)
    have hkB : ContDiffAt ℝ (k : ℕ∞) (fun r : ℝ => bCoeff S m (realIncl r)) r :=
      (hcdB.contDiffAt).of_le (by exact_mod_cast hk)
    have hfun : Ψ m = fun r : ℝ => dirichletTerm m.1 τ * aCoeff S m (realIncl r)
        + (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ) * dirichletTerm m.1 τ)
          * bCoeff S m (realIncl r) := by
      funext y; simp only [hΨ]; ring
    rw [hfun]
    change iteratedDeriv k ((fun r : ℝ => dirichletTerm m.1 τ * aCoeff S m (realIncl r))
        + (fun r : ℝ => (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ) * dirichletTerm m.1 τ)
            * bCoeff S m (realIncl r))) r = _
    rw [iteratedDeriv_add
      ((contDiffAt_const (x := r) (c := dirichletTerm m.1 τ)).mul hkA)
      ((contDiffAt_const (x := r) (c := _)).mul hkB),
      iteratedDeriv_const_mul _ hkA, iteratedDeriv_const_mul _ hkB]
    ring
  have hder : ∀ (m : Set.Ici (1 : ℕ)) (k : ℕ), k < ℓ → ∀ r : ℝ,
      HasDerivAt (fun r : ℝ => iteratedDeriv k (Ψ m) r) (iteratedDeriv (k+1) (Ψ m) r) r := by
    intro m k hk r
    have h1 : (fun r : ℝ => iteratedDeriv k (Ψ m) r)
        = fun r : ℝ => iteratedDeriv k (fun r : ℝ => aCoeff S m (realIncl r)) r * dirichletTerm m.1 τ
            + (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ) * dirichletTerm m.1 τ)
              * iteratedDeriv k (fun r : ℝ => bCoeff S m (realIncl r)) r :=
      funext (fun y => hform m k (le_of_lt hk) y)
    have h2 := hform m (k+1) (by omega) r
    rw [h1, h2]
    exact (((hA m).2.2 k (by omega) r).mul_const _).add (((hB m).2.2 k (by omega) r).const_mul _)
  have hpoint : ∀ r : ℝ, (∑' m : Set.Ici (1 : ℕ), Ψ m r) = S.F τ (realIncl r) := by
    intro r
    have hs1 : Summable (fun m : Set.Ici (1 : ℕ) =>
        aCoeff S m (realIncl r) * dirichletTerm m.1 τ) := by
      refine summable_mul_dirichletTerm (N := Nat.ceil (growthData S 0).2.1)
        (poly_const_nonneg (growthData S) (growthData_nonneg S) 0)
        (c := fun m => aCoeff S m (realIncl r)) (fun m => ?_) τ hτ
      refine le_trans (by simpa using (hA m).2.1 0 (by omega) r) ?_
      exact Cker_le_poly (growthData_nonneg S) 0 m.1
    have hs2 : Summable (fun m : Set.Ici (1 : ℕ) =>
        (2 * (Real.pi : ℂ) * Complex.I * τ)
          * ((rate m.1 : ℂ) * bCoeff S m (realIncl r) * dirichletTerm m.1 τ)) := by
      refine (summable_rate_mul_dirichletTerm (N := Nat.ceil (growthData S 0).2.1)
        (poly_const_nonneg (growthData S) (growthData_nonneg S) 0)
        (c := fun m => bCoeff S m (realIncl r)) (fun m => ?_) τ hτ).mul_left _
      refine le_trans (by simpa using (hB m).2.1 0 (by omega) r) ?_
      exact Cker_le_poly (growthData_nonneg S) 0 m.1
    rw [show (fun m : Set.Ici (1 : ℕ) => Ψ m r) = fun m : Set.Ici (1 : ℕ) =>
        aCoeff S m (realIncl r) * dirichletTerm m.1 τ
        + (2 * (Real.pi : ℂ) * Complex.I * τ)
          * ((rate m.1 : ℂ) * bCoeff S m (realIncl r) * dirichletTerm m.1 τ) from
      funext (fun m => by simp only [hΨ]; ring)]
    rw [Summable.tsum_add hs1 hs2, tsum_mul_left]
    exact (expansion_F_pointwise S τ hτ (realIncl r)).symm
  have hbound : ∀ (m : Set.Ici (1 : ℕ)) (k : ℕ), k ≤ ℓ → ∀ y : ℝ,
      ‖iteratedDeriv k (Ψ m) y‖ ≤ vSeq S τ k m := by
    intro m k hk y
    have hkA : ‖iteratedDeriv k (fun r : ℝ => aCoeff S m (realIncl r)) y‖
        ≤ Cker (growthData S) k m.1 := (hA m).2.1 k (by omega) y
    have hkB : ‖iteratedDeriv k (fun r : ℝ => bCoeff S m (realIncl r)) y‖
        ≤ Cker (growthData S) k m.1 := (hB m).2.1 k (by omega) y
    rw [hform m k hk y]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · rw [norm_mul]
      calc ‖iteratedDeriv k (fun r : ℝ => aCoeff S m (realIncl r)) y‖ * ‖dirichletTerm m.1 τ‖
          ≤ Cker (growthData S) k m.1 * ‖dirichletTerm m.1 τ‖ :=
            mul_le_mul_of_nonneg_right hkA (norm_nonneg _)
        _ = ‖dirichletTerm m.1 τ‖ * Cker (growthData S) k m.1 := by ring
    · rw [norm_mul]
      have hnormeq : ‖2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ) * dirichletTerm m.1 τ‖
          = ‖(rate m.1 : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I * τ) * dirichletTerm m.1 τ)‖ := by
        rw [show 2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ) * dirichletTerm m.1 τ
            = (rate m.1 : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I * τ) * dirichletTerm m.1 τ)
            from by ring]
      rw [hnormeq]
      exact mul_le_mul_of_nonneg_left hkB (norm_nonneg _)
  have hmain : ∀ k : ℕ, k ≤ ℓ →
      iteratedDeriv k (fun r : ℝ => ∑' m : Set.Ici (1 : ℕ), Ψ m r)
        = fun r : ℝ => ∑' m : Set.Ici (1 : ℕ), iteratedDeriv k (Ψ m) r := by
    intro k
    induction k with
    | zero =>
      intro _
      funext r
      simp only [iteratedDeriv_zero]
    | succ k ih =>
      intro hk
      have hk' : k < ℓ := by omega
      rw [iteratedDeriv_succ, ih (by omega)]
      funext r
      have hv : Summable (fun m : Set.Ici (1 : ℕ) => vSeq S τ (k+1) m) := summable_vSeq S (k+1) τ hτ
      have hv0 : Summable (fun m : Set.Ici (1 : ℕ) => iteratedDeriv k (Ψ m) r) :=
        (summable_vSeq S k τ hτ).of_norm_bounded (fun m => hbound m k (by omega) r)
      exact (hasDerivAt_tsum hv (fun m y => hder m k hk' y)
        (fun m y => hbound m (k+1) (by omega) y) hv0 r).deriv
  intro r
  have hΦ : (fun r : ℝ => S.F τ (realIncl r)) = fun r : ℝ => ∑' m : Set.Ici (1 : ℕ), Ψ m r :=
    funext (fun y => (hpoint y).symm)
  rw [hΦ, congrFun (hmain ℓ le_rfl) r]
  rw [show (fun m : Set.Ici (1 : ℕ) => iteratedDeriv ℓ (Ψ m) r) = fun m : Set.Ici (1 : ℕ) =>
      iteratedDeriv ℓ (fun r : ℝ => aCoeff S m (realIncl r)) r * dirichletTerm m.1 τ
      + (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ) * dirichletTerm m.1 τ)
        * iteratedDeriv ℓ (fun r : ℝ => bCoeff S m (realIncl r)) r from
    funext (fun m => hform m ℓ le_rfl r)]
  have hs1 : Summable (fun m : Set.Ici (1 : ℕ) =>
      iteratedDeriv ℓ (fun r : ℝ => aCoeff S m (realIncl r)) r * dirichletTerm m.1 τ) := by
    refine summable_mul_dirichletTerm (N := Nat.ceil (growthData S ℓ).2.1)
      (poly_const_nonneg (growthData S) (growthData_nonneg S) ℓ)
      (c := fun m => iteratedDeriv ℓ (fun r : ℝ => aCoeff S m (realIncl r)) r) (fun m => ?_) τ hτ
    exact le_trans ((hA m).2.1 ℓ (by omega) r) (Cker_le_poly (growthData_nonneg S) ℓ m.1)
  have hs2 : Summable (fun m : Set.Ici (1 : ℕ) =>
      (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ) * dirichletTerm m.1 τ)
        * iteratedDeriv ℓ (fun r : ℝ => bCoeff S m (realIncl r)) r) := by
    have hc : ∀ m : Set.Ici (1 : ℕ),
        ‖iteratedDeriv ℓ (fun r : ℝ => bCoeff S m (realIncl r)) r‖
          ≤ 6 * Real.exp (2 * Real.pi)
              * ((growthData S ℓ).1 + (growthData S ℓ).2.2.1 * 3 ^ ((growthData S ℓ).2.2.2))
              * ((m.1 : ℝ) + 1) ^ (Nat.ceil (growthData S ℓ).2.1) :=
      fun m => le_trans ((hB m).2.1 ℓ (by omega) r) (Cker_le_poly (growthData_nonneg S) ℓ m.1)
    have h0 := summable_rate_mul_dirichletTerm (N := Nat.ceil (growthData S ℓ).2.1)
      (poly_const_nonneg (growthData S) (growthData_nonneg S) ℓ)
      (c := fun m => iteratedDeriv ℓ (fun r : ℝ => bCoeff S m (realIncl r)) r) hc τ hτ
    exact (h0.mul_left (2 * (Real.pi : ℂ) * Complex.I * τ)).congr (fun m => by ring)
  rw [Summable.tsum_add hs1 hs2]
  rw [show (fun m : Set.Ici (1 : ℕ) => (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ)
        * dirichletTerm m.1 τ) * iteratedDeriv ℓ (fun r : ℝ => bCoeff S m (realIncl r)) r)
      = fun m : Set.Ici (1 : ℕ) => (2 * (Real.pi : ℂ) * Complex.I * τ)
          * ((rate m.1 : ℂ) * iteratedDeriv ℓ (fun r : ℝ => bCoeff S m (realIncl r)) r
              * dirichletTerm m.1 τ) from funext (fun m => by ring)]
  rw [tsum_mul_left]


/-- **Termwise radial differentiation of the expansion of `F̃`.** -/
lemma expansion_Ftilde_deriv {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (ℓ : ℕ) (τ : ℂ) (hτ : 0 < τ.im) :
    ∀ r : ℝ, iteratedDeriv ℓ (fun r : ℝ => S.Ftilde τ (realIncl r)) r =
      (∑' m : Set.Ici (1 : ℕ),
          iteratedDeriv ℓ (fun r : ℝ => aTildeCoeff S m (realIncl r)) r * dirichletTerm m.1 τ)
      + (2 * (Real.pi : ℂ) * Complex.I * τ)
        * ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ)
            * iteratedDeriv ℓ (fun r : ℝ => bTildeCoeff S m (realIncl r)) r * dirichletTerm m.1 τ := by
  have hA := fun m : Set.Ici (1 : ℕ) => facts_aTildeCoeff S (ℓ + 1) m
  have hB := fun m : Set.Ici (1 : ℕ) => facts_bTildeCoeff S (ℓ + 1) m
  set Ψ : Set.Ici (1 : ℕ) → ℝ → ℂ := fun m r =>
      (fun r : ℝ => aTildeCoeff S m (realIncl r)) r * dirichletTerm m.1 τ
      + (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ) * dirichletTerm m.1 τ)
        * (fun r : ℝ => bTildeCoeff S m (realIncl r)) r with hΨ
  have hform : ∀ (m : Set.Ici (1 : ℕ)) (k : ℕ), k ≤ ℓ → ∀ r : ℝ,
      iteratedDeriv k (Ψ m) r
        = iteratedDeriv k (fun r : ℝ => aTildeCoeff S m (realIncl r)) r * dirichletTerm m.1 τ
          + (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ) * dirichletTerm m.1 τ)
            * iteratedDeriv k (fun r : ℝ => bTildeCoeff S m (realIncl r)) r := by
    intro m k hk r
    have hcdA : ContDiff ℝ ℓ (fun r : ℝ => aTildeCoeff S m (realIncl r)) :=
      contDiff_of_differentiable_iteratedDeriv (fun i hi => fun y =>
        ((hA m).2.2 i (by have h : i ≤ ℓ := WithTop.coe_le_coe.mp hi; omega) y).differentiableAt)
    have hcdB : ContDiff ℝ ℓ (fun r : ℝ => bTildeCoeff S m (realIncl r)) :=
      contDiff_of_differentiable_iteratedDeriv (fun i hi => fun y =>
        ((hB m).2.2 i (by have h : i ≤ ℓ := WithTop.coe_le_coe.mp hi; omega) y).differentiableAt)
    have hkA : ContDiffAt ℝ (k : ℕ∞) (fun r : ℝ => aTildeCoeff S m (realIncl r)) r :=
      (hcdA.contDiffAt).of_le (by exact_mod_cast hk)
    have hkB : ContDiffAt ℝ (k : ℕ∞) (fun r : ℝ => bTildeCoeff S m (realIncl r)) r :=
      (hcdB.contDiffAt).of_le (by exact_mod_cast hk)
    have hfun : Ψ m = fun r : ℝ => dirichletTerm m.1 τ * aTildeCoeff S m (realIncl r)
        + (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ) * dirichletTerm m.1 τ)
          * bTildeCoeff S m (realIncl r) := by
      funext y; simp only [hΨ]; ring
    rw [hfun]
    change iteratedDeriv k ((fun r : ℝ => dirichletTerm m.1 τ * aTildeCoeff S m (realIncl r))
        + (fun r : ℝ => (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ) * dirichletTerm m.1 τ)
            * bTildeCoeff S m (realIncl r))) r = _
    rw [iteratedDeriv_add
      ((contDiffAt_const (x := r) (c := dirichletTerm m.1 τ)).mul hkA)
      ((contDiffAt_const (x := r) (c := _)).mul hkB),
      iteratedDeriv_const_mul _ hkA, iteratedDeriv_const_mul _ hkB]
    ring
  have hder : ∀ (m : Set.Ici (1 : ℕ)) (k : ℕ), k < ℓ → ∀ r : ℝ,
      HasDerivAt (fun r : ℝ => iteratedDeriv k (Ψ m) r) (iteratedDeriv (k+1) (Ψ m) r) r := by
    intro m k hk r
    have h1 : (fun r : ℝ => iteratedDeriv k (Ψ m) r)
        = fun r : ℝ => iteratedDeriv k (fun r : ℝ => aTildeCoeff S m (realIncl r)) r * dirichletTerm m.1 τ
            + (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ) * dirichletTerm m.1 τ)
              * iteratedDeriv k (fun r : ℝ => bTildeCoeff S m (realIncl r)) r :=
      funext (fun y => hform m k (le_of_lt hk) y)
    have h2 := hform m (k+1) (by omega) r
    rw [h1, h2]
    exact (((hA m).2.2 k (by omega) r).mul_const _).add (((hB m).2.2 k (by omega) r).const_mul _)
  have hpoint : ∀ r : ℝ, (∑' m : Set.Ici (1 : ℕ), Ψ m r) = S.Ftilde τ (realIncl r) := by
    intro r
    have hs1 : Summable (fun m : Set.Ici (1 : ℕ) =>
        aTildeCoeff S m (realIncl r) * dirichletTerm m.1 τ) := by
      refine summable_mul_dirichletTerm (N := Nat.ceil (growthDataT S 0).2.1)
        (poly_const_nonneg (growthDataT S) (growthDataT_nonneg S) 0)
        (c := fun m => aTildeCoeff S m (realIncl r)) (fun m => ?_) τ hτ
      refine le_trans (by simpa using (hA m).2.1 0 (by omega) r) ?_
      exact Cker_le_poly (growthDataT_nonneg S) 0 m.1
    have hs2 : Summable (fun m : Set.Ici (1 : ℕ) =>
        (2 * (Real.pi : ℂ) * Complex.I * τ)
          * ((rate m.1 : ℂ) * bTildeCoeff S m (realIncl r) * dirichletTerm m.1 τ)) := by
      refine (summable_rate_mul_dirichletTerm (N := Nat.ceil (growthDataT S 0).2.1)
        (poly_const_nonneg (growthDataT S) (growthDataT_nonneg S) 0)
        (c := fun m => bTildeCoeff S m (realIncl r)) (fun m => ?_) τ hτ).mul_left _
      refine le_trans (by simpa using (hB m).2.1 0 (by omega) r) ?_
      exact Cker_le_poly (growthDataT_nonneg S) 0 m.1
    rw [show (fun m : Set.Ici (1 : ℕ) => Ψ m r) = fun m : Set.Ici (1 : ℕ) =>
        aTildeCoeff S m (realIncl r) * dirichletTerm m.1 τ
        + (2 * (Real.pi : ℂ) * Complex.I * τ)
          * ((rate m.1 : ℂ) * bTildeCoeff S m (realIncl r) * dirichletTerm m.1 τ) from
      funext (fun m => by simp only [hΨ]; ring)]
    rw [Summable.tsum_add hs1 hs2, tsum_mul_left]
    exact (expansion_Ftilde_pointwise S τ hτ (realIncl r)).symm
  have hbound : ∀ (m : Set.Ici (1 : ℕ)) (k : ℕ), k ≤ ℓ → ∀ y : ℝ,
      ‖iteratedDeriv k (Ψ m) y‖ ≤ vSeqT S τ k m := by
    intro m k hk y
    have hkA : ‖iteratedDeriv k (fun r : ℝ => aTildeCoeff S m (realIncl r)) y‖
        ≤ Cker (growthDataT S) k m.1 := (hA m).2.1 k (by omega) y
    have hkB : ‖iteratedDeriv k (fun r : ℝ => bTildeCoeff S m (realIncl r)) y‖
        ≤ Cker (growthDataT S) k m.1 := (hB m).2.1 k (by omega) y
    rw [hform m k hk y]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · rw [norm_mul]
      calc ‖iteratedDeriv k (fun r : ℝ => aTildeCoeff S m (realIncl r)) y‖ * ‖dirichletTerm m.1 τ‖
          ≤ Cker (growthDataT S) k m.1 * ‖dirichletTerm m.1 τ‖ :=
            mul_le_mul_of_nonneg_right hkA (norm_nonneg _)
        _ = ‖dirichletTerm m.1 τ‖ * Cker (growthDataT S) k m.1 := by ring
    · rw [norm_mul]
      have hnormeq : ‖2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ) * dirichletTerm m.1 τ‖
          = ‖(rate m.1 : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I * τ) * dirichletTerm m.1 τ)‖ := by
        rw [show 2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ) * dirichletTerm m.1 τ
            = (rate m.1 : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I * τ) * dirichletTerm m.1 τ)
            from by ring]
      rw [hnormeq]
      exact mul_le_mul_of_nonneg_left hkB (norm_nonneg _)
  have hmain : ∀ k : ℕ, k ≤ ℓ →
      iteratedDeriv k (fun r : ℝ => ∑' m : Set.Ici (1 : ℕ), Ψ m r)
        = fun r : ℝ => ∑' m : Set.Ici (1 : ℕ), iteratedDeriv k (Ψ m) r := by
    intro k
    induction k with
    | zero =>
      intro _
      funext r
      simp only [iteratedDeriv_zero]
    | succ k ih =>
      intro hk
      have hk' : k < ℓ := by omega
      rw [iteratedDeriv_succ, ih (by omega)]
      funext r
      have hv : Summable (fun m : Set.Ici (1 : ℕ) => vSeqT S τ (k+1) m) := summable_vSeqT S (k+1) τ hτ
      have hv0 : Summable (fun m : Set.Ici (1 : ℕ) => iteratedDeriv k (Ψ m) r) :=
        (summable_vSeqT S k τ hτ).of_norm_bounded (fun m => hbound m k (by omega) r)
      exact (hasDerivAt_tsum hv (fun m y => hder m k hk' y)
        (fun m y => hbound m (k+1) (by omega) y) hv0 r).deriv
  intro r
  have hΦ : (fun r : ℝ => S.Ftilde τ (realIncl r)) = fun r : ℝ => ∑' m : Set.Ici (1 : ℕ), Ψ m r :=
    funext (fun y => (hpoint y).symm)
  rw [hΦ, congrFun (hmain ℓ le_rfl) r]
  rw [show (fun m : Set.Ici (1 : ℕ) => iteratedDeriv ℓ (Ψ m) r) = fun m : Set.Ici (1 : ℕ) =>
      iteratedDeriv ℓ (fun r : ℝ => aTildeCoeff S m (realIncl r)) r * dirichletTerm m.1 τ
      + (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ) * dirichletTerm m.1 τ)
        * iteratedDeriv ℓ (fun r : ℝ => bTildeCoeff S m (realIncl r)) r from
    funext (fun m => hform m ℓ le_rfl r)]
  have hs1 : Summable (fun m : Set.Ici (1 : ℕ) =>
      iteratedDeriv ℓ (fun r : ℝ => aTildeCoeff S m (realIncl r)) r * dirichletTerm m.1 τ) := by
    refine summable_mul_dirichletTerm (N := Nat.ceil (growthDataT S ℓ).2.1)
      (poly_const_nonneg (growthDataT S) (growthDataT_nonneg S) ℓ)
      (c := fun m => iteratedDeriv ℓ (fun r : ℝ => aTildeCoeff S m (realIncl r)) r) (fun m => ?_) τ hτ
    exact le_trans ((hA m).2.1 ℓ (by omega) r) (Cker_le_poly (growthDataT_nonneg S) ℓ m.1)
  have hs2 : Summable (fun m : Set.Ici (1 : ℕ) =>
      (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ) * dirichletTerm m.1 τ)
        * iteratedDeriv ℓ (fun r : ℝ => bTildeCoeff S m (realIncl r)) r) := by
    have hc : ∀ m : Set.Ici (1 : ℕ),
        ‖iteratedDeriv ℓ (fun r : ℝ => bTildeCoeff S m (realIncl r)) r‖
          ≤ 6 * Real.exp (2 * Real.pi)
              * ((growthDataT S ℓ).1 + (growthDataT S ℓ).2.2.1 * 3 ^ ((growthDataT S ℓ).2.2.2))
              * ((m.1 : ℝ) + 1) ^ (Nat.ceil (growthDataT S ℓ).2.1) :=
      fun m => le_trans ((hB m).2.1 ℓ (by omega) r) (Cker_le_poly (growthDataT_nonneg S) ℓ m.1)
    have h0 := summable_rate_mul_dirichletTerm (N := Nat.ceil (growthDataT S ℓ).2.1)
      (poly_const_nonneg (growthDataT S) (growthDataT_nonneg S) ℓ)
      (c := fun m => iteratedDeriv ℓ (fun r : ℝ => bTildeCoeff S m (realIncl r)) r) hc τ hτ
    exact (h0.mul_left (2 * (Real.pi : ℂ) * Complex.I * τ)).congr (fun m => by ring)
  rw [Summable.tsum_add hs1 hs2]
  rw [show (fun m : Set.Ici (1 : ℕ) => (2 * (Real.pi : ℂ) * Complex.I * τ * (rate m.1 : ℂ)
        * dirichletTerm m.1 τ) * iteratedDeriv ℓ (fun r : ℝ => bTildeCoeff S m (realIncl r)) r)
      = fun m : Set.Ici (1 : ℕ) => (2 * (Real.pi : ℂ) * Complex.I * τ)
          * ((rate m.1 : ℂ) * iteratedDeriv ℓ (fun r : ℝ => bTildeCoeff S m (realIncl r)) r
              * dirichletTerm m.1 τ) from funext (fun m => by ring)]
  rw [tsum_mul_left]


end

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

theorem FunctionDerivExpansion {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) :
    (∀ (ℓ : ℕ) (τ : ℂ) (x : E n), 0 < τ.im →
      radialDeriv ℓ (S.F τ) x =
        (∑' m : Set.Ici (1 : ℕ), radialDeriv ℓ (aCoeff S m) x * dirichletTerm m.1 τ)
        + (2 * (Real.pi : ℂ) * Complex.I * τ)
          * ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * radialDeriv ℓ (bCoeff S m) x
              * dirichletTerm m.1 τ) ∧
    (∀ (ℓ : ℕ) (τ : ℂ) (x : E n), 0 < τ.im →
      radialDeriv ℓ (S.Ftilde τ) x =
        (∑' m : Set.Ici (1 : ℕ), radialDeriv ℓ (aTildeCoeff S m) x * dirichletTerm m.1 τ)
        + (2 * (Real.pi : ℂ) * Complex.I * τ)
          * ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * radialDeriv ℓ (bTildeCoeff S m) x
              * dirichletTerm m.1 τ) := by
  refine ⟨fun ℓ τ x hτ => ?_, fun ℓ τ x hτ => ?_⟩
  · simpa only [radialDeriv] using expansion_F_deriv S ℓ τ hτ ‖x‖
  · simpa only [radialDeriv] using expansion_Ftilde_deriv S ℓ τ hτ ‖x‖

end Work.FunctionalEquations
