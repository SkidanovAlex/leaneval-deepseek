import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.B3.Recon
import Submission.Work.Diff.STE.B3.dens_lower_bound
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.B3.fourierCoeff_periodization
import Submission.Work.Diff.STE.flat.fourierCoeff_seriesFun
import Submission.Work.Diff.STE.flat.hasDerivWithinAt_seriesFunM
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.Lead.Rper_contDiff
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.Lead.bil_apply_eq_sum_R
import Submission.Work.Diff.STE.Lead.normCoeffSubLe

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

open Filter MeasureTheory
open scoped BigOperators Topology

set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

noncomputable section

/-- **The Fourier-coefficient family of the pointwise value `h x u v`, read off from the chart
`i`.**  Fourier inversion of the localised component `R i h a b` gives `R i h a b z` as the series
`Σ_μ ĉ_μ(Rper i h a b) · e_μ(z)`; the reconstruction `R = ψ · √dens · mat` turns
`h x u v = Σ_ab mat i h a b z · ⟨u,e i a⟩ · ⟨v,e i b⟩` into a series in which the `(a,b)`-term is
contracted with the coefficients of `u` and `v` in the `g₀`-orthonormal frame `e i`, and normalised
by the factor `(ζ i x · √(dens i z))⁻¹`.  Summing over `(a,b)` gives the coefficient family of the
*pointwise* value `h x u v`. -/
def bilCoeff (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) (x : M)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (u v : TangentSpace I x) :
    (Fin (Module.finrank ℝ E) → ℤ) → ℂ :=
  fun μ =>
    (((D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹ : ℝ) : ℂ)
      * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
            * Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ

/-- **`ℓ¹`-summability of the Fourier coefficients of a localised component of a chart-smooth
section.**  `Rper i h a b` is `C^∞` and `1`-periodic (`Rper_contDiff_and_periodic`), so its
weighted coefficients are summable (`summable_weighted_fourierCoeff_of_contDiff`) for a weight of
Sobolev order exceeding `n/2`, whence its coefficients are absolutely summable
(`summable_norm_of_CSq`). -/
lemma summable_fourierCoeff_Rper
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    Summable (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
      Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ) := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : ℕ, Fintype.card (Fin (Module.finrank ℝ E)) < 2 * s :=
    ⟨Module.finrank ℝ E + 1, by rw [Fintype.card_fin]; omega⟩
  have hcd := Work.Diff.STE.Lead.Rper_contDiff_and_periodic D h hh i a b
  refine Summable.of_norm ?_
  exact Work.Diff.STE.summable_norm_of_CSq s hs _
    (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff _ hcd.1 hcd.2 s)

/-- **Term-by-term differentiation of a finite sum of curves.** -/
lemma hasDerivWithinAt_sum_fun {ι : Type*} [Fintype ι] {s : Set ℝ} {x : ℝ}
    {f : ι → ℝ → ℂ} {g : ι → ℂ}
    (h : ∀ i, HasDerivWithinAt (f i) (g i) s x) :
    HasDerivWithinAt (fun y : ℝ => ∑ i, f i y) (∑ i, g i) s x :=
  (HasDerivWithinAt.sum (u := Finset.univ) (A := f) (A' := g)
    (fun i _ => h i)).congr (fun y _ => (Finset.sum_apply y Finset.univ f).symm)
    (Finset.sum_apply x Finset.univ f).symm

/-- **The value of the Fourier series of `bilCoeff` is the pointwise value of `h`.**  This is the
reconstruction step of the coefficient-to-pointwise passage: for a chart-smooth section `h` and a
point `x` at which the chart `i` is genuine (`ζ i x ≠ 0`), the series with the coefficients
`bilCoeff D i x h u v` converges to `h x u v`. -/
lemma seriesFun_bilCoeff
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) (x : M)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (u v : TangentSpace I x)
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (hz : D.ζ i x ≠ 0) :
    Work.Diff.STE.seriesFun (bilCoeff D i x h u v)
        (Work.Diff.STE.coord (I := I) (D.x₀ i) x) = ((h x u v : ℝ) : ℂ) := by
  classical
  obtain ⟨hsrc, hlt⟩ := D.hζsupp i x hz
  have hσ2 : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) x‖ < (1 / 2 : ℝ) := by
    have h1 := D.hσ i
    have h2 := D.hσ2 i
    linarith
  have hcoord : ∀ j : Fin (Module.finrank ℝ E),
      Work.Diff.STE.coord (I := I) (D.x₀ i) x j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    intro j
    have h1 : |Work.Diff.STE.coord (I := I) (D.x₀ i) x j|
        ≤ ‖Work.Diff.STE.coord (I := I) (D.x₀ i) x‖ := by
      simpa only [Real.norm_eq_abs] using
        norm_le_pi_norm (Work.Diff.STE.coord (I := I) (D.x₀ i) x) j
    exact abs_lt.mp (lt_of_le_of_lt h1 hσ2)
  -- the pointwise reconstruction of `h` from its localised components
  have hrec : h x u v
      = (D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹
        * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            D.R i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
              * g₀.inner x u (D.e i a x) * g₀.inner x v (D.e i b x)) :=
    bil_apply_eq_sum_R D i x h hz u v
  -- `ℓ¹`-summability of the coefficients, and of the terms of the series
  have hsum : ∀ a b : Fin (Module.finrank ℝ E),
      Summable (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
        Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ) :=
    fun a b => summable_fourierCoeff_Rper D h hh i a b
  have hsumE : ∀ a b : Fin (Module.finrank ℝ E),
      Summable (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
        Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ
          * Work.Diff.STE.fourierExp μ (Work.Diff.STE.coord (I := I) (D.x₀ i) x)) := by
    intro a b
    refine Summable.of_norm ?_
    simpa only [norm_mul, Work.Diff.STE.flat.norm_fourierExp_char, mul_one] using (hsum a b).norm
  -- Fourier inversion of the localised component at the point
  have hinv : ∀ a b : Fin (Module.finrank ℝ E),
      (∑' μ : Fin (Module.finrank ℝ E) → ℤ,
          Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ
            * Work.Diff.STE.fourierExp μ (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
        = ((D.R i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x) : ℝ) : ℂ) := by
    intro a b
    have hcd := Work.Diff.STE.Lead.Rper_contDiff_and_periodic D h hh i a b
    change Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff (D.Rper i h a b))
      (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
      = ((D.R i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x) : ℝ) : ℂ)
    rw [Work.Diff.STE.flat.seriesFun_fourierCoeff (D.Rper i h a b) hcd.1 hcd.2
      (Work.Diff.STE.coord (I := I) (D.x₀ i) x), D.Rper_eq_R i h a b hcoord]
  -- the term of the series, with the Fourier character moved inside the finite sums
  have hterm : ∀ μ : Fin (Module.finrank ℝ E) → ℤ,
      bilCoeff D i x h u v μ * Work.Diff.STE.fourierExp μ (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
      = (((D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹ : ℝ) : ℂ)
        * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
              * (Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ
                  * Work.Diff.STE.fourierExp μ (Work.Diff.STE.coord (I := I) (D.x₀ i) x)) := by
    intro μ
    simp only [bilCoeff]
    rw [show ((((D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹
            : ℝ) : ℂ)
          * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
                * Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ)
          * Work.Diff.STE.fourierExp μ (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
        = (((D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹
            : ℝ) : ℂ)
          * ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
                * Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ)
              * Work.Diff.STE.fourierExp μ (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
        from by ring]
    congr 1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  -- summability of the (already contracted) inner families
  have hsum2 : ∀ a : Fin (Module.finrank ℝ E),
      Summable (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
        ∑ b : Fin (Module.finrank ℝ E),
          (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
            * (Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ
                * Work.Diff.STE.fourierExp μ (Work.Diff.STE.coord (I := I) (D.x₀ i) x))) := by
    intro a
    refine summable_sum (s := Finset.univ) (fun b _ => ?_)
    exact Summable.mul_left _ (hsumE a b)
  -- interchange `Σ_μ` with the finite sums over `(a,b)`
  have hswap : (∑' μ : Fin (Module.finrank ℝ E) → ℤ, ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
            * (Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ
                * Work.Diff.STE.fourierExp μ (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))
      = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          ∑' μ : Fin (Module.finrank ℝ E) → ℤ,
            (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
              * (Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ
                  * Work.Diff.STE.fourierExp μ (Work.Diff.STE.coord (I := I) (D.x₀ i) x)) := by
    have h1 : HasSum (fun μ : Fin (Module.finrank ℝ E) → ℤ => ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
              * (Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ
                  * Work.Diff.STE.fourierExp μ (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          ∑' μ : Fin (Module.finrank ℝ E) → ℤ,
            (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
              * (Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ
                  * Work.Diff.STE.fourierExp μ (Work.Diff.STE.coord (I := I) (D.x₀ i) x))) := by
      refine hasSum_sum (s := Finset.univ) (fun a _ => ?_)
      refine hasSum_sum (s := Finset.univ) (fun b _ => ?_)
      exact (Summable.mul_left _ (hsumE a b)).hasSum
    exact h1.tsum_eq
  -- pull the constant out of each `Σ_μ`
  have hstep2 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ∑' μ : Fin (Module.finrank ℝ E) → ℤ,
          (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
            * (Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ
                * Work.Diff.STE.fourierExp μ (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))
      = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
            * (∑' μ : Fin (Module.finrank ℝ E) → ℤ,
                Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ
                  * Work.Diff.STE.fourierExp μ (Work.Diff.STE.coord (I := I) (D.x₀ i) x)) := by
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    exact Summable.tsum_mul_left _ (hsumE a b)
  -- identify each `Σ_μ` with the localised component
  have hstep3 : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
          * (∑' μ : Fin (Module.finrank ℝ E) → ℤ,
              Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ
                * Work.Diff.STE.fourierExp μ (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))
      = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
            * ((D.R i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hinv a b]
  -- the final bookkeeping of the casts and of the normalisation
  have hfinal : (((D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹
          : ℝ) : ℂ)
        * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
              * ((D.R i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x) : ℝ) : ℂ))
      = ((h x u v : ℝ) : ℂ) := by
    have hcast : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
            * ((D.R i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x) : ℝ) : ℂ))
        = ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            D.R i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
              * g₀.inner x u (D.e i a x) * g₀.inner x v (D.e i b x) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Complex.ofReal_mul, Complex.ofReal_mul]
      ring
    rw [hcast, ← Complex.ofReal_mul, hrec]
  rw [Work.Diff.STE.seriesFun, tsum_congr hterm,
    Summable.tsum_mul_left _ (summable_sum (s := Finset.univ) (fun a _ => hsum2 a)),
    hswap, hstep2, hstep3]
  exact hfinal

/-- From the coefficient equation to the pointwise equation (the reconstruction step). U has
uniformly rapidly decaying Fourier coefficients, W has uniformly summable coefficients, the
coefficients of U are differentiable with derivative the corresponding coefficient of W, and each
component of W is continuous in the parameter. Then every matrix coefficient of U is differentiable
within Ico 0 tau0 with derivative the corresponding matrix coefficient of W. -/
theorem pointwise_hasDerivWithinAt_of_coeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (τ₀ : ℝ) (hτ₀ : 0 < τ₀)
    (U W : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hsmU : ∀ t : ℝ, Work.Diff.STE.D.ChartData (I := I) (M := M) (U t))
    (hsmW : ∀ t : ℝ, Work.Diff.STE.D.ChartData (I := I) (M := M) (W t))
    (hdecU : ∀ M₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) τ₀,
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖ * (Work.Diff.STE.wt μ) ^ M₀ ≤ C)
    (hWsum : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ∃ g : (Fin (Module.finrank ℝ E) → ℤ) → ℝ, Summable g ∧ ∀ t ∈ Set.Ico (0 : ℝ) τ₀,
        ∀ μ : Fin (Module.finrank ℝ E) → ℤ,
        ‖Work.Diff.STE.fourierCoeff (D.Rper i (W t) a b) μ‖ ≤ g μ)
    (hcoeff : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) τ₀ → ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ),
      HasDerivWithinAt (fun s : ℝ => Work.Diff.STE.fourierCoeff (D.Rper i (U s) a b) μ)
        (Work.Diff.STE.fourierCoeff (D.Rper i (W t) a b) μ) (Set.Ico (0 : ℝ) τ₀) t)
    (hWcont : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) τ₀ → ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (z : Fin (Module.finrank ℝ E) → ℝ),
      ContinuousWithinAt (fun σ : ℝ => D.R i (W σ) a b z) (Set.Ico (0 : ℝ) τ₀) t) :
    ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) τ₀ → ∀ (x : M) (u v : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (U s) x u v) ((W t) x u v) (Set.Ico (0 : ℝ) τ₀) t := by
  intro t ht x u v
  -- a chart whose normalised weight does not vanish at `x`
  have hex : ∃ i : ι₀, D.ζ i x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hsum : (∑ i : ι₀, (D.ζ i x) ^ 2) = 0 :=
      Finset.sum_eq_zero (fun i _ => by rw [hcon i]; ring)
    rw [D.hζsq x] at hsum
    exact one_ne_zero hsum
  obtain ⟨i, hzi⟩ := hex
  -- the per-`(a,b)` summable majorants of the coefficients of `W`
  have hpick : ∀ a b : Fin (Module.finrank ℝ E),
      ∃ g : (Fin (Module.finrank ℝ E) → ℤ) → ℝ,
        Summable g ∧ (∀ μ, 0 ≤ g μ) ∧ ∀ σ ∈ Set.Ico (0 : ℝ) τ₀, ∀ μ,
          ‖Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ‖ ≤ g μ := by
    intro a b
    obtain ⟨g, hg, hgb⟩ := hWsum i a b
    exact ⟨g, hg, fun μ => le_trans (norm_nonneg _) (hgb 0 ⟨le_refl 0, hτ₀⟩ μ),
      fun σ hσ μ => hgb σ hσ μ⟩
  choose gab hgab using hpick
  have hgabsum : ∀ a b : Fin (Module.finrank ℝ E), Summable (gab a b) :=
    fun a b => (hgab a b).1
  have hgab0 : ∀ (a b : Fin (Module.finrank ℝ E)) (μ), 0 ≤ gab a b μ :=
    fun a b μ => (hgab a b).2.1 μ
  have hgabb : ∀ (a b : Fin (Module.finrank ℝ E)) (σ : ℝ), σ ∈ Set.Ico (0 : ℝ) τ₀ → ∀ μ,
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ‖ ≤ gab a b μ :=
    fun a b σ hσ μ => (hgab a b).2.2 σ hσ μ
  -- the decay majorant of the coefficients of `U`
  have hM₀ : Fintype.card (Fin (Module.finrank ℝ E))
      < 2 * (Module.finrank ℝ E + 1) := by
    rw [Fintype.card_fin]; omega
  obtain ⟨CU, hCU0, hCUb⟩ := hdecU (Module.finrank ℝ E + 1)
  have hUle : ∀ (σ : ℝ), σ ∈ Set.Ico (0 : ℝ) τ₀ → ∀ (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ),
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (U σ) a b) μ‖
        ≤ CU / (Work.Diff.STE.wt μ) ^ (Module.finrank ℝ E + 1) := by
    intro σ hσ a b μ
    have h := hCUb σ hσ i a b μ
    have hwt : 0 < (Work.Diff.STE.wt μ) ^ (Module.finrank ℝ E + 1) :=
      pow_pos (Work.Diff.STE.wt_pos μ) _
    rw [le_div_iff₀ hwt]
    exact h
  have hCUsumm : Summable (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
      CU / (Work.Diff.STE.wt μ) ^ (Module.finrank ℝ E + 1)) := by
    have h1 : Summable (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
        CU * (Work.Diff.STE.wt μ) ^ (-((Module.finrank ℝ E + 1 : ℕ) : ℤ))) :=
      Summable.mul_left CU (Work.Diff.STE.summable_wt_zpow (Module.finrank ℝ E + 1) hM₀)
    refine h1.congr (fun μ => ?_)
    rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
  -- the majorant of the derivative family
  set G : (Fin (Module.finrank ℝ E) → ℤ) → ℝ := fun μ =>
      |(D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹|
        * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            (|g₀.inner x u (D.e i a x)| * |g₀.inner x v (D.e i b x)|) * gab a b μ with hGdef
  set GU : (Fin (Module.finrank ℝ E) → ℤ) → ℝ := fun μ =>
      |(D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹|
        * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            (|g₀.inner x u (D.e i a x)| * |g₀.inner x v (D.e i b x)|)
              * (CU / (Work.Diff.STE.wt μ) ^ (Module.finrank ℝ E + 1)) with hGUdef
  -- the mean value bound for the coefficients of `U`
  have hmvt : ∀ (a b : Fin (Module.finrank ℝ E)) (s : ℝ), s ∈ Set.Ico (0 : ℝ) τ₀ →
      ∀ μ : Fin (Module.finrank ℝ E) → ℤ,
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (U s) a b) μ
          - Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖ ≤ |s - t| * gab a b μ :=
    fun a b s hs μ => normCoeffSubLe (hder := fun r hr => hcoeff r hr i a b μ)
      (hb := fun r hr => hgabb a b r hr μ) ht s hs
  -- summability of the majorants
  have hGsum : Summable G := by
    rw [hGdef]
    refine Summable.mul_left _ ?_
    refine summable_sum (s := Finset.univ) (fun a _ => ?_)
    refine summable_sum (s := Finset.univ) (fun b _ => ?_)
    exact Summable.mul_left _ (hgabsum a b)
  have hGUsum : Summable GU := by
    rw [hGUdef]
    refine Summable.mul_left _ ?_
    refine summable_sum (s := Finset.univ) (fun a _ => ?_)
    refine summable_sum (s := Finset.univ) (fun b _ => ?_)
    exact Summable.mul_left _ hCUsumm
  have hG0 : ∀ μ, 0 ≤ G μ := by
    intro μ
    rw [hGdef]
    refine mul_nonneg (abs_nonneg _) ?_
    refine Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => ?_))
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (hgab0 a b μ)
  -- summability of the coefficient family at `t`
  have hct : Summable (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
      ‖bilCoeff D i x (U t) u v μ‖) := by
    refine Summable.of_nonneg_of_le (fun μ => norm_nonneg _) (fun μ => ?_) hGUsum
    have hKnorm : ‖(((D.ζ i x
            * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹ : ℝ) : ℂ)‖
        = |(D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    calc ‖bilCoeff D i x (U t) u v μ‖
        = ‖(((D.ζ i x
              * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹ : ℝ) : ℂ)
            * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
                  * Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖ := by
              simp only [bilCoeff]
      _ = |(D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹|
            * ‖∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
                  * Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖ := by
              rw [norm_mul, hKnorm]
      _ ≤ |(D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹|
            * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                (|g₀.inner x u (D.e i a x)| * |g₀.inner x v (D.e i b x)|)
                  * ‖Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖ := by
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              calc ‖∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                    (((g₀.inner x u (D.e i a x) : ℝ) : ℂ)
                        * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
                      * Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖
                  ≤ ∑ a : Fin (Module.finrank ℝ E), ‖∑ b : Fin (Module.finrank ℝ E),
                      (((g₀.inner x u (D.e i a x) : ℝ) : ℂ)
                          * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
                        * Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖ :=
                    norm_sum_le (Finset.univ) _
                _ ≤ ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                      ‖(((g₀.inner x u (D.e i a x) : ℝ) : ℂ)
                          * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
                        * Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖ :=
                    Finset.sum_le_sum (fun a _ => norm_sum_le (Finset.univ) _)
                _ = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                      (|g₀.inner x u (D.e i a x)| * |g₀.inner x v (D.e i b x)|)
                        * ‖Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖ := by
                    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
                    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |(D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹|
            * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                (|g₀.inner x u (D.e i a x)| * |g₀.inner x v (D.e i b x)|)
                  * (CU / (Work.Diff.STE.wt μ) ^ (Module.finrank ℝ E + 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              refine Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => ?_))
              exact mul_le_mul_of_nonneg_left (hUle t ht a b μ)
                (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = GU μ := by rw [hGUdef]
  -- the Lipschitz bound for the coefficient family
  have hdiff : ∀ s ∈ Set.Ico (0 : ℝ) τ₀, ∀ μ : Fin (Module.finrank ℝ E) → ℤ,
      ‖bilCoeff D i x (U s) u v μ - bilCoeff D i x (U t) u v μ‖ ≤ |s - t| * G μ := by
    intro s hs μ
    have hsub : bilCoeff D i x (U s) u v μ - bilCoeff D i x (U t) u v μ
        = (((D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹
            : ℝ) : ℂ)
          * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
                * (Work.Diff.STE.fourierCoeff (D.Rper i (U s) a b) μ
                    - Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ) := by
      simp only [bilCoeff]
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      ring
    have hKnorm : ‖(((D.ζ i x
          * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹ : ℝ) : ℂ)‖
        = |(D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hsub, norm_mul, hKnorm]
    calc |(D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹|
          * ‖∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
                * (Work.Diff.STE.fourierCoeff (D.Rper i (U s) a b) μ
                    - Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ)‖
        ≤ |(D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹|
          * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              (|g₀.inner x u (D.e i a x)| * |g₀.inner x v (D.e i b x)|)
                * ‖Work.Diff.STE.fourierCoeff (D.Rper i (U s) a b) μ
                    - Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          calc ‖∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
                  * (Work.Diff.STE.fourierCoeff (D.Rper i (U s) a b) μ
                      - Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ)‖
              ≤ ∑ a : Fin (Module.finrank ℝ E), ‖∑ b : Fin (Module.finrank ℝ E),
                  (((g₀.inner x u (D.e i a x) : ℝ) : ℂ) * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
                    * (Work.Diff.STE.fourierCoeff (D.Rper i (U s) a b) μ
                        - Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ)‖ :=
                norm_sum_le (Finset.univ) _
            _ ≤ ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                  ‖(((g₀.inner x u (D.e i a x) : ℝ) : ℂ)
                      * ((g₀.inner x v (D.e i b x) : ℝ) : ℂ))
                    * (Work.Diff.STE.fourierCoeff (D.Rper i (U s) a b) μ
                        - Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ)‖ :=
                Finset.sum_le_sum (fun a _ => norm_sum_le (Finset.univ) _)
            _ = ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                  (|g₀.inner x u (D.e i a x)| * |g₀.inner x v (D.e i b x)|)
                    * ‖Work.Diff.STE.fourierCoeff (D.Rper i (U s) a b) μ
                        - Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖ := by
                refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
                simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |(D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹|
          * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              (|g₀.inner x u (D.e i a x)| * |g₀.inner x v (D.e i b x)|)
                * (|s - t| * gab a b μ) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => ?_))
          exact mul_le_mul_of_nonneg_left (hmvt a b s hs μ)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = |s - t| * G μ := by
          rw [hGdef]
          have hS : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                (|g₀.inner x u (D.e i a x)| * |g₀.inner x v (D.e i b x)|)
                  * (|s - t| * gab a b μ))
              = |s - t| * (∑ a : Fin (Module.finrank ℝ E),
                  ∑ b : Fin (Module.finrank ℝ E),
                    (|g₀.inner x u (D.e i a x)| * |g₀.inner x v (D.e i b x)|)
                      * gab a b μ) := by
            symm
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun b _ => ?_)
            ring
          rw [hS]
          ring
  -- the derivative of the coefficient family
  have hder : ∀ μ : Fin (Module.finrank ℝ E) → ℤ,
      HasDerivWithinAt (fun s : ℝ => bilCoeff D i x (U s) u v μ)
        (bilCoeff D i x (W t) u v μ) (Set.Ico (0 : ℝ) τ₀) t := by
    intro μ
    simp only [bilCoeff]
    refine HasDerivWithinAt.const_mul _ ?_
    refine hasDerivWithinAt_sum_fun (fun a => ?_)
    refine hasDerivWithinAt_sum_fun (fun b => ?_)
    exact HasDerivWithinAt.const_mul _ (hcoeff t ht i a b μ)
  -- the value of the series is the pointwise value
  have hvalU : ∀ s : ℝ, Work.Diff.STE.seriesFun (bilCoeff D i x (U s) u v)
      (Work.Diff.STE.coord (I := I) (D.x₀ i) x) = (((U s) x u v : ℝ) : ℂ) :=
    fun s => seriesFun_bilCoeff D i x (U s) u v (hsmU s) hzi
  have hvalW : Work.Diff.STE.seriesFun (bilCoeff D i x (W t) u v)
      (Work.Diff.STE.coord (I := I) (D.x₀ i) x) = (((W t) x u v : ℝ) : ℂ) :=
    seriesFun_bilCoeff D i x (W t) u v (hsmW t) hzi
  -- term-by-term differentiation of the series
  have hcore := Work.Diff.STE.flat.hasDerivWithinAt_seriesFun_core
    (τ := τ₀) (t := t) hτ₀ ht
    (fun s => bilCoeff D i x (U s) u v) (bilCoeff D i x (W t) u v)
    (Work.Diff.STE.coord (I := I) (D.x₀ i) x) G hGsum hG0 hdiff hct hder
  have h3 : HasDerivWithinAt (fun s : ℝ => (((U s) x u v : ℝ) : ℂ))
      ((((W t) x u v : ℝ)) : ℂ) (Set.Ico (0 : ℝ) τ₀) t := by
    have h := hcore.congr (fun y _ => (hvalU y).symm) (hvalU t).symm
    rwa [hvalW] at h
  -- pass from the complexified statement back to the real one
  have h4 := hasDerivWithinAt_iff_hasFDerivWithinAt.mp h3
  have h5 : HasFDerivWithinAt (fun s : ℝ => Complex.reCLM ((((U s) x u v : ℝ)) : ℂ))
      (Complex.reCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ ((((W t) x u v : ℝ)) : ℂ)))
      (Set.Ico (0 : ℝ) τ₀) t :=
    HasFDerivWithinAt.comp t (ContinuousLinearMap.hasFDerivWithinAt Complex.reCLM) h4
      (Set.mapsTo_univ _ _)
  have h6 : Complex.reCLM.comp
        (ContinuousLinearMap.toSpanSingleton ℝ ((((W t) x u v : ℝ)) : ℂ))
      = ContinuousLinearMap.toSpanSingleton ℝ ((W t) x u v) := by
    ext z
    simp [ContinuousLinearMap.toSpanSingleton_apply, Complex.ofReal_re]
  rw [h6] at h5
  have hfun : (fun s : ℝ => Complex.reCLM ((((U s) x u v : ℝ)) : ℂ))
      = fun s : ℝ => (U s) x u v := by
    funext s
    simp [Complex.ofReal_re]
  rw [hfun] at h5
  exact hasDerivWithinAt_iff_hasFDerivWithinAt.mpr h5

end

end Work.Diff.STE.Lead
