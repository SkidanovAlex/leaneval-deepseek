import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.LatGreen.HeatPeriodFixedS
import Submission.Work.BoseFixR.LatGreen.HeatPeriodIocDomination
import Submission.Work.BoseFixR.LatGreen.LatGreenSmoothBddBelow
import Submission.Work.BoseFixR.LatGreen.LatGreenTripleIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

open scoped Real BigOperators RealInnerProductSpace
open MeasureTheory

/-- **Step 3 of the passage, `(B)`-carrying form** (re-filed at this path because
`LatGreenParseval` already exists with the statement its prover correctly refuted; the witness
there was `P_r = A·cos(N x₁)·1_{B_r}`, `N = r⁻²`, `A = r^{-7/2}`, where `hsum` is finite while
`∬|P P·latGreen| ≈ r⁻² → ∞`).

`Σ'_{k∈ℤ³∖0}(chat W q_k)²/‖q_k‖² = ∬_{cell ℓ × cell ℓ} P(x)P(y)·K_♯(x−y)`, with
`q_k = ℓ⁻¹•vec k`, `P = period W ℓ`, `K_♯(z) = ℓ²·latGreen(ℓ⁻¹•z)`, and **(B)** absolute
integrability explicit.  `hWev` is necessary (otherwise the RHS keeps the sine cross terms — witness
`W = 1_{cell}·sin⟨q_j,·⟩`); **(B)** is necessary (the refutation); `hsum` is the row's summability;
`hW`/`hper` make the periodisation genuine (`chat W (kmomLab ℓ N k) = ∫_cell P·cos⟨q_k,·⟩` by
`chat_cellIntegral`).

Route (per review): the bounded `ε`-cut kernels
`K_ε♯ = Σ_{m≠0}e^{−4π²ε‖m‖²}cos⟨q_m,·⟩/‖q_m‖²` satisfy `∬PP·K_ε♯ = Σ_k e^{−ε‖q_k‖²}ĉ_k²/λ_k`
elementarily (Fubini, `|K_ε♯| ≤ C`), and **(B)** supplies the domination for `ε → 0`; equivalently
pass `CellParseval` to the cube-exhaustion limit using `hsum` plus `(B)`.
`cellCoulombIntegrableOn` supplies **(B)** for the intended bounded a.e.-measurable `P`.

**How it is proved here** (the route actually formalised, which needs neither the `ε`-cut kernels
nor a cube-exhaustion limit).  Write `P = period W ℓ`, `q_k = qmom ℓ k = ℓ⁻¹ • vec k`, `μ` for
`volume.restrict (cell ℓ)` and `ν = volume.restrict (Ioi 0)`.

1. *Cell Fourier coefficients* (`LatGreenCellFourier`): `chat W q_k = ∫_{cell} P cos⟨q_k,·⟩`
   (the phase `⟨q_k, lat ℓ n⟩ = 2π(k·n)` drops out of the tiling sum), the sine coefficient
   vanishes for even `W` (this is where `hWev` is used), and hence the pairing
   `∬_{cell²} P(x)P(y)cos⟨q_k,x−y⟩ = (chat W q_k)²`.
2. *Fixed-time identity* (`HeatPeriodFixedS`): for every `s > 0`, the Poisson/θ series of the
   bounded kernel `heatPeriod s (ℓ⁻¹•(x−y)) − 1` may be integrated termwise against `P ⊗ P`,
   giving `∬ PP (heatPeriod s(ℓ⁻¹•(x−y)) − 1) = Σ_k [k≠0] e^{−s‖vec k‖²}(chat W q_k)²`.
3. *Fubini in `s`*: `latGreen u = ∫_0^∞ (heatPeriod s u − 1) ds` by definition, so the target
   right-hand side is `ℓ² ∫_s ∫_p P p₁ P p₂ (heatPeriod s (ℓ⁻¹•(p₁−p₂)) − 1)`.  The exchange of
   the two integrals is licensed by `LatGreenTripleIntegrable`, which bounds the (s,p)-integrand
   by the *local* Coulomb kernel through `HeatPeriodIocDomination` (small `s`) and
   `abs_heatPeriod_sub_one_le_exp` (large `s`), and converts the `1/‖u−n‖` singularity into the
   integrable **(B)** via the lower bound `LatGreenSmoothBddBelow` on the smooth part of
   `latGreen` together with its periodicity.
4. *The `s`-integral*: `∫_0^∞ e^{−s‖vec k‖²} ds = 1/‖vec k‖²` (Tonelli; all terms nonnegative,
   finiteness from `hsum`), and `ℓ²‖q_k‖² = ‖vec k‖²` converts the result into the stated
   `Σ_k [k≠0](chat W q_k)²/‖q_k‖²`. -/
theorem LatGreenParsevalB {ℓ : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W)
    (hWev : ∀ x : EuclideanSpace ℝ (Fin 3), W (-x) = W x)
    (hper : ∀ x : EuclideanSpace ℝ (Fin 3),
      Summable (fun n : Fin 3 → ℤ => W (x - Work.BoseFixR.lat ℓ n)))
    (hsum : Summable (fun k : Fin 3 → ℤ => if k = 0 then 0 else
      (Work.BoseFixR.chat W (ℓ⁻¹ • Work.BoseB4.vec k)) ^ 2
        / ‖ℓ⁻¹ • Work.BoseB4.vec k‖ ^ 2))
    (hB : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        |Work.BoseFixR.LatGreen.period W ℓ p.1 * Work.BoseFixR.LatGreen.period W ℓ p.2
          * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2)))|)
      (Work.BoseFixR.cell ℓ ×ˢ Work.BoseFixR.cell ℓ)) :
    (∑' k : Fin 3 → ℤ, if k = 0 then 0 else
        (Work.BoseFixR.chat W (ℓ⁻¹ • Work.BoseB4.vec k)) ^ 2
          / ‖ℓ⁻¹ • Work.BoseB4.vec k‖ ^ 2)
      = ∫ x in Work.BoseFixR.cell ℓ, ∫ y in Work.BoseFixR.cell ℓ,
          Work.BoseFixR.LatGreen.period W ℓ x * Work.BoseFixR.LatGreen.period W ℓ y
            * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (x - y))) := by
  set P : EuclideanSpace ℝ (Fin 3) → ℝ := Work.BoseFixR.LatGreen.period W ℓ with hP
  set μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)) :=
    MeasureTheory.volume.restrict (Work.BoseFixR.cell ℓ) with hμ
  set ν : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) with hν
  obtain ⟨Cdom, hdom⟩ := HeatPeriodIocDomination
  obtain ⟨Mdom, hlt⟩ := LatGreenSmoothBddBelow
  have hTriple := LatGreenTripleIntegrable (ℓ := ℓ) hℓ hW hper hlt hdom hB
  -- the per-mode pairing (cell Fourier coefficient identity)
  have hcos : ∀ k : Fin 3 → ℤ,
      ∫ x in Work.BoseFixR.cell ℓ, ∫ y in Work.BoseFixR.cell ℓ,
          P x * P y * Real.cos (inner ℝ (qmom ℓ k) (x - y))
        = (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2 := by
    intro k
    rw [hP]
    exact LatGreenCellPairing hℓ hW hWev hper k
  -- measurability of `latGreen`
  have hLGsm : Measurable (fun u : EuclideanSpace ℝ (Fin 3) => latGreen u) := by
    have h1 : StronglyMeasurable (Function.uncurry (fun (t : ℝ)
        (u : EuclideanSpace ℝ (Fin 3)) => heatPeriod t u - 1)) :=
      (measurable_heatPeriod_pair.sub measurable_const).stronglyMeasurable
    have h2 : StronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
        ∫ t, (fun (t : ℝ) (u : EuclideanSpace ℝ (Fin 3)) => heatPeriod t u - 1) t u
          ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :=
      h1.integral_prod_left (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    exact h2.measurable
  have hPint : MeasureTheory.Integrable P μ := integrableOn_period hℓ hW hper
  -- (B) transferred to the product measure
  have hB' : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        |P p.1 * P p.2 * (ℓ ^ 2 * latGreen (ℓ⁻¹ • (p.1 - p.2)))|) (μ.prod μ) := by
    rw [hP, hμ]
    rw [MeasureTheory.Measure.prod_restrict]
    exact hB
  -- the right-hand integrand is integrable on the square
  have hRint : MeasureTheory.Integrable
      (Function.uncurry (fun x y : EuclideanSpace ℝ (Fin 3) =>
        P x * P y * (ℓ ^ 2 * latGreen (ℓ⁻¹ • (x - y))))) (μ.prod μ) := by
    refine hB'.mono' ?_ ?_
    · refine ((((hPint.aestronglyMeasurable.aemeasurable.comp_fst).mul
        (hPint.aestronglyMeasurable.aemeasurable.comp_snd)).mul
        (aemeasurable_const.mul ?_)).aestronglyMeasurable)
      exact ((hLGsm.comp (by fun_prop : Measurable fun p :
        EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => ℓ⁻¹ • (p.1 - p.2))).aemeasurable)
    · filter_upwards with p
      have hp : Function.uncurry (fun x y : EuclideanSpace ℝ (Fin 3) =>
          P x * P y * (ℓ ^ 2 * latGreen (ℓ⁻¹ • (x - y)))) p
          = P p.1 * P p.2 * (ℓ ^ 2 * latGreen (ℓ⁻¹ • (p.1 - p.2))) := rfl
      rw [hp, Real.norm_eq_abs]
  -- the target right-hand side, in product form
  have hRHSprod : (∫ x in Work.BoseFixR.cell ℓ, ∫ y in Work.BoseFixR.cell ℓ,
        Work.BoseFixR.LatGreen.period W ℓ x * Work.BoseFixR.LatGreen.period W ℓ y
          * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (x - y))))
      = ∫ p, P p.1 * P p.2 * (ℓ ^ 2 * latGreen (ℓ⁻¹ • (p.1 - p.2))) ∂(μ.prod μ) :=
    MeasureTheory.integral_integral hRint
  -- rewrite `latGreen` as its defining heat integral and pull out `ℓ ^ 2`
  have hstep2 : (∫ p, P p.1 * P p.2 * (ℓ ^ 2 * latGreen (ℓ⁻¹ • (p.1 - p.2))) ∂(μ.prod μ))
      = ℓ ^ 2 * ∫ p, ∫ s, P p.1 * P p.2
          * (heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1) ∂ν ∂(μ.prod μ) := by
    have h1 : ∀ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        P p.1 * P p.2 * (ℓ ^ 2 * latGreen (ℓ⁻¹ • (p.1 - p.2)))
          = ℓ ^ 2 * ∫ s, P p.1 * P p.2 * (heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1) ∂ν := by
      intro p
      rw [latGreen]
      rw [show P p.1 * P p.2 * (ℓ ^ 2 * ∫ s, (heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1) ∂ν)
          = ℓ ^ 2 * ((P p.1 * P p.2) * ∫ s, (heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1) ∂ν) by ring]
      rw [← MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h1),
      MeasureTheory.integral_const_mul]
  -- the (s,p) integrand is jointly integrable
  have hTriple0 : MeasureTheory.Integrable
      (Function.uncurry (fun (s : ℝ)
        (p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        P p.1 * P p.2 * (heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1)))
      (ν.prod (μ.prod μ)) := by
    rw [hP, hμ, hν]
    rw [MeasureTheory.Measure.prod_restrict]
    exact hTriple
  have hTriple' : MeasureTheory.Integrable
      (Function.uncurry (fun (p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
        (s : ℝ) => P p.1 * P p.2 * (heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1)))
      ((μ.prod μ).prod ν) := hTriple0.swap
  have hstep3 : (∫ p, ∫ s, P p.1 * P p.2 * (heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1) ∂ν ∂(μ.prod μ))
      = ∫ s, ∫ p, P p.1 * P p.2 * (heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1) ∂(μ.prod μ) ∂ν :=
    MeasureTheory.integral_integral_swap hTriple'
  -- the inner (cell) integral, for every `s > 0`
  have hpair (s : ℝ) (hs : 0 < s) :
      (∫ p, P p.1 * P p.2 * (heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1) ∂(μ.prod μ))
        = ∑' k : Fin 3 → ℤ, if k = 0 then 0 else
            Real.exp (-s * ‖Work.BoseB4.vec k‖ ^ 2)
              * (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2 := by
    have hint : MeasureTheory.Integrable
        (Function.uncurry (fun x y : EuclideanSpace ℝ (Fin 3) =>
          P x * P y * (heatPeriod s (ℓ⁻¹ • (x - y)) - 1))) (μ.prod μ) := by
      have hsm : AEStronglyMeasurable
          (Function.uncurry (fun x y : EuclideanSpace ℝ (Fin 3) =>
            P x * P y * (heatPeriod s (ℓ⁻¹ • (x - y)) - 1))) (μ.prod μ) := by
        refine ((((hPint.aestronglyMeasurable.aemeasurable.comp_fst).mul
          (hPint.aestronglyMeasurable.aemeasurable.comp_snd)).mul
          ?_).aestronglyMeasurable)
        exact (((measurable_heatPeriod s hs).comp (by fun_prop)).aemeasurable.sub
          aemeasurable_const)
      refine MeasureTheory.Integrable.mono'
        ((hPint.norm.mul_prod hPint.norm).const_mul (∑' k : {k : Fin 3 → ℤ // k ≠ 0},
          Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2))) hsm ?_
      filter_upwards with p
      have hp : Function.uncurry (fun x y : EuclideanSpace ℝ (Fin 3) =>
          P x * P y * (heatPeriod s (ℓ⁻¹ • (x - y)) - 1)) p
          = P p.1 * P p.2 * (heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1) := rfl
      rw [hp, Real.norm_eq_abs, abs_mul, abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |P p.1| * |P p.2| * |heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1|
          ≤ |P p.1| * |P p.2| * (∑' k : {k : Fin 3 → ℤ // k ≠ 0},
              Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left (abs_heatPeriod_sub_one_le s hs _)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = (∑' k : {k : Fin 3 → ℤ // k ≠ 0},
              Real.exp (-s * ‖Work.BoseB4.vec (k : Fin 3 → ℤ)‖ ^ 2))
            * (|P p.1| * |P p.2|) := by ring
    rw [← MeasureTheory.integral_integral hint]
    exact HeatPeriodFixedS hℓ hW hper hcos hs
  -- the `s`-integration of the lattice row
  have hval' : ∀ k : Fin 3 → ℤ,
      (∫ s, (if k = 0 then 0 else
          Real.exp (-s * ‖Work.BoseB4.vec k‖ ^ 2)
            * (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2) ∂ν)
        = if k = 0 then 0 else
            (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2 / ‖Work.BoseB4.vec k‖ ^ 2 := by
    intro k
    have hif : (fun s : ℝ => (if k = 0 then 0 else
          Real.exp (-s * ‖Work.BoseB4.vec k‖ ^ 2)
            * (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2))
        = (if k = 0 then (0 : ℝ → ℝ) else
            fun s : ℝ => Real.exp (-s * ‖Work.BoseB4.vec k‖ ^ 2)
              * (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2) := by
      funext s
      by_cases hk : k = 0 <;> simp [hk]
    rw [hif]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk]
      have hpos : 0 < ‖Work.BoseB4.vec k‖ ^ 2 := pow_pos (norm_vec_pos hk) 2
      rw [show (fun s : ℝ => Real.exp (-s * ‖Work.BoseB4.vec k‖ ^ 2)
            * (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2)
          = fun s : ℝ => (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2
              * Real.exp (-(‖Work.BoseB4.vec k‖ ^ 2) * s) from by
        funext s
        rw [show -s * ‖Work.BoseB4.vec k‖ ^ 2 = -(‖Work.BoseB4.vec k‖ ^ 2) * s by ring]
        ring]
      rw [MeasureTheory.integral_const_mul,
        integral_exp_mul_Ioi (a := -(‖Work.BoseB4.vec k‖ ^ 2)) (by linarith) 0,
        mul_zero, Real.exp_zero]
      congr 1
      rw [neg_div_neg_eq, one_div]
  have hGint : ∀ k : Fin 3 → ℤ, MeasureTheory.Integrable
      (fun s : ℝ => if k = 0 then 0 else
        Real.exp (-s * ‖Work.BoseB4.vec k‖ ^ 2) * (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2) ν := by
    intro k
    have hif : (fun s : ℝ => (if k = 0 then 0 else
          Real.exp (-s * ‖Work.BoseB4.vec k‖ ^ 2)
            * (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2))
        = (if k = 0 then (0 : ℝ → ℝ) else
            fun s : ℝ => Real.exp (-s * ‖Work.BoseB4.vec k‖ ^ 2)
              * (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2) := by
      funext s
      by_cases hk : k = 0 <;> simp [hk]
    rw [hif]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk]
      have hpos : 0 < ‖Work.BoseB4.vec k‖ ^ 2 := pow_pos (norm_vec_pos hk) 2
      refine ((integrableOn_exp_mul_Ioi (a := -(‖Work.BoseB4.vec k‖ ^ 2))
        (by linarith) 0).const_mul ((Work.BoseFixR.chat W (qmom ℓ k)) ^ 2)).congr ?_
      filter_upwards with s
      rw [show -s * ‖Work.BoseB4.vec k‖ ^ 2 = -(‖Work.BoseB4.vec k‖ ^ 2) * s by ring]
      ring
  have hsum' : Summable (fun k : Fin 3 → ℤ => if k = 0 then 0 else
      (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2 / ‖Work.BoseB4.vec k‖ ^ 2) := by
    refine (hsum.mul_left ((ℓ ^ 2)⁻¹)).congr fun k => ?_
    by_cases hk : k = 0
    · simp [hk]
    · have hv : ‖Work.BoseB4.vec k‖ ≠ 0 := ne_of_gt (norm_vec_pos hk)
      have hℓ2 : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hℓ)
      rw [if_neg hk, if_neg hk, qmom, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hℓ)]
      field_simp
  have hGsum : Summable (fun k : Fin 3 → ℤ =>
      ∫ s, ‖(if k = 0 then 0 else
        Real.exp (-s * ‖Work.BoseB4.vec k‖ ^ 2) * (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2)‖ ∂ν) := by
    refine hsum'.congr fun k => ?_
    by_cases hk : k = 0
    · subst hk
      simp
    · have hnorm : (fun s : ℝ => ‖(if k = 0 then 0 else
            Real.exp (-s * ‖Work.BoseB4.vec k‖ ^ 2)
              * (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2)‖)
          = fun s : ℝ => (if k = 0 then 0 else
              Real.exp (-s * ‖Work.BoseB4.vec k‖ ^ 2)
                * (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2) := by
        funext s
        rw [if_neg hk]
        exact Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
      rw [hnorm, ← hval' k]
  have hIntSum : (∫ s, (∑' k : Fin 3 → ℤ, if k = 0 then 0 else
        Real.exp (-s * ‖Work.BoseB4.vec k‖ ^ 2) * (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2) ∂ν)
      = ∑' k : Fin 3 → ℤ, if k = 0 then 0 else
          (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2 / ‖Work.BoseB4.vec k‖ ^ 2 := by
    have hsum2 := MeasureTheory.hasSum_integral_of_summable_integral_norm (μ := ν) hGint hGsum
    rw [← hsum2.tsum_eq]
    exact tsum_congr fun k => hval' k
  -- arithmetic: `ℓ ^ 2 / ‖vec k‖ ^ 2 = 1 / ‖ℓ⁻¹ • vec k‖ ^ 2`
  have harith : (∑' k : Fin 3 → ℤ, if k = 0 then 0 else
        (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2 / ‖Work.BoseB4.vec k‖ ^ 2)
      = (1 / ℓ ^ 2) * ∑' k : Fin 3 → ℤ, if k = 0 then 0 else
          (Work.BoseFixR.chat W (ℓ⁻¹ • Work.BoseB4.vec k)) ^ 2
            / ‖ℓ⁻¹ • Work.BoseB4.vec k‖ ^ 2 := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg hk, qmom, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hℓ)]
      field_simp
  calc (∑' k : Fin 3 → ℤ, if k = 0 then 0 else
        (Work.BoseFixR.chat W (ℓ⁻¹ • Work.BoseB4.vec k)) ^ 2
          / ‖ℓ⁻¹ • Work.BoseB4.vec k‖ ^ 2)
      = ℓ ^ 2 * (∑' k : Fin 3 → ℤ, if k = 0 then 0 else
          (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2 / ‖Work.BoseB4.vec k‖ ^ 2) := by
        rw [harith]
        field_simp
    _ = ℓ ^ 2 * (∫ s, (∑' k : Fin 3 → ℤ, if k = 0 then 0 else
          Real.exp (-s * ‖Work.BoseB4.vec k‖ ^ 2)
            * (Work.BoseFixR.chat W (qmom ℓ k)) ^ 2) ∂ν) := by rw [hIntSum]
    _ = ℓ ^ 2 * (∫ s, ∫ p, P p.1 * P p.2
          * (heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1) ∂(μ.prod μ) ∂ν) := by
        congr 1
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
        exact (hpair s hs).symm
    _ = ℓ ^ 2 * (∫ p, ∫ s, P p.1 * P p.2
          * (heatPeriod s (ℓ⁻¹ • (p.1 - p.2)) - 1) ∂ν ∂(μ.prod μ)) := by rw [hstep3]
    _ = ∫ p, P p.1 * P p.2 * (ℓ ^ 2 * latGreen (ℓ⁻¹ • (p.1 - p.2))) ∂(μ.prod μ) := by
        rw [hstep2]
    _ = ∫ x in Work.BoseFixR.cell ℓ, ∫ y in Work.BoseFixR.cell ℓ,
          Work.BoseFixR.LatGreen.period W ℓ x * Work.BoseFixR.LatGreen.period W ℓ y
            * (ℓ ^ 2 * Work.BoseFixR.LatGreen.latGreen (ℓ⁻¹ • (x - y))) := hRHSprod.symm

end Work.BoseFixR.LatGreen
