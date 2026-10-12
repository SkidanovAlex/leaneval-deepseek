import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SmallBoxA0.aQsum_sq_integral_le
import Submission.Work.SmallBoxA0.slot_abs_integral_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission BoseGases
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- **The `√`-shaped bound on the `Corr` residue** (scale-invariant form; the
previous attempt at this path was FALSIFIED by the rescaling counterexample
`s ↦ εs, v ↦ ε⁻²v(·/ε), μ ↦ μ/ε³`, which showed that the `s⁻³` belongs on the
`2·s⁻³·CorrWord` side of the assembly and NOT on this `√`-bound).

For a NORMALISED continuous `Φ : X (n+1)`,

    2·CorrWord s h Φ
      ≤ (32·π·chiSup²·(n+2))·(av)·√(cS1 s Φ)·√(cnPlus s Φ) .

`CorrWord s h Φ = Σᵢ∫(aP s i Φ)·f₁(xᵢ)·(Σ_k aQ s k (aQ s i Φ))` is bilinear in the
condensate (`P`-side, → `√cS1`) and the excited (`Q`-side, → `√cnPlus`) parts, so a
`√`-shaped bound is the only kind available from the corpus's quadratic-form
framework.  The constant is `fsqC2(av) = 32π(av)chiSup²` times the unavoidable
`(N+1)` factor of the `Σ_k`-sum: since `aQ k (aQ i Φ) = Q_i(aQ k Φ)` and
`Σ_k aQ k ψ = N·ψ − Σ_k mean_k ψ`, one has `Σ_k‖aQ k ψ‖₂ ≤ N‖ψ‖₂`, so the `N`-factor
cannot be dropped (a product state `Φ = Π_j ψ(x_j)` with `∫ψ`-mean part gives
`CorrWord ~ N·√(cS1)·√(cnPlus)`).

Route.  `|f₁| ≤ fsqC1(av) = 16π(av)chiSup²` pointwise
(`QMassUpper.w1c_fibre_acube_abs_le`, as used in
`Step4SqrtFactorisation.qOneMass_le_fsqC1_mul_cnPlus`); then Cauchy–Schwarz in the
position variable slot by slot,
`|∫(aP i Φ)·f₁·(Σ_k aQ k (aQ i Φ))| ≤ fsqC1·‖aP i Φ‖₂·‖Σ_k aQ k (aQ i Φ)‖₂`, then
Cauchy–Schwarz over `i`:
`Σᵢ‖aP i Φ‖₂‖Σ_k aQ k (aQ i Φ)‖₂ ≤ √(cS1)·√(Σᵢ‖Σ_k aQ k (aQ i Φ)‖₂²)`, and finally
`Σᵢ‖Σ_k aQ k (aQ i Φ)‖₂² ≤ N²·cnPlus s Φ` (two Cauchy–Schwarz steps over `k` and
`‖aQ k ψ‖₂ ≤ ‖ψ‖₂`, with the normalisation giving `cS1 ≤ N`).

With this, the bundle's `CorrC` becomes the CONCRETE constant `32π·chiSup²·(N+1)`
(no longer a data field) and the `Corr` residue is a theorem; the assembly's linear
form is already proved by `Work.SmallBoxA0.corr_linear_of_sqrt` (AM–GM + the regime
`4(CorrC(av))²N̂ ≤ π(av)μs⁴`). -/
lemma corrWord_sqrt_bound {n : ℕ} {s R : ℝ} {v : ℝ³ → ℝ} (hs : 0 < s) (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (hRs : R ≤ s * chiR0)
    {Φ : X (n + 1) → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox (n + 1) s, (Φ x) ^ 2) = 1) :
    2 * CorrWord s h Φ
      ≤ (32 * π * chiSup ^ 2 * ((n : ℝ) + 2)) * (a v)
          * Real.sqrt (cS1 s Φ) * Real.sqrt (cnPlus s Φ) := by
  classical
  have hav : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  set K : ℝ := fsqC1 (a v) with hKdef
  set f1 : ℝ³ → ℝ := fun z => w1Fibre s (wPairC s (g0 v h)) z with hf1def
  have hf1b : ∀ z, |f1 z| ≤ K := by
    intro z
    have hb := w1c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hs hRs z
    rw [hKdef, hf1def]
    simpa [fsqC1, w1Fibre, wPairC] using hb
  have hKnn : 0 ≤ K := le_trans (abs_nonneg (f1 0)) (hf1b 0)
  have hf1aem : ∀ i : Fin (n + 1),
      AEStronglyMeasurable (fun x : X (n + 1) => f1 (x i)) (volume.restrict (abox (n + 1) s)) := by
    intro i
    have hg0 : Integrable (g0 v h) volume := g0_integrable hR hv_supp h
    have hthis := w1Fibre_coord_aem (N := n + 1) (ℓ := s) (h := g0 v h) hg0 i
    simpa [hf1def] using hthis
  have hHc : ∀ i : Fin (n + 1), Continuous (fun x : X (n + 1) =>
      ∑ k : Fin (n + 1), aQ s k (aQ s i Φ) x) := by
    intro i
    apply continuous_finsetSum
    intro k _
    exact aQ_continuous hs k (aQ_continuous hs i hΦc)
  have hCorr_eq : CorrWord s h Φ = ∑ i : Fin (n + 1), ∫ x in abox (n + 1) s,
      (aP s i Φ x) * f1 (x i) * (∑ k : Fin (n + 1), aQ s k (aQ s i Φ) x) := by
    simp only [CorrWord, hf1def]
  have hGi : ∀ i : Fin (n + 1),
      |∫ x in abox (n + 1) s, (aP s i Φ x) * f1 (x i) * (∑ k : Fin (n + 1), aQ s k (aQ s i Φ) x)|
        ≤ K * Real.sqrt (∫ x in abox (n + 1) s, (aP s i Φ x) ^ 2)
            * Real.sqrt (∫ x in abox (n + 1) s, (∑ k : Fin (n + 1), aQ s k (aQ s i Φ) x) ^ 2) := by
    intro i
    exact slot_abs_integral_le hs (hf1aem i) (fun x => hf1b (x i))
      (aP_continuous hs i hΦc) (hHc i)
  have hB : ∀ i : Fin (n + 1),
      (∫ x in abox (n + 1) s, (∑ k : Fin (n + 1), aQ s k (aQ s i Φ) x) ^ 2)
        ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * ∫ x in abox (n + 1) s, (aQ s i Φ x) ^ 2 := by
    intro i
    simpa using aQsum_sq_integral_le (N := n + 1) (s := s) hs (aQ_continuous hs i hΦc)
  have hBsum : (∑ i : Fin (n + 1), ∫ x in abox (n + 1) s,
        (∑ k : Fin (n + 1), aQ s k (aQ s i Φ) x) ^ 2)
      ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * cnPlus s Φ := by
    calc (∑ i : Fin (n + 1), ∫ x in abox (n + 1) s, (∑ k : Fin (n + 1), aQ s k (aQ s i Φ) x) ^ 2)
        ≤ ∑ i : Fin (n + 1), (((n + 1 : ℕ) : ℝ) ^ 2 * ∫ x in abox (n + 1) s, (aQ s i Φ x) ^ 2) :=
          Finset.sum_le_sum (fun i _ => hB i)
      _ = ((n + 1 : ℕ) : ℝ) ^ 2 * (∑ i : Fin (n + 1), ∫ x in abox (n + 1) s, (aQ s i Φ x) ^ 2) := by
          rw [Finset.mul_sum]
      _ = ((n + 1 : ℕ) : ℝ) ^ 2 * cnPlus s Φ := by rw [cnPlus]
  have hS1 : (∑ i : Fin (n + 1), ∫ x in abox (n + 1) s, (aP s i Φ x) ^ 2) = cS1 s Φ := by
    rw [cS1]
  have hAfun_nonneg : ∀ i : Fin (n + 1),
      0 ≤ (∫ x in abox (n + 1) s, (aP s i Φ x) ^ 2) := by
    intro i
    exact integral_nonneg (fun x => sq_nonneg _)
  have hBfun_nonneg : ∀ i : Fin (n + 1),
      0 ≤ (∫ x in abox (n + 1) s, (∑ k : Fin (n + 1), aQ s k (aQ s i Φ) x) ^ 2) := by
    intro i
    exact integral_nonneg (fun x => sq_nonneg _)
  have hCS : (∑ i : Fin (n + 1), Real.sqrt (∫ x in abox (n + 1) s, (aP s i Φ x) ^ 2)
        * Real.sqrt (∫ x in abox (n + 1) s, (∑ k : Fin (n + 1), aQ s k (aQ s i Φ) x) ^ 2))
      ≤ Real.sqrt (cS1 s Φ) * Real.sqrt (((n + 1 : ℕ) : ℝ) ^ 2 * cnPlus s Φ) := by
    have h := Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
      (f := fun i : Fin (n + 1) => ∫ x in abox (n + 1) s, (aP s i Φ x) ^ 2)
      (g := fun i : Fin (n + 1) => ∫ x in abox (n + 1) s, (∑ k : Fin (n + 1), aQ s k (aQ s i Φ) x) ^ 2)
      hAfun_nonneg hBfun_nonneg
    rw [hS1] at h
    refine le_trans h ?_
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    exact Real.sqrt_le_sqrt hBsum
  have hAbsBound : |CorrWord s h Φ|
      ≤ K * Real.sqrt (cS1 s Φ) * Real.sqrt (((n + 1 : ℕ) : ℝ) ^ 2 * cnPlus s Φ) := by
    calc |CorrWord s h Φ|
        = |∑ i : Fin (n + 1), ∫ x in abox (n + 1) s,
            (aP s i Φ x) * f1 (x i) * (∑ k : Fin (n + 1), aQ s k (aQ s i Φ) x)| := by rw [hCorr_eq]
      _ ≤ ∑ i : Fin (n + 1), |∫ x in abox (n + 1) s,
            (aP s i Φ x) * f1 (x i) * (∑ k : Fin (n + 1), aQ s k (aQ s i Φ) x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin (n + 1), K * Real.sqrt (∫ x in abox (n + 1) s, (aP s i Φ x) ^ 2)
            * Real.sqrt (∫ x in abox (n + 1) s, (∑ k : Fin (n + 1), aQ s k (aQ s i Φ) x) ^ 2) :=
          Finset.sum_le_sum (fun i _ => hGi i)
      _ = ∑ i : Fin (n + 1), K * (Real.sqrt (∫ x in abox (n + 1) s, (aP s i Φ x) ^ 2)
            * Real.sqrt (∫ x in abox (n + 1) s, (∑ k : Fin (n + 1), aQ s k (aQ s i Φ) x) ^ 2)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_); ring
      _ = K * (∑ i : Fin (n + 1), Real.sqrt (∫ x in abox (n + 1) s, (aP s i Φ x) ^ 2)
            * Real.sqrt (∫ x in abox (n + 1) s, (∑ k : Fin (n + 1), aQ s k (aQ s i Φ) x) ^ 2)) := by
          rw [Finset.mul_sum]
      _ ≤ K * (Real.sqrt (cS1 s Φ) * Real.sqrt (((n + 1 : ℕ) : ℝ) ^ 2 * cnPlus s Φ)) :=
          mul_le_mul_of_nonneg_left hCS hKnn
      _ = K * Real.sqrt (cS1 s Φ) * Real.sqrt (((n + 1 : ℕ) : ℝ) ^ 2 * cnPlus s Φ) := by ring
  have hsqrt : Real.sqrt (((n + 1 : ℕ) : ℝ) ^ 2 * cnPlus s Φ)
      = ((n + 1 : ℕ) : ℝ) * Real.sqrt (cnPlus s Φ) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2)]
    rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))]
  have hfinal : 2 * CorrWord s h Φ
      ≤ (2 * K * ((n + 1 : ℕ) : ℝ)) * Real.sqrt (cS1 s Φ) * Real.sqrt (cnPlus s Φ) := by
    have h2 := hAbsBound
    rw [hsqrt] at h2
    have hs1 := le_abs_self (CorrWord s h Φ)
    have hstep2 : 2 * |CorrWord s h Φ|
        ≤ 2 * (K * Real.sqrt (cS1 s Φ) * (((n + 1 : ℕ) : ℝ) * Real.sqrt (cnPlus s Φ))) :=
      mul_le_mul_of_nonneg_left h2 (by norm_num)
    have hstep3 : 2 * (K * Real.sqrt (cS1 s Φ) * (((n + 1 : ℕ) : ℝ) * Real.sqrt (cnPlus s Φ)))
        = (2 * K * ((n + 1 : ℕ) : ℝ)) * Real.sqrt (cS1 s Φ) * Real.sqrt (cnPlus s Φ) := by ring
    linarith [hs1, hstep2, hstep3]
  have hconst : 2 * K * ((n + 1 : ℕ) : ℝ) ≤ (32 * π * chiSup ^ 2 * ((n : ℝ) + 2)) * (a v) := by
    have h2KN : 2 * K * ((n + 1 : ℕ) : ℝ) = 32 * π * chiSup ^ 2 * (a v) * ((n : ℝ) + 1) := by
      simp only [hKdef, fsqC1]; push_cast; ring
    rw [h2KN]
    have hle : ((n : ℝ) + 1) ≤ ((n : ℝ) + 2) := by norm_num
    have hnn : 0 ≤ 32 * π * chiSup ^ 2 * (a v) := by
      have h1 : (0 : ℝ) ≤ 32 * π := by positivity
      have h2 : (0 : ℝ) ≤ chiSup ^ 2 := sq_nonneg _
      exact mul_nonneg (mul_nonneg h1 h2) hav
    calc 32 * π * chiSup ^ 2 * (a v) * ((n : ℝ) + 1)
        ≤ 32 * π * chiSup ^ 2 * (a v) * ((n : ℝ) + 2) := mul_le_mul_of_nonneg_left hle hnn
      _ = (32 * π * chiSup ^ 2 * ((n : ℝ) + 2)) * (a v) := by ring
  calc 2 * CorrWord s h Φ
      ≤ (2 * K * ((n + 1 : ℕ) : ℝ)) * Real.sqrt (cS1 s Φ) * Real.sqrt (cnPlus s Φ) := hfinal
    _ ≤ (32 * π * chiSup ^ 2 * ((n : ℝ) + 2)) * (a v) * Real.sqrt (cS1 s Φ)
          * Real.sqrt (cnPlus s Φ) := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_right hconst
          exact Real.sqrt_nonneg _
        · exact Real.sqrt_nonneg _

end Work.SmallBoxA0
