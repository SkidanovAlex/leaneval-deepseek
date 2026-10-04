import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.STE.B3.posDef_of_BNorm_sub_le
import Submission.Work.Diff.STE.B3.SupBound
import Submission.Work.Diff.STE.B3.Pointwise
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.D.ChartData_genMap
import Submission.Work.Diff.STE.D.ChartData_Rstar
import Submission.Work.Diff.STE.B3.STruncC_contDiff_periodic
import Submission.Work.Diff.STE.B3.J_finite_rank
import Submission.Work.Diff.STE.Lead.truncDiff_tendsto_uniform
import Submission.Work.Diff.STE.B3.Rstar_apply
import Submission.Work.Diff.STE.B3.densGood_noT2
import Submission.Work.Diff.STE.B3.matChart_metric_contDiffOn
import Submission.Work.Diff.STE.B3.STruncR_R_sub_le_uniform

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: the seed margin of the Friedrichs mollifier

The Galerkin scheme of Layer D starts at the seed metric `g₀`: its initial state is
`D.J ρ ε g₀.inner`, and the ODE can be started only if `J ρ ε g₀.inner` is positive definite
*with a margin that is uniform in* `ε ≤ ε₀`.  This file proves exactly that.

The proof does **not** use the hypothesis `hJT` (nor `hg`): `J ρ ε` is a Friedrichs mollifier of the
*fixed smooth* metric components `D.R i g₀.inner a b`, and the Friedrichs truncation of a fixed
smooth compactly supported flat function converges *uniformly* to it
(`Work.Diff.STE.Lead.truncDiff_tendsto_uniform`).  Concretely, writing
`W_i = ζ_i(x)·χ_i(coord_i x)·(√(dens_i(coord_i x)))⁻¹`,

`(D.J ρ ε g₀.inner) x v v = Σ_i W_i · Σ_{ab} (S_ε (R_i g₀)_{ab})(coord_i x) · ⟪v,eᵢa⟫·⟪v,eᵢb⟫`,

and replacing the truncated components by the components themselves reconstructs `g₀ x v v`
(the normalisation `Σ_i ζ_i² = 1` and the orthonormality of the frame `e i`), while the defect
contributes at most `δ · (√c)⁻¹ · card ι₀ · finrank · g₀ x v v` when every component defect is
`≤ δ` on the cube and `dens i ≥ c` on the `σ i`-ball.  This is `seed_lower` below; the main theorem
instantiates it with the uniform defect supplied by `STruncR_R_sub_le_uniform`.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The metric pairing of a vector with itself is nonnegative. -/
lemma seed_inner_nonneg (x : M) (v : TangentSpace I x) : 0 ≤ g₀.inner x v v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact le_of_lt (g₀.pos x v hv)

/-- **The value of `D.J ρ ε g₀.inner` at `(x,v,v)`**, expanded in the Fourier components of the B3
data: the definition of `D.J` combined with `Rstar_apply`. -/
lemma seed_J_eval (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (x : M) (v : TangentSpace I x) :
    (D.J ρ ε g₀.inner) x v v
      = ∑ i : ι₀, (D.ζ i x * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
            * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹)
          * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b)
                (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
              * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x) := by
  simp only [Work.Diff.STE.B3Data.J, Finset.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Work.Diff.STE.B3.Rstar_apply]

/-- **The untruncated components of chart `i` reconstruct `g₀`.**  For every chart `i` and every
`(x, v)`, the contribution of the *untruncated* components `(R_i g₀)_{ab}` of the seed metric,
weighted by the localisation factor of `Rstar`, equals `ζ_i(x)² · g₀(v,v)`. -/
lemma seed_term_id (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (x : M) (v : TangentSpace I x) (i : ι₀) :
    (D.ζ i x * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
        * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹)
      * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
            * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x))
    = (D.ζ i x) ^ 2 * g₀.inner x v v := by
  by_cases hζ : D.ζ i x = 0
  · rw [hζ]
    simp
  · obtain ⟨hsrc, hlt⟩ := D.hζsupp i x hζ
    have hlt2 : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) x‖ ≤ 2 * D.σ i := by
      have := D.hσ i; linarith
    have hpt : D.pt i (Work.Diff.STE.coord (I := I) (D.x₀ i) x) = x := D.pt_coord i hsrc
    have hpt' : (extChartAt I (D.x₀ i)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ i)
        (Work.Diff.STE.coord (I := I) (D.x₀ i) x)) = x := D.pt_coord i hsrc
    have hON : Submission.Diff.IsONFrame g₀ x (fun a => D.e i a x) := by
      have h0 := D.heON i (Work.Diff.STE.coord (I := I) (D.x₀ i) x) hlt2
      rw [hpt'] at h0
      exact h0
    have hχ : D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) x) = 1 :=
      D.hχ1 i _ (le_of_lt hlt)
    have hψ : D.psi i (Work.Diff.STE.coord (I := I) (D.x₀ i) x) = D.ζ i x :=
      D.psi_coord_eq_zeta i hζ
    have hR : ∀ a b : Fin (Module.finrank ℝ E),
        D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
          = D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
              * g₀.inner x (D.e i a x) (D.e i b x) := by
      intro a b
      simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, hψ]
      rw [hpt]
    have hONab : ∀ a b : Fin (Module.finrank ℝ E),
        g₀.inner x (D.e i a x) (D.e i b x) = if a = b then (1 : ℝ) else 0 :=
      fun a b => hON a b
    have hsq : (∑ a : Fin (Module.finrank ℝ E), g₀.inner x v (D.e i a x) ^ 2)
        = g₀.inner x v v := D.sum_inner_sq i hON v
    have h2 : ∀ a b : Fin (Module.finrank ℝ E),
        (D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
            * (if a = b then (1 : ℝ) else 0))
          * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x)
        = D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
          * (g₀.inner x v (D.e i a x)
              * ((if a = b then (1 : ℝ) else 0) * g₀.inner x v (D.e i b x))) := by
      intro a b; ring
    have hsum : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
            * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x))
        = D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
            * (∑ a : Fin (Module.finrank ℝ E), g₀.inner x v (D.e i a x) ^ 2) := by
      calc (∑ a, ∑ b, D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
              * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x))
          = ∑ a, ∑ b, (D.ζ i x
                * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
                * (if a = b then (1 : ℝ) else 0))
              * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x) := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            rw [hR a b, hONab a b]
        _ = ∑ a, D.ζ i x
              * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
              * (g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i a x)) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.sum_congr rfl fun b _ => h2 a b, ← Finset.mul_sum]
            congr 1
            rw [Finset.sum_eq_single a
              (fun b _ hba => by rw [if_neg (Ne.symm hba), zero_mul, mul_zero])
              (fun ha => absurd (Finset.mem_univ a) ha)]
            simp
        _ = D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
              * ∑ a : Fin (Module.finrank ℝ E),
                  (g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i a x)) := by
            rw [Finset.mul_sum]
        _ = D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
              * (∑ a : Fin (Module.finrank ℝ E), g₀.inner x v (D.e i a x) ^ 2) := by
            congr 1
            exact Finset.sum_congr rfl fun a _ => (sq _).symm
    rw [hsum, hχ, hsq]
    have hd : Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)) ≠ 0 := by
      have hpos : 0 < D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x) :=
        dens_pos_of_mem_target D i (D.htarget i _ hlt2)
      exact (Real.sqrt_pos.mpr hpos).ne'
    field_simp

/-- **The defect of chart `i` is small.**  If every component defect is `≤ δ` on the open cube and
`dens i ≥ c` on the `σ i`-ball, then the contribution of the defect of chart `i` to the value
`(D.J ρ ε g₀.inner) x v v` is at most `δ · (√c)⁻¹ · finrank · g₀(v,v)`. -/
lemma seed_term_bound (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε δ c : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hdensb : ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i → c ≤ D.dens i z)
    (hdefect : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (y : Fin (Module.finrank ℝ E) → ℝ),
        (∀ j : Fin (Module.finrank ℝ E), y j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
          |Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b) y
              - D.R i g₀.inner a b y| ≤ δ)
    (x : M) (v : TangentSpace I x) (i : ι₀) :
    |(D.ζ i x * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
        * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹)
      * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b)
              (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
            - D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
          * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x))|
    ≤ δ * (Real.sqrt c)⁻¹ * (Module.finrank ℝ E : ℝ) * g₀.inner x v v := by
  by_cases hζ : D.ζ i x = 0
  · simp only [hζ, zero_mul, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hδ)
      (inv_nonneg.mpr (Real.sqrt_nonneg c))) (by positivity)) (seed_inner_nonneg (g₀ := g₀) x v)
  · obtain ⟨hsrc, hlt⟩ := D.hζsupp i x hζ
    have hlt2 : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) x‖ ≤ 2 * D.σ i := by
      have := D.hσ i; linarith
    have hpt : D.pt i (Work.Diff.STE.coord (I := I) (D.x₀ i) x) = x := D.pt_coord i hsrc
    have hpt' : (extChartAt I (D.x₀ i)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ i)
        (Work.Diff.STE.coord (I := I) (D.x₀ i) x)) = x := D.pt_coord i hsrc
    have hON : Submission.Diff.IsONFrame g₀ x (fun a => D.e i a x) := by
      have h0 := D.heON i (Work.Diff.STE.coord (I := I) (D.x₀ i) x) hlt2
      rw [hpt'] at h0
      exact h0
    have hχ : D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) x) = 1 :=
      D.hχ1 i _ (le_of_lt hlt)
    have hcube : ∀ j : Fin (Module.finrank ℝ E),
        Work.Diff.STE.coord (I := I) (D.x₀ i) x j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
      intro j
      have h1 : |Work.Diff.STE.coord (I := I) (D.x₀ i) x j|
          ≤ ‖Work.Diff.STE.coord (I := I) (D.x₀ i) x‖ := by
        simpa only [Real.norm_eq_abs] using
          norm_le_pi_norm (Work.Diff.STE.coord (I := I) (D.x₀ i) x) j
      have h2 : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) x‖ < (1 / 2 : ℝ) := by
        have h3 := D.hσ2 i; have h4 := D.hσ i; linarith
      exact Set.mem_Ioo.mpr (abs_lt.mp (lt_of_le_of_lt h1 h2))
    have hdens : c ≤ D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x) :=
      hdensb i _ (le_of_lt hlt)
    have hdpos : 0 < D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x) :=
      lt_of_lt_of_le hc hdens
    have hζle : D.ζ i x ≤ 1 := by
      have h1 : (D.ζ i x) ^ 2 ≤ 1 := by
        have h2 := Finset.single_le_sum (f := fun j : ι₀ => (D.ζ j x) ^ 2)
          (fun j _ => sq_nonneg (D.ζ j x)) (Finset.mem_univ i)
        rwa [D.hζsq x] at h2
      nlinarith [D.hζnn i x]
    have hW : |D.ζ i x * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
        * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹|
        ≤ (Real.sqrt c)⁻¹ := by
      rw [hχ, mul_one, abs_of_nonneg (mul_nonneg (D.hζnn i x)
        (inv_nonneg.mpr (Real.sqrt_nonneg _)))]
      have hinv : (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹
          ≤ (Real.sqrt c)⁻¹ :=
        (inv_le_inv₀ (Real.sqrt_pos.mpr hdpos) (Real.sqrt_pos.mpr hc)).mpr
          (Real.sqrt_le_sqrt hdens)
      calc D.ζ i x * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹
          ≤ 1 * (Real.sqrt c)⁻¹ :=
            mul_le_mul hζle hinv (inv_nonneg.mpr (Real.sqrt_nonneg _)) zero_le_one
        _ = (Real.sqrt c)⁻¹ := one_mul _
    have habs : (∑ a : Fin (Module.finrank ℝ E), |g₀.inner x v (D.e i a x)|)
        ≤ Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x v v) :=
      D.sum_abs_inner_le i hON v
    have hsum2 : (∑ a : Fin (Module.finrank ℝ E), |g₀.inner x v (D.e i a x)|) ^ 2
        ≤ (Module.finrank ℝ E : ℝ) * g₀.inner x v v := by
      have h2 : 0 ≤ Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x v v) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have h3 : (∑ a : Fin (Module.finrank ℝ E), |g₀.inner x v (D.e i a x)|) ^ 2
          ≤ (Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x v v)) ^ 2 := by
        nlinarith [habs, h2, Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) =>
          abs_nonneg (g₀.inner x v (D.e i a x)))]
      rw [mul_pow, Real.sq_sqrt (by positivity),
        Real.sq_sqrt (seed_inner_nonneg (g₀ := g₀) x v)] at h3
      exact h3
    have hdef : ∀ a b : Fin (Module.finrank ℝ E),
        |Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b)
              (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
            - D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)| ≤ δ :=
      fun a b => hdefect i a b _ hcube
    have hS : |∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b)
              (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
            - D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
          * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x)|
        ≤ δ * (∑ a : Fin (Module.finrank ℝ E), |g₀.inner x v (D.e i a x)|) ^ 2 := by
      calc |∑ a, ∑ b,
              (Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b)
                  (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
                - D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
              * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x)|
          ≤ ∑ a, ∑ b,
              |(Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b)
                  (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
                - D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
              * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x)| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            refine Finset.sum_le_sum fun a _ => ?_
            exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a, ∑ b,
              δ * (|g₀.inner x v (D.e i a x)| * |g₀.inner x v (D.e i b x)|) := by
            refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
            rw [abs_mul, abs_mul]
            calc |Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b)
                    (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
                  - D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)|
                  * |g₀.inner x v (D.e i a x)| * |g₀.inner x v (D.e i b x)|
                ≤ δ * |g₀.inner x v (D.e i a x)| * |g₀.inner x v (D.e i b x)| :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right (hdef a b) (abs_nonneg _)) (abs_nonneg _)
              _ = δ * (|g₀.inner x v (D.e i a x)| * |g₀.inner x v (D.e i b x)|) := by ring
        _ = δ * (∑ a : Fin (Module.finrank ℝ E), |g₀.inner x v (D.e i a x)|) ^ 2 := by
            have h1 : (∑ a, ∑ b,
                  δ * (|g₀.inner x v (D.e i a x)| * |g₀.inner x v (D.e i b x)|))
                = δ * ∑ a, ∑ b,
                    |g₀.inner x v (D.e i a x)| * |g₀.inner x v (D.e i b x)| := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.mul_sum]
            rw [h1, sq, Finset.sum_mul_sum]
    calc |(D.ζ i x * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
          * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹)
        * (∑ a, ∑ b,
            (Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b)
                (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
              - D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
            * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x))|
        = |D.ζ i x * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
            * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹|
          * |∑ a, ∑ b,
              (Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b)
                  (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
                - D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
              * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x)| := abs_mul _ _
      _ ≤ (Real.sqrt c)⁻¹
          * (δ * (∑ a : Fin (Module.finrank ℝ E), |g₀.inner x v (D.e i a x)|) ^ 2) :=
            mul_le_mul hW hS (abs_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg c))
      _ ≤ (Real.sqrt c)⁻¹
          * (δ * ((Module.finrank ℝ E : ℝ) * g₀.inner x v v)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum2 (le_of_lt hδ))
              (inv_nonneg.mpr (Real.sqrt_nonneg c))
      _ = δ * (Real.sqrt c)⁻¹ * (Module.finrank ℝ E : ℝ) * g₀.inner x v v := by ring

/-- **The seed margin, pointwise form.**  If the component defects of the seed metric are `≤ δ` on
the open cube, `dens i ≥ c` on the `σ i`-ball, and `δ` is small enough
(`δ · (√c)⁻¹ · card ι₀ · finrank ≤ 1/2`), then `J ρ ε g₀.inner` dominates `1/2 g₀` pointwise. -/
theorem seed_lower (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε δ c : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hdensb : ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i → c ≤ D.dens i z)
    (hdefect : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (y : Fin (Module.finrank ℝ E) → ℝ),
        (∀ j : Fin (Module.finrank ℝ E), y j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
          |Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b) y
              - D.R i g₀.inner a b y| ≤ δ)
    (hδK : δ * ((Real.sqrt c)⁻¹ * (Fintype.card ι₀ : ℝ) * (Module.finrank ℝ E : ℝ)) ≤ 1 / 2)
    (x : M) (v : TangentSpace I x) :
    (1 / 2) * g₀.inner x v v ≤ (D.J ρ ε g₀.inner) x v v := by
  have hA := seed_J_eval D ρ ε x v
  have hId : (∑ i : ι₀, (D.ζ i x * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
        * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹)
      * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
            * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x)))
      = g₀.inner x v v := by
    calc (∑ i : ι₀, (D.ζ i x * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
            * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹)
          * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
                * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x)))
        = ∑ i : ι₀, (D.ζ i x) ^ 2 * g₀.inner x v v :=
          Finset.sum_congr rfl fun i _ => seed_term_id D x v i
      _ = (∑ i : ι₀, (D.ζ i x) ^ 2) * g₀.inner x v v := by rw [Finset.sum_mul]
      _ = g₀.inner x v v := by rw [D.hζsq x, one_mul]
  have hSplit : (D.J ρ ε g₀.inner) x v v
      = (∑ i : ι₀, (D.ζ i x * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
            * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹)
          * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
                * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x)))
        + ∑ i : ι₀, (D.ζ i x * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
            * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹)
          * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              (Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b)
                  (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
                - D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
              * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x)) := by
    rw [hA, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hErr : |∑ i : ι₀, (D.ζ i x * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
        * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹)
      * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b)
              (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
            - D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
          * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x))|
      ≤ (1 / 2) * g₀.inner x v v := by
    calc |∑ i : ι₀, (D.ζ i x * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
          * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹)
        * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            (Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b)
                (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
              - D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
            * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x))|
        ≤ ∑ i : ι₀, |(D.ζ i x * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
            * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹)
          * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              (Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b)
                  (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
                - D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
              * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι₀, δ * (Real.sqrt c)⁻¹ * (Module.finrank ℝ E : ℝ) * g₀.inner x v v := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact seed_term_bound D ρ ε δ c hc hδ hdensb hdefect x v i
      _ = (Fintype.card ι₀ : ℝ) * (δ * (Real.sqrt c)⁻¹ * (Module.finrank ℝ E : ℝ)
            * g₀.inner x v v) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (δ * ((Real.sqrt c)⁻¹ * (Fintype.card ι₀ : ℝ) * (Module.finrank ℝ E : ℝ)))
            * g₀.inner x v v := by ring
      _ ≤ (1 / 2) * g₀.inner x v v :=
          mul_le_mul_of_nonneg_right hδK (seed_inner_nonneg (g₀ := g₀) x v)
  rw [hSplit, hId]
  have h2 : -(1 / 2 * g₀.inner x v v)
      ≤ ∑ i : ι₀, (D.ζ i x * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
          * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹)
        * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            (Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b)
                (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
              - D.R i g₀.inner a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
            * g₀.inner x v (D.e i a x) * g₀.inner x v (D.e i b x)) :=
    (abs_le.mp hErr).1
  linarith

theorem seed_margin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (hJT : ∀ (k : ℕ) (h : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h →
      Filter.Tendsto (fun ε => D.BNorm k (D.J ρ ε h - h)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ lam : ℝ, 0 < lam ∧
      ∀ ε ∈ Set.Ioc (0 : ℝ) ε₀, ∀ (x : M) (v : TangentSpace I x),
        lam * g₀.inner x v v ≤ (D.J ρ ε g₀.inner) x v v := by
  classical
  obtain ⟨c, C, hc, hC, hdens⟩ := Work.Diff.STE.B3.dens_bound_sigma D
  have hdensb : ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ D.σ i → c ≤ D.dens i z :=
    fun i z hz => (hdens i z hz).1
  have hdg : ∀ i : ι₀, D.DensGood i := fun i => Work.Diff.STE.B3.densGood_noT2 D i
  have hmat : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (⊤ : ℕ∞) (D.matChart i g₀.inner a b) (extChartAt I (D.x₀ i)).target :=
    fun i a b => Work.Diff.STE.B3.matChart_metric_contDiffOn D i a b
  have hρc : ContinuousAt ρ 0 := hρs.continuous.continuousAt
  set K : ℝ := (Real.sqrt c)⁻¹ * (Fintype.card ι₀ : ℝ) * (Module.finrank ℝ E : ℝ) with hK
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  set δ : ℝ := 1 / (2 * (K + 1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδK : δ * K ≤ 1 / 2 := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (K + 1))]
    nlinarith [hKnn]
  have hdef := Work.Diff.STE.B3.STruncR_R_sub_le_uniform D ρ hρ0 hρ hρc hρ1 hdg hmat δ hδpos
  obtain ⟨ε₀, hε₀pos, hε₀⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) ε₀,
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (y : Fin (Module.finrank ℝ E) → ℝ),
        (∀ j : Fin (Module.finrank ℝ E), y j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
          |Work.Diff.STE.B3Data.STruncR ρ ε (D.R i g₀.inner a b) y
            - D.R i g₀.inner a b y| ≤ δ := by
    rw [eventually_nhdsWithin_iff] at hdef
    rw [Metric.eventually_nhds_iff] at hdef
    obtain ⟨η, hηpos, hη⟩ := hdef
    refine ⟨η / 2, by linarith, fun ε hε => hη ?_ hε.1⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos hε.1]
    linarith [hε.2]
  refine ⟨ε₀, hε₀pos, 1 / 2, by norm_num, ?_⟩
  intro ε hε x v
  refine seed_lower D ρ ε δ c hc hδpos hdensb ?_ ?_ x v
  · intro i a b y hy
    exact hε₀ ε hε i a b y hy
  · rw [← hK]
    exact hδK

end Work.Diff.STE.B3
