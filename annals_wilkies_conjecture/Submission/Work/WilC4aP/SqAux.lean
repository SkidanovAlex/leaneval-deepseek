/-
  Work.WilC4aP — auxiliary lemmas for the complex Puiseux theorem (square-free case).
-/
import Mathlib
import Submission.Work.WilC4aP.Basic
import Submission.Work.WilC4aP.SqDefs
import Submission.Work.WilC4aP.exists_local_factorization
import Submission.Work.WilC4aP.prod_eq_of_distinct_roots
import Submission.Work.WilC4aP.exists_root_enum
import Submission.Work.WilC4aP.exists_ball_injective
import Submission.Work.WilC4aP.analytic_bivariate_Pz_eval

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators Topology

namespace Work.WilC4aP

open Polynomial

/-- The left half plane `{w : ℂ | w.re < a}`. -/
def leftHalfPlane (a : ℝ) : Set ℂ := {w : ℂ | w.re < a}

@[simp] lemma mem_leftHalfPlane {a : ℝ} {w : ℂ} : w ∈ leftHalfPlane a ↔ w.re < a := Iff.rfl

/-- Finitely many functions analytic at `0` are analytic on a common disk around `0`. -/
lemma exists_ball_holCoeffs (P : Polynomial (ℂ → ℂ)) (han : HolCoeffs P 0) :
    ∃ r > (0 : ℝ), ∀ z : ℂ, ‖z‖ < r → HolCoeffs P z := by
  have h1 : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ i ∈ Finset.range (P.natDegree + 1),
      AnalyticAt ℂ (P.coeff i) z :=
    eventually_all_finset _ |>.mpr fun i _ => (han i).eventually_analyticAt
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp h1
  refine ⟨r, hr, fun z hz => ?_⟩
  have hz' : z ∈ Metric.ball (0 : ℂ) r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  intro i
  by_cases hi : i ≤ P.natDegree
  · exact hsub hz' i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  · have h0 : P.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [h0]; exact analyticAt_const

/-- Local factorization with pairwise distinct branches: a variant of
`exists_local_factorization` that also produces the pointwise injectivity of the branches. -/
lemma exists_local_factor_distinct {m : ℕ} (P : Polynomial (ℂ → ℂ)) (hmon : P.Monic)
    (hdeg : P.natDegree = m) {z₀ : ℂ} (han : HolCoeffs P z₀)
    (hsep : ∀ w : ℂ, (Pz P z₀).eval w = 0 → (Pz P z₀).derivative.eval w ≠ 0) :
    ∃ (ρ : ℝ) (η : Fin m → ℂ → ℂ), 0 < ρ ∧
      (∀ j, AnalyticOnNhd ℂ (η j) (Metric.ball z₀ ρ)) ∧
      (∀ z ∈ Metric.ball z₀ ρ, Function.Injective fun j => η j z) ∧
      ∀ z ∈ Metric.ball z₀ ρ, Pz P z = ∏ j, (Polynomial.X - Polynomial.C (η j z)) := by
  classical
  obtain ⟨r, hrinj, hroot⟩ := exists_root_enum (monic_Pz hmon z₀)
    (by rw [natDegree_Pz hmon z₀, hdeg]) hsep
  have key : ∀ j : Fin m, ∃ (ζ : ℂ → ℂ) (ρ : ℝ), 0 < ρ ∧
      AnalyticOnNhd ℂ ζ (Metric.ball z₀ ρ) ∧ ζ z₀ = r j ∧
      ∀ z ∈ Metric.ball z₀ ρ, (Pz P z).eval (ζ z) = 0 :=
    fun j => exists_analytic_root_at P han (hroot j) (hsep (r j) (hroot j))
  choose η ρj hρj hηan hη0 hηroot using key
  have hmem : (⋂ j, Metric.ball z₀ (ρj j)) ∈ 𝓝 z₀ :=
    Filter.iInter_mem.mpr fun j => Metric.ball_mem_nhds z₀ (hρj j)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hmem
  have hcont : ∀ j, ContinuousAt (η j) z₀ :=
    fun j => (hηan j).continuousOn.continuousAt (Metric.ball_mem_nhds z₀ (hρj j))
  have hinj0 : Function.Injective fun j => η j z₀ := by
    intro i j hij
    apply hrinj
    rw [← hη0 i, ← hη0 j]
    exact hij
  obtain ⟨ρI, hρI, hinjI⟩ := exists_ball_injective hcont hinj0
  refine ⟨min ε ρI, η, lt_min hε hρI, ?_, ?_, ?_⟩
  · intro j
    exact (hηan j).mono fun z hz =>
      Set.mem_iInter.mp (hεsub (Metric.ball_subset_ball (min_le_left _ _) hz)) j
  · intro z hz
    exact hinjI z (Metric.ball_subset_ball (min_le_right _ _) hz)
  · intro z hz
    exact prod_eq_of_distinct_roots (monic_Pz hmon z) (by rw [natDegree_Pz hmon z, hdeg])
      (hinjI z (Metric.ball_subset_ball (min_le_right _ _) hz))
      (fun j => hηroot j z (Set.mem_iInter.mp
        (hεsub (Metric.ball_subset_ball (min_le_left _ _) hz)) j))

/-- The root space `{(z,Y) : ‖z‖ ≤ r, ‖Y‖ ≤ R, (Pz P z).eval Y = 0}` is compact when all
coefficients of `P` are holomorphic on the closed disk of radius `r`. -/
lemma isCompact_rootSpace_aux (P : Polynomial (ℂ → ℂ)) {r R : ℝ}
    (hcont : ∀ z : ℂ, z ∈ Metric.closedBall (0 : ℂ) r → HolCoeffs P z) :
    IsCompact (RootSpace P r R) := by
  have hK : IsCompact (Metric.closedBall (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) R) :=
    (isCompact_closedBall (0 : ℂ) r).prod (isCompact_closedBall (0 : ℂ) R)
  have hF : ContinuousOn (fun q : ℂ × ℂ => (Pz P q.1).eval q.2)
      (Metric.closedBall (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) R) := fun q hq =>
    (continuousAt_pzEval P (hcont q.1 hq.1) q.2).continuousWithinAt
  have hcl : IsClosed (RootSpace P r R) := by
    have h0 : IsClosed ({(0 : ℂ)} : Set ℂ) := isClosed_singleton
    have h := ContinuousOn.preimage_isClosed_of_isClosed hF
      ((Metric.isClosed_closedBall (x := (0 : ℂ)) (ε := r)).prod
        (Metric.isClosed_closedBall (x := (0 : ℂ)) (ε := R))) h0
    simpa [RootSpace, Set.mem_setOf_eq, Set.preimage] using h
  exact hK.of_isClosed_subset hcl fun q hq => hq.1

/-- **Removable singularity, punctured-ball form.** A function which is complex differentiable on
a punctured ball and bounded there extends to an analytic function on the whole ball. -/
lemma exists_analyticOnNhd_ball_of_bounded_punctured_aux {f : ℂ → ℂ} {ρ B : ℝ} (hρ : 0 < ρ)
    (hdiff : ∀ u ∈ Metric.ball (0 : ℂ) ρ \ {0}, DifferentiableAt ℂ f u)
    (hbdd : ∀ u ∈ Metric.ball (0 : ℂ) ρ \ {0}, ‖f u‖ ≤ B) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball 0 ρ) ∧
      ∀ u ∈ Metric.ball (0 : ℂ) ρ \ {0}, g u = f u := by
  refine ⟨Function.update f 0 (limUnder (𝓝[≠] (0 : ℂ)) f), ?_, ?_⟩
  · refine (Complex.differentiableOn_update_limUnder_of_bddAbove
      (Metric.ball_mem_nhds (0 : ℂ) hρ) ?_ ?_).analyticOnNhd Metric.isOpen_ball
    · intro z hz
      exact (hdiff z hz).differentiableWithinAt
    · refine ⟨B, ?_⟩
      rintro x ⟨y, hy, rfl⟩
      exact hbdd y hy
  · intro u hu
    have hu0 : u ≠ 0 := by simpa using hu.2
    simp [Function.update_apply, hu0]

/-- **The logarithm-composite is analytic.** If `ζ` is analytic on the half-plane
`{w : ℂ | w.re < a}` and periodic with period `N * (2πi)`, then `u ↦ ζ (N * log u)` is analytic at
every nonzero `u₀` for which `N * log u₀` lies in the half-plane.

Indeed, near `u₀` the function `log` may be replaced by the local branch
`l u = log u₀ + log (u / u₀)` (analytic at `u₀`, since `u / u₀` is near `1`, which is not on the
branch cut).  One has `exp (l u) = u = exp (log u)` for `u ≠ 0`, so `l u - log u ∈ 2πi ℤ`, and
`N * (l u - log u) ∈ N * 2πi ℤ` is a multiple of the period; the periodicity, iterated over `ℤ`,
shows `ζ (N * log u) = ζ (N * l u)` near `u₀`. -/
theorem analyticAt_zeta_log_aux {a : ℝ} {ζ : ℂ → ℂ} (hζ : ∀ w : ℂ, w.re < a → AnalyticAt ℂ ζ w)
    {N : ℕ} (hper : ∀ w : ℂ, w.re < a →
      ζ (w + (N : ℂ) * (2 * Real.pi * Complex.I)) = ζ w)
    {u₀ : ℂ} (hu₀ : u₀ ≠ 0) (hval : ((N : ℂ) * Complex.log u₀).re < a) :
    AnalyticAt ℂ (fun u : ℂ => ζ ((N : ℂ) * Complex.log u)) u₀ := by
  classical
  set P : ℂ := (N : ℂ) * (2 * Real.pi * Complex.I) with hP
  have hperP : ∀ w : ℂ, w.re < a → ζ (w + P) = ζ w := by
    intro w hw; simpa [hP] using hper w hw
  have hPre : P.re = 0 := by
    rw [hP, Complex.mul_re]; simp
  have hre_smul : ∀ (n : ℕ), (n • P).re = 0 := by
    intro n; rw [nsmul_eq_mul, Complex.mul_re, hPre]; simp
  have hper_nat : ∀ (n : ℕ) (w : ℂ), w.re < a → ζ (w + n • P) = ζ w := by
    intro n
    induction n with
    | zero => intro w _; simp
    | succ n ih =>
      intro w hw
      have hw' : (w + n • P).re < a := by rw [Complex.add_re, hre_smul n, add_zero]; exact hw
      rw [succ_nsmul, ← add_assoc, hperP (w + n • P) hw', ih w hw]
  have hper_int : ∀ (k : ℤ) (w : ℂ), w.re < a → ζ (w + k • P) = ζ w := by
    intro k w hw
    obtain ⟨n, hk | hk⟩ := Int.eq_nat_or_neg k
    · rw [hk]
      have h : ((n : ℤ) • P) = n • P := by
        rw [zsmul_eq_mul, nsmul_eq_mul]; push_cast; ring
      rw [h]; exact hper_nat n w hw
    · rw [hk]
      have h : ((-(n : ℤ)) • P) = -(n • P) := by
        rw [neg_zsmul, zsmul_eq_mul, nsmul_eq_mul]; push_cast; ring
      rw [h]
      have hwn : (w + -(n • P)).re < a := by
        rw [Complex.add_re, Complex.neg_re, hre_smul n, neg_zero, add_zero]; exact hw
      have hstep : ζ ((w + -(n • P)) + n • P) = ζ (w + -(n • P)) := hper_nat n _ hwn
      have hz : (w + -(n • P)) + n • P = w := by abel
      rw [hz] at hstep
      exact hstep.symm
  have hmem : u₀ / u₀ ∈ Complex.slitPlane := by
    rw [div_self hu₀]; exact Complex.one_mem_slitPlane
  have hlog_an : ∀ z ∈ Complex.slitPlane, AnalyticAt ℂ Complex.log z := by
    intro z hz
    exact (Complex.analyticOnNhd_iff_differentiableOn Complex.isOpen_slitPlane).mpr
      (fun y hy => (Complex.differentiableAt_log hy).differentiableWithinAt) z hz
  have hinner : AnalyticAt ℂ (fun u : ℂ => u / u₀) u₀ :=
    analyticAt_id.mul (analyticAt_const (v := u₀⁻¹))
  have hlogdiv : AnalyticAt ℂ (fun u : ℂ => Complex.log (u / u₀)) u₀ :=
    AnalyticAt.comp (g := Complex.log) (f := fun u : ℂ => u / u₀) (x := u₀)
      (hlog_an (u₀ / u₀) hmem) hinner
  have hl : AnalyticAt ℂ (fun u : ℂ => Complex.log u₀ + Complex.log (u / u₀)) u₀ :=
    (analyticAt_const (v := Complex.log u₀)).add hlogdiv
  have hnl : AnalyticAt ℂ
      (fun u : ℂ => (N : ℂ) * (Complex.log u₀ + Complex.log (u / u₀))) u₀ :=
    (analyticAt_const (v := (N : ℂ))).mul hl
  have hcomp : AnalyticAt ℂ
      (fun u : ℂ => ζ ((N : ℂ) * (Complex.log u₀ + Complex.log (u / u₀)))) u₀ := by
    refine AnalyticAt.comp (g := ζ)
      (f := fun u : ℂ => (N : ℂ) * (Complex.log u₀ + Complex.log (u / u₀))) (x := u₀) ?_ hnl
    have hpt : ((N : ℂ) * (Complex.log u₀ + Complex.log (u₀ / u₀))).re < a := by
      rw [div_self hu₀, Complex.log_one, add_zero]; exact hval
    exact hζ _ hpt
  have hkey : ∀ u : ℂ, u ≠ 0 → ((N : ℂ) * Complex.log u).re < a →
      ζ ((N : ℂ) * Complex.log u)
        = ζ ((N : ℂ) * (Complex.log u₀ + Complex.log (u / u₀))) := by
    intro u hu hlt
    have hexp_l : Complex.exp (Complex.log u₀ + Complex.log (u / u₀)) = u := by
      rw [Complex.exp_add, Complex.exp_log hu₀, Complex.exp_log (div_ne_zero hu hu₀)]
      rw [mul_comm u₀, div_mul_cancel₀ _ hu₀]
    have hexp_eq : Complex.exp (Complex.log u₀ + Complex.log (u / u₀))
        = Complex.exp (Complex.log u) := by
      rw [hexp_l]; exact (Complex.exp_log hu).symm
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp_eq
    have hmul : (N : ℂ) * (Complex.log u₀ + Complex.log (u / u₀))
        = (N : ℂ) * Complex.log u + m • P := by
      calc (N : ℂ) * (Complex.log u₀ + Complex.log (u / u₀))
          = (N : ℂ) * (Complex.log u + (m : ℂ) * (2 * Real.pi * Complex.I)) := by rw [hm]
        _ = (N : ℂ) * Complex.log u + m • P := by rw [hP, zsmul_eq_mul]; ring
    rw [hmul]
    exact (hper_int m ((N : ℂ) * Complex.log u) hlt).symm
  have hcont_re : ContinuousAt (fun u : ℂ => ((N : ℂ) * Complex.log u).re) u₀ := by
    have heq : (fun u : ℂ => ((N : ℂ) * Complex.log u).re)
        = fun u => (N : ℝ) * Real.log ‖u‖ := by
      funext u
      rw [Complex.mul_re, Complex.log_re]
      simp
    rw [heq]
    exact ((Real.continuousAt_log (norm_ne_zero_iff.mpr hu₀)).comp
      continuous_norm.continuousAt).const_mul (N : ℝ)
  refine hcomp.congr ?_
  filter_upwards [hcont_re.preimage_mem_nhds (isOpen_Iio.mem_nhds hval),
    isOpen_ne.mem_nhds hu₀] with u hlt hu
  exact (hkey u hu hlt).symm

end Work.WilC4aP
