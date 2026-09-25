/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The basic estimate for `∂̄` with weight

From the Kohn–Morrey identity

  `‖∂̄f‖²_φ + ‖∂̄*_φf‖²_φ = Σ_{j,k} ‖∂̄_k f_j‖²_φ + Σ_{j,k} ∫ (∂_j∂̄_kφ) f_j f̄_k e^{-φ}`

it follows at once that the curvature (complex Hessian) term is dominated by the two `∂̄`-norms:
the first sum on the right is nonnegative.  This is Hörmander's *basic estimate*; for a weight
`φ` with `∂∂̄φ ≥ κ` in the sense of Hermitian forms (`HessLowerBound φ κ`) it reads

  `κ ‖f‖²_{L²_φ} ≤ ‖∂̄f‖²_φ + ‖∂̄*_φf‖²_φ`,

and for the quadratic weight `φ = K‖z‖²` (whose Hessian is `K·δ_{jk}`) the constant is `K`,
arbitrarily large.
-/
import Submission.Work.Hormander.Weights.KohnMorrey
import Submission.Work.Hormander.Weights.HessLowerBound_quadWeight
import Submission.Work.Hormander.Weights.contDiff_quadWeight
import Submission.Work.Hormander.Weights.contDiff_dCoord
import Submission.Work.Hormander.Weights.contDiff_dbarCoord

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.Hormander.Weights

variable {n : ℕ}

lemma normSq0_nonneg (φ : Cn n → ℝ) (u : Form0 n) : 0 ≤ normSq0 φ u :=
  rint_nonneg fun z => sq_nonneg _

lemma normSq1_nonneg (φ : Cn n → ℝ) (f : Form1 n) : 0 ≤ normSq1 φ f :=
  rint_nonneg fun z => Finset.sum_nonneg fun j _ => sq_nonneg _

lemma normSq2_nonneg (φ : Cn n → ℝ) (F : Form2 n) : 0 ≤ normSq2 φ F :=
  rint_nonneg fun z => mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun k _ => sq_nonneg _)

/-- The complex Hessian of a `C²` weight is continuous. -/
lemma continuous_hessPhi {φ : Cn n → ℝ} (hφ : ContDiff ℝ 2 φ) (j k : Fin n) :
    Continuous (fun z => hessPhi n j k φ z) := by
  have h1 : ContDiff ℝ 2 (fun z : Cn n => (φ z : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  have h2 : ContDiff ℝ 1 (fun z => dbarPhi n k φ z) := contDiff_dbarCoord k h1
  have hfd : Continuous (fderiv ℝ (fun z => dbarPhi n k φ z)) :=
    h2.continuous_fderiv (by norm_num)
  have h_eq : (fun z => hessPhi n j k φ z) = fun z => (1 / 2 : ℂ) *
      (fderiv ℝ (fun w => dbarPhi n k φ w) z (evec n j)
        - Complex.I * fderiv ℝ (fun w => dbarPhi n k φ w) z (ivec n j)) := rfl
  rw [h_eq]
  exact continuous_const.mul
    ((hfd.clm_apply continuous_const).sub (continuous_const.mul (hfd.clm_apply continuous_const)))

/-- The curvature term of the Kohn–Morrey identity is bounded below by `κ ‖f‖²_φ`. -/
lemma hessian_term_lower_bound {φ : Cn n → ℝ} {κ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hκ : HessLowerBound φ κ) (f : Form1 n) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (hfs : ∀ j, HasCompactSupport (f j)) :
    κ * normSq1 φ f
      ≤ ∑ j, ∑ k, rpair0 φ (fun z => f j z * hessPhi n j k φ z) (f k) := by
  have hφc : Continuous φ := hφ.continuous
  have hhess : ∀ j k, Continuous (fun z => f j z * hessPhi n j k φ z) := fun j k =>
    (hf j).continuous.mul (continuous_hessPhi hφ j k)
  have hint : ∀ j k, Integrable (fun z =>
      ((f j z * hessPhi n j k φ z) * star (f k z)).re * wn n φ z) := fun j k =>
    integrable_rpair0_integrand_right hφc (hhess j k) ((hf k).continuous) (hfs k)
  have hpt : ∀ z, κ * (∑ j, ‖f j z‖ ^ 2)
      ≤ (∑ j, ∑ k, (f j z * hessPhi n j k φ z) * star (f k z)).re := by
    intro z
    refine le_trans (hκ z (fun j => f j z)) ?_
    have hsum : (∑ i, ∑ j, hessPhi n i j φ z * (f i z * star (f j z)))
        = (∑ j, ∑ k, (f j z * hessPhi n j k φ z) * star (f k z)) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsum]
  -- rewrite the right-hand side as a single weighted integral
  have hR : (∑ j, ∑ k, rpair0 φ (fun z => f j z * hessPhi n j k φ z) (f k))
      = rint φ (fun z => (∑ j, ∑ k, (f j z * hessPhi n j k φ z) * star (f k z)).re) := by
    have hinner : ∀ j, (∑ k, rint φ (fun z =>
          ((f j z * hessPhi n j k φ z) * star (f k z)).re))
        = rint φ (fun z => ∑ k, ((f j z * hessPhi n j k φ z) * star (f k z)).re) := by
      intro j
      rw [rint_sum (s := Finset.univ) (U := fun k z =>
        ((f j z * hessPhi n j k φ z) * star (f k z)).re) (fun k _ => hint j k)]
    calc (∑ j, ∑ k, rpair0 φ (fun z => f j z * hessPhi n j k φ z) (f k))
        = ∑ j, ∑ k, rint φ (fun z =>
            ((f j z * hessPhi n j k φ z) * star (f k z)).re) := rfl
      _ = ∑ j, rint φ (fun z => ∑ k,
            ((f j z * hessPhi n j k φ z) * star (f k z)).re) :=
            Finset.sum_congr rfl fun j _ => hinner j
      _ = rint φ (fun z => ∑ j, ∑ k,
            ((f j z * hessPhi n j k φ z) * star (f k z)).re) := by
            rw [rint_sum (s := Finset.univ) (U := fun j z => ∑ k,
              ((f j z * hessPhi n j k φ z) * star (f k z)).re)
              (fun j _ => integrable_rint_sum Finset.univ (fun k _ => hint j k))]
      _ = rint φ (fun z => (∑ j, ∑ k,
            (f j z * hessPhi n j k φ z) * star (f k z)).re) := by
            congr 1
            funext z
            simp only [Complex.re_sum]
  have hU : Integrable (fun z => (κ * ∑ j, ‖f j z‖ ^ 2) * wn n φ z) := by
    refine integrable_rint_const_mul κ (integrable_rint_sum Finset.univ ?_)
    intro j _
    exact integrable_wn_mul hφc (((hf j).continuous.norm).pow 2)
      ((hfs j).comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp))
  have hV : Integrable (fun z =>
      (∑ j, ∑ k, (f j z * hessPhi n j k φ z) * star (f k z)).re * wn n φ z) := by
    refine (integrable_rint_sum Finset.univ fun j _ =>
      integrable_rint_sum Finset.univ fun k _ => hint j k).congr ?_
    filter_upwards with z
    simp only [Complex.re_sum]
  rw [hR, show normSq1 φ f = rint φ (fun z => ∑ j, ‖f j z‖ ^ 2) from rfl, ← rint_const_mul]
  exact rint_mono hpt hU hV

/-- **The basic estimate** for `∂̄` with a weight `φ ∈ C²` whose complex Hessian dominates
`κ`, in the sense of Hermitian forms. -/
theorem basicEstimate_general {n : ℕ} (φ : Cn n → ℝ) (κ : ℝ) (hφ : ContDiff ℝ 2 φ)
    (hκ : HessLowerBound φ κ) (f : Form1 n) (hf : ∀ j, ContDiff ℝ 2 (f j))
    (hfs : ∀ j, HasCompactSupport (f j)) :
    κ * normSq1 φ f ≤ normSq2 φ (dbarForm f) + normSq0 φ (dbarStar φ f) := by
  rw [kohnMorrey_identity φ f hφ hf hfs]
  have h1 : 0 ≤ ∑ j, ∑ k, normSq0 φ (fun z => dbarCoord n k (f j) z) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => normSq0_nonneg _ _
  have h2 := hessian_term_lower_bound hφ hκ f (fun j => (hf j).of_le (by norm_num)) hfs
  linarith

/-- **The basic estimate for the quadratic weight** `φ = K‖z‖²`, with the sharp constant `K`:
`K ‖f‖²_{L²_φ} ≤ ‖∂̄f‖²_φ + ‖∂̄*_φ f‖²_φ`. -/
theorem basicEstimate_quad {n : ℕ} (K : ℝ) (f : Form1 n) (hf : ∀ j, ContDiff ℝ 2 (f j))
    (hfs : ∀ j, HasCompactSupport (f j)) :
    K * normSq1 (quadWeight n K) f
      ≤ normSq2 (quadWeight n K) (dbarForm f)
        + normSq0 (quadWeight n K) (dbarStar (quadWeight n K) f) :=
  basicEstimate_general (quadWeight n K) K
    ((contDiff_quadWeight (n := n) K).of_le (by simp)) (HessLowerBound_quadWeight K) f hf hfs

end Work.Hormander.Weights
