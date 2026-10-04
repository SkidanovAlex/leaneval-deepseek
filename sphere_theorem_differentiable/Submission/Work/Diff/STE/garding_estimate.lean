import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.CubeSplit
import Submission.Work.Diff.STE.cube_fubini
import Submission.Work.Diff.STE.pd_integral_zero
import Submission.Work.Diff.STE.pd_fourierExp
import Submission.Work.Diff.STE.fourierCoeff_pd
import Submission.Work.Diff.STE.garding_base
import Submission.Work.Diff.STE.elliptic_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Gårding estimate for a scalar elliptic operator on the torus

`Work.Diff.STE.garding_estimate` is Layer A9 of the STE design (see
`REFS/NOTES_LEAD_P1_STE.md`): for a smooth periodic coefficient matrix `A` on the flat torus
that is elliptic with constant `lam` and whose first derivatives are bounded by `K₁`, the
quadratic form of the operator `u ↦ Σ_{c,d} A_{cd} ∂_c∂_d u` is bounded above by
`-(lam/2)‖∇u‖² + C‖u‖²`.

The proof is the classical one: integrate by parts once,
`⟨A ∂∂u, u⟩ = -∫ A_{cd} ⟨∂_d u, ∂_c u⟩ - ∫ ∂_c A_{cd} ⟨∂_d u, u⟩`,
bound the first (good) term below by `lam Σ ‖∂_i u‖²` using ellipticity, and absorb the
second (first order) term with Young's inequality.
-/

namespace Work.Diff.STE

open MeasureTheory BigOperators

/-- Integration by parts for one summand `A_{cd} ∂_c∂_d u · conj u`: the real part of the
integral is minus the (good) second order term minus the (first order) commutator term. -/
lemma ga_term_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → (ι → ℝ) → ℝ) (c d : ι)
    (hA : ContDiff ℝ 1 (A c d)) (hAper : Periodic1 (A c d))
    (u : (ι → ℝ) → ℂ) (hu : ContDiff ℝ 2 u) (hup : Periodic1 u) :
    Complex.re (∫ x in unitCube, (A c d x : ℂ) * pd c (pd d u) x * star (u x))
      = - (∫ x in unitCube, (pdR c (A c d) x) * Complex.re (pd d u x * star (u x)))
        - (∫ x in unitCube, (A c d x) * Complex.re (pd d u x * star (pd c u x))) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hdd : ContDiff ℝ 1 (pd d u) := ga_contDiff_pd 1 hu d
  have hpc : ContDiff ℝ 1 (pd c u) := ga_contDiff_pd 1 hu c
  have hAd : ContDiff ℝ 1 (fun y : ι → ℝ => (A c d y : ℂ)) := ga_contDiff_ofReal hA
  have hus : ContDiff ℝ 1 (fun y : ι → ℝ => star (u y)) := ga_contDiff_star hu1
  have hf : ContDiff ℝ 1 (fun y : ι → ℝ => (A c d y : ℂ) * star (u y)) := hAd.mul hus
  have hfp : PeriodicIn c (fun y : ι → ℝ => (A c d y : ℂ) * star (u y)) :=
    ga_periodicIn_mul c (ga_periodicIn_ofReal c hAper) (ga_periodicIn_star c hup)
  have hwp : PeriodicIn c (pd d u) := ga_periodicIn_pd c d hup hu1.differentiable_one
  have hibp : (∫ x in unitCube, ((A c d x : ℂ) * star (u x)) * pd c (pd d u) x)
      = - ∫ x in unitCube, pd c (fun y => (A c d y : ℂ) * star (u y)) x * pd d u x :=
    ga_ibp_pd_unitCube c _ _ hf hdd hfp hwp
  have hpd : ∀ x : ι → ℝ, pd c (fun y => (A c d y : ℂ) * star (u y)) x
      = (pdR c (A c d) x : ℂ) * star (u x) + (A c d x : ℂ) * star (pd c u x) := by
    intro x
    rw [pd_mul c (hAd.differentiable_one.differentiableAt)
        (hus.differentiable_one.differentiableAt),
      ga_pd_ofReal c (A c d) x (hA.differentiable_one.differentiableAt),
      ga_pd_star c (hu1.differentiable_one.differentiableAt)]
  have hcontF : Continuous (fun x : ι → ℝ => (A c d x : ℂ) * pd c (pd d u) x * star (u x)) :=
    ((ga_contDiff_ofReal hA).continuous.mul (ga_contDiff_pd 0 hdd c).continuous).mul
      (ga_contDiff_star hu1).continuous
  have hcontG1 : Continuous
      (fun x : ι → ℝ => (pdR c (A c d) x : ℂ) * star (u x) * pd d u x) :=
    ((ga_continuous_ofReal (ga_continuous_pdR hA c)).mul (ga_contDiff_star hu1).continuous).mul
      hdd.continuous
  have hcontG2 : Continuous
      (fun x : ι → ℝ => (A c d x : ℂ) * star (pd c u x) * pd d u x) :=
    ((ga_contDiff_ofReal hA).continuous.mul (ga_contDiff_star hpc).continuous).mul hdd.continuous
  have hL : (∫ x in unitCube, (A c d x : ℂ) * pd c (pd d u) x * star (u x))
      = ∫ x in unitCube, ((A c d x : ℂ) * star (u x)) * pd c (pd d u) x := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hG : (∫ x in unitCube, pd c (fun y => (A c d y : ℂ) * star (u y)) x * pd d u x)
      = (∫ x in unitCube, (pdR c (A c d) x : ℂ) * star (u x) * pd d u x)
        + (∫ x in unitCube, (A c d x : ℂ) * star (pd c u x) * pd d u x) := by
    rw [show (fun x => pd c (fun y => (A c d y : ℂ) * star (u y)) x * pd d u x)
        = fun x => ((pdR c (A c d) x : ℂ) * star (u x) * pd d u x)
            + ((A c d x : ℂ) * star (pd c u x) * pd d u x) from
      funext (fun x => by rw [hpd x]; ring)]
    rw [integral_add (integrableOn_unitCube_of_continuous hcontG1)
      (integrableOn_unitCube_of_continuous hcontG2)]
  have hmain : (∫ x in unitCube, (A c d x : ℂ) * pd c (pd d u) x * star (u x))
      = - ((∫ x in unitCube, (pdR c (A c d) x : ℂ) * star (u x) * pd d u x)
          + (∫ x in unitCube, (A c d x : ℂ) * star (pd c u x) * pd d u x)) := by
    rw [hL, hibp, hG]
  have hre1 : Complex.re (∫ x in unitCube, (pdR c (A c d) x : ℂ) * star (u x) * pd d u x)
      = ∫ x in unitCube, (pdR c (A c d) x) * Complex.re (pd d u x * star (u x)) := by
    rw [ga_re_integral _ (integrableOn_unitCube_of_continuous hcontG1)]
    apply integral_congr_ae
    filter_upwards with x
    rw [show (pdR c (A c d) x : ℂ) * star (u x) * pd d u x
        = (pdR c (A c d) x : ℂ) * (star (u x) * pd d u x) by ring]
    rw [Complex.re_ofReal_mul]
    congr 1
    exact congrArg Complex.re (mul_comm (star (u x)) (pd d u x))
  have hre2 : Complex.re (∫ x in unitCube, (A c d x : ℂ) * star (pd c u x) * pd d u x)
      = ∫ x in unitCube, (A c d x) * Complex.re (pd d u x * star (pd c u x)) := by
    rw [ga_re_integral _ (integrableOn_unitCube_of_continuous hcontG2)]
    apply integral_congr_ae
    filter_upwards with x
    rw [show (A c d x : ℂ) * star (pd c u x) * pd d u x
        = (A c d x : ℂ) * (star (pd c u x) * pd d u x) by ring]
    rw [Complex.re_ofReal_mul]
    congr 1
    exact congrArg Complex.re (mul_comm (star (pd c u x)) (pd d u x))
  rw [hmain, Complex.neg_re, Complex.add_re, hre1, hre2]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Expansion of the quadratic form `L2re (Σ A_{cd} ∂_c∂_d u) u` by integration by parts. -/
lemma ga_operator_identity
    (A : ι → ι → (ι → ℝ) → ℝ) (hA : ∀ c d, ContDiff ℝ 1 (A c d))
    (hAper : ∀ c d, Periodic1 (A c d))
    (u : (ι → ℝ) → ℂ) (hu : ContDiff ℝ 2 u) (hup : Periodic1 u) :
    L2re (fun x => ∑ c, ∑ d, A c d x * pd c (pd d u) x) u
      = - (∑ c, ∑ d, ∫ x in unitCube, (pdR c (A c d) x) * Complex.re (pd d u x * star (u x)))
        - (∑ c, ∑ d, ∫ x in unitCube, (A c d x) * Complex.re (pd d u x * star (pd c u x))) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hcont : ∀ c d, Continuous
      (fun x : ι → ℝ => (A c d x : ℂ) * pd c (pd d u) x * star (u x)) := by
    intro c d
    exact ((ga_contDiff_ofReal (hA c d)).continuous.mul
        (ga_contDiff_pd 0 (ga_contDiff_pd 1 hu d) c).continuous).mul
      (ga_contDiff_star hu1).continuous
  have hsplit : ∀ x : ι → ℝ, (∑ c, ∑ d, A c d x * pd c (pd d u) x) * star (u x)
      = ∑ c, ∑ d, (A c d x : ℂ) * pd c (pd d u) x * star (u x) := by
    intro x
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_mul]
  have hout : (∫ x in unitCube, ∑ c, ∑ d, (A c d x : ℂ) * pd c (pd d u) x * star (u x))
      = ∑ c, ∑ d, ∫ x in unitCube, (A c d x : ℂ) * pd c (pd d u) x * star (u x) := by
    have h1 : (∫ x in unitCube, ∑ c, ∑ d, (A c d x : ℂ) * pd c (pd d u) x * star (u x))
        = ∑ c, ∫ x in unitCube, ∑ d, (A c d x : ℂ) * pd c (pd d u) x * star (u x) := by
      rw [integral_finsetSum]
      intro c _
      exact integrableOn_unitCube_of_continuous (continuous_finsetSum _ (fun d _ => hcont c d))
    rw [h1]
    apply Finset.sum_congr rfl
    intro c _
    rw [integral_finsetSum]
    intro d _
    exact integrableOn_unitCube_of_continuous (hcont c d)
  have hresum : Complex.re (∑ c, ∑ d, ∫ x in unitCube, (A c d x : ℂ) * pd c (pd d u) x * star (u x))
      = ∑ c, ∑ d, Complex.re (∫ x in unitCube, (A c d x : ℂ) * pd c (pd d u) x * star (u x)) := by
    rw [ga_re_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [ga_re_sum]
  have hterm : ∀ c d, Complex.re (∫ x in unitCube, (A c d x : ℂ) * pd c (pd d u) x * star (u x))
      = - (∫ x in unitCube, (pdR c (A c d) x) * Complex.re (pd d u x * star (u x)))
        - (∫ x in unitCube, (A c d x) * Complex.re (pd d u x * star (pd c u x))) :=
    fun c d => ga_term_identity A c d (hA c d) (hAper c d) u hu hup
  have hsum : (∑ c, ∑ d, Complex.re (∫ x in unitCube, (A c d x : ℂ) * pd c (pd d u) x * star (u x)))
      = - (∑ c, ∑ d, ∫ x in unitCube, (pdR c (A c d) x) * Complex.re (pd d u x * star (u x)))
        - (∑ c, ∑ d, ∫ x in unitCube, (A c d x) * Complex.re (pd d u x * star (pd c u x))) := by
    simp only [hterm]
    have inner : ∀ c, (∑ d, (- (∫ x in unitCube, (pdR c (A c d) x) * Complex.re (pd d u x * star (u x)))
          - (∫ x in unitCube, (A c d x) * Complex.re (pd d u x * star (pd c u x)))))
        = -(∑ d, ∫ x in unitCube, (pdR c (A c d) x) * Complex.re (pd d u x * star (u x)))
          - (∑ d, ∫ x in unitCube, (A c d x) * Complex.re (pd d u x * star (pd c u x))) :=
      fun c => ga_sum_neg_sub _ _
    simp only [inner]
    exact ga_sum_neg_sub _ _
  simp only [L2re, hsplit]
  rw [hout, hresum, hsum]

/-- The first order (drift) term of the Gårding estimate is absorbed by `Young`: for any
`ε > 0`, `Σ_{c,d} ∫ ∂_c A_{cd} Re(∂_d u · conj u) ≥ -(K n ε/2)‖∇u‖² - (K n²/(2ε))‖u‖²`
with `n = card ι`. -/
lemma ga_first_order_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → (ι → ℝ) → ℝ) (hA : ∀ c d, ContDiff ℝ 1 (A c d))
    (K : ℝ) (hK : 0 ≤ K) (hK₁ : ∀ c d i x, |pdR i (A c d) x| ≤ K)
    (u : (ι → ℝ) → ℂ) (hu : ContDiff ℝ 2 u) (ε : ℝ) (hε : 0 < ε) :
    -(K * (Fintype.card ι : ℝ) * ε / 2) * (∑ i, ∫ x in unitCube, ‖pd i u x‖ ^ 2)
      - (K * (Fintype.card ι : ℝ) ^ 2 / (2 * ε)) * (∫ x in unitCube, ‖u x‖ ^ 2)
    ≤ ∑ c, ∑ d, ∫ x in unitCube, (pdR c (A c d) x) * Complex.re (pd d u x * star (u x)) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hpc : ∀ i, Continuous (pd i u) := fun i => continuous_pd hu1 i
  have hucont : Continuous u := hu1.continuous
  have hintR : ∀ c d, Integrable
      (fun x : ι → ℝ => (pdR c (A c d) x) * Complex.re (pd d u x * star (u x)))
      (volume.restrict unitCube) := by
    intro c d
    refine ga_integrableOn_unitCube_real ?_
    exact (ga_continuous_pdR (hA c d) c).mul
      (Complex.continuous_re.comp ((hpc d).mul hucont.star))
  have hintL : ∀ d, Integrable
      (fun x : ι → ℝ => -(K * ε / 2) * ‖pd d u x‖ ^ 2 - (K / (2 * ε)) * ‖u x‖ ^ 2)
      (volume.restrict unitCube) := by
    intro d
    refine ga_integrableOn_unitCube_real ?_
    exact (continuous_const.mul ((hpc d).norm.pow 2)).sub
      (continuous_const.mul (hucont.norm.pow 2))
  have hpt : ∀ (c d : ι) (x : ι → ℝ),
      -(K * ε / 2) * ‖pd d u x‖ ^ 2 - (K / (2 * ε)) * ‖u x‖ ^ 2
        ≤ (pdR c (A c d) x) * Complex.re (pd d u x * star (u x)) := by
    intro c d x
    have habs : |Complex.re (pd d u x * star (u x))| ≤ ‖pd d u x‖ * ‖u x‖ := by
      calc |Complex.re (pd d u x * star (u x))| ≤ ‖pd d u x * star (u x)‖ :=
            Complex.abs_re_le_norm _
        _ = ‖pd d u x‖ * ‖star (u x)‖ := norm_mul _ _
        _ = ‖pd d u x‖ * ‖u x‖ := by rw [norm_star]
    have h1 : -(K * (‖pd d u x‖ * ‖u x‖))
        ≤ (pdR c (A c d) x) * Complex.re (pd d u x * star (u x)) := by
      have h2 : -|(pdR c (A c d) x) * Complex.re (pd d u x * star (u x))|
          ≤ (pdR c (A c d) x) * Complex.re (pd d u x * star (u x)) := neg_abs_le _
      rw [abs_mul] at h2
      have h3 : |pdR c (A c d) x| * |Complex.re (pd d u x * star (u x))|
          ≤ K * (‖pd d u x‖ * ‖u x‖) :=
        mul_le_mul (hK₁ c d c x) habs (abs_nonneg _) hK
      linarith
    have h4 : K * (‖pd d u x‖ * ‖u x‖)
        ≤ (K * ε / 2) * ‖pd d u x‖ ^ 2 + (K / (2 * ε)) * ‖u x‖ ^ 2 :=
      ga_young (p := ‖pd d u x‖) (q := ‖u x‖) hK hε
    linarith
  have hmono : ∀ c d, (∫ x in unitCube, -(K * ε / 2) * ‖pd d u x‖ ^ 2 - (K / (2 * ε)) * ‖u x‖ ^ 2)
      ≤ ∫ x in unitCube, (pdR c (A c d) x) * Complex.re (pd d u x * star (u x)) := by
    intro c d
    exact integral_mono (hintL d) (hintR c d) (hpt c d)
  have hsum : (∑ c : ι, ∑ d : ι, ∫ x in unitCube, -(K * ε / 2) * ‖pd d u x‖ ^ 2 - (K / (2 * ε)) * ‖u x‖ ^ 2)
      ≤ ∑ c, ∑ d, ∫ x in unitCube, (pdR c (A c d) x) * Complex.re (pd d u x * star (u x)) := by
    apply Finset.sum_le_sum
    intro c _
    apply Finset.sum_le_sum
    intro d _
    exact hmono c d
  have hd : ∀ d, (∫ x in unitCube, -(K * ε / 2) * ‖pd d u x‖ ^ 2 - (K / (2 * ε)) * ‖u x‖ ^ 2)
      = -((K * ε / 2)) * (∫ x in unitCube, ‖pd d u x‖ ^ 2)
        - ((K / (2 * ε))) * (∫ x in unitCube, ‖u x‖ ^ 2) := by
    intro d
    have h1 : Integrable (fun x : ι → ℝ => -(K * ε / 2) * ‖pd d u x‖ ^ 2)
        (volume.restrict unitCube) :=
      ga_integrableOn_unitCube_real (continuous_const.mul ((hpc d).norm.pow 2))
    have h2 : Integrable (fun x : ι → ℝ => (K / (2 * ε)) * ‖u x‖ ^ 2)
        (volume.restrict unitCube) :=
      ga_integrableOn_unitCube_real (continuous_const.mul (hucont.norm.pow 2))
    rw [integral_sub h1 h2, integral_const_mul, integral_const_mul]
  have hval : (∑ c : ι, ∑ d : ι, ∫ x in unitCube, -(K * ε / 2) * ‖pd d u x‖ ^ 2 - (K / (2 * ε)) * ‖u x‖ ^ 2)
      = -(K * (Fintype.card ι : ℝ) * ε / 2) * (∑ i, ∫ x in unitCube, ‖pd i u x‖ ^ 2)
        - (K * (Fintype.card ι : ℝ) ^ 2 / (2 * ε)) * (∫ x in unitCube, ‖u x‖ ^ 2) := by
    rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => hd d))]
    rw [ga_double_sum_factor (K * ε / 2) (K / (2 * ε)) (∫ x in unitCube, ‖u x‖ ^ 2)
      (fun d => ∫ x in unitCube, ‖pd d u x‖ ^ 2)]
    ring
  rw [hval] at hsum
  exact hsum

theorem garding_estimate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → (ι → ℝ) → ℝ)
    (hA : ∀ c d, ContDiff ℝ (⊤ : ℕ∞) (A c d)) (hAper : ∀ c d, Work.Diff.STE.Periodic1 (A c d))
    (hsym : ∀ c d x, A c d x = A d c x)
    (lam : ℝ) (hlam : 0 < lam)
    (hpos : ∀ x (ξ : ι → ℝ), lam * ∑ i, (ξ i) ^ 2 ≤ ∑ c, ∑ d, A c d x * ξ c * ξ d)
    (K₁ : ℝ) (hK₁ : ∀ c d i x, |Work.Diff.STE.pdR i (A c d) x| ≤ K₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ 2 u → Work.Diff.STE.Periodic1 u →
      Work.Diff.STE.L2re (fun x => ∑ c, ∑ d, A c d x * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) x) u
        ≤ -((lam / 2) * ∑ i, ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pd i u x‖ ^ 2)
          + C * ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖u x‖ ^ 2 := by
  have hA1 : ∀ c d, ContDiff ℝ 1 (A c d) := fun c d => (hA c d).of_le (by simp)
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hnn : 0 ≤ n := by rw [hn]; exact Nat.cast_nonneg _
  set K : ℝ := max K₁ 0 with hKdef
  have hK : 0 ≤ K := by rw [hKdef]; exact le_max_right _ _
  have hK' : ∀ c d i x, |pdR i (A c d) x| ≤ K := by
    intro c d i x; rw [hKdef]; exact le_trans (hK₁ c d i x) (le_max_left _ _)
  set D : ℝ := K * n + 1 with hDdef
  have hD : 0 < D := by rw [hDdef]; nlinarith [hK, hnn]
  set ε : ℝ := lam / D with hεdef
  have hε : 0 < ε := by rw [hεdef]; exact div_pos hlam hD
  set C : ℝ := K * n ^ 2 * D / (2 * lam) with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    exact div_nonneg (mul_nonneg (mul_nonneg hK (sq_nonneg n)) (le_of_lt hD)) (by linarith)
  have ha_eq : K * n * ε / 2 = lam / 2 - lam / (2 * D) := by
    have hDne : D ≠ 0 := ne_of_gt hD
    rw [hεdef]
    field_simp
    ring
  have ha_le : K * n * ε / 2 ≤ lam / 2 := by
    rw [ha_eq]
    have h0 : 0 ≤ lam / (2 * D) := div_nonneg (le_of_lt hlam) (by linarith)
    linarith
  have hb_eq : K * n ^ 2 / (2 * ε) = C := by
    have hDne : D ≠ 0 := ne_of_gt hD
    have hlne : lam ≠ 0 := ne_of_gt hlam
    rw [hεdef, hCdef]
    field_simp
  have hb_le : K * n ^ 2 / (2 * ε) ≤ C := le_of_eq hb_eq
  refine ⟨C, hCnn, fun u hu hup => ?_⟩
  have hop := ga_operator_identity A hA1 (fun c d => hAper c d) u hu hup
  have hell := elliptic_lower A hA lam hpos u hu
  have hfo := ga_first_order_bound A hA1 K hK hK' u hu ε hε
  set S : ℝ := ∑ i, ∫ x in unitCube, ‖pd i u x‖ ^ 2 with hS
  set T : ℝ := ∫ x in unitCube, ‖u x‖ ^ 2 with hT
  set J1 : ℝ := ∑ c : ι, ∑ d : ι,
    ∫ x in unitCube, (pdR c (A c d) x) * Complex.re (pd d u x * star (u x)) with hJ1
  set J2 : ℝ := ∑ c : ι, ∑ d : ι,
    ∫ x in unitCube, (A c d x) * Complex.re (pd d u x * star (pd c u x)) with hJ2
  rw [← hn] at hfo
  have hSnn : 0 ≤ S := by
    rw [hS]; exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => by positivity))
  have hTnn : 0 ≤ T := by
    rw [hT]; exact integral_nonneg (fun x => by positivity)
  have hJ1' : -(lam / 2) * S - C * T ≤ J1 := by
    have ha' : -(lam / 2) * S ≤ -(K * n * ε / 2) * S :=
      mul_le_mul_of_nonneg_right (neg_le_neg ha_le) hSnn
    have hb' : -C * T ≤ -(K * n ^ 2 / (2 * ε)) * T :=
      mul_le_mul_of_nonneg_right (neg_le_neg hb_le) hTnn
    linarith [hfo, ha', hb']
  rw [hop]
  linarith [hJ1', hell]

end Work.Diff.STE
