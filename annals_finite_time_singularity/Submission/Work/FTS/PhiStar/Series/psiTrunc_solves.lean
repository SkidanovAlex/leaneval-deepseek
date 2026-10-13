/-
# `Work.FTS.PhiStar.Series.psiTrunc_solves`

The truncated mode series

  `psiTrunc α F N z θ = ∑_{m ≤ N} acoeff α m F z · e_m(θ)`,
  `acoeff α m F = radGreen α m (cmode m F)`

solves the truncated elliptic equation: for `z > 0` and `0 < θ < π/2`,

  `bslOp α (psiTrunc α F N) z θ = ∑_{m ≤ N} cmode m F z · e_m(θ)`.

**Proof.**  `bslOp α Ψ = -α²z²∂_zzΨ - α(5+α)z∂_zΨ + L₀Ψ` is a linear differential operator, so it
commutes with the finite sum as soon as the summands are differentiable (`deriv` is the totalised
derivative, so this genuinely needs the differentiability lemmas of `radGreen`, supplied by
`radGreenI_differentiableAt`).  For a single mode `Ψ_m(z,θ) = a_m(z)·e_m(θ)` the operator acts
mode-wise (`Work.FTS.PhiStar.Basic`-style computation, redone here):

* `∂_zΨ_m = a_m'·e_m`, `∂_zzΨ_m = a_m''·e_m` (differentiation of a constant multiple),
* `L₀Ψ_m = a_m·L₀e_m = a_m·λ_m·e_m` (`Gegenbauer.eFam_Lzero`, `λ_m = 2m(2m+5)`),

whence `bslOp α Ψ_m = (λ_m a_m - α²z²a_m'' - α(5+α)z a_m')·e_m`, and the bracket is exactly
`cmode m F z` by the defining ODE of `radGreen` (`Radial.radGreen_solves`).  Summing over
`m ≤ N` gives the claim.

The two auxiliary families of lemmas are the differentiation of finite sums of separable terms
(`deriv sum`, `∂_θ`-sum, and their iterates) and the bookkeeping identity that turns
`p·∑A - q·∑B + ((-∑C + ∑D) - r·∑E)` into the sum of the per-mode expressions.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Radial.radGreen_solves
import Submission.Work.FTS.PhiStar.Radial.radGreenIntended
import Submission.Work.FTS.PhiStar.Series.radGreenI_differentiableAt
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

/-! ## Elementary helpers -/

/-- `cos θ ≠ 0` on the open angular interval. -/
lemma cos_ne_zero_of_pos {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) : Real.cos θ ≠ 0 :=
  ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩)

/-- The `radGreen` of `Radial/Defs.lean` is definitionally the intended Green's function. -/
lemma radGreen_eq_radGreenI (α : ℝ) (m : ℕ) (c : ℝ → ℝ) :
    Work.FTS.PhiStar.Radial.radGreen α m c = Work.FTS.PhiStar.Radial.radGreenI α m c := rfl

/-- The angular eigenfunctions are `C³`. -/
lemma contDiff_eFam (m : ℕ) : ContDiff ℝ 3 (Gegenbauer.eFam m) := by
  have h1 : ContDiff ℝ 3 (fun θ : ℝ => Gegenbauer.gC (2 * m + 1) (Real.sin θ)) :=
    (Gegenbauer.contDiff_gC (2 * m + 1)).comp Real.contDiff_sin
  have h2 : ContDiff ℝ 3 (fun θ : ℝ => Real.cos θ) := Real.contDiff_cos
  exact h2.mul h1

/-! ## Differentiation of finite sums of separable terms -/

/-- `∂_z` of a finite sum of separable terms. -/
theorem deriv_sum_sep (s : Finset ℕ) (b e : ℕ → ℝ → ℝ) (θ z : ℝ)
    (hb : ∀ m ∈ s, DifferentiableAt ℝ (b m) z) :
    deriv (fun z' : ℝ => ∑ m ∈ s, b m z' * e m θ) z = ∑ m ∈ s, deriv (b m) z * e m θ := by
  have hfun : (fun z' : ℝ => ∑ m ∈ s, b m z' * e m θ)
      = ∑ m ∈ s, (fun z' : ℝ => b m z' * e m θ) := by
    funext z'; rw [Finset.sum_apply]
  rw [hfun, deriv_sum (fun m hm => (hb m hm).mul_const (e m θ))]
  exact Finset.sum_congr rfl fun m hm => deriv_mul_const (hb m hm) (e m θ)

/-- `∂_θ` of a finite sum of separable terms. -/
theorem deriv_sum_sep_theta (s : Finset ℕ) (b e : ℕ → ℝ → ℝ) (z θ : ℝ)
    (he : ∀ m ∈ s, DifferentiableAt ℝ (e m) θ) :
    deriv (fun θ' : ℝ => ∑ m ∈ s, b m z * e m θ') θ = ∑ m ∈ s, b m z * deriv (e m) θ := by
  have hfun : (fun θ' : ℝ => ∑ m ∈ s, b m z * e m θ')
      = ∑ m ∈ s, (fun θ' : ℝ => b m z * e m θ') := by
    funext θ'; rw [Finset.sum_apply]
  rw [hfun, deriv_sum (fun m hm => (he m hm).const_mul (b m z))]
  exact Finset.sum_congr rfl fun m hm => deriv_const_mul (b m z) (he m hm)

/-- `∂_θ(tan θ · ·)` of a finite sum of separable terms. -/
theorem deriv_sum_tan_sep (s : Finset ℕ) (b e : ℕ → ℝ → ℝ) (z θ : ℝ)
    (hcos : Real.cos θ ≠ 0) (he : ∀ m ∈ s, DifferentiableAt ℝ (e m) θ) :
    deriv (fun θ' : ℝ => Real.tan θ' * (∑ m ∈ s, b m z * e m θ')) θ
      = ∑ m ∈ s, b m z * deriv (fun θ' : ℝ => Real.tan θ' * e m θ') θ := by
  have htan : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr hcos
  have hfun : (fun θ' : ℝ => Real.tan θ' * (∑ m ∈ s, b m z * e m θ'))
      = ∑ m ∈ s, (fun θ' : ℝ => Real.tan θ' * (b m z * e m θ')) := by
    funext θ'
    rw [Finset.sum_apply, Finset.mul_sum]
  have hstep : deriv (∑ m ∈ s, (fun θ' : ℝ => Real.tan θ' * (b m z * e m θ'))) θ
      = ∑ m ∈ s, deriv (fun θ' : ℝ => Real.tan θ' * (b m z * e m θ')) θ :=
    deriv_sum (fun m hm => htan.mul ((he m hm).const_mul (b m z)))
  rw [hfun, hstep]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [show (fun θ' : ℝ => Real.tan θ' * (b m z * e m θ'))
      = fun θ' : ℝ => b m z * (Real.tan θ' * e m θ') from by funext θ'; ring]
  exact deriv_const_mul (b m z) (htan.mul (he m hm))

/-- `∂_zz` of a finite sum of separable terms (with the differentiability of the first derivative
of each coefficient). -/
theorem pzIter_two_sum_sep (s : Finset ℕ) (b e : ℕ → ℝ → ℝ) (θ z : ℝ) (hz : 0 < z)
    (hb : ∀ m ∈ s, ∀ z' : ℝ, 0 < z' → DifferentiableAt ℝ (b m) z')
    (hb1 : ∀ m ∈ s, DifferentiableAt ℝ (deriv (b m)) z) :
    Work.Spaces.pzIter 2 (fun z' θ' => ∑ m ∈ s, b m z' * e m θ') z θ
      = ∑ m ∈ s, deriv (deriv (b m)) z * e m θ := by
  have hev : (fun z' : ℝ => Work.Spaces.pz (fun z' θ' => ∑ m ∈ s, b m z' * e m θ') z' θ)
      =ᶠ[𝓝 z] fun z' : ℝ => ∑ m ∈ s, deriv (b m) z' * e m θ := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact deriv_sum_sep s b e θ z' (fun m hm => hb m hm z' hz')
  change deriv (fun z' : ℝ => Work.Spaces.pz (fun z' θ' => ∑ m ∈ s, b m z' * e m θ') z' θ) z
    = ∑ m ∈ s, deriv (deriv (b m)) z * e m θ
  rw [hev.deriv_eq]
  exact deriv_sum_sep s (fun m => deriv (b m)) e θ z (fun m hm => hb1 m hm)

/-- `∂_θθ` of a finite sum of separable terms. -/
theorem pthIter_two_sum_sep (s : Finset ℕ) (b e : ℕ → ℝ → ℝ) (z θ : ℝ)
    (he : ∀ m ∈ s, ∀ θ' : ℝ, DifferentiableAt ℝ (e m) θ')
    (he1 : ∀ m ∈ s, DifferentiableAt ℝ (deriv (e m)) θ) :
    Work.Spaces.pthIter 2 (fun z' θ' => ∑ m ∈ s, b m z' * e m θ') z θ
      = ∑ m ∈ s, b m z * deriv (deriv (e m)) θ := by
  have hev : (fun θ' : ℝ => Work.Spaces.pth (fun z' θ' => ∑ m ∈ s, b m z' * e m θ') z θ')
      =ᶠ[𝓝 θ] fun θ' : ℝ => ∑ m ∈ s, b m z * deriv (e m) θ' := by
    filter_upwards with θ'
    exact deriv_sum_sep_theta s b e z θ' (fun m hm => he m hm θ')
  change deriv (fun θ' : ℝ => Work.Spaces.pth (fun z' θ' => ∑ m ∈ s, b m z' * e m θ') z θ') θ
    = ∑ m ∈ s, b m z * deriv (deriv (e m)) θ
  rw [hev.deriv_eq]
  exact deriv_sum_sep_theta s b (fun m => deriv (e m)) z θ (fun m hm => he1 m hm)

/-- `∂_θ(tan θ · ·)` of a finite sum of separable terms, in `Work.Spaces.pth` form. -/
theorem pth_tan_sum_sep (s : Finset ℕ) (b e : ℕ → ℝ → ℝ) (z θ : ℝ)
    (hcos : Real.cos θ ≠ 0) (he : ∀ m ∈ s, DifferentiableAt ℝ (e m) θ) :
    Work.Spaces.pth (fun z' θ' => Real.tan θ' * (∑ m ∈ s, b m z' * e m θ')) z θ
      = ∑ m ∈ s, b m z * deriv (fun θ' : ℝ => Real.tan θ' * e m θ') θ := by
  show deriv (fun θ' : ℝ => Real.tan θ' * (∑ m ∈ s, b m z * e m θ')) θ = _
  exact deriv_sum_tan_sep s b e z θ hcos he

/-- The bookkeeping identity distributing a linear combination of finite sums into the sum of the
per-mode linear combinations. -/
theorem sum_lin_comb (s : Finset ℕ) (A B C D E : ℕ → ℝ) (p q r : ℝ) :
    p * (∑ m ∈ s, A m) - q * (∑ m ∈ s, B m)
        + ((-(∑ m ∈ s, C m) + (∑ m ∈ s, D m)) - r * (∑ m ∈ s, E m))
      = ∑ m ∈ s, (p * A m - q * B m + ((-(C m) + D m) - r * E m)) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

/-! ## The truncated series solves the truncated equation -/

theorem psiTrunc_solves (α : ℝ) (hα : 0 < α) (F : ℝ → ℝ → ℝ) (N : ℕ)
    (hc : ∀ m ≤ N, ContinuousOn (fun t => Work.FTS.PhiStar.Series.cmode m F t) (Set.Ioi 0))
    (h0 : ∀ m ≤ N, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m F t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (h0' : ∀ m ≤ N, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m F t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioo 0 1))
    (hinf : ∀ m ≤ N, MeasureTheory.IntegrableOn
      (fun t => Work.FTS.PhiStar.Series.cmode m F t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α (fun z' θ' => Work.FTS.PhiStar.Series.psiTrunc α F N z' θ') z θ
        = ∑ m ∈ Finset.range (N + 1),
            Work.FTS.PhiStar.Series.cmode m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  intro z hz θ hθ hθ2
  have hcos : Real.cos θ ≠ 0 := cos_ne_zero_of_pos hθ hθ2
  have hacoeff : ∀ m : ℕ, acoeff α m F = Work.FTS.PhiStar.Radial.radGreenI α m
      (fun t => cmode m F t) := fun m => rfl
  have hrg : ∀ m : ℕ, acoeff α m F = Work.FTS.PhiStar.Radial.radGreen α m
      (fun t => cmode m F t) := fun m => rfl
  -- smoothness of the angular modes
  have he : ∀ m ∈ Finset.range (N + 1), ∀ θ' : ℝ,
      DifferentiableAt ℝ (Gegenbauer.eFam m) θ' :=
    fun m _ θ' => (contDiff_eFam m).differentiable (by norm_num) |>.differentiableAt
  have heθ : ∀ m ∈ Finset.range (N + 1), DifferentiableAt ℝ (Gegenbauer.eFam m) θ :=
    fun m hm => he m hm θ
  have he1 : ∀ m ∈ Finset.range (N + 1), DifferentiableAt ℝ (deriv (Gegenbauer.eFam m)) θ :=
    fun m _ => (ContDiff.deriv' (n := 2) (contDiff_eFam m)).differentiable (by norm_num)
      |>.differentiableAt
  -- differentiability of the radial modes
  have hcoef : ∀ m ∈ Finset.range (N + 1), ∀ z' : ℝ, 0 < z' →
      DifferentiableAt ℝ (acoeff α m F) z' ∧
        DifferentiableAt ℝ (deriv (acoeff α m F)) z' := by
    intro m hm z' hz'
    have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have h := radGreenI_differentiableAt (α := α) hα m (hc m hmN) (h0 m hmN) (h0' m hmN)
      (hinf m hmN) z' hz'
    rw [hacoeff m]
    exact h
  -- the four derivative identities
  have hpzId : Work.Spaces.pz (fun z' θ' => psiTrunc α F N z' θ') z θ
      = ∑ m ∈ Finset.range (N + 1), deriv (acoeff α m F) z * Gegenbauer.eFam m θ := by
    show deriv (fun z' : ℝ => ∑ m ∈ Finset.range (N + 1),
        acoeff α m F z' * Gegenbauer.eFam m θ) z = _
    exact deriv_sum_sep _ _ _ _ _ (fun m hm => (hcoef m hm z hz).1)
  have hpz2Id : Work.Spaces.pzIter 2 (fun z' θ' => psiTrunc α F N z' θ') z θ
      = ∑ m ∈ Finset.range (N + 1), deriv (deriv (acoeff α m F)) z * Gegenbauer.eFam m θ := by
    show Work.Spaces.pzIter 2 (fun z' θ' => ∑ m ∈ Finset.range (N + 1),
        acoeff α m F z' * Gegenbauer.eFam m θ') z θ = _
    exact pzIter_two_sum_sep _ _ _ _ _ hz (fun m hm z' hz' => (hcoef m hm z' hz').1)
      (fun m hm => (hcoef m hm z hz).2)
  have hpthId : Work.Spaces.pthIter 2 (fun z' θ' => psiTrunc α F N z' θ') z θ
      = ∑ m ∈ Finset.range (N + 1), acoeff α m F z * deriv (deriv (Gegenbauer.eFam m)) θ := by
    show Work.Spaces.pthIter 2 (fun z' θ' => ∑ m ∈ Finset.range (N + 1),
        acoeff α m F z' * Gegenbauer.eFam m θ') z θ = _
    exact pthIter_two_sum_sep _ _ _ _ _ (fun m hm => he m hm) (fun m hm => he1 m hm)
  have htanId : Work.Spaces.pth (fun z' θ' => Real.tan θ' * psiTrunc α F N z' θ') z θ
      = ∑ m ∈ Finset.range (N + 1), acoeff α m F z
          * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ := by
    show Work.Spaces.pth (fun z' θ' => Real.tan θ' * (∑ m ∈ Finset.range (N + 1),
        acoeff α m F z' * Gegenbauer.eFam m θ')) z θ = _
    exact pth_tan_sum_sep _ _ _ _ _ hcos (fun m hm => heθ m hm)
  have hsumId : psiTrunc α F N z θ
      = ∑ m ∈ Finset.range (N + 1), acoeff α m F z * Gegenbauer.eFam m θ := rfl
  have hLzeroId : Work.Elliptic.Lzero (fun z' θ' => psiTrunc α F N z' θ') z θ
      = -(∑ m ∈ Finset.range (N + 1), acoeff α m F z * deriv (deriv (Gegenbauer.eFam m)) θ)
        + (∑ m ∈ Finset.range (N + 1), acoeff α m F z
            * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ)
        - 6 * (∑ m ∈ Finset.range (N + 1), acoeff α m F z * Gegenbauer.eFam m θ) := by
    show -(Work.Spaces.pthIter 2 (fun z' θ' => psiTrunc α F N z' θ') z θ)
      + Work.Spaces.pth (fun z θ' => Real.tan θ' * psiTrunc α F N z θ') z θ
      - 6 * psiTrunc α F N z θ = _
    rw [hpthId, htanId, hsumId]
  rw [Work.Elliptic.bslOp_apply, hpz2Id, hpzId, hLzeroId]
  refine (sum_lin_comb (Finset.range (N + 1))
      (fun m => deriv (deriv (acoeff α m F)) z * Gegenbauer.eFam m θ)
      (fun m => deriv (acoeff α m F) z * Gegenbauer.eFam m θ)
      (fun m => acoeff α m F z * deriv (deriv (Gegenbauer.eFam m)) θ)
      (fun m => acoeff α m F z * deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ)
      (fun m => acoeff α m F z * Gegenbauer.eFam m θ)
      (-(α ^ 2 * z ^ 2)) (α * (5 + α) * z) 6).trans ?_
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hODE := Work.FTS.PhiStar.Radial.radGreen_solves (α := α) hα m (hc m hmN) (h0 m hmN)
    (h0' m hmN) (hinf m hmN) z hz
  -- the angular eigenrelation, in the form used by the linear combination
  have hLam : deriv (fun θ' => Real.tan θ' * Gegenbauer.eFam m θ') θ
      - deriv (deriv (Gegenbauer.eFam m)) θ - 6 * Gegenbauer.eFam m θ
      = Gegenbauer.lam m * Gegenbauer.eFam m θ := by
    have h2 : -(deriv (deriv (Gegenbauer.eFam m)) θ)
        + deriv (fun t : ℝ => Real.tan t * Gegenbauer.eFam m t) θ
        - 6 * Gegenbauer.eFam m θ = Gegenbauer.lam m * Gegenbauer.eFam m θ := by
      have h4 := congrFun (Work.FTS.EllipticEst.Lzero1_eq_Lzero (Gegenbauer.eFam m) z) θ
      rw [Gegenbauer.eFam_Lzero m hcos z] at h4
      simpa only [Work.FTS.EllipticEst.Lzero1] using h4
    linarith [h2]
  have hlam : Work.FTS.PhiStar.Radial.lamR m = Gegenbauer.lam m := rfl
  rw [hrg m]
  rw [← hlam] at hLam
  linear_combination (Gegenbauer.eFam m θ) * hODE
    + (Work.FTS.PhiStar.Radial.radGreen α m (fun t => cmode m F t)) z * hLam

end Work.FTS.PhiStar.Series
