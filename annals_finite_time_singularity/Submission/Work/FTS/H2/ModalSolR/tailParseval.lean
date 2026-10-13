import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.EllipticEst.ModalSolution.psiTrunc_pair_identities
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Series.psiTrunc_solves
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.EllipticEst.ModalSolution.EFP.sum_sq_orth_collapse

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR

open scoped Real Topology BigOperators
open MeasureTheory Set Filter
open Work.FTS.PhiStar.Gegenbauer (eFam lam)

/-!
# `tailParseval` — finite Parseval for a *tail* of the mode series

The two diagonal identities of `psiTrunc_pair_identities` are stated for the partial sums over
`Finset.range (N+1)`.  Here we need the same identities for the *tail* `Finset.Icc (M+1) N` of the
mode series, i.e.

* `∫_{Iθ} (Σ_{M<m≤N} a_m e_m)² cos θ = Σ_{M<m≤N} (∫_{Iθ} e_m² cos θ) a_m²`;
* `∫_{Iθ} Lzero (Σ_{M<m≤N} a_m e_m) · (Σ_{M<m≤N} a_m e_m) · cos θ
     = Σ_{M<m≤N} lam m · (∫_{Iθ} e_m² cos θ) · a_m²`.

Both are purely finitary: the finite sums are expanded, the `z`-independent `Lzero` acts
diagonally on the eigenbasis (`Gegenbauer.eFam_Lzero`), and off-diagonal cross terms die by the
orthogonality `Gegenbauer.eFam_orthogonal` (with respect to the weight `cos θ dθ` on
`Iθ = [0, π/2]`).

The two ingredients are proved below for an *arbitrary* finite set of modes
(`eFam_finset_bilin`, `lzero_finset_eFam`); the specialisations to `Finset.Icc (M+1) N` then
give the theorem.  The `tan θ`-term of `Lzero` requires `cos θ ≠ 0`, which on `Iθ` holds except
at the single (null) endpoint `θ = π/2`.
-/

/-! ## Elementary facts about the modes -/

/-- The set integral over `Iθ = [0, π/2]` is the interval integral over `(0, π/2)`. -/
private lemma setIntegral_Iθ_eq_interval (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by
  show (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2), f θ) = _
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le
    (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)).symm

/-- Orthogonality of the modes in the set-integral form over `Iθ` used below. -/
private lemma eFam_orthogonal_Iθ {m n : ℕ} (hmn : m ≠ n) :
    (∫ θ in Work.Spaces.Iθ, eFam m θ * eFam n θ * Real.cos θ) = 0 := by
  rw [setIntegral_Iθ_eq_interval]
  exact Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal m n hmn

/-- `eFam m` is continuous (it is `cos θ · gC (2m+1) (sin θ)`). -/
private lemma continuous_eFam (m : ℕ) : Continuous (eFam m) := by
  have h : eFam m = fun θ : ℝ =>
      Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ) := rfl
  rw [h]
  exact Real.continuous_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp Real.continuous_sin)

/-- `e m θ · e n θ · cos θ` is integrable on `Iθ` (continuous on a compact interval). -/
private lemma integrableOn_eFam_mul (m n : ℕ) :
    IntegrableOn (fun θ => eFam m θ * eFam n θ * Real.cos θ) Work.Spaces.Iθ :=
  ContinuousOn.integrableOn_compact isCompact_Icc
    (((continuous_eFam m).mul (continuous_eFam n)).mul Real.continuous_cos).continuousOn

/-- The only zero of `cos` on `Iθ = [0, π/2]` is the right endpoint. -/
private lemma cos_ne_zero_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (h : θ ≠ Real.pi / 2) : Real.cos θ ≠ 0 := by
  have hlt : θ < Real.pi / 2 := lt_of_le_of_ne hθ.2 h
  exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hlt⟩)

/-- The single point `π/2` is null, so `θ ≠ π/2` holds almost everywhere. -/
private lemma ae_ne_pi_half_volume :
    ∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), θ ≠ Real.pi / 2 := by
  rw [MeasureTheory.ae_iff]
  have h : {θ : ℝ | ¬ θ ≠ Real.pi / 2} = ({Real.pi / 2} : Set ℝ) := by ext θ; simp
  rw [h]
  exact MeasureTheory.measure_singleton _

/-! ## The bilinear finite Parseval identity for an arbitrary finite set of modes -/

/-- **Bilinearity of the `L²(Iθ, cos θ dθ)` pairing of two finite mode sums.**  For any finite set
`s` of modes and any coefficients `a`, `b`, the pairing of `∑_{m ∈ s} a m · e_m` and
`∑_{m ∈ s} b m · e_m` collapses to the diagonal sum `∑_{m ∈ s} (∫ e_m² cos) · a m · b m`. -/
theorem eFam_finset_bilin (s : Finset ℕ) (a b : ℕ → ℝ) :
    (∫ θ in Work.Spaces.Iθ,
        (∑ m ∈ s, a m * eFam m θ) * (∑ m ∈ s, b m * eFam m θ) * Real.cos θ)
      = ∑ m ∈ s,
          (∫ θ in Work.Spaces.Iθ, eFam m θ ^ 2 * Real.cos θ) * a m * b m := by
  -- Step 1: expand the product of the two finite sums into a double sum.
  have hpt : ∀ θ : ℝ, (∑ m ∈ s, a m * eFam m θ) * (∑ m ∈ s, b m * eFam m θ) * Real.cos θ
      = ∑ m ∈ s, ∑ n ∈ s, (a m * b n) * (eFam m θ * eFam n θ * Real.cos θ) := by
    intro θ
    calc (∑ m ∈ s, a m * eFam m θ) * (∑ m ∈ s, b m * eFam m θ) * Real.cos θ
        = (∑ m ∈ s, (a m * eFam m θ) * (∑ n ∈ s, b n * eFam n θ)) * Real.cos θ := by
          rw [Finset.sum_mul]
      _ = ∑ m ∈ s, ((a m * eFam m θ) * (∑ n ∈ s, b n * eFam n θ)) * Real.cos θ := by
          rw [Finset.sum_mul]
      _ = ∑ m ∈ s, ∑ n ∈ s, (a m * b n) * (eFam m θ * eFam n θ * Real.cos θ) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun n _ => ?_
          ring
  -- Step 2: integrate the double sum term by term.
  have hint : ∀ m ∈ s, ∀ n ∈ s,
      IntegrableOn (fun θ => (a m * b n) * (eFam m θ * eFam n θ * Real.cos θ))
        Work.Spaces.Iθ :=
    fun m _ n _ => (integrableOn_eFam_mul m n).const_mul (a m * b n)
  have h1 : (∫ θ in Work.Spaces.Iθ,
        (∑ m ∈ s, a m * eFam m θ) * (∑ m ∈ s, b m * eFam m θ) * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ, ∑ m ∈ s, ∑ n ∈ s,
          (a m * b n) * (eFam m θ * eFam n θ * Real.cos θ) :=
    integral_congr_ae (Eventually.of_forall hpt)
  rw [h1]
  rw [MeasureTheory.integral_finset_sum s
    (fun m hm => MeasureTheory.integrable_finset_sum s (fun n hn => hint m hm n hn))]
  -- Step 3: pull out the constants and collapse each inner sum to its diagonal term.
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MeasureTheory.integral_finset_sum s (fun n hn => hint m hm n hn)]
  have hkey : (∑ n ∈ s, (a m * b n) * (∫ θ in Work.Spaces.Iθ, eFam m θ * eFam n θ
        * Real.cos θ))
      = (∫ θ in Work.Spaces.Iθ, eFam m θ ^ 2 * Real.cos θ) * a m * b m := by
    have hsingle := Finset.sum_eq_single (s := s)
      (f := fun n => (a m * b n) * (∫ θ in Work.Spaces.Iθ, eFam m θ * eFam n θ
        * Real.cos θ)) m
      (fun n _ hnm => by rw [eFam_orthogonal_Iθ (Ne.symm hnm), mul_zero])
      (fun hms => absurd hm hms)
    rw [hsingle]
    have hdiag : (∫ θ in Work.Spaces.Iθ, eFam m θ * eFam m θ * Real.cos θ)
        = ∫ θ in Work.Spaces.Iθ, eFam m θ ^ 2 * Real.cos θ := by
      refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
      ring
    rw [hdiag]
    ring
  rw [Finset.sum_congr rfl (fun n _ => by rw [MeasureTheory.integral_const_mul])]
  exact hkey

/-! ## `Lzero` on an arbitrary finite mode sum -/

/-- `Lzero` applied to a function of `θ` alone: the `z`-variable is irrelevant. -/
private lemma lzero_indep (f : ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero (fun _ θ' => f θ') z θ
      = -(deriv (deriv f) θ) + deriv (fun θ' => Real.tan θ' * f θ') θ - 6 * f θ := by
  simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
    Work.Spaces.pth]

/-- `∂_θ` of a finite sum of modes `θ ↦ ∑ m, a m · e m θ`. -/
private lemma deriv_sum_const_mul (s : Finset ℕ) (a : ℕ → ℝ) (e : ℕ → ℝ → ℝ) (θ : ℝ)
    (he : ∀ m ∈ s, DifferentiableAt ℝ (e m) θ) :
    deriv (fun θ' => ∑ m ∈ s, a m * e m θ') θ = ∑ m ∈ s, a m * deriv (e m) θ := by
  have hfun : (fun θ' : ℝ => ∑ m ∈ s, a m * e m θ')
      = ∑ m ∈ s, (fun θ' : ℝ => a m * e m θ') := by
    funext θ'; rw [Finset.sum_apply]
  rw [hfun, deriv_sum (fun m hm => (he m hm).const_mul (a m))]
  exact Finset.sum_congr rfl fun m hm => deriv_const_mul (a m) (he m hm)

/-- `∂_θ(tan θ · ·)` of a finite sum of modes `θ ↦ ∑ m, a m · e m θ`. -/
private lemma deriv_sum_tan_const_mul (s : Finset ℕ) (a : ℕ → ℝ) (e : ℕ → ℝ → ℝ) (θ : ℝ)
    (hcos : Real.cos θ ≠ 0) (he : ∀ m ∈ s, DifferentiableAt ℝ (e m) θ) :
    deriv (fun θ' => Real.tan θ' * (∑ m ∈ s, a m * e m θ')) θ
      = ∑ m ∈ s, a m * deriv (fun θ' => Real.tan θ' * e m θ') θ := by
  have htan : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr hcos
  have hfun : (fun θ' : ℝ => Real.tan θ' * (∑ m ∈ s, a m * e m θ'))
      = ∑ m ∈ s, (fun θ' : ℝ => Real.tan θ' * (a m * e m θ')) := by
    funext θ'; rw [Finset.sum_apply, Finset.mul_sum]
  have hstep : deriv (∑ m ∈ s, (fun θ' : ℝ => Real.tan θ' * (a m * e m θ'))) θ
      = ∑ m ∈ s, deriv (fun θ' : ℝ => Real.tan θ' * (a m * e m θ')) θ :=
    deriv_sum (fun m hm => htan.mul ((he m hm).const_mul (a m)))
  rw [hfun, hstep]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [show (fun θ' : ℝ => Real.tan θ' * (a m * e m θ'))
      = fun θ' : ℝ => a m * (Real.tan θ' * e m θ') from by funext θ'; ring]
  exact deriv_const_mul (a m) (htan.mul (he m hm))

/-- **`Lzero` on a finite sum of eigenmodes.**  For any finite set `s` of modes, any coefficients
`a` and any `θ` with `cos θ ≠ 0`, the action of `Lzero` on `θ ↦ ∑ m ∈ s, a m · eFam m θ` is the
mode-wise action, with eigenvalue `lam m = 2m(2m+5)`. -/
theorem lzero_finset_eFam (s : Finset ℕ) (a : ℕ → ℝ) (z θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    Work.Elliptic.Lzero (fun _ θ' => ∑ m ∈ s, a m * eFam m θ') z θ
      = ∑ m ∈ s, lam m * a m * eFam m θ := by
  have he : ∀ m ∈ s, ∀ θ' : ℝ, DifferentiableAt ℝ (eFam m) θ' :=
    fun m _ θ' => (Work.FTS.PhiStar.Series.contDiff_eFam m).differentiable (by norm_num)
      |>.differentiableAt
  have he1 : ∀ m ∈ s, DifferentiableAt ℝ (deriv (eFam m)) θ :=
    fun m _ => (ContDiff.deriv' (n := 2) (Work.FTS.PhiStar.Series.contDiff_eFam m)).differentiable
      (by norm_num) |>.differentiableAt
  have h2 : deriv (deriv (fun θ' => ∑ m ∈ s, a m * eFam m θ')) θ
      = ∑ m ∈ s, a m * deriv (deriv (eFam m)) θ := by
    have hf : deriv (fun θ' => ∑ m ∈ s, a m * eFam m θ')
        = fun θ' => ∑ m ∈ s, a m * deriv (eFam m) θ' := by
      funext θ'
      exact deriv_sum_const_mul s a (fun m => eFam m) θ' (fun m hm => he m hm θ')
    rw [hf]
    exact deriv_sum_const_mul s a (fun m => deriv (eFam m)) θ (fun m hm => he1 m hm)
  have h1 : deriv (fun θ' => Real.tan θ' * (∑ m ∈ s, a m * eFam m θ')) θ
      = ∑ m ∈ s, a m * deriv (fun θ' => Real.tan θ' * eFam m θ') θ :=
    deriv_sum_tan_const_mul s a (fun m => eFam m) θ hθ (fun m hm => he m hm θ)
  have hL : Work.Elliptic.Lzero (fun _ θ' => ∑ m ∈ s, a m * eFam m θ') z θ
      = -(∑ m ∈ s, a m * deriv (deriv (eFam m)) θ)
        + (∑ m ∈ s, a m * deriv (fun θ' => Real.tan θ' * eFam m θ') θ)
        - 6 * (∑ m ∈ s, a m * eFam m θ) := by
    rw [lzero_indep]
    rw [h2, h1]
  have hLam : ∀ m ∈ s, deriv (fun θ' => Real.tan θ' * eFam m θ') θ
      - deriv (deriv (eFam m)) θ - 6 * eFam m θ = lam m * eFam m θ := by
    intro m _
    have h6 := lzero_indep (eFam m) z θ
    rw [Work.FTS.PhiStar.Gegenbauer.eFam_Lzero m hθ z] at h6
    linarith [h6]
  rw [hL]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  calc -(a m * deriv (deriv (eFam m)) θ) + a m * deriv (fun θ' => Real.tan θ' * eFam m θ') θ
        - 6 * (a m * eFam m θ)
      = a m * (deriv (fun θ' => Real.tan θ' * eFam m θ') θ - deriv (deriv (eFam m)) θ
          - 6 * eFam m θ) := by ring
    _ = a m * (lam m * eFam m θ) := by rw [hLam m hm]
    _ = lam m * a m * eFam m θ := by ring

/-! ## The target -/

theorem tailParseval (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) {M N : ℕ} (hMN : M ≤ N) :
    ((∫ θ in Work.Spaces.Iθ,
        (∑ m ∈ Finset.Icc (M + 1) N,
          Work.FTS.PhiStar.Series.acoeff α m F z
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ)
      = ∑ m ∈ Finset.Icc (M + 1) N,
          (∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
            * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2)
    ∧ ((∫ θ in Work.Spaces.Iθ,
          Work.Elliptic.Lzero
            (fun _ θ' => ∑ m ∈ Finset.Icc (M + 1) N,
              Work.FTS.PhiStar.Series.acoeff α m F z
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ') 0 θ
            * (∑ m ∈ Finset.Icc (M + 1) N,
              Work.FTS.PhiStar.Series.acoeff α m F z
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Real.cos θ)
      = ∑ m ∈ Finset.Icc (M + 1) N,
          Work.FTS.PhiStar.Gegenbauer.lam m
            * (∫ θ in Work.Spaces.Iθ,
                Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
            * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2) := by
  constructor
  · -- First identity: expand the finite mode sum and use orthogonality of the basis.
    have hcollapse := Work.EllipticEst.ModalSolution.EFP.sum_sq_orth_collapse
      (Finset.Icc (M + 1) N) (fun m => Work.FTS.PhiStar.Series.acoeff α m F z)
      (fun m : ℕ => eFam m) (fun m => continuous_eFam m)
      (fun m _ n _ hmn => eFam_orthogonal_Iθ hmn)
    refine hcollapse.trans ?_
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  · -- Second identity: `Lzero` acts diagonally on the truncated (tail) mode sum.
    have hpt : (∫ θ in Work.Spaces.Iθ,
          Work.Elliptic.Lzero
            (fun _ θ' => ∑ m ∈ Finset.Icc (M + 1) N,
              Work.FTS.PhiStar.Series.acoeff α m F z
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ') 0 θ
            * (∑ m ∈ Finset.Icc (M + 1) N,
              Work.FTS.PhiStar.Series.acoeff α m F z
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Real.cos θ)
        = (∫ θ in Work.Spaces.Iθ,
            (∑ m ∈ Finset.Icc (M + 1) N,
                Work.FTS.PhiStar.Gegenbauer.lam m
                  * Work.FTS.PhiStar.Series.acoeff α m F z
                  * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
              * (∑ m ∈ Finset.Icc (M + 1) N,
                Work.FTS.PhiStar.Series.acoeff α m F z
                  * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Real.cos θ) := by
      refine MeasureTheory.setIntegral_congr_ae ?_ ?_
      · rw [Work.Spaces.Iθ]; exact measurableSet_Icc
      · filter_upwards [ae_ne_pi_half_volume] with θ hθ hθI
        exact congrArg
          (fun t => t * (∑ m ∈ Finset.Icc (M + 1) N,
              Work.FTS.PhiStar.Series.acoeff α m F z
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Real.cos θ)
          (lzero_finset_eFam (Finset.Icc (M + 1) N)
            (fun m => Work.FTS.PhiStar.Series.acoeff α m F z) 0 θ
            (cos_ne_zero_of_mem_Iθ hθI hθ))
    have hbilin := eFam_finset_bilin (Finset.Icc (M + 1) N)
      (fun m => Work.FTS.PhiStar.Gegenbauer.lam m
        * Work.FTS.PhiStar.Series.acoeff α m F z)
      (fun m => Work.FTS.PhiStar.Series.acoeff α m F z)
    exact hpt.trans (hbilin.trans (Finset.sum_congr rfl fun m _ => by ring))

end Work.FTS.H2.ModalSolR
