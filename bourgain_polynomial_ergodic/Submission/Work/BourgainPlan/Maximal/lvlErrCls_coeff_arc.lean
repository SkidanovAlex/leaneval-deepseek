import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_lvl_err_aux
import Submission.Work.BourgainPlan.Maximal.mst_lvl_defs
import Submission.Work.BourgainPlan.Maximal.mst_minor_per_n

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal
open Work.BourgainPlan.IonescuWainger

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))
local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

set_option maxHeartbeats 1000000

/-- `‖mstWeyl P N ξ‖ ≤ 1`: the Weyl kernel is an average of unit complex numbers. -/
lemma lvlErrCls_norm_mstWeyl_le_one (P : Polynomial ℤ) (N : ℕ) (ξ : Circ) :
    ‖mstWeyl P N ξ‖ ≤ 1 := by
  rw [mstWeyl_apply, polyWeylKernel]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hterm : ∀ n : ℕ, ‖Complex.exp (2 * Real.pi * Complex.I *
      ((((iwRep ξ) * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ))‖ = 1 := by
    intro n
    rw [show (2 : ℂ) * Real.pi * Complex.I * (((iwRep ξ) * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)
        = (((2 * Real.pi * (iwRep ξ) * ((P.eval (n : ℤ) : ℤ) : ℝ)) : ℝ) : ℂ) * Complex.I by
          push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  calc ‖(((N : ℝ))⁻¹ : ℂ) * ∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
        ((((iwRep ξ) * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ))‖
      = (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
        ((((iwRep ξ) * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ))‖ := by
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, Nat.abs_cast]
    _ ≤ (N : ℝ)⁻¹ * N := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ‖∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
              ((((iwRep ξ) * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ))‖
            ≤ ∑ n ∈ Finset.range N, ‖Complex.exp (2 * Real.pi * Complex.I *
              ((((iwRep ξ) * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ))‖ := norm_sum_le _ _
          _ = ∑ _n ∈ Finset.range N, (1 : ℝ) := Finset.sum_congr rfl (fun n _ => hterm n)
          _ = N := by simp
    _ = 1 := by field_simp

/-- **The Fourier coefficients of the freezing error of the level-`s` model**: they are the sum
over the level-`s` arcs of the coefficients of the single-arc terms
`(star (G β) − star (m_J ξ))·star (Φ_{2^k}(ξ−β))·η_s(ξ−β)`.

The proof computes the a.e. value of the `L^∞`-class
`ν^s_{2^k} − m_J • Π^s_{2^k}` (`mstNuSCls_coeFn`, `arcSymbolLp_coeFn`,
`khatZMult_coeFn_star_mstWeyl`, `Lp.coeFn_sub`, `Lp.coeFn_lpSMul`), rewrites the integral against
`star (fourier m ·)` as one of those values (`integral_congr_ae`), pushes the finite arc sum out of
the integral (`integral_finsetSum`, each term being bounded by `2M` and a.e. strongly measurable),
and recognises each single-arc integral `∫ (star (G β) − star (m_J ξ))·ψ(ξ−β)·star (fourier m ξ)`
as the Fourier coefficient defining `arcCoeff` (`fourierCoeff_eq_integral_mul_star`). -/
theorem lvlErrCls_coeff_arc (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (J k s : ℕ)
    (M : ℝ) (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hML : MeasureTheory.MemLp (Work.BourgainPlan.Maximal.mstNuS P l d χ η k s) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hηml : MeasureTheory.MemLp (Work.BourgainPlan.Maximal.mstEta d χ η s) ⊤
      (AddCircle.haarAddCircle (T := 1))) (m : ℤ) :
    MeasureTheory.integral (AddCircle.haarAddCircle (T := 1))
        (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
          (((Work.BourgainPlan.Maximal.mstNuSCls P l d χ η k s hML
              - Work.BourgainPlan.Maximal.khatZMult P J •
                Work.BourgainPlan.Maximal.mstPiCls P l d χ η s hηml (2 ^ k) :
              MeasureTheory.Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) :
            Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ * star (fourier m ξ)))
      = ∑ β ∈ Work.BourgainPlan.Maximal.mstLevel l (s + 1) \
            Work.BourgainPlan.Maximal.mstLevel l s,
          Work.BourgainPlan.Maximal.arcCoeff P l d χ η J s k β m := by
  classical
  have hae : (((mstNuSCls P l d χ η k s hML
        - khatZMult P J • mstPiCls P l d χ η s hηml (2 ^ k) :
        Lp ℂ ⊤ haarT) : Circ → ℂ))
      =ᵐ[haarT] fun ξ => ∑ β ∈ mstLevel l (s + 1) \ mstLevel l s,
          (star (mstG P β) - star (mstWeyl P J ξ))
            * (star (mstProf P (2 ^ k) (ξ - β)) * mstEta d χ η s (ξ - β)) := by
    have h1 := mstNuSCls_coeFn P l d χ η k s hML
    have h2 := khatZMult_coeFn_star_mstWeyl P J
    have h3 := arcSymbolLp_coeFn (mstPiBump P d χ η (2 ^ k) s)
      (memLp_mstPiBump P d χ η (2 ^ k) s hηml) (mstLevel l (s + 1) \ mstLevel l s)
    have h4 := Lp.coeFn_sub (mstNuSCls P l d χ η k s hML)
      (khatZMult P J • mstPiCls P l d χ η s hηml (2 ^ k))
    have h5 := Lp.coeFn_lpSMul (r := ⊤) (khatZMult P J)
      (mstPiCls P l d χ η s hηml (2 ^ k))
    filter_upwards [h1, h2, h3, h4, h5] with ξ e1 e2 e3 e4 e5
    rw [e4, Pi.sub_apply, e1, e5]
    simp only [smul_eq_mul]
    rw [Pi.mul_apply, e2, mstPiCls, e3, arcSymbol_apply, mstNuS_apply]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun β hβ => ?_)
    rw [mstPiBump_apply]
    ring
  have hInt : ∀ β ∈ mstLevel l (s + 1) \ mstLevel l s,
      Integrable (fun ξ : Circ => (star (mstG P β) - star (mstWeyl P J ξ))
        * (star (mstProf P (2 ^ k) (ξ - β)) * mstEta d χ η s (ξ - β))
        * star (fourier m ξ)) haarT := by
    intro β hβ
    have hW : AEStronglyMeasurable (fun ξ : Circ => star (mstWeyl P J ξ)) haarT :=
      (Lp.aestronglyMeasurable (khatZMult P J)).congr (khatZMult_coeFn_star_mstWeyl P J)
    have hbdd : ∀ ξ : Circ, ‖(star (mstG P β) - star (mstWeyl P J ξ))
        * (star (mstProf P (2 ^ k) (ξ - β)) * mstEta d χ η s (ξ - β))
        * star (fourier m ξ)‖ ≤ 2 * M := by
      intro ξ
      have hG1 : ‖star (mstG P β) - star (mstWeyl P J ξ)‖ ≤ 2 := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_star, norm_star]
        linarith [mstG_norm_le_one P β, lvlErrCls_norm_mstWeyl_le_one P J ξ]
      have hψ : ‖star (mstProf P (2 ^ k) (ξ - β)) * mstEta d χ η s (ξ - β)‖ ≤ M := by
        rw [norm_mul, norm_star, mstProf_apply]
        have hψ1 : ‖polyProfile P (2 ^ k) (iwRep (ξ - β))‖ ≤ 1 :=
          norm_polyProfile_le_one P _ _
        have hψ2 : ‖mstEta d χ η s (ξ - β)‖ ≤ M := by rw [mstEta_apply]; exact hηbd _
        calc ‖polyProfile P (2 ^ k) (iwRep (ξ - β))‖ * ‖mstEta d χ η s (ξ - β)‖
            ≤ 1 * M := mul_le_mul hψ1 hψ2 (norm_nonneg _) (by norm_num)
          _ = M := one_mul M
      calc ‖(star (mstG P β) - star (mstWeyl P J ξ))
            * (star (mstProf P (2 ^ k) (ξ - β)) * mstEta d χ η s (ξ - β))
            * star (fourier m ξ)‖
          = ‖star (mstG P β) - star (mstWeyl P J ξ)‖
            * ‖star (mstProf P (2 ^ k) (ξ - β)) * mstEta d χ η s (ξ - β)‖ := by
              rw [norm_mul, norm_mul, norm_star, norm_fourier_apply', mul_one]
        _ ≤ 2 * M := mul_le_mul hG1 hψ (norm_nonneg _) (by norm_num)
    refine Integrable.of_bound ?_ _ (Filter.Eventually.of_forall hbdd)
    · have hψ : AEStronglyMeasurable (fun ξ : Circ =>
          star (mstProf P (2 ^ k) (ξ - β)) * mstEta d χ η s (ξ - β)) haarT :=
        (memLp_arcTranslate (memLp_mstPiBump P d χ η (2 ^ k) s hηml) β).aestronglyMeasurable
      exact (((aestronglyMeasurable_const.sub hW)).mul hψ).mul
        ((continuous_star.comp (map_continuous (fourier m))).aestronglyMeasurable)
  have h1 : MeasureTheory.integral haarT
        (fun ξ : Circ => ((mstNuSCls P l d χ η k s hML
              - khatZMult P J • mstPiCls P l d χ η s hηml (2 ^ k) :
              MeasureTheory.Lp ℂ ⊤ haarT) : Circ → ℂ) ξ * star (fourier m ξ))
      = MeasureTheory.integral haarT (fun ξ : Circ =>
          (∑ β ∈ mstLevel l (s + 1) \ mstLevel l s,
            (star (mstG P β) - star (mstWeyl P J ξ))
              * (star (mstProf P (2 ^ k) (ξ - β)) * mstEta d χ η s (ξ - β)))
          * star (fourier m ξ)) :=
    integral_congr_ae (hae.mul (Filter.EventuallyEq.refl _ _))
  rw [h1]
  have h2 : MeasureTheory.integral haarT (fun ξ : Circ =>
          (∑ β ∈ mstLevel l (s + 1) \ mstLevel l s,
            (star (mstG P β) - star (mstWeyl P J ξ))
              * (star (mstProf P (2 ^ k) (ξ - β)) * mstEta d χ η s (ξ - β)))
          * star (fourier m ξ))
      = ∑ β ∈ mstLevel l (s + 1) \ mstLevel l s,
          MeasureTheory.integral haarT (fun ξ : Circ =>
            (star (mstG P β) - star (mstWeyl P J ξ))
              * (star (mstProf P (2 ^ k) (ξ - β)) * mstEta d χ η s (ξ - β))
              * star (fourier m ξ)) := by
    rw [show (fun ξ : Circ => (∑ β ∈ mstLevel l (s + 1) \ mstLevel l s,
            (star (mstG P β) - star (mstWeyl P J ξ))
              * (star (mstProf P (2 ^ k) (ξ - β)) * mstEta d χ η s (ξ - β)))
          * star (fourier m ξ))
        = fun ξ : Circ => ∑ β ∈ mstLevel l (s + 1) \ mstLevel l s,
            (star (mstG P β) - star (mstWeyl P J ξ))
              * (star (mstProf P (2 ^ k) (ξ - β)) * mstEta d χ η s (ξ - β))
              * star (fourier m ξ) by
      funext ξ; rw [Finset.sum_mul]]
    exact integral_finsetSum _ (fun β hβ => hInt β hβ)
  rw [h2]
  refine Finset.sum_congr rfl (fun β hβ => ?_)
  rw [arcCoeff, fourierCoeff_eq_integral_mul_star]
  rfl

end Work.BourgainPlan.Maximal
