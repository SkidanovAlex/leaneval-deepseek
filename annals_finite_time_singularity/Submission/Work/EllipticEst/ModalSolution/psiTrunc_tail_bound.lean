/-
# `Work.EllipticEst.ModalSolution.psiTrunc_tail_bound`

Tail bound for the truncated modal series `psiTrunc α F N z θ = Σ_{m ≤ N} acoeff α m F z · eFam m θ`.

**Statement.**  For `0 < c < d < π/2` there is `K > 0` such that for all `z, θ ∈ [c,d]`, all
`M ≤ N` and every source `F`,

`|Ψ_N(z,θ) − Ψ_M(z,θ)| ≤ K · √( Σ_{M<m≤N} 𝔄_m a_m² + Σ_{M<m≤N} λ_m 𝔄_m a_m² )`,

where `𝔄_m = ∫_{Iθ} eFam m θ'² cos θ'`, `a_m = acoeff α m F z` and `λ_m = lam m = 2m(2m+5)`.

**Proof (the route hinted at in `NOTES_bslOp_weakSolExistsFts.md`).**  Write
`V := Σ_{M<m≤N} a_m eFam m`, so that `Ψ_N − Ψ_M = V` as functions (a finite reindexing
`Finset.Icc (M+1) N ↔ Finset.range (N+1) \ Finset.range (M+1)`, `sum_Icc_eq_sum_range_sub`) and

* `∫_{Iθ} V² cos θ = P := Σ_{M<m≤N} 𝔄_m a_m²` (finite bilinear Parseval,
  `PTBSupp.finSum_bilin_gen`), and
* `∫_{Iθ} (Lzero V)·V·cos θ = Q := Σ_{M<m≤N} λ_m 𝔄_m a_m²` (`PTBSupp.lzero_finSum_gen` plus the
  same bilinear Parseval).

The cos-weighted energy identity `Lzero1_energy_cos_correct` (middle coefficient `1`, not `1/2`)
then gives `∫_{Iθ} (V')² cos θ = Q − ∫_{Iθ}(V/cos θ)² cos θ + 6P ≤ Q + 6P`.

Finally `abs_le_of_l2_Icc` bounds `|V θ|` by the `L²` norms of `V` and `V'` on `[c,d]`, and
`cos θ ≥ cos d > 0` on `[c,d] ⊆ Iθ` compares those with the `cos`-weighted integrals over `Iθ`
(`intervalIntegral_le_inv_cos_Itheta'`).  No hypothesis on `F` is needed: the argument never looks
inside `acoeff`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.EllipticEst.ModalSolution.PTBSupp
import Submission.Work.EllipticEst.ModalSolution.abs_le_of_l2_Icc
import Submission.Work.EllipticEst.ModalSolution.Lzero1_energy_cos_correct
import Submission.Work.FTS.H2.ModalSol.ModeIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ
local notation "eF" => Work.FTS.PhiStar.Gegenbauer.eFam
local notation "lamF" => Work.FTS.PhiStar.Gegenbauer.lam

/-! ## Three elementary auxiliary facts -/

/-- The tail sum over `Finset.Icc (M+1) N` as a difference of partial sums of `Finset.range`. -/
private lemma sum_Icc_eq_sum_range_sub (f : ℕ → ℝ) {M N : ℕ} (h : M ≤ N) :
    ∑ m ∈ Finset.Icc (M + 1) N, f m
      = ∑ m ∈ Finset.range (N + 1), f m - ∑ m ∈ Finset.range (M + 1), f m := by
  have hI : (Finset.Icc (M + 1) N : Finset ℕ) = Finset.Ico (M + 1) (N + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hI]
  exact Finset.sum_Ico_eq_sub f (Nat.succ_le_succ h)

/-- Two functions agreeing on the open interval `(0, π/2)` agree almost everywhere on
`Iθ = [0, π/2]` (the two endpoints form a null set). -/
private lemma ae_eq_restrict_Iθ_of_eqOn_Ioo {g h : ℝ → ℝ}
    (hgh : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), g θ = h θ) :
    g =ᵐ[volume.restrict Iθ] h := by
  show ∀ᵐ θ ∂(volume.restrict Iθ), g θ = h θ
  rw [MeasureTheory.ae_restrict_iff' (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc),
    MeasureTheory.ae_iff]
  have hset : {x : ℝ | ¬(x ∈ Iθ → g x = h x)} = {x : ℝ | x ∈ Iθ ∧ g x ≠ h x} := by
    ext x; simp only [not_imp]
  rw [hset]
  refine measure_mono_null (t := ({0, Real.pi / 2} : Set ℝ)) ?_ ?_
  · rintro x ⟨hxI, hxg⟩
    simp only [Work.Spaces.Iθ, Set.mem_Icc] at hxI
    rcases eq_or_lt_of_le hxI.1 with h0 | h0
    · exact Or.inl h0.symm
    · rcases eq_or_lt_of_le hxI.2 with h2 | h2
      · exact Or.inr h2
      · exact absurd (hgh x ⟨h0, h2⟩) hxg
  · rw [show ({0, Real.pi / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {Real.pi / 2} from by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
    exact measure_union_null (measure_singleton 0) (measure_singleton (Real.pi / 2))

/-- Comparison of an interval integral over `[c,d] ⊆ Iθ` with the `cos`-weighted set integral over
`Iθ`: because `cos t ≥ cos d > 0` on `[c,d]`, the factor `1/cos d` is the only loss. -/
private lemma intervalIntegral_le_inv_cos_Itheta' (F : ℝ → ℝ) (hF : Continuous F)
    (hF0 : ∀ t, 0 ≤ F t) {c d : ℝ} (hcd : c < d) (hc : 0 < c) (hd : d < Real.pi / 2) :
    (∫ t in c..d, F t) ≤ (1 / Real.cos d) * ∫ t in Iθ, F t * Real.cos t := by
  have hcosd : 0 < Real.cos d :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hc], hd⟩
  have hsub : Set.Ioc c d ⊆ Iθ := by
    intro t ht
    exact ⟨(lt_trans hc ht.1).le, (lt_of_le_of_lt ht.2 hd).le⟩
  have hcos_t : ∀ t ∈ Iθ, 0 ≤ Real.cos t := by
    intro t ht
    rw [Work.Spaces.Iθ] at ht
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, ht.1],
      by linarith [Real.pi_pos, ht.2]⟩
  have hcos_ge : ∀ t ∈ Set.Ioc c d, Real.cos d ≤ Real.cos t := by
    intro t ht
    exact Real.cos_le_cos_of_nonneg_of_le_pi (lt_trans hc ht.1).le
      (by linarith [Real.pi_pos, hd]) ht.2
  have hIntF : IntegrableOn F (Set.Ioc c d) :=
    hF.integrableOn_Icc.mono_set (fun t ht => ⟨ht.1.le, ht.2⟩)
  have hIntFc : IntegrableOn (fun t => F t * Real.cos t) (Set.Ioc c d) :=
    (hF.mul Real.continuous_cos).integrableOn_Icc.mono_set (fun t ht => ⟨ht.1.le, ht.2⟩)
  have hIntIθ : IntegrableOn (fun t => F t * Real.cos t) Iθ :=
    (hF.mul Real.continuous_cos).integrableOn_Icc
  rw [intervalIntegral.integral_of_le hcd.le]
  have hstep1 : (∫ t in Set.Ioc c d, F t)
      ≤ ∫ t in Set.Ioc c d, (1 / Real.cos d) * (F t * Real.cos t) := by
    refine setIntegral_mono_on hIntF (hIntFc.const_mul _) measurableSet_Ioc (fun t ht => ?_)
    have h1 : 1 ≤ Real.cos t / Real.cos d := (one_le_div hcosd).mpr (hcos_ge t ht)
    calc F t = F t * 1 := by ring
      _ ≤ F t * (Real.cos t / Real.cos d) := mul_le_mul_of_nonneg_left h1 (hF0 t)
      _ = (1 / Real.cos d) * (F t * Real.cos t) := by ring
  have hstep2 : (∫ t in Set.Ioc c d, F t * Real.cos t) ≤ ∫ t in Iθ, F t * Real.cos t := by
    refine setIntegral_mono_set hIntIθ ?_ (Filter.Eventually.of_forall (fun t ht => hsub ht))
    show ∀ᵐ t ∂(volume.restrict Iθ), 0 ≤ F t * Real.cos t
    rw [MeasureTheory.ae_restrict_iff' (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
    exact Filter.Eventually.of_forall (fun t ht => mul_nonneg (hF0 t) (hcos_t t ht))
  calc (∫ t in Set.Ioc c d, F t)
      ≤ ∫ t in Set.Ioc c d, (1 / Real.cos d) * (F t * Real.cos t) := hstep1
    _ = (1 / Real.cos d) * ∫ t in Set.Ioc c d, F t * Real.cos t := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ (1 / Real.cos d) * ∫ t in Iθ, F t * Real.cos t :=
        mul_le_mul_of_nonneg_left hstep2 (div_nonneg zero_le_one hcosd.le)

/-! ## The main theorem -/

theorem psiTrunc_tail_bound (α : ℝ) {F : ℝ → ℝ → ℝ} {c d : ℝ} (hcd : c < d) (hc : 0 < c)
    (hd : d < Real.pi / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (z θ : ℝ) (M N : ℕ), θ ∈ Set.Icc c d → M ≤ N →
      |Work.FTS.PhiStar.Series.psiTrunc α F N z θ
          - Work.FTS.PhiStar.Series.psiTrunc α F M z θ|
        ≤ K * Real.sqrt
            ((∑ m ∈ Finset.Icc (M + 1) N,
                (∫ θ' in Work.Spaces.Iθ,
                    Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2 * Real.cos θ')
                  * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2)
              + ∑ m ∈ Finset.Icc (M + 1) N,
                  Work.FTS.PhiStar.Gegenbauer.lam m
                    * (∫ θ' in Work.Spaces.Iθ,
                        Work.FTS.PhiStar.Gegenbauer.eFam m θ' ^ 2 * Real.cos θ')
                    * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2) := by
  have hLpos : 0 < d - c := sub_pos.mpr hcd
  have hcosd : 0 < Real.cos d :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hc], hd⟩
  have hcosd0 : 0 ≤ Real.cos d := hcosd.le
  refine ⟨Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)
      + Real.sqrt (d - c) * Real.sqrt (7 / Real.cos d), ?_, ?_⟩
  · have h1 : 0 < Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c) :=
      div_pos (Real.sqrt_pos_of_pos (div_pos one_pos hcosd)) (Real.sqrt_pos_of_pos hLpos)
    have h2 : 0 ≤ Real.sqrt (d - c) * Real.sqrt (7 / Real.cos d) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    linarith
  intro z θ M N hθ hMN
  -- ## abbreviations
  set s : Finset ℕ := Finset.Icc (M + 1) N with hs
  set P : ℝ := ∑ m ∈ s,
      (∫ t in Iθ, eF m t ^ 2 * Real.cos t)
        * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 with hPdef
  set Q : ℝ := ∑ m ∈ s, lamF m
      * (∫ t in Iθ, eF m t ^ 2 * Real.cos t)
      * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2 with hQdef
  set V : ℝ → ℝ := fun t => ∑ m ∈ s,
      Work.FTS.PhiStar.Series.acoeff α m F z * eF m t with hV
  set K : ℝ := Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)
      + Real.sqrt (d - c) * Real.sqrt (7 / Real.cos d) with hKdef
  have hVeq : ∀ t : ℝ, V t = ∑ m ∈ s,
      Work.FTS.PhiStar.Series.acoeff α m F z * eF m t := fun t => rfl
  -- ## the difference of the partial sums is the tail sum
  have hdiff : ∀ t : ℝ, Work.FTS.PhiStar.Series.psiTrunc α F N z t
      - Work.FTS.PhiStar.Series.psiTrunc α F M z t = V t := by
    intro t
    rw [hVeq t]
    have h2 := sum_Icc_eq_sum_range_sub
      (fun m => Work.FTS.PhiStar.Series.acoeff α m F z * eF m t) hMN
    simp only [Work.FTS.PhiStar.Series.psiTrunc]
    rw [hs]
    exact h2.symm
  -- ## vanishing at the two endpoints
  have hV0 : V 0 = 0 := by
    rw [hVeq]
    simp [Work.FTS.PhiStar.Gegenbauer.eFam, Work.FTS.PhiStar.Gegenbauer.gC_odd_zero]
  have hVpi : V (Real.pi / 2) = 0 := by
    rw [hVeq]
    simp [Work.FTS.PhiStar.Gegenbauer.eFam, Real.cos_pi_div_two]
  -- ## smoothness
  have hVcont : ContDiff ℝ 3 V := by
    rw [hV]
    refine ContDiff.sum (fun m _ => ?_)
    have hcst : ContDiff ℝ 3 (fun _ : ℝ => Work.FTS.PhiStar.Series.acoeff α m F z) :=
      contDiff_const
    exact hcst.mul (Work.FTS.H2.ModalSol.ModeIdent.contDiff_eFam m)
  have hderiv : Continuous (deriv V) := hVcont.continuous_deriv (by norm_num)
  -- ## the pointwise `Lzero` action on the tail sum
  have hLz : ∀ t : ℝ, Work.FTS.EllipticEst.Lzero1 V t
      = Work.Elliptic.Lzero (fun _ θ' => V θ') 0 t := by
    intro t
    simpa using congrArg (fun f : ℝ → ℝ => f t)
      (Work.FTS.EllipticEst.Lzero1_eq_Lzero V 0)
  have hpt : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Elliptic.Lzero (fun _ θ' => V θ') 0 t
        = ∑ m ∈ s, lamF m * Work.FTS.PhiStar.Series.acoeff α m F z * eF m t := by
    intro t ht
    have hcos : Real.cos t ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
    have h1 : (fun (_ : ℝ) θ' => V θ')
        = (fun (_ : ℝ) θ' => ∑ m ∈ s,
            Work.FTS.PhiStar.Series.acoeff α m F z * eF m θ') := by
      funext x θ'
      exact hVeq θ'
    rw [h1]
    exact PTBSupp.lzero_finSum_gen (fun m => Work.FTS.PhiStar.Series.acoeff α m F z) s 0 t hcos
  -- ## the two diagonal pairings
  have hP : (∫ t in Iθ, V t ^ 2 * Real.cos t) = P := by
    rw [hPdef]
    have hsq : (∫ t in Iθ, V t ^ 2 * Real.cos t)
        = ∫ t in Iθ, V t * V t * Real.cos t := by
      refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
      ring
    have hcongr : (∫ t in Iθ, V t * V t * Real.cos t)
        = ∫ t in Iθ,
            (∑ m ∈ s, Work.FTS.PhiStar.Series.acoeff α m F z * eF m t)
              * (∑ m ∈ s, Work.FTS.PhiStar.Series.acoeff α m F z * eF m t)
              * Real.cos t := by
      refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
      simp only [hVeq]
    rw [hsq, hcongr]
    exact (PTBSupp.finSum_bilin_gen (fun m => Work.FTS.PhiStar.Series.acoeff α m F z)
      (fun m => Work.FTS.PhiStar.Series.acoeff α m F z) s).trans
      (Finset.sum_congr rfl (fun m _ => by
        have h1 : (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)
            = (∫ t in Iθ, eF m t ^ 2 * Real.cos t) := rfl
        rw [h1]
        ring))
  have hQ : (∫ t in Iθ, Work.FTS.EllipticEst.Lzero1 V t * V t * Real.cos t) = Q := by
    rw [hQdef]
    have hae : (fun t : ℝ => Work.FTS.EllipticEst.Lzero1 V t * V t * Real.cos t)
        =ᵐ[volume.restrict Iθ]
        (fun t : ℝ =>
            (∑ m ∈ s, lamF m * Work.FTS.PhiStar.Series.acoeff α m F z * eF m t)
              * V t * Real.cos t) := by
      refine ae_eq_restrict_Iθ_of_eqOn_Ioo ?_
      intro t ht
      rw [hLz t, hpt t ht]
    rw [integral_congr_ae hae]
    have h2 : (∫ t in Iθ,
          (∑ m ∈ s, lamF m * Work.FTS.PhiStar.Series.acoeff α m F z * eF m t)
            * V t * Real.cos t)
        = ∫ t in Iθ,
            (∑ m ∈ s, lamF m * Work.FTS.PhiStar.Series.acoeff α m F z * eF m t)
              * (∑ m ∈ s, Work.FTS.PhiStar.Series.acoeff α m F z * eF m t)
              * Real.cos t := by
      refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
      simp only [hVeq]
    rw [h2]
    exact (PTBSupp.finSum_bilin_gen
        (fun m => lamF m * Work.FTS.PhiStar.Series.acoeff α m F z)
        (fun m => Work.FTS.PhiStar.Series.acoeff α m F z) s).trans
      (Finset.sum_congr rfl (fun m _ => by
        have h1 : (∫ θ in Iθ, eF m θ ^ 2 * Real.cos θ)
            = (∫ t in Iθ, eF m t ^ 2 * Real.cos t) := rfl
        rw [h1]
        ring))
  -- ## positivity of the two sums
  have hsig : ∀ m : ℕ, 0 ≤ ∫ t in Iθ, eF m t ^ 2 * Real.cos t := by
    intro m
    refine setIntegral_nonneg measurableSet_Icc (fun t ht => ?_)
    exact mul_nonneg (sq_nonneg _)
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos],
        by linarith [ht.2, Real.pi_pos]⟩)
  have hlam : ∀ m : ℕ, 0 ≤ lamF m := by
    intro m
    rw [Work.FTS.PhiStar.Gegenbauer.lam]
    positivity
  have hP0 : 0 ≤ P := by
    rw [hPdef]
    exact Finset.sum_nonneg (fun m _ => mul_nonneg (hsig m) (sq_nonneg _))
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    exact Finset.sum_nonneg (fun m _ =>
      mul_nonneg (mul_nonneg (hlam m) (hsig m)) (sq_nonneg _))
  -- ## integrability of the four energy integrands
  have hintA : IntegrableOn (fun t => (deriv V t) ^ 2 * Real.cos t) Iθ :=
    ((hderiv.pow 2).mul Real.continuous_cos).integrableOn_Icc
  have hintC : IntegrableOn (fun t => V t ^ 2 * Real.cos t) Iθ :=
    ((hVcont.continuous.pow 2).mul Real.continuous_cos).integrableOn_Icc
  have hUcont : Continuous (fun t : ℝ => ∑ m ∈ s,
      Work.FTS.PhiStar.Series.acoeff α m F z
        * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin t)) :=
    continuous_finsetSum s (fun m _ =>
      ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp
        Real.continuous_sin).const_mul (Work.FTS.PhiStar.Series.acoeff α m F z))
  have hintB : IntegrableOn (fun t => (V t / Real.cos t) ^ 2 * Real.cos t) Iθ := by
    have hnice : IntegrableOn (fun t : ℝ => (∑ m ∈ s,
        Work.FTS.PhiStar.Series.acoeff α m F z
          * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin t)) ^ 2 * Real.cos t) Iθ :=
      ((hUcont.pow 2).mul Real.continuous_cos).integrableOn_Icc
    refine hnice.congr_fun_ae (ae_eq_restrict_Iθ_of_eqOn_Ioo ?_)
    intro t ht
    have hcos : Real.cos t ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
    have hVt : V t = Real.cos t * (∑ m ∈ s,
        Work.FTS.PhiStar.Series.acoeff α m F z
          * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin t)) := by
      rw [hVeq]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      simp only [Work.FTS.PhiStar.Gegenbauer.eFam]
      ring
    rw [hVt, mul_div_cancel_left₀ _ hcos]
  have hScont : Continuous (fun t : ℝ => ∑ m ∈ s, lamF m
      * Work.FTS.PhiStar.Series.acoeff α m F z * eF m t) :=
    continuous_finsetSum s (fun m _ =>
      (Work.FTS.H2.ModalSol.ModeIdent.contDiff_eFam m).continuous.const_mul
        (lamF m * Work.FTS.PhiStar.Series.acoeff α m F z))
  have hintL : IntegrableOn (fun t => Work.FTS.EllipticEst.Lzero1 V t * V t * Real.cos t) Iθ := by
    have hnice : IntegrableOn (fun t : ℝ =>
        (∑ m ∈ s, lamF m * Work.FTS.PhiStar.Series.acoeff α m F z * eF m t)
          * V t * Real.cos t) Iθ :=
      ((hScont.mul hVcont.continuous).mul Real.continuous_cos).integrableOn_Icc
    refine hnice.congr_fun_ae (ae_eq_restrict_Iθ_of_eqOn_Ioo ?_)
    intro t ht
    rw [hLz t, hpt t ht]
  -- ## the weighted energy identity
  have hVcd : ContDiffOn ℝ 2 V (Set.Icc 0 (Real.pi / 2)) :=
    (hVcont.contDiffOn (s := Set.Icc (0 : ℝ) (Real.pi / 2))).of_le (by norm_num)
  have henergy := Lzero1_energy_cos_correct V hVcd hV0 hVpi hintL hintA hintB hintC
  have hBnn : 0 ≤ ∫ t in Iθ, (V t / Real.cos t) ^ 2 * Real.cos t := by
    refine setIntegral_nonneg measurableSet_Icc (fun t ht => ?_)
    exact mul_nonneg (sq_nonneg _)
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos],
        by linarith [ht.2, Real.pi_pos]⟩)
  have hEnergy : (∫ t in Iθ, (deriv V t) ^ 2 * Real.cos t) ≤ Q + 6 * P := by
    rw [hQ, hP] at henergy
    linarith
  -- ## comparison of the `[c,d]` and `Iθ` integrals
  have hIntV : (∫ x in c..d, V x ^ 2) ≤ (1 / Real.cos d) * P :=
    calc (∫ x in c..d, V x ^ 2)
        ≤ (1 / Real.cos d) * ∫ t in Iθ, V t ^ 2 * Real.cos t :=
          intervalIntegral_le_inv_cos_Itheta' (fun x : ℝ => V x ^ 2)
            (hVcont.continuous.pow 2) (fun t => sq_nonneg _) hcd hc hd
      _ = (1 / Real.cos d) * P := by simp only [hP]
  have hIntD : (∫ x in c..d, (deriv V x) ^ 2) ≤ (1 / Real.cos d) * (Q + 6 * P) := by
    have hbase := intervalIntegral_le_inv_cos_Itheta'
      (fun x : ℝ => (deriv V x) ^ 2) (hderiv.pow 2) (fun t => sq_nonneg _) hcd hc hd
    calc (∫ x in c..d, (deriv V x) ^ 2)
        ≤ (1 / Real.cos d) * ∫ t in Iθ, deriv V t ^ 2 * Real.cos t := hbase
      _ ≤ (1 / Real.cos d) * (Q + 6 * P) :=
          mul_le_mul_of_nonneg_left hEnergy (div_nonneg zero_le_one hcosd0)
  -- ## the two square-root bounds
  have hsV : Real.sqrt (∫ x in c..d, V x ^ 2)
      ≤ Real.sqrt (1 / Real.cos d) * Real.sqrt (P + Q) := by
    calc Real.sqrt (∫ x in c..d, V x ^ 2) ≤ Real.sqrt ((1 / Real.cos d) * P) :=
          Real.sqrt_le_sqrt hIntV
      _ = Real.sqrt (1 / Real.cos d) * Real.sqrt P :=
          Real.sqrt_mul (div_nonneg zero_le_one hcosd0) P
      _ ≤ Real.sqrt (1 / Real.cos d) * Real.sqrt (P + Q) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_add_of_nonneg_right hQ0))
            (Real.sqrt_nonneg _)
  have hsD : Real.sqrt (∫ x in c..d, (deriv V x) ^ 2)
      ≤ Real.sqrt (7 / Real.cos d) * Real.sqrt (P + Q) := by
    have h2 : (1 / Real.cos d) * (Q + 6 * P) ≤ (7 / Real.cos d) * (P + Q) := by
      have h3 : Q + 6 * P ≤ 7 * (P + Q) := by linarith
      calc (1 / Real.cos d) * (Q + 6 * P) = (Q + 6 * P) / Real.cos d := by ring
        _ ≤ (7 * (P + Q)) / Real.cos d := div_le_div_of_nonneg_right h3 hcosd0
        _ = (7 / Real.cos d) * (P + Q) := by ring
    calc Real.sqrt (∫ x in c..d, (deriv V x) ^ 2)
        ≤ Real.sqrt ((1 / Real.cos d) * (Q + 6 * P)) := Real.sqrt_le_sqrt hIntD
      _ ≤ Real.sqrt ((7 / Real.cos d) * (P + Q)) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt (7 / Real.cos d) * Real.sqrt (P + Q) :=
          Real.sqrt_mul (div_nonneg (by norm_num) hcosd0) (P + Q)
  have hA : Real.sqrt (∫ x in c..d, V x ^ 2) / Real.sqrt (d - c)
      ≤ (Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)) * Real.sqrt (P + Q) := by
    calc Real.sqrt (∫ x in c..d, V x ^ 2) / Real.sqrt (d - c)
        ≤ (Real.sqrt (1 / Real.cos d) * Real.sqrt (P + Q)) / Real.sqrt (d - c) :=
          div_le_div_of_nonneg_right hsV (Real.sqrt_nonneg _)
      _ = (Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)) * Real.sqrt (P + Q) := by ring
  have hB : Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (deriv V x) ^ 2)
      ≤ (Real.sqrt (d - c) * Real.sqrt (7 / Real.cos d)) * Real.sqrt (P + Q) := by
    calc Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (deriv V x) ^ 2)
        ≤ Real.sqrt (d - c) * (Real.sqrt (7 / Real.cos d) * Real.sqrt (P + Q)) :=
          mul_le_mul_of_nonneg_left hsD (Real.sqrt_nonneg _)
      _ = (Real.sqrt (d - c) * Real.sqrt (7 / Real.cos d)) * Real.sqrt (P + Q) := by ring
  -- ## the one-dimensional `L∞`–`L²` bound
  have hVcd1 : ContDiffOn ℝ 1 V (Set.Icc c d) :=
    (hVcont.contDiffOn (s := Set.Icc c d)).of_le (by norm_num)
  have habs := abs_le_of_l2_Icc V hcd hθ hVcd1
  calc |Work.FTS.PhiStar.Series.psiTrunc α F N z θ
        - Work.FTS.PhiStar.Series.psiTrunc α F M z θ|
      = |V θ| := by rw [hdiff θ]
    _ ≤ Real.sqrt (∫ x in c..d, V x ^ 2) / Real.sqrt (d - c)
          + Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (deriv V x) ^ 2) := habs
    _ ≤ (Real.sqrt (1 / Real.cos d) / Real.sqrt (d - c)) * Real.sqrt (P + Q)
          + (Real.sqrt (d - c) * Real.sqrt (7 / Real.cos d)) * Real.sqrt (P + Q) :=
        add_le_add hA hB
    _ = K * Real.sqrt (P + Q) := by rw [hKdef]; ring

end Work.EllipticEst.ModalSolution
