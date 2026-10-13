import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.VopAux.SliceTraceDefs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.H2W.sliceEtaPoincare
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad
import Submission.Work.FTS.EllipticEst.Lop_iter_sin_sq_bound
import Submission.Work.FTS.EllipticEst.Lop_iter_cos_eq
import Submission.Work.FTS.EllipticEst.sd_lop_iter_sin_bound
import Submission.Work.FTS.EllSol.VopAux.sliceDerivPointLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.VopAux

/-- `thGam α` is continuous on the open angular interval `(0, π/2)`. -/
private lemma continuousOn_thGam_open (α : ℝ) :
    ContinuousOn (Work.FTS.EllipticEst.thGam α) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  refine hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt ?_))
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-
# The one-dimensional `∂_θ`-Poincaré estimate with boundary *traces*

Same setting as `Work.FTS.EllSol.VopAux.sliceF_le_sliceV` (see that file): `sliceF K α u` is the
angular datum `∫_{Iθ}[(u)²thEta + ∑_{1≤i≤K}(L^i u)²thGam α]`, `L = D_θ = sin(2θ)∂_θ`,
`thEta = sin(2θ)^{-η}`, `thGam α = sin(2θ)^{-γ}`, `γ = 1+α/10`, `η = 99/100`.
`u` is `C^∞` on the OPEN interval `(0,π/2)` with vanishing endpoint LIMITS and the datum
`v = u''` has `∫v²·thEta < ∞` and `∫(L^m v)²·thGam < ∞` for `1 ≤ m ≤ K`.
Claim: `sliceF K α (deriv u) ≤ C_K · sliceF K α v` (uniformly in `α ∈ (0,1]` and `u`), and the
terms of `sliceF K α (deriv u)` are integrable on `Iθ`.

This is the `∂_θ`-case (as opposed to the `∂_θ²`-case of `sliceF_le_sliceV`) and it is NOT
obtained by applying that result to `w = deriv u` (which would produce the datum `w'' = u'''`);
it uses the first-order identity `L(deriv u) = sin(2θ)·v`.

ROUTE. `∫(u')²·thEta ≤ C·∫v²·thEta` (and the integrability of `(u')²·thEta`) is the second
conclusion of `Work.FTS.EllipticEst.H2W.sliceEtaPoincare` (sorry-free) — note `sliceV u = deriv
(deriv u)`, `sEta = thEta` definitionally. For `i ≥ 1`, `L^i(deriv u) = L^{i-1}(s·v)` because
`L(deriv u) = s·deriv(deriv u) = s·v`; expanding this by the iterated Leibniz rule
`Work.FTS.LocData.Lop_iter_mul_eqOn_smooth` (on `U = Set.Ioo 0 (π/2)`, with
`ContDiffOn ℝ Work.Stability.smoothOrder` obtained from the `∀ n` hypothesis via
`contDiffOn_infty.mpr`; the two factors are `fun θ => Real.sin (2*θ)` and `v`) gives
`L^i(deriv u) θ = ∑_{a ≤ i-1} C(i-1,a)·L^a(sin 2·)(θ)·L^{i-1-a}(v)(θ)`, and
`|L^a(sin 2·)(θ)| ≤ C_a·sin 2θ` (`Work.FTS.EllipticEst.sd_lop_iter_sin_bound`). Since
`sin(2θ) ≤ 1` on `Iθ`, the extra factor is harmless. The `a = i-1` term is
`L^{i-1}(sin 2·)(θ)·v θ` with `(L^{i-1}(sin 2·)(θ))² ≤ C·sin²(2θ)`, and
`sin²(2θ)·v²·thGam = v²·sin(2θ)^{2-γ} ≤ v²·thEta` because `2-γ ≥ -η` (uniform for `α ≤ 1`);
so the `m = 0` term is covered by `v²thEta` (integrable by hypothesis) — do NOT use `v²thGam`,
which need not be integrable. For `m ≥ 1` the terms are `(L^m v)²thGam`, integrable by
hypothesis. The resulting pointwise bound is
`(L^i(deriv u) θ)²·thGam α θ ≤ C_i·((v θ)²thEta θ + ∑_{1 ≤ m ≤ i-1}(L^m v θ)²·thGam α θ)`
(obtained via `(L^a(sin 2·)(θ))² ≤ C_a` plus the weight comparisons), and it integrates
directly against `sliceF K α (sliceV u)`. Integrate with
`MeasureTheory.integral_mono_of_nonneg` (a.e. measurability from continuity on `(0,π/2)`),
transporting `Ioo 0 (π/2)` to `Iθ` by `MeasureTheory.Ioo_ae_eq_Icc`, and bound the `i ≤ K` cases
by one constant using `sliceW_mono`/a finite max.
-/
theorem sliceF_deriv_le_sliceV (K : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u : ℝ → ℝ),
    0 < α → α ≤ 1 →
    (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
    Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    MeasureTheory.IntegrableOn (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    (∀ m ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ ∧
      (∀ i ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ)
        Work.Spaces.Iθ) ∧
      Work.FTS.EllSol.VopAux.sliceF K α (deriv u)
        ≤ C * Work.FTS.EllSol.VopAux.sliceF K α (Work.FTS.EllipticEst.sliceV u) := by
  obtain ⟨Cs, hCspos, hCsb⟩ := Work.FTS.EllipticEst.sd_lop_iter_sin_bound K
  have hCs0 : 0 ≤ Cs := le_of_lt hCspos
  obtain ⟨C1, hC1pos, hC1main⟩ := Work.FTS.EllipticEst.H2W.sliceEtaPoincare
  have hM1 : (1 : ℝ) ≤ max 1 (((2 : ℝ) ^ K) ^ 2 * (K : ℝ) ^ 2 * Cs ^ 2) := le_max_left _ _
  have hMpos : (0 : ℝ) < max 1 (((2 : ℝ) ^ K) ^ 2 * (K : ℝ) ^ 2 * Cs ^ 2) :=
    lt_of_lt_of_le zero_lt_one hM1
  refine ⟨C1 + (K : ℝ) * max 1 (((2 : ℝ) ^ K) ^ 2 * (K : ℝ) ^ 2 * Cs ^ 2) + 1, ?_, ?_⟩
  · have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    have hmm : 0 < max 1 (((2 : ℝ) ^ K) ^ 2 * (K : ℝ) ^ 2 * Cs ^ 2) := hMpos
    have hKM : 0 ≤ (K : ℝ) * max 1 (((2 : ℝ) ^ K) ^ 2 * (K : ℝ) ^ 2 * Cs ^ 2) :=
      mul_nonneg hK0 (le_of_lt hmm)
    linarith
  · intro α u hα0 hα1 hu hlim0 hlim1 hint hintK
    set M : ℝ := max 1 (((2 : ℝ) ^ K) ^ 2 * (K : ℝ) ^ 2 * Cs ^ 2) with hM
    have hM0 : 0 ≤ M := by rw [hM]; exact le_of_lt hMpos
    have hrestrict : volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
        = volume.restrict Work.Spaces.Iθ :=
      Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)
    -- (A) the pointwise bound, a.e. on `Iθ`
    have hpt : ∀ i ∈ Finset.Icc 1 K, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ
          ≤ M * sliceW K α (Work.FTS.EllipticEst.sliceV u) θ := by
      intro i hi
      rw [hM, ← hrestrict]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact sliceDerivPointLe hu hCs0 hCsb hα1 hi hθ
    -- (B) integrability of the dominating function
    have hSW : MeasureTheory.IntegrableOn
        (fun θ => sliceW K α (Work.FTS.EllipticEst.sliceV u) θ) Work.Spaces.Iθ := by
      have hsum : MeasureTheory.IntegrableOn (fun θ => ∑ m ∈ Finset.Icc 1 K,
          (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ :=
        MeasureTheory.integrable_finsetSum (Finset.Icc 1 K) hintK
      show MeasureTheory.IntegrableOn (fun θ =>
          (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
          + ∑ m ∈ Finset.Icc 1 K,
              (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
                * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ
      exact hint.add hsum
    have hMSW : MeasureTheory.IntegrableOn
        (fun θ => M * sliceW K α (Work.FTS.EllipticEst.sliceV u) θ) Work.Spaces.Iθ :=
      hSW.const_mul M
    -- (C) smoothness (hence measurability) of the iterates of `L` applied to `deriv u`
    have hsmooth : ∀ i m : ℕ, ContDiffOn ℝ m (Work.FTS.EllipticEst.LopIter i (deriv u))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      intro i
      induction i with
      | zero =>
          intro m
          have h : ContDiffOn ℝ m (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
            ContDiffOn.deriv_of_isOpen (m := ((m : ℕ) : WithTop ℕ∞))
              (n := ((m + 1 : ℕ) : WithTop ℕ∞)) (hu (m + 1)) isOpen_Ioo
              (by exact_mod_cast le_refl (m + 1))
          simpa only [Work.FTS.EllipticEst.LopIter_zero] using h
      | succ n ih =>
          intro m
          have h1 : ContDiffOn ℝ (m + 1) (Work.FTS.EllipticEst.LopIter n (deriv u))
              (Set.Ioo (0 : ℝ) (Real.pi / 2)) := ih (m + 1)
          have h2 : ContDiffOn ℝ m (deriv (Work.FTS.EllipticEst.LopIter n (deriv u)))
              (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
            ContDiffOn.deriv_of_isOpen (m := ((m : ℕ) : WithTop ℕ∞))
              (n := ((m + 1 : ℕ) : WithTop ℕ∞)) h1 isOpen_Ioo
              (by exact_mod_cast le_refl (m + 1))
          have hsin : ContDiffOn ℝ m (fun θ : ℝ => Real.sin (2 * θ))
              (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by fun_prop
          have hL : Work.FTS.EllipticEst.LopIter (n + 1) (deriv u)
              = fun θ : ℝ => Real.sin (2 * θ)
                  * deriv (Work.FTS.EllipticEst.LopIter n (deriv u)) θ := by
            rw [Work.FTS.EllipticEst.LopIter_succ]; rfl
          rw [hL]
          simpa only [Pi.mul_apply] using hsin.mul h2
    have hmeas : ∀ i : ℕ, AEStronglyMeasurable
        (fun θ => (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) (volume.restrict Work.Spaces.Iθ) := by
      intro i
      rw [← hrestrict]
      exact (((hsmooth i 1).continuousOn.pow 2).mul (continuousOn_thGam_open α))
        |>.aestronglyMeasurable measurableSet_Ioo
    -- (D) integrability of the single terms
    have hLint : ∀ i ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
        (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ := by
      intro i hi
      refine Integrable.mono' hMSW (hmeas i) ?_
      filter_upwards [hpt i hi, ae_restrict_mem measurableSet_Icc] with θ hb hmem
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hmem))]
      exact hb
    -- (E) the integral bounds of the single terms
    have hIle : ∀ i ∈ Finset.Icc 1 K,
        (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ)
          ≤ M * sliceF K α (Work.FTS.EllipticEst.sliceV u) := by
      intro i hi
      calc (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
              * Work.FTS.EllipticEst.thGam α θ)
          ≤ ∫ θ in Work.Spaces.Iθ, M * sliceW K α (Work.FTS.EllipticEst.sliceV u) θ :=
            integral_mono_ae (hLint i hi) hMSW (hpt i hi)
        _ = M * sliceF K α (Work.FTS.EllipticEst.sliceV u) := by
            rw [sliceF, MeasureTheory.integral_const_mul]
    -- (F) the `sliceEtaPoincare` consequences
    obtain ⟨hu2int, hderivInt, _hu2le, hderivLe⟩ := hC1main u hu hlim0 hlim1 hint
    have hdInt : MeasureTheory.IntegrableOn
        (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := hderivInt
    have hVle : (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.sliceV u θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        ≤ sliceF K α (Work.FTS.EllipticEst.sliceV u) := by
      rw [sliceF]
      refine integral_mono_of_nonneg ?_ hSW ?_
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        show (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
          ≤ sliceW K α (Work.FTS.EllipticEst.sliceV u) θ
        rw [sliceW]
        exact le_add_of_nonneg_right (Finset.sum_nonneg fun m _ =>
          mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hθ))
    have hderivBound : (∫ θ in Work.Spaces.Iθ,
          (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ C1 * sliceF K α (Work.FTS.EllipticEst.sliceV u) := by
      calc (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          ≤ C1 * ∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.sliceV u θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ := hderivLe
        _ ≤ C1 * sliceF K α (Work.FTS.EllipticEst.sliceV u) :=
            mul_le_mul_of_nonneg_left hVle (le_of_lt hC1pos)
    -- (G) the sum over `i`
    have hsumInt : MeasureTheory.IntegrableOn (fun θ => ∑ i ∈ Finset.Icc 1 K,
        (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ :=
      MeasureTheory.integrable_finsetSum (Finset.Icc 1 K) hLint
    have hsumBound : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.Icc 1 K,
        (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ)
        ≤ (K : ℝ) * M * sliceF K α (Work.FTS.EllipticEst.sliceV u) := by
      rw [MeasureTheory.integral_finsetSum (Finset.Icc 1 K) hLint]
      have h1 : ∑ i ∈ Finset.Icc 1 K, (∫ θ in Work.Spaces.Iθ,
            (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
              * Work.FTS.EllipticEst.thGam α θ)
          ≤ ∑ _i ∈ Finset.Icc 1 K,
              M * sliceF K α (Work.FTS.EllipticEst.sliceV u) :=
        Finset.sum_le_sum fun i hi => hIle i hi
      have h2 : (∑ _i ∈ Finset.Icc 1 K,
            M * sliceF K α (Work.FTS.EllipticEst.sliceV u))
          = ((Finset.Icc 1 K).card : ℝ)
              * (M * sliceF K α (Work.FTS.EllipticEst.sliceV u)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have h3 : ((Finset.Icc 1 K).card : ℝ) ≤ (K : ℝ) := by
        simp
      have h4 : ((Finset.Icc 1 K).card : ℝ)
            * (M * sliceF K α (Work.FTS.EllipticEst.sliceV u))
          ≤ (K : ℝ) * (M * sliceF K α (Work.FTS.EllipticEst.sliceV u)) :=
        mul_le_mul_of_nonneg_right h3
          (mul_nonneg hM0 (sliceF_nonneg K α (Work.FTS.EllipticEst.sliceV u)))
      linarith [h1, h4, le_of_eq h2]
    -- (H) assembly
    have hsplit : sliceF K α (deriv u)
        = (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.Icc 1 K,
              (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
                * Work.FTS.EllipticEst.thGam α θ) := by
      rw [sliceF]
      have hfun : (fun θ => sliceW K α (deriv u) θ)
          = fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
              + ∑ i ∈ Finset.Icc 1 K,
                  (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2
                    * Work.FTS.EllipticEst.thGam α θ := by
        funext θ
        rw [sliceW]
      rw [hfun, MeasureTheory.integral_add hdInt hsumInt]
    have hfinal : sliceF K α (deriv u)
        ≤ (C1 + (K : ℝ) * M + 1) * sliceF K α (Work.FTS.EllipticEst.sliceV u) := by
      rw [hsplit]
      have hS0 : 0 ≤ sliceF K α (Work.FTS.EllipticEst.sliceV u) :=
        sliceF_nonneg K α (Work.FTS.EllipticEst.sliceV u)
      nlinarith [hderivBound, hsumBound, hS0]
    exact ⟨hdInt, hLint, hfinal⟩

end Work.FTS.EllSol.VopAux
