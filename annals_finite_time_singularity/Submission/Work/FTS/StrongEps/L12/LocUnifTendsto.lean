import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.PhiStar.Honesty.CptApp.lamDzDeriv
import Submission.Work.FTS.PhiStar.Honesty.CptApp.momentDzZero
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.c2mGam_Wt_bound
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.Spaces.SmoothStripDefs
-- ===== merged: Submission.Work.FTS.ClassC.HkIntegrand_zero_DzIter_Dz_pthIter_two_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The slot `D_z^j (z ∂_z∂_θ²Ψ)` is dominated by the grid majorant `vanGrid`

The grid majorant `vanGrid α Ψ` (`ClassC/VanishFamilyDefs.lean`) is the sum of

* the singular-weight `ℋ^0`-integrands `HkIntegrand α 0 (D_z^l ∂_θ^m Ψ)` for `l ≤ 9`, `m ≤ 2`,
* the vanishing-weight integrands `hVint α Ψ t l = (D_z^l ∂_θ^t Ψ · w)² · sin(2θ)^{2t-4-γ}`
  for `3 ≤ t ≤ 9`, `l ≤ 9`.

The function `z ∂_z∂_θ²Ψ` is by definition `D_z(∂_θ²Ψ)`, so `D_z^j (z ∂_z∂_θ²Ψ)` is the
`(j+1)`-st iterated radial derivative of `∂_θ²Ψ`; with `j ≤ 7` it is thus literally the
summand `(l,m) = (j+1,2)` of the first block (*this* is the only mathematical content: the
associativity `D_z^j ∘ D_z = D_z^{j+1}` of the iteration).  It is therefore bounded by
`vanGrid`, hence by `4 * vanGrid` (the factor `4` being the slack used by the surrounding
assembly).  All summands of `vanGrid` are nonnegative, so no regularity of `Ψ` is needed
beyond what makes the statement typecheck.
-/
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false




end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.HkIntegrand_zero_DzIter_pthIter_two_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pure-`z` slot `D_z^j (∂_θ²Ψ)` is dominated by the grid majorant `vanGrid`

The grid majorant `vanGrid α Ψ` (`ClassC/VanishFamilyDefs.lean`) is the sum of

* the singular-weight `ℋ^0`-integrands `HkIntegrand α 0 (D_z^l ∂_θ^m Ψ)` for `l ≤ 9`, `m ≤ 2`,
* the vanishing-weight integrands `hVint α Ψ t l = (D_z^l ∂_θ^t Ψ · w)² · sin(2θ)^{2t-4-γ}`
  for `3 ≤ t ≤ 9`, `l ≤ 9`.

The slot `HkIntegrand α 0 (D_z^j ∂_θ²Ψ)` with `j ≤ 7` is literally the summand `(l,m) = (j,2)`
of the first block, so it is bounded by `vanGrid`, hence by `4 * vanGrid` (the factor `4` being
the slack used by the surrounding assembly).  All summands are nonnegative, so no regularity of
`Ψ` is needed beyond what makes the statement typecheck.
-/
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false



end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.HkIntegrand_zero_DzIter_zsqPz2_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-! ## A single pure slot against the grid majorant -/


/-! ## The target estimate -/


end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.VigPthIter2Bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false




end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.vig_Dz_pthIter_two_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC





end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.ClassC.vig_zsqPz2_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Membership of the single slots in the grid majorant -/



/-! ## The domination of a single plain angular slot -/


/-! ## The operator identity -/

/-- **The operator identity.** On the open quadrant, the `D_z^j ∂_θ^r`-slot of the smoothing
family `z²∂_z²Ψ` is the difference of the two shifted radial slots of `∂_θ^rΨ`:
`D_z^j∂_θ^r(z²∂_z²Ψ) = D_z^{j+2}(∂_θ^rΨ) − D_z^{j+1}(∂_θ^rΨ)`. -/
theorem vig_DzIter_pthIter_eq {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (r j : ℕ) :
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.DzIter j
          (Work.Spaces.pthIter r (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        = Work.Spaces.DzIter (j + 2) (Work.Spaces.pthIter r Ψ) z θ
          - Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter r Ψ) z θ := by
  intro z θ hz hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < Real.pi / 2 := hθ.2
  have hH : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter r Ψ) :=
    SmoothOpen_pthIter_classC hΨ r
  have hC : Work.Spaces.DzIter j
        (Work.Spaces.pthIter r (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
      = Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter r Ψ) z θ) z θ :=
    Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
      (F := Work.Spaces.pthIter r (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      (G := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter r Ψ) z θ)
      (fun z' θ' hz' hθ' hπ' => by
        rw [congrFun (congrFun (seven_pthIter_zsq_mul r (Work.Spaces.pzIter 2 Ψ)) z') θ',
          seven_pzIter_two_pthIter_eqOn_Q0 hΨ r z' θ' hz' hθ' hπ'])
      j z θ hz hθ0 hθ1
  have hD : Work.Spaces.DzIter j
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter r Ψ) z θ) z θ
      = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j (Work.Spaces.pthIter r Ψ)) z θ :=
    NormPiecesAux.zsqPz2_DzIter_eqOn (Work.Spaces.pthIter r Ψ) hH j z θ hz hθ0 hθ1
  have hE : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j (Work.Spaces.pthIter r Ψ)) z θ
      = Work.Spaces.DzIter 2 (Work.Spaces.DzIter j (Work.Spaces.pthIter r Ψ)) z θ
        - Work.Spaces.DzIter 1 (Work.Spaces.DzIter j (Work.Spaces.pthIter r Ψ)) z θ :=
    seven_zsq_pzIter_two_eq (Work.Spaces.DzIter j (Work.Spaces.pthIter r Ψ)) (hH.DzIter j)
      z θ hz hθ0 hθ1
  have e2 : Work.Spaces.DzIter 2 (Work.Spaces.DzIter j (Work.Spaces.pthIter r Ψ))
      = Work.Spaces.DzIter (j + 2) (Work.Spaces.pthIter r Ψ) := by
    rw [← seven_DzIter_add 2 j (Work.Spaces.pthIter r Ψ)]
    exact congrArg (fun n => Work.Spaces.DzIter n (Work.Spaces.pthIter r Ψ)) (by omega)
  have e1 : Work.Spaces.DzIter 1 (Work.Spaces.DzIter j (Work.Spaces.pthIter r Ψ))
      = Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter r Ψ) := by
    rw [← seven_DzIter_add 1 j (Work.Spaces.pthIter r Ψ)]
    exact congrArg (fun n => Work.Spaces.DzIter n (Work.Spaces.pthIter r Ψ)) (by omega)
  rw [hC, hD, hE, e2, e1]

/-! ## The target -/


end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.LamEst.lam_correction_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.LamEst

set_option maxHeartbeats 1600000

/-- The angular cutoff takes values in `[0,1]` (local copy of
`CptApp.zetaR_bounds`; `CptApp.cutBasic` cannot be imported here, see the note below). -/
private lemma zetaR_bounds (n : ℕ) (θ : ℝ) : 0 ≤ zetaR n θ ∧ zetaR n θ ≤ 1 := by
  have hnn : 0 ≤ zetaR n θ := by
    simp only [zetaR, cut01]
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  refine ⟨hnn, ?_⟩
  simp only [zetaR, cut01]
  calc Real.smoothTransition ((n : ℝ) * θ - 1)
        * Real.smoothTransition ((n : ℝ) * (Real.pi / 2 - θ) - 1)
      ≤ 1 * 1 := mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
        (Real.smoothTransition.nonneg _) zero_le_one
    _ = 1 := by norm_num

/-- The angular cutoff equals `1` on its plateau (local copy of `CptApp.zetaR_eq_one`). -/
private lemma zetaR_eq_one {n : ℕ} (hn : 2 ≤ n) {θ : ℝ} (h1 : 2 / (n : ℝ) ≤ θ)
    (h2 : θ ≤ Real.pi / 2 - 2 / (n : ℝ)) : zetaR n θ = 1 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have ha : 1 ≤ (n : ℝ) * θ - 1 := by
    have := (div_le_iff₀ hnpos).mp h1
    nlinarith
  have hb : 1 ≤ (n : ℝ) * (Real.pi / 2 - θ) - 1 := by
    have h : 2 / (n : ℝ) ≤ Real.pi / 2 - θ := by linarith
    have := (div_le_iff₀ hnpos).mp h
    nlinarith
  simp only [zetaR, cut01, Real.smoothTransition.one_of_one_le ha,
    Real.smoothTransition.one_of_one_le hb]
  norm_num

private lemma sin_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h; simp
  · exact le_of_lt (Real.sin_lt h)

/-- On the support of `zetaR n - 1` the factor `(zetaR n θ - 1)²` is at most `1`. -/
private lemma zetaR_sub_one_sq_le_one (n : ℕ) (θ : ℝ) : (zetaR n θ - 1) ^ 2 ≤ 1 := by
  obtain ⟨h0, h1⟩ := zetaR_bounds n θ
  nlinarith

private lemma indicator_unit_nonneg (s : Set ℝ) (x : ℝ) :
    0 ≤ s.indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]; norm_num
  · rw [Set.indicator_of_notMem hx]

private lemma indicator_unit_le_one (s : Set ℝ) (x : ℝ) :
    s.indicator (fun _ => (1 : ℝ)) x ≤ 1 := by
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]; norm_num

/-- The two-strip majorant: the constant `C` on `[0,t]` and on `[π/2 - t, π/2]`. -/
private def majorant (t C : ℝ) : ℝ → ℝ := fun θ =>
  C * (Set.Icc 0 t).indicator (fun _ => (1 : ℝ)) θ
    + C * (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)).indicator (fun _ => (1 : ℝ)) θ

private lemma majorant_nonneg {t C : ℝ} (hC : 0 ≤ C) (θ : ℝ) : 0 ≤ majorant t C θ := by
  unfold majorant
  exact add_nonneg (mul_nonneg hC (indicator_unit_nonneg _ _))
    (mul_nonneg hC (indicator_unit_nonneg _ _))

private lemma majorant_le {t C : ℝ} (hC : 0 ≤ C) (θ : ℝ) : majorant t C θ ≤ 2 * C := by
  unfold majorant
  have h1 := indicator_unit_le_one (Set.Icc 0 t) θ
  have h2 := indicator_unit_le_one (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)) θ
  nlinarith [hC]

/-- On the strips the integrand is at most `4 t^{2+η}`. -/
private lemma pointwise_bound {n : ℕ} {t θ : ℝ} (ht : 0 < t)
    (hsin0 : 0 ≤ Real.sin (2 * θ)) (hsin : Real.sin (2 * θ) ≤ 2 * t)
    (hsc : (Work.Elliptic.sinCos2 θ) ^ 2 ≤ t ^ 2) :
    (zetaR n θ - 1) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
        * (Work.Elliptic.sinCos2 θ) ^ 2 ≤ 4 * t ^ (2 + Work.Spaces.eta) := by
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  have hz : (zetaR n θ - 1) ^ 2 ≤ 1 := zetaR_sub_one_sq_le_one n θ
  have h2 : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ (2 * t) ^ Work.Spaces.eta :=
    Real.rpow_le_rpow hsin0 hsin Work.Spaces.eta_nonneg
  have h3 : (2 * t) ^ Work.Spaces.eta = 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta :=
    Real.mul_rpow (by norm_num) ht0
  have h4 : (2 : ℝ) ^ Work.Spaces.eta ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (le_of_lt Work.Spaces.eta_lt_one)
    simpa using h
  have h2t : (2 * t) ^ Work.Spaces.eta ≤ 2 * t ^ Work.Spaces.eta := by
    rw [h3]
    exact mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg ht0 _)
  have htp : t ^ Work.Spaces.eta * t ^ 2 = t ^ (2 + Work.Spaces.eta) := by
    rw [← Real.rpow_two t, ← Real.rpow_add ht, add_comm Work.Spaces.eta 2]
  have hsin_nn : 0 ≤ (Real.sin (2 * θ)) ^ Work.Spaces.eta :=
    Real.rpow_nonneg hsin0 _
  have h2t_nn : 0 ≤ (2 * t) ^ Work.Spaces.eta := Real.rpow_nonneg (by positivity) _
  calc (zetaR n θ - 1) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
        * (Work.Elliptic.sinCos2 θ) ^ 2
      ≤ 1 * (2 * t) ^ Work.Spaces.eta * t ^ 2 :=
        mul_le_mul (mul_le_mul hz h2 hsin_nn zero_le_one) hsc (sq_nonneg _)
          (mul_nonneg zero_le_one h2t_nn)
    _ ≤ 1 * (2 * t ^ Work.Spaces.eta) * t ^ 2 := by
        have h := mul_le_mul_of_nonneg_right h2t (sq_nonneg t)
        nlinarith [h]
    _ = 2 * (t ^ Work.Spaces.eta * t ^ 2) := by ring
    _ = 2 * t ^ (2 + Work.Spaces.eta) := by rw [htp]
    _ ≤ 4 * t ^ (2 + Work.Spaces.eta) := by
        linarith [Real.rpow_nonneg ht0 (2 + Work.Spaces.eta)]

private theorem angular_cutoff_bound_aux {n : ℕ} (hn : 2 ≤ n) :
    ∫ θ in Work.Spaces.Iθ, (Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) ^ 2
        * (Real.sin (2 * θ)) ^ Work.Spaces.eta * (Work.Elliptic.sinCos2 θ) ^ 2
      ≤ 16 * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) := by
  set t : ℝ := 2 / (n : ℝ) with ht
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one hnpos]
    exact_mod_cast hn
  set C : ℝ := 4 * t ^ (2 + Work.Spaces.eta) with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg ht0.le _)
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hIθ_fin : volume Work.Spaces.Iθ < ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  haveI hfin : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := by
    rw [isFiniteMeasure_restrict]
    exact hIθ_fin.ne
  -- basic pointwise facts on `Iθ`
  have hsin2_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    obtain ⟨h0, h1⟩ := hθ
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  -- the pointwise domination
  have hpoint : ∀ θ ∈ Work.Spaces.Iθ,
      (zetaR n θ - 1) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
          * (Work.Elliptic.sinCos2 θ) ^ 2 ≤ majorant t C θ := by
    intro θ hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    have hsinθ0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ0, by linarith [Real.pi_pos]⟩
    have hcosθ0 : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ0], by linarith [hθ1, Real.pi_pos]⟩
    have hcos2_le : Real.cos θ ^ 2 ≤ 1 := by
      nlinarith [abs_nonneg (Real.cos θ), Real.abs_cos_le_one θ, sq_abs (Real.cos θ)]
    have hsc0 : 0 ≤ Work.Elliptic.sinCos2 θ := by
      rw [Work.Elliptic.sinCos2]; exact mul_nonneg hsinθ0 (sq_nonneg _)
    by_cases hlt : θ < t
    · -- left strip `[0, t]`
      have hsinθ_le : Real.sin θ ≤ t := le_trans (sin_le_self_of_nonneg hθ0) (le_of_lt hlt)
      have hsin : Real.sin (2 * θ) ≤ 2 * t := by
        rw [Real.sin_two_mul]
        have h := mul_le_mul hsinθ_le (Real.cos_le_one θ) hcosθ0 ht0.le
        linarith [h]
      have hsct : Work.Elliptic.sinCos2 θ ≤ t := by
        rw [Work.Elliptic.sinCos2]
        nlinarith [hsinθ_le, hsinθ0, hcos2_le, sq_nonneg (Real.cos θ), ht0.le]
      have hsc : (Work.Elliptic.sinCos2 θ) ^ 2 ≤ t ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hsct) (add_nonneg ht0.le hsc0)]
      have hb := pointwise_bound (n := n) ht0 hsin0 hsin hsc
      rw [← hC] at hb
      have hind : (Set.Icc 0 t).indicator (fun _ => (1 : ℝ)) θ = 1 := by
        rw [Set.indicator_of_mem (show θ ∈ Set.Icc 0 t from ⟨hθ0, le_of_lt hlt⟩)]
      have hgm : C ≤ majorant t C θ := by
        simp only [majorant, hind]
        have h2n := mul_nonneg hC0 (indicator_unit_nonneg (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)) θ)
        linarith
      exact le_trans hb hgm
    · push_neg at hlt
      by_cases hple : θ ≤ Real.pi / 2 - t
      · -- the plateau: `zetaR n θ = 1`
        have hz : zetaR n θ = 1 := by
          refine zetaR_eq_one hn ?_ ?_
          · rw [← ht]; exact hlt
          · rw [← ht]; exact hple
        rw [hz]
        have hzero : (1 - 1 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
            * (Work.Elliptic.sinCos2 θ) ^ 2 = 0 := by ring
        rw [hzero]
        exact majorant_nonneg hC0 θ
      · -- right strip `[π/2 - t, π/2]`
        push_neg at hple
        have hsin : Real.sin (2 * θ) ≤ 2 * t := by
          have h1 : Real.sin (2 * θ) = Real.sin (Real.pi - 2 * θ) := by
            conv_lhs => rw [show 2 * θ = Real.pi - (Real.pi - 2 * θ) by ring]
            rw [Real.sin_pi_sub]
          rw [h1]
          have hx0 : 0 ≤ Real.pi - 2 * θ := by linarith [hθ1]
          have hxle : Real.pi - 2 * θ ≤ 2 * t := by linarith [hple]
          exact le_trans (sin_le_self_of_nonneg hx0) hxle
        have hcos_le : Real.cos θ ≤ t := by
          have h1 : Real.cos θ = Real.sin (Real.pi / 2 - θ) :=
            (Real.sin_pi_div_two_sub θ).symm
          rw [h1]
          exact le_trans (sin_le_self_of_nonneg (by linarith [hθ1])) (by linarith [hple])
        have hc2 : Real.cos θ ^ 2 ≤ t ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hcos_le) (add_nonneg ht0.le hcosθ0)]
        have hsc : (Work.Elliptic.sinCos2 θ) ^ 2 ≤ t ^ 2 := by
          have hst : Work.Elliptic.sinCos2 θ ≤ t ^ 2 := by
            rw [Work.Elliptic.sinCos2]
            have h := mul_le_mul (Real.sin_le_one θ) le_rfl (sq_nonneg (Real.cos θ)) zero_le_one
            nlinarith [h, hc2]
          have ht21 : t ^ 2 ≤ 1 := by nlinarith [ht0.le, ht1]
          have h1s : Work.Elliptic.sinCos2 θ ≤ 1 := le_trans hst ht21
          nlinarith [mul_nonneg hsc0 (sub_nonneg.mpr h1s), hst]
        have hb := pointwise_bound (n := n) ht0 hsin0 hsin hsc
        rw [← hC] at hb
        have hind : (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)).indicator (fun _ => (1 : ℝ)) θ = 1 := by
          rw [Set.indicator_of_mem (show θ ∈ Set.Icc (Real.pi / 2 - t) (Real.pi / 2)
            from ⟨le_of_lt hple, hθ1⟩)]
        have hgm : C ≤ majorant t C θ := by
          simp only [majorant, hind]
          have h2n := mul_nonneg hC0 (indicator_unit_nonneg (Set.Icc 0 t) θ)
          linarith
        exact le_trans hb hgm
  -- the majorant is integrable
  have hmaj_meas : AEStronglyMeasurable (majorant t C) (volume.restrict Work.Spaces.Iθ) := by
    have h1 : Measurable (fun θ : ℝ => C * (Set.Icc 0 t).indicator (fun _ => (1 : ℝ)) θ) :=
      measurable_const.mul (Measurable.indicator measurable_const measurableSet_Icc)
    have h2 : Measurable (fun θ : ℝ =>
        C * (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)).indicator (fun _ => (1 : ℝ)) θ) :=
      measurable_const.mul (Measurable.indicator measurable_const measurableSet_Icc)
    have h3 : Measurable (majorant t C) := by
      unfold majorant
      exact h1.add h2
    exact h3.aestronglyMeasurable
  have hmaj_int : Integrable (majorant t C) (volume.restrict Work.Spaces.Iθ) := by
    refine IntegrableOn.of_bound hIθ_fin hmaj_meas (2 * C) ?_
    filter_upwards with θ
    have h1 : 0 ≤ majorant t C θ := majorant_nonneg hC0 θ
    have h2 : majorant t C θ ≤ 2 * C := majorant_le hC0 θ
    calc ‖majorant t C θ‖ = |majorant t C θ| := Real.norm_eq_abs _
      _ = majorant t C θ := abs_of_nonneg h1
      _ ≤ 2 * C := h2
  -- the two strip integrals
  have hvol1 : (volume.restrict Work.Spaces.Iθ).real (Set.Icc 0 t) ≤ t := by
    have hm : (volume.restrict Work.Spaces.Iθ) (Set.Icc 0 t) ≤ ENNReal.ofReal t := by
      calc (volume.restrict Work.Spaces.Iθ) (Set.Icc 0 t)
          = volume (Set.Icc 0 t ∩ Work.Spaces.Iθ) := Measure.restrict_apply measurableSet_Icc
        _ ≤ volume (Set.Icc 0 t) := measure_mono (Set.inter_subset_left)
        _ = ENNReal.ofReal t := by rw [Real.volume_Icc]; norm_num
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    simpa [measureReal_def, ENNReal.toReal_ofReal ht0.le] using h
  have hvol2 : (volume.restrict Work.Spaces.Iθ).real
      (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)) ≤ t := by
    have hm : (volume.restrict Work.Spaces.Iθ)
        (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)) ≤ ENNReal.ofReal t := by
      calc (volume.restrict Work.Spaces.Iθ) (Set.Icc (Real.pi / 2 - t) (Real.pi / 2))
          = volume (Set.Icc (Real.pi / 2 - t) (Real.pi / 2) ∩ Work.Spaces.Iθ) :=
            Measure.restrict_apply measurableSet_Icc
        _ ≤ volume (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)) := measure_mono (Set.inter_subset_left)
        _ = ENNReal.ofReal t := by rw [Real.volume_Icc]; ring_nf
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    simpa [measureReal_def, ENNReal.toReal_ofReal ht0.le] using h
  have hmaj_val : ∫ θ in Work.Spaces.Iθ, majorant t C θ
      = C * (volume.restrict Work.Spaces.Iθ).real (Set.Icc 0 t)
        + C * (volume.restrict Work.Spaces.Iθ).real
            (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)) := by
    have hi1 : Integrable (fun θ : ℝ => C * (Set.Icc 0 t).indicator (fun _ => (1 : ℝ)) θ)
        (volume.restrict Work.Spaces.Iθ) :=
      Integrable.const_mul (Integrable.indicator (integrable_const (1 : ℝ)) measurableSet_Icc) C
    have hi2 : Integrable (fun θ : ℝ =>
        C * (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)).indicator (fun _ => (1 : ℝ)) θ)
        (volume.restrict Work.Spaces.Iθ) :=
      Integrable.const_mul (Integrable.indicator (integrable_const (1 : ℝ)) measurableSet_Icc) C
    simp only [majorant]
    rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul,
      integral_indicator_const (1 : ℝ) measurableSet_Icc,
      integral_indicator_const (1 : ℝ) measurableSet_Icc]
    simp
  have hmaj_le : ∫ θ in Work.Spaces.Iθ, majorant t C θ ≤ C * t + C * t := by
    rw [hmaj_val]
    have h1 := mul_le_mul_of_nonneg_left hvol1 hC0
    have h2 := mul_le_mul_of_nonneg_left hvol2 hC0
    linarith
  -- the final arithmetic
  have harith : C * t + C * t ≤ 16 * t ^ (2 + Work.Spaces.eta) := by
    have hnn : 0 ≤ t ^ (2 + Work.Spaces.eta) := Real.rpow_nonneg ht0.le _
    have hmul : t ^ (2 + Work.Spaces.eta) * t ≤ t ^ (2 + Work.Spaces.eta) := by
      nlinarith [hnn, ht1]
    calc C * t + C * t = 8 * (t ^ (2 + Work.Spaces.eta) * t) := by rw [hC]; ring
      _ ≤ 8 * t ^ (2 + Work.Spaces.eta) := by linarith
      _ ≤ 16 * t ^ (2 + Work.Spaces.eta) := by linarith
  have hf_nn : ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ (zetaR n θ - 1) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
          * (Work.Elliptic.sinCos2 θ) ^ 2 := by
    intro θ hθ
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin2_nn θ hθ) _)) (sq_nonneg _)
  calc ∫ θ in Work.Spaces.Iθ, (zetaR n θ - 1) ^ 2
          * (Real.sin (2 * θ)) ^ Work.Spaces.eta * (Work.Elliptic.sinCos2 θ) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, majorant t C θ :=
        integral_mono_of_nonneg
          (ae_restrict_of_forall_mem hIθ_meas hf_nn) hmaj_int
          (ae_restrict_of_forall_mem hIθ_meas hpoint)
    _ ≤ C * t + C * t := hmaj_le
    _ ≤ 16 * t ^ (2 + Work.Spaces.eta) := harith
    _ = 16 * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) := by rw [ht]


/-- The angular cutoff factor `zetaR n θ - 1` is bounded by `1` (it lies in `[-1, 0]`). -/
theorem abs_zetaR_sub_one_le (n : ℕ) (θ : ℝ) : |zetaR n θ - 1| ≤ 1 := by
  have hnn : 0 ≤ zetaR n θ := by
    rw [zetaR, cut01]
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hle : zetaR n θ ≤ 1 := by
    rw [zetaR, cut01]
    calc Real.smoothTransition ((n : ℝ) * θ - 1)
          * Real.smoothTransition ((n : ℝ) * (Real.pi / 2 - θ) - 1)
        ≤ 1 * 1 := mul_le_mul (Real.smoothTransition.le_one _)
            (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) zero_le_one
      _ = 1 := by norm_num
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

theorem lam_correction_sq_le {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α k F)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) :
    ∃ Cmom : ℝ, 0 ≤ Cmom ∧
      ∀ (n : ℕ), 2 ≤ n → ∀ (s : ℕ), s ≤ k →
        ∀ᵐ z ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)),
          (Work.Spaces.DzIter s
              (fun z _ => Work.FTS.PhiStar.Honesty.CptApp.lam n F z) z 0)^2 * (Work.Spaces.w z)^2
            ≤ Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
              * (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.DzIter s F z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))^2) := by
  refine ⟨16, by norm_num, ?_⟩
  intro n hn s hs
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  filter_upwards [momentDzZero hsm hF hFs s hs,
    MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hmom hz
  have hzpos : 0 < z := hz
  -- ## Integrability and measurability of the weighted `D_z^s F` slot
  have hX2 : MeasureTheory.Integrable
      (fun θ : ℝ => (Work.Spaces.DzIter s F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.integrableOn_zSummand α k hsm hF s hs
      (Set.mem_Ici.mpr hzpos.le)
  have hXm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.DzIter s F z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.DzIter s F p.1 p.2) ((hsm.DzIter s).continuousOn) hzpos
  have hAm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.DzIter s F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hsm.aesm_slice_summand s hzpos
  have hXsc : MeasureTheory.Integrable
      (fun θ : ℝ => Work.Spaces.DzIter s F z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    integrable_mul_sinCos2 hzpos hXm hX2
  -- ## The cancellation identity: the uncut moment of `D_z^s F` vanishes
  have hγm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => zetaR n θ - 1)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ((continuous_zetaR n).aestronglyMeasurable).sub
      (continuous_const.aestronglyMeasurable)
  have hscm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    continuous_sinCos2.aestronglyMeasurable
  have hζint : MeasureTheory.Integrable
      (fun θ : ℝ => (zetaR n θ - 1) * Work.Spaces.DzIter s F z θ
        * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono hXsc ((hγm.mul hXm).mul hscm) ?_
    filter_upwards with θ
    have h3 : |zetaR n θ - 1| ≤ 1 := abs_zetaR_sub_one_le n θ
    calc ‖(zetaR n θ - 1) * Work.Spaces.DzIter s F z θ * Work.Elliptic.sinCos2 θ‖
        = |zetaR n θ - 1| * |Work.Spaces.DzIter s F z θ| * |Work.Elliptic.sinCos2 θ| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
      _ ≤ 1 * |Work.Spaces.DzIter s F z θ| * |Work.Elliptic.sinCos2 θ| := by gcongr
      _ = |Work.Spaces.DzIter s F z θ| * |Work.Elliptic.sinCos2 θ| := by ring
      _ = ‖Work.Spaces.DzIter s F z θ * Work.Elliptic.sinCos2 θ‖ := by
          rw [Real.norm_eq_abs, abs_mul]
  have hId : (∫ θ in Work.Spaces.Iθ,
        zetaR n θ * Work.Spaces.DzIter s F z θ * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ,
        (zetaR n θ - 1) * Work.Spaces.DzIter s F z θ * Work.Elliptic.sinCos2 θ := by
    have hsum := MeasureTheory.integral_add hζint hXsc
    have hcongr : (∫ θ in Work.Spaces.Iθ,
          ((zetaR n θ - 1) * Work.Spaces.DzIter s F z θ * Work.Elliptic.sinCos2 θ)
            + (Work.Spaces.DzIter s F z θ * Work.Elliptic.sinCos2 θ))
        = ∫ θ in Work.Spaces.Iθ,
            zetaR n θ * Work.Spaces.DzIter s F z θ * Work.Elliptic.sinCos2 θ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with θ
      ring
    rw [hcongr, hmom, add_zero] at hsum
    exact hsum
  -- ## Cauchy–Schwarz against the `(s,0)`-slot, with the cutoff weight
  have hcs := cs_cutoff (X := fun θ : ℝ => Work.Spaces.DzIter s F z θ)
    (γ := fun θ : ℝ => zetaR n θ - 1) hzpos hγm (abs_zetaR_sub_one_le n) hAm hX2
  have hang := angular_cutoff_bound_aux hn
  have hΦnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter s F z θ * (Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  -- ## Assembly
  rw [Work.FTS.PhiStar.Honesty.CptApp.lamDzDeriv hsm k n hn1 s hs z hzpos, hId]
  have hstep : (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter s F z θ * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      * (∫ θ in Work.Spaces.Iθ,
        (zetaR n θ - 1) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
          * (Work.Elliptic.sinCos2 θ) ^ 2)
      ≤ 16 * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
        * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter s F z θ * (Work.Spaces.w z
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    calc (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter s F z θ * (Work.Spaces.w z
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        * (∫ θ in Work.Spaces.Iθ,
          (zetaR n θ - 1) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
            * (Work.Elliptic.sinCos2 θ) ^ 2)
        ≤ (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter s F z θ * (Work.Spaces.w z
              / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          * (16 * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_left hang hΦnn
      _ = 16 * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
          * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter s F z θ * (Work.Spaces.w z
              / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by ring
  exact le_trans hcs hstep

end Work.FTS.PhiStar.Honesty.CptApp.LamEst
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.VanGridK =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The level-`K` grid majorant.**  The sum of all the integrands of the two families whose
integrability the hypotheses of the honesty transfer supply: the singular-weight `ℋ⁰`-slots
`HkIntegrand α 0 (D_z^l ∂_θ^m Ψ)` (`l ≤ K + 2`, `m ≤ 2`) and the vanishing-weight slots
`hVint α Ψ t l` (`3 ≤ t ≤ K + 2`, `l ≤ K + 2`). -/
def vanGridK (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (K : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    (∑ l ∈ Finset.range (K + 3), ∑ m ∈ Finset.range 3,
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ)
      + ∑ t ∈ Finset.Icc 3 (K + 2), ∑ l ∈ Finset.range (K + 3),
          Work.FTS.ClassC.hVint α Ψ t l z θ

/-- The grid majorant is nonnegative on the angular interval. -/
theorem vanGridK_nonneg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (K : ℕ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ vanGridK α Ψ K z θ := by
  rw [vanGridK]
  refine add_nonneg
    (Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun m _ =>
      Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
    (Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun l _ => ?_)
  simp only [Work.FTS.ClassC.hVint]
  exact mul_nonneg (sq_nonneg _)
    (Real.rpow_nonneg (Work.FTS.ClassC.sin_two_nonneg_of_mem_Iθ' hθ) _)

/-! ## Membership of the single slots in the grid majorant -/

/-- Every pure radial slot `HkIntegrand α 0 (D_z^l Ψ)` with `l ≤ K + 2` is a summand of the
grid majorant. -/
theorem hkDze_zero_DzIter_le_vanGridK {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {K l : ℕ}
    (hl : l ≤ K + 2) :
    ∀ z θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l Ψ) z θ ≤ vanGridK α Ψ K z θ := by
  intro z θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsin : 0 < Real.sin (2 * θ) := Work.FTS.ClassC.sin_two_pos_of_mem_Ioo hθ
  have hmem_l : l ∈ Finset.range (K + 3) := Finset.mem_range.mpr (by omega)
  have hmem_m : (0 : ℕ) ∈ Finset.range 3 := Finset.mem_range.mpr (by norm_num)
  -- the slot with `m = 0` is the `m = 0` term of the inner sum
  have hinner : Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l Ψ) z θ
      ≤ ∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ := by
    simpa only [Work.Spaces.pthIter_zero] using
      (Finset.single_le_sum
        (f := fun m => Work.Spaces.HkIntegrand α 0
          (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ)
        (fun m _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ) hmem_m)
  have houter : (∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ)
      ≤ ∑ l' ∈ Finset.range (K + 3), ∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l' (Work.Spaces.pthIter m Ψ)) z θ :=
    Finset.single_le_sum
      (f := fun l' => ∑ m ∈ Finset.range 3, Work.Spaces.HkIntegrand α 0
        (Work.Spaces.DzIter l' (Work.Spaces.pthIter m Ψ)) z θ)
      (fun l' _ => Finset.sum_nonneg fun m _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ) hmem_l
  have htail : 0 ≤ ∑ t ∈ Finset.Icc 3 (K + 2), ∑ l' ∈ Finset.range (K + 3),
      Work.FTS.ClassC.hVint α Ψ t l' z θ :=
    Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun l' _ => by
      simp only [Work.FTS.ClassC.hVint]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hsin) _)
  rw [vanGridK]
  linarith

/-- The `HkIntegrand α 0`-slot of angular order `r ≤ 2` and radial order `l ≤ K + 2` is a
summand of the grid majorant. -/
theorem hkIntegrand_le_vanGridK {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {K r l : ℕ}
    (hr : r ≤ 2) (hl : l ≤ K + 2) :
    ∀ z θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter r Ψ)) z θ
        ≤ vanGridK α Ψ K z θ := by
  intro z θ hθ
  have hsin : 0 < Real.sin (2 * θ) := Work.FTS.ClassC.sin_two_pos_of_mem_Ioo hθ
  have hmem_l : l ∈ Finset.range (K + 3) := Finset.mem_range.mpr (by omega)
  have hmem_r : r ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
  have hinner : Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter r Ψ))
        z θ
      ≤ ∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ :=
    Finset.single_le_sum
      (f := fun m => Work.Spaces.HkIntegrand α 0
        (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ)
      (fun m _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ) hmem_r
  have hmid : (∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l (Work.Spaces.pthIter m Ψ)) z θ)
      ≤ ∑ l' ∈ Finset.range (K + 3), ∑ m ∈ Finset.range 3,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l' (Work.Spaces.pthIter m Ψ)) z θ :=
    Finset.single_le_sum
      (f := fun l' => ∑ m ∈ Finset.range 3, Work.Spaces.HkIntegrand α 0
        (Work.Spaces.DzIter l' (Work.Spaces.pthIter m Ψ)) z θ)
      (fun l' _ => Finset.sum_nonneg fun m _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ) hmem_l
  have htail : 0 ≤ ∑ t ∈ Finset.Icc 3 (K + 2), ∑ l' ∈ Finset.range (K + 3),
      Work.FTS.ClassC.hVint α Ψ t l' z θ :=
    Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun l' _ => by
      simp only [Work.FTS.ClassC.hVint]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hsin) _)
  rw [vanGridK]
  linarith

/-- The `hVint`-slot of angular order `3 ≤ t ≤ K + 2` and radial order `l ≤ K + 2` is a summand
of the grid majorant. -/
theorem hVint_le_vanGridK {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {K t l : ℕ}
    (ht3 : 3 ≤ t) (ht : t ≤ K + 2) (hl : l ≤ K + 2) :
    ∀ z θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.FTS.ClassC.hVint α Ψ t l z θ ≤ vanGridK α Ψ K z θ := by
  intro z θ hθ
  have hsin : 0 < Real.sin (2 * θ) := Work.FTS.ClassC.sin_two_pos_of_mem_Ioo hθ
  have hmem_t : t ∈ Finset.Icc 3 (K + 2) := Finset.mem_Icc.mpr ⟨ht3, ht⟩
  have hmem_l : l ∈ Finset.range (K + 3) := Finset.mem_range.mpr (by omega)
  have hnonneg : ∀ t' l' : ℕ, 0 ≤ Work.FTS.ClassC.hVint α Ψ t' l' z θ := fun t' l' => by
    simp only [Work.FTS.ClassC.hVint]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hsin) _)
  have hinner : Work.FTS.ClassC.hVint α Ψ t l z θ
      ≤ ∑ l' ∈ Finset.range (K + 3), Work.FTS.ClassC.hVint α Ψ t l' z θ :=
    Finset.single_le_sum (f := fun l' => Work.FTS.ClassC.hVint α Ψ t l' z θ)
      (fun l' _ => hnonneg t l') hmem_l
  have hmid : (∑ l' ∈ Finset.range (K + 3), Work.FTS.ClassC.hVint α Ψ t l' z θ)
      ≤ ∑ t' ∈ Finset.Icc 3 (K + 2), ∑ l' ∈ Finset.range (K + 3),
          Work.FTS.ClassC.hVint α Ψ t' l' z θ :=
    Finset.single_le_sum
      (f := fun t' => ∑ l' ∈ Finset.range (K + 3), Work.FTS.ClassC.hVint α Ψ t' l' z θ)
      (fun t' _ => Finset.sum_nonneg fun l' _ => hnonneg t' l') hmem_t
  have hhead : 0 ≤ ∑ l' ∈ Finset.range (K + 3), ∑ m ∈ Finset.range 3,
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter l' (Work.Spaces.pthIter m Ψ)) z θ :=
    Finset.sum_nonneg fun l' _ => Finset.sum_nonneg fun m _ =>
      Work.Spaces.HkIntegrand_nonneg α 0 _ z θ
  rw [vanGridK]
  linarith

/-- **A single plain angular slot against the grid.**  For `1 ≤ r ≤ K + 2` and `l ≤ K + 2`, the
vanishing-weight slot `(D_z^l ∂_θ^r Ψ · w)² · sin(2θ)^{2r-γ}` is dominated by the grid
majorant: for `r ≤ 2` the singular `ℋ⁰`-slot dominates it (because `2r - γ ≥ 2 - 3/2 ≥ -η`),
and for `r ≥ 3` the grid's own `hVint`-slot has the smaller exponent `2r - 4 - γ`. -/
theorem vig_slot_le_vanGridK {α : ℝ} (hγ : Work.Spaces.gam α ≤ 3 / 2) (Ψ : ℝ → ℝ → ℝ)
    (K r l : ℕ) (hr : 1 ≤ r) (hrK : r ≤ K + 2) (hl : l ≤ K + 2) :
    ∀ z θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (Work.Spaces.DzIter l (Work.Spaces.pthIter r Ψ) z θ * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α)
        ≤ vanGridK α Ψ K z θ := by
  intro z θ hθ
  by_cases hr2 : r ≤ 2
  · -- `r ≤ 2`: the singular `ℋ⁰`-integrand dominates the vanishing weight
    refine le_trans (Work.FTS.ClassC.sq_mul_sin_le_HkIntegrand_zero α _ hθ ?_)
      (hkIntegrand_le_vanGridK hr2 hl z θ hθ)
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have heta : Work.Spaces.eta = 99 / 100 := rfl
    have hgam := hγ
    rw [Work.Spaces.gam] at hgam
    rw [heta]
    linarith
  · -- `r ≥ 3`: the grid's own vanishing slot has the smaller exponent `2r - 4 - γ`
    have hr3 : 3 ≤ r := by omega
    refine le_trans (Work.FTS.ClassC.sq_mul_sin_le_sq_mul_sin hθ ?_ ?_)
      (hVint_le_vanGridK hr3 hrK hl z θ hθ)
    · -- `0 ≤ 2r - 4 - γ`
      have hr3' : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr3
      have hgam := hγ
      rw [Work.Spaces.gam] at hgam
      linarith
    · -- `2r - 4 - γ ≤ 2r - γ`
      linarith

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12.LocUnifTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.L12

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## From the box-uniform bound to the convergence of the functional -/


end Work.FTS.StrongEps.L12
end
end
