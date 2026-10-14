import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.FinalAux
import Submission.Work.FTS.TransportS.T3SlotAux.Pointwise
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.N6TP.termBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongPersist.N6TP.termBound`

The *pointwise* per-summand estimate of the level-six `D_z`-transport Leibniz expansion
(the pointwise companion of `Work.FTS.StrongPersist.N6TP.summandBound`).

At a slot `(a,b)` of total order `≤ 6` and a Leibniz index `(a₁,b₁) ≠ (0,0)`, the summand

`ρ · (D_z^{b₁}D_θ^{a₁} f) · (D_z^{b-b₁+1}D_θ^{a-a₁} g) · (D_z^bD_θ^a g)`

of the expansion of `mixed b a (f · D_z g)` is dominated pointwise on the open quadrant by

`(1000 |f|_{𝒲^{6,∞}} + Cf · CoefTh 5 f) · HkIntegrand α 6 g`.

The two regimes:

* `a₁ = 0` (so `b₁ ≥ 1`): the pure radial derivative `D_z^{b₁}f` is bounded by
  `1000 |f|_{𝒲^{6,∞}}` (`dzIter_le_WlInf6`), and the leaf weight `ρ` paired with the two
  `g`-slots is bounded by `HkIntegrand α 6 g` (`l6_summand_le_zero`, which runs the
  two-factor AM–GM estimate `canonW_pair_le6` at the canonical exponent of the slot).
* `1 ≤ a₁`: the caller's hypothesis supplies the *angular* gain
  `|D_z^{b₁}D_θ^{a₁}f| ≤ Cf sin(2θ) · CoefTh 5 f`; the extra factor `sin(2θ)` turns the leaf
  weight into `canonW (α/10)` (`sin_mul_leafW_le_canonW`), and the two *mixed* `g`-slots are
  again absorbed by `canonW_pair_le6` — this time at the exponent `α/10`, which is `≤ η` and
  `≤ γ`, so it is admissible in both slots.
-/

namespace Work.FTS.StrongPersist.N6TP




end Work.FTS.StrongPersist.N6TP
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1SlotZ.Base2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SlotZ

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_eta_eq canonW_gam_eq)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## Joint continuity of `Wt` -/

theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p
    simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  rw [hfun]
  refine ContinuousOn.mul ?_ ?_
  · show ContinuousOn (fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2) Work.FTS.EllipticEst.Q0
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  · refine ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const ?_
    intro p hp
    refine Or.inl (ne_of_gt ?_)
    show 0 < Real.sin (2 * p.2)
    apply Real.sin_pos_of_pos_of_lt_pi
    · have h := hp.2.1; linarith
    · have h := hp.2.2; linarith [Real.pi_pos]

/-! ## An arithmetic monotonicity -/


/-! ## A function dominated by the `ℋ⁶`-integrand is `L²` -/


/-! ## The two-dimensional Cauchy–Schwarz -/


end Work.FTS.StrongPersist.N6Trans.T1SlotZ
end
end
-- ===== merged: Submission.Work.FTS.TransportS.T2Sup.Final =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2Sup

set_option autoImplicit false

open Work.FTS.TransportS.SlotT2


/-- The three leaf weights are the canonical weights `canonW η`, `canonW 0` and `canonW γ`. -/
theorem leafWeight_eq_canon : (Work.FTS.TransportS.leafEta = canonW Work.Spaces.eta) ∧
    (Work.FTS.TransportS.leafOne = canonW 0) ∧
    (∀ α : ℝ, Work.FTS.TransportS.leafGam α = canonW (Work.Spaces.gam α)) := by
  refine ⟨rfl, ?_, fun α => rfl⟩
  funext z θ
  simp only [Work.FTS.TransportS.leafOne, canonW, neg_zero, Real.rpow_zero, mul_one]


end Work.FTS.TransportS.T2Sup
end
end
-- ===== merged: Submission.Work.FTS.TransportS.T2Sup.smainBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2Sup

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Work.FTS.TransportS.SlotT2

/-! ## Interior comparison of the canonical weights -/

/-- At interior angles the canonical weight `canonW q` is monotone in the exponent. -/
theorem canonW_le_of_le {q q' z θ : ℝ} (hqq : q ≤ q') (hθ0 : 0 < θ) (hθ2 : θ < π / 2) :
    canonW q z θ ≤ canonW q' z θ := by
  have hσ0 : 0 < Real.sin (2 * θ) := sin_two_pos_of_Ioo ⟨hθ0, hθ2⟩
  have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_exponent_ge hσ0 hσ1 (show -q' ≤ -q by linarith)
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-! ## The slot dominations at an arbitrary order -/

/-- `canonW q · (D_z^j g)² ≤ HkIntegrand α k g` for any `q ≤ η` and `j ≤ k`
(interior angles). -/
theorem canonW_mul_z_le_of_le {α q : ℝ} {g : ℝ → ℝ → ℝ} (k : ℕ) (hq : q ≤ Work.Spaces.eta)
    {z θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < π / 2) {j : ℕ} (hj : j ≤ k) :
    canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
  have hw : canonW q z θ ≤ (Work.FTS.H2.Whz z θ) ^ 2 := by
    rw [← canonW_eta_eq z θ hθI]
    exact canonW_le_of_le hq hθ0 hθ2
  calc canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2
      ≤ (Work.FTS.H2.Whz z θ) ^ 2 * (Work.Spaces.DzIter j g z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = (Work.Spaces.DzIter j g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [Work.FTS.H2.Whz]; ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α k g z θ j hj

/-- `canonW q · (mixed j i g)² ≤ HkIntegrand α k g` for any `q ≤ γ`, `1 ≤ i`, `i + j ≤ k`
(interior angles). -/
theorem canonW_mul_mixed_le_of_le {α q : ℝ} {g : ℝ → ℝ → ℝ} (k : ℕ)
    (hqγ : q ≤ Work.Spaces.gam α) {z θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < π / 2)
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
  have hw : canonW q z θ ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
    rw [← canonW_gam_eq α z θ hθI]
    exact canonW_le_of_le hqγ hθ0 hθ2
  calc canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2
      ≤ (Work.Spaces.Wt α z θ) ^ 2 * (Work.Spaces.mixed j i g z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ = (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α k g z θ i j hi hij

/-! ## The `θ`-slice bound of the `Smain` summand -/

/-- **The angular slice bound.**  If the `canonW q`-weighted squares of the two factors are
dominated by the (`θ`-integrable) functions `HkIntegrand α k₁ g` resp. `HkIntegrand α k₂ g`,
then the absolute value of the angular integral of the `Smain` summand is at most `Mf` times
the sum of the two slot energies. -/
theorem smain_slice_abs_le {α q Mf : ℝ} (hMf : 0 ≤ Mf) {f g : ℝ → ℝ → ℝ} {a b : ℕ}
    {k₁ k₂ : ℕ} {z : ℝ}
    (hI1 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k₁ g z θ)
      Work.Spaces.Iθ)
    (hI2 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k₂ g z θ)
      Work.Spaces.Iθ)
    (hf : ∀ θ : ℝ, 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    (hX : ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α k₁ g z θ)
    (hY : ∀ θ : ℝ, 0 < θ → θ < π / 2 →
      canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α k₂ g z θ) :
    |∫ θ in Work.Spaces.Iθ, canonW q z θ * f z θ * Work.Spaces.mixed (b + 1) a g z θ
        * Work.Spaces.mixed b a g z θ|
      ≤ Mf * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k₁ g z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k₂ g z θ)) := by
  have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖canonW q z θ * f z θ * Work.Spaces.mixed (b + 1) a g z θ
        * Work.Spaces.mixed b a g z θ‖
        ≤ Mf * (Work.Spaces.HkIntegrand α k₁ g z θ + Work.Spaces.HkIntegrand α k₂ g z θ) := by
    refine ae_of_forall_Ioo (fun θ hθ => ?_)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hcw : 0 ≤ canonW q z θ := canonW_nonneg hθI
    have hA := hX θ hθ.1 hθ.2
    have hB := hY θ hθ.1 hθ.2
    have hamgm : |Work.Spaces.mixed (b + 1) a g z θ| * |Work.Spaces.mixed b a g z θ|
        ≤ ((Work.Spaces.mixed (b + 1) a g z θ) ^ 2
            + (Work.Spaces.mixed b a g z θ) ^ 2) / 2 := by
      have h := two_mul_le_add_sq |Work.Spaces.mixed (b + 1) a g z θ|
        |Work.Spaces.mixed b a g z θ|
      rw [sq_abs, sq_abs] at h
      linarith
    have hGY : canonW q z θ * |Work.Spaces.mixed (b + 1) a g z θ|
          * |Work.Spaces.mixed b a g z θ|
        ≤ Work.Spaces.HkIntegrand α k₁ g z θ + Work.Spaces.HkIntegrand α k₂ g z θ := by
      calc canonW q z θ * |Work.Spaces.mixed (b + 1) a g z θ|
            * |Work.Spaces.mixed b a g z θ|
          = canonW q z θ * (|Work.Spaces.mixed (b + 1) a g z θ|
              * |Work.Spaces.mixed b a g z θ|) := by ring
        _ ≤ canonW q z θ * (((Work.Spaces.mixed (b + 1) a g z θ) ^ 2
              + (Work.Spaces.mixed b a g z θ) ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left hamgm hcw
        _ = (canonW q z θ * (Work.Spaces.mixed (b + 1) a g z θ) ^ 2
              + canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) / 2 := by ring
        _ ≤ Work.Spaces.HkIntegrand α k₁ g z θ + Work.Spaces.HkIntegrand α k₂ g z θ := by
            linarith [Work.Spaces.HkIntegrand_nonneg α k₁ g z θ,
              Work.Spaces.HkIntegrand_nonneg α k₂ g z θ]
    calc ‖canonW q z θ * f z θ * Work.Spaces.mixed (b + 1) a g z θ
            * Work.Spaces.mixed b a g z θ‖
        = canonW q z θ * |f z θ| * |Work.Spaces.mixed (b + 1) a g z θ|
            * |Work.Spaces.mixed b a g z θ| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hcw]
      _ = |f z θ| * (canonW q z θ * |Work.Spaces.mixed (b + 1) a g z θ|
            * |Work.Spaces.mixed b a g z θ|) := by ring
      _ ≤ Mf * (Work.Spaces.HkIntegrand α k₁ g z θ + Work.Spaces.HkIntegrand α k₂ g z θ) :=
          mul_le_mul (hf θ hθ.1 hθ.2) hGY
            (mul_nonneg (mul_nonneg hcw (abs_nonneg _)) (abs_nonneg _)) hMf
  have h1 : ‖∫ θ, canonW q z θ * f z θ * Work.Spaces.mixed (b + 1) a g z θ
        * Work.Spaces.mixed b a g z θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)‖
      ≤ ∫ θ, ‖canonW q z θ * f z θ * Work.Spaces.mixed (b + 1) a g z θ
        * Work.Spaces.mixed b a g z θ‖ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.norm_integral_le_integral_norm _
  have h2 : (∫ θ, ‖canonW q z θ * f z θ * Work.Spaces.mixed (b + 1) a g z θ
        * Work.Spaces.mixed b a g z θ‖ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ≤ ∫ θ, Mf * (Work.Spaces.HkIntegrand α k₁ g z θ + Work.Spaces.HkIntegrand α k₂ g z θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => norm_nonneg _)
      ((hI1.add hI2).const_mul Mf) hpt
  have h3 : (∫ θ, Mf * (Work.Spaces.HkIntegrand α k₁ g z θ + Work.Spaces.HkIntegrand α k₂ g z θ)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = Mf * ((∫ θ, Work.Spaces.HkIntegrand α k₁ g z θ
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          + (∫ θ, Work.Spaces.HkIntegrand α k₂ g z θ
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hI1 hI2]
  rw [← Real.norm_eq_abs]
  exact le_trans h1 (le_trans h2 (le_of_eq h3))

/-! ## Integrability of the radial marginal -/


/-! ## The easy case `a + b ≤ 3` -/


/-! ## The main statement -/


end Work.FTS.TransportS.T2Sup
end
end
