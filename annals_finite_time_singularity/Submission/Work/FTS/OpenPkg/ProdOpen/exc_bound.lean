/-
# `Work.FTS.OpenPkg.ProdOpen.exc_bound`

The two **exceptional terms** of the open-quadrant product rule: the products
`D_z³f · D_θg` and `D_θf · D_z³g` of the `(3,1)`-slot, whose `ℋ⁴`-integrand carries the weight
`W = w · sin(2θ)^{-γ/2}` on **both** factors while `D_z³f` (resp. `D_z³g`) is priced in the norm
only by the *lighter* weight `sin(2θ)^{-η/2}`.

In the classical proof these are handled by Elgindi's Lemma `infinity_separated` (one Hardy
inequality in each variable).  Here they are handled by the *mean term* inequalities of this
chapter:

* for each `z > 0`, the angular estimate `sob_theta_mean` applied to the slice `θ ↦ D_z³f(z,θ)`
  bounds `D_z³f` by an average plus the next mixed slot `D_θD_z³f`;
* the `g`-side factor `(D_θg)² sin(2θ)^{-γ}` is bounded *uniformly in `z`* by `|g|²_{ℋ⁴}`
  (`sliceAng_le` at the slot `(0,1)`).

Both exceptional terms are the *same* estimate with the two functions interchanged (the two
integrands differ only by the order of the two factors), so it is proved once, for a general
pair `(p,q)`, as `exc_pair_bound`, and the two conjuncts of the target are its two instances.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.OpenPkg.ProdOpen.SlicesOpen
import Submission.Work.FTS.OpenPkg.ProdOpen.PwOpen
import Submission.Work.Spaces.ProductTools
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow
import Submission.Work.H2.T1Q.PwBdQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.ProdOpen

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open Work.Spaces
open Work.FTS.EllipticEst (SmoothOpen Q0 mem_Q0)

/-! ## Almost-everywhere strong measurability of partially integrated functions -/

/-- The partially integrated function of a function continuous on `Q0` is a.e. strongly
measurable on `Iz`. -/
theorem aesm_integral_right {F : ℝ → ℝ → ℝ} (hcont : ContinuousOn (Function.uncurry F) Q0) :
    AEStronglyMeasurable (fun z : ℝ => ∫ θ in Iθ, F z θ) (volume.restrict Iz) := by
  have h : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry F) hcont
  have h2 := h.integral_prod_right' (ν := volume.restrict Iθ)
  simpa only [Function.uncurry] using h2

/-! ## Elementary nonnegativity and continuity facts -/

theorem sin_neg_gam_nonneg {α θ : ℝ} (hθ : θ ∈ Iθ) :
    0 ≤ (Real.sin (2 * θ)) ^ (-(gam α)) := by
  apply Real.rpow_nonneg
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem one_le_sin_neg_eta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(eta)) := by
  apply Work.H2.T1Q.one_le_rpow_neg
  · exact sin_two_pos hθ
  · exact Real.sin_le_one _
  · exact le_of_lt eta_pos

theorem continuousOn_sin_neg_gam (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(gam α))) Q0 := by
  have hbase : Continuous fun p : ℝ × ℝ => Real.sin (2 * p.2) := by fun_prop
  refine hbase.continuousOn.rpow_const ?_
  intro p hp
  obtain ⟨-, hθ⟩ := mem_Q0.mp hp
  exact Or.inl (ne_of_gt (Real.sin_pos_of_mem_Ioo
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩))

theorem continuousOn_w_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => w p.1) Q0 := by
  have hfun : (fun p : ℝ × ℝ => w p.1) = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
    funext p; rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) fun p hp => ?_
  exact pow_ne_zero 2 (ne_of_gt (mem_Q0.mp hp).1)

theorem continuousOn_w_sq :
    ContinuousOn (fun p : ℝ × ℝ => (w p.1) ^ 2) Q0 :=
  continuousOn_w_Q0.pow 2

/-- `Wt` on the quadrant is continuous, for every `α`. -/
theorem continuousOn_Wt (α : ℝ) :
    ContinuousOn (fun u : ℝ × ℝ => Wt α u.1 u.2) Q0 := by
  have hfun : (fun u : ℝ × ℝ => Wt α u.1 u.2)
      = fun u : ℝ × ℝ => w u.1 * (Real.sin (2 * u.2)) ^ (-(gam α / 2)) := by
    funext u; rw [Wt, wTheta]
  rw [hfun]
  refine continuousOn_w_Q0.mul ?_
  have hbase : Continuous fun u : ℝ × ℝ => Real.sin (2 * u.2) := by fun_prop
  exact hbase.continuousOn.rpow_const (fun u hu => Or.inl (ne_of_gt
    (Real.sin_pos_of_mem_Ioo ⟨by linarith [(mem_Q0.mp hu).2.1],
      by linarith [(mem_Q0.mp hu).2.2, Real.pi_pos]⟩)))

/-! ## Congruence of the `L²`-vocabulary under pointwise equality -/

theorem L2Mem_congr_pt {g h : ℝ → ℝ → ℝ} (hgh : ∀ z θ, g z θ = h z θ) :
    L2Mem g ↔ L2Mem h := by
  have hfun : g = h := funext fun z => funext fun θ => hgh z θ
  rw [hfun]

theorem L2Sq_congr_pt {g h : ℝ → ℝ → ℝ} (hgh : ∀ z θ, g z θ = h z θ) :
    L2Sq g = L2Sq h := by
  have hfun : g = h := funext fun z => funext fun θ => hgh z θ
  rw [hfun]

/-! ## Pointwise domination of the individual slots -/

/-- The weighted square of a pure `D_z`-slot is dominated by the `ℋ⁴`-integrand. -/
theorem dzIter_sq_w_sq_le {α : ℝ} (hα : 0 < α) (f : ℝ → ℝ → ℝ) (j : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hj : j ≤ 4) :
    (DzIter j f z θ) ^ 2 * (w z) ^ 2 ≤ HkIntegrand α 4 f z θ := by
  have hsin : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have hη := one_le_sin_neg_eta hθ
  calc (DzIter j f z θ) ^ 2 * (w z) ^ 2
      = (DzIter j f z θ) ^ 2 * (w z) ^ 2 * 1 := by ring
    _ ≤ (DzIter j f z θ) ^ 2 * (w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(eta)) :=
        mul_le_mul_of_nonneg_left hη (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = (DzIter j f z θ
          * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 := by
        rw [mul_pow, Work.H2.T1Q.div_rpow_sq (w z) (Real.sin (2 * θ)) eta hsin]
        ring
    _ ≤ HkIntegrand α 4 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ j hj

/-! ## Integrability of the slices -/

/-- The `θ`-slice of `(D_θg)² sin(2·)^{-γ}` is integrable. -/
theorem integrableOn_dth_sq {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} (hG : SmoothOpen g)
    (hmemG : HkMem α 4 g) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (Dth g z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α))) Iθ := by
  have hcont : ContinuousOn (fun θ : ℝ => (Dth g z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α))) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hbase : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
    exact (((hG.Dth).curry_θ hz).continuousOn.pow 2).mul
      (hbase.continuousOn.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ))))
  refine Integrable.mono' (hmemG.1 z hz.le)
    (Work.H2.T1Q.aesm_Iθ_of_continuousOn hcont) ?_
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  have hsinpos : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have hw1 : (1 : ℝ) ≤ (w z) ^ 2 := by nlinarith [one_le_w_of_pos hz]
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsinpos.le _))]
  have hkey : (Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
      ≤ (mixed 0 1 g z θ * Wt α z θ) ^ 2 := by
    rw [show (mixed 0 1 g z θ * Wt α z θ) ^ 2
        = (Dth g z θ) ^ 2 * ((w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) from by
      rw [show mixed 0 1 g = Dth g from by
          simp only [mixed_zero_left, DthIter_succ, DthIter_zero], mul_pow,
        Work.H2.T1Q.Wt_sq_eq α z θ hsinpos]]
    exact mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left (Real.rpow_nonneg hsinpos.le _) hw1) (sq_nonneg _)
  exact le_trans hkey (sq_le_HkIntegrand_mixed α 4 g z θ 1 0 (by norm_num) (by norm_num))

/-- The `θ`-slice of `(D_z³f)²` is integrable. -/
theorem integrableOn_dzIter3_sq {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (hF : SmoothOpen f)
    (hmemF : HkMem α 4 f) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (DzIter 3 f z θ) ^ 2) Iθ := by
  have h := integrableOn_slice_sq hα hF hmemF 3 0 (by norm_num) hz
  rwa [show (fun σ : ℝ => (mixed 3 0 f z σ) ^ 2)
    = fun σ : ℝ => (DzIter 3 f z σ) ^ 2 from by
      funext σ; simp [mixed_zero_right]] at h

/-- The `θ`-slice of `(D_z³f · D_θg · W)²` is integrable at every `z > 0`. -/
theorem integrableOn_excA {α : ℝ} (hα : 0 < α) {f g : ℝ → ℝ → ℝ} (hF : SmoothOpen f)
    (hmemF : HkMem α 4 f) (hG : SmoothOpen g) (hmemG : HkMem α 4 g)
    {C1 : ℝ} (hC1pos : 0 < C1)
    (hC1 : ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (DzIter 3 f z θ) ^ 2 ≤ C1 * ((∫ σ in Iθ, (DzIter 3 f z σ) ^ 2)
        + (gam α - 1)⁻¹ * ∫ σ in Iθ, (mixed 3 1 f z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(gam α))))
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (DzIter 3 f z θ * Dth g z θ
      * Wt α z θ) ^ 2) Iθ := by
  set K : ℝ := C1 * ((∫ σ in Iθ, (DzIter 3 f z σ) ^ 2)
    + (gam α - 1)⁻¹ * ∫ σ in Iθ, (mixed 3 1 f z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (-(gam α))) with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    refine mul_nonneg hC1pos.le ?_
    refine add_nonneg (integral_nonneg fun σ => sq_nonneg _) ?_
    have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
    exact mul_nonneg (inv_nonneg.mpr hγ.le)
      (setIntegral_nonneg measurableSet_Icc fun σ hσ =>
        mul_nonneg (sq_nonneg _) (sin_neg_gam_nonneg hσ))
  have hGint : IntegrableOn (fun θ => (Dth g z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α))) Iθ := integrableOn_dth_sq hα hG hmemG hz
  refine Integrable.mono' (hGint.const_mul (K * (w z) ^ 2)) ?_ ?_
  · have hcont : ContinuousOn (fun θ : ℝ => (DzIter 3 f z θ
        * Dth g z θ * Wt α z θ) ^ 2)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h1 : ContinuousOn (fun θ : ℝ => DzIter 3 f z θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := ((hF.DzIter 3).curry_θ hz).continuousOn
      have h2 : ContinuousOn (fun θ : ℝ => Dth g z θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := ((hG.Dth).curry_θ hz).continuousOn
      have hb : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(gam α / 2)))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        (show Continuous fun θ : ℝ => Real.sin (2 * θ) from by fun_prop).continuousOn.rpow_const
          (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ)))
      have h3 : ContinuousOn (fun θ : ℝ => Wt α z θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
        have hfun : (fun θ : ℝ => Wt α z θ)
            = fun θ : ℝ => w z
              * (Real.sin (2 * θ)) ^ (-(gam α / 2)) := by
          funext θ; rw [Wt, wTheta]
        rw [hfun]
        exact continuousOn_const.mul hb
      exact ((h1.mul h2).mul h3).pow 2
    exact Work.H2.T1Q.aesm_Iθ_of_continuousOn hcont
  · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hsin : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have h1 := hC1 z hz θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    rw [show (DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2
        = ((DzIter 3 f z θ) ^ 2 * (w z) ^ 2)
          * ((Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) from by
      rw [mul_pow, mul_pow, Work.H2.T1Q.Wt_sq_eq α z θ hsin]
      ring]
    rw [← hKdef] at h1
    have hstep : (DzIter 3 f z θ) ^ 2 * (w z) ^ 2 ≤ K * (w z) ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right hstep
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _))

/-! ## The exceptional term, for a general pair of functions -/

/-- **The exceptional term of the `(3,1)`-slot**, for a general ordered pair `(p,q)`: the
function `D_z³p · D_θq · W` is square integrable and its `L²`-square is bounded by
`C (γ-1)⁻¹ |p|²_{ℋ⁴} |q|²_{ℋ⁴}`.

The `p`-factor is bounded pointwise through the *mean term* angular inequality applied to the
slice `θ ↦ D_z³p(z,θ)` (the mean term being the `θ`-average of `(D_z³p)²` and the next mixed
slot `D_z³D_θp`), while the `q`-factor `(D_θq)² sin(2·)^{-γ}` is bounded uniformly in `z` by
`sliceAng_le` at the slot `(0,1)`. -/
theorem exc_pair_bound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (p q : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    SmoothOpen p → HkMem α 4 p → SmoothOpen q → HkMem α 4 q →
    L2Mem (fun z θ => DzIter 3 p z θ * Dth q z θ * Wt α z θ) ∧
    L2Sq (fun z θ => DzIter 3 p z θ * Dth q z θ * Wt α z θ)
      ≤ C / (gam α - 1) * HkSq α 4 p * HkSq α 4 q := by
  obtain ⟨C1, hC1pos, hC1⟩ := sob_theta_mean
  obtain ⟨Cq, hCqpos, hCq⟩ := sliceAng_le
  have hMq : (0 : ℝ) < max Cq 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨2 * C1 * max Cq 1, by positivity, ?_⟩
  intro α p q hα hα1 hP hmemP hQ hmemQ
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγle : gam α - 1 ≤ 1 := by rw [gam_sub_one]; linarith
  have hHkP : 0 ≤ HkSq α 4 p := HkSq_nonneg α 4 p
  have hHkQ : 0 ≤ HkSq α 4 q := HkSq_nonneg α 4 q
  have hγinv : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr hγ.le
  set M1 : ℝ → ℝ := fun z => ∫ θ in Iθ, (DzIter 3 p z θ) ^ 2 with hM1def
  set M2 : ℝ → ℝ := fun z => ∫ θ in Iθ, (mixed 3 1 p z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α)) with hM2def
  set J : ℝ → ℝ := fun z => ∫ θ in Iθ, (Dth q z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α)) with hJdef
  have hM1val : ∀ z : ℝ, M1 z = ∫ θ in Iθ, (DzIter 3 p z θ) ^ 2 := fun z => by
    simp only [hM1def]
  have hM2val : ∀ z : ℝ, M2 z = ∫ θ in Iθ, (mixed 3 1 p z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α)) := fun z => by simp only [hM2def]
  have hJval : ∀ z : ℝ, J z = ∫ θ in Iθ, (Dth q z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α)) := fun z => by simp only [hJdef]
  have hM1nn : ∀ z, 0 ≤ M1 z := fun z => by
    rw [hM1val z]; exact integral_nonneg fun θ => sq_nonneg _
  have hM2nn : ∀ z, 0 ≤ M2 z := fun z => by
    rw [hM2val z]; exact setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (sin_neg_gam_nonneg hθ)
  have hJnn : ∀ z, 0 ≤ J z := fun z => by
    rw [hJval z]; exact setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (sin_neg_gam_nonneg hθ)
  -- (1) the `q`-side is uniformly bounded by the `ℋ⁴`-norm of `q`
  have hJbd : ∀ z : ℝ, 0 < z → J z ≤ max Cq 1 * HkSq α 4 q := by
    intro z hz
    have h := hCq α q 0 1 hα hα1 hQ hmemQ (le_refl 1) (by norm_num) z hz
    have hfun : (fun θ : ℝ => (mixed 0 1 q z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(gam α)))
        = fun θ : ℝ => (Dth q z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
      funext θ
      simp only [mixed_zero_left, DthIter_succ, DthIter_zero]
    rw [hfun] at h
    rw [hJval z]
    exact le_trans h (mul_le_mul_of_nonneg_right (le_max_left Cq 1) hHkQ)
  -- (2) the angular mean-term estimate on the `p`-slice, at every `z > 0`
  have hsob : ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (DzIter 3 p z θ) ^ 2 ≤ C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) := by
    intro z hz θ hθ
    have hder : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        HasDerivAt (fun σ' : ℝ => DzIter 3 p z σ')
          (deriv (fun σ' : ℝ => DzIter 3 p z σ') x) x := by
      intro x hx
      exact (((hP.DzIter 3).curry_θ hz).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds hx) |>.hasDerivAt
    have hcontd : ContinuousOn (deriv (fun σ' : ℝ => DzIter 3 p z σ'))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h : ContinuousOn (fun σ => pth (DzIter 3 p) z σ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := ((hP.DzIter 3).pth.curry_θ hz).continuousOn
      simpa only [pth] using h
    have hint1 : IntegrableOn (fun σ => (DzIter 3 p z σ) ^ 2) Iθ :=
      integrableOn_dzIter3_sq hα hP hmemP hz
    have hBeq : (∫ σ in Iθ, (deriv (fun σ' : ℝ => DzIter 3 p z σ') σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - gam α))
        = ∫ σ in Iθ, (mixed 3 1 p z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(gam α)) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_mem_Ioo_Iθ] with σ hσ
      have h := deriv_mixed_weight α hP 3 0 hz hσ
      rwa [show mixed 3 (0 + 1) p = mixed 3 1 p from by norm_num] at h
    have hint2 : IntegrableOn (fun σ => (deriv (fun σ' : ℝ => DzIter 3 p z σ') σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - gam α)) Iθ := by
      have h := integrableOn_slice_neg_gam hα hP hmemP 3 1 (le_refl 1) (by norm_num) hz
      refine h.congr ?_
      filter_upwards [ae_mem_Ioo_Iθ] with σ hσ
      exact (deriv_mixed_weight α hP 3 0 hz hσ).symm
    have hmain := hC1 α (fun σ' : ℝ => DzIter 3 p z σ') θ hα hα1 hθ hder hcontd
      hint1 hint2
    rw [hBeq] at hmain
    rw [← hM1val z, ← hM2val z] at hmain
    exact hmain
  -- (3) pointwise domination of the two slice integrals by the `ℋ⁴`-integrand of `p`
  have hM1dom : ∀ z : ℝ, 0 < z →
      M1 z * (w z) ^ 2 ≤ ∫ θ in Iθ, HkIntegrand α 4 p z θ := by
    intro z hz
    have hfeq : M1 z * (w z) ^ 2
        = ∫ θ in Iθ, (DzIter 3 p z θ) ^ 2 * (w z) ^ 2 := by
      rw [hM1val z]
      exact (integral_mul_const ((w z) ^ 2)
        (fun θ : ℝ => (DzIter 3 p z θ) ^ 2)).symm
    rw [hfeq]
    refine integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Icc fun θ _ =>
        mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hmemP.1 z hz.le) ?_
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    exact dzIter_sq_w_sq_le hα p 3 hz hθ (by norm_num)
  have hM2dom : ∀ z : ℝ, 0 < z →
      M2 z * (w z) ^ 2 ≤ ∫ θ in Iθ, HkIntegrand α 4 p z θ := by
    intro z hz
    have hfeq : M2 z * (w z) ^ 2 = ∫ θ in Iθ, (mixed 3 1 p z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(gam α)) * (w z) ^ 2 := by
      rw [hM2val z]
      have hfun : (fun θ : ℝ => (mixed 3 1 p z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(gam α)) * (w z) ^ 2)
          = fun θ : ℝ => ((mixed 3 1 p z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(gam α))) * (w z) ^ 2 := rfl
      rw [hfun]
      exact (integral_mul_const ((w z) ^ 2)
        (fun θ : ℝ => (mixed 3 1 p z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(gam α)))).symm
    rw [hfeq]
    refine integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (sin_neg_gam_nonneg hθ)) (sq_nonneg _))
      (hmemP.1 z hz.le) ?_
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hsin : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hkey : (mixed 3 1 p z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
          * (w z) ^ 2
        = (mixed 3 1 p z θ * Wt α z θ) ^ 2 := by
      rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z θ hsin]; ring
    rw [hkey]
    exact sq_le_HkIntegrand_mixed α 4 p z θ 1 3 (by norm_num) (by norm_num)
  -- (4) a.e. strong measurability and `z`-integrability of the two slice integrals
  have hAESM1 : AEStronglyMeasurable (fun z : ℝ => M1 z * (w z) ^ 2) (volume.restrict Iz) := by
    have hcont : ContinuousOn (Function.uncurry
        (fun z θ : ℝ => (DzIter 3 p z θ) ^ 2 * (w z) ^ 2)) Q0 := by
      show ContinuousOn (fun u : ℝ × ℝ => (DzIter 3 p u.1 u.2) ^ 2
        * (w u.1) ^ 2) Q0
      exact ((hP.DzIter 3).continuousOn.pow 2).mul continuousOn_w_sq
    have h := aesm_integral_right (F := fun z θ =>
      (DzIter 3 p z θ) ^ 2 * (w z) ^ 2) hcont
    have h2 : (fun z : ℝ => ∫ θ in Iθ, (DzIter 3 p z θ) ^ 2 * (w z) ^ 2)
        = fun z : ℝ => M1 z * (w z) ^ 2 := by
      funext z
      rw [hM1val z]
      exact integral_mul_const ((w z) ^ 2)
        (fun θ : ℝ => (DzIter 3 p z θ) ^ 2)
    rwa [h2] at h
  have hAESM2 : AEStronglyMeasurable (fun z : ℝ => M2 z * (w z) ^ 2) (volume.restrict Iz) := by
    have hcont : ContinuousOn (Function.uncurry (fun z θ : ℝ =>
        (mixed 3 1 p z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) * (w z) ^ 2)) Q0 := by
      show ContinuousOn (fun u : ℝ × ℝ => (mixed 3 1 p u.1 u.2) ^ 2
        * (Real.sin (2 * u.2)) ^ (-(gam α)) * (w u.1) ^ 2) Q0
      exact (((hP.mixed 3 1).continuousOn.pow 2).mul (continuousOn_sin_neg_gam α)).mul
        continuousOn_w_sq
    have h := aesm_integral_right (F := fun z θ => (mixed 3 1 p z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α)) * (w z) ^ 2) hcont
    have h2 : (fun z : ℝ => ∫ θ in Iθ, (mixed 3 1 p z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(gam α)) * (w z) ^ 2)
        = fun z : ℝ => M2 z * (w z) ^ 2 := by
      funext z
      rw [hM2val z]
      exact integral_mul_const ((w z) ^ 2)
        (fun θ : ℝ => (mixed 3 1 p z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(gam α)))
    rwa [h2] at h
  have hAESMJ : AEStronglyMeasurable J (volume.restrict Iz) := by
    have hcont : ContinuousOn (Function.uncurry (fun z θ : ℝ =>
        (Dth q z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)))) Q0 := by
      show ContinuousOn (fun u : ℝ × ℝ => (Dth q u.1 u.2) ^ 2
        * (Real.sin (2 * u.2)) ^ (-(gam α))) Q0
      exact ((hQ.Dth).continuousOn.pow 2).mul (continuousOn_sin_neg_gam α)
    have h := aesm_integral_right (F := fun z θ => (Dth q z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(gam α))) hcont
    exact h
  have hInt1 : Integrable (fun z : ℝ => M1 z * (w z) ^ 2) (volume.restrict Iz) := by
    refine Integrable.mono' hmemP.2 hAESM1 ?_
    filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz
    rw [Real.norm_of_nonneg (mul_nonneg (hM1nn z) (sq_nonneg _))]
    exact hM1dom z hz
  have hInt2 : Integrable (fun z : ℝ => M2 z * (w z) ^ 2) (volume.restrict Iz) := by
    refine Integrable.mono' hmemP.2 hAESM2 ?_
    filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz
    rw [Real.norm_of_nonneg (mul_nonneg (hM2nn z) (sq_nonneg _))]
    exact hM2dom z hz
  have hz1 : (∫ z in Iz, M1 z * (w z) ^ 2) ≤ HkSq α 4 p := by
    have h := integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
        mul_nonneg (hM1nn z) (sq_nonneg _)) hmemP.2
      (by filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz; exact hM1dom z hz)
    exact h
  have hz2 : (∫ z in Iz, M2 z * (w z) ^ 2) ≤ HkSq α 4 p := by
    have h := integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
        mul_nonneg (hM2nn z) (sq_nonneg _)) hmemP.2
      (by filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz; exact hM2dom z hz)
    exact h
  -- (5) the per-`z` bound on the angular integral of the exceptional integrand
  have hzpt : ∀ z : ℝ, 0 < z → (∫ θ in Iθ, (DzIter 3 p z θ
        * Dth q z θ * Wt α z θ) ^ 2)
      ≤ C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2 * J z := by
    intro z hz
    have hGint := (integrableOn_dth_sq hα hQ hmemQ hz).const_mul
      (C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2)
    have hpt : ∀ᵐ θ ∂(volume.restrict Iθ),
        (DzIter 3 p z θ * Dth q z θ * Wt α z θ) ^ 2
        ≤ (C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2)
          * ((Dth q z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) := by
      filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      have hsin : 0 < Real.sin (2 * θ) := sin_two_pos hθ
      have h1 := hsob z hz θ hθ
      rw [show (DzIter 3 p z θ * Dth q z θ * Wt α z θ) ^ 2
          = ((DzIter 3 p z θ) ^ 2 * (w z) ^ 2)
            * ((Dth q z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) from by
          rw [mul_pow, mul_pow, Work.H2.T1Q.Wt_sq_eq α z θ hsin]; ring]
      have hstep : (DzIter 3 p z θ) ^ 2 * (w z) ^ 2
          ≤ C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right hstep
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _))
    refine le_trans (integral_mono_of_nonneg ?_ hGint hpt) ?_
    · exact ae_restrict_of_forall_mem measurableSet_Icc fun θ _ => sq_nonneg _
    · rw [integral_const_mul, hJval z]
  -- (6) integrability of the `max`-majorant
  have hmajInt : Integrable (fun z : ℝ => C1 * (M1 z + (gam α - 1)⁻¹ * M2 z)
      * (w z) ^ 2 * (max Cq 1 * HkSq α 4 q)) (volume.restrict Iz) := by
    have hbase : Integrable (fun z : ℝ => C1 * (max Cq 1 * HkSq α 4 q) * (M1 z * (w z) ^ 2)
        + C1 * (max Cq 1 * HkSq α 4 q) * ((gam α - 1)⁻¹ * (M2 z * (w z) ^ 2)))
        (volume.restrict Iz) :=
      (hInt1.const_mul (C1 * (max Cq 1 * HkSq α 4 q))).add
        ((hInt2.const_mul (gam α - 1)⁻¹).const_mul (C1 * (max Cq 1 * HkSq α 4 q)))
    refine Integrable.mono' hbase ?_ ?_
    · have h1 : AEStronglyMeasurable (fun z : ℝ => C1 * (max Cq 1 * HkSq α 4 q)
          * (M1 z * (w z) ^ 2)
          + C1 * (max Cq 1 * HkSq α 4 q) * ((gam α - 1)⁻¹ * (M2 z * (w z) ^ 2)))
          (volume.restrict Iz) :=
        (hAESM1.const_mul _).add ((hAESM2.const_mul _).const_mul _)
      refine h1.congr ?_
      filter_upwards with z
      ring
    · filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC1pos.le
        (add_nonneg (hM1nn z) (mul_nonneg hγinv (hM2nn z)))) (sq_nonneg _))
        (mul_nonneg hMq.le hHkQ))]
      ring_nf
      nlinarith [hM1nn z, hM2nn z, sq_nonneg (w z), hγinv, hHkP, hHkQ, hMq]
  -- (7) the `L²`-square bound
  have hL2Sq : L2Sq (fun z θ => DzIter 3 p z θ * Dth q z θ
        * Wt α z θ)
      ≤ 2 * C1 * max Cq 1 / (gam α - 1) * HkSq α 4 p * HkSq α 4 q := by
    rw [L2Sq]
    have hB : (∫ z in Iz, ∫ θ in Iθ, (DzIter 3 p z θ * Dth q z θ
          * Wt α z θ) ^ 2)
        ≤ ∫ z in Iz, C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2
            * (max Cq 1 * HkSq α 4 q) := by
      refine integral_mono_of_nonneg ?_ hmajInt ?_
      · exact ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
          integral_nonneg fun θ => sq_nonneg _
      · filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz
        exact le_trans (hzpt z hz) (mul_le_mul_of_nonneg_left (hJbd z hz) (mul_nonneg
          (mul_nonneg hC1pos.le (add_nonneg (hM1nn z) (mul_nonneg hγinv (hM2nn z))))
          (sq_nonneg _)))
    refine le_trans hB ?_
    have hC : (∫ z in Iz, C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2
          * (max Cq 1 * HkSq α 4 q))
        = C1 * (max Cq 1 * HkSq α 4 q) * ((∫ z in Iz, M1 z * (w z) ^ 2)
            + (gam α - 1)⁻¹ * (∫ z in Iz, M2 z * (w z) ^ 2)) := by
      have hfun1 : (fun z : ℝ => C1 * (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2
            * (max Cq 1 * HkSq α 4 q))
          = fun z : ℝ => (C1 * (max Cq 1 * HkSq α 4 q))
            * ((M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2) := by
        funext z; ring
      rw [hfun1, integral_const_mul]
      have hfun2 : (fun z : ℝ => (M1 z + (gam α - 1)⁻¹ * M2 z) * (w z) ^ 2)
          = fun z : ℝ => M1 z * (w z) ^ 2
            + ((gam α - 1)⁻¹ * (M2 z * (w z) ^ 2)) := by
        funext z; ring
      rw [hfun2, integral_add hInt1 (hInt2.const_mul (gam α - 1)⁻¹)]
      rw [integral_const_mul]
    rw [hC]
    have hX : (∫ z in Iz, M1 z * (w z) ^ 2) + (gam α - 1)⁻¹
          * (∫ z in Iz, M2 z * (w z) ^ 2)
        ≤ 2 * (gam α - 1)⁻¹ * HkSq α 4 p := by
      have h1 : (1 : ℝ) ≤ (gam α - 1)⁻¹ := by
        rw [one_le_inv₀ hγ]; simpa using hγle
      have hA1 : (∫ z in Iz, M1 z * (w z) ^ 2) ≤ (gam α - 1)⁻¹ * HkSq α 4 p :=
        le_trans hz1 (le_mul_of_one_le_left hHkP h1)
      have hA2 : (gam α - 1)⁻¹ * (∫ z in Iz, M2 z * (w z) ^ 2)
          ≤ (gam α - 1)⁻¹ * HkSq α 4 p := mul_le_mul_of_nonneg_left hz2 hγinv
      linarith
    have hfac : 0 ≤ C1 * (max Cq 1 * HkSq α 4 q) :=
      mul_nonneg hC1pos.le (mul_nonneg hMq.le hHkQ)
    have hstep := mul_le_mul_of_nonneg_left hX hfac
    refine le_trans hstep (le_of_eq ?_)
    rw [div_eq_mul_inv]; ring
  refine ⟨⟨?_, ?_⟩, hL2Sq⟩
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
    · subst h0
      have hzero : (fun θ : ℝ => (DzIter 3 p 0 θ * Dth q 0 θ
          * Wt α 0 θ) ^ 2) = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        have hw0 : w (0 : ℝ) = 0 := by simp [w]
        simp [Wt, hw0]
      rw [hzero]
      exact integrableOn_zero
    · exact integrableOn_excA hα hP hmemP hQ hmemQ hC1pos
        (fun z hz θ hθ => hsob z hz θ hθ) hpos
  · have haesm : AEStronglyMeasurable (fun z : ℝ => ∫ θ in Iθ,
        (DzIter 3 p z θ * Dth q z θ * Wt α z θ) ^ 2)
        (volume.restrict Iz) := by
      refine aesm_integral_right (F := fun z θ => (DzIter 3 p z θ
        * Dth q z θ * Wt α z θ) ^ 2) ?_
      have hW := continuousOn_Wt (α := α)
      exact (((hP.DzIter 3).continuousOn.mul (hQ.Dth).continuousOn).mul hW).pow 2
    refine Integrable.mono' hmajInt haesm ?_
    filter_upwards [Work.H2.T1Q.ae_pos_Iz] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact le_trans (hzpt z hz) (mul_le_mul_of_nonneg_left (hJbd z hz) (mul_nonneg
      (mul_nonneg hC1pos.le (add_nonneg (hM1nn z) (mul_nonneg hγinv (hM2nn z))))
      (sq_nonneg _)))

/-! ## The target: the two exceptional terms -/

theorem exc_bound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
    (Work.Spaces.L2Mem (fun z θ => Work.Spaces.DzIter 3 f z θ * Work.Spaces.Dth g z θ
        * Work.Spaces.Wt α z θ) ∧
      Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter 3 f z θ * Work.Spaces.Dth g z θ
        * Work.Spaces.Wt α z θ) ≤ C / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f
          * Work.Spaces.HkSq α 4 g)
    ∧ (Work.Spaces.L2Mem (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.DzIter 3 g z θ
        * Work.Spaces.Wt α z θ) ∧
      Work.Spaces.L2Sq (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.DzIter 3 g z θ
        * Work.Spaces.Wt α z θ) ≤ C / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f
          * Work.Spaces.HkSq α 4 g) := by
  obtain ⟨C, hCpos, hC⟩ := exc_pair_bound
  refine ⟨C, hCpos, ?_⟩
  intro α f g hα hα1 hF hmemF hG hmemG
  obtain ⟨hA1, hA2⟩ := hC α f g hα hα1 hF hmemF hG hmemG
  obtain ⟨hB1, hB2⟩ := hC α g f hα hα1 hG hmemG hF hmemF
  refine ⟨⟨hA1, hA2⟩, ?_, ?_⟩
  · have hcongr : L2Mem (fun z θ => Dth f z θ * DzIter 3 g z θ * Wt α z θ)
        ↔ L2Mem (fun z θ => DzIter 3 g z θ * Dth f z θ * Wt α z θ) :=
      L2Mem_congr_pt (fun z θ => by ring)
    exact hcongr.mpr hB1
  · have hcongr : L2Sq (fun z θ => Dth f z θ * DzIter 3 g z θ * Wt α z θ)
        = L2Sq (fun z θ => DzIter 3 g z θ * Dth f z θ * Wt α z θ) :=
      L2Sq_congr_pt (fun z θ => by ring)
    rw [hcongr]
    refine le_trans hB2 (le_of_eq ?_)
    ring

end Work.FTS.OpenPkg.ProdOpen
