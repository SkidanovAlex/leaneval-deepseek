import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.dzSelf2dW
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.leafGamPureZ_b1fiveAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.MismatchHardB5
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.sigmaDivisibility
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.thetaHardyLeft
import Submission.Work.FTS.StrongPersist.SP6.Flat6Defs
import Submission.Work.FTS.StrongPersist.SP6.PthEVzR
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3BadAux.slot_slice_le
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_MuLipC.RowN.PvAesmOpen
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12ShiftThetaAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Helpers for `L12ShiftThetaLe` — the `k = 0` term of the `L₁₂·D_θ` slot expansion

The target `Work.FTS.StrongPersist.H6Pair6Aux.L12ShiftThetaLe` bounds

  `|∫_z L₁₂f(z)·∫_θ ρ·(D_z^bD_θ^{a+1}f)·(D_z^bD_θ^a f)| ≤ C·|f|_{ℋ⁴}·|f|²_{ℋ⁶}`

for a leaf weight `ρ = w(z)²·sin(2θ)^{-q}` (`q = η`, `0` or `γ`).  This file collects the
elementary ingredients:

* `leafdom_rpow`: the pointwise domination `w² sin(2θ)^{-q}·(D_z^bD_θ^ah)² ≤ HkIntegrand α k h`
  for a general exponent `q` (the level-`k` version of `Work.FTS.IPGen.leaf_dom`);
* `ae_prod_mem_Q0`, `ae_prod_fst_pos`: the open quadrant is conull for the product measure
  `(volume.restrict Iz).prod (volume.restrict Iθ)`;
* `continuousOn_w_sq`, `continuousOn_sin_two_rpow_neg`, `continuousOn_cos_mul_sin_rpow_neg`,
  `continuousOn_L12`: the continuity of the individual factors on the open quadrant resp. the
  open half-line;
* `aesm_uncurry_mul`: the a.e. strong measurability of `(z,θ) ↦ A z · B θ · C z θ`;
* `dth_mixed_eqOn_Q0`, `dth_mixed_ae_eq`: `D_θ(D_z^bD_θ^a f) = D_z^bD_θ^{a+1} f` on the open
  quadrant / a.e. for the product measure.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## The pointwise slot domination with a general exponent `q` -/

/-- **The pointwise domination of a leaf weight `w²·sin(2θ)^{-q}` by the `ℋ^k`-integrand.**

For `a + b ≤ k`, an exponent `q` with `q ≤ γ` (and `q ≤ η` when `a = 0`), and
`z ∈ Iz`, `θ ∈ (0,π/2)`,

  `w(z)²·sin(2θ)^{-q}·(D_z^bD_θ^ah)² ≤ HkIntegrand α k h`.

Each leaf weight is the square of one of the block weights `Whz = w σ^{-η/2}`, `1` and
`Wm = W σ^{-γ/2}`, and the blocks of `HkIntegrand α k` are exactly the squares of those
weights times the slots (`Work.Spaces.sq_le_HkIntegrand_z`, `..._mixed`). -/
theorem leafdom_rpow {α : ℝ} (hα : 0 < α) {q : ℝ} {a b k : ℕ} (hab : a + b ≤ k)
    (hqle : q ≤ Work.Spaces.gam α) (hq0 : a = 0 → q ≤ Work.Spaces.eta)
    {h : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (Work.Spaces.mixed b a h z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k h z θ := by
  have hσ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    rw [Work.Spaces.mixed_zero_right]
    have hb : b ≤ k := by omega
    have hq : q ≤ Work.Spaces.eta := hq0 rfl
    have hle : (Real.sin (2 * θ)) ^ (-q) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Real.rpow_le_rpow_of_exponent_ge hσ hσ1 (by linarith)
    have hkey : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.DzIter b h z θ) ^ 2
        = (Work.Spaces.DzIter b h z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      rw [Work.Spaces.sq_mul_div_rpow _ _ _ _ hσ.le (by norm_num [Work.Spaces.eta])]
      ring
    calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.DzIter b h z θ) ^ 2
        = (Work.Spaces.w z) ^ 2
            * ((Real.sin (2 * θ)) ^ (-q) * (Work.Spaces.DzIter b h z θ) ^ 2) := by ring
      _ ≤ (Work.Spaces.w z) ^ 2
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              * (Work.Spaces.DzIter b h z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hle (sq_nonneg _)) (sq_nonneg _)
      _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.DzIter b h z θ) ^ 2 := by ring
      _ = (Work.Spaces.DzIter b h z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := hkey
      _ ≤ Work.Spaces.HkIntegrand α k h z θ := Work.Spaces.sq_le_HkIntegrand_z α k h z θ b hb
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    have hle : (Real.sin (2 * θ)) ^ (-q) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      Real.rpow_le_rpow_of_exponent_ge hσ hσ1 (by linarith)
    have hWm := Work.FTS.H2.hbi_Wm_sq α z θ hσ.le
    simp only [Work.FTS.H2.Wm] at hWm
    calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a h z θ) ^ 2
        = (Work.Spaces.w z) ^ 2
            * ((Real.sin (2 * θ)) ^ (-q) * (Work.Spaces.mixed b a h z θ) ^ 2) := by ring
      _ ≤ (Work.Spaces.w z) ^ 2
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed b a h z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hle (sq_nonneg _)) (sq_nonneg _)
      _ = (Work.Spaces.Wt α z θ) ^ 2 * (Work.Spaces.mixed b a h z θ) ^ 2 := by rw [hWm]; ring
      _ = (Work.Spaces.mixed b a h z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α k h z θ :=
          Work.Spaces.sq_le_HkIntegrand_mixed α k h z θ a b ha1 (by omega)

/-! ## The open quadrant is conull -/

/-- The open quadrant `Q0` is conull for the product measure
`(volume.restrict Iz).prod (volume.restrict Iθ)`: its complement is contained in the
coordinate hyperplanes, each of which is null. -/
theorem ae_prod_mem_Q0 :
    ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      p ∈ Work.FTS.EllipticEst.Q0 := by
  have hz : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[volume.prod volume] Work.FTS.EllipticEst.Q0 :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  have h1 : (volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume.prod volume).restrict Work.FTS.EllipticEst.Q0 :=
    MeasureTheory.Measure.restrict_congr_set hprod
  rw [MeasureTheory.Measure.prod_restrict, h1]
  exact MeasureTheory.ae_restrict_mem Work.FTS.EllipticEst.isOpen_Q0.measurableSet

/-- For the product measure, `z > 0` almost everywhere. -/
theorem ae_prod_fst_pos :
    ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      0 < p.1 :=
  ae_prod_mem_Q0.mono fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1

/-! ## Continuity of the individual weight factors -/

/-- `(w z)²` is continuous on `(0,∞)`. -/
theorem continuousOn_w_sq : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2) = fun z => (((1 + z) ^ 2 / z ^ 2) ^ 2) := by
    funext z; rw [Work.Spaces.w]
  rw [hfun]
  refine ContinuousOn.pow ?_ 2
  refine ContinuousOn.div ?_ ?_ ?_
  · exact (continuousOn_const.add continuousOn_id).pow 2
  · exact continuousOn_id.pow 2
  · intro z hz; exact pow_ne_zero 2 (ne_of_gt (Set.mem_Ioi.mp hz))

/-- `sin(2θ)^{-q}` is continuous on the open angular interval. -/
theorem continuousOn_sin_two_rpow_neg (q : ℝ) :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q)) (Set.Ioo 0 (π / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (π / 2)) := by fun_prop
  refine hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt ?_))
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])


/-- `L₁₂(f)` is continuous on `(0,∞)` for `f` smooth on the open quadrant with honest
`ℋ⁶`-integral. -/
theorem continuousOn_L12 {α : ℝ} {f : ℝ → ℝ → ℝ} (hO : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem6 : Work.Spaces.HkMem α 6 f) :
    ContinuousOn (Work.Construction.L12 f) (Set.Ioi 0) :=
  (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 6 f hO hmem6
    (by norm_num)).1.continuousOn

/-! ## A.e. strong measurability of products `(z,θ) ↦ A z · B θ · C z θ` -/

/-- If `A` is continuous on `(0,∞)`, `B` on `(0,π/2)` and the uncurried `C` is continuous on
the open quadrant, then `(z,θ) ↦ A z · B θ · C z θ` is a.e. strongly measurable for the
product measure. -/
theorem aesm_uncurry_mul {A B : ℝ → ℝ} {C : ℝ → ℝ → ℝ}
    (hA : ContinuousOn A (Set.Ioi 0)) (hB : ContinuousOn B (Set.Ioo 0 (π / 2)))
    (hC : ContinuousOn (Function.uncurry C) Work.FTS.EllipticEst.Q0) :
    AEStronglyMeasurable (Function.uncurry (fun z θ => A z * B θ * C z θ))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
  have h1 : ContinuousOn (fun p : ℝ × ℝ => A p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hA.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have h2 : ContinuousOn (fun p : ℝ × ℝ => B p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hB.comp continuous_snd.continuousOn (fun p hp => hp.2)
  exact (h1.mul h2).mul hC

/-- The uncurried form of a product of two `C`-functions on the open quadrant. -/
theorem continuousOn_uncurry_mul {C D : ℝ → ℝ → ℝ}
    (hC : ContinuousOn (Function.uncurry C) Work.FTS.EllipticEst.Q0)
    (hD : ContinuousOn (Function.uncurry D) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (Function.uncurry (fun z θ => C z θ * D z θ)) Work.FTS.EllipticEst.Q0 := by
  have h : Function.uncurry (fun z θ => C z θ * D z θ)
      = fun p : ℝ × ℝ => Function.uncurry C p * Function.uncurry D p := rfl
  rw [h]
  exact hC.mul hD

/-- The uncurried form of a square. -/
theorem continuousOn_uncurry_sq {C : ℝ → ℝ → ℝ}
    (hC : ContinuousOn (Function.uncurry C) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (Function.uncurry (fun z θ => C z θ ^ 2)) Work.FTS.EllipticEst.Q0 := by
  have h : Function.uncurry (fun z θ => C z θ ^ 2)
      = fun p : ℝ × ℝ => (Function.uncurry C p) ^ 2 := rfl
  rw [h]
  exact hC.pow 2

/-! ## The commutation `D_θ(D_z^bD_θ^a f) = D_z^bD_θ^{a+1} f` -/

/-- On the open quadrant, `D_θ` commutes with `D_z^b`:
`D_θ(D_z^bD_θ^af) = D_z^bD_θ^{a+1}f`. -/
theorem dth_mixed_eqOn_Q0 {f : ℝ → ℝ → ℝ} (hO : Work.FTS.EllipticEst.SmoothOpen f) (a b : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.mixed b a f)))
      (Function.uncurry (Work.Spaces.mixed b (a + 1) f)) Work.FTS.EllipticEst.Q0 := by
  intro p hp
  have hcomm := Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
      (V := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0
      (g := Work.Spaces.DthIter a f) (fun n => (hO.DthIter a).forall n) b 1
  exact hcomm hp

/-- The a.e. form of `dth_mixed_eqOn_Q0` for the product measure. -/
theorem dth_mixed_ae_eq {f : ℝ → ℝ → ℝ} (hO : Work.FTS.EllipticEst.SmoothOpen f) (a b : ℕ) :
    (fun p : ℝ × ℝ => Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2)
      =ᵐ[(volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)]
    (fun p : ℝ × ℝ => Work.Spaces.mixed b (a + 1) f p.1 p.2) := by
  filter_upwards [ae_prod_mem_Q0] with p hp
  exact dth_mixed_eqOn_Q0 (f := f) hO a b hp

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.T5bZeroTerm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

set_option maxHeartbeats 1600000

theorem T5bZeroTerm : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 7 f → Work.Spaces.VanishTheta f →
      (∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0) →
      Work.Construction.L12 f 0 = 0 →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * (Work.Construction.c2m θ * Work.Construction.L12 f z)
            * Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ|
        ≤ C * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨CL, hCLpos, hCL⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
  refine ⟨8 * CL, by positivity, ?_⟩
  intro α hα f a b ρ hsm hm6 hm7 hvt haxis hl12 hab hleaf
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hCL' : ∀ k ≤ 4, ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ CL * Work.Spaces.HkNorm α 4 f :=
    fun k hk z hz => hCL α f hα0 hα1 hsm hm6 hl12 k hk z hz
  have hψsm : ContDiffOn ℝ 1 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) :=
    l12ContDiffOnOpen α hα f hsm hm7
  rcases hleaf with hρ | hρ | ⟨ha1, hρ⟩
  · subst hρ
    have hcore := T5bZeroTerm_core (f := f) (CL := CL) hCLpos hCL' hψsm a b
      (σ := fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (hσcont := Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0 Work.Spaces.eta)
      (hσnn := fun θ hθ =>
        Real.rpow_nonneg (Work.FTS.StrongPersist.H6Pair6Aux.sin_two_nonneg_Iθ
          ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) _)
      (hσcap := by
        intro θ hθ
        by_cases ha0 : a = 0
        · rw [if_pos ha0]
        · rw [if_neg ha0]
          exact Work.FTS.H2.rpow_eta_le_gam hα0 ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
      hα0 hsm hm6 hm7 hab
    simpa only [Work.FTS.TransportS.leafEta] using hcore
  · subst hρ
    have hcore := T5bZeroTerm_core (f := f) (CL := CL) hCLpos hCL' hψsm a b
      (σ := fun _ => (1:ℝ)) (hσcont := continuousOn_const)
      (hσnn := fun θ _ => zero_le_one)
      (hσcap := by
        intro θ hθ
        refine Work.FTS.TransportS.one_le_rpow_neg ?_ hθ
        by_cases ha0 : a = 0
        · rw [if_pos ha0]; norm_num [Work.Spaces.eta]
        · rw [if_neg ha0, Work.Spaces.gam]; linarith)
      hα0 hsm hm6 hm7 hab
    simpa only [Work.FTS.TransportS.leafOne, mul_one] using hcore
  · subst hρ
    have hcore := T5bZeroTerm_core (f := f) (CL := CL) hCLpos hCL' hψsm a b
      (σ := fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (hσcont := Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0
        (Work.Spaces.gam α))
      (hσnn := fun θ hθ =>
        Real.rpow_nonneg (Work.FTS.StrongPersist.H6Pair6Aux.sin_two_nonneg_Iθ
          ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) _)
      (hσcap := by
        intro θ hθ
        rw [if_neg (by omega : ¬ a = 0)])
      hα0 hsm hm6 hm7 hab
    simpa only [Work.FTS.TransportS.leafGam] using hcore

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCaseHard =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The mismatch coefficient estimate: the case `a = a₁ = 1`, `b₁ = 0`

With these indices the pairing is `∫∫ w²σ^{-γ}·(D_θA)·(D_z^b f)·(D_z^bD_θ f)`, `b ≤ 5`.

* `b ≤ 4`: complete (`mh_hard_b_le_four` in `MismatchHardBLe4`), via `N6.PwAny6` +
  `mixed_slot_le` + `slotAmgm`.
* `b = 5`: complete (`mh_hard_b5` in `MismatchHardB5`), via the σ-divisibility identity
  `leafGam α·D_θA = w²σ^{1-γ}∂_θA`, the radial-uniform slice bound for the `(0,1)`-slot of `A`,
  the slice Agmon bound for `D_z⁵f` (`mh_agmon`), the slice Cauchy–Schwarz at the bounded
  weight `σ^{2-γ}` (`mh_slice_bound`) and the two `z`-marginals of `D_z⁵f`
  (`mh_pureZ_eta_slot_l2`, `T6Coef.zProdIntLe`).
-/
namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 1600000

theorem mismatchCaseHard : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (A f : ℝ → ℝ → ℝ) (K0 K4 : ℝ) (a b a₁ b₁ : ℕ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 4 A →
      Work.Spaces.HkMem α 6 A →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0) →
      Work.FTS.Nonlin.Xn α A ≤ K4 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 7 f →
      Work.Spaces.VanishTheta f →
      1 ≤ a₁ → a₁ + b₁ ≤ 2 → a₁ ≤ a → b₁ ≤ b → a + b ≤ 6 →
      a = a₁ → a₁ = 1 → b₁ = 0 →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed b₁ a₁ A p.1 p.2
          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
            * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
  obtain ⟨C, hCpos, hC⟩ := mh_hard_b_le_four
  obtain ⟨C', hC'pos, hC'⟩ := mh_hard_b5
  refine ⟨max C C', lt_max_of_lt_left hCpos, ?_⟩
  intro α hα A f K0 K4 a b a₁ b₁ hAsm hA4 hA6 hAbdd hXn hfsm hf7 hfv
    ha₁ hab₁ ha₁a hb₁b hab hae ha₁e hb₁e
  subst hae
  subst ha₁e
  subst hb₁e
  simp only [Nat.sub_zero, Nat.sub_self] at *
  have hf6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.OpenPkg.HkMem_mono_open (k := 7) hfsm 6 (by norm_num) hf7
  have hK0 : 0 ≤ K0 := by
    have h := hAbdd 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
    linarith [abs_nonneg (A 1 (Real.pi / 4))]
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hXn
  have hHf6 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  by_cases hb : b ≤ 4
  · have h := hC α hα A f K0 K4 b hAsm hA4 hAbdd hXn hfsm hf6 hb
    have hle : C * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))
        ≤ max C C' * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
      have h1 : C * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)))
          ≤ max C C' * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))) :=
        mul_le_mul_of_nonneg_right (le_max_left C C')
          (mul_nonneg (Real.rpow_nonneg hα.1.le (-(3 : ℝ)))
            (mul_nonneg (by linarith [hK0, hK4]) (by linarith [hHf6])))
      rw [mul_assoc C, mul_assoc (max C C')]
      exact h1
    exact ⟨by simpa only [Work.FTS.TransportS.leafGam, pm] using h.1,
      le_trans (by simpa only [Work.FTS.TransportS.leafGam, pm] using h.2) hle⟩
  · have hb5 : b = 5 := by omega
    subst hb5
    have h := hC' α hα A f K0 K4 hAsm hA4 hA6 hAbdd hXn hfsm hf6
    have hle : C' * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))
        ≤ max C C' * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
      have h1 : C' * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)))
          ≤ max C C' * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))) :=
        mul_le_mul_of_nonneg_right (le_max_right C C')
          (mul_nonneg (Real.rpow_nonneg hα.1.le (-(3 : ℝ)))
            (mul_nonneg (by linarith [hK0, hK4]) (by linarith [hHf6])))
      rw [mul_assoc C', mul_assoc (max C C')]
      exact h1
    exact ⟨by simpa only [Work.FTS.TransportS.leafGam, pm] using h.1,
      le_trans (by simpa only [Work.FTS.TransportS.leafGam, pm] using h.2) hle⟩
end

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
end
