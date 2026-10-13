/-
Copyright: work module for the Elgindi finite-time singularity project.

# `IntPkgSq_O` — the five squared-block integrability certificates in the **open** class

The integrability bundle `Work.FTS.CoercivityFix.Coer1.IntPkg` carries five fields that are pure
`IntegrableOn` certificates for the squared weighted blocks

* `(D_z^i f)²·ρ_η`, `i ≤ 2`;
* `(D_z^jD_θ^i f)²·ρ_η`, `1 ≤ i`, `i + j ≤ 2`;
* `(D_z^jD_θ^i f)²·ρ_γ`, `1 ≤ i`, `i + j ≤ 2`;
* `(D_z^i f)²·w²`, `i ≤ 2`;
* `(D_z^jD_θ^i f)²·w²`, `1 ≤ i`, `i + j ≤ 2`;

where `ρ_β = w²·sin(2θ)^{-β}`.  The frozen `SmoothQuad`-class proofs live in
`Work.FTS.CoercivityFix.Coer1.IntFacts` (`sq_DzEta`, `sq_MixedEta`, `sq_MixedGam`, `sq_DzOne`,
`sq_MixedOne`).  The route, however, reaches its data only in the *open* class `SmoothOpen`
(`C^∞` on `(0,∞) × (0,π/2)`), which is what this file handles: the five fields are re-proved
verbatim with `SmoothQuad` replaced by `SmoothOpen`, so that the open-class bundle `IntPkgO`
can be assembled.

The mechanism is unchanged and rests on three ingredients:

* the dominated summand of `HkIntegrand α 2 f` (`Work.Spaces.sq_le_HkIntegrand_z` resp.
  `Work.Spaces.sq_le_HkIntegrand_mixed`) gives the `IntegrableOn` of the *weighted* summands
  via `Work.FTS.CoercivityFix.Coer1.joint_of_le_HkIntegrand`, whose side condition is
  continuity of the uncurried square on the open quadrant — supplied here by
  `Work.FTS.EllipticEst.SmoothOpen.continuousOn_summand` resp. by the local
  `continuousOn_mixed_Wt_O`;
* the algebraic identifications `sig_div_sq_Iθ` and `Wt_sq_self_Iθ` turn the weighted summands
  into the required `(·)²·ρ_β`;
* the monotonicity of the angular weight (`Rho_eta_le_Rho_gam`, `w2_le_Rho_eta`,
  `w2_le_Rho_gam`) and `Work.FTS.CoercivityFix.Coer1.integrableOn_of_le_Q` give the `η`- and
  plain-`w²` versions from the `γ`-weighted one.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Continuity of the weighted blocks on the open quadrant -/

/-- The `ℋ^k`-weight `Wt α z θ = w z · sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
theorem continuousOn_Wt_Q0O (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
    have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun2]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  exact hw.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp))))

/-- The uncurried weighted `D_z`-summand of the `ℋ^k`-integrand has a continuous square on the
open quadrant, for a datum of class `SmoothOpen`. -/
theorem continuousOn_Dz_sq_O {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter i f p.1 p.2
      * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
  (hs.continuousOn_summand i).pow 2

/-- The uncurried mixed `ℋ^k`-summand has a continuous square on the open quadrant, for a datum
of class `SmoothOpen`. -/
theorem continuousOn_mixed_Wt_O (α : ℝ) {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f)
    (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
  (((hs.mixed j i).continuousOn).mul (continuousOn_Wt_Q0O α)).pow 2

/-- The uncurried `D_z`-iterate is continuous on the open quadrant. -/
theorem continuousOn_DzIter_O {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i f p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
  (hs.DzIter i).continuousOn

/-- The uncurried mixed derivative is continuous on the open quadrant. -/
theorem continuousOn_mixed_O {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
  (hs.mixed j i).continuousOn

/-! ## The five squared-block certificates -/

theorem IntPkgSq_O (α : ℝ) (hα : 0 < α) {f : Work.FTS.Galerkin.Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 2 f) :
    (∀ i : ℕ, i ≤ 2 → MeasureTheory.IntegrableOn
       (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
       (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    ∧ (∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
       (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
       (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    ∧ (∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
       (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
       (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    ∧ (∀ i : ℕ, i ≤ 2 → MeasureTheory.IntegrableOn
       (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
       (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    ∧ (∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
       (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
       (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
  -- ## the `D_z`-blocks with the `η`-weight
  have hsqDzEta : ∀ i : ℕ, i ≤ 2 → MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    intro i hi
    have h := Work.FTS.CoercivityFix.Coer1.joint_of_le_HkIntegrand α 2 hm
      (continuousOn_Dz_sq_O hs i)
      (fun z _ θ _ => Work.Spaces.sq_le_HkIntegrand_z α 2 f z θ i hi)
    refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair] at hp ⊢
    rw [mul_pow, Work.FTS.CoercivityFix.Coer1.sig_div_sq_Iθ Work.Spaces.eta
      (by rw [Work.Spaces.eta]; norm_num) z θ hp.2]
    rfl
  -- ## the mixed blocks with the `γ`-weight
  have hsqMixedGam : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    intro i j hi hij
    have h := Work.FTS.CoercivityFix.Coer1.joint_of_le_HkIntegrand α 2 hm
      (continuousOn_mixed_Wt_O α hs j i)
      (fun z _ θ _ => Work.Spaces.sq_le_HkIntegrand_mixed α 2 f z θ i j hi hij)
    refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair] at hp ⊢
    rw [mul_pow, Work.FTS.CoercivityFix.Coer1.Wt_sq_self_Iθ α z θ hα hp.2]
    rfl
  -- ## the mixed blocks with the `η`-weight (dominated by the `γ`-weighted ones)
  have hsqMixedEta : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    intro i j hi hij
    have h := hsqMixedGam i j hi hij
    refine Work.FTS.CoercivityFix.Coer1.integrableOn_of_le_Q
      (((continuousOn_mixed_O hs j i).pow 2).mul
        (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho _)) h ?_
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem measurableSet_Icc
      (MeasureTheory.ae_restrict_mem measurableSet_Icc)] with p hp
    rcases p with ⟨z, θ⟩
    rw [abs_mul, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (Work.FTS.CoercivityFix.Coer1.Rho_nonneg _ z θ hp)]
    exact mul_le_mul_of_nonneg_left
      (Work.FTS.CoercivityFix.Coer1.Rho_eta_le_Rho_gam α hα z θ hp)
      (sq_nonneg (Work.Spaces.mixed j i f z θ))
  refine ⟨hsqDzEta, hsqMixedEta, hsqMixedGam, ?_, ?_⟩
  · -- ## the `D_z`-blocks with the plain radial weight
    intro i hi
    refine Work.FTS.CoercivityFix.Coer1.integrableOn_of_le_Q
      (((continuousOn_DzIter_O hs i).pow 2).mul
        Work.FTS.CoercivityFix.Coer1.continuousOn_w2) (hsqDzEta i hi) ?_
    refine (Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo).mono (fun p hp => ?_)
    rcases p with ⟨z, θ⟩
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (Work.FTS.CoercivityFix.Coer1.w2_le_Rho_eta z θ hp)
      (sq_nonneg (Work.Spaces.DzIter i f z θ))
  · -- ## the mixed blocks with the plain radial weight
    intro i j hi hij
    refine Work.FTS.CoercivityFix.Coer1.integrableOn_of_le_Q
      (((continuousOn_mixed_O hs j i).pow 2).mul
        Work.FTS.CoercivityFix.Coer1.continuousOn_w2) (hsqMixedGam i j hi hij) ?_
    refine (Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo).mono (fun p hp => ?_)
    rcases p with ⟨z, θ⟩
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (Work.FTS.CoercivityFix.Coer1.w2_le_Rho_gam α hα z θ hp)
      (sq_nonneg (Work.Spaces.mixed j i f z θ))

end Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux
