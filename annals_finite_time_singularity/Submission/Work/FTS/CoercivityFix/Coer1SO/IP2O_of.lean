/-
# `Coer1SO/IP2O_of` — the integrability fragment `IP2O` in the open class

This file proves `Work.FTS.CoercivityFix.Coer1SO.IP2O α f` from the two hypotheses of the
open-quadrant class `RegQo`:

* `Work.FTS.EllipticEst.SmoothOpen f` — `f` is `C^∞` on the *open* quadrant `(0,∞) × (0,π/2)`;
* `Work.Spaces.HkMem α 2 f` — `f ∈ ℋ²` (all the weighted derivatives of order `≤ 2` occurring
  in `HkIntegrand` have honest iterated integrals).

It is the verbatim open-class analogue of `Work.FTS.CoercivityFix.Coer1.IntPkg_Q`, which proves
the (larger) interior-class bundle `IntPkg α f` from `RegQ α 2 f` (i.e. from the *analytic*
`SmoothQuad`).  Every field of `IP2O` is one of the fields of `IntPkg`, so the arguments are
identical; the only difference is the source of the continuity of the blocks: `SmoothQuad`
gives a `C^∞` function on a neighbourhood of the closed quadrant `(-1,∞) × (-1,π/2+1)`, while
`SmoothOpen` only gives `C^∞` on `(0,∞) × (0,π/2)`, which is however exactly the set on which
the a.e. strong measurability of the blocks is needed (the `aesm_of_continuousOn_Qd` of
`Work.Spaces` is stated with the *open* quadrant).

The three sources of integrability are the same as in `IntPkg_Q`:

* the summands of `HkIntegrand α 2 f`, whose slices are integrable by `HkMem`
  (`Work.Spaces.sq_le_HkIntegrand_z` / `_mixed`), producing the weighted squares
  (`sq_DzEta_O`, `sq_MixedGam_O`) and then, by domination with the monotonicity of the angular
  weight, the plain ones (`sq_DzOne_O`, `sq_MixedOne_O`);
* `2|ab| ≤ a² + b²` (`integrableOn_mul_of_sq_Q`) for the `𝓛`-pairings (`intL_of_O`);
* Clairaut (`Work.Spaces.Dz_Dth_comm`) for the a.e. commutation.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Coer1SO.Defs
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1SO

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Continuity of the weighted blocks on the open quadrant -/

/-- `SmoothOpen` gives `C²` at every point of the open quadrant. -/
theorem contDiffAt_two_O {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
  (hs.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))

/-- The full angular weight `Wt α = w·sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
theorem continuousOn_Wt_O (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
    have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hfun2]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  refine hw.mul ?_
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-- The square of a weighted `D_z`-summand is continuous on the open quadrant. -/
theorem continuousOn_block_z_O {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.DzIter i f p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.FTS.EllipticEst.Q0 :=
  (((hs.DzIter i).continuousOn).mul Work.FTS.EllipticEst.continuousOn_wdivsin_Q0).pow 2

/-- The square of a weighted mixed summand is continuous on the open quadrant. -/
theorem continuousOn_block_m_O {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) (α : ℝ)
    (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0 :=
  (((hs.mixed j i).continuousOn.mul (continuousOn_Wt_O α))).pow 2

/-! ## The weighted squares -/

/-- The squared `D_z`-blocks with the `η`-weight. -/
theorem sq_DzEta_O (α : ℝ) {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f)
    (hm : Work.Spaces.HkMem α 2 f) (i : ℕ) (hi : i ≤ 2) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ =>
        (Work.Spaces.DzIter i f z θ) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have h := Work.FTS.CoercivityFix.Coer1.joint_of_le_HkIntegrand α 2 hm
    (continuousOn_block_z_O hs i)
    (fun z _ θ _ => Work.Spaces.sq_le_HkIntegrand_z α 2 f z θ i hi)
  refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair] at hp ⊢
  rw [mul_pow, Work.FTS.CoercivityFix.Coer1.sig_div_sq_Iθ Work.Spaces.eta
    (by rw [Work.Spaces.eta]; norm_num) z θ hp.2]
  rfl

/-- The squared mixed blocks with the `γ`-weight. -/
theorem sq_MixedGam_O (α : ℝ) (hα : 0 < α) {f : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 2 f)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 2) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have h := Work.FTS.CoercivityFix.Coer1.joint_of_le_HkIntegrand α 2 hm
    (continuousOn_block_m_O hs α j i)
    (fun z _ θ _ => Work.Spaces.sq_le_HkIntegrand_mixed α 2 f z θ i j hi hij)
  refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair] at hp ⊢
  rw [mul_pow, Work.FTS.CoercivityFix.Coer1.Wt_sq_self_Iθ α z θ hα hp.2]
  rfl

/-- The squared `D_z`-blocks with the plain radial weight. -/
theorem sq_DzOne_O (α : ℝ) {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f)
    (hm : Work.Spaces.HkMem α 2 f) (i : ℕ) (hi : i ≤ 2) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have h := sq_DzEta_O α hs hm i hi
  refine Work.FTS.CoercivityFix.Coer1.integrableOn_of_le_Q
    ((hs.DzIter i).continuousOn.pow 2 |>.mul Work.FTS.CoercivityFix.Coer1.continuousOn_w2)
    h ?_
  refine (Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem measurableSet_Ioo
    Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo).mono (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (Work.FTS.CoercivityFix.Coer1.w2_le_Rho_eta z θ hp)
    (sq_nonneg (Work.Spaces.DzIter i f z θ))

/-- The squared mixed blocks with the plain radial weight. -/
theorem sq_MixedOne_O (α : ℝ) (hα : 0 < α) {f : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 2 f)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 2) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have h := sq_MixedGam_O α hα hs hm i j hi hij
  refine Work.FTS.CoercivityFix.Coer1.integrableOn_of_le_Q
    ((hs.mixed j i).continuousOn.pow 2 |>.mul Work.FTS.CoercivityFix.Coer1.continuousOn_w2)
    h ?_
  refine (Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem measurableSet_Ioo
    Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo).mono (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (Work.FTS.CoercivityFix.Coer1.w2_le_Rho_gam α hα z θ hp)
    (sq_nonneg (Work.Spaces.mixed j i f z θ))

/-! ## The `𝓛`-pairings -/

/-- The `𝓛`-pairing `𝓛u·u·ρ` is integrable as soon as `u²ρ` and `(D_zu)²ρ` are.  The open-class
version of `Work.FTS.CoercivityFix.Coer1.intL_of`. -/
theorem intL_of_O {u : Fn} {ρ : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hρc : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hρnn : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ)
    (hsq : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => u z θ ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hdz : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dz u z θ) ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hcross : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_mul_of_sq_Q
      (((hu.mixed 1 0).continuousOn.mul hu.continuousOn).mul hρc) hρnn hdz hsq
  have h1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ ^ 2 * ρ z θ + Work.Spaces.Dz u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_add_Q hsq hcross
  have h3 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (u z θ ^ 2 * ρ z θ) / (1 + z))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_div_one_add_Q hsq
  have h4 := h3.const_mul (-2)
  have h5 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (u z θ ^ 2 * ρ z θ + Work.Spaces.Dz u z θ * u z θ * ρ z θ)
        + (-2) * ((u z θ ^ 2 * ρ z θ) / (1 + z)))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_add_Q h1 h4
  refine h5.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Work.Coercivity.L]
  ring

/-! ## The a.e. commutation of `D_z` and `D_θ` -/

/-- `D_z` and `D_θ` commute a.e. on the quadrant, for `SmoothOpen f` (Clairaut at every interior
point). -/
theorem ae_DzDth_comm_O {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Dz (Work.Spaces.Dth f) z θ = Work.Spaces.Dth (Work.Spaces.Dz f) z θ := by
  have hzpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_ae_restrict]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  filter_upwards [hzpos] with z hz
  filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
  exact Work.Spaces.Dz_Dth_comm (contDiffAt_two_O hs hz hθ)

/-! ## The bundle -/

theorem IP2O_of (α : ℝ) (hα : 0 < α) {f : Work.FTS.Galerkin.Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 2 f) :
    Work.FTS.CoercivityFix.Coer1SO.IP2O α f := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `sqDzEta_one`
    exact sq_DzEta_O α hs hm 1 (by norm_num)
  · -- `sqDzEta_zero`
    exact sq_DzEta_O α hs hm 0 (by norm_num)
  · -- `sqDzOne_zero`
    exact sq_DzOne_O α hs hm 0 (by norm_num)
  · -- `sqDzOne_one`
    exact sq_DzOne_O α hs hm 1 (by norm_num)
  · -- `sqDthOne`
    exact sq_MixedOne_O α hα hs hm 1 0 (by norm_num) (by norm_num)
  · -- `sqDthGam`
    exact sq_MixedGam_O α hα hs hm 1 0 (by norm_num) (by norm_num)
  · -- `intL_f_eta`
    exact intL_of_O hs (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho Work.Spaces.eta)
      (Work.FTS.CoercivityFix.Coer1.Rho_nonneg Work.Spaces.eta)
      (sq_DzEta_O α hs hm 0 (by norm_num)) (sq_DzEta_O α hs hm 1 (by norm_num))
  · -- `intL_Dz_eta`
    exact intL_of_O hs.Dz (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho Work.Spaces.eta)
      (Work.FTS.CoercivityFix.Coer1.Rho_nonneg Work.Spaces.eta)
      (sq_DzEta_O α hs hm 1 (by norm_num)) (sq_DzEta_O α hs hm 2 (by norm_num))
  · -- `intL_f_one`
    exact intL_of_O hs Work.FTS.CoercivityFix.Coer1.continuousOn_w2
      Work.FTS.CoercivityFix.Coer1.w2_nonneg
      (sq_DzOne_O α hs hm 0 (by norm_num)) (sq_DzOne_O α hs hm 1 (by norm_num))
  · -- `intL_Dz_one`
    exact intL_of_O hs.Dz Work.FTS.CoercivityFix.Coer1.continuousOn_w2
      Work.FTS.CoercivityFix.Coer1.w2_nonneg
      (sq_DzOne_O α hs hm 1 (by norm_num)) (sq_DzOne_O α hs hm 2 (by norm_num))
  · -- `intL_Dth_one`
    exact intL_of_O hs.Dth Work.FTS.CoercivityFix.Coer1.continuousOn_w2
      Work.FTS.CoercivityFix.Coer1.w2_nonneg
      (sq_MixedOne_O α hα hs hm 1 0 (by norm_num) (by norm_num))
      (sq_MixedOne_O α hα hs hm 1 1 (by norm_num) (by norm_num))
  · -- `intL_Dth_gam`
    exact intL_of_O hs.Dth (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho
        (Work.Spaces.gam α))
      (Work.FTS.CoercivityFix.Coer1.Rho_nonneg (Work.Spaces.gam α))
      (sq_MixedGam_O α hα hs hm 1 0 (by norm_num) (by norm_num))
      (sq_MixedGam_O α hα hs hm 1 1 (by norm_num) (by norm_num))
  · -- `dzDthComm`
    exact ae_DzDth_comm_O hs

end Work.FTS.CoercivityFix.Coer1SO
