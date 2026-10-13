import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongEps.HkSq_Jeps_le
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.leaf_pairIntegral_le_HkSq
import Submission.Work.FTS.StrongEps.JepsSmoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# Integrability of the leaf pairings against the mollifier `J_ε`

The three integrands of `integrable_pairing_Jeps` are, on the open quadrant,

* `w · J_ε(D_z^bD_θ^a u) · D_z^bD_θ^a v`,
* `w · (D_z^bD_θ^a u)²`,
* `w · (D_z^bD_θ^a v)²`

with `w` a leaf weight of the `IP4`-unfolding (`IsLeafW α a w`) and `(a,b)` a slot of order
`a + b ≤ 1`.  Each is dominated pointwise on the open quadrant by a sum of two
`ℋ¹`-integrands, which are integrable there:

* `w · (D_z^bD_θ^a f)² ≤ HkIntegrand α 1 f` for every `f` (`H6Pair6Aux.domLeaf_all`), so the
  second and third integrands are dominated by `HkIntegrand α 1 u` respectively
  `HkIntegrand α 1 v`;
* for the first one, `D_z^bD_θ^a (J_ε u) = J_ε (D_z^bD_θ^a u)` on the open quadrant
  (`mixed_Jeps`), and then AM–GM gives the bound `(HkIntegrand α 1 (J_ε u) + HkIntegrand α 1 v)/2`.

The only non-pointwise inputs are that those `ℋ¹`-integrands are integrable on the quadrant
(`integrable_HkIntegrand`, from `HkMem` and the continuity furnished by `SmoothOpen`) and that a
leaf weight is continuous there (`continuousOn_uncurry_leafW`, used exactly once, for the a.e.
strong measurability of the first integrand; for the other two the a.e. strong measurability is
read off from the pointwise domination).
-/

/-- **A leaf weight of the `IP4`-unfolding is continuous on the open quadrant.**  `IsLeafW`
pins the weight to one of the three explicit functions `w² sin(2θ)^{-η}`, `w²`,
`w² sin(2θ)^{-γ}`, all of which are continuous where `z > 0` and `sin(2θ) > 0`. -/
private theorem continuousOn_uncurry_leafW {α : ℝ} {a : ℕ} {w : ℝ → ℝ → ℝ}
    (h : Work.FTS.TransportS.IsLeafW α a w) :
    ContinuousOn (Function.uncurry w) Work.FTS.StrongEps.Quad := by
  have hsinpos : ∀ p ∈ Work.FTS.StrongEps.Quad, 0 < Real.sin (2 * p.2) := by
    intro p hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.StrongEps.Quad := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hfun]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsinpow : ∀ c : ℝ,
      ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Work.FTS.StrongEps.Quad :=
    fun c => ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      |>.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  rcases h with h | h | ⟨-, h⟩
  · rw [h]
    show ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 *
      (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) Work.FTS.StrongEps.Quad
    exact (hw.pow 2).mul (hsinpow _)
  · rw [h]
    show ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2) Work.FTS.StrongEps.Quad
    exact hw.pow 2
  · rw [h]
    show ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 *
      (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))) Work.FTS.StrongEps.Quad
    exact (hw.pow 2).mul (hsinpow _)

/-- The pointwise AM–GM estimate `|x| |y| ≤ (x² + y²)/2`. -/
private theorem abs_mul_le_half_sq (x y : ℝ) : |x| * |y| ≤ (x ^ 2 + y ^ 2) / 2 := by
  have h : 0 ≤ (|x| - |y|) ^ 2 := sq_nonneg _
  have h2 : (|x| - |y|) ^ 2 = |x| ^ 2 - 2 * |x| * |y| + |y| ^ 2 := by ring
  rw [h2] at h
  simp only [sq_abs] at h
  linarith

/-- **The `ℋ^k`-integrand is integrable on the open quadrant.**  `HkMem` supplies the angular
integrability at each `z` and the integrability of the outer integral; `SmoothOpen` supplies the
joint a.e. strong measurability (continuity on the open quadrant, the boundary being null); the
product-measure form is `Work.Spaces.integrable_prod_of_iterated`, and the restriction to the
open quadrant only lowers the measure (`Iz ×ˢ Iθ ⊇ Quad`). -/
private theorem integrable_HkIntegrand {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    MeasureTheory.Integrable (Function.uncurry (Work.Spaces.HkIntegrand α k f))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad) := by
  have hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2)
      Work.FTS.StrongEps.Quad :=
    Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad α k (fun n => hsm.forall n)
  have haesm : AEStronglyMeasurable (Function.uncurry (Work.Spaces.HkIntegrand α k f))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have hprod : MeasureTheory.Integrable (Function.uncurry (Work.Spaces.HkIntegrand α k f))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.integrable_prod_of_iterated
      (μ := volume.restrict Work.Spaces.Iz) (ν := volume.restrict Work.Spaces.Iθ)
      (G := fun z θ => Work.Spaces.HkIntegrand α k f z θ)
      (fun z θ => Work.Spaces.HkIntegrand_nonneg α k f z θ) haesm
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ici).mpr
        (Eventually.of_forall fun z hz => hmem.1 z hz))
      hmem.2).1
  refine hprod.mono_measure ?_
  rw [MeasureTheory.Measure.prod_restrict]
  exact MeasureTheory.Measure.restrict_mono
    (Set.prod_mono Set.Ioi_subset_Ici_self Set.Ioo_subset_Icc_self) le_rfl

theorem integrable_pairing_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∀ {α ε : ℝ} (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
      {w : ℝ → ℝ → ℝ} {a b : ℕ} (hleaf : Work.FTS.TransportS.IsLeafW α a w)
      (hab : a + b ≤ 1) {u v : ℝ → ℝ → ℝ}
      (hu : Work.FTS.VocabO.HQo α 1 u) (hv : Work.FTS.VocabO.HQo α 1 v),
      MeasureTheory.Integrable (Function.uncurry (fun z θ =>
          w z θ * Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a u) z θ
            * Work.Spaces.mixed b a v z θ))
          (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
      ∧ MeasureTheory.Integrable (Function.uncurry (fun z θ =>
          w z θ * (Work.Spaces.mixed b a u z θ) ^ 2))
          (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
      ∧ MeasureTheory.Integrable (Function.uncurry (fun z θ =>
          w z θ * (Work.Spaces.mixed b a v z θ) ^ 2))
          (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) := by
  intro α ε hα hε w a b hleaf hab u v hu hv
  obtain ⟨hsu, hmu⟩ := hu
  obtain ⟨hsv, hmv⟩ := hv
  have hαpos : 0 < α := hα.1
  have hεpos : 0 < ε := hε.1
  have hQuad : MeasurableSet Work.FTS.StrongEps.Quad := isOpen_Quad.measurableSet
  -- the leaf weight is continuous on the open quadrant
  have hcw : ContinuousOn (Function.uncurry w) Work.FTS.StrongEps.Quad :=
    continuousOn_uncurry_leafW hleaf
  -- the two plain slots
  have hua : ContinuousOn (Function.uncurry (Work.Spaces.mixed b a u))
      Work.FTS.StrongEps.Quad := (hsu.mixed b a).continuousOn
  have hva : ContinuousOn (Function.uncurry (Work.Spaces.mixed b a v))
      Work.FTS.StrongEps.Quad := (hsv.mixed b a).continuousOn
  have hIntu : MeasureTheory.Integrable (Function.uncurry (Work.Spaces.HkIntegrand α 1 u))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad) := integrable_HkIntegrand hsu hmu
  have hIntv : MeasureTheory.Integrable (Function.uncurry (Work.Spaces.HkIntegrand α 1 v))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad) := integrable_HkIntegrand hsv hmv
  -- the mollified datum `J_ε u`
  have hsmJu : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε u) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hεpos (fun n => hsu.forall n)
  have hmemJu : Work.Spaces.HkMem α 1 (Work.FTS.StrongEps.Jeps ρ ε u) :=
    Work.FTS.StrongEps.HkMem_Jeps (ρ := ρ) (k := 1) hρ.moll hα hεpos (fun n => hsu.forall n) hmu
  have hIntJu : MeasureTheory.Integrable
      (Function.uncurry (Work.Spaces.HkIntegrand α 1 (Work.FTS.StrongEps.Jeps ρ ε u)))
      (MeasureTheory.volume.restrict Work.FTS.StrongEps.Quad) :=
    integrable_HkIntegrand hsmJu hmemJu
  have hJa : ContinuousOn
      (Function.uncurry (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u)))
      Work.FTS.StrongEps.Quad := (hsmJu.mixed b a).continuousOn
  have hJcont : ContinuousOn
      (Function.uncurry (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a u)))
      Work.FTS.StrongEps.Quad :=
    (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hεpos (fun n => (hsu.mixed b a).forall n)).continuousOn
  refine ⟨?_, ?_, ?_⟩
  · -- the cross pairing `w · J_ε(D^b_a u) · D^b_a v`, dominated by the average of the two squares
    refine MeasureTheory.Integrable.mono'
      (g := fun p : ℝ × ℝ => (Work.Spaces.HkIntegrand α 1 (Work.FTS.StrongEps.Jeps ρ ε u)
        p.1 p.2 + Work.Spaces.HkIntegrand α 1 v p.1 p.2) / 2)
      ((hIntJu.add hIntv).div_const 2) ?_ ?_
    · exact ((hcw.mul hJcont).mul hva).aestronglyMeasurable hQuad
    · filter_upwards [MeasureTheory.ae_restrict_mem hQuad] with p hp
      simp only [Function.uncurry]
      have hw0 : 0 ≤ w p.1 p.2 :=
        Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hleaf p.1
          ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩
      have hJeq : Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a u) p.1 p.2
          = Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u) p.1 p.2 :=
        (Work.FTS.StrongEps.mixed_Jeps ρ hρ.moll hεpos (fun n => hsu.forall n) hp.1 hp.2 b a).symm
      have hAM : |Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u) p.1 p.2|
            * |Work.Spaces.mixed b a v p.1 p.2|
          ≤ (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u) p.1 p.2 ^ 2
            + Work.Spaces.mixed b a v p.1 p.2 ^ 2) / 2 :=
        abs_mul_le_half_sq _ _
      have hd1 : w p.1 p.2
            * Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u) p.1 p.2 ^ 2
          ≤ Work.Spaces.HkIntegrand α 1 (Work.FTS.StrongEps.Jeps ρ ε u) p.1 p.2 :=
        Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all (α := α) (a := a) (ρ := w)
          (f := Work.FTS.StrongEps.Jeps ρ ε u) (b' := b) (n := 1) hαpos hleaf hp.2 hab
      have hd2 : w p.1 p.2 * Work.Spaces.mixed b a v p.1 p.2 ^ 2
          ≤ Work.Spaces.HkIntegrand α 1 v p.1 p.2 :=
        Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all (α := α) (a := a) (ρ := w)
          (f := v) (b' := b) (n := 1) hαpos hleaf hp.2 hab
      rw [Real.norm_eq_abs, hJeq]
      calc |w p.1 p.2 * Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u) p.1 p.2
              * Work.Spaces.mixed b a v p.1 p.2|
          = w p.1 p.2 * (|Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u) p.1 p.2|
              * |Work.Spaces.mixed b a v p.1 p.2|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hw0]; ring
        _ ≤ w p.1 p.2 * ((Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u) p.1 p.2 ^ 2
              + Work.Spaces.mixed b a v p.1 p.2 ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left hAM hw0
        _ = (w p.1 p.2 * Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε u) p.1 p.2 ^ 2
              + w p.1 p.2 * Work.Spaces.mixed b a v p.1 p.2 ^ 2) / 2 := by ring
        _ ≤ (Work.Spaces.HkIntegrand α 1 (Work.FTS.StrongEps.Jeps ρ ε u) p.1 p.2
              + Work.Spaces.HkIntegrand α 1 v p.1 p.2) / 2 := by linarith
  · -- the `u`-square
    refine MeasureTheory.Integrable.mono' hIntu ?_ ?_
    · exact (hcw.mul (hua.pow 2)).aestronglyMeasurable hQuad
    · filter_upwards [MeasureTheory.ae_restrict_mem hQuad] with p hp
      simp only [Function.uncurry]
      have hw0 : 0 ≤ w p.1 p.2 :=
        Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hleaf p.1
          ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 (sq_nonneg _))]
      exact Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all (α := α) (a := a) (ρ := w)
        (f := u) (b' := b) (n := 1) hαpos hleaf hp.2 hab
  · -- the `v`-square
    refine MeasureTheory.Integrable.mono' hIntv ?_ ?_
    · exact (hcw.mul (hva.pow 2)).aestronglyMeasurable hQuad
    · filter_upwards [MeasureTheory.ae_restrict_mem hQuad] with p hp
      simp only [Function.uncurry]
      have hw0 : 0 ≤ w p.1 p.2 :=
        Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hleaf p.1
          ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 (sq_nonneg _))]
      exact Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all (α := α) (a := a) (ρ := w)
        (f := v) (b' := b) (n := 1) hαpos hleaf hp.2 hab

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer
