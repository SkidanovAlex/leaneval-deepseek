import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.dictIIDefs
import Submission.Work.BoseFixB1S.integrableOn_cont_mul_pairComp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dictIIAux.tendstoRhsClamp` — the dominated-convergence step of the `L¹`
block-`II` dictionary

`Work.BoseBoxFock.dictII_L1` removes the boundedness hypothesis from `blockII_dict` by clamping
the kernel (`clampK N k = max (−N) (min N k)`) and passing to the limit.  This module supplies the
limit of the **right-hand** side of the identity, i.e. of

    RHS(f) = ∫_{abox n ℓ} (PᵢPⱼΨ)(QⱼQᵢΨ)·f(xᵢ,xⱼ)  ,

for a pair `i = p.1 ≠ p.2 = j`:

    `Work.BoseBoxFock.dictIIAux.tendstoRhsClamp` :
    RHS(clampK N f) → RHS(k)   as `N → ∞`, for `f =ᵐ k` on `ℝ³ × ℝ³` and `k` integrable.

## Route

The integrand is `V x * g (x p.1, x p.2)` with `V = (PᵢPⱼΨ)·(QⱼQᵢΨ)`: `V` is **continuous**
(`aP_continuous`, `aQ_continuous`) so it is bounded on the compact box `abox n ℓ`, while the kernel
factor is handled by the a.e. machinery.

* `ae_pair_pullback_of_ae` / `aestronglyMeasurable_pair_pullback` — a.e. facts about the pair
  kernel transfer to its pullback `x ↦ w (x p.1) (x p.2)` along the coordinate pair.  This is
  `Submission.BoseGases.ae_eq_pair_pullback` (stated on the *cube product*) promoted to the stated
  hypothesis on the *whole* space via `ae_restrict_of_ae`.
* Since `f =ᵐ k`, also `clampK N f =ᵐ clampK N k`, so the two integrals coincide **for every `N`**
  (`integral_congr_ae`); it remains to pass to the limit in the `k`-integrand.
* `tendsto_integral_of_dominated_convergence` on `μ = volume.restrict (abox n ℓ)` with
  * pointwise convergence `clampK N k (xᵢ,xⱼ) → k (xᵢ,xⱼ)` (`clampK_tendsto`),
  * the dominator `x ↦ |V x| · |k (x p.1) (x p.2)|`, integrable by
    `Work.BoseFixB1S.integrableOn_cont_mul_pairComp` (continuous factor times a kernel integrable
    on the cube product),
  * a.e. strong measurability of the clamped pullback, from `aestronglyMeasurable_pair_pullback`
    applied to `AEMeasurable (uncurry (clampK N k))` (a continuous function of the a.e. measurable
    `uncurry k`).

Everything in this file is `sorry`-free.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Work.BoseBoxFock.dictIIAux

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Pullback of a.e. equality to the box.**  If two pair kernels agree a.e. for the product
Lebesgue measure on `ℝ³ × ℝ³`, then their pullbacks along the pair of coordinates `(i, j)`
(`i ≠ j`) agree a.e. for the box measure on `abox N ℓ`.  This is
`Submission.BoseGases.ae_eq_pair_pullback` with the a.e. hypothesis stated on the *whole* space
(instead of on the cube product). -/
lemma ae_pair_pullback_of_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {w w' : E3 → E3 → ℝ} (hw : Function.uncurry w =ᵐ[volume] Function.uncurry w') :
    (fun x : Submission.BoseGases.X N => w (x i) (x j))
      =ᵐ[volume.restrict (Submission.BoseGases.abox N ℓ)]
      (fun x : Submission.BoseGases.X N => w' (x i) (x j)) := by
  have h2 : Function.uncurry w
      =ᵐ[volume.restrict (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)]
      Function.uncurry w' := MeasureTheory.ae_restrict_of_ae hw
  simpa only [Function.uncurry] using Submission.BoseGases.ae_eq_pair_pullback hℓ hij h2

/-- **A.e. strong measurability of a pair pullback.**  If `w : ℝ³ × ℝ³ → ℝ` is a.e. measurable,
then the pullback `x ↦ w (x i, x j)` (`i ≠ j`) is a.e. strongly measurable for the box measure:
pull back a measurable representative of `w` with `ae_pair_pullback_of_ae`. -/
lemma aestronglyMeasurable_pair_pullback {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N}
    (hij : i ≠ j) {w : E3 × E3 → ℝ} (hw : AEMeasurable w volume) :
    AEStronglyMeasurable (fun x : Submission.BoseGases.X N => w (x i, x j))
      (volume.restrict (Submission.BoseGases.abox N ℓ)) := by
  obtain ⟨g, hgm, hgew⟩ := hw
  have hw2 : w
      =ᵐ[volume.restrict (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)] g :=
    MeasureTheory.ae_restrict_of_ae hgew
  have h1 := Submission.BoseGases.ae_eq_pair_pullback hℓ hij hw2
  have h2 : Measurable (fun x : Submission.BoseGases.X N => (x i, x j)) := by fun_prop
  exact (hgm.comp h2).aestronglyMeasurable.congr h1.symm

theorem tendstoRhsClamp {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨc : Continuous Ψ) {f k : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hkI : MeasureTheory.Integrable (Function.uncurry k) MeasureTheory.volume)
    (hfe : Function.uncurry f =ᵐ[MeasureTheory.volume] Function.uncurry k)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    Filter.Tendsto (fun N : ℕ => ∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Ψ) x
          * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Ψ) x
          * Work.BoseBoxFock.clampK N f (x p.1) (x p.2)) Filter.atTop
      (nhds (∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Ψ) x
          * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Ψ) x
          * k (x p.1) (x p.2))) := by
  classical
  -- the continuous weight
  set V : Submission.BoseGases.X n → ℝ := fun x =>
    Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Ψ) x
      * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Ψ) x
  have hVc : Continuous V := (Submission.BoseGases.aP_continuous hℓ p.1
      (Submission.BoseGases.aP_continuous hℓ p.2 hΨc)).mul
    (Submission.BoseGases.aQ_continuous hℓ p.2 (Submission.BoseGases.aQ_continuous hℓ p.1 hΨc))
  -- the pullback of `f =ᵐ k` to the box
  have hae' : (fun x : Submission.BoseGases.X n => f (x p.1) (x p.2))
      =ᵐ[volume.restrict (Submission.BoseGases.abox n ℓ)]
      (fun x : Submission.BoseGases.X n => k (x p.1) (x p.2)) := by
    simpa only [Function.uncurry] using ae_pair_pullback_of_ae hℓ hp hfe
  -- clamping preserves a.e. equality, so the integrals coincide for every `N`
  have hclamp_ae : ∀ N : ℕ,
      (fun x : Submission.BoseGases.X n => V x * Work.BoseBoxFock.clampK N f (x p.1) (x p.2))
        =ᵐ[volume.restrict (Submission.BoseGases.abox n ℓ)]
      (fun x : Submission.BoseGases.X n => V x * Work.BoseBoxFock.clampK N k (x p.1) (x p.2)) := by
    intro N
    filter_upwards [hae'] with x hx
    simp only [Work.BoseBoxFock.clampK, hx]
  -- the dominator is integrable on the box
  have hkabs : MeasureTheory.IntegrableOn (fun q : E3 × E3 => |k q.1 q.2|)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) volume :=
    (hkI.norm).integrableOn
  have hbnd : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => |V x| * |k (x p.1) (x p.2)|)
      (Submission.BoseGases.abox n ℓ) volume :=
    Work.BoseFixB1S.integrableOn_cont_mul_pairComp hℓ hp hVc.abs hkabs
  -- a.e. strong measurability of the clamped pullback
  have hAESM : ∀ N : ℕ, AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n => V x * Work.BoseBoxFock.clampK N k (x p.1) (x p.2))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) := by
    intro N
    have hclamp_aem : AEMeasurable (Function.uncurry (Work.BoseBoxFock.clampK N k)) volume := by
      have hφ : Measurable (fun t : ℝ => max (-(N : ℝ)) (min (N : ℝ) t)) := by fun_prop
      have heq : Function.uncurry (Work.BoseBoxFock.clampK N k)
          = (fun t : ℝ => max (-(N : ℝ)) (min (N : ℝ) t)) ∘ Function.uncurry k := by
        funext q
        rfl
      rw [heq]
      exact hφ.comp_aemeasurable hkI.aestronglyMeasurable.aemeasurable
    exact hVc.measurable.aestronglyMeasurable.mul
      (aestronglyMeasurable_pair_pullback hℓ hp hclamp_aem)
  -- the pointwise domination
  have hdom : ∀ N : ℕ, ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox n ℓ)),
      ‖V x * Work.BoseBoxFock.clampK N k (x p.1) (x p.2)‖ ≤ |V x| * |k (x p.1) (x p.2)| := by
    intro N
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (Work.BoseBoxFock.clampK_abs_le N k (x p.1) (x p.2))
      (abs_nonneg _)
  -- the pointwise convergence
  have hlim : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox n ℓ)),
      Filter.Tendsto (fun N : ℕ => V x * Work.BoseBoxFock.clampK N k (x p.1) (x p.2))
        Filter.atTop (nhds (V x * k (x p.1) (x p.2))) :=
    Eventually.of_forall fun x =>
      (Work.BoseBoxFock.clampK_tendsto k (x p.1) (x p.2)).const_mul (V x)
  -- dominated convergence for the `k`-integrand
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Submission.BoseGases.abox n ℓ))
    (F := fun N x => V x * Work.BoseBoxFock.clampK N k (x p.1) (x p.2))
    (f := fun x => V x * k (x p.1) (x p.2))
    (fun x => |V x| * |k (x p.1) (x p.2)|) hAESM hbnd hdom hlim
  -- replace `k` by `f` inside the clamp, for every `N`
  refine hDCT.congr' (Eventually.of_forall fun N => ?_)
  exact (MeasureTheory.integral_congr_ae (hclamp_ae N)).symm

end Work.BoseBoxFock.dictIIAux
