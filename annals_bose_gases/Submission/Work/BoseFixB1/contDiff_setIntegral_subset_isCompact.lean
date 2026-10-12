import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Smoothness of a parametric integral over a measurable subset of a compact set

If `F : P → ℝ³ → ℝ` is jointly `C^n` and `A ⊆ K` with `K` compact and `A` measurable, then
`p ↦ ∫ x in A, F p x` is `C^n`.

The proof avoids any induction on `n` (which would run into the problem that the derivative of the
family is again a parametric integral but with a different codomain). Instead we exhibit the
integral as a convolution: choose a smooth bump function `b` with compact support which is `1` on
`K`; then, with `f = 1_A` and `g p y = F p (-y) b (-y)` (a family which is smooth in `(p,y)` and
uniformly compactly supported in `y`), one has

`(f ⋆ g p) 0 = ∫ t, (f t) * (F p t * b t) = ∫ x in A, F p x`,

and Mathlib's `contDiffOn_convolution_right_with_param` gives the smoothness in `p`.
-/

namespace Work.BoseFixB1

open MeasureTheory Set Function

theorem contDiff_setIntegral_subset_isCompact {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {A K : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A) (hK : IsCompact K)
    (hAK : A ⊆ K) {F : P → EuclideanSpace ℝ (Fin 3) → ℝ} {n : ℕ∞}
    (hF : ContDiff ℝ n (Function.uncurry F)) :
    ContDiff ℝ n (fun p => ∫ x in A, F p x) := by
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin 3))
  let r : ℝ := |R| + 1
  have hr : 0 < r := by positivity
  have hKr : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) r :=
    hKR.trans (Metric.closedBall_subset_closedBall
      (show R ≤ r by simp only [r]; linarith [le_abs_self R]))
  -- a smooth bump function, equal to `1` on `K`, with compact support
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin 3)) := ⟨r, r + 1, hr, by linarith⟩
  have hb_one : ∀ x ∈ K, b x = 1 := fun x hx =>
    b.one_of_mem_closedBall (Metric.closedBall_subset_closedBall (by linarith) (hKr hx))
  have hbc : HasCompactSupport (b : EuclideanSpace ℝ (Fin 3) → ℝ) := b.hasCompactSupport
  have hk : IsCompact (-tsupport (b : EuclideanSpace ℝ (Fin 3) → ℝ)) := hbc.isCompact.neg
  -- the parametric family, supported in `-tsupport b` uniformly in `p`
  let g : P → EuclideanSpace ℝ (Fin 3) → ℝ := fun p y => F p (-y) * b (-y)
  have hg_smooth : ContDiff ℝ n (Function.uncurry g) := by
    have h1 : ContDiff ℝ n (fun q : P × EuclideanSpace ℝ (Fin 3) => F q.1 (-q.2)) :=
      hF.comp (contDiff_fst.prodMk contDiff_snd.neg)
    have h2 : ContDiff ℝ n (fun q : P × EuclideanSpace ℝ (Fin 3) => b (-q.2)) :=
      (b.contDiff : ContDiff ℝ n (b : EuclideanSpace ℝ (Fin 3) → ℝ)).comp contDiff_snd.neg
    have hg_eq : Function.uncurry g
        = fun q : P × EuclideanSpace ℝ (Fin 3) => F q.1 (-q.2) * b (-q.2) := by
      funext q
      simp [g, Function.uncurry_def]
    rw [hg_eq]
    exact h1.mul h2
  -- the locally integrable factor `1_A`
  let f : EuclideanSpace ℝ (Fin 3) → ℝ := A.indicator (fun _ => (1:ℝ))
  have hf : LocallyIntegrable f := (locallyIntegrable_const (1:ℝ)).indicator hA
  have hgs : ∀ p x, p ∈ (univ : Set P) →
      x ∉ -tsupport (b : EuclideanSpace ℝ (Fin 3) → ℝ) → g p x = 0 := by
    intro p x _ hx
    have hxt : -x ∉ tsupport (b : EuclideanSpace ℝ (Fin 3) → ℝ) := fun h => hx (Set.mem_neg.mpr h)
    have hbs : b (-x) = 0 := (Function.notMem_support).mp fun h => hxt (subset_tsupport _ h)
    simp [g, hbs]
  have hmain : ContDiffOn ℝ n
      (fun q : P × EuclideanSpace ℝ (Fin 3) =>
        (convolution f (g q.1) (ContinuousLinearMap.mul ℝ ℝ) volume) q.2) (univ ×ˢ univ) :=
    contDiffOn_convolution_right_with_param (ContinuousLinearMap.mul ℝ ℝ) isOpen_univ hk hgs hf
      (by rw [Set.univ_prod_univ]; exact (contDiffOn_univ).mpr hg_smooth)
  have hstep : ContDiff ℝ n
      (fun p : P => (convolution f (g p) (ContinuousLinearMap.mul ℝ ℝ) volume) 0) := by
    have hfull : ContDiff ℝ n (fun q : P × EuclideanSpace ℝ (Fin 3) =>
        (convolution f (g q.1) (ContinuousLinearMap.mul ℝ ℝ) volume) q.2) := by
      rw [← contDiffOn_univ, ← Set.univ_prod_univ]
      exact hmain
    exact hfull.comp (contDiff_id.prodMk contDiff_const)
  refine (contDiffOn_univ).mp (hstep.contDiffOn.congr (fun p _ => ?_))
  -- identify the convolution with the wanted integral
  have hpt : (fun t : EuclideanSpace ℝ (Fin 3) =>
      (ContinuousLinearMap.mul ℝ ℝ) (f t) (g p (0 - t)))
      = fun t => A.indicator (fun t => F p t * b t) t := by
    funext t
    by_cases ht : t ∈ A <;> simp [f, g, ht]
  rw [MeasureTheory.convolution_def, hpt, MeasureTheory.integral_indicator hA]
  refine MeasureTheory.setIntegral_congr_fun hA (fun x hx => ?_)
  rw [hb_one x (hAK hx), mul_one]

end Work.BoseFixB1
