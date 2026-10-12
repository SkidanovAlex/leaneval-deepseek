import Mathlib
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The gradient norm is bounded by the sum of the directional `L²` norms

`Work.BoseSym.gradNorm N f` is the `L²` seminorm of the operator norm of the
Fréchet derivative `fderiv ℝ f`.  Since the configuration space
`Conf N = Fin N → EuclideanSpace ℝ (Fin 3)` is finite dimensional with the
coordinates `eDir N i k` as a basis whose coordinate functionals are bounded by
the norm, the operator norm of any continuous linear functional `T` on `Conf N`
is bounded by the sum of the absolute values of its values on the coordinate
directions:

  `‖T‖ ≤ ∑ j : GIdx N, ‖T (eDir N j.1 j.2)‖`.

Applying this pointwise to `T = fderiv ℝ f x` and using the triangle inequality
for the `ℒ²` seminorm (which needs the directional derivatives to be almost
everywhere strongly measurable — this holds because `fderiv` of an arbitrary
function is measurable, `measurable_fderiv_apply_const`) gives the stated
inequality.
-/

namespace Work.BoseSym.Rellich

open MeasureTheory
open scoped ENNReal

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **Coordinate expansion.**  Every point of configuration space is the sum of
its coordinate multiples of the directions `eDir N i k`. -/
lemma eq_sum_smul_eDir {N : ℕ} (v : Conf N) :
    v = ∑ j : GIdx N, (v j.1 j.2) • eDir N j.1 j.2 := by
  funext i
  nth_rewrite 1 [show v i = ∑ k : Fin 3, (v i k) • EuclideanSpace.single k 1 from
    (OrthonormalBasis.sum_repr (EuclideanSpace.basisFun (Fin 3) ℝ) (v i)).symm.trans ?_]
  · rw [Finset.sum_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.smul_apply, show (eDir N i k : Conf N) i = EuclideanSpace.single k 1 by
        simp [Work.BoseSym.eDir, Submission.BoseGases.kcDir, Submission.BoseGases.kcStdBasis]]
    · intro b _ hb
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Pi.smul_apply, show (eDir N b k : Conf N) i = 0 by
        simp [Work.BoseSym.eDir, Submission.BoseGases.kcDir, Submission.BoseGases.kcStdBasis,
          Ne.symm hb], smul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]

/-- **Operator norm bound.**  The norm of a continuous linear functional on
configuration space is at most the sum of the absolute values of its values on
the coordinate directions `eDir N i k`. -/
lemma opNorm_le_sum_dir {N : ℕ} (T : Conf N →L[ℝ] ℝ) :
    ‖T‖ ≤ ∑ j : GIdx N, ‖T (eDir N j.1 j.2)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun j _ => norm_nonneg _) fun v => ?_
  have hvv : T v = ∑ j : GIdx N, (v j.1 j.2) * T (eDir N j.1 j.2) := by
    conv_lhs => rw [eq_sum_smul_eDir v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
    rfl
  rw [hvv]
  calc ‖∑ j : GIdx N, (v j.1 j.2) * T (eDir N j.1 j.2)‖
      ≤ ∑ j : GIdx N, ‖(v j.1 j.2) * T (eDir N j.1 j.2)‖ := norm_sum_le _ _
    _ = ∑ j : GIdx N, ‖v j.1 j.2‖ * ‖T (eDir N j.1 j.2)‖ := by simp [norm_mul]
    _ ≤ ∑ j : GIdx N, ‖v‖ * ‖T (eDir N j.1 j.2)‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 : ‖v j.1 j.2‖ ≤ ‖v‖ :=
          le_trans (PiLp.norm_apply_le (v j.1) j.2) (norm_le_pi_norm v j.1)
        gcongr
    _ = (∑ j : GIdx N, ‖T (eDir N j.1 j.2)‖) * ‖v‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- **Triangle inequality** for the `ℒᵖ` seminorm of a pointwise sum over a
`Fintype` index type, in the form in which the sum is taken inside the function.
Only the almost everywhere strong measurability of the summands is required. -/
lemma eLpNorm_sum_univ_le {ι α ε : Type*} [Fintype ι] [MeasurableSpace α]
    [TopologicalSpace ε] [ESeminormedAddCommMonoid ε] [ContinuousAdd ε]
    {p : ℝ≥0∞} {μ : Measure α} (F : ι → α → ε)
    (hF : ∀ i, AEStronglyMeasurable (F i) μ) (hp : 1 ≤ p) :
    eLpNorm (fun x => ∑ i, F i x) p μ ≤ ∑ i, eLpNorm (F i) p μ := by
  have hfun : (∑ i, F i) = fun x => ∑ i, F i x := by
    funext x
    rw [Finset.sum_apply]
  rw [← hfun]
  exact eLpNorm_sum_le (s := Finset.univ) hp

theorem gradNorm_le_sum_dir {N : ℕ} (f : Work.BoseSym.Conf N → ℝ) :
    Work.BoseSym.gradNorm N f ≤ ∑ j : Work.BoseSym.GIdx N,
      MeasureTheory.eLpNorm (fun x => fderiv ℝ f x (Work.BoseSym.eDir N j.1 j.2)) 2
        (Work.BoseSym.volC N) := by
  -- the directional derivatives are almost everywhere strongly measurable,
  -- because `fderiv` of an arbitrary function is measurable
  have hmeas : ∀ j : GIdx N, AEStronglyMeasurable
      (fun x => fderiv ℝ f x (eDir N j.1 j.2)) (volC N) :=
    fun j => (measurable_fderiv_apply_const ℝ f (eDir N j.1 j.2)).aestronglyMeasurable
  -- the pointwise bound on the operator norm of the derivative
  have hpt : ∀ x, ‖(fun x => ‖fderiv ℝ f x‖) x‖ ≤
      ‖(fun x => ∑ j : GIdx N, ‖fderiv ℝ f x (eDir N j.1 j.2)‖) x‖ := by
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)]
    exact opNorm_le_sum_dir (fderiv ℝ f x)
  calc gradNorm N f
      = eLpNorm (fun x => ‖fderiv ℝ f x‖) 2 (volC N) := rfl
    _ ≤ eLpNorm (fun x => ∑ j : GIdx N, ‖fderiv ℝ f x (eDir N j.1 j.2)‖) 2 (volC N) :=
        eLpNorm_mono (measurable_fderiv ℝ f).norm.aestronglyMeasurable hpt
    _ ≤ ∑ j : GIdx N, eLpNorm (fun x => ‖fderiv ℝ f x (eDir N j.1 j.2)‖) 2 (volC N) :=
        eLpNorm_sum_univ_le _ (fun j => (hmeas j).norm) (by norm_num)
    _ = ∑ j : GIdx N, eLpNorm (fun x => fderiv ℝ f x (eDir N j.1 j.2)) 2 (volC N) :=
        Finset.sum_congr rfl fun j _ => eLpNorm_norm _ (hmeas j)

end

end Work.BoseSym.Rellich
