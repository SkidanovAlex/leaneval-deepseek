import Mathlib
import Submission.Work.NN.Newton.DefectDefs

/-!
# The linearised almost-complex relation

Let `J = JstdCn n + A` be a (pointwise) almost complex structure on `ℂⁿ`: it satisfies
`J z ∘ J z = -1` for every `z` in the polydisc `P_r`.  If `A` is `C¹` there, then
differentiating the identity `z ↦ (J z ∘ J z) v = -v` shows that the derivative
`DA_z X` of the perturbation anticommutes with `J z`:

`(DA_z X) (J z Y) = - (J z ((DA_z X) Y))`.

This is the linearised form of the relation `A_z J_z + J_z A_z + A_z² = 0` obtained by
expanding `(JstdCn n + A_z)² = -1`:  the derivative of that identity in the direction `X`
is precisely the statement below (the terms `(DA_z X) A_z` and `A_z (DA_z X)` cancel the
quadratic `J z`-factors on the two sides).

## Formalisation

The whole content is the chain rule for the map `w ↦ (J + A w)((J + A w) Y)`, which is
constant (equal to `-Y`) on the polydisc.  We prove this chain rule as the auxiliary
statement `hasFDerivAt_clm_apply_self` (derivative of the "operator square"
`T ↦ T (T v)`) and combine it with the composition `w ↦ J + A w`.
-/

namespace Work.NN.Newton.Defect

open scoped ContDiff
open scoped Topology
open Set Filter

/-- Derivative of the "operator-square" map `T ↦ T (T v)` on the space of continuous linear
endomorphisms of a real normed space: it is `dT ↦ dT (T v) + T (dT v)`. -/
private lemma hasFDerivAt_clm_apply_self {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : V) (T : V →L[ℝ] V) :
    HasFDerivAt (fun S : V →L[ℝ] V => S (S v))
      (ContinuousLinearMap.apply ℝ V (T v) + T.comp (ContinuousLinearMap.apply ℝ V v)) T := by
  have hf : HasFDerivAt (fun S : V →L[ℝ] V => S v) (ContinuousLinearMap.apply ℝ V v) T :=
    (ContinuousLinearMap.apply ℝ V v).hasFDerivAt
  have hg : HasFDerivAt (fun S : V →L[ℝ] V => S)
      (1 : (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] V)) T :=
    hasFDerivAt_id T
  have hbil := (ContinuousLinearMap.apply ℝ V).hasFDerivAt_of_bilinear hf hg
  have hder : ((ContinuousLinearMap.precompR (V →L[ℝ] V) (ContinuousLinearMap.apply ℝ V)) (T v))
        (1 : (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] V))
      + ((ContinuousLinearMap.precompL (V →L[ℝ] V) (ContinuousLinearMap.apply ℝ V))
          (ContinuousLinearMap.apply ℝ V v)) T
      = (ContinuousLinearMap.apply ℝ V (T v) + T.comp (ContinuousLinearMap.apply ℝ V v)) := by
    ext X
    simp only [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, add_apply,
      one_apply_eq_self]
  rw [hder] at hbil
  exact hbil

theorem almostComplex_relation {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    {r : ℝ} (hr : 0 < r) (hA : ContDiffOn ℝ 1 A (Work.NN.Newton.polydiscR n r))
    (hac : ∀ z ∈ Work.NN.Newton.polydiscR n r, ∀ v,
      (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v)
    {z : Work.NN.Core.Cn n} (hz : z ∈ Work.NN.Newton.polydiscR n r)
    (X Y : Work.NN.Core.Cn n) :
    (fderiv ℝ A z X) ((Work.NN.Core.JstdCn n + A) z Y)
      = -((Work.NN.Core.JstdCn n + A) z ((fderiv ℝ A z X) Y)) := by
  have hP : IsOpen (Work.NN.Newton.polydiscR n r) := Work.NN.Newton.isOpen_polydiscR n r
  -- `A` is differentiable at the interior point `z`, with derivative `DA_z`.
  have hAt : ContDiffAt ℝ 1 A z := hA.contDiffAt (hP.mem_nhds hz)
  have hAdiff : DifferentiableAt ℝ A z := hAt.differentiableAt (by norm_num)
  have hAder : HasFDerivAt A (fderiv ℝ A z) z := hAdiff.hasFDerivAt
  -- derivative of `w ↦ (JstdCn n + A) w`, the constant part contributing nothing
  have hΦ : HasFDerivAt (fun w : Work.NN.Core.Cn n => (Work.NN.Core.JstdCn n + A) w)
      (fderiv ℝ A z) z := by
    have h := hAder.const_add (Work.NN.Core.JstdCn n 0)
    convert h using 1
    ext w; rfl
  -- derivative of the operator square at `(JstdCn n + A) z`
  have hΨ := hasFDerivAt_clm_apply_self Y ((Work.NN.Core.JstdCn n + A) z)
  have hcomp := hΨ.comp z hΦ
  -- rewrite its derivative into the expanded form appearing in the conclusion
  have hder : (ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n) (((Work.NN.Core.JstdCn n + A) z) Y)
        + ((Work.NN.Core.JstdCn n + A) z).comp
            (ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n) Y)).comp (fderiv ℝ A z)
      = (ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n)
            (((Work.NN.Core.JstdCn n + A) z) Y)).comp (fderiv ℝ A z)
        + ((Work.NN.Core.JstdCn n + A) z).comp
            ((ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n) Y).comp (fderiv ℝ A z)) := by
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_assoc]
  have hG : HasFDerivAt
      (fun w : Work.NN.Core.Cn n => (Work.NN.Core.JstdCn n + A) w
        (((Work.NN.Core.JstdCn n + A) w) Y))
      ((ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n)
          (((Work.NN.Core.JstdCn n + A) z) Y)).comp (fderiv ℝ A z)
        + ((Work.NN.Core.JstdCn n + A) z).comp
            ((ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n) Y).comp (fderiv ℝ A z))) z := by
    rw [hder] at hcomp
    exact hcomp
  -- the composite is constant on the (open) polydisc, hence has zero derivative at `z`
  have hmem : ∀ᶠ w in 𝓝 z, w ∈ Work.NN.Newton.polydiscR n r := hP.mem_nhds hz
  have hconst : (fun w : Work.NN.Core.Cn n => (Work.NN.Core.JstdCn n + A) w
        (((Work.NN.Core.JstdCn n + A) w) Y)) =ᶠ[𝓝 z] (fun _ => -Y) :=
    hmem.mono (fun w hw => hac w hw Y)
  have hg0 : fderiv ℝ (fun w : Work.NN.Core.Cn n => (Work.NN.Core.JstdCn n + A) w
        (((Work.NN.Core.JstdCn n + A) w) Y)) z = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq hconst, fderiv_const_apply]
  -- hence the explicit derivative vanishes, and evaluating at `X` is the claim
  have hG0 : (ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n)
          (((Work.NN.Core.JstdCn n + A) z) Y)).comp (fderiv ℝ A z)
        + ((Work.NN.Core.JstdCn n + A) z).comp
            ((ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n) Y).comp (fderiv ℝ A z)) = 0 := by
    rw [← hG.fderiv, hg0]
  have hX := congrArg
    (fun f : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n => f X) hG0
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, ContinuousLinearMap.apply_apply] at hX
  exact eq_neg_of_add_eq_zero_left hX

end Work.NN.Newton.Defect
