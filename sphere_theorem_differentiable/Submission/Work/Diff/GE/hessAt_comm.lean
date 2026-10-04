import Mathlib
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.mvfderivWithin_apply_mlieBracketWithin_two

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Symmetry of the Hessian `hessAt`

`Submission.Diff.hessAt g u x v w` is the second covariant derivative of `u` at `x` in the
directions `v`, `w`, computed with the `Classical.epsilon`-chosen smooth extensions
`smoothExt x v`, `smoothExt x w` of `v`, `w`:

`hessAt g u x v w = (d% (fun y ↦ d% u y (smoothExt x w y)) x) v − (d% u x) (∇_v smoothExt x w)`.

For a `C²` function `u` and a torsion free connection (`LCSmooth I M`) this is symmetric in
`v`, `w`.  The proof is the standard one: the antisymmetrised difference of the two second
directional derivatives along two smooth fields `A`, `B` equals
`(d% u x) ([A,B] x) − (d% u x) (∇_A B x) + (d% u x) (∇_B A x)`, which vanishes by torsion
freeness and linearity of `d% u x`.  The commutation identity for a merely `C²` function is
`Work.Diff.GE.mvfderivWithin_apply_mlieBracketWithin_two`.

This file is used to justify the definition of the Laplacian `laplAt` (its value does not depend
on the chosen orthonormal frame).
-/

namespace Work.Diff.GE

set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

theorem hessAt_comm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (u : M → ℝ) (x : M)
    (hu : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) 2 u x) (v w : TangentSpace I x) :
    Submission.Diff.hessAt g u x v w = Submission.Diff.hessAt g u x w v := by
  classical
  haveI : IsManifold I (2 : ℕ∞ω) M :=
    IsManifold.of_le (I := I) (M := M) (m := (2 : ℕ∞ω)) (n := ∞) (by simp)
  -- `u` is `C²` on an open neighbourhood `U` of `x`
  obtain ⟨U, hUopen, hxU, hUsm⟩ :=
    hu.contMDiffOn' (m := (2 : ℕ∞ω)) (n := (2 : ℕ∞ω)) (by simp) (by intro h; exact absurd h (by decide))
  have hUsm' : CMDiff[U] (2 : ℕ∞ω) u := by simpa using hUsm
  have hUmems : U ∈ 𝓝 x := hUopen.mem_nhds hxU
  -- within the open set `U` the `mvfderivWithin` of a (scalar) function is its global `mvfderiv`
  have hw : ∀ (F : M → ℝ), mvfderivWithin I F U x = mvfderiv I F x :=
    fun F => by simp only [mvfderivWithin, mvfderiv, mfderivWithin_of_mem_nhds hUmems]
  have hconv : ∀ (B' : Π z : M, TangentSpace I z),
      mvfderivWithin I (fun z => mvfderivWithin I u U z (B' z)) U x
        = mvfderiv I (fun z => mvfderiv I u z (B' z)) x := by
    intro B'
    have hev : (fun z => mvfderiv I u z (B' z)) =ᶠ[𝓝[U] x]
        (fun z => mvfderivWithin I u U z (B' z)) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [mvfderivWithin, mvfderiv, mfderivWithin_of_isOpen hUopen hz]
    have hx' : (fun z => mvfderiv I u z (B' z)) x
        = (fun z => mvfderivWithin I u U z (B' z)) x := by
      simp only [mvfderivWithin, mvfderiv, mfderivWithin_of_isOpen hUopen hxU]
    have hcongr := Commons.Geometry.Manifold.VectorField.mvfderivWithin_congr_eventually
      (I := I) (s := U) (x := x) hev hx'
    rw [← hcongr, hw (fun z => mvfderiv I u z (B' z))]
  -- the commutation identity `X(Yu) − Y(Xu) = [X,Y]u` for two smooth fields, `u` only `C²` on `U`
  have key : ∀ (A B : Π y : M, TangentSpace I y), CMDiff ∞ (T% A) → CMDiff ∞ (T% B) →
      mvfderiv I (fun y => mvfderiv I u y (B y)) x (A x)
        = mvfderiv I (fun y => mvfderiv I u y (A y)) x (B x)
          + mvfderiv I u x (mlieBracket I A B x) := by
    intro A B hA hB
    have hAs : CMDiff[U] ∞ (T% A) := (contMDiffOn_univ.mpr hA).mono (subset_univ U)
    have hBs : CMDiff[U] ∞ (T% B) := (contMDiffOn_univ.mpr hB).mono (subset_univ U)
    have hxs' : x ∈ closure (interior U) := by
      rw [hUopen.interior_eq]; exact subset_closure hxU
    have hmain := mvfderivWithin_apply_mlieBracketWithin_two (s := U) (f := u) (X := A) (Y := B)
      (x := x) hUopen.uniqueMDiffOn hxU hxs' hUsm' hAs hBs
    have hbr : mvfderivWithin I u U x (mlieBracketWithin I A B U x)
        = mvfderiv I u x (mlieBracket I A B x) := by
      rw [hw u]
      congr 1
      rw [← mlieBracketWithin_univ, ← univ_inter U,
        mlieBracketWithin_inter (s := univ) (t := U) hUmems]
    rw [hconv B, hconv A, hbr] at hmain
    exact hmain
  -- the two smooth fields whose restrictions to `x` are `v` and `w`
  have hA : CMDiff ∞ (T% (smoothExt x v)) := smoothExt_cmdiff x v
  have hB : CMDiff ∞ (T% (smoothExt x w)) := smoothExt_cmdiff x w
  have hv : smoothExt x v x = v := smoothExt_apply x v
  have hwv : smoothExt x w x = w := smoothExt_apply x w
  have hkey : mvfderiv I (fun y => mvfderiv I u y (smoothExt x w y)) x v
      = mvfderiv I (fun y => mvfderiv I u y (smoothExt x v y)) x w
        + mvfderiv I u x (mlieBracket I (smoothExt x v) (smoothExt x w) x) := by
    have := key (smoothExt x v) (smoothExt x w) hA hB
    simpa only [hv, hwv] using this
  -- torsion freeness turns the bracket into the connection terms
  have hAv : MDiffAt (T% (smoothExt x v)) x := hA.contMDiffAt.mdifferentiableAt (by simp)
  have hBv : MDiffAt (T% (smoothExt x w)) x := hB.contMDiffAt.mdifferentiableAt (by simp)
  have htor : ((lcOf g) (smoothExt x w) x) v - ((lcOf g) (smoothExt x v) x) w
      = mlieBracket I (smoothExt x v) (smoothExt x w) x := by
    have h0 := (CovariantDerivative.torsion_eq_zero_iff (lcOf g)).1 (hLC g).2.1 hAv hBv
    simpa only [hv, hwv] using h0
  rw [hessAt, hessAt, hkey, ← htor, map_sub]
  abel

end Work.Diff.GE
