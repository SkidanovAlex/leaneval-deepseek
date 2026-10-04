import ChallengeDeps
import Mathlib
import Submission.Work.Diff.EXT.evolKDefs
import Submission.Work.Diff.EXT.curvNormK_frame_indep
import Submission.Work.Diff.EXT.covK_linear
import Submission.Work.Diff.EXT.covK_valueDep
import Submission.Work.Diff.EXT.covKRmExt_tensorial
import Submission.Work.Diff.EXT.sum_fin_add_four
import Submission.Work.Diff.C.jetFunction
import Submission.Work.Diff.GE.mvfderivWithin_apply_mlieBracketWithin_two
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.GE.kato_geodesic_frame
import Submission.Work.Diff.GE.kato_lapl_sum
import Submission.Work.Diff.GE.Gest.lapl_mul
import Submission.Work.Diff.GE.kato_frame_second_antisymm
import Submission.Work.Diff.GE.dRmPhi_slotA
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.Kato3.CovRmKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Kato (Bochner/Weitzenböck) identity for `|∇^k Rm|²` (area `EXT`)

`Work.Diff.EXT.laplAt_curvNormK_eq` is the identity
`Δ|∇^k Rm|² = 2|∇^{k+1} Rm|² + 2⟪∇^k Rm, Δ∇^k Rm⟫` for the `k`-th covariant derivative of the
curvature of a smooth metric, in the form needed by `Work.Diff.EXT.evolK_of_flow`.

The proof follows the standard route: choose a `g`-orthonormal frame `W` which is geodesic at `x`
(`Work.Diff.GE.kato_geodesic_frame`), write `|∇^k Rm|²` as the sum of squares of the components of
`∇^k Rm` in that frame (the tower `ckt` of `Submission.Work.Diff.EXT.curvNormK_frame_indep`), apply
the product rule for `laplAt` (`Work.Diff.GE.Gest.lapl_mul`, `Work.Diff.GE.kato_lapl_sum`) and
identify the first and second derivatives of the components with the components of `∇^{k+1} Rm` and
`∇^k Rm` (`mvfderiv_ckt`, `mvfderiv2_ckt`).  The second derivative produces the *leftover* terms
coming from the second covariant derivative of the frame itself; these cancel when paired with the
components, by the antisymmetry of `g(∇_m∇_m W_j, W_β)` (`Work.Diff.GE.kato_frame_second_antisymm`)
and the combinatorial cancellation `cancelK`.
-/

set_option maxHeartbeats 2000000

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option linter.unusedSectionVars false

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

local macro "TfK" : term => `((y : M) → TangentSpace I y)

/-- `laplAt g · x` only depends on the germ of the function at `x`. -/
private theorem laplAt_congr_ev (g : SMet I M) {u v : M → ℝ} (x : M) (h : u =ᶠ[𝓝 x] v) :
    laplAt g u x = laplAt g v x := by
  have hmem : {z : M | u z = v z} ∈ 𝓝 x := h
  have hx : x ∈ interior {z : M | u z = v z} := mem_interior_iff_mem_nhds.mpr hmem
  have hinner : ∀ w : TangentSpace I x,
      (fun y : M => mvfderiv I u y (smoothExt x w y))
        =ᶠ[𝓝 x] (fun y : M => mvfderiv I v y (smoothExt x w y)) := by
    intro w
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    rw [Work.Diff.GE.mvfderiv_congr_eventuallyEq (I := I)
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset)]
  simp only [laplAt, hessAt]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Work.Diff.GE.mvfderiv_congr_eventuallyEq (I := I) (hinner (onFrame g x i)),
    Work.Diff.GE.mvfderiv_congr_eventuallyEq (I := I) h]

/-- The recursion of `ckt`, in the form where a new differentiation slot is prepended. -/
lemma ckt_succ_cons (g : SMet I M) (k : ℕ) (X : TfK) (F : Fin (k + 4) → TfK) :
    ckt g (k + 1) (Fin.cons X F)
      = (fun y : M => mvfderiv I (fun z : M => ckt g k F z) y (X y))
        - ∑ s : Fin (k + 4), ckt g k (Function.update F s (dirF g (F s) X)) := by
  have hF' : (fun i : Fin (k + 4) => (Fin.cons (α := fun _ : Fin (k + 4 + 1) => TfK) X F) i.succ)
      = F := by
    funext i
    exact Fin.cons_succ (α := fun _ : Fin (k + 4 + 1) => TfK) X F i
  have hX' : (Fin.cons (α := fun _ : Fin (k + 4 + 1) => TfK) X F) 0 = X :=
    Fin.cons_zero (α := fun _ : Fin (k + 4 + 1) => TfK) X F
  rw [ckt_succ, hF', hX']

/-- A finite combination of smooth fields over an arbitrary `Finset` is smooth. -/
lemma smoothF_finsum_partial {ι : Type*} (c : ι → ℝ) (Y : ι → TfK) (hY : ∀ i, SmoothF (Y i))
    (s : Finset ι) : SmoothF (∑ i ∈ s, (fun _ : M => c i) • Y i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact Work.Diff.GE.cmDiff_zeroField
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact smoothF_add ((contMDiff_const (c := c a)).smul_section (hY a)) ih

/-- A finite combination of smooth fields is smooth. -/
lemma smoothF_finsum {ι : Type*} [Fintype ι] (c : ι → ℝ) (Y : ι → TfK)
    (hY : ∀ i, SmoothF (Y i)) : SmoothF (∑ i, (fun _ : M => c i) • Y i) :=
  smoothF_finsum_partial c Y hY Finset.univ

/-- A tuple with a slot that vanishes at `x` evaluates to `0` at `x`. -/
lemma ckt_zero_slot (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ) {F : Fin (k + 4) → TfK}
    (hF : ∀ s, SmoothF (F s)) (s : Fin (k + 4)) (x : M) {Y : TfK}
    (hY : SmoothF Y) (hYx : Y x = 0) :
    ckt g k (Function.update F s Y) x = 0 := by
  have h1 : ckt g k (Function.update F s Y) x = ckt g k (Function.update F s 0) x :=
    ckt_val_dep hLC g k x hF s hY Work.Diff.GE.cmDiff_zeroField (by simpa using hYx)
  have h2 : ckt g k (Function.update F s (0 : TfK)) x = 0 := by
    have h := TensProp_smul hLC g (tensProp_all hLC g k) (F := F) hF s (0 : ℝ) (hF s)
    have e : (fun _ : M => (0 : ℝ)) • (F s) = (0 : TfK) := by
      funext y; simp
    rw [e, Function.update_eq_self] at h
    simpa using congrFun h x
  rw [h1, h2]

/-- If a slot of the tuple vanishes at `x`, the whole expression vanishes at `x`. -/
lemma ckt_zero_of_slot_zero (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ)
    {F : Fin (k + 4) → TfK} (hF : ∀ s, SmoothF (F s)) (s : Fin (k + 4)) (x : M)
    (hFs : F s x = 0) : ckt g k F x = 0 := by
  have h := ckt_zero_slot hLC g k hF s x (hF s) hFs
  simpa only [Function.update_eq_self] using h

/-- **The exact recursion**, evaluated at a point. -/
lemma mvfderiv_ckt_gen (g : SMet I M) (k : ℕ) (F : Fin (k + 4) → TfK) (X : TfK) (x : M) :
    mvfderiv I (fun y : M => ckt g k F y) x (X x)
      = ckt g (k + 1) (Fin.cons X F) x
        + ∑ s : Fin (k + 4), ckt g k (Function.update F s (dirF g (F s) X)) x := by
  have h := congrFun (ckt_succ_cons g k X F) x
  simp only [Finset.sum_apply, Pi.sub_apply] at h
  rw [h]; ring

/-- **First derivative of a component in a geodesic frame.** -/
lemma mvfderiv_ckt (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ) {F : Fin (k + 4) → TfK}
    (hF : ∀ s, SmoothF (F s)) (X : TfK) (hX : SmoothF X) (x : M)
    (hvan : ∀ s, dirF g (F s) X x = 0) :
    mvfderiv I (fun y : M => ckt g k F y) x (X x) = ckt g (k + 1) (Fin.cons X F) x := by
  rw [mvfderiv_ckt_gen]
  have hsum : (∑ s : Fin (k + 4), ckt g k (Function.update F s (dirF g (F s) X)) x) = 0 :=
    Finset.sum_eq_zero fun s _ => ckt_zero_slot hLC g k hF s x
      (dirF_smooth hLC g (hF s) hX) (hvan s)
  rw [hsum, add_zero]

/-- **Second derivative of a component in a geodesic frame**, with the leftover terms. -/
lemma mvfderiv2_ckt (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ) {F : Fin (k + 4) → TfK}
    (hF : ∀ s, SmoothF (F s)) (X : TfK) (hX : SmoothF X) (x : M)
    (hvan : ∀ s, dirF g (F s) X x = 0) (hvanX : dirF g X X x = 0) :
    mvfderiv I (fun y : M => mvfderiv I (fun z : M => ckt g k F z) y (X y)) x (X x)
      = ckt g (k + 2) (Fin.cons X (Fin.cons X F)) x
        + ∑ s : Fin (k + 4), ckt g k (Function.update F s (dirF g (dirF g (F s) X) X)) x := by
  have hsm1 : CMDiff ∞ (fun y : M => ckt g (k + 1) (Fin.cons X F) y) :=
    (tensProp_all hLC g (k + 1) (Fin.cons X F) (smoothF_cons hX hF)).1
  have hsm2 : CMDiff ∞ (fun y : M =>
      ∑ s : Fin (k + 4), ckt g k (Function.update F s (dirF g (F s) X)) y) :=
    ContMDiff.sum (fun s _ => (tensProp_all hLC g k _
      (smoothF_update hF (dirF_smooth hLC g (hF s) hX))).1)
  have hdec : (fun y : M => mvfderiv I (fun z : M => ckt g k F z) y (X y))
      = (fun y : M => ckt g (k + 1) (Fin.cons X F) y
          + ∑ s : Fin (k + 4), ckt g k (Function.update F s (dirF g (F s) X)) y) := by
    funext y
    rw [mvfderiv_ckt_gen]
  rw [hdec]
  have hfun : (fun y : M => ckt g (k + 1) (Fin.cons X F) y
        + ∑ s : Fin (k + 4), ckt g k (Function.update F s (dirF g (F s) X)) y)
      = (fun y : M => ckt g (k + 1) (Fin.cons X F) y)
        + (fun y : M => ∑ s : Fin (k + 4), ckt g k (Function.update F s (dirF g (F s) X)) y) :=
    rfl
  rw [hfun, mvfderiv_add (hsm1.mdifferentiableAt (by simp))
    (hsm2.mdifferentiableAt (by simp))]
  simp only [ContinuousLinearMap.add_apply]
  have h1 : mvfderiv I (fun y : M => ckt g (k + 1) (Fin.cons X F) y) x (X x)
      = ckt g (k + 2) (Fin.cons X (Fin.cons X F)) x := by
    refine mvfderiv_ckt hLC g (k + 1) (smoothF_cons hX hF) X hX x ?_
    intro s
    refine Fin.cases ?_ ?_ s
    · simpa only [Fin.cons_zero] using hvanX
    · intro j
      simpa only [Fin.cons_succ] using hvan j
  rw [h1]
  congr 1
  rw [Work.Diff.GE.Kato3.mvfderiv_sum (Finset.univ)
    (fun s : Fin (k + 4) => fun y : M => ckt g k (Function.update F s (dirF g (F s) X)) y)
    (fun s => (tensProp_all hLC g k _
      (smoothF_update hF (dirF_smooth hLC g (hF s) hX))).1) x (X x)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have hD : SmoothF (dirF g (F s) X) := dirF_smooth hLC g (hF s) hX
  have hG' : ∀ q, SmoothF ((Function.update F s (dirF g (F s) X)) q) := smoothF_update hF hD
  have hz1 : ckt g (k + 1) (Fin.cons X (Function.update F s (dirF g (F s) X))) x = 0 :=
    ckt_zero_of_slot_zero hLC g (k + 1) (smoothF_cons hX hG') (Fin.succ s) x (by
      simpa only [Fin.cons_succ, Function.update_self] using hvan s)
  have hsum : (∑ q : Fin (k + 4), ckt g k (Function.update (Function.update F s (dirF g (F s) X)) q
        (dirF g ((Function.update F s (dirF g (F s) X)) q) X)) x)
      = ckt g k (Function.update (Function.update F s (dirF g (F s) X)) s
          (dirF g ((Function.update F s (dirF g (F s) X)) s) X)) x := by
    refine Finset.sum_eq_single s ?_ ?_
    · intro q _ hqs
      have hT : Function.update (Function.update F s (dirF g (F s) X)) q
            (dirF g ((Function.update F s (dirF g (F s) X)) q) X)
          = Function.update (Function.update F q
              (dirF g ((Function.update F s (dirF g (F s) X)) q) X)) s (dirF g (F s) X) :=
        Function.update_comm (Ne.symm hqs) _ _ _
      rw [hT]
      exact ckt_zero_slot hLC g k (smoothF_update hF (dirF_smooth hLC g (hG' q) hX)) s x hD
        (hvan s)
    · intro hs; exact absurd (Finset.mem_univ s) hs
  have hs' : Function.update (Function.update F s (dirF g (F s) X)) s
      (dirF g ((Function.update F s (dirF g (F s) X)) s) X)
      = Function.update F s (dirF g (dirF g (F s) X) X) := by
    rw [Function.update_idem, Function.update_self]
  rw [mvfderiv_ckt_gen, hz1, zero_add, hsum, hs']

open Work.Diff.GE in
/-- **`hessAt` depends on its second argument only through the value.**  For a function `u` smooth at
`x`, the frozen `hessAt g u x v w` is defined with the `Classical.epsilon`-chosen extension
`smoothExt x w`; it equals the field-based expression with *any* smooth field `Z` with `Z x = w`, namely
`mvfderiv (fun y ↦ mvfderiv I u y (Z y)) x v - mvfderiv I u x (∇_v Z)`.  Equivalently, `hessAt g u x v w`
is the second covariant derivative `(∇_v du)(w)` of `u` at `x`.  Proof route: compare the two choices of
the field using the identity `X (Y f) = Y (X f) + [X, Y] f` for first and second directional derivatives
along fields (`Commons.Geometry.Manifold.VectorField.mvfderiv_second_along_fields`), the formula
`[X, Y] = ∇_X Y - ∇_Y X` for a torsion-free connection and the fact that `∇_X Y` at `x` depends only on
`X x`; alternatively use the Leibniz rule for the pairing `⟨du, Z⟩` of the covector field `du` with the
field `Z`, which gives `(∇_v du)(Z x)` directly. -/
theorem hessAt_field_aux
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) {u : M → ℝ} (hu : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ u x)
    (Y Z : Π y : M, TangentSpace I y) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    hessAt g u x (Y x) (Z x)
      = mvfderiv I (fun y : M ↦ mvfderiv I u y (Z y)) x (Y x)
        - mvfderiv I u x (lcOf g Z x (Y x)) := by
  classical
  haveI : IsManifold I (2 : ℕ∞ω) M :=
    IsManifold.of_le (I := I) (M := M) (m := (2 : ℕ∞ω)) (n := ∞) (by simp)
  -- `u` is `C²` at `x`, hence `C²` on an open neighbourhood `U` of `x`
  obtain ⟨U, hUopen, hxU, hUsm⟩ :=
    hu.contMDiffOn' (m := (2 : ℕ∞ω)) (n := ∞) (by simp) (by intro h; exact absurd h (by decide))
  have hUsm' : CMDiff[U] (2 : ℕ∞ω) u := by simpa using hUsm
  have hUmems : U ∈ 𝓝 x := hUopen.mem_nhds hxU
  -- within `U` the `mvfderivWithin` of a (scalar) function is its global `mvfderiv`
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
    have hmain := Work.Diff.GE.mvfderivWithin_apply_mlieBracketWithin_two
      (s := U) (f := u) (X := A) (Y := B) (x := x)
      hUopen.uniqueMDiffOn hxU hxs' hUsm' hAs hBs
    have hbr : mvfderivWithin I u U x (mlieBracketWithin I A B U x)
        = mvfderiv I u x (mlieBracket I A B x) := by
      rw [hw u]
      congr 1
      rw [← mlieBracketWithin_univ, ← univ_inter U,
        mlieBracketWithin_inter (s := univ) (t := U) hUmems]
    rw [hconv B, hconv A, hbr] at hmain
    exact hmain
  -- the two fields whose values at `x` are compared
  have hW : CMDiff ∞ (T% (smoothExt x (Z x))) := smoothExt_cmdiff x (Z x)
  have hWx : smoothExt x (Z x) x = Z x := smoothExt_apply x (Z x)
  have hYm : MDiffAt (T% Y) x := hY.contMDiffAt.mdifferentiableAt (by simp)
  have hWm : MDiffAt (T% (smoothExt x (Z x))) x := hW.contMDiffAt.mdifferentiableAt (by simp)
  have hZm : MDiffAt (T% Z) x := hZ.contMDiffAt.mdifferentiableAt (by simp)
  have htors : ∀ {A B : Π y : M, TangentSpace I y},
      MDiffAt (T% A) x → MDiffAt (T% B) x →
      ((lcOf g) B x) (A x) - ((lcOf g) A x) (B x) = mlieBracket I A B x :=
    fun hA hB => (CovariantDerivative.torsion_eq_zero_iff (lcOf g)).1 (hLC g).2.1 hA hB
  have htor1 : mlieBracket I Y (smoothExt x (Z x)) x
      = ((lcOf g) (smoothExt x (Z x)) x) (Y x) - ((lcOf g) Y x) (smoothExt x (Z x) x) :=
    (htors hYm hWm).symm
  have htor2 : mlieBracket I Y Z x = ((lcOf g) Z x) (Y x) - ((lcOf g) Y x) (Z x) :=
    (htors hYm hZm).symm
  have hkey1 := key Y (smoothExt x (Z x)) hY hW
  have hkey2 := key Y Z hY hZ
  rw [hessAt, hkey1, hkey2, htor1, htor2, hWx, map_sub, map_sub]
  abel

/-- **`laplAt` in a geodesic frame.** -/
lemma laplAt_eq_sum_frameK (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → TfK) (hWs : ∀ i, SmoothF (W i))
    (hWx : ∀ i, W i x = onFrame g x i) (hgeo : ∀ m j, lcOf g (W j) x (W m x) = 0)
    {u : M → ℝ} (hu : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ u x) :
    laplAt g u x = ∑ i, mvfderiv I (fun y : M => mvfderiv I u y (W i y)) x (W i x) := by
  simp only [laplAt]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 := hessAt_field_aux hLC g x hu (W i) (W i) (hWs i) (hWs i)
  rw [← hWx i, h1, hgeo i i, map_zero, sub_zero]

/-- **Expansion of a tangent vector in an orthonormal frame.** -/
lemma expand_frameK (g : SMet I M) (x : M) (W : Fin (Module.finrank ℝ E) → TfK)
    (hn : 0 < Module.finrank ℝ E) (hON : IsONFrame g x (fun i => W i x))
    (A : TangentSpace I x) :
    ∑ e, g.inner x (W e x) A • W e x = A :=
  Work.Diff.GE.sum_inner_smul_eq_self g x hn (fun i => W i x) hON A

/-- **The value-level linearity in a single slot.** -/
lemma Kpt_sum_slot (hLC : LCSmooth I M) (g : SMet I M) (x : M) (k : ℕ)
    {ι : Type*} [Fintype ι] (w : Fin (k + 4) → TangentSpace I x) (s : Fin (k + 4))
    (c : ι → ℝ) (Y : ι → TangentSpace I x) :
    Kpt g x k (Function.update w s (∑ i, c i • Y i))
      = ∑ i, c i • Kpt g x k (Function.update w s (Y i)) := by
  classical
  have key : ∀ t : Finset ι,
      Kpt g x k (Function.update w s (∑ i ∈ t, c i • Y i))
        = ∑ i ∈ t, c i • Kpt g x k (Function.update w s (Y i)) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      have h := Kpt_smul hLC g x k w s (0 : ℝ) (w s)
      simpa using h
    | insert a t ha ih =>
      have hsum : (∑ i ∈ insert a t, c i • Y i) = c a • Y a + ∑ i ∈ t, c i • Y i := by
        rw [Finset.sum_insert ha]
      have step : Kpt g x k (Function.update w s (c a • Y a + ∑ i ∈ t, c i • Y i))
          = Kpt g x k (Function.update w s (c a • Y a))
            + Kpt g x k (Function.update w s (∑ i ∈ t, c i • Y i)) :=
        Kpt_add hLC g x k w s (c a • Y a) (∑ i ∈ t, c i • Y i)
      have step2 : Kpt g x k (Function.update w s (c a • Y a))
          = c a • Kpt g x k (Function.update w s (Y a)) :=
        Kpt_smul hLC g x k w s (c a) (Y a)
      rw [hsum, step, step2, ih, Finset.sum_insert ha]
  simpa using key Finset.univ

/-- `ckt` at a point is the value-level evaluation `Kpt` of its tuple of values. -/
lemma ckt_eq_Kpt (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ) (x : M)
    {T : Fin (k + 4) → TfK} (hT : ∀ s, SmoothF (T s)) :
    ckt g k T x = Kpt g x k (fun s => T s x) := by
  have h := ckt_val_dep_all (I := I) (M := M) hLC g k x hT
    (fun s => Work.Diff.GE.smoothExt_cmdiff x (T s x))
    (fun s => by rw [Work.Diff.GE.smoothExt_apply])
  show ckt g k T x = ckt g k (fun s => smoothExt x (T s x)) x
  exact h

/-- **The leftover terms, with the frame coefficients made explicit.** -/
lemma leftover_ckt (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ) (x : M)
    (W : Fin (Module.finrank ℝ E) → TfK) (hWs : ∀ i, SmoothF (W i))
    (hON : IsONFrame g x (fun e => W e x))
    (w : Fin (k + 4) → Fin (Module.finrank ℝ E)) (i : Fin (Module.finrank ℝ E)) :
    (∑ s : Fin (k + 4), ckt g k (Function.update (fun s : Fin (k + 4) => W (w s)) s
        (dirF g (dirF g (W (w s)) (W i)) (W i))) x)
      = ∑ s : Fin (k + 4), ∑ e : Fin (Module.finrank ℝ E),
          g.inner x (W e x) (dirF g (dirF g (W (w s)) (W i)) (W i) x)
            * ckt g k (fun s' : Fin (k + 4) => W ((Function.update w s e) s')) x := by
  have hn : 0 < Module.finrank ℝ E := Fin.pos_iff_nonempty.mpr ⟨i⟩
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have hF : ∀ s' : Fin (k + 4), SmoothF ((fun s : Fin (k + 4) => W (w s)) s') :=
    fun s' => hWs (w s')
  have hAsm : SmoothF (dirF g (dirF g (W (w s)) (W i)) (W i)) :=
    dirF_smooth hLC g (dirF_smooth hLC g (hWs _) (hWs i)) (hWs i)
  have hSsm : SmoothF (∑ e, (fun _ : M =>
      g.inner x (W e x) (dirF g (dirF g (W (w s)) (W i)) (W i) x)) • W e) :=
    smoothF_finsum _ _ hWs
  have hval : (∑ e, g.inner x (W e x) (dirF g (dirF g (W (w s)) (W i)) (W i) x) • W e x)
      = dirF g (dirF g (W (w s)) (W i)) (W i) x :=
    expand_frameK g x W hn hON _
  have step1 : ckt g k (Function.update (fun s : Fin (k + 4) => W (w s)) s
        (dirF g (dirF g (W (w s)) (W i)) (W i))) x
      = ckt g k (Function.update (fun s : Fin (k + 4) => W (w s)) s
          (∑ e, (fun _ : M => g.inner x (W e x)
            (dirF g (dirF g (W (w s)) (W i)) (W i) x)) • W e)) x :=
    ckt_val_dep_all hLC g k x (smoothF_update hF hAsm) (smoothF_update hF hSsm) (by
      intro s'
      rw [Function.update_apply, Function.update_apply]
      by_cases hs' : s' = s
      · rw [ite_eq_left hs', ite_eq_left hs']
        simp only [Finset.sum_apply, Pi.smul_apply]
        exact hval.symm
      · rw [ite_eq_right hs', ite_eq_right hs'])
  rw [step1]
  rw [ckt_eq_Kpt hLC g k x (smoothF_update hF hSsm)]
  rw [show (fun s' : Fin (k + 4) => (Function.update (fun s : Fin (k + 4) => W (w s)) s
        (∑ e, (fun _ : M => g.inner x (W e x)
          (dirF g (dirF g (W (w s)) (W i)) (W i) x)) • W e)) s' x)
      = Function.update (fun s' : Fin (k + 4) => W (w s') x) s
          (∑ e, g.inner x (W e x) (dirF g (dirF g (W (w s)) (W i)) (W i) x) • W e x) from by
    funext s'
    rw [Function.update_apply, Function.update_apply]
    by_cases h : s' = s
    · rw [ite_eq_left h, ite_eq_left h]
      simp only [Finset.sum_apply, Pi.smul_apply', smul_eq_mul]
    · rw [ite_eq_right h, ite_eq_right h]]
  rw [Kpt_sum_slot hLC g x k (fun s' : Fin (k + 4) => W (w s') x) s _ _]
  simp only [smul_eq_mul]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  congr 1
  rw [ckt_eq_Kpt (T := fun s' : Fin (k + 4) => W ((Function.update w s e) s')) hLC g k x
    (fun s' => hWs _)]
  congr 1
  funext s'
  by_cases hs' : s' = s <;> simp [hs']

/-- **Cancellation of the leftover terms.** -/
private theorem cancelK {n m : ℕ} (cM : Fin n → Fin n → Fin n → ℝ)
    (hcM : ∀ i a b, cM i a b = - cM i b a) (P : (Fin m → Fin n) → ℝ) :
    (∑ α : Fin m → Fin n, P α * (∑ i : Fin n, ∑ j : Fin m, ∑ β : Fin n,
        cM i (α j) β * P (Function.update α j β))) = 0 := by
  classical
  have hdiag : ∀ i a, cM i a a = 0 := by
    intro i a
    have h := hcM i a a
    linarith
  have hsingle : ∀ i : Fin n, ∀ j : Fin m,
      (∑ α : Fin m → Fin n, ∑ β : Fin n,
        P α * cM i (α j) β * P (Function.update α j β)) = 0 := by
    intro i j
    rw [← Fintype.sum_prod_type (fun x : (Fin m → Fin n) × Fin n =>
      P x.1 * cM i (x.1 j) x.2 * P (Function.update x.1 j x.2))]
    refine Finset.sum_ninvolution (s := Finset.univ)
      (f := fun x : (Fin m → Fin n) × Fin n =>
        P x.1 * cM i (x.1 j) x.2 * P (Function.update x.1 j x.2))
      (fun x => (Function.update x.1 j x.2, x.1 j)) ?_ ?_ ?_ ?_
    · intro a
      have h1 : Function.update a.1 j a.2 j = a.2 := Function.update_self _ _ _
      have h2 : Function.update (Function.update a.1 j a.2) j (a.1 j) = a.1 := by
        rw [Function.update_idem, Function.update_eq_self]
      simp only [h1, h2, hcM i a.2 (a.1 j)]
      ring
    · intro a hg hga
      apply hg
      have h1 : a.1 j = a.2 := by
        simpa using congrArg (fun p : (Fin m → Fin n) × Fin n => p.2) hga
      rw [← h1]
      simp [hdiag]
    · intro a; exact Finset.mem_univ _
    · intro a
      refine Prod.ext ?_ ?_
      · rw [Function.update_idem, Function.update_eq_self]
      · exact Function.update_self _ _ _
  have hconv : (∑ α : Fin m → Fin n, P α * (∑ i : Fin n, ∑ j : Fin m, ∑ β : Fin n,
        cM i (α j) β * P (Function.update α j β)))
      = ∑ i : Fin n, ∑ j : Fin m, ∑ α : Fin m → Fin n, ∑ β : Fin n,
          P α * cM i (α j) β * P (Function.update α j β) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun α _ => ?_)
    refine Finset.sum_congr rfl (fun β _ => ?_)
    ring
  rw [hconv]
  simp [hsingle]


/-- The equivalence `(Fin d × (Fin k → Fin d)) ≃ (Fin (k+1) → Fin d)` given by prepending. -/
def finConsEquiv (k d : ℕ) : (Fin d × (Fin k → Fin d)) ≃ (Fin (k + 1) → Fin d) where
  toFun p := Fin.cons p.1 p.2
  invFun w := (w 0, fun i => w i.succ)
  left_inv p := by
    obtain ⟨a, g⟩ := p
    refine Prod.ext rfl ?_
    funext i
    exact Fin.cons_succ (α := fun _ : Fin (k + 1) => Fin d) a g i
  right_inv w := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp

/-- The tuple of frame fields attached to a multi-index. -/
noncomputable def frmTup (W : Fin (Module.finrank ℝ E) → TfK) {k : ℕ}
    (w : Fin (k + 4) → Fin (Module.finrank ℝ E)) : Fin (k + 4) → TfK :=
  fun s => W (w s)

lemma frmTup_cons (W : Fin (Module.finrank ℝ E) → TfK) {k : ℕ} (i : Fin (Module.finrank ℝ E))
    (w : Fin (k + 4) → Fin (Module.finrank ℝ E)) :
    Fin.cons (W i) (frmTup W w) = frmTup W (Fin.cons i w) := by
  funext s
  refine Fin.cases ?_ ?_ s
  · simp [frmTup]
  · intro j
    simp [frmTup]

/-- **Identification of the frozen `covKRm` with the tower `ckt`** (frame vectors). -/
lemma covKRm_eq_ckt_W (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ) (x : M)
    {W : Fin (Module.finrank ℝ E) → TfK} (hWs : ∀ i, SmoothF (W i))
    (w : Fin (k + 4) → Fin (Module.finrank ℝ E)) :
    covKRm g x k (fun r : Fin k => W (w (Fin.castAdd 4 r)) x)
        (W (w (Fin.natAdd k 0)) x) (W (w (Fin.natAdd k 1)) x)
        (W (w (Fin.natAdd k 2)) x) (W (w (Fin.natAdd k 3)) x)
      = ckt g k (frmTup W w) x := by
  have hva : ∀ r : Fin k, (fun z : M => smoothExt x (W (w (Fin.castAdd 4 r)) x) z) x
      = (fun z : M => W (w (Fin.castAdd 4 r)) z) x := by
    intro r
    show smoothExt x (W (w (Fin.castAdd 4 r)) x) x = W (w (Fin.castAdd 4 r)) x
    rw [Work.Diff.GE.smoothExt_apply]
  rw [show covKRm g x k (fun r : Fin k => W (w (Fin.castAdd 4 r)) x)
        (W (w (Fin.natAdd k 0)) x) (W (w (Fin.natAdd k 1)) x)
        (W (w (Fin.natAdd k 2)) x) (W (w (Fin.natAdd k 3)) x)
      = covKRmExt g k (fun r : Fin k => fun z : M => smoothExt x (W (w (Fin.castAdd 4 r)) x) z)
          (fun z : M => smoothExt x (W (w (Fin.natAdd k 0)) x) z)
          (fun z : M => smoothExt x (W (w (Fin.natAdd k 1)) x) z)
          (fun z : M => smoothExt x (W (w (Fin.natAdd k 2)) x) z)
          (fun z : M => smoothExt x (W (w (Fin.natAdd k 3)) x) z) x from rfl]
  rw [covKRmExt_tensorial hLC k g x _ _ _ _ _ _ _ _ _ _
    (fun r => Work.Diff.GE.smoothExt_cmdiff x _) (fun r => hWs _)
    (Work.Diff.GE.smoothExt_cmdiff x _) (hWs _) (Work.Diff.GE.smoothExt_cmdiff x _) (hWs _)
    (Work.Diff.GE.smoothExt_cmdiff x _) (hWs _) (Work.Diff.GE.smoothExt_cmdiff x _) (hWs _)
    hva (by show smoothExt x (W (w (Fin.natAdd k 0)) x) x = W (w (Fin.natAdd k 0)) x
            rw [Work.Diff.GE.smoothExt_apply])
    (by show smoothExt x (W (w (Fin.natAdd k 1)) x) x = W (w (Fin.natAdd k 1)) x
        rw [Work.Diff.GE.smoothExt_apply])
    (by show smoothExt x (W (w (Fin.natAdd k 2)) x) x = W (w (Fin.natAdd k 2)) x
        rw [Work.Diff.GE.smoothExt_apply])
    (by show smoothExt x (W (w (Fin.natAdd k 3)) x) x = W (w (Fin.natAdd k 3)) x
        rw [Work.Diff.GE.smoothExt_apply])]
  exact (ckt_eq_covKRmExt g k (frmTup W w) x).symm

/-- The component of `∇^k Rm` in the frame, as a `ckt`-value at the corresponding multi-index. -/
lemma covKRmC_eq_ckt_append (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ) (x : M)
    {W : Fin (Module.finrank ℝ E) → TfK} (hWs : ∀ i, SmoothF (W i))
    (ι : Fin k → Fin (Module.finrank ℝ E)) (i j l m : Fin (Module.finrank ℝ E)) :
    covKRmC g x (fun i => W i x) k ι i j l m
      = ckt g k (frmTup W (Fin.append ι ![i, j, l, m])) x := by
  rw [covKRmC_eq_covKRm]
  have h1 : (fun r : Fin k => W (ι r) x)
      = (fun r : Fin k => W ((Fin.append ι ![i, j, l, m]) (Fin.castAdd 4 r)) x) := by
    funext r; rw [Fin.append_left]
  have h2 : W i x = W ((Fin.append ι ![i, j, l, m]) (Fin.natAdd k 0)) x := by
    rw [Fin.append_right]; rfl
  have h3 : W j x = W ((Fin.append ι ![i, j, l, m]) (Fin.natAdd k 1)) x := by
    rw [Fin.append_right]; rfl
  have h4 : W l x = W ((Fin.append ι ![i, j, l, m]) (Fin.natAdd k 2)) x := by
    rw [Fin.append_right]; rfl
  have h5 : W m x = W ((Fin.append ι ![i, j, l, m]) (Fin.natAdd k 3)) x := by
    rw [Fin.append_right]; rfl
  rw [h1, h2, h3, h4, h5]
  exact covKRm_eq_ckt_W hLC g k x hWs (Fin.append ι ![i, j, l, m])

/-- **The reduction of `curvNormK` to a sum of squares of components.** -/
lemma curvNormK_eq_sum_ckt (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ) (x : M)
    {W : Fin (Module.finrank ℝ E) → TfK} (hWs : ∀ i, SmoothF (W i))
    (hON : IsONFrame g x (fun i => W i x)) :
    curvNormK g x k
      = ∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E), (ckt g k (frmTup W w) x) ^ 2 := by
  rw [curvNormK_frame_indep hLC x k (fun i => W i x) hON]
  rw [show (∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
        (covKRmC g x (fun i => W i x) k ι i j l m) ^ 2)
      = ∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
        (ckt g k (frmTup W (Fin.append ι ![i, j, l, m])) x) ^ 2 from by
    refine Finset.sum_congr rfl (fun ι _ => Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ =>
        Finset.sum_congr rfl (fun m _ => by rw [covKRmC_eq_ckt_append hLC g k x hWs])))))]
  rw [← sum_fin_add_four (fun w : Fin (k + 4) → Fin (Module.finrank ℝ E) =>
    (ckt g k (frmTup W w) x) ^ 2)]

/-- Reindexing: a sum over the trace index together with the multi-index. -/
lemma sum_cons_reindex {d k : ℕ} (G : (Fin (k + 1) → Fin d) → ℝ) :
    (∑ i : Fin d, ∑ w : Fin k → Fin d, G (Fin.cons i w)) = ∑ w' : Fin (k + 1) → Fin d, G w' := by
  have h1 : (∑ i : Fin d, ∑ w : Fin k → Fin d, G (Fin.cons i w))
      = ∑ p : Fin d × (Fin k → Fin d), G (Fin.cons p.1 p.2) := by
    rw [Fintype.sum_prod_type]
  rw [h1]
  exact Fintype.sum_equiv (finConsEquiv k d) (fun p : Fin d × (Fin k → Fin d) =>
    G (Fin.cons p.1 p.2)) G (fun p => rfl)


set_option maxHeartbeats 4000000 in
/-- **The Kato computation in a geodesic frame**: the Laplacian of the sum of squares of the
components of `∇^k Rm` equals `2 |∇^{k+1} Rm|² + 2 ⟨∇^k Rm, Δ∇^k Rm⟩` at `x`. -/
theorem kato_tower (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ) (x : M)
    (W : Fin (Module.finrank ℝ E) → TfK) (hWs : ∀ i, SmoothF (W i))
    (hWON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => W i y))
    (hWx : ∀ i, W i x = onFrame g x i) (hgeo : ∀ m j, lcOf g (W j) x (W m x) = 0) :
    laplAt g (fun y : M => ∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
        (ckt g k (frmTup W w) y) ^ 2) x
      = 2 * (∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
              ∑ i : Fin (Module.finrank ℝ E),
              (ckt g (k + 1) (frmTup W (Fin.cons i w)) x) ^ 2)
        + 2 * (∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
              ∑ i : Fin (Module.finrank ℝ E),
              ckt g k (frmTup W w) x
                * ckt g (k + 2) (frmTup W (Fin.cons i (Fin.cons i w))) x) := by
  classical
  rw [Work.Diff.GE.kato_lapl_sum g (fun w (y : M) => (ckt g k (frmTup W w) y) ^ 2) x
    (fun w => ((tensProp_all hLC g k (frmTup W w) (fun s => hWs (w s))).1).pow 2)]
  have hprod : ∀ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
      laplAt g (fun y : M => (ckt g k (frmTup W w) y) ^ 2) x
        = 2 * (ckt g k (frmTup W w) x * laplAt g (fun y : M => ckt g k (frmTup W w) y) x)
          + 2 * ∑ i : Fin (Module.finrank ℝ E),
              (mvfderiv I (fun y : M => ckt g k (frmTup W w) y) x (onFrame g x i)) ^ 2 := by
    intro w
    have hsm : CMDiff ∞ (fun y : M => ckt g k (frmTup W w) y) :=
      (tensProp_all hLC g k (frmTup W w) (fun s => hWs (w s))).1
    have h := Work.Diff.GE.Gest.lapl_mul g hsm hsm x
    rw [show (fun y : M => (ckt g k (frmTup W w) y) ^ 2)
        = (fun y : M => ckt g k (frmTup W w) y * ckt g k (frmTup W w) y) from by
      funext y; ring]
    rw [h]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          mvfderiv I (fun y : M => ckt g k (frmTup W w) y) x (onFrame g x i)
            * mvfderiv I (fun y : M => ckt g k (frmTup W w) y) x (onFrame g x i))
        = ∑ i : Fin (Module.finrank ℝ E),
          (mvfderiv I (fun y : M => ckt g k (frmTup W w) y) x (onFrame g x i)) ^ 2 from
      Finset.sum_congr rfl (fun i _ => by ring)]
    ring
  simp only [hprod]
  have hlap : ∀ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
      laplAt g (fun y : M => ckt g k (frmTup W w) y) x
        = ∑ i : Fin (Module.finrank ℝ E),
            mvfderiv I (fun y : M => mvfderiv I (fun z : M => ckt g k (frmTup W w) z) y
              (W i y)) x (W i x) := by
    intro w
    exact laplAt_eq_sum_frameK hLC g x W hWs hWx hgeo
      ((tensProp_all hLC g k (frmTup W w) (fun s => hWs (w s))).1.contMDiffAt)
  simp only [hlap]
  have hvan : ∀ (w : Fin (k + 4) → Fin (Module.finrank ℝ E)) (i : Fin (Module.finrank ℝ E))
      (s : Fin (k + 4)), dirF g (frmTup W w s) (W i) x = 0 := by
    intro w i s
    show lcOf g (W (w s)) x (W i x) = 0
    exact hgeo i (w s)
  have hmv1 : ∀ (w : Fin (k + 4) → Fin (Module.finrank ℝ E)) (i : Fin (Module.finrank ℝ E)),
      mvfderiv I (fun y : M => ckt g k (frmTup W w) y) x (onFrame g x i)
        = ckt g (k + 1) (frmTup W (Fin.cons i w)) x := by
    intro w i
    have h := mvfderiv_ckt hLC g k (F := frmTup W w) (fun s => hWs (w s)) (W i) (hWs i) x
      (hvan w i)
    rw [frmTup_cons] at h
    rw [← hWx i]
    exact h
  have hmv2 : ∀ (w : Fin (k + 4) → Fin (Module.finrank ℝ E)) (i : Fin (Module.finrank ℝ E)),
      mvfderiv I (fun y : M => mvfderiv I (fun z : M => ckt g k (frmTup W w) z) y (W i y))
          x (W i x)
        = ckt g (k + 2) (frmTup W (Fin.cons i (Fin.cons i w))) x
          + ∑ s : Fin (k + 4), ckt g k (Function.update (frmTup W w) s
              (dirF g (dirF g (W (w s)) (W i)) (W i))) x := by
    intro w i
    have h := mvfderiv2_ckt hLC g k (F := frmTup W w) (fun s => hWs (w s)) (W i) (hWs i) x
      (hvan w i) (by
        show lcOf g (W i) x (W i x) = 0
        exact hgeo i i)
    rw [frmTup_cons, frmTup_cons] at h
    exact h
  simp only [hmv1, hmv2]
  have hONx : IsONFrame g x (fun e => W e x) := by
    intro a b
    show g.inner x (W a x) (W b x) = if a = b then 1 else 0
    rw [hWx a, hWx b]
    exact Work.Diff.GE.isONFrame_onFrame g x a b
  have hsplit : ∀ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
      2 * (ckt g k (frmTup W w) x *
          ∑ i : Fin (Module.finrank ℝ E),
            (ckt g (k + 2) (frmTup W (Fin.cons i (Fin.cons i w))) x
              + ∑ s : Fin (k + 4),
                  ckt g k (Function.update (frmTup W w) s
                    (dirF g (dirF g (W (w s)) (W i)) (W i))) x))
        = (2 * (ckt g k (frmTup W w) x *
              ∑ i : Fin (Module.finrank ℝ E),
                ckt g (k + 2) (frmTup W (Fin.cons i (Fin.cons i w))) x))
          + (2 * (ckt g k (frmTup W w) x *
              ∑ i : Fin (Module.finrank ℝ E), ∑ s : Fin (k + 4),
                ckt g k (Function.update (frmTup W w) s
                  (dirF g (dirF g (W (w s)) (W i)) (W i))) x)) := by
    intro w
    rw [Finset.sum_add_distrib]
    ring
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun w _ => hsplit w)]
  rw [Finset.sum_add_distrib]
  have hcore : (∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
        ckt g k (frmTup W w) x *
          ∑ i : Fin (Module.finrank ℝ E), ∑ s : Fin (k + 4),
            ckt g k (Function.update (frmTup W w) s
              (dirF g (dirF g (W (w s)) (W i)) (W i))) x) = 0 := by
    have hbst : ∀ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
        ckt g k (frmTup W w) x *
          (∑ i : Fin (Module.finrank ℝ E), ∑ s : Fin (k + 4),
            ckt g k (Function.update (frmTup W w) s
              (dirF g (dirF g (W (w s)) (W i)) (W i))) x)
        = ckt g k (frmTup W w) x *
          (∑ i : Fin (Module.finrank ℝ E), ∑ s : Fin (k + 4),
            ∑ e : Fin (Module.finrank ℝ E),
              g.inner x (W e x) (dirF g (dirF g (W (w s)) (W i)) (W i) x)
                * ckt g k (frmTup W (Function.update w s e)) x) := by
      intro w
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact leftover_ckt hLC g k x W hWs hONx w i
    rw [Finset.sum_congr rfl (fun w _ => hbst w)]
    exact cancelK (fun i a b => g.inner x (W b x) (dirF g (dirF g (W a) (W i)) (W i) x))
      (fun i a b => by
        have h := Work.Diff.GE.kato_frame_second_antisymm hLC g W x hWs hWON hgeo i a b
        have h1 : g.inner x (W b x) (dirF g (dirF g (W a) (W i)) (W i) x)
            = g.inner x (dirF g (dirF g (W a) (W i)) (W i) x) (W b x) :=
          g.symm x (W b x) (dirF g (dirF g (W a) (W i)) (W i) x)
        have h2 : g.inner x (W a x) (dirF g (dirF g (W b) (W i)) (W i) x)
            = g.inner x (dirF g (dirF g (W b) (W i)) (W i) x) (W a x) :=
          g.symm x (W a x) (dirF g (dirF g (W b) (W i)) (W i) x)
        rw [h1, h2]
        exact h)
      (fun a => ckt g k (frmTup W a) x)
  have hLzero : (∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
        2 * (ckt g k (frmTup W w) x *
          ∑ i : Fin (Module.finrank ℝ E), ∑ s : Fin (k + 4),
            ckt g k (Function.update (frmTup W w) s
              (dirF g (dirF g (W (w s)) (W i)) (W i))) x)) = 0 := by
    rw [← Finset.mul_sum, hcore, mul_zero]
  have hSd : (∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
        2 * (ckt g k (frmTup W w) x *
          ∑ i : Fin (Module.finrank ℝ E),
            ckt g (k + 2) (frmTup W (Fin.cons i (Fin.cons i w))) x))
      = 2 * (∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
          ∑ i : Fin (Module.finrank ℝ E),
            ckt g k (frmTup W w) x
              * ckt g (k + 2) (frmTup W (Fin.cons i (Fin.cons i w))) x) := by
    rw [← Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.mul_sum]
  have hQd : (∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
        2 * ∑ i : Fin (Module.finrank ℝ E),
          ckt g (k + 1) (frmTup W (Fin.cons i w)) x ^ 2)
      = 2 * (∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
          ∑ i : Fin (Module.finrank ℝ E),
            ckt g (k + 1) (frmTup W (Fin.cons i w)) x ^ 2) := by
    rw [← Finset.mul_sum]
  rw [hLzero, hSd, hQd]
  ring

/-- **The component of `∇^k Rm` on the frame `onFrame g x`, through the tower `ckt`.** -/
lemma covKRm_eq_ckt_frame_aux (hLC : LCSmooth I M) (g : SMet I M) (x : M) (k : ℕ)
    {W : Fin (Module.finrank ℝ E) → TfK} (hWs : ∀ i, SmoothF (W i))
    (hWx : ∀ i, W i x = onFrame g x i)
    (ι : Fin k → Fin (Module.finrank ℝ E)) (i j l m : Fin (Module.finrank ℝ E)) :
    covKRm g x k (fun r => onFrame g x (ι r)) (onFrame g x i)
        (onFrame g x j) (onFrame g x l) (onFrame g x m)
      = ckt g k (frmTup W (Fin.append ι ![i, j, l, m])) x := by
  have h1 : covKRm g x k (fun r => onFrame g x (ι r)) (onFrame g x i)
      (onFrame g x j) (onFrame g x l) (onFrame g x m)
      = covKRmC g x (onFrame g x) k ι i j l m := rfl
  rw [h1, ← funext hWx]
  exact covKRmC_eq_ckt_append hLC g k x hWs ι i j l m

/-- **The rough Laplacian of `∇^k Rm` traced in `onFrame g x`, through the tower `ckt`.** -/
lemma lapCovKRm_eq_sum_ckt_aux (hLC : LCSmooth I M) (g : SMet I M) (x : M) (k : ℕ)
    {W : Fin (Module.finrank ℝ E) → TfK} (hWs : ∀ i, SmoothF (W i))
    (hWx : ∀ i, W i x = onFrame g x i)
    (ι : Fin k → Fin (Module.finrank ℝ E)) (i j l m : Fin (Module.finrank ℝ E)) :
    lapCovKRm g x k (fun r => onFrame g x (ι r)) (onFrame g x i)
        (onFrame g x j) (onFrame g x l) (onFrame g x m)
      = ∑ a : Fin (Module.finrank ℝ E),
          ckt g (k + 2)
            (frmTup W ((Fin.cons a (Fin.cons a (Fin.append ι ![i, j, l, m]))) :
              Fin (k + 2 + 4) → Fin (Module.finrank ℝ E))) x := by
  rw [lapCovKRm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  let wI : Fin (k + 2 + 4) → Fin (Module.finrank ℝ E) :=
    Fin.cons a (Fin.cons a (Fin.append ι ![i, j, l, m]))
  let uI : Fin (k + 2) → Fin (Module.finrank ℝ E) := Fin.cons a (Fin.cons a ι)
  have hwI : wI = Fin.cons a (Fin.cons a (Fin.append ι ![i, j, l, m])) := rfl
  have huI : uI = Fin.cons a (Fin.cons a ι) := rfl
  have h := covKRm_eq_ckt_W hLC g (k + 2) x hWs wI
  rw [← h]
  have hcons : (fun r : Fin (k + 2) => onFrame g x (uI r))
      = Fin.cons (onFrame g x a) (Fin.cons (onFrame g x a) (fun r => onFrame g x (ι r))) := by
    funext r
    refine Fin.cases ?_ ?_ r
    · rfl
    · intro j1
      refine Fin.cases ?_ ?_ j1
      · rfl
      · intro q1
        rfl
  have hidx : ∀ r : Fin (k + 2), wI (Fin.castAdd 4 r) = uI r := by
    intro r
    rw [hwI, huI]
    refine Fin.cases ?_ ?_ r
    · rfl
    · intro j1
      rw [Fin.cons_succ]
      refine Fin.cases ?_ ?_ j1
      · rfl
      · intro q1
        rw [Fin.cons_succ]
        exact Fin.append_left ι ![i, j, l, m] q1
  have hcur : ∀ t : Fin 4, wI (Fin.natAdd (k + 2) t) = ![i, j, l, m] t := by
    intro t
    rw [hwI]
    fin_cases t
    · show Fin.append ι ![i, j, l, m] (Fin.natAdd k (0 : Fin 4)) = ![i, j, l, m] (0 : Fin 4)
      rw [Fin.append_right]
    · show Fin.append ι ![i, j, l, m] (Fin.natAdd k (1 : Fin 4)) = ![i, j, l, m] (1 : Fin 4)
      rw [Fin.append_right]
    · show Fin.append ι ![i, j, l, m] (Fin.natAdd k (2 : Fin 4)) = ![i, j, l, m] (2 : Fin 4)
      rw [Fin.append_right]
    · show Fin.append ι ![i, j, l, m] (Fin.natAdd k (3 : Fin 4)) = ![i, j, l, m] (3 : Fin 4)
      rw [Fin.append_right]
  have hfl : (fun r : Fin (k + 2) => W (wI (Fin.castAdd 4 r)) x)
      = Fin.cons (onFrame g x a) (Fin.cons (onFrame g x a) (fun r => onFrame g x (ι r))) := by
    funext r
    rw [hWx, hidx r]
    exact congrFun hcons r
  rw [hfl, hWx (wI (Fin.natAdd (k + 2) 0)), hWx (wI (Fin.natAdd (k + 2) 1)),
    hWx (wI (Fin.natAdd (k + 2) 2)), hWx (wI (Fin.natAdd (k + 2) 3)),
    hcur 0, hcur 1, hcur 2, hcur 3]
  rfl

/-- A finite sum `∑ i, f i • Y i` of smooth functions times smooth fields is smooth. -/
lemma smoothF_finsum_gen {ι : Type*} [Fintype ι] (f : ι → M → ℝ) (Y : ι → TfK)
    (hf : ∀ i, CMDiff ∞ (f i)) (hY : ∀ i, SmoothF (Y i)) :
    SmoothF (∑ i, f i • Y i) := by
  classical
  have h : ∀ i, SmoothF (f i • Y i) := fun i => (hf i).smul_section (hY i)
  have key : ∀ t : Finset ι, SmoothF (∑ i ∈ t, f i • Y i) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      exact Work.Diff.GE.cmDiff_zeroField
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact smoothF_add (h a) ih
  exact key Finset.univ

/-- **A globally smooth function with prescribed value and derivative at a point.** -/
theorem jetCovector (x : M) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    ∃ f : M → ℝ, CMDiff ∞ f ∧ f x = 0 ∧ mvfderiv I f x = ξ := by
  classical
  set D : TangentSpace I x →L[ℝ] E := mfderiv I 𝓘(ℝ,E) (extChartAt I x) x with hDdef
  have hD : D.IsInvertible :=
    isInvertible_mfderiv_extChartAt (I := I) (x := x) (mem_extChartAt_source x)
  set ℓ : E →L[ℝ] ℝ := ξ.comp D.inverse with hℓdef
  have hℓD : ℓ.comp D = ξ := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, hℓdef]
    rw [hD.inverse_apply_self v]
  obtain ⟨ψ, -, hψsupp⟩ : ∃ ψ : SmoothBumpFunction I x,
      True ∧ tsupport (ψ : M → ℝ) ⊆ (chartAt H x).source :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  set g : M → ℝ := fun y => ℓ ((extChartAt I x) y - (extChartAt I x) x) with hg
  have hgOn : ContMDiffOn I 𝓘(ℝ,ℝ) ∞ g (chartAt H x).source := by
    have h1 : ContMDiffOn I 𝓘(ℝ,E) ∞ (fun y : M => (extChartAt I x) y - (extChartAt I x) x)
        (chartAt H x).source :=
      (contMDiffOn_extChartAt (I := I) (x := x)).sub_const _
    exact (ℓ.contMDiff).comp_contMDiffOn h1
  have hgcd : CMDiff ∞ (fun y : M => (ψ : M → ℝ) y • g y) := ψ.contMDiff_smul hgOn
  have hgd : MDifferentiableAt I 𝓘(ℝ,ℝ) g x :=
    ((hgOn x (mem_chart_source H x)).contMDiffAt
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))).mdifferentiableAt (by simp)
  have hψd : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y : M => (ψ : M → ℝ) y) x :=
    ψ.contMDiff.mdifferentiableAt (by simp)
  have hg0 : g x = 0 := by simp [hg, map_sub]
  have hψx : (ψ : M → ℝ) x = 1 := SmoothBumpFunction.eq_one ψ
  have hgderiv : mvfderiv I g x = ξ := by
    rw [hg, Work.Diff.C.mvfderiv_affine_chart]
    exact hℓD
  refine ⟨fun y => (ψ : M → ℝ) y * g y, ?_, ?_, ?_⟩
  · simpa only [smul_eq_mul] using hgcd
  · simp only [hg, SmoothBumpFunction.eq_one, sub_self, map_zero, mul_zero]
  · have hmul := mvfderiv_mul (f := fun y : M => (ψ : M → ℝ) y) (g := g) hψd hgd
    show mvfderiv I ((fun y : M => (ψ : M → ℝ) y) * g) x = ξ
    rw [hmul, hψx, hg0, one_smul, zero_smul, add_zero]
    exact hgderiv

open scoped Matrix in
/-- **Jet correction for the Levi-Civita connection.**  Every tangent vector at `x` extends to a
globally smooth vector field `Y` with `Y x = u` and `∇Y|_x = 0`. -/
theorem lcOf_jet_correction_aux (g : SMet I M) (x : M) (u : TangentSpace I x) :
    ∃ Y : TfK, SmoothF Y ∧ Y x = u ∧ lcOf g Y x = 0 := by
  classical
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    Module.finBasis ℝ (TangentSpace I x) with hb
  set Z : TfK := smoothExt x u with hZ
  have hZs : SmoothF Z := Work.Diff.GE.smoothExt_cmdiff x u
  have hZx : Z x = u := Work.Diff.GE.smoothExt_apply x u
  set A : TangentSpace I x →L[ℝ] TangentSpace I x := lcOf g Z x with hA
  have hf : ∀ i : Fin (Module.finrank ℝ E),
      ∃ f : M → ℝ, CMDiff ∞ f ∧ f x = 0 ∧
        mvfderiv I f x = LinearMap.toContinuousLinearMap (b.coord i) :=
    fun i => jetCovector x (LinearMap.toContinuousLinearMap (b.coord i))
  choose f hfs hfx hfderiv using hf
  set W' : Fin (Module.finrank ℝ E) → TfK := fun i => smoothExt x (-(A (b i))) with hW'
  have hW's : ∀ i, SmoothF (W' i) := fun i => Work.Diff.GE.smoothExt_cmdiff x (-(A (b i)))
  have hW'x : ∀ i, W' i x = -(A (b i)) :=
    fun i => Work.Diff.GE.smoothExt_apply x (-(A (b i)))
  set S : TfK := ∑ i, f i • W' i with hS
  have hSs : SmoothF S := by
    rw [hS]
    exact smoothF_finsum_gen f W' hfs hW's
  have hSx : S x = 0 := by
    rw [hS]
    simp only [Finset.sum_apply, Pi.smul_apply']
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hfx i, zero_smul]
  have hSderiv : lcOf g S x = -A := by
    ext v
    rw [hS, Work.Diff.GE.kato_lcOf_sum_apply g x Finset.univ f W'
      (fun i _ => hfs i) (fun i _ => hW's i) v]
    have hterm : ∀ i : Fin (Module.finrank ℝ E),
        f i x • lcOf g (W' i) x v + mvfderiv I (f i) x v • W' i x
          = -(b.coord i v) • (A (b i)) := by
      intro i
      rw [hfx i, zero_smul, zero_add, hfderiv i, hW'x i]
      simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
      rw [smul_neg, neg_smul]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    have hrep : (∑ i, (b.coord i v) • b i) = v := by
      simpa only [Module.Basis.coord_apply] using b.sum_repr v
    have hgoal : -(A v) = ∑ i : Fin (Module.finrank ℝ E), (-(b.coord i v)) • (A (b i)) := by
      conv_lhs => rw [← hrep]
      rw [map_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul, ← neg_smul]
    exact hgoal.symm
  refine ⟨Z + S, ?_, ?_, ?_⟩
  · exact smoothF_add hZs hSs
  · show Z x + S x = u
    rw [hZx, hSx, add_zero]
  · have h1 : MDiffAt (T% Z) x := hZs.contMDiffAt.mdifferentiableAt (by simp)
    have h2 : MDiffAt (T% S) x := hSs.contMDiffAt.mdifferentiableAt (by simp)
    rw [(lcOf g).isCovariantDerivativeOn.add h1 h2, hSderiv, ← hA]
    exact add_neg_cancel A

open Work.Diff.GE in
/-- **A geodesic orthonormal frame at a point** (from the jet correction `lcOf_jet_correction_aux`). -/
theorem geodesic_frame_aux (g : SMet I M) (x : M) :
    ∃ W : Fin (Module.finrank ℝ E) → TfK,
      (∀ i, SmoothF (W i)) ∧
      (∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => W i y)) ∧
      (∀ i, W i x = onFrame g x i) ∧
      (∀ m j, lcOf g (W j) x (W m x) = 0):= by
  classical
  set e : katoIdx E → TangentSpace I x := onFrame g x with hedef
  have he : IsONFrame g x e := isONFrame_onFrame g x
  choose V hVs hVx hVc using fun i => lcOf_jet_correction_aux g x (e i)
  have key : ∀ m : ℕ, ∀ i : katoIdx E, i.val < m →
      (SmoothF (katoFrame g x V i))
      ∧ (katoFrame g x V i x = V i x)
      ∧ (lcOf g (katoFrame g x V i) x = 0)
      ∧ (∀ᶠ y in 𝓝 x, g.inner y (katoFrame g x V i y) (katoFrame g x V i y) = 1)
      ∧ (∀ᶠ y in 𝓝 x, ∀ k, k.val < i.val →
          g.inner y (katoFrame g x V i y) (katoFrame g x V k y) = 0) := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact ih i hlt
      · have hIH : ∀ j, j.val < i.val →
            (CMDiff ∞ (T% (katoFrame g x V j)))
            ∧ (katoFrame g x V j x = V j x)
            ∧ (lcOf g (katoFrame g x V j) x = 0)
            ∧ (∀ᶠ y in 𝓝 x, g.inner y (katoFrame g x V j y) (katoFrame g x V j y) = 1)
            ∧ (∀ᶠ y in 𝓝 x, ∀ k, k.val < j.val →
                g.inner y (katoFrame g x V j y) (katoFrame g x V k y) = 0) :=
          fun j hj => ih j (by rw [← heq]; exact hj)
        obtain ⟨hUs, hGs⟩ :=
          kato_smooth g V (katoFrame g x V) i (hVs i) (fun j hj => (hIH j hj).1)
        have hON : ∀ j, j.val < i.val → g.inner x (V i x) (V j x) = 0 := by
          intro j hj
          have hne : i ≠ j := by
            intro hij; rw [← hij] at hj; exact absurd hj (Nat.lt_irrefl _)
          rw [hVx i, hVx j, he i j, ite_eq_right hne]
        have hUx : katoU g V (katoFrame g x V) i x = V i x :=
          katoU_apply_x g x V (katoFrame g x V) i (fun j hj => (hIH j hj).2.1) hON
        have hV1 : g.inner x (V i x) (V i x) = 1 := by
          rw [hVx i, he i i, ite_eq_left rfl]
        have hfx : 0 < katoGram g V (katoFrame g x V) i x := by
          rw [katoGram_apply_x g x V (katoFrame g x V) i hUx hV1]; norm_num
        obtain ⟨hFpos, hFs, hCs, hCeq, hFx, hFeq⟩ :=
          kato_smooth_norm g x V (katoFrame g x V) i hGs hfx
        have hUc : lcOf g (katoU g V (katoFrame g x V) i) x = 0 :=
          katoU_cov_zero g x V (katoFrame g x V) i (hVs i)
            (fun j hj => (hIH j hj).1) (hVc i) (fun j hj => (hIH j hj).2.2.1)
            (fun j hj => (hIH j hj).2.1) hON
        have hdf := katoGram_mvfderiv_zero g x V (katoFrame g x V) i hUs hUc
        have hψs : CMDiff ∞ (katoBump (I := I) (katoGram g V (katoFrame g x V) i) x) :=
          (katoBump_spec hGs hfx).1
        have hdF := katoNorm_mvfderiv_zero g x V (katoFrame g x V) i hGs hψs hdf
        have hdC := katoC_mvfderiv_zero g x V (katoFrame g x V) i hFs hFpos hdF
        have hCx : katoC g x V (katoFrame g x V) i x = 1 :=
          katoC_apply_x g x V (katoFrame g x V) i
            (by rw [hFx, katoGram_apply_x g x V (katoFrame g x V) i hUx hV1])
        have hWx : katoFrame g x V i x = V i x := by
          rw [katoFrame_eq g x V i]
          show katoC g x V (katoFrame g x V) i x • katoU g V (katoFrame g x V) i x = V i x
          rw [hCx, hUx, one_smul]
        have hWs : CMDiff ∞ (T% (katoFrame g x V i)) := by
          rw [katoFrame_eq g x V i]
          exact hCs.smul_section hUs
        have hWc : lcOf g (katoFrame g x V i) x = 0 := by
          have hUsd : MDiffAt (T% (katoU g V (katoFrame g x V) i)) x :=
            hUs.contMDiffAt.mdifferentiableAt (by simp)
          have hCsd : MDiffAt (katoC g x V (katoFrame g x V) i) x :=
            hCs.contMDiffAt.mdifferentiableAt (by simp)
          have hdC0 : mvfderiv I (katoC g x V (katoFrame g x V) i) x = 0 := by
            ext v; exact hdC v
          rw [katoFrame_eq g x V i,
            show katoStep g x V (katoFrame g x V) i
              = (katoC g x V (katoFrame g x V) i) • (katoU g V (katoFrame g x V) i) from rfl,
            (lcOf g).isCovariantDerivativeOn.leibniz hUsd hCsd, hdC0, hUc, hCx]
          simp
        have hdiag_prev : ∀ᶠ y in 𝓝 x, ∀ j, j.val < i.val →
            g.inner y (katoFrame g x V j y) (katoFrame g x V j y) = 1 := by
          rw [Filter.eventually_all]
          intro j
          by_cases hj : j.val < i.val
          · filter_upwards [(hIH j hj).2.2.2.1] with y hy
            exact fun _ => hy
          · exact Filter.Eventually.of_forall fun y h => absurd h hj
        have hoff_prev : ∀ᶠ y in 𝓝 x, ∀ j, j.val < i.val → ∀ k, k.val < j.val →
            g.inner y (katoFrame g x V j y) (katoFrame g x V k y) = 0 := by
          rw [Filter.eventually_all]
          intro j
          by_cases hj : j.val < i.val
          · filter_upwards [(hIH j hj).2.2.2.2] with y hy
            exact fun _ => hy
          · exact Filter.Eventually.of_forall fun y h => absurd h hj
        have hbump1 : ∀ᶠ y in 𝓝 x,
            katoBump (I := I) (katoGram g V (katoFrame g x V) i) x y = 1 :=
          (katoBump_spec hGs hfx).2.2.2.2
        have hfpos_ev : ∀ᶠ y in 𝓝 x, 0 < katoGram g V (katoFrame g x V) i y :=
          (hGs x).continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hfx)
        have hdiag_i : ∀ᶠ y in 𝓝 x,
            g.inner y (katoFrame g x V i y) (katoFrame g x V i y) = 1 := by
          filter_upwards [hbump1, hfpos_ev, hdiag_prev, hoff_prev] with y hb hf hp ho
          rw [katoFrame_eq g x V i]
          exact (kato_orthonormal_algebra g x V (katoFrame g x V) i y hb hf hp ho).1
        have hoff_i : ∀ᶠ y in 𝓝 x, ∀ k, k.val < i.val →
            g.inner y (katoFrame g x V i y) (katoFrame g x V k y) = 0 := by
          filter_upwards [hbump1, hfpos_ev, hdiag_prev, hoff_prev] with y hb hf hp ho
          intro k hk
          rw [katoFrame_eq g x V i]
          exact (kato_orthonormal_algebra g x V (katoFrame g x V) i y hb hf hp ho).2 k hk
        exact ⟨hWs, hWx, hWc, hdiag_i, hoff_i⟩
  refine ⟨katoFrame g x V, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (key (i.val + 1) i (Nat.lt_succ_self _)).1
  · refine isONFrame_of_diag_off g x (katoFrame g x V) ?_ ?_
    · rw [Filter.eventually_all]
      intro i
      exact (key (i.val + 1) i (Nat.lt_succ_self _)).2.2.2.1
    · rw [Filter.eventually_all]
      intro i
      exact (key (i.val + 1) i (Nat.lt_succ_self _)).2.2.2.2
  · intro i
    rw [(key (i.val + 1) i (Nat.lt_succ_self _)).2.1]
    exact hVx i
  · intro m j
    rw [(key (m.val + 1) m (Nat.lt_succ_self _)).2.1,
      (key (j.val + 1) j (Nat.lt_succ_self _)).2.2.1]
    rw [hVx m]
    rfl

end Helpers

theorem laplAt_curvNormK_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] :
    ∀ (g : Submission.Diff.SMet I M) (x : M) (k : ℕ), 1 ≤ k →
      Submission.Diff.laplAt g (fun y => Work.Diff.EXT.curvNormK g y k) x =
        2 * Work.Diff.EXT.curvNormK g x (k + 1) +
        2 * (∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
              Work.Diff.EXT.covKRm g x k (fun r => Submission.Diff.onFrame g x (ι r))
                (Submission.Diff.onFrame g x i) (Submission.Diff.onFrame g x j)
                (Submission.Diff.onFrame g x l) (Submission.Diff.onFrame g x m) *
              Work.Diff.EXT.lapCovKRm g x k (fun r => Submission.Diff.onFrame g x (ι r))
                (Submission.Diff.onFrame g x i) (Submission.Diff.onFrame g x j)
                (Submission.Diff.onFrame g x l) (Submission.Diff.onFrame g x m)) := by
  intro g x k hk
  obtain ⟨W, hWsm, hWON, hWx, hgeo⟩ := geodesic_frame_aux g x
  have hLC : LCSmooth I M := Work.Diff.T.lc_smooth
  have hWs : ∀ i, SmoothF (W i) := hWsm
  have hONx : IsONFrame g x (fun i => W i x) := by
    intro a b
    show g.inner x (W a x) (W b x) = if a = b then 1 else 0
    rw [hWx a, hWx b]
    exact Work.Diff.GE.isONFrame_onFrame g x a b
  have hev : (fun y : M => curvNormK g y k) =ᶠ[𝓝 x]
      (fun y : M => ∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
        (ckt g k (frmTup W w) y) ^ 2) := by
    filter_upwards [hWON] with y hy
    exact curvNormK_eq_sum_ckt hLC g k y hWs hy
  rw [laplAt_congr_ev g x hev, kato_tower hLC g k x W hWs hWON hWx hgeo]
  have hQ : (∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
        ∑ i : Fin (Module.finrank ℝ E), (ckt g (k + 1) (frmTup W (Fin.cons i w)) x) ^ 2)
      = curvNormK g x (k + 1) := by
    rw [Finset.sum_comm]
    rw [sum_cons_reindex (fun w' : Fin (k + 4 + 1) → Fin (Module.finrank ℝ E) =>
      (ckt g (k + 1) (frmTup W w') x) ^ 2)]
    exact (curvNormK_eq_sum_ckt hLC g (k + 1) x hWs hONx).symm
  have hS : (∑ w : Fin (k + 4) → Fin (Module.finrank ℝ E),
        ∑ a : Fin (Module.finrank ℝ E),
          ckt g k (frmTup W w) x * ckt g (k + 2) (frmTup W (Fin.cons a (Fin.cons a w))) x)
      = ∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            ∑ m : Fin (Module.finrank ℝ E),
              covKRm g x k (fun r => onFrame g x (ι r)) (onFrame g x i)
                  (onFrame g x j) (onFrame g x l) (onFrame g x m)
                * lapCovKRm g x k (fun r => onFrame g x (ι r)) (onFrame g x i)
                    (onFrame g x j) (onFrame g x l) (onFrame g x m) := by
    rw [sum_fin_add_four (fun w : Fin (k + 4) → Fin (Module.finrank ℝ E) =>
      ∑ a : Fin (Module.finrank ℝ E),
        ckt g k (frmTup W w) x * ckt g (k + 2) (frmTup W (Fin.cons a (Fin.cons a w))) x)]
    refine Finset.sum_congr rfl (fun ι _ => ?_)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [covKRm_eq_ckt_frame_aux hLC g x k hWs hWx ι i j l m,
      lapCovKRm_eq_sum_ckt_aux hLC g x k hWs hWx ι i j l m,
      ← Finset.mul_sum]
  rw [hQ, hS]

end Work.Diff.EXT
