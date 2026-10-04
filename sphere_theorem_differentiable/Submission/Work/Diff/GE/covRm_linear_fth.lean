import Mathlib
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.dRmPhi_slotA
import Submission.Work.Diff.GE.Frame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ℝ`-linearity of `covRm` in its fourth argument

The frozen `covRm g x v a b c d` is `dRmPhi g x v (smoothExt x a) … (smoothExt x d)` on the chosen
extensions (`covRm_eq_dRmPhi`), so its linearity in the fourth argument `c` is the statement that
the operation `dRmPhi` is `C^∞(M)`-linear in its **third** field slot.  The field `C` occurs in the
integrand `rmP g y (A y) (B y) (C y) (D y)` as the *third* argument of `rmP` and as `C x` in three
of the four connection correction terms, and as `lcOf g C x v` in the remaining one; the relevant
pointwise lemmas are therefore `rmP_add_thd`, `rmP_smul_thd`, `rmP_sum_thd`.

This file mirrors `Work.Diff.GE.dRmPhi_slotA` (which does the same for the first field slot) with
`rmP`'s first slot replaced by its third slot throughout.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Commons.Geometry.Manifold.VectorField

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

variable {g : SMet I M} {x : M} {v : TangentSpace I x}

/-! ## `dRmPhi` is linear in its third field slot -/

/-- `dRmPhi` is `ℝ`-linear (in fact `C^∞(M)`-linear) in its third field slot. -/
theorem fth_dRmPhi_linear (hLC : LCSmooth I M)
    {A B C₁ C₂ D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC₁ : CMDiff ∞ (T% C₁)) (hC₂ : CMDiff ∞ (T% C₂)) (hD : CMDiff ∞ (T% D))
    {f₁ f₂ : M → ℝ} (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    dRmPhi g x v A B (f₁ • C₁ + f₂ • C₂) D
      = f₁ x * dRmPhi g x v A B C₁ D + f₂ x * dRmPhi g x v A B C₂ D := by
  have hF₁c : CMDiff ∞ (fun y : M => rmP g y (A y) (B y) (C₁ y) (D y)) :=
    rmP_fields_smooth hLC g hA hB hC₁ hD
  have hF₂c : CMDiff ∞ (fun y : M => rmP g y (A y) (B y) (C₂ y) (D y)) :=
    rmP_fields_smooth hLC g hA hB hC₂ hD
  have hF₁d : MDiffAt (fun y : M => rmP g y (A y) (B y) (C₁ y) (D y)) x :=
    hF₁c.mdifferentiableAt (by simp)
  have hF₂d : MDiffAt (fun y : M => rmP g y (A y) (B y) (C₂ y) (D y)) x :=
    hF₂c.mdifferentiableAt (by simp)
  have hf₁d : MDiffAt f₁ x := hf₁.mdifferentiableAt (by simp)
  have hf₂d : MDiffAt f₂ x := hf₂.mdifferentiableAt (by simp)
  -- the integrand: `rmP` of a sum of scaled fields is the sum of the scaled `rmP`s
  have hint : (fun y : M => rmP g y (A y) (B y) ((f₁ • C₁ + f₂ • C₂) y) (D y))
      = f₁ * (fun y : M => rmP g y (A y) (B y) (C₁ y) (D y))
        + f₂ * (fun y : M => rmP g y (A y) (B y) (C₂ y) (D y)) := by
    funext y
    rw [show (f₁ • C₁ + f₂ • C₂) y = f₁ y • C₁ y + f₂ y • C₂ y from rfl]
    simp only [rmP_add_thd g hLC, rmP_smul_thd g hLC]
    rfl
  have hderiv : mvfderiv I (fun y : M => rmP g y (A y) (B y) ((f₁ • C₁ + f₂ • C₂) y) (D y)) x v
      = (f₁ x * mvfderiv I (fun y : M => rmP g y (A y) (B y) (C₁ y) (D y)) x v
          + mvfderiv I f₁ x v * rmP g x (A x) (B x) (C₁ x) (D x))
        + (f₂ x * mvfderiv I (fun y : M => rmP g y (A y) (B y) (C₂ y) (D y)) x v
          + mvfderiv I f₂ x v * rmP g x (A x) (B x) (C₂ x) (D x)) := by
    rw [hint, mvfderiv_add (hf₁d.mul hF₁d) (hf₂d.mul hF₂d),
      mvfderiv_mul (f := f₁) (g := fun y : M => rmP g y (A y) (B y) (C₁ y) (D y)) hf₁d hF₁d,
      mvfderiv_mul (f := f₂) (g := fun y : M => rmP g y (A y) (B y) (C₂ y) (D y)) hf₂d hF₂d]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  -- the connection: additivity and Leibniz in the third slot
  have hfC₁ : CMDiff ∞ (T% (f₁ • C₁)) := hf₁.smul_section hC₁
  have hfC₂ : CMDiff ∞ (T% (f₂ • C₂)) := hf₂.smul_section hC₂
  have hconnv : (lcOf g) (f₁ • C₁ + f₂ • C₂) x v
      = (lcOf g) (f₁ • C₁) x v + (lcOf g) (f₂ • C₂) x v := by
    have h := (lcOf g).isCovariantDerivativeOn.add (hfC₁.mdifferentiableAt (by simp))
      (hfC₂.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) h, add_apply]
  have hlei₁ : (lcOf g) (f₁ • C₁) x v = f₁ x • (lcOf g) C₁ x v + mvfderiv I f₁ x v • C₁ x := by
    have h := (lcOf g).isCovariantDerivativeOn.leibniz (σ := C₁) (g := f₁)
      (hC₁.mdifferentiableAt (by simp)) (hf₁.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) h, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  have hlei₂ : (lcOf g) (f₂ • C₂) x v = f₂ x • (lcOf g) C₂ x v + mvfderiv I f₂ x v • C₂ x := by
    have h := (lcOf g).isCovariantDerivativeOn.leibniz (σ := C₂) (g := f₂)
      (hC₂.mdifferentiableAt (by simp)) (hf₂.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) h, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  -- the four correction terms
  have hcx : (f₁ • C₁ + f₂ • C₂) x = f₁ x • C₁ x + f₂ x • C₂ x := rfl
  have hc₁ : rmP g x (A x) (B x) ((lcOf g) (f₁ • C₁ + f₂ • C₂) x v) (D x)
      = f₁ x * rmP g x (A x) (B x) ((lcOf g) C₁ x v) (D x)
        + mvfderiv I f₁ x v * rmP g x (A x) (B x) (C₁ x) (D x)
        + (f₂ x * rmP g x (A x) (B x) ((lcOf g) C₂ x v) (D x)
          + mvfderiv I f₂ x v * rmP g x (A x) (B x) (C₂ x) (D x)) := by
    rw [hconnv, hlei₁, hlei₂]
    simp only [rmP_add_thd g hLC, rmP_smul_thd g hLC]
  have hc₂ : rmP g x (A x) ((lcOf g) B x v) ((f₁ • C₁ + f₂ • C₂) x) (D x)
      = f₁ x * rmP g x (A x) ((lcOf g) B x v) (C₁ x) (D x)
        + f₂ x * rmP g x (A x) ((lcOf g) B x v) (C₂ x) (D x) := by
    rw [hcx]
    simp only [rmP_add_thd g hLC, rmP_smul_thd g hLC]
  have hc₃ : rmP g x (A x) (B x) ((f₁ • C₁ + f₂ • C₂) x) ((lcOf g) D x v)
      = f₁ x * rmP g x (A x) (B x) (C₁ x) ((lcOf g) D x v)
        + f₂ x * rmP g x (A x) (B x) (C₂ x) ((lcOf g) D x v) := by
    rw [hcx]
    simp only [rmP_add_thd g hLC, rmP_smul_thd g hLC]
  have hc₄ : rmP g x ((lcOf g) A x v) (B x) ((f₁ • C₁ + f₂ • C₂) x) (D x)
      = f₁ x * rmP g x ((lcOf g) A x v) (B x) (C₁ x) (D x)
        + f₂ x * rmP g x ((lcOf g) A x v) (B x) (C₂ x) (D x) := by
    rw [hcx]
    simp only [rmP_add_thd g hLC, rmP_smul_thd g hLC]
  simp only [dRmPhi]
  rw [hderiv, hc₁, hc₂, hc₃, hc₄]
  ring

/-- The homogeneity special case of `fth_dRmPhi_linear`. -/
theorem fth_dRmPhi_smul (hLC : LCSmooth I M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    {f : M → ℝ} (hf : CMDiff ∞ f) :
    dRmPhi g x v A B (f • C) D = f x * dRmPhi g x v A B C D := by
  have h := fth_dRmPhi_linear (g := g) (x := x) (v := v) hLC (A := A) (B := B) (C₁ := C)
    (C₂ := 0) hA hB hC cmDiff_zeroField hD hf (contMDiff_const (c := (0 : ℝ)))
  simpa only [smul_zero, add_zero, zero_mul] using h

/-- The additivity special case of `fth_dRmPhi_linear`. -/
theorem fth_dRmPhi_add (hLC : LCSmooth I M)
    {A B C₁ C₂ D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC₁ : CMDiff ∞ (T% C₁)) (hC₂ : CMDiff ∞ (T% C₂)) (hD : CMDiff ∞ (T% D)) :
    dRmPhi g x v A B (C₁ + C₂) D = dRmPhi g x v A B C₁ D + dRmPhi g x v A B C₂ D := by
  have h := fth_dRmPhi_linear (g := g) (x := x) (v := v) hLC hA hB hC₁ hC₂ hD
    (f₁ := (1 : M → ℝ)) (f₂ := (1 : M → ℝ))
    (contMDiff_const (c := (1 : ℝ))) (contMDiff_const (c := (1 : ℝ)))
  rw [show (1 : M → ℝ) • C₁ = C₁ from by funext y; simp,
    show (1 : M → ℝ) • C₂ = C₂ from by funext y; simp] at h
  simpa using h

/-! ## Dependence on the germ and on the value at `x` -/

/-- `dRmPhi` only depends on the germ of its third argument. -/
theorem fth_dRmPhi_germ (hLC : LCSmooth I M)
    {A B C C' D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hC' : CMDiff ∞ (T% C')) (hD : CMDiff ∞ (T% D))
    (heq : C =ᶠ[𝓝 x] C') :
    dRmPhi g x v A B C D = dRmPhi g x v A B C' D := by
  have hev : (fun y : M => rmP g y (A y) (B y) (C y) (D y))
      =ᶠ[𝓝 x] (fun y : M => rmP g y (A y) (B y) (C' y) (D y)) := by
    filter_upwards [heq] with y hy
    rw [hy]
  have h1 : mvfderiv I (fun y : M => rmP g y (A y) (B y) (C y) (D y)) x
      = mvfderiv I (fun y : M => rmP g y (A y) (B y) (C' y) (D y)) x :=
    mvfderiv_congr_eventuallyEq (I := I) hev
  have h2 : (lcOf g) C x = (lcOf g) C' x :=
    (lcOf g).isCovariantDerivativeOn.congr_of_eventuallyEq (hC.mdifferentiableAt (by simp))
      (hC'.mdifferentiableAt (by simp)) Filter.univ_mem heq
  have h3 : C x = C' x := heq.self_of_nhds
  simp only [dRmPhi]
  rw [h1, h2, h3]

/-- The finite-sum form of the linearity in the third slot. -/
theorem fth_dRmPhi_sum (hLC : LCSmooth I M) {ι : Type*} (s : Finset ι)
    (f : ι → M → ℝ) (C : ι → Π y : M, TangentSpace I y)
    (hf : ∀ i, CMDiff ∞ (f i)) (hC : ∀ i, CMDiff ∞ (T% (C i)))
    {A B D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hD : CMDiff ∞ (T% D)) :
    dRmPhi g x v A B (∑ i ∈ s, f i • C i) D
      = ∑ i ∈ s, f i x * dRmPhi g x v A B (C i) D := by
  classical
  have hsum : ∀ t : Finset ι, CMDiff ∞ (T% (∑ i ∈ t, f i • C i)) :=
    fun t => cmDiff_sum_smul (I := I) t f C hf hC
  induction s using Finset.induction_on with
  | empty =>
      have hzero : dRmPhi g x v A B (0 : Π y : M, TangentSpace I y) D = 0 := by
        have h := fth_dRmPhi_smul (g := g) (x := x) (v := v) hLC
          (A := A) (B := B) (C := (0 : Π y : M, TangentSpace I y)) hA hB
          (cmDiff_zeroField (I := I) (M := M)) hD
          (f := (0 : M → ℝ)) (contMDiff_const (c := (0 : ℝ)))
        simpa only [smul_zero, Pi.zero_apply, zero_mul] using h
      rw [Finset.sum_empty]
      simpa using hzero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, fth_dRmPhi_add hLC hA hB ((hf i).smul_section (hC i)) (hsum s) hD,
        fth_dRmPhi_smul hLC hA hB (hC i) hD (hf i), ih, Finset.sum_insert hi]

/-- `dRmPhi` vanishes on a third field that vanishes at `x`. -/
theorem fth_dRmPhi_zero (hLC : LCSmooth I M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (hCx : C x = 0) :
    dRmPhi g x v A B C D = 0 := by
  obtain ⟨f, Y, hf, hY, hfx, hdecomp⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero
      (I := I) hC hCx
  have hsumfin : dRmPhi g x v A B (∑ i, f i • Y i) D
      = ∑ i, f i x * dRmPhi g x v A B (Y i) D :=
    fth_dRmPhi_sum (g := g) (x := x) (v := v) hLC Finset.univ f Y
      (fun i => hf i) (fun i => hY i) hA hB hD
  have hsum_smooth : CMDiff ∞ (T% (∑ i, f i • Y i)) :=
    cmDiff_sum_smul (I := I) Finset.univ f Y (fun i => hf i) (fun i => hY i)
  rw [fth_dRmPhi_germ (g := g) (x := x) (v := v) hLC hA hB hC hsum_smooth hD hdecomp,
    hsumfin]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hfx i, zero_mul]

/-- `dRmPhi` depends on its third field only through its value at `x`. -/
theorem fth_dRmPhi_bind (hLC : LCSmooth I M)
    {A B C C' D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hC' : CMDiff ∞ (T% C')) (hD : CMDiff ∞ (T% D))
    (h : C x = C' x) :
    dRmPhi g x v A B C D = dRmPhi g x v A B C' D := by
  have hsub : CMDiff ∞ (T% (C - C')) := hC.sub_section hC'
  have h0 : (C - C') x = 0 := by rw [Pi.sub_apply, h, sub_self]
  have hd : dRmPhi g x v A B (C - C') D = 0 := fth_dRmPhi_zero hLC hA hB hsub hD h0
  have hsplit : C = (C - C') + C' := by funext y; simp
  rw [hsplit, fth_dRmPhi_add hLC hA hB hsub hC' hD, hd, zero_add]

/-! ## The requested statement -/

/-- `covRm` is `ℝ`-linear in its **fourth** argument `c`. -/
theorem covRm_linear_fth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    ∀ (v a b : TangentSpace I x) (r s : ℝ) (c₁ c₂ d : TangentSpace I x),
      covRm g x v a b (r • c₁ + s • c₂) d
        = r * covRm g x v a b c₁ d + s * covRm g x v a b c₂ d := by
  intro v a b r s c₁ c₂ d
  have h1 : CMDiff ∞ (T% (smoothExt x c₁)) := smoothExt_cmdiff x c₁
  have h2 : CMDiff ∞ (T% (smoothExt x c₂)) := smoothExt_cmdiff x c₂
  have h3 : CMDiff ∞ (T% (smoothExt x a)) := smoothExt_cmdiff x a
  have h4 : CMDiff ∞ (T% (smoothExt x b)) := smoothExt_cmdiff x b
  have h5 : CMDiff ∞ (T% (smoothExt x d)) := smoothExt_cmdiff x d
  have h6 : CMDiff ∞ (T% ((fun _ : M => r) • smoothExt x c₁ + (fun _ : M => s) • smoothExt x c₂)) :=
    ((contMDiff_const (c := r)).smul_section h1).add_section
      ((contMDiff_const (c := s)).smul_section h2)
  have hsum : smoothExt x (r • c₁ + s • c₂) x
      = ((fun _ : M => r) • smoothExt x c₁ + (fun _ : M => s) • smoothExt x c₂) x := by
    rw [show ((fun _ : M => r) • smoothExt x c₁ + (fun _ : M => s) • smoothExt x c₂) x
        = r • smoothExt x c₁ x + s • smoothExt x c₂ x from rfl,
      smoothExt_apply x (r • c₁ + s • c₂), smoothExt_apply x c₁, smoothExt_apply x c₂]
  have hbind := fth_dRmPhi_bind (g := g) (x := x) (v := v) hLC h3 h4
    (smoothExt_cmdiff x (r • c₁ + s • c₂)) h6 h5 hsum
  have hlin := fth_dRmPhi_linear (g := g) (x := x) (v := v) hLC h3 h4 h1 h2 h5
    (contMDiff_const (c := r)) (contMDiff_const (c := s))
  have hcov1 := covRm_eq_dRmPhi (g := g) (x := x) (v := v) (a := a) (b := b)
    (c := r • c₁ + s • c₂) (d := d)
  have hcov2 := covRm_eq_dRmPhi (g := g) (x := x) (v := v) (a := a) (b := b) (c := c₁) (d := d)
  have hcov3 := covRm_eq_dRmPhi (g := g) (x := x) (v := v) (a := a) (b := b) (c := c₂) (d := d)
  rw [hcov1, hbind, hlin, hcov2, hcov3]

end Work.Diff.GE
