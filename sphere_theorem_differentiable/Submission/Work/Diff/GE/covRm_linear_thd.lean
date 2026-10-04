import Mathlib
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.dRmPhi_slotA

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Multilinearity of `dRmPhi` in its second field slot

`dRmPhi g x v A B C D` is the `C^∞(M)`-multilinear operation on sections (of the tangent bundle)
whose value on the chosen extensions `smoothExt x ·` is the frozen `covRm g x v a b c d`
(`covRm_eq_dRmPhi`).  This module proves that it is `C^∞(M)`-linear in its **second** field slot and
that it only depends on the *value* of that field at `x`:

* `dRmPhi_linear_slotB`, `dRmPhi_add_slotB`, `dRmPhi_smul_slotB`;
* `dRmPhi_germ_slotB`: the value is unchanged if the second field is changed away from `x`;
* `dRmPhi_sum_slotB`: the finite-sum form of the linearity;
* `dRmPhi_zero_slotB`, `dRmPhi_bind_slotB`: the value depends only on `B x`;
* `covRm_linear_thd`: the resulting multilinearity of the *frozen* `covRm` in its third argument
  (`b`).

This is the exact analogue of `dRmPhi_slotA.lean` for the first slot: the field `B` occurs in the
integrand `rmP g y (A y) (B y) (C y) (D y)` as the second argument of `rmP` (so the relevant
algebra is `rmP_add_snd`, `rmP_smul_snd`) and in the correction terms as `lcOf g B x v` in the
second correction and as `B x` in the other three.  `rmP_fields_smooth` is unchanged.
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

/-! ## The main computation -/

/-- `dRmPhi` is `ℝ`-linear (in fact `C^∞(M)`-linear) in its second field slot. -/
theorem dRmPhi_linear_slotB (hLC : LCSmooth I M)
    {A B₁ B₂ C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB₁ : CMDiff ∞ (T% B₁)) (hB₂ : CMDiff ∞ (T% B₂))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    {f₁ f₂ : M → ℝ} (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    dRmPhi g x v A (f₁ • B₁ + f₂ • B₂) C D
      = f₁ x * dRmPhi g x v A B₁ C D + f₂ x * dRmPhi g x v A B₂ C D := by
  have hF₁c : CMDiff ∞ (fun y : M => rmP g y (A y) (B₁ y) (C y) (D y)) :=
    rmP_fields_smooth hLC g hA hB₁ hC hD
  have hF₂c : CMDiff ∞ (fun y : M => rmP g y (A y) (B₂ y) (C y) (D y)) :=
    rmP_fields_smooth hLC g hA hB₂ hC hD
  have hF₁d : MDiffAt (fun y : M => rmP g y (A y) (B₁ y) (C y) (D y)) x :=
    hF₁c.mdifferentiableAt (by simp)
  have hF₂d : MDiffAt (fun y : M => rmP g y (A y) (B₂ y) (C y) (D y)) x :=
    hF₂c.mdifferentiableAt (by simp)
  have hf₁d : MDiffAt f₁ x := hf₁.mdifferentiableAt (by simp)
  have hf₂d : MDiffAt f₂ x := hf₂.mdifferentiableAt (by simp)
  -- the integrand: `rmP` of a sum of scaled fields is the sum of the scaled `rmP`s
  have hint : (fun y : M => rmP g y (A y) ((f₁ • B₁ + f₂ • B₂) y) (C y) (D y))
      = f₁ * (fun y : M => rmP g y (A y) (B₁ y) (C y) (D y))
        + f₂ * (fun y : M => rmP g y (A y) (B₂ y) (C y) (D y)) := by
    funext y
    rw [show (f₁ • B₁ + f₂ • B₂) y = f₁ y • B₁ y + f₂ y • B₂ y from rfl]
    simp only [rmP_add_snd g hLC, rmP_smul_snd g hLC]
    rfl
  have hderiv : mvfderiv I (fun y : M => rmP g y (A y) ((f₁ • B₁ + f₂ • B₂) y) (C y) (D y)) x v
      = (f₁ x * mvfderiv I (fun y : M => rmP g y (A y) (B₁ y) (C y) (D y)) x v
          + mvfderiv I f₁ x v * rmP g x (A x) (B₁ x) (C x) (D x))
        + (f₂ x * mvfderiv I (fun y : M => rmP g y (A y) (B₂ y) (C y) (D y)) x v
          + mvfderiv I f₂ x v * rmP g x (A x) (B₂ x) (C x) (D x)) := by
    rw [hint, mvfderiv_add (hf₁d.mul hF₁d) (hf₂d.mul hF₂d),
      mvfderiv_mul (f := f₁) (g := fun y : M => rmP g y (A y) (B₁ y) (C y) (D y)) hf₁d hF₁d,
      mvfderiv_mul (f := f₂) (g := fun y : M => rmP g y (A y) (B₂ y) (C y) (D y)) hf₂d hF₂d]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  -- the connection: additivity and Leibniz in the second slot
  have hfB₁ : CMDiff ∞ (T% (f₁ • B₁)) := hf₁.smul_section hB₁
  have hfB₂ : CMDiff ∞ (T% (f₂ • B₂)) := hf₂.smul_section hB₂
  have hconnv : (lcOf g) (f₁ • B₁ + f₂ • B₂) x v
      = (lcOf g) (f₁ • B₁) x v + (lcOf g) (f₂ • B₂) x v := by
    have h := (lcOf g).isCovariantDerivativeOn.add (hfB₁.mdifferentiableAt (by simp))
      (hfB₂.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) h, add_apply]
  have hlei₁ : (lcOf g) (f₁ • B₁) x v = f₁ x • (lcOf g) B₁ x v + mvfderiv I f₁ x v • B₁ x := by
    have h := (lcOf g).isCovariantDerivativeOn.leibniz (σ := B₁) (g := f₁)
      (hB₁.mdifferentiableAt (by simp)) (hf₁.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) h, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  have hlei₂ : (lcOf g) (f₂ • B₂) x v = f₂ x • (lcOf g) B₂ x v + mvfderiv I f₂ x v • B₂ x := by
    have h := (lcOf g).isCovariantDerivativeOn.leibniz (σ := B₂) (g := f₂)
      (hB₂.mdifferentiableAt (by simp)) (hf₂.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) h, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  -- the four correction terms
  have hcx : (f₁ • B₁ + f₂ • B₂) x = f₁ x • B₁ x + f₂ x • B₂ x := rfl
  have hc₁ : rmP g x ((lcOf g) A x v) ((f₁ • B₁ + f₂ • B₂) x) (C x) (D x)
      = f₁ x * rmP g x ((lcOf g) A x v) (B₁ x) (C x) (D x)
        + f₂ x * rmP g x ((lcOf g) A x v) (B₂ x) (C x) (D x) := by
    rw [hcx]
    simp only [rmP_add_snd g hLC, rmP_smul_snd g hLC]
  have hc₂ : rmP g x (A x) ((lcOf g) (f₁ • B₁ + f₂ • B₂) x v) (C x) (D x)
      = f₁ x * rmP g x (A x) ((lcOf g) B₁ x v) (C x) (D x)
        + mvfderiv I f₁ x v * rmP g x (A x) (B₁ x) (C x) (D x)
        + (f₂ x * rmP g x (A x) ((lcOf g) B₂ x v) (C x) (D x)
          + mvfderiv I f₂ x v * rmP g x (A x) (B₂ x) (C x) (D x)) := by
    rw [hconnv, hlei₁, hlei₂]
    simp only [rmP_add_snd g hLC, rmP_smul_snd g hLC]
  have hc₃ : rmP g x (A x) ((f₁ • B₁ + f₂ • B₂) x) ((lcOf g) C x v) (D x)
      = f₁ x * rmP g x (A x) (B₁ x) ((lcOf g) C x v) (D x)
        + f₂ x * rmP g x (A x) (B₂ x) ((lcOf g) C x v) (D x) := by
    rw [hcx]
    simp only [rmP_add_snd g hLC, rmP_smul_snd g hLC]
  have hc₄ : rmP g x (A x) ((f₁ • B₁ + f₂ • B₂) x) (C x) ((lcOf g) D x v)
      = f₁ x * rmP g x (A x) (B₁ x) (C x) ((lcOf g) D x v)
        + f₂ x * rmP g x (A x) (B₂ x) (C x) ((lcOf g) D x v) := by
    rw [hcx]
    simp only [rmP_add_snd g hLC, rmP_smul_snd g hLC]
  simp only [dRmPhi]
  rw [hderiv, hc₂, hc₃, hc₄, hc₁]
  ring

/-- The homogeneity special case of `dRmPhi_linear_slotB`. -/
theorem dRmPhi_smul_slotB (hLC : LCSmooth I M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    {f : M → ℝ} (hf : CMDiff ∞ f) :
    dRmPhi g x v A (f • B) C D = f x * dRmPhi g x v A B C D := by
  have h := dRmPhi_linear_slotB (g := g) (x := x) (v := v) hLC (A := A) (B₁ := B) (B₂ := 0)
    hA hB cmDiff_zeroField hC hD hf (contMDiff_const (c := (0 : ℝ)))
  simpa only [smul_zero, add_zero, zero_mul] using h

/-- The additivity special case of `dRmPhi_linear_slotB`. -/
theorem dRmPhi_add_slotB (hLC : LCSmooth I M)
    {A B₁ B₂ C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB₁ : CMDiff ∞ (T% B₁)) (hB₂ : CMDiff ∞ (T% B₂))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    dRmPhi g x v A (B₁ + B₂) C D = dRmPhi g x v A B₁ C D + dRmPhi g x v A B₂ C D := by
  have h := dRmPhi_linear_slotB (g := g) (x := x) (v := v) hLC hA hB₁ hB₂ hC hD
    (f₁ := (1 : M → ℝ)) (f₂ := (1 : M → ℝ))
    (contMDiff_const (c := (1 : ℝ))) (contMDiff_const (c := (1 : ℝ)))
  rw [show (1 : M → ℝ) • B₁ = B₁ from by funext y; simp,
    show (1 : M → ℝ) • B₂ = B₂ from by funext y; simp] at h
  simpa using h

/-! ## Dependence on the germ and on the value at `x` -/

/-- `dRmPhi` only depends on the germ of its second argument. -/
theorem dRmPhi_germ_slotB (hLC : LCSmooth I M)
    {A B B' C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hB' : CMDiff ∞ (T% B'))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (heq : B =ᶠ[𝓝 x] B') :
    dRmPhi g x v A B C D = dRmPhi g x v A B' C D := by
  have hev : (fun y : M => rmP g y (A y) (B y) (C y) (D y))
      =ᶠ[𝓝 x] (fun y : M => rmP g y (A y) (B' y) (C y) (D y)) := by
    filter_upwards [heq] with y hy
    rw [hy]
  have h1 : mvfderiv I (fun y : M => rmP g y (A y) (B y) (C y) (D y)) x
      = mvfderiv I (fun y : M => rmP g y (A y) (B' y) (C y) (D y)) x :=
    mvfderiv_congr_eventuallyEq (I := I) hev
  have h2 : (lcOf g) B x = (lcOf g) B' x :=
    (lcOf g).isCovariantDerivativeOn.congr_of_eventuallyEq (hB.mdifferentiableAt (by simp))
      (hB'.mdifferentiableAt (by simp)) Filter.univ_mem heq
  have h3 : B x = B' x := heq.self_of_nhds
  simp only [dRmPhi]
  rw [h1, h2, h3]

/-- The finite-sum form of the linearity in the second slot. -/
theorem dRmPhi_sum_slotB (hLC : LCSmooth I M) {ι : Type*} (s : Finset ι)
    (f : ι → M → ℝ) (B : ι → Π y : M, TangentSpace I y)
    (hf : ∀ i, CMDiff ∞ (f i)) (hB : ∀ i, CMDiff ∞ (T% (B i)))
    {A C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    dRmPhi g x v A (∑ i ∈ s, f i • B i) C D
      = ∑ i ∈ s, f i x * dRmPhi g x v A (B i) C D := by
  classical
  have hsum : ∀ t : Finset ι, CMDiff ∞ (T% (∑ i ∈ t, f i • B i)) :=
    fun t => cmDiff_sum_smul (I := I) t f B hf hB
  induction s using Finset.induction_on with
  | empty =>
      have hzero : dRmPhi g x v A (0 : Π y : M, TangentSpace I y) C D = 0 := by
        have h := dRmPhi_smul_slotB (g := g) (x := x) (v := v) hLC
          (B := (0 : Π y : M, TangentSpace I y)) hA (cmDiff_zeroField (I := I) (M := M)) hC hD
          (f := (0 : M → ℝ)) (contMDiff_const (c := (0 : ℝ)))
        simpa only [smul_zero, Pi.zero_apply, zero_mul] using h
      rw [Finset.sum_empty]
      simpa using hzero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, dRmPhi_add_slotB hLC hA ((hf i).smul_section (hB i)) (hsum s)
          hC hD,
        dRmPhi_smul_slotB hLC hA (hB i) hC hD (hf i), ih, Finset.sum_insert hi]

/-- `dRmPhi` vanishes on a second field that vanishes at `x`. -/
theorem dRmPhi_zero_slotB (hLC : LCSmooth I M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (hBx : B x = 0) :
    dRmPhi g x v A B C D = 0 := by
  obtain ⟨f, Y, hf, hY, hfx, hdecomp⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero
      (I := I) hB hBx
  have hsumfin : dRmPhi g x v A (∑ i, f i • Y i) C D
      = ∑ i, f i x * dRmPhi g x v A (Y i) C D :=
    dRmPhi_sum_slotB (g := g) (x := x) (v := v) hLC Finset.univ f Y
      (fun i => hf i) (fun i => hY i) hA hC hD
  have hsum_smooth : CMDiff ∞ (T% (∑ i, f i • Y i)) :=
    cmDiff_sum_smul (I := I) Finset.univ f Y (fun i => hf i) (fun i => hY i)
  rw [dRmPhi_germ_slotB (g := g) (x := x) (v := v) hLC hA hB hsum_smooth hC hD hdecomp,
    hsumfin]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hfx i, zero_mul]

/-- `dRmPhi` depends on its second field only through its value at `x`. -/
theorem dRmPhi_bind_slotB (hLC : LCSmooth I M)
    {A B B' C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hB' : CMDiff ∞ (T% B'))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (h : B x = B' x) :
    dRmPhi g x v A B C D = dRmPhi g x v A B' C D := by
  have hsub : CMDiff ∞ (T% (B - B')) := hB.sub_section hB'
  have h0 : (B - B') x = 0 := by rw [Pi.sub_apply, h, sub_self]
  have hd : dRmPhi g x v A (B - B') C D = 0 := dRmPhi_zero_slotB hLC hA hsub hC hD h0
  have hsplit : B = (B - B') + B' := by funext y; simp
  rw [hsplit, dRmPhi_add_slotB hLC hA hsub hB' hC hD, hd, zero_add]

/-! ## Multilinearity of the frozen `covRm` in its third argument -/

/-- `covRm` is `ℝ`-linear in its **third** argument `b`.

Template: `Submission/Work/Diff/GE/dRmPhi_slotA.lean` proves the corresponding statement for the
second argument (`covRm_linear_snd`), via the operation `dRmPhi g x v A B C D`
(`= covRm g x v a b c d` on the chosen extensions `smoothExt x a` etc., see `covRm_eq_dRmPhi` in
`Submission/Work/Diff/GE/dRmPhi.lean`).  For this slot the same proof applies with `rmP`'s **second**
slot linearity (`rmP_add_snd`, `rmP_smul_snd`, `rmP_sum_snd` from `Work.Diff.GE.dRmPhi`) and with
`rmP_fields_smooth` unchanged: the field `B` occurs in the integrand `rmP g y (A y) (B y) (C y) (D y)`
as the second argument of `rmP`, and in the correction terms as `lcOf g B x v` in the second
correction and as `B x` in the other three. -/
theorem covRm_linear_thd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    ∀ (v a : TangentSpace I x) (r s : ℝ) (b₁ b₂ c d : TangentSpace I x),
      covRm g x v a (r • b₁ + s • b₂) c d
        = r * covRm g x v a b₁ c d + s * covRm g x v a b₂ c d := by
  intro v a r s b₁ b₂ c d
  have h1 : CMDiff ∞ (T% (smoothExt x b₁)) := smoothExt_cmdiff x b₁
  have h2 : CMDiff ∞ (T% (smoothExt x b₂)) := smoothExt_cmdiff x b₂
  have h3 : CMDiff ∞ (T% (smoothExt x a)) := smoothExt_cmdiff x a
  have h4 : CMDiff ∞ (T% (smoothExt x c)) := smoothExt_cmdiff x c
  have h5 : CMDiff ∞ (T% (smoothExt x d)) := smoothExt_cmdiff x d
  have h6 : CMDiff ∞ (T% ((fun _ : M => r) • smoothExt x b₁ + (fun _ : M => s) • smoothExt x b₂)) :=
    ((contMDiff_const (c := r)).smul_section h1).add_section
      ((contMDiff_const (c := s)).smul_section h2)
  have hsum : smoothExt x (r • b₁ + s • b₂) x
      = ((fun _ : M => r) • smoothExt x b₁ + (fun _ : M => s) • smoothExt x b₂) x := by
    rw [show ((fun _ : M => r) • smoothExt x b₁ + (fun _ : M => s) • smoothExt x b₂) x
        = r • smoothExt x b₁ x + s • smoothExt x b₂ x from rfl,
      smoothExt_apply x (r • b₁ + s • b₂), smoothExt_apply x b₁, smoothExt_apply x b₂]
  have hbind := dRmPhi_bind_slotB (g := g) (x := x) (v := v) hLC
    h3 (smoothExt_cmdiff x (r • b₁ + s • b₂)) h6 h4 h5 hsum
  have hlin := dRmPhi_linear_slotB (g := g) (x := x) (v := v) hLC h3 h1 h2 h4 h5
    (contMDiff_const (c := r)) (contMDiff_const (c := s))
  have hcov1 := covRm_eq_dRmPhi (g := g) (x := x) (v := v) (a := a) (b := r • b₁ + s • b₂)
    (c := c) (d := d)
  have hcov2 := covRm_eq_dRmPhi (g := g) (x := x) (v := v) (a := a) (b := b₁) (c := c) (d := d)
  have hcov3 := covRm_eq_dRmPhi (g := g) (x := x) (v := v) (a := a) (b := b₂) (c := c) (d := d)
  rw [hcov1, hbind, hlin, hcov2, hcov3]

end Work.Diff.GE
