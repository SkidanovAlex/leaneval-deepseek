import Mathlib
import Submission.Work.Diff.GE.dRmPhi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Multilinearity of `dRmPhi` in its first field slot

`dRmPhi g x v A B C D` is the `C^∞(M)`-multilinear operation on sections (of the tangent bundle)
whose value on the chosen extensions `smoothExt x ·` is the frozen `covRm g x v a b c d`
(`covRm_eq_dRmPhi`).  This module proves that it is `C^∞(M)`-linear in its **first** field slot and
that it only depends on the *value* of that field at `x`:

* `dRmPhi_linear_fst`, `dRmPhi_add_fst`, `dRmPhi_smul_fst`;
* `dRmPhi_germ_fst`: the value is unchanged if the first field is changed away from `x`;
* `dRmPhi_sum_fst`: the finite-sum form of the linearity;
* `dRmPhi_zero_fst`, `dRmPhi_bind_fst`: the value depends only on `A x`;
* `covRm_linear_snd`: the resulting multilinearity of the *frozen* `covRm` in its second argument
  (`a`).

The same proof pattern, with `rmP`'s other slots (`rmP_add_fst` → `rmP_add_snd`, `rmP_add_thd`,
`rmP_add_fth`, and the corresponding arguments of `rmP_fields_smooth`) gives the analogous
statements for the third, fourth and fifth arguments of `covRm`.
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

/-- The zero tangent field is smooth. -/
theorem cmDiff_zeroField : CMDiff ∞ (T% (0 : Π y : M, TangentSpace I y)) :=
  contMDiff_zeroSection ℝ (TangentSpace I (M := M))

/-- A finite sum of smooth fields with smooth real coefficients is a smooth field. -/
theorem cmDiff_sum_smul {ι : Type*} (s : Finset ι) (f : ι → M → ℝ)
    (A : ι → Π y : M, TangentSpace I y)
    (hf : ∀ i, CMDiff ∞ (f i)) (hA : ∀ i, CMDiff ∞ (T% (A i))) :
    CMDiff ∞ (T% (∑ i ∈ s, f i • A i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cmDiff_zeroField (I := I) (M := M)
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact ((hf i).smul_section (hA i)).add_section ih

/-! ## The main computation -/

/-- `dRmPhi` is `ℝ`-linear (in fact `C^∞(M)`-linear) in its first field slot. -/
theorem dRmPhi_linear_fst (hLC : LCSmooth I M)
    {A₁ A₂ B C D : Π y : M, TangentSpace I y}
    (hA₁ : CMDiff ∞ (T% A₁)) (hA₂ : CMDiff ∞ (T% A₂))
    (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    {f₁ f₂ : M → ℝ} (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    dRmPhi g x v (f₁ • A₁ + f₂ • A₂) B C D
      = f₁ x * dRmPhi g x v A₁ B C D + f₂ x * dRmPhi g x v A₂ B C D := by
  have hF₁c : CMDiff ∞ (fun y : M => rmP g y (A₁ y) (B y) (C y) (D y)) :=
    rmP_fields_smooth hLC g hA₁ hB hC hD
  have hF₂c : CMDiff ∞ (fun y : M => rmP g y (A₂ y) (B y) (C y) (D y)) :=
    rmP_fields_smooth hLC g hA₂ hB hC hD
  have hF₁d : MDiffAt (fun y : M => rmP g y (A₁ y) (B y) (C y) (D y)) x :=
    hF₁c.mdifferentiableAt (by simp)
  have hF₂d : MDiffAt (fun y : M => rmP g y (A₂ y) (B y) (C y) (D y)) x :=
    hF₂c.mdifferentiableAt (by simp)
  have hf₁d : MDiffAt f₁ x := hf₁.mdifferentiableAt (by simp)
  have hf₂d : MDiffAt f₂ x := hf₂.mdifferentiableAt (by simp)
  -- the integrand: `rmP` of a sum of scaled fields is the sum of the scaled `rmP`s
  have hint : (fun y : M => rmP g y ((f₁ • A₁ + f₂ • A₂) y) (B y) (C y) (D y))
      = f₁ * (fun y : M => rmP g y (A₁ y) (B y) (C y) (D y))
        + f₂ * (fun y : M => rmP g y (A₂ y) (B y) (C y) (D y)) := by
    funext y
    rw [show (f₁ • A₁ + f₂ • A₂) y = f₁ y • A₁ y + f₂ y • A₂ y from rfl]
    simp only [rmP_add_fst g hLC, rmP_smul_fst g hLC]
    rfl
  have hderiv : mvfderiv I (fun y : M => rmP g y ((f₁ • A₁ + f₂ • A₂) y) (B y) (C y) (D y)) x v
      = (f₁ x * mvfderiv I (fun y : M => rmP g y (A₁ y) (B y) (C y) (D y)) x v
          + mvfderiv I f₁ x v * rmP g x (A₁ x) (B x) (C x) (D x))
        + (f₂ x * mvfderiv I (fun y : M => rmP g y (A₂ y) (B y) (C y) (D y)) x v
          + mvfderiv I f₂ x v * rmP g x (A₂ x) (B x) (C x) (D x)) := by
    rw [hint, mvfderiv_add (hf₁d.mul hF₁d) (hf₂d.mul hF₂d),
      mvfderiv_mul (f := f₁) (g := fun y : M => rmP g y (A₁ y) (B y) (C y) (D y)) hf₁d hF₁d,
      mvfderiv_mul (f := f₂) (g := fun y : M => rmP g y (A₂ y) (B y) (C y) (D y)) hf₂d hF₂d]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  -- the connection: additivity and Leibniz in the first slot
  have hfA₁ : CMDiff ∞ (T% (f₁ • A₁)) := hf₁.smul_section hA₁
  have hfA₂ : CMDiff ∞ (T% (f₂ • A₂)) := hf₂.smul_section hA₂
  have hconnv : (lcOf g) (f₁ • A₁ + f₂ • A₂) x v
      = (lcOf g) (f₁ • A₁) x v + (lcOf g) (f₂ • A₂) x v := by
    have h := (lcOf g).isCovariantDerivativeOn.add (hfA₁.mdifferentiableAt (by simp))
      (hfA₂.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) h, add_apply]
  have hlei₁ : (lcOf g) (f₁ • A₁) x v = f₁ x • (lcOf g) A₁ x v + mvfderiv I f₁ x v • A₁ x := by
    have h := (lcOf g).isCovariantDerivativeOn.leibniz (σ := A₁) (g := f₁)
      (hA₁.mdifferentiableAt (by simp)) (hf₁.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) h, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  have hlei₂ : (lcOf g) (f₂ • A₂) x v = f₂ x • (lcOf g) A₂ x v + mvfderiv I f₂ x v • A₂ x := by
    have h := (lcOf g).isCovariantDerivativeOn.leibniz (σ := A₂) (g := f₂)
      (hA₂.mdifferentiableAt (by simp)) (hf₂.mdifferentiableAt (by simp))
    rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) h, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  -- the four correction terms
  have hcx : (f₁ • A₁ + f₂ • A₂) x = f₁ x • A₁ x + f₂ x • A₂ x := rfl
  have hc₁ : rmP g x ((lcOf g) (f₁ • A₁ + f₂ • A₂) x v) (B x) (C x) (D x)
      = f₁ x * rmP g x ((lcOf g) A₁ x v) (B x) (C x) (D x)
        + mvfderiv I f₁ x v * rmP g x (A₁ x) (B x) (C x) (D x)
        + (f₂ x * rmP g x ((lcOf g) A₂ x v) (B x) (C x) (D x)
          + mvfderiv I f₂ x v * rmP g x (A₂ x) (B x) (C x) (D x)) := by
    rw [hconnv, hlei₁, hlei₂]
    simp only [rmP_add_fst g hLC, rmP_smul_fst g hLC]
  have hc₂ : rmP g x ((f₁ • A₁ + f₂ • A₂) x) ((lcOf g) B x v) (C x) (D x)
      = f₁ x * rmP g x (A₁ x) ((lcOf g) B x v) (C x) (D x)
        + f₂ x * rmP g x (A₂ x) ((lcOf g) B x v) (C x) (D x) := by
    rw [hcx]
    simp only [rmP_add_fst g hLC, rmP_smul_fst g hLC]
  have hc₃ : rmP g x ((f₁ • A₁ + f₂ • A₂) x) (B x) ((lcOf g) C x v) (D x)
      = f₁ x * rmP g x (A₁ x) (B x) ((lcOf g) C x v) (D x)
        + f₂ x * rmP g x (A₂ x) (B x) ((lcOf g) C x v) (D x) := by
    rw [hcx]
    simp only [rmP_add_fst g hLC, rmP_smul_fst g hLC]
  have hc₄ : rmP g x ((f₁ • A₁ + f₂ • A₂) x) (B x) (C x) ((lcOf g) D x v)
      = f₁ x * rmP g x (A₁ x) (B x) (C x) ((lcOf g) D x v)
        + f₂ x * rmP g x (A₂ x) (B x) (C x) ((lcOf g) D x v) := by
    rw [hcx]
    simp only [rmP_add_fst g hLC, rmP_smul_fst g hLC]
  simp only [dRmPhi]
  rw [hderiv, hc₁, hc₂, hc₃, hc₄]
  ring

/-- The homogeneity special case of `dRmPhi_linear_fst`. -/
theorem dRmPhi_smul_fst (hLC : LCSmooth I M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    {f : M → ℝ} (hf : CMDiff ∞ f) :
    dRmPhi g x v (f • A) B C D = f x * dRmPhi g x v A B C D := by
  have h := dRmPhi_linear_fst (g := g) (x := x) (v := v) hLC (A₁ := A) (A₂ := 0)
    hA cmDiff_zeroField hB hC hD hf (contMDiff_const (c := (0 : ℝ)))
  simpa only [smul_zero, add_zero, zero_mul] using h

/-- The additivity special case of `dRmPhi_linear_fst`. -/
theorem dRmPhi_add_fst (hLC : LCSmooth I M)
    {A₁ A₂ B C D : Π y : M, TangentSpace I y}
    (hA₁ : CMDiff ∞ (T% A₁)) (hA₂ : CMDiff ∞ (T% A₂))
    (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    dRmPhi g x v (A₁ + A₂) B C D = dRmPhi g x v A₁ B C D + dRmPhi g x v A₂ B C D := by
  have h := dRmPhi_linear_fst (g := g) (x := x) (v := v) hLC hA₁ hA₂ hB hC hD
    (f₁ := (1 : M → ℝ)) (f₂ := (1 : M → ℝ))
    (contMDiff_const (c := (1 : ℝ))) (contMDiff_const (c := (1 : ℝ)))
  rw [show (1 : M → ℝ) • A₁ = A₁ from by funext y; simp,
    show (1 : M → ℝ) • A₂ = A₂ from by funext y; simp] at h
  simpa using h

/-! ## Dependence on the germ and on the value at `x` -/

/-- `dRmPhi` only depends on the germ of its first argument. -/
theorem dRmPhi_germ_fst (hLC : LCSmooth I M)
    {A A' B C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hA' : CMDiff ∞ (T% A'))
    (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (heq : A =ᶠ[𝓝 x] A') :
    dRmPhi g x v A B C D = dRmPhi g x v A' B C D := by
  have hev : (fun y : M => rmP g y (A y) (B y) (C y) (D y))
      =ᶠ[𝓝 x] (fun y : M => rmP g y (A' y) (B y) (C y) (D y)) := by
    filter_upwards [heq] with y hy
    rw [hy]
  have h1 : mvfderiv I (fun y : M => rmP g y (A y) (B y) (C y) (D y)) x
      = mvfderiv I (fun y : M => rmP g y (A' y) (B y) (C y) (D y)) x :=
    mvfderiv_congr_eventuallyEq (I := I) hev
  have h2 : (lcOf g) A x = (lcOf g) A' x :=
    (lcOf g).isCovariantDerivativeOn.congr_of_eventuallyEq (hA.mdifferentiableAt (by simp))
      (hA'.mdifferentiableAt (by simp)) Filter.univ_mem heq
  have h3 : A x = A' x := heq.self_of_nhds
  simp only [dRmPhi]
  rw [h1, h2, h3]

/-- The finite-sum form of the linearity in the first slot. -/
theorem dRmPhi_sum_fst (hLC : LCSmooth I M) {ι : Type*} (s : Finset ι)
    (f : ι → M → ℝ) (A : ι → Π y : M, TangentSpace I y)
    (hf : ∀ i, CMDiff ∞ (f i)) (hA : ∀ i, CMDiff ∞ (T% (A i)))
    {B C D : Π y : M, TangentSpace I y}
    (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    dRmPhi g x v (∑ i ∈ s, f i • A i) B C D
      = ∑ i ∈ s, f i x * dRmPhi g x v (A i) B C D := by
  classical
  have hsum : ∀ t : Finset ι, CMDiff ∞ (T% (∑ i ∈ t, f i • A i)) :=
    fun t => cmDiff_sum_smul (I := I) t f A hf hA
  induction s using Finset.induction_on with
  | empty =>
      have hzero : dRmPhi g x v (0 : Π y : M, TangentSpace I y) B C D = 0 := by
        have h := dRmPhi_smul_fst (g := g) (x := x) (v := v) hLC
          (A := (0 : Π y : M, TangentSpace I y)) (cmDiff_zeroField (I := I) (M := M)) hB hC hD
          (f := (0 : M → ℝ)) (contMDiff_const (c := (0 : ℝ)))
        simpa only [smul_zero, Pi.zero_apply, zero_mul] using h
      rw [Finset.sum_empty]
      simpa using hzero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, dRmPhi_add_fst hLC ((hf i).smul_section (hA i)) (hsum s) hB hC hD,
        dRmPhi_smul_fst hLC (hA i) hB hC hD (hf i), ih, Finset.sum_insert hi]

/-- `dRmPhi` vanishes on a first field that vanishes at `x`. -/
theorem dRmPhi_zero_fst (hLC : LCSmooth I M)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (hAx : A x = 0) :
    dRmPhi g x v A B C D = 0 := by
  obtain ⟨f, Y, hf, hY, hfx, hdecomp⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero
      (I := I) hA hAx
  have hsumfin : dRmPhi g x v (∑ i, f i • Y i) B C D
      = ∑ i, f i x * dRmPhi g x v (Y i) B C D :=
    dRmPhi_sum_fst (g := g) (x := x) (v := v) hLC Finset.univ f Y
      (fun i => hf i) (fun i => hY i) hB hC hD
  have hsum_smooth : CMDiff ∞ (T% (∑ i, f i • Y i)) :=
    cmDiff_sum_smul (I := I) Finset.univ f Y (fun i => hf i) (fun i => hY i)
  rw [dRmPhi_germ_fst (g := g) (x := x) (v := v) hLC hA hsum_smooth hB hC hD hdecomp,
    hsumfin]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hfx i, zero_mul]

/-- `dRmPhi` depends on its first field only through its value at `x`. -/
theorem dRmPhi_bind_fst (hLC : LCSmooth I M)
    {A A' B C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hA' : CMDiff ∞ (T% A'))
    (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D))
    (h : A x = A' x) :
    dRmPhi g x v A B C D = dRmPhi g x v A' B C D := by
  have hsub : CMDiff ∞ (T% (A - A')) := hA.sub_section hA'
  have h0 : (A - A') x = 0 := by rw [Pi.sub_apply, h, sub_self]
  have hd : dRmPhi g x v (A - A') B C D = 0 := dRmPhi_zero_fst hLC hsub hB hC hD h0
  have hsplit : A = (A - A') + A' := by funext y; simp
  rw [hsplit, dRmPhi_add_fst hLC hsub hA' hB hC hD, hd, zero_add]

/-! ## Multilinearity of the frozen `covRm` in its second argument -/

/-- `covRm` is `ℝ`-linear in its second argument `a`. -/
theorem covRm_linear_snd (hLC : LCSmooth I M) (g : SMet I M) (x : M) :
    ∀ (v : TangentSpace I x) (r s : ℝ) (a₁ a₂ b c d : TangentSpace I x),
      covRm g x v (r • a₁ + s • a₂) b c d
        = r * covRm g x v a₁ b c d + s * covRm g x v a₂ b c d := by
  intro v r s a₁ a₂ b c d
  have h1 : CMDiff ∞ (T% (smoothExt x a₁)) := smoothExt_cmdiff x a₁
  have h2 : CMDiff ∞ (T% (smoothExt x a₂)) := smoothExt_cmdiff x a₂
  have h3 : CMDiff ∞ (T% (smoothExt x b)) := smoothExt_cmdiff x b
  have h4 : CMDiff ∞ (T% (smoothExt x c)) := smoothExt_cmdiff x c
  have h5 : CMDiff ∞ (T% (smoothExt x d)) := smoothExt_cmdiff x d
  have h6 : CMDiff ∞ (T% ((fun _ : M => r) • smoothExt x a₁ + (fun _ : M => s) • smoothExt x a₂)) :=
    ((contMDiff_const (c := r)).smul_section h1).add_section
      ((contMDiff_const (c := s)).smul_section h2)
  have hsum : smoothExt x (r • a₁ + s • a₂) x
      = ((fun _ : M => r) • smoothExt x a₁ + (fun _ : M => s) • smoothExt x a₂) x := by
    rw [show ((fun _ : M => r) • smoothExt x a₁ + (fun _ : M => s) • smoothExt x a₂) x
        = r • smoothExt x a₁ x + s • smoothExt x a₂ x from rfl,
      smoothExt_apply x (r • a₁ + s • a₂), smoothExt_apply x a₁, smoothExt_apply x a₂]
  have hbind := dRmPhi_bind_fst (g := g) (x := x) (v := v) hLC
    (smoothExt_cmdiff x (r • a₁ + s • a₂)) h6 h3 h4 h5 hsum
  have hlin := dRmPhi_linear_fst (g := g) (x := x) (v := v) hLC h1 h2 h3 h4 h5
    (contMDiff_const (c := r)) (contMDiff_const (c := s))
  have hcov1 := covRm_eq_dRmPhi (g := g) (x := x) (v := v) (a := r • a₁ + s • a₂)
    (b := b) (c := c) (d := d)
  have hcov2 := covRm_eq_dRmPhi (g := g) (x := x) (v := v) (a := a₁) (b := b) (c := c) (d := d)
  have hcov3 := covRm_eq_dRmPhi (g := g) (x := x) (v := v) (a := a₂) (b := b) (c := c) (d := d)
  rw [hcov1, hbind, hlin, hcov2, hcov3]

end Work.Diff.GE
