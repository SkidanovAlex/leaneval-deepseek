import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Submission.Commons.Analysis.Calculus.FDeriv.kernelField_direction_perp
import Submission.Commons.Analysis.Calculus.FDeriv.kernelFieldMirror_direction_perp
import Submission.PaperBand.Codazzi

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix
open InnerProductGeometry

set_option autoImplicit false
set_option maxHeartbeats 400000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Straightening of the kernel line field (Lemma `mc`, support)

With the Codazzi equations (`Submission.PaperBand.Codazzi`) and the Gauss
(flatness) identity `a c = b²` in hand, the kernel line field of the shape
matrix is *straightening*: writing the kernel vector field as

    w(y) = b(y) • e₀̂ − a(y) • e₁̂      (a = S₀₀, b = S₁₀, c = S₁₁)

we prove the infinitesimal straightness condition
`fderiv w y (w y) ∥ w y` at interior points (the componentwise statement
`a·(dw)₀ + b·(dw)₁ = 0`, which says the directional derivative of `w` along
itself is perpendicular to `(a,b)`, hence parallel to `(b,−a)`).

Then the integral curves of the kernel field are straight, giving the
"unique bend through each point" of Lemma `mc` once combined with a local
flow of the field (Mathlib `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`)
and the kernel-segment lemmas of `Submission.PaperBand.BendSegments`.
-/

noncomputable section
namespace Submission.PaperBand

/-- The basis vector `e₀̂ = (1,0)`. -/
abbrev e0 : ℝ² := !₂[1, 0]

/-- The basis vector `e₁̂ = (0,1)`. -/
abbrev e1 : ℝ² := !₂[0, 1]

/-- The shape-entry functions `a = dNentry · 0 0`, `b = dNentry · 1 0`,
`c = dNentry · 1 1`. -/
abbrev S00f (f : ℝ² → ℝ³) : ℝ² → ℝ := fun y => dNentry f y 0 0
abbrev S10f (f : ℝ² → ℝ³) : ℝ² → ℝ := fun y => dNentry f y 1 0
abbrev S11f (f : ℝ² → ℝ³) : ℝ² → ℝ := fun y => dNentry f y 1 1

/-- The kernel vector field `w(y) = b(y)•e₀̂ − a(y)•e₁̂` (a smooth local
section of `ker (dN f)` wherever `a` and `b` are not both zero). -/
abbrev Wf (f : ℝ² → ℝ³) : ℝ² → ℝ² := fun y =>
  (dNentry f y 1 0) • e0 - (dNentry f y 0 0) • e1

/-- Gauss's equation as a scalar: `a c = b²` for the shape entries
`a = S₀₀, b = S₁₀, c = S₁₁` on the interior. -/
lemma gauss_scalar {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      dNentry f x 0 0 * dNentry f x 1 1 = (dNentry f x 1 0)^2 := by
  intro x hx
  have hd := shapeOperator_det_zero hf x hx
  rw [Matrix.det_fin_two, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply] at hd
  have h01 : dNentry f x 0 1 = dNentry f x 1 0 :=
    shapeOperator_symm hf x hx (0 : Fin 2) (1 : Fin 2)
  rw [h01] at hd
  rw [pow_two]
  nlinarith [hd]

/-- The shape-entry functions are differentiable at interior points. -/
lemma differentiableAt_dNentry₀₀ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, DifferentiableAt ℝ (S00f f) x := by
  intro x hx
  have he : S00f f =ᶠ[𝓝 x] (fun y => inner ℝ
      (fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[1, 0]) (tangent₀ f y)) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    exact dNentry₀₀_eq (f := f) y hy
  exact (DifferentiableAt.inner ℝ (differentiableAt_Ndir₀ hf x hx)
    (differentiableAt_tangent₀ hf x hx)).congr_of_eventuallyEq he

/-- The shape-entry functions are differentiable at interior points. -/
lemma differentiableAt_dNentry₁₀ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, DifferentiableAt ℝ (S10f f) x := by
  intro x hx
  have he : S10f f =ᶠ[𝓝 x] (fun y => inner ℝ
      (fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[0, 1]) (tangent₀ f y)) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    exact dNentry₁₀_eq (f := f) y hy
  exact (DifferentiableAt.inner ℝ (differentiableAt_Ndir₁ hf x hx)
    (differentiableAt_tangent₀ hf x hx)).congr_of_eventuallyEq he

/-- The shape-entry functions are differentiable at interior points. -/
lemma differentiableAt_dNentry₁₁ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, DifferentiableAt ℝ (S11f f) x := by
  intro x hx
  have he : S11f f =ᶠ[𝓝 x] (fun y => inner ℝ
      (fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[0, 1]) (tangent₁ f y)) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    exact dNentry₁₁_eq (f := f) y hy
  exact (DifferentiableAt.inner ℝ (differentiableAt_Ndir₁ hf x hx)
    (differentiableAt_tangent₁ hf x hx)).congr_of_eventuallyEq he

/-- Differentiating Gauss's equation along `e₀̂`:
`c·a_u + a·c_u = 2b·b_u`. -/
lemma gauss_deriv₀ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      dNentry f x 1 1 * (fderiv ℝ (S00f f) x !₂[1, 0]) +
      dNentry f x 0 0 * (fderiv ℝ (S11f f) x !₂[1, 0]) =
      2 * (dNentry f x 1 0) * (fderiv ℝ (S10f f) x !₂[1, 0]) := by
  intro x hx
  let a := S00f f
  let b := S10f f
  let c := S11f f
  have hg : ∀ y ∈ stripInterior, a y * c y = (b y)^2 := by
    intro y hy
    exact gauss_scalar hf y hy
  have he : (fun y : ℝ² => a y * c y) =ᶠ[𝓝 x] (fun y : ℝ² => b y * b y) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    rw [hg y hy]
    rw [pow_two]
  have hda : DifferentiableAt ℝ a x := by simpa [a] using differentiableAt_dNentry₀₀ hf x hx
  have hdb : DifferentiableAt ℝ b x := by simpa [b] using differentiableAt_dNentry₁₀ hf x hx
  have hdc : DifferentiableAt ℝ c x := by simpa [c] using differentiableAt_dNentry₁₁ hf x hx
  have hprodL : fderiv ℝ (fun y : ℝ² => a y * c y) x = (c x) • fderiv ℝ a x + (a x) • fderiv ℝ c x := by
    change fderiv ℝ (a * c) x = (c x) • fderiv ℝ a x + (a x) • fderiv ℝ c x
    rw [fderiv_mul hda hdc]
    rw [add_comm]
  have hprodR : fderiv ℝ (fun y : ℝ² => b y * b y) x = (2 * b x) • fderiv ℝ b x := by
    change fderiv ℝ (b * b) x = (2 * b x) • fderiv ℝ b x
    rw [fderiv_mul hdb hdb]
    rw [← add_smul]
    congr 1
    ring
  have hder : fderiv ℝ (fun y : ℝ² => a y * c y) x = fderiv ℝ (fun y : ℝ² => b y * b y) x :=
    Filter.EventuallyEq.fderiv_eq he
  -- apply both sides to e₀̂:
  have hmain := congrArg (fun L : ℝ² →L[ℝ] ℝ => L !₂[1, 0]) hder
  rw [hprodL, hprodR] at hmain
  -- hmain is the application of the derivative equality to e0; unfold the
  -- scalar multiplications of linear maps to scalar multiplications of reals:
  have hmain' : (dNentry f x 1 1) * (fderiv ℝ (S00f f) x !₂[1, 0]) +
        (dNentry f x 0 0) * (fderiv ℝ (S11f f) x !₂[1, 0]) =
      2 * (dNentry f x 1 0) * (fderiv ℝ (S10f f) x !₂[1, 0]) := by
    simpa [a, b, c, S00f, S10f, S11f] using hmain
  exact hmain'



/-- The shape-entry function `S₀₀` is `C^∞` on the interior of the strip. -/
lemma contDiffOn_S00f {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ContDiffOn ℝ ∞ (S00f f) stripInterior := by
  exact (ContDiffOn.inner ℝ (contDiffOn_fderiv_dirN₀ hf) (contDiffOn_tangent₀ hf)).congr
    (fun y hy => dNentry₀₀_eq (f := f) y hy)

/-- The shape-entry function `S₁₀` is `C^∞` on the interior of the strip. -/
lemma contDiffOn_S10f {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ContDiffOn ℝ ∞ (S10f f) stripInterior := by
  exact (ContDiffOn.inner ℝ (contDiffOn_fderiv_dirN₁ hf) (contDiffOn_tangent₀ hf)).congr
    (fun y hy => dNentry₁₀_eq (f := f) y hy)

/-- The shape-entry function `S₁₁` is `C^∞` on the interior of the strip. -/
lemma contDiffOn_S11f {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ContDiffOn ℝ ∞ (S11f f) stripInterior := by
  exact (ContDiffOn.inner ℝ (contDiffOn_fderiv_dirN₁ hf) (contDiffOn_tangent₁ hf)).congr
    (fun y hy => dNentry₁₁_eq (f := f) y hy)

/-- The kernel vector field `Wf` is `C^∞` on the interior of the strip. -/
lemma contDiffOn_Wf {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ContDiffOn ℝ ∞ (Wf f) stripInterior := by
  have h₀ : ContDiffOn ℝ ∞ (fun y : ℝ² => (dNentry f y 1 0) • e0) stripInterior := by
    have hs := (contDiffOn_S10f hf).smul
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ² => e0) stripInterior)
    convert hs using 1
    funext y
    rfl
  have hb : ContDiffOn ℝ ∞ (fun y : ℝ² => (dNentry f y 0 0) • e1) stripInterior := by
    have hs := (contDiffOn_S00f hf).smul
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ² => e1) stripInterior)
    convert hs using 1
    funext y
    rfl
  simpa [Wf] using h₀.sub hb

/-- The kernel vector field is `C¹` at every interior point (hence admits a
local flow there by Picard–Lindelöf). -/
lemma contDiffAt_Wf_one {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, ContDiffAt ℝ 1 (Wf f) x := by
  intro x hx
  exact ((contDiffOn_Wf hf).contDiffAt (IsOpen.mem_nhds stripInterior_isOpen hx)).of_le (by decide)





/-- The basis vector `!₂[1,0]` is `EuclideanSpace.single 0 1`. -/
lemma single₀ : EuclideanSpace.single (0 : Fin 2) (1 : ℝ) = (!₂[1, 0] : ℝ²) := by
  ext i <;> fin_cases i <;> simp [EuclideanSpace.single]

/-- The basis vector `!₂[0,1]` is `EuclideanSpace.single 1 1`. -/
lemma single₁ : EuclideanSpace.single (1 : Fin 2) (1 : ℝ) = (!₂[0, 1] : ℝ²) := by
  ext i <;> fin_cases i <;> simp [EuclideanSpace.single]

/-- Coordinate functional: the `0`-coordinate of the derivative of a
basis-field `y ↦ g y • e0 + h y • e1` equals the derivative of the scalar
entry `g`. -/
lemma coord0_fderiv_basisField (g h : ℝ² → ℝ) (x w : ℝ²)
    (hdg : DifferentiableAt ℝ g x) (hdh : DifferentiableAt ℝ h x) :
    (fderiv ℝ (fun y : ℝ² => g y • e0 + h y • e1) x w) (0 : Fin 2) = fderiv ℝ g x w := by
  have hd0 : DifferentiableAt ℝ (fun y : ℝ² => g y • e0) x := hdg.smul (differentiableAt_const e0)
  have hd1 : DifferentiableAt ℝ (fun y : ℝ² => h y • e1) x := hdh.smul (differentiableAt_const e1)
  have hfmap : fderiv ℝ (fun y : ℝ² => g y • e0 + h y • e1) x =
      (fderiv ℝ g x).smulRight e0 + (fderiv ℝ h x).smulRight e1 := by
    have h1 : fderiv ℝ (fun y : ℝ² => g y • e0) x = (fderiv ℝ g x).smulRight e0 :=
      fderiv_smul_const hdg e0
    have h2 : fderiv ℝ (fun y : ℝ² => h y • e1) x = (fderiv ℝ h x).smulRight e1 :=
      fderiv_smul_const hdh e1
    calc
      fderiv ℝ (fun y : ℝ² => g y • e0 + h y • e1) x
          = fderiv ℝ ((fun y : ℝ² => g y • e0) + (fun y : ℝ² => h y • e1)) x := by rfl
      _ = fderiv ℝ (fun y : ℝ² => g y • e0) x + fderiv ℝ (fun y : ℝ² => h y • e1) x :=
          fderiv_add hd0 hd1
      _ = (fderiv ℝ g x).smulRight e0 + (fderiv ℝ h x).smulRight e1 := by rw [h1, h2]
  calc
    (fderiv ℝ (fun y : ℝ² => g y • e0 + h y • e1) x w) (0 : Fin 2)
        = (((fderiv ℝ g x).smulRight e0 + (fderiv ℝ h x).smulRight e1) w) (0 : Fin 2) := by
            rw [hfmap]
    _ = fderiv ℝ g x w := by
            simp [e0, e1, ContinuousLinearMap.smulRight_apply]

/-- Coordinate functional: the `1`-coordinate of the derivative of a
basis-field `y ↦ g y • e0 + h y • e1` equals the derivative of the scalar
entry `h`. -/
lemma coord1_fderiv_basisField (g h : ℝ² → ℝ) (x w : ℝ²)
    (hdg : DifferentiableAt ℝ g x) (hdh : DifferentiableAt ℝ h x) :
    (fderiv ℝ (fun y : ℝ² => g y • e0 + h y • e1) x w) (1 : Fin 2) = fderiv ℝ h x w := by
  have hd0 : DifferentiableAt ℝ (fun y : ℝ² => g y • e0) x := hdg.smul (differentiableAt_const e0)
  have hd1 : DifferentiableAt ℝ (fun y : ℝ² => h y • e1) x := hdh.smul (differentiableAt_const e1)
  have hfmap : fderiv ℝ (fun y : ℝ² => g y • e0 + h y • e1) x =
      (fderiv ℝ g x).smulRight e0 + (fderiv ℝ h x).smulRight e1 := by
    have h1 : fderiv ℝ (fun y : ℝ² => g y • e0) x = (fderiv ℝ g x).smulRight e0 :=
      fderiv_smul_const hdg e0
    have h2 : fderiv ℝ (fun y : ℝ² => h y • e1) x = (fderiv ℝ h x).smulRight e1 :=
      fderiv_smul_const hdh e1
    calc
      fderiv ℝ (fun y : ℝ² => g y • e0 + h y • e1) x
          = fderiv ℝ ((fun y : ℝ² => g y • e0) + (fun y : ℝ² => h y • e1)) x := by rfl
      _ = fderiv ℝ (fun y : ℝ² => g y • e0) x + fderiv ℝ (fun y : ℝ² => h y • e1) x :=
          fderiv_add hd0 hd1
      _ = (fderiv ℝ g x).smulRight e0 + (fderiv ℝ h x).smulRight e1 := by rw [h1, h2]
  calc
    (fderiv ℝ (fun y : ℝ² => g y • e0 + h y • e1) x w) (1 : Fin 2)
        = (((fderiv ℝ g x).smulRight e0 + (fderiv ℝ h x).smulRight e1) w) (1 : Fin 2) := by
            rw [hfmap]
    _ = fderiv ℝ h x w := by
            simp [e0, e1, ContinuousLinearMap.smulRight_apply]

/-- **Straightening of the kernel field, infinitesimal form** (perpendicular
statement): at an interior point, the directional derivative of the kernel
vector field `y ↦ b(y)•e0 − a(y)•e1` along itself is perpendicular to
`(a,b)` (in coordinates `a·(dw)₀ + b·(dw)₁ = 0`).  Instantiation of
`Commons.Analysis.Calculus.FDeriv.kernelField_direction_perp`. -/
lemma kernelField_direction_perp {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      let w : ℝ² := (dNentry f x 1 0) • e0 + (-(dNentry f x 0 0)) • e1
      dNentry f x 0 0 * ((fderiv ℝ (fun y : ℝ² =>
        (dNentry f y 1 0) • e0 + (-(dNentry f y 0 0)) • e1) x w) (0 : Fin 2)) +
      dNentry f x 1 0 * ((fderiv ℝ (fun y : ℝ² =>
        (dNentry f y 1 0) • e0 + (-(dNentry f y 0 0)) • e1) x w) (1 : Fin 2)) = 0 := by
  intro x hx
  let w : ℝ² := (dNentry f x 1 0) • e0 + (-(dNentry f x 0 0)) • e1
  have hmain := Commons.Analysis.Calculus.FDeriv.kernelField_direction_perp
    (U := stripInterior) (a := S00f f) (b := S10f f) (c := S11f f)
    stripInterior_isOpen
    ((contDiffOn_S00f hf).of_le (by decide))
    ((contDiffOn_S10f hf).of_le (by decide))
    ((contDiffOn_S11f hf).of_le (by decide))
    (fun y hy => gauss_scalar hf y hy)
    (fun y hy => by
      rw [single₁, single₀]
      simpa [S00f, S10f] using codazzi₀ hf y hy)
    (fun y hy => by
      rw [single₀, single₁]
      simpa [S11f, S10f] using codazzi₁ hf y hy)
  specialize hmain x hx
  -- hmain is the same statement with e0/e1 replaced by EuclideanSpace.single
  -- vectors and Sxxf abbreviations expanded; rewrite those:
  simpa [w, S00f, S10f, e0, e1, single₀, single₁, mul_comm, mul_left_comm, mul_assoc] using hmain



/-- The kernel vector field in "plus" form:
`y ↦ b(y)•e0 + (−a(y))•e1` (equal to `Wf f` as a field). -/
abbrev Vf (f : ℝ² → ℝ³) : ℝ² → ℝ² := fun y =>
  (dNentry f y 1 0) • e0 + (-(dNentry f y 0 0)) • e1

/-- The two presentations `Vf` and `Wf` of the kernel vector field agree. -/
lemma Vf_eq_Wf (f : ℝ² → ℝ³) : Vf f = Wf f := by
  funext y
  dsimp [Vf, Wf]
  rw [neg_smul]
  rw [sub_eq_add_neg]

/-- In two dimensions a nonzero vector with zero "cross product" against
another vector is a scalar multiple of it. -/
lemma exists_smul_of_det_zero {u v : ℝ²} (hv : v ≠ 0)
    (hdet : u 0 * v 1 = u 1 * v 0) : ∃ l : ℝ, u = l • v := by
  by_cases h0 : v 0 ≠ 0
  · refine ⟨u 0 / v 0, ?_⟩
    ext i <;> fin_cases i
    · simp [smul_eq_mul]
      field_simp [h0]
    · simp [smul_eq_mul]
      field_simp [h0]
      rw [hdet]
  · have hv0 : v 0 = 0 := by
      by_contra h
      exact h0 h
    have hv1 : v 1 ≠ 0 := by
      intro hz
      apply hv
      ext i <;> fin_cases i <;> simp [hv0, hz]
    refine ⟨u 1 / v 1, ?_⟩
    ext i <;> fin_cases i
    · simp [smul_eq_mul]
      field_simp [hv1]
      rw [hdet]
    · simp [smul_eq_mul]
      field_simp [hv1]

/-- **The kernel field straightens**: wherever the kernel vector field
`w = Vf f` is nonzero at an interior point, its directional derivative along
itself is parallel to it (`fderiv w x w = λ•w`).  Integral curves of `w`
therefore have `γ'' ∥ γ'`, i.e. they are straight segments. -/
lemma Vf_deriv_parallel {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      Vf f x ≠ 0 → ∃ l : ℝ, fderiv ℝ (Vf f) x (Vf f x) = l • (Vf f x) := by
  intro x hx hw
  let w : ℝ² := Vf f x
  have hperp := kernelField_direction_perp hf x hx
  -- hperp : dNentry f x 0 0 * ((fderiv (Vf f) x w) 0) +
  --          dNentry f x 1 0 * ((fderiv (Vf f) x w) 1) = 0   (with w := Vf f x)
  have hw0 : w 0 = dNentry f x 1 0 := by simp [w, Vf, e0, e1]
  have hw1 : w 1 = -(dNentry f x 0 0) := by simp [w, Vf, e0, e1]
  have hdet : (fderiv ℝ (Vf f) x w) 0 * (w 1) = (fderiv ℝ (Vf f) x w) 1 * (w 0) := by
    rw [hw0, hw1]
    nlinarith [hperp]
  rw [show Vf f x = w by rfl]
  exact exists_smul_of_det_zero hw hdet


/-- The kernel vector field `Vf` is `C^∞` on the interior of the strip. -/
lemma contDiffOn_Vf {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ContDiffOn ℝ ∞ (Vf f) stripInterior := by
  have hV : ContDiffOn ℝ ∞ (Vf f) stripInterior := by
    rw [Vf_eq_Wf]
    exact contDiffOn_Wf hf
  simpa using hV

/-- The kernel vector field is `C¹` at every interior point (hence admits a
local flow there by Picard–Lindelöf). -/
lemma contDiffAt_Vf_one {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, ContDiffAt ℝ 1 (Vf f) x := by
  intro x hx
  have hV : ContDiffAt ℝ 1 (Vf f) x := by
    rw [Vf_eq_Wf]
    exact contDiffAt_Wf_one hf x hx
  simpa using hV

/-- The kernel vector field is differentiable at every interior point. -/
lemma differentiableAt_Vf {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, DifferentiableAt ℝ (Vf f) x := by
  intro x hx
  exact ((contDiffOn_Vf hf).differentiableOn (by simp) x hx).differentiableAt
    (IsOpen.mem_nhds stripInterior_isOpen hx)

/-- The kernel vector field is continuous at every interior point. -/
lemma continuousAt_Vf {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, ContinuousAt (Vf f) x := by
  intro x hx
  exact (differentiableAt_Vf hf x hx).continuousAt

/-- **The kernel field is a section of the kernel of the shape operator**:
`dN f x (Vf f x) = 0` at every interior point (Gauss's equation). -/
lemma Vf_mem_ker {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, dN f x (Vf f x) = 0 := by
  intro x hx
  let w : Fin 2 → ℝ := ![dNentry f x 1 0, -dNentry f x 0 0]
  have hw : Vf f x = WithLp.toLp 2 w := by
    ext i <;> fin_cases i
    · simp [Vf, w, e0, e1]
    · simp [Vf, w, e0, e1]
  have hwv : ((Matrix.of (dNentry f x))ᵀ).mulVec w = 0 := by
    ext i <;> fin_cases i <;> simp [w, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Matrix.of_apply, Fin.sum_univ_two]
    · ring_nf
    · have hg := gauss_scalar hf x hx
      have hs : dNentry f x 0 1 = dNentry f x 1 0 :=
        shapeOperator_symm hf x hx (0 : Fin 2) (1 : Fin 2)
      rw [hs]
      ring_nf
      nlinarith [hg]
  have hker := shape_ker_of_mulVec hf x hx w hwv
  rw [← hw] at hker
  exact hker


/-- The **mirror kernel vector field** `V2f`: `y ↦ c(y)•e₀̂ − b(y)•e₁̂` with
`c = S₁₁`, `b = S₁₀` (a second section of the kernel, nonzero exactly where
the first one vanishes if `dN ≠ 0`). -/
abbrev V2f (f : ℝ² → ℝ³) : ℝ² → ℝ² := fun y =>
  (dNentry f y 1 1) • e0 + (-(dNentry f y 1 0)) • e1

/-- The mirror kernel vector field is `C^∞` on the interior of the strip. -/
lemma contDiffOn_V2f {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ContDiffOn ℝ ∞ (V2f f) stripInterior := by
  have h₀ : ContDiffOn ℝ ∞ (fun y : ℝ² => (dNentry f y 1 1) • e0) stripInterior := by
    have hs := (contDiffOn_S11f hf).smul
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ² => e0) stripInterior)
    convert hs using 1
    funext y
    rfl
  have hbp : ContDiffOn ℝ ∞ (fun y : ℝ² => (dNentry f y 1 0) • e1) stripInterior := by
    have hs := (contDiffOn_S10f hf).smul
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ² => e1) stripInterior)
    convert hs using 1
    funext y
    rfl
  simpa [V2f, sub_eq_add_neg, ← neg_smul] using h₀.sub hbp

/-- The mirror kernel vector field is `C¹` at every interior point. -/
lemma contDiffAt_V2f_one {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, ContDiffAt ℝ 1 (V2f f) x := by
  intro x hx
  exact ((contDiffOn_V2f hf).contDiffAt (IsOpen.mem_nhds stripInterior_isOpen hx)).of_le (by decide)

/-- The mirror kernel vector field is differentiable at every interior point. -/
lemma differentiableAt_V2f {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, DifferentiableAt ℝ (V2f f) x := by
  intro x hx
  exact ((contDiffOn_V2f hf).differentiableOn (by simp) x hx).differentiableAt
    (IsOpen.mem_nhds stripInterior_isOpen hx)

/-- The mirror kernel vector field is continuous at every interior point. -/
lemma continuousAt_V2f {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, ContinuousAt (V2f f) x := by
  intro x hx
  exact (differentiableAt_V2f hf x hx).continuousAt

/-- **The mirror kernel field is a section of the kernel of the shape
operator**: `dN f x (V2f f x) = 0` at every interior point. -/
lemma V2f_mem_ker {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, dN f x (V2f f x) = 0 := by
  intro x hx
  let w : Fin 2 → ℝ := ![dNentry f x 1 1, -dNentry f x 1 0]
  have hw : V2f f x = WithLp.toLp 2 w := by
    ext i <;> fin_cases i
    · simp [V2f, w, e0, e1]
    · simp [V2f, w, e0, e1]
  have hwv : ((Matrix.of (dNentry f x))ᵀ).mulVec w = 0 := by
    ext i <;> fin_cases i <;> simp [w, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Matrix.of_apply, Fin.sum_univ_two]
    · have hg := gauss_scalar hf x hx
      rw [pow_two] at hg
      nlinarith
    · have hs : dNentry f x 0 1 = dNentry f x 1 0 :=
        shapeOperator_symm hf x hx (0 : Fin 2) (1 : Fin 2)
      rw [hs]
      ring
  have hker := shape_ker_of_mulVec hf x hx w hwv
  rw [← hw] at hker
  exact hker


/-- **Straightening of the mirror kernel field, infinitesimal form**
(perpendicular statement): for the mirror field `w = (c,−b)`, the directional
derivative of `w` along itself is perpendicular to `(b,c)`:
`b·(dw)₀ + c·(dw)₁ = 0`.  Instantiation of
`Commons.Analysis.Calculus.FDeriv.kernelFieldMirror_direction_perp`. -/
lemma kernelFieldMirror_direction_perp {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      let w : ℝ² := (dNentry f x 1 1) • e0 + (-(dNentry f x 1 0)) • e1
      dNentry f x 1 0 * ((fderiv ℝ (fun y : ℝ² =>
        (dNentry f y 1 1) • e0 + (-(dNentry f y 1 0)) • e1) x w) (0 : Fin 2)) +
      dNentry f x 1 1 * ((fderiv ℝ (fun y : ℝ² =>
        (dNentry f y 1 1) • e0 + (-(dNentry f y 1 0)) • e1) x w) (1 : Fin 2)) = 0 := by
  intro x hx
  let w : ℝ² := (dNentry f x 1 1) • e0 + (-(dNentry f x 1 0)) • e1
  have hmain := Commons.Analysis.Calculus.FDeriv.kernelFieldMirror_direction_perp
    (U := stripInterior) (a := S00f f) (b := S10f f) (c := S11f f)
    stripInterior_isOpen
    ((contDiffOn_S00f hf).of_le (by decide))
    ((contDiffOn_S10f hf).of_le (by decide))
    ((contDiffOn_S11f hf).of_le (by decide))
    (fun y hy => gauss_scalar hf y hy)
    (fun y hy => by
      rw [single₁, single₀]
      simpa [S00f, S10f] using codazzi₀ hf y hy)
    (fun y hy => by
      rw [single₀, single₁]
      simpa [S11f, S10f] using codazzi₁ hf y hy)
  specialize hmain x hx
  simpa [w, S00f, S10f, S11f, e0, e1, single₀, single₁, mul_comm, mul_left_comm, mul_assoc] using hmain

/-- **The mirror kernel field straightens**: wherever the mirror kernel
vector field `w = V2f f` is nonzero at an interior point, its directional
derivative along itself is parallel to it.  Integral curves of `w` are
straight. -/
lemma V2_deriv_parallel {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      V2f f x ≠ 0 → ∃ l : ℝ, fderiv ℝ (V2f f) x (V2f f x) = l • (V2f f x) := by
  intro x hx hw
  let w : ℝ² := V2f f x
  have hperp := kernelFieldMirror_direction_perp hf x hx
  have hw0 : w 0 = dNentry f x 1 1 := by simp [w, V2f, e0, e1]
  have hw1 : w 1 = -(dNentry f x 1 0) := by simp [w, V2f, e0, e1]
  have hdet : (fderiv ℝ (V2f f) x w) 0 * (w 1) = (fderiv ℝ (V2f f) x w) 1 * (w 0) := by
    rw [hw0, hw1]
    nlinarith [hperp]
  rw [show V2f f x = w by rfl]
  exact exists_smul_of_det_zero hw hdet

end Submission.PaperBand
end
