import Mathlib
import Submission.Work.RPA3.TubularDefs
import Submission.Work.RPA3.Symp
import Submission.Work.RPA3.contDiff_thetaP
import Submission.Work.RPA3.theta_columns_defs

/-!
# RPA3: the tubular map is a local diffeomorphism at `ξ = 0` (no smallness needed)

At `ξ = 0` the tubular parametrisation

`θ(τ,x,t,ξ) = ℓ τ (x,t) + J (ξ₁ ∂_xℓ + ξ₂ ∂_tℓ)`

is affine in `ξ`, so its derivative at `(τ,((x,t),(0,0)))` is the block triangular map

`(σ, ((a,b),(c,d))) ↦ (σ, σ ∂_τℓ + a ∂_xℓ + b ∂_tℓ + c J∂_xℓ + d J∂_tℓ)`.

The `(x,t,ξ)` block has the four independent columns `∂_xℓ, ∂_tℓ, J∂_xℓ, J∂_tℓ`
(`lagrangian_independent`, `Symp.lean`), so this block is injective, hence bijective on the
finite dimensional `PS`; the `τ`-block `1` then makes the whole map invertible.  Consequently
`thetaP L` is a local diffeomorphism at every point of the plane `ξ = 0` — in particular for
*every* `x`, with no smallness of `ξ` and no restriction beyond `τ ∈ [-1,2]` (the latter is in
fact unused).

The two `ξ`-columns are read off from the affineness of `θ` in `ξ` (`theta_eq_affine`) and the
three `(τ,x,t)`-columns from `theta L _ _ _ (0,0) = ℓ` (`theta_zero`) followed by the shift rule
for `deriv`.  `HasFDerivAt` comes from `ContDiff ℝ 7 (thetaP L)`.
-/

open scoped ContDiff

set_option autoImplicit false
noncomputable section

namespace Work.RPA3

/-! ## Coordinates of `PS` as continuous linear functionals -/

/-- `q₁` as a continuous linear functional. -/
def cq1 : PS →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))

/-- `q₂` as a continuous linear functional. -/
def cq2 : PS →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))

/-- `p₁` as a continuous linear functional. -/
def cp1 : PS →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))

/-- `p₂` as a continuous linear functional. -/
def cp2 : PS →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))

@[simp] theorem cq1_apply (z : PS) : cq1 z = z.1.1 := rfl
@[simp] theorem cq2_apply (z : PS) : cq2 z = z.1.2 := rfl
@[simp] theorem cp1_apply (z : PS) : cp1 z = z.2.1 := rfl
@[simp] theorem cp2_apply (z : PS) : cp2 z = z.2.2 := rfl

/-! ## Elementary one-dimensional calculus helpers -/

theorem deriv_comp_add_const_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (c : ℝ) : deriv (fun s : ℝ => f (c + s)) 0 = deriv f c := by
  have h : (fun s : ℝ => f (c + s)) = fun s : ℝ => f (s + c) := by
    funext s; rw [add_comm]
  rw [h, deriv_comp_add_const]
  simp

theorem fderiv_apply_eq_deriv_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x v : E}
    (hd : DifferentiableAt ℝ f x) :
    fderiv ℝ f x v = deriv (fun t : ℝ => f (x + t • v)) 0 := by
  rw [← DifferentiableAt.lineDeriv_eq_fderiv hd]
  rfl

/-! ## The derivative of `θ` at `ξ = 0` -/

/-- The `(x,t,ξ)` block of the derivative of `θ` at `ξ = 0`: it sends
`((a,b),(c,d))` to `a ∂_xℓ + b ∂_tℓ + c J∂_xℓ + d J∂_tℓ`. -/
def normLin (u v : PS) : PS →L[ℝ] PS :=
  cq1.smulRight u + cq2.smulRight v + cp1.smulRight (J u) + cp2.smulRight (J v)

@[simp] theorem normLin_apply (u v z : PS) :
    normLin u v z = z.1.1 • u + z.1.2 • v + z.2.1 • J u + z.2.2 • J v := by
  simp [normLin]

/-- The derivative of `thTheta L` at `(τ,((x,t),(0,0)))`. -/
def thThetaDeriv (L : LagFamilyAll) (τ x t : ℝ) : (ℝ × PS) →L[ℝ] PS :=
  ((ContinuousLinearMap.fst ℝ ℝ PS).smulRight (deriv (fun σ => L.ℓ σ (x, t)) τ))
    + (normLin (deriv (fun y => L.ℓ τ (y, t)) x) (deriv (fun s => L.ℓ τ (x, s)) t)).comp
        (ContinuousLinearMap.snd ℝ ℝ PS)

/-- The derivative of `thetaP L` at `(τ,((x,t),(0,0)))`; block triangular with `1` in the `τ`
slot. -/
def thetaPDeriv (L : LagFamilyAll) (τ x t : ℝ) : (ℝ × PS) →L[ℝ] (ℝ × PS) :=
  (ContinuousLinearMap.fst ℝ ℝ PS).prod (thThetaDeriv L τ x t)

@[simp] theorem thThetaDeriv_apply (L : LagFamilyAll) (τ x t : ℝ) (w : ℝ × PS) :
    thThetaDeriv L τ x t w = w.1 • deriv (fun σ => L.ℓ σ (x, t)) τ
      + normLin (deriv (fun y => L.ℓ τ (y, t)) x) (deriv (fun s => L.ℓ τ (x, s)) t) w.2 := rfl

@[simp] theorem thetaPDeriv_apply (L : LagFamilyAll) (τ x t : ℝ) (w : ℝ × PS) :
    thetaPDeriv L τ x t w = (w.1, w.1 • deriv (fun σ => L.ℓ σ (x, t)) τ
      + normLin (deriv (fun y => L.ℓ τ (y, t)) x) (deriv (fun s => L.ℓ τ (x, s)) t) w.2) := rfl

theorem thetaPDeriv_snd (L : LagFamilyAll) (τ x t : ℝ) (w : ℝ × PS) :
    (thetaPDeriv L τ x t w).2 = w.1 • deriv (fun σ => L.ℓ σ (x, t)) τ
      + normLin (deriv (fun y => L.ℓ τ (y, t)) x) (deriv (fun s => L.ℓ τ (x, s)) t) w.2 := rfl

/-! ## Non-degeneracy of the four columns -/

theorem normLin_eq_zero {u v : PS}
    (huv : ∀ a b : ℝ, a • u + b • v = 0 → a = 0 ∧ b = 0) (hlag : symp u v = 0) {z : PS}
    (hz : normLin u v z = 0) : z = 0 := by
  have h' : z.1.1 • u + z.1.2 • v + z.2.1 • J u + z.2.2 • J v = 0 := by
    rw [← normLin_apply]; exact hz
  obtain ⟨h1, h2, h3, h4⟩ := lagrangian_independent u v huv hlag z.1.1 z.1.2 z.2.1 z.2.2 h'
  exact Prod.ext (Prod.ext h1 h2) (Prod.ext h3 h4)

theorem normLin_injective {u v : PS}
    (huv : ∀ a b : ℝ, a • u + b • v = 0 → a = 0 ∧ b = 0) (hlag : symp u v = 0) :
    Function.Injective (normLin u v) := by
  intro z z' h
  have hzero : normLin u v (z - z') = 0 := by rw [map_sub, h, sub_self]
  have := normLin_eq_zero huv hlag hzero
  exact sub_eq_zero.mp this

/-! ## `thetaPDeriv` is injective, hence invertible -/

theorem thetaPDeriv_injective (L : LagFamilyAll) (τ x t : ℝ) :
    Function.Injective (thetaPDeriv L τ x t) := by
  intro p q hpq
  have h1 : p.1 = q.1 := by
    have := congrArg Prod.fst hpq
    simpa using this
  have hA : p.2 = q.2 := by
    refine normLin_injective (L.imm τ x t) (L.lag τ x t) ?_
    have h2' := congrArg Prod.snd hpq
    simp only [thetaPDeriv_snd] at h2'
    rw [h1] at h2'
    exact add_left_cancel h2'
  exact Prod.ext h1 hA

/-! ## `θ` is affine in `ξ` -/

theorem theta_eq_affine (L : LagFamilyAll) (τ x t : ℝ) (ξ : ℝ × ℝ) :
    theta L τ x t ξ = L.ℓ τ (x, t) + ξ.1 • J (deriv (fun y => L.ℓ τ (y, t)) x)
      + ξ.2 • J (deriv (fun s => L.ℓ τ (x, s)) t) := by
  simp only [theta]
  rw [J_add, J_smul, J_smul]
  abel

/-! ## The five columns of `fderiv (thTheta L)` at `ξ = 0` -/

abbrev eτ : ℝ × PS := (1, ((0, 0), (0, 0)))
abbrev ex : ℝ × PS := (0, ((1, 0), (0, 0)))
abbrev et : ℝ × PS := (0, ((0, 1), (0, 0)))
abbrev ec : ℝ × PS := (0, ((0, 0), (1, 0)))
abbrev ed : ℝ × PS := (0, ((0, 0), (0, 1)))

@[simp] theorem thThetaDeriv_eτ (L : LagFamilyAll) (τ x t : ℝ) :
    thThetaDeriv L τ x t eτ = deriv (fun σ => L.ℓ σ (x, t)) τ := by
  simp [thThetaDeriv, eτ]

@[simp] theorem thThetaDeriv_ex (L : LagFamilyAll) (τ x t : ℝ) :
    thThetaDeriv L τ x t ex = deriv (fun y => L.ℓ τ (y, t)) x := by
  simp [thThetaDeriv, ex]

@[simp] theorem thThetaDeriv_et (L : LagFamilyAll) (τ x t : ℝ) :
    thThetaDeriv L τ x t et = deriv (fun s => L.ℓ τ (x, s)) t := by
  simp [thThetaDeriv, et]

@[simp] theorem thThetaDeriv_ec (L : LagFamilyAll) (τ x t : ℝ) :
    thThetaDeriv L τ x t ec = J (deriv (fun y => L.ℓ τ (y, t)) x) := by
  simp [thThetaDeriv, ec]

@[simp] theorem thThetaDeriv_ed (L : LagFamilyAll) (τ x t : ℝ) :
    thThetaDeriv L τ x t ed = J (deriv (fun s => L.ℓ τ (x, s)) t) := by
  simp [thThetaDeriv, ed]

theorem decomp (v : ℝ × PS) :
    v = v.1 • eτ + v.2.1.1 • ex + v.2.1.2 • et + v.2.2.1 • ec + v.2.2.2 • ed := by
  ext <;> simp [eτ, ex, et, ec, ed]

theorem differentiableAt_thTheta (L : LagFamilyAll) (τ x t : ℝ) :
    DifferentiableAt ℝ (thTheta L) (τ, ((x, t), (0, 0))) := by
  have h : DifferentiableAt ℝ (fun w : ℝ × PS => (thetaP L w).snd) (τ, ((x, t), (0, 0))) :=
    ((contDiff_thetaP L).differentiable (by norm_num)).differentiableAt.snd
  convert h using 1
  funext w
  rfl

theorem fderiv_thTheta_eτ (L : LagFamilyAll) (τ x t : ℝ) :
    fderiv ℝ (thTheta L) (τ, ((x, t), (0, 0))) eτ = deriv (fun σ => L.ℓ σ (x, t)) τ := by
  rw [fderiv_apply_eq_deriv_line (differentiableAt_thTheta L τ x t)]
  have hfun : (fun s : ℝ => thTheta L ((τ, ((x, t), (0, 0))) + s • eτ))
      = fun s : ℝ => theta L (τ + s) x t (0, 0) := by
    funext s
    have harg : (τ, ((x, t), (0, 0))) + s • eτ = (τ + s, ((x, t), (0, 0))) := by
      simp [eτ]
    rw [harg, thTheta_apply]
  rw [hfun]
  have hstep : deriv (fun s : ℝ => theta L (τ + s) x t (0, 0)) 0
      = deriv (fun σ => theta L σ x t (0, 0)) τ :=
    deriv_comp_add_const_zero (fun σ => theta L σ x t (0, 0)) τ
  rw [hstep]
  simp

theorem fderiv_thTheta_ex (L : LagFamilyAll) (τ x t : ℝ) :
    fderiv ℝ (thTheta L) (τ, ((x, t), (0, 0))) ex = deriv (fun y => L.ℓ τ (y, t)) x := by
  rw [fderiv_apply_eq_deriv_line (differentiableAt_thTheta L τ x t)]
  have hfun : (fun s : ℝ => thTheta L ((τ, ((x, t), (0, 0))) + s • ex))
      = fun s : ℝ => theta L τ (x + s) t (0, 0) := by
    funext s
    have harg : (τ, ((x, t), (0, 0))) + s • ex = (τ, ((x + s, t), (0, 0))) := by
      simp [ex]
    rw [harg, thTheta_apply]
  rw [hfun]
  have hstep : deriv (fun s : ℝ => theta L τ (x + s) t (0, 0)) 0
      = deriv (fun y => theta L τ y t (0, 0)) x :=
    deriv_comp_add_const_zero (fun y => theta L τ y t (0, 0)) x
  rw [hstep]
  simp

theorem fderiv_thTheta_et (L : LagFamilyAll) (τ x t : ℝ) :
    fderiv ℝ (thTheta L) (τ, ((x, t), (0, 0))) et = deriv (fun s => L.ℓ τ (x, s)) t := by
  rw [fderiv_apply_eq_deriv_line (differentiableAt_thTheta L τ x t)]
  have hfun : (fun s : ℝ => thTheta L ((τ, ((x, t), (0, 0))) + s • et))
      = fun s : ℝ => theta L τ x (t + s) (0, 0) := by
    funext s
    have harg : (τ, ((x, t), (0, 0))) + s • et = (τ, ((x, t + s), (0, 0))) := by
      simp [et]
    rw [harg, thTheta_apply]
  rw [hfun]
  have hstep : deriv (fun s : ℝ => theta L τ x (t + s) (0, 0)) 0
      = deriv (fun s => theta L τ x s (0, 0)) t :=
    deriv_comp_add_const_zero (fun s => theta L τ x s (0, 0)) t
  rw [hstep]
  simp

theorem fderiv_thTheta_ec (L : LagFamilyAll) (τ x t : ℝ) :
    fderiv ℝ (thTheta L) (τ, ((x, t), (0, 0))) ec
      = J (deriv (fun y => L.ℓ τ (y, t)) x) := by
  rw [fderiv_apply_eq_deriv_line (differentiableAt_thTheta L τ x t)]
  have hfun : (fun s : ℝ => thTheta L ((τ, ((x, t), (0, 0))) + s • ec))
      = fun s : ℝ => L.ℓ τ (x, t) + s • J (deriv (fun y => L.ℓ τ (y, t)) x) := by
    funext s
    have harg : (τ, ((x, t), (0, 0))) + s • ec = (τ, ((x, t), (s, 0))) := by
      simp [ec]
    rw [harg, thTheta_apply, theta_eq_affine]
    simp
  rw [hfun]
  have hd : HasDerivAt
      (fun s : ℝ => L.ℓ τ (x, t) + s • J (deriv (fun y => L.ℓ τ (y, t)) x))
      (J (deriv (fun y => L.ℓ τ (y, t)) x)) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => s • J (deriv (fun y => L.ℓ τ (y, t)) x))
        (J (deriv (fun y => L.ℓ τ (y, t)) x)) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (J (deriv (fun y => L.ℓ τ (y, t)) x))
    simpa using h1.const_add (L.ℓ τ (x, t))
  exact hd.deriv

theorem fderiv_thTheta_ed (L : LagFamilyAll) (τ x t : ℝ) :
    fderiv ℝ (thTheta L) (τ, ((x, t), (0, 0))) ed
      = J (deriv (fun s => L.ℓ τ (x, s)) t) := by
  rw [fderiv_apply_eq_deriv_line (differentiableAt_thTheta L τ x t)]
  have hfun : (fun s : ℝ => thTheta L ((τ, ((x, t), (0, 0))) + s • ed))
      = fun s : ℝ => L.ℓ τ (x, t) + s • J (deriv (fun s => L.ℓ τ (x, s)) t) := by
    funext s
    have harg : (τ, ((x, t), (0, 0))) + s • ed = (τ, ((x, t), (0, s))) := by
      simp [ed]
    rw [harg, thTheta_apply, theta_eq_affine]
    simp
  rw [hfun]
  have hd : HasDerivAt
      (fun s : ℝ => L.ℓ τ (x, t) + s • J (deriv (fun s => L.ℓ τ (x, s)) t))
      (J (deriv (fun s => L.ℓ τ (x, s)) t)) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => s • J (deriv (fun s => L.ℓ τ (x, s)) t))
        (J (deriv (fun s => L.ℓ τ (x, s)) t)) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (J (deriv (fun s => L.ℓ τ (x, s)) t))
    simpa using h1.const_add (L.ℓ τ (x, t))
  exact hd.deriv

theorem fderiv_thTheta (L : LagFamilyAll) (τ x t : ℝ) :
    fderiv ℝ (thTheta L) (τ, ((x, t), (0, 0))) = thThetaDeriv L τ x t := by
  have h1 := fderiv_thTheta_eτ L τ x t
  have h2 := fderiv_thTheta_ex L τ x t
  have h3 := fderiv_thTheta_et L τ x t
  have h4 := fderiv_thTheta_ec L τ x t
  have h5 := fderiv_thTheta_ed L τ x t
  apply ContinuousLinearMap.ext
  intro v
  rw [decomp v]
  simp only [map_add, map_smul, h1, h2, h3, h4, h5]
  rw [decomp v]
  simp only [thThetaDeriv_eτ, thThetaDeriv_ex, thThetaDeriv_et,
    thThetaDeriv_ec, thThetaDeriv_ed]

/-! ## The main statement -/

theorem hasFDerivAt_thTheta (L : LagFamilyAll) (τ x t : ℝ) :
    HasFDerivAt (thTheta L) (thThetaDeriv L τ x t) (τ, ((x, t), (0, 0))) := by
  rw [← fderiv_thTheta L τ x t]
  exact (differentiableAt_thTheta L τ x t).hasFDerivAt

theorem hasFDerivAt_thetaP (L : LagFamilyAll) (τ x t : ℝ) :
    HasFDerivAt (thetaP L) (thetaPDeriv L τ x t) (τ, ((x, t), (0, 0))) := by
  have h := hasFDerivAt_fst.prodMk (hasFDerivAt_thTheta L τ x t)
  convert h using 1
  · funext w
    rfl
  · rw [thetaPDeriv]

/-- At `ξ = 0` the tubular map is a local diffeomorphism for every `τ ∈ [-1,2]` and every `x, t`:
the derivative is block triangular with `1` in the `τ` slot and, in the `(x,t,ξ)` slots, the
four independent vectors `∂_xℓ, ∂_tℓ, J∂_xℓ, J∂_tℓ` (`LagFamilyAll.imm` and `LagFamilyAll.lag`,
via `lagrangian_independent` in `Submission.Work.RPA3.Symp`).  No smallness of `ξ` is needed here,
because at `ξ = 0` the columns are exactly these four vectors.  `HasFDerivAt` comes from
`ContDiff ℝ 7 (thetaP L)`. -/
theorem thetaP_locDiffeo_zero (L : Work.RPA3.LagFamilyAll) :
    ∀ τ ∈ Set.Icc (-1 : ℝ) 2, ∀ x t, Work.RPA3.IsLocDiffeoAt L (τ, ((x, t), (0, 0))) := by
  intro τ _ x t
  have hker : (thetaPDeriv L τ x t : (ℝ × PS) →ₗ[ℝ] (ℝ × PS)).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (thetaPDeriv_injective L τ x t)
  have hrange : (thetaPDeriv L τ x t : (ℝ × PS) →ₗ[ℝ] (ℝ × PS)).range = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact LinearMap.injective_iff_surjective.mp (thetaPDeriv_injective L τ x t)
  refine ⟨ContinuousLinearEquiv.ofBijective (thetaPDeriv L τ x t) hker hrange, ?_⟩
  simpa only [ContinuousLinearEquiv.coe_ofBijective] using hasFDerivAt_thetaP L τ x t

end Work.RPA3

end
