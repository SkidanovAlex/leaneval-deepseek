import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Submission.RadialRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The radial Laplacian formula on `EuclideanSpace ℝ (Fin 3)`

For a twice-differentiable profile `f : ℝ → ℝ`, the function
`F(y) := f ‖y‖` on `ℝ³` satisfies, at every `x ≠ 0`,

    ΔF(x) = f''(‖x‖) + (2/‖x‖)·f'(‖x‖)

(the standard radial Laplacian in three dimensions; the `2` is the dimension
minus one).  This is the second brick of the Layer-3 (scattering) analysis:
with `ω(x) = g(‖x‖)` radial, the three-dimensional scattering equation
`−Δω = v(1−ω)/2` reduces to the 1D ODE for `g`.
-/

noncomputable section

open Filter MeasureTheory Laplacian
open scoped ContDiff Topology Real RealInnerProductSpace
namespace Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma radlap_fderiv_apply_eq_deriv_mul {f : ℝ → ℝ} {t s : ℝ} (hfd : DifferentiableAt ℝ f t) :
    fderiv ℝ f t s = deriv f t * s := by
  have hfda : HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℝ (deriv f t)) t :=
    hfd.hasDerivAt.hasFDerivAt
  rw [hfda.fderiv]
  simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]

lemma radlap_differentiableAt_deriv_of_contDiffAt {f : ℝ → ℝ} {r : ℝ} (hf : ContDiffAt ℝ 2 f r) :
    DifferentiableAt ℝ (deriv f) r := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) r := by
    exact hf.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)
  have hd : DifferentiableAt ℝ (fun t : ℝ => (fderiv ℝ f t) (1 : ℝ)) r := by
    have hc : DifferentiableAt ℝ (fun t : ℝ => fderiv ℝ f t) r :=
      h1.differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
    exact DifferentiableAt.clm_apply (c := fun t : ℝ => fderiv ℝ f t)
      (u := fun _ : ℝ => (1 : ℝ)) hc (differentiableAt_const (c := (1 : ℝ)) (x := r))
  have hder : deriv f = fun t : ℝ => (fderiv ℝ f t) (1 : ℝ) := by
    funext t
    rfl
  rwa [hder]

lemma radlap_differentiableAt_norm (x : E) (hx : x ≠ 0) : DifferentiableAt ℝ (fun y : E => ‖y‖) x := by
  exact (contDiffAt_norm ℝ (n := (2 : ℕ∞ω)) hx).differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)

lemma radlap_fderiv_norm_apply (x : E) (hx : x ≠ 0) (a : E) :
    fderiv ℝ (fun y : E => ‖y‖) x a = inner ℝ x a / ‖x‖ := by
  let Q : E → ℝ := fun y => ‖y‖ ^ 2
  have hQdiff : DifferentiableAt ℝ Q x := by
    dsimp [Q]
    exact DifferentiableAt.norm_sq ℝ (differentiableAt_id (x := x))
  have hQx : Q x ≠ 0 := by
    dsimp [Q]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hfd := fderiv_sqrt (f := Q) (x := x) hQdiff hQx
  have hfun : (fun x : E => √(Q x)) = fun x : E => ‖x‖ := by
    funext y
    dsimp [Q]
    rw [Real.sqrt_sq (norm_nonneg y)]
  calc
    fderiv ℝ (fun y : E => ‖y‖) x a
        = fderiv ℝ (fun x : E => √(Q x)) x a := by rw [hfun.symm]
    _ = ((1 / (2 * √(Q x))) • fderiv ℝ Q x) a := by rw [hfd]
    _ = (1 / (2 * √(Q x))) * (fderiv ℝ Q x a) := by simp
    _ = (1 / (2 * ‖x‖)) * (2 * inner ℝ x a) := by
          dsimp [Q]
          rw [fderiv_norm_sq_apply]
          rw [Real.sqrt_sq (norm_nonneg x)]
          simp
    _ = inner ℝ x a / ‖x‖ := by
          have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
          field_simp [hx0]

lemma radlap_differentiableAt_inner_right (x u : E) : DifferentiableAt ℝ (fun z : E => inner ℝ z u) x := by
  have h : (fun z : E => inner ℝ z u) = ⇑(innerSL ℝ u) := by
    funext z
    rw [real_inner_comm]
    rfl
  rw [h]
  exact (innerSL ℝ u).differentiableAt

lemma radlap_fderiv_inner_right_apply_value (x u v : E) :
    fderiv ℝ (fun z : E => inner ℝ z u) x v = inner ℝ v u := by
  have hswap : (fun z : E => inner ℝ z u) = fun z : E => inner ℝ u z := by
    funext z
    exact real_inner_comm u z
  rw [hswap]
  have hL : (fun z : E => inner ℝ u z) = fun z : E => (innerSL ℝ u) z := by
    funext z
    rfl
  rw [hL]
  rw [ContinuousLinearMap.fderiv]
  rw [real_inner_comm]
  rfl

lemma radlap_fderiv_norm_inv_apply (x : E) (hx : x ≠ 0) (v : E) :
    fderiv ℝ (fun z : E => (‖z‖)⁻¹) x v = -(‖x‖ ^ 2)⁻¹ * (inner ℝ x v / ‖x‖) := by
  have hN : DifferentiableAt ℝ (fun z : E => ‖z‖) x := radlap_differentiableAt_norm x hx
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hInv : DifferentiableAt ℝ (fun t : ℝ => t⁻¹) ‖x‖ :=
    DifferentiableAt.inv (differentiableAt_id (x := ‖x‖)) hx0
  have hc := fderiv_comp (x := x) (f := fun z : E => ‖z‖) (g := fun t : ℝ => t⁻¹) hInv hN
  calc
    fderiv ℝ (fun z : E => (‖z‖)⁻¹) x v
        = (fderiv ℝ (fun t : ℝ => t⁻¹) (‖x‖) ∘SL fderiv ℝ (fun z : E => ‖z‖) x) v := by
          change fderiv ℝ ((fun t : ℝ => t⁻¹) ∘ (fun z : E => ‖z‖)) x v = _
          rw [hc]
    _ = fderiv ℝ (fun t : ℝ => t⁻¹) (‖x‖) (fderiv ℝ (fun z : E => ‖z‖) x v) := rfl
    _ = -(‖x‖ ^ 2)⁻¹ * (fderiv ℝ (fun z : E => ‖z‖) x v) := by
          rw [radlap_fderiv_apply_eq_deriv_mul hInv, deriv_inv]
    _ = -(‖x‖ ^ 2)⁻¹ * (inner ℝ x v / ‖x‖) := by rw [radlap_fderiv_norm_apply x hx v]

lemma radlap_fderiv_inner_div_norm (x u : E) (hx : x ≠ 0) :
    fderiv ℝ (fun z : E => inner ℝ z u / ‖z‖) x u =
      ‖u‖ ^ 2 / ‖x‖ - inner ℝ x u ^ 2 / ‖x‖ ^ 3 := by
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let I : E → ℝ := fun z => inner ℝ z u
  let J : E → ℝ := fun z => (‖z‖)⁻¹
  have hId : DifferentiableAt ℝ I x := by
    dsimp [I]
    exact radlap_differentiableAt_inner_right x u
  have hJd : DifferentiableAt ℝ J x := by
    dsimp [J]
    exact DifferentiableAt.inv (radlap_differentiableAt_norm x hx) hx0
  have hmul := fderiv_fun_mul (c := I) (d := J) hId hJd
  calc
    fderiv ℝ (fun z : E => inner ℝ z u / ‖z‖) x u
        = fderiv ℝ (fun z : E => inner ℝ z u * (‖z‖)⁻¹) x u := by
          apply congrArg (fun g : E → ℝ => fderiv ℝ g x u)
          funext z
          rw [div_eq_mul_inv]
    _ = (I x • fderiv ℝ J x + J x • fderiv ℝ I x) u := by
          change fderiv ℝ (fun z : E => I z * J z) x u = _
          rw [hmul]
    _ = I x * (fderiv ℝ J x u) + J x * (fderiv ℝ I x u) := by simp
    _ = inner ℝ x u * (-(‖x‖ ^ 2)⁻¹ * (inner ℝ x u / ‖x‖)) +
        (‖x‖)⁻¹ * inner ℝ u u := by
          rw [radlap_fderiv_norm_inv_apply x hx u]
          rw [radlap_fderiv_inner_right_apply_value x u u]
    _ = ‖u‖ ^ 2 / ‖x‖ - inner ℝ x u ^ 2 / ‖x‖ ^ 3 := by
          have hu2 : inner ℝ u u = ‖u‖ ^ 2 := by
            rw [real_inner_self_eq_norm_sq]
          rw [hu2]
          field_simp [hx0]
          ring

lemma radlap_fderiv_derivF_norm_apply {f : ℝ → ℝ} (x : E) (hx : x ≠ 0) (u : E)
    (hf : ContDiffAt ℝ 2 f ‖x‖) :
    fderiv ℝ (fun z : E => deriv f ‖z‖) x u =
      deriv (deriv f) ‖x‖ * (inner ℝ x u / ‖x‖) := by
  have hdf : DifferentiableAt ℝ (deriv f) ‖x‖ := radlap_differentiableAt_deriv_of_contDiffAt hf
  have hN : DifferentiableAt ℝ (fun z : E => ‖z‖) x := radlap_differentiableAt_norm x hx
  have hc := fderiv_comp (x := x) (f := fun z : E => ‖z‖) (g := deriv f) hdf hN
  calc
    fderiv ℝ (fun z : E => deriv f ‖z‖) x u
        = (fderiv ℝ (deriv f) (‖x‖) ∘SL fderiv ℝ (fun z : E => ‖z‖) x) u := by
          change fderiv ℝ ((deriv f) ∘ (fun z : E => ‖z‖)) x u = _
          rw [hc]
    _ = fderiv ℝ (deriv f) (‖x‖) (fderiv ℝ (fun z : E => ‖z‖) x u) := rfl
    _ = deriv (deriv f) ‖x‖ * (fderiv ℝ (fun z : E => ‖z‖) x u) := by
          rw [radlap_fderiv_apply_eq_deriv_mul hdf]
    _ = deriv (deriv f) ‖x‖ * (inner ℝ x u / ‖x‖) := by rw [radlap_fderiv_norm_apply x hx u]

lemma radlap_differentiableAt_derivF_norm {f : ℝ → ℝ} (x : E) (hx : x ≠ 0)
    (hf : ContDiffAt ℝ 2 f ‖x‖) : DifferentiableAt ℝ (fun z : E => deriv f ‖z‖) x := by
  have hdf : DifferentiableAt ℝ (deriv f) ‖x‖ := radlap_differentiableAt_deriv_of_contDiffAt hf
  have hN : DifferentiableAt ℝ (fun z : E => ‖z‖) x := radlap_differentiableAt_norm x hx
  change DifferentiableAt ℝ ((deriv f) ∘ (fun z : E => ‖z‖)) x
  exact hdf.comp x hN

lemma radlap_eventuallyEq_fderiv_radial {f : ℝ → ℝ} {x : E} (hx : x ≠ 0) (u : E)
    (hf : ContDiffAt ℝ 2 f ‖x‖) :
    (fun z : E => fderiv ℝ (fun y : E => f ‖y‖) z u)
      =ᶠ[𝓝 x] (fun z : E => deriv f ‖z‖ * (inner ℝ z u / ‖z‖)) := by
  obtain ⟨W, hWmem, hcd⟩ := hf.contDiffOn (by norm_num : (1 : ℕ∞ω) ≤ 2) (by norm_num)
  obtain ⟨O, hOW, hOopen, hOr⟩ := mem_nhds_iff.mp hWmem
  have hcdO : ContDiffOn ℝ 1 f O := hcd.mono hOW
  have hdO : DifferentiableOn ℝ f O :=
    hcdO.differentiableOn (by norm_num : (1 : ℕ∞ω) ≠ 0)
  filter_upwards [isOpen_ne.mem_nhds hx,
    ContinuousAt.preimage_mem_nhds (continuous_norm.continuousAt (x := x))
      (IsOpen.mem_nhds hOopen hOr)] with z hz hzO
  have hfd : DifferentiableAt ℝ f ‖z‖ := hdO.differentiableAt (IsOpen.mem_nhds hOopen hzO)
  have hN : DifferentiableAt ℝ (fun y : E => ‖y‖) z := radlap_differentiableAt_norm z hz
  have hc := fderiv_comp (x := z) (f := fun y : E => ‖y‖) (g := f) hfd hN
  calc
    fderiv ℝ (fun y : E => f ‖y‖) z u
        = (fderiv ℝ f (‖z‖) ∘SL fderiv ℝ (fun y : E => ‖y‖) z) u := by
          change fderiv ℝ (f ∘ (fun y : E => ‖y‖)) z u = _
          rw [hc]
    _ = fderiv ℝ f (‖z‖) (fderiv ℝ (fun y : E => ‖y‖) z u) := rfl
    _ = deriv f ‖z‖ * (fderiv ℝ (fun y : E => ‖y‖) z u) := by
          rw [radlap_fderiv_apply_eq_deriv_mul hfd]
    _ = deriv f ‖z‖ * (inner ℝ z u / ‖z‖) := by rw [radlap_fderiv_norm_apply z hz u]

lemma radlap_fderiv_psi_apply {f : ℝ → ℝ} (x : E) (hx : x ≠ 0) (u : E)
    (hf : ContDiffAt ℝ 2 f ‖x‖) :
    fderiv ℝ (fun z : E => deriv f ‖z‖ * (inner ℝ z u / ‖z‖)) x u =
      deriv (deriv f) ‖x‖ * (inner ℝ x u / ‖x‖)^2
        + deriv f ‖x‖ * (‖u‖ ^ 2 / ‖x‖ - inner ℝ x u ^ 2 / ‖x‖ ^ 3) := by
  let h1 : E → ℝ := fun z => deriv f ‖z‖
  let h2 : E → ℝ := fun z => inner ℝ z u / ‖z‖
  have hh1d : DifferentiableAt ℝ h1 x := by
    dsimp [h1]
    exact radlap_differentiableAt_derivF_norm x hx hf
  have hh2d : DifferentiableAt ℝ h2 x := by
    dsimp [h2]
    have hJd : DifferentiableAt ℝ (fun z : E => (‖z‖)⁻¹) x :=
      DifferentiableAt.inv (radlap_differentiableAt_norm x hx) (norm_ne_zero_iff.mpr hx)
    have hm : DifferentiableAt ℝ (fun z : E => inner ℝ z u * (‖z‖)⁻¹) x :=
      DifferentiableAt.mul (radlap_differentiableAt_inner_right x u) hJd
    simpa [div_eq_mul_inv] using hm
  have hmul := fderiv_fun_mul (c := h1) (d := h2) hh1d hh2d
  calc
    fderiv ℝ (fun z : E => deriv f ‖z‖ * (inner ℝ z u / ‖z‖)) x u
        = (h1 x • fderiv ℝ h2 x + h2 x • fderiv ℝ h1 x) u := by
          change fderiv ℝ (fun z : E => h1 z * h2 z) x u = _
          rw [hmul]
    _ = h1 x * (fderiv ℝ h2 x u) + h2 x * (fderiv ℝ h1 x u) := by simp
    _ = deriv f ‖x‖ * (‖u‖ ^ 2 / ‖x‖ - inner ℝ x u ^ 2 / ‖x‖ ^ 3)
        + (inner ℝ x u / ‖x‖) * (deriv (deriv f) ‖x‖ * (inner ℝ x u / ‖x‖)) := by
          rw [radlap_fderiv_inner_div_norm x u hx]
          rw [radlap_fderiv_derivF_norm_apply x hx u hf]
    _ = deriv (deriv f) ‖x‖ * (inner ℝ x u / ‖x‖)^2
        + deriv f ‖x‖ * (‖u‖ ^ 2 / ‖x‖ - inner ℝ x u ^ 2 / ‖x‖ ^ 3) := by
          ring

lemma radlap_fderiv_radial_second_apply {f : ℝ → ℝ} {x u : E} (hx : x ≠ 0)
    (hf : ContDiffAt ℝ 2 f ‖x‖) :
    fderiv ℝ (fun z : E => fderiv ℝ (fun y : E => f ‖y‖) z u) x u =
      deriv (deriv f) ‖x‖ * (inner ℝ x u / ‖x‖)^2
        + deriv f ‖x‖ * (‖u‖ ^ 2 / ‖x‖ - inner ℝ x u ^ 2 / ‖x‖ ^ 3) := by
  have hev := radlap_eventuallyEq_fderiv_radial hx u hf
  have heq : fderiv ℝ (fun z : E => fderiv ℝ (fun y : E => f ‖y‖) z u) x
      = fderiv ℝ (fun z : E => deriv f ‖z‖ * (inner ℝ z u / ‖z‖)) x := by
    exact hev.fderiv_eq
  rw [heq]
  exact radlap_fderiv_psi_apply x hx u hf

lemma radlap_iteratedFDeriv_two_eq_fderiv_dir {f : E → ℝ} {x a : E}
    (hfd : DifferentiableAt ℝ (fderiv ℝ f) x) :
    iteratedFDeriv ℝ 2 f x ![a, a] = fderiv ℝ (fun z => fderiv ℝ f z a) x a := by
  rw [iteratedFDeriv_two_apply]
  have hc : DifferentiableAt ℝ (fun z : E => fderiv ℝ f z) x := hfd
  have hg : fderiv ℝ (fun z : E => fderiv ℝ f z a) x = (fderiv ℝ (fderiv ℝ f) x).flip a := by
    rw [fderiv_clm_apply (c := fun z : E => fderiv ℝ f z) (u := fun _ : E => a) hc
      (differentiableAt_const (c := a) (x := x))]
    simp
  rw [hg]
  rfl

lemma radlap_contDiffAt_radial {f : ℝ → ℝ} {x : E} (hx : x ≠ 0)
    (hf : ContDiffAt ℝ 2 f ‖x‖) :
    ContDiffAt ℝ 2 (fun y : E => f ‖y‖) x := by
  exact hf.comp x (contDiffAt_norm ℝ (n := (2 : ℕ∞ω)) hx)

lemma radlap_differentiableAt_fderiv_radial {f : ℝ → ℝ} {x : E} (hx : x ≠ 0)
    (hf : ContDiffAt ℝ 2 f ‖x‖) :
    DifferentiableAt ℝ (fderiv ℝ (fun y : E => f ‖y‖)) x := by
  have hF : ContDiffAt ℝ 2 (fun y : E => f ‖y‖) x := radlap_contDiffAt_radial hx hf
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ (fun y : E => f ‖y‖)) x := by
    exact hF.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)
  exact h1.differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)

lemma radlap_iteratedFDeriv_radial_two {f : ℝ → ℝ} {x u : E} (hx : x ≠ 0)
    (hf : ContDiffAt ℝ 2 f ‖x‖) :
    iteratedFDeriv ℝ 2 (fun y : E => f ‖y‖) x ![u, u]
      = deriv (deriv f) ‖x‖ * (inner ℝ x u / ‖x‖)^2
        + deriv f ‖x‖ * (‖u‖ ^ 2 / ‖x‖ - inner ℝ x u ^ 2 / ‖x‖ ^ 3) := by
  have hFd : DifferentiableAt ℝ (fderiv ℝ (fun y : E => f ‖y‖)) x :=
    radlap_differentiableAt_fderiv_radial hx hf
  rw [radlap_iteratedFDeriv_two_eq_fderiv_dir (f := fun y : E => f ‖y‖) (x := x) (a := u) hFd]
  exact radlap_fderiv_radial_second_apply hx hf

lemma radlap_sum_affine {ι : Type*} [Fintype ι] (A B : ℝ) (c : ι → ℝ) :
    (∑ i, (A * c i ^ 2 + B * (1 - c i ^ 2))) =
      A * (∑ i, c i ^ 2) + B * ((Fintype.card ι : ℝ) - ∑ i, c i ^ 2) := by
  calc
    (∑ i, (A * c i ^ 2 + B * (1 - c i ^ 2)))
        = ∑ i, ((A - B) * c i ^ 2 + B) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (A - B) * (∑ i, c i ^ 2) + (∑ i : ι, B) := by
          rw [Finset.sum_add_distrib]
          rw [Finset.mul_sum]
    _ = (A - B) * (∑ i, c i ^ 2) + (Fintype.card ι : ℝ) * B := by
          simp [nsmul_eq_mul]
    _ = A * (∑ i, c i ^ 2) + B * ((Fintype.card ι : ℝ) - ∑ i, c i ^ 2) := by
          ring

end Generic

/-- The Laplacian of a radial function in three dimensions -/
lemma laplacian_radial_norm {f : ℝ → ℝ} {x : ℝ³} (hx : x ≠ 0)
    (hf : ContDiffAt ℝ 2 f ‖x‖) :
    (Δ fun y : ℝ³ => f ‖y‖) x = deriv (deriv f) ‖x‖ + 2 * deriv f ‖x‖ / ‖x‖ := by
  let E := EuclideanSpace ℝ (Fin 3)
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let A : ℝ := deriv (deriv f) ‖x‖
  let B : ℝ := deriv f ‖x‖ / ‖x‖
  let c : Fin 3 → ℝ := fun i => inner ℝ x (euclBasis3 i) / ‖x‖
  have hlap : (Δ (fun y : ℝ³ => f ‖y‖)) x =
      ∑ i : Fin 3, iteratedFDeriv ℝ 2 (fun y : ℝ³ => f ‖y‖) x ![euclBasis3 i, euclBasis3 i] := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := (fun y : ℝ³ => f ‖y‖)) euclBasis3]
  have hterm : ∀ i : Fin 3, iteratedFDeriv ℝ 2 (fun y : ℝ³ => f ‖y‖) x ![euclBasis3 i, euclBasis3 i]
      = A * (c i)^2 + B * (1 - (c i)^2) := by
    intro i
    have hmain := radlap_iteratedFDeriv_radial_two (E := EuclideanSpace ℝ (Fin 3)) (x := x) (u := euclBasis3 i) hx hf
    have hu1 : ‖euclBasis3 i‖ = 1 := euclBasis3.orthonormal.1 i
    dsimp [A, B, c]
    rw [hmain]
    have hr2 : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 hx0
    field_simp [hr2]
    rw [hu1]
    ring
  have hc2 : (∑ i : Fin 3, (c i)^2) = 1 := by
    dsimp [c]
    have hsum : (∑ i : Fin 3, inner ℝ x (euclBasis3 i) ^ 2) = ‖x‖ ^ 2 := by
      simpa using (OrthonormalBasis.sum_sq_inner_left (b := euclBasis3) x)
    calc
      (∑ i : Fin 3, (inner ℝ x (euclBasis3 i) / ‖x‖) ^ 2)
          = (∑ i : Fin 3, inner ℝ x (euclBasis3 i) ^ 2 / ‖x‖ ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [div_pow]
      _ = (∑ i : Fin 3, inner ℝ x (euclBasis3 i) ^ 2) / ‖x‖ ^ 2 := by
            rw [Finset.sum_div]
      _ = 1 := by
            rw [hsum]
            field_simp [hx0]
  calc
    (Δ (fun y : ℝ³ => f ‖y‖)) x
        = ∑ i : Fin 3, iteratedFDeriv ℝ 2 (fun y : ℝ³ => f ‖y‖) x ![euclBasis3 i, euclBasis3 i] := hlap
    _ = ∑ i : Fin 3, (A * (c i)^2 + B * (1 - (c i)^2)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hterm i
    _ = A * (∑ i : Fin 3, (c i)^2) + B * (3 - ∑ i : Fin 3, (c i)^2) := by
          rw [radlap_sum_affine]
          norm_num
    _ = A + 2 * B := by
          rw [hc2]
          norm_num
          ring
    _ = deriv (deriv f) ‖x‖ + 2 * deriv f ‖x‖ / ‖x‖ := by
          dsimp [A, B]
          ring

lemma laplacian_radial_profile {w : ℝ³ → ℝ} (hw : IsRadial w) {x : ℝ³} (hx : x ≠ 0)
    (hg : ContDiffAt ℝ 2 (radialProfile w) ‖x‖) :
    (Δ w) x = deriv (deriv (radialProfile w)) ‖x‖ + 2 * deriv (radialProfile w) ‖x‖ / ‖x‖ := by
  have hEq : (Δ w) = (Δ fun y : ℝ³ => radialProfile w ‖y‖) := by
    congr 1
    funext y
    exact radial_eq_profile hw y
  rw [hEq]
  exact laplacian_radial_norm (f := radialProfile w) hx hg

end Submission.BoseGases
