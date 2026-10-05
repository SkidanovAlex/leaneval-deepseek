import Mathlib
import Submission.Work.RPA3.flux_prim_defs
import Submission.Work.RPA3.flux_prim_smooth
import Submission.Work.RPA3.flux_form_closed
import Submission.Work.RPA3.deriv_deriv_swap

namespace Work.RPA3

open scoped ContDiff

/-! ## Regularity of the `t`-partial of the primitive

Both inputs of the Clairaut argument of `deriv_Hf_t` are packaged here: the `C⁷`-regularity of
`(s,y) ↦ Hf L τ y s` (the primitive with its two variables swapped) and the `C⁶`-regularity of its
`t`-partial `(t₀,x) ↦ ∂_t Hf L τ x t₀`, which is all we need for the differentiability of the
two summands of `F`. -/

/-- `(s, y) ↦ Hf L τ y s` is `C⁷`: it is `contDiff_Hf` composed with the (smooth) swap of the
last two variables. -/
lemma contDiff_Hf_swap (L : LagFamily) (τ : ℝ) :
    ContDiff ℝ 7 (fun w : ℝ × ℝ => Hf L τ w.2 w.1) := by
  have hmap : ContDiff ℝ 7 (fun q : ℝ × ℝ => ((τ, (q.2, q.1)) : ℝ × (ℝ × ℝ))) := by fun_prop
  have h1 := (contDiff_Hf L).comp hmap
  simpa [Function.comp_def] using h1

/-- The `t`-partial of the flux primitive, `(t₀, x) ↦ ∂_t Hf L τ x t₀`, is `C⁶`.  This is
`ContDiff.fderiv` applied to `(s,y) ↦ Hf L τ y s` (a `C⁷` map, `contDiff_Hf_swap`), followed by
evaluation in the direction `(1,0)`, which is `deriv` by `Work.RPA3.deriv_prodMk_left`. -/
lemma contDiff_deriv_Hf_t (L : LagFamily) (τ : ℝ) :
    ContDiff ℝ 6 (fun p : ℝ × ℝ => deriv (fun s => Hf L τ p.2 s) p.1) := by
  have hG := contDiff_Hf_swap L τ
  have hfd : ContDiff ℝ 6 (fderiv ℝ (fun q : ℝ × ℝ => Hf L τ q.2 q.1)) :=
    hG.fderiv_right (m := 6) (by norm_num)
  have h2 : ContDiff ℝ 6
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => Hf L τ q.2 q.1) p (1, 0)) :=
    hfd.clm_apply contDiff_const
  have heq : (fun p : ℝ × ℝ => deriv (fun s => Hf L τ p.2 s) p.1)
      = fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => Hf L τ q.2 q.1) p (1, 0) := by
    funext p
    exact deriv_prodMk_left
      ((hG.differentiable (by norm_num)).differentiableAt (x := p)).hasFDerivAt
  rw [heq]
  exact h2

/-- The `t`-derivative of the flux primitive is minus the `t`-component of the flux form.

Route (avoiding differentiation under the integral sign).  Let
`F y = deriv (fun s => Hf L τ y s) t + btf L τ y t`.
(1) By `flux_form_closed` (with `ℓ := fun σ x t => L.ℓ σ (x,t)`), the flux form is closed:
`deriv (fun y => btf L τ y t) y = deriv (fun s => bxf L τ y s) t` — the symmetric form of the
statement in that file.
(2) By `Work.RPA3.deriv_Hf_x`, `deriv (fun y => Hf L τ y s) y = -bxf L τ y s`.
(3) By Clairaut in the two remaining variables, `Work.RPA3.deriv_deriv_swap` applied to the `C²`
function `G (s,y) = Hf L τ y s` (a composition of `Work.RPA3.contDiff_Hf` with the smooth
`(s,y) ↦ (τ,(y,s))`), we have
`deriv (fun y => deriv (fun s => Hf L τ y s) t) y = deriv (fun s => deriv (fun y => Hf L τ y s) y) t`.
Substituting (2) and (1) into this, `F` has zero derivative everywhere; it is differentiable (its
two summands are restrictions of the `C⁶` partials of `contDiff_Hf` and of `contDiff_fluxT`), so
it is constant, and at `y = -X₀` it vanishes: `Hf L τ (-X₀) s = -∫_{-X₀}^{-X₀} bxf = 0` for all
`s` (by `Work.RPA3.Hf_eq_integral` and `intervalIntegral.integral_same`), so its `t`-derivative
vanishes; while `btf L τ (-X₀) t = 0` by `Work.RPA3.bxf_btf_van` since `X₀ ≤ |X₀| = |-(X₀)|`
(always true, no sign hypothesis on `X₀` is needed).  Hence `F ≡ 0`, which is the claim. -/
theorem deriv_Hf_t (L : Work.RPA3.LagFamily) (τ x t : ℝ) :
    deriv (fun s => Work.RPA3.Hf L τ x s) t = -Work.RPA3.btf L τ x t := by
  -- (3) Clairaut: the `y`-derivative of `∂_t Hf` equals the `t`-derivative of `∂_y Hf`.
  have hAeq : ∀ y, deriv (fun y' : ℝ => deriv (fun s => Hf L τ y' s) t) y
      = -deriv (fun s => bxf L τ y s) t := by
    intro y
    have hswap := deriv_deriv_swap (G := fun w : ℝ × ℝ => Hf L τ w.2 w.1)
      (a := t) (b := y) ((contDiff_Hf_swap L τ).contDiffAt.of_le (by norm_num))
    have hfun : (fun σ : ℝ => deriv (fun y' => Hf L τ y' σ) y) = fun σ => -bxf L τ y σ :=
      funext fun σ => deriv_Hf_x L τ y σ
    rw [hfun] at hswap
    rw [hswap]
    simp
  -- (1) Closedness of the flux form.
  have hBeq : ∀ y, deriv (fun y' : ℝ => btf L τ y' t) y = deriv (fun s => bxf L τ y s) t := by
    intro y
    have hclosed := flux_form_closed (ℓ := fun σ (a b : ℝ) => L.ℓ σ (a, b))
      (by simpa using L.smooth.of_le (by norm_num)) (fun τ x t => L.lag τ x t) τ y t
    simpa only [bxf, btf] using hclosed
  -- Differentiability of the two summands of `F`.
  have hAdiff : Differentiable ℝ (fun y : ℝ => deriv (fun s => Hf L τ y s) t) := by
    have h := ((contDiff_deriv_Hf_t L τ).differentiable (by norm_num)).comp
      (f := fun y : ℝ => (t, y)) (by fun_prop)
    simpa [Function.comp_def] using h
  have hBdiff : Differentiable ℝ (fun y : ℝ => btf L τ y t) := by
    have hbase : ContDiff ℝ 7 (fun y : ℝ => btf L τ y t) := by
      have hmap : ContDiff ℝ 7 (fun y : ℝ => ((τ, (y, t)) : ℝ × (ℝ × ℝ))) := by fun_prop
      have h1 := (contDiff_fluxT L).comp hmap
      simpa [Function.comp_def] using h1
    exact hbase.differentiable (by norm_num)
  -- `F` has vanishing derivative, hence is constant.
  have hFdiff : Differentiable ℝ
      (fun y : ℝ => deriv (fun s => Hf L τ y s) t + btf L τ y t) := hAdiff.add hBdiff
  have hderivF : ∀ y, deriv (fun y' : ℝ => deriv (fun s => Hf L τ y' s) t + btf L τ y' t) y = 0 := by
    intro y
    change deriv ((fun y' : ℝ => deriv (fun s => Hf L τ y' s) t) + fun y' => btf L τ y' t) y = 0
    rw [deriv_add hAdiff.differentiableAt hBdiff.differentiableAt, hAeq y, hBeq y]
    ring
  have hmain := is_const_of_deriv_eq_zero hFdiff hderivF x (-(L.X0))
  -- `F (-X₀) = 0`: both summands vanish there.
  have hzero1 : deriv (fun s : ℝ => Hf L τ (-(L.X0)) s) t = 0 := by
    have h : (fun s : ℝ => Hf L τ (-(L.X0)) s) = fun _ => (0 : ℝ) := by
      funext s
      rw [Hf_eq_integral L τ (-(L.X0)) s]
      simp
    rw [h]
    simp
  have hzero2 : btf L τ (-(L.X0)) t = 0 :=
    (bxf_btf_van L τ (-(L.X0)) t (by rw [abs_neg]; exact le_abs_self (L.X0))).2
  rw [hzero1, hzero2, add_zero] at hmain
  linarith

end Work.RPA3
