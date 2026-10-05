import Mathlib
import Submission.Work.RPA3.flux_prim_defs

/-!
# RPA3, D1: smoothness of the flux components and of the primitive

This module collects the `C⁷`-regularity inputs of the flux primitive (D1):

* `bxf`, `btf` are `C⁷` as functions of `(τ,x,t)`
  (`contDiff_fluxX`, `contDiff_fluxT`);
* the fixed-interval integral `Hf` is `C⁷` (`contDiff_Hf`), by
  `contDiff_param_intervalIntegral`;
* `Hf` equals `-∫_{u=-X₀}^{x} β_u du` (`Hf_eq_integral`), and its `x`-derivative is `-β_x`
  (`deriv_Hf_x`), by the fundamental theorem of calculus;
* both components of the flux form vanish for `|x| ≥ X₀` (`bxf_btf_van`).

Everything here is used by `Work.RPA3.flux_primitive`.
-/

namespace Work.RPA3

open scoped ContDiff
open scoped Interval
open MeasureTheory

set_option autoImplicit false

noncomputable section

/-! ## `symp` of two smooth maps -/

lemma contDiff_symp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞}
    {u v : X → PS} (hu : ContDiff ℝ n u) (hv : ContDiff ℝ n v) :
    ContDiff ℝ n (fun z => symp (u z) (v z)) := by
  simp only [symp]
  fun_prop

/-! ## The three slice derivatives are `C⁷` -/

lemma contDiff_deriv_fst (L : LagFamily) :
    ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) => deriv (fun σ => L.ℓ σ z.2) z.1) := by
  have hperm : ContDiff ℝ 8 (fun w : (ℝ × (ℝ × ℝ)) × ℝ => (w.2, w.1.2)) := by fun_prop
  have hf : ContDiff ℝ 8 (Function.uncurry (fun (z : ℝ × (ℝ × ℝ)) (σ : ℝ) => L.ℓ σ z.2)) := by
    show ContDiff ℝ 8 (fun w : (ℝ × (ℝ × ℝ)) × ℝ => L.ℓ w.2 w.1.2)
    exact L.smooth.comp hperm
  have hg : ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) => z.1) := by fun_prop
  have h := ContDiff.fderiv (𝕜 := ℝ) (n := (7 : ENat)) (m := (8 : ENat))
    (f := fun (z : ℝ × (ℝ × ℝ)) (σ : ℝ) => L.ℓ σ z.2)
    (g := fun (z : ℝ × (ℝ × ℝ)) => z.1) hf hg (by norm_num)
  have h2 : ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) =>
      (fderiv ℝ (fun σ => L.ℓ σ z.2) z.1) 1) :=
    ContDiff.clm_apply h contDiff_const
  simpa only [fderiv_apply_one_eq_deriv] using h2

lemma contDiff_deriv_x (L : LagFamily) :
    ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) => deriv (fun y => L.ℓ z.1 (y, z.2.2)) z.2.1) := by
  have hperm : ContDiff ℝ 8 (fun w : (ℝ × (ℝ × ℝ)) × ℝ => (w.1.1, (w.2, w.1.2.2))) := by fun_prop
  have hf : ContDiff ℝ 8 (Function.uncurry (fun (z : ℝ × (ℝ × ℝ)) (y : ℝ) =>
      L.ℓ z.1 (y, z.2.2))) := by
    show ContDiff ℝ 8 (fun w : (ℝ × (ℝ × ℝ)) × ℝ => L.ℓ w.1.1 (w.2, w.1.2.2))
    exact L.smooth.comp hperm
  have hg : ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) => z.2.1) := by fun_prop
  have h := ContDiff.fderiv (𝕜 := ℝ) (n := (7 : ENat)) (m := (8 : ENat))
    (f := fun (z : ℝ × (ℝ × ℝ)) (y : ℝ) => L.ℓ z.1 (y, z.2.2))
    (g := fun (z : ℝ × (ℝ × ℝ)) => z.2.1) hf hg (by norm_num)
  have h2 : ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) =>
      (fderiv ℝ (fun y => L.ℓ z.1 (y, z.2.2)) z.2.1) 1) :=
    ContDiff.clm_apply h contDiff_const
  simpa only [fderiv_apply_one_eq_deriv] using h2

lemma contDiff_deriv_trd (L : LagFamily) :
    ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) => deriv (fun s => L.ℓ z.1 (z.2.1, s)) z.2.2) := by
  have hperm : ContDiff ℝ 8 (fun w : (ℝ × (ℝ × ℝ)) × ℝ => (w.1.1, (w.1.2.1, w.2))) := by fun_prop
  have hf : ContDiff ℝ 8 (Function.uncurry (fun (z : ℝ × (ℝ × ℝ)) (s : ℝ) =>
      L.ℓ z.1 (z.2.1, s))) := by
    show ContDiff ℝ 8 (fun w : (ℝ × (ℝ × ℝ)) × ℝ => L.ℓ w.1.1 (w.1.2.1, w.2))
    exact L.smooth.comp hperm
  have hg : ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) => z.2.2) := by fun_prop
  have h := ContDiff.fderiv (𝕜 := ℝ) (n := (7 : ENat)) (m := (8 : ENat))
    (f := fun (z : ℝ × (ℝ × ℝ)) (s : ℝ) => L.ℓ z.1 (z.2.1, s))
    (g := fun (z : ℝ × (ℝ × ℝ)) => z.2.2) hf hg (by norm_num)
  have h2 : ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) =>
      (fderiv ℝ (fun s => L.ℓ z.1 (z.2.1, s)) z.2.2) 1) :=
    ContDiff.clm_apply h contDiff_const
  simpa only [fderiv_apply_one_eq_deriv] using h2

/-! ## The two components of the flux form are `C⁷` -/

theorem contDiff_fluxX (L : LagFamily) :
    ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) => bxf L z.1 z.2.1 z.2.2) := by
  have h1 := contDiff_deriv_fst L
  have h2 := contDiff_deriv_x L
  have h3 : ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) =>
      symp (deriv (fun σ => L.ℓ σ z.2) z.1) (deriv (fun y => L.ℓ z.1 (y, z.2.2)) z.2.1)) :=
    contDiff_symp h1 h2
  simpa only [bxf] using h3

theorem contDiff_fluxT (L : LagFamily) :
    ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) => btf L z.1 z.2.1 z.2.2) := by
  have h1 := contDiff_deriv_fst L
  have h2 := contDiff_deriv_trd L
  have h3 : ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) =>
      symp (deriv (fun σ => L.ℓ σ z.2) z.1) (deriv (fun s => L.ℓ z.1 (z.2.1, s)) z.2.2)) :=
    contDiff_symp h1 h2
  simpa only [btf] using h3

/-! ## Smoothness of the primitive -/

theorem contDiff_HfIntegrand (L : LagFamily) :
    ContDiff ℝ 7 (fun w : (ℝ × (ℝ × ℝ)) × ℝ => HfIntegrand L w) := by
  have hbx := contDiff_fluxX L
  have hmap : ContDiff ℝ 7 (fun w : (ℝ × (ℝ × ℝ)) × ℝ =>
      ((w.1.1, -(L.X0) + (w.1.2.1 + L.X0) * w.2, w.1.2.2) : ℝ × ℝ × ℝ)) := by fun_prop
  have hcomp : ContDiff ℝ 7 (fun w : (ℝ × (ℝ × ℝ)) × ℝ =>
      bxf L w.1.1 (-(L.X0) + (w.1.2.1 + L.X0) * w.2) w.1.2.2) := by
    have h := hbx.comp hmap
    simpa [Function.comp_def] using h
  have hlin : ContDiff ℝ 7 (fun w : (ℝ × (ℝ × ℝ)) × ℝ => w.1.2.1 + L.X0) := by fun_prop
  have h := hlin.mul hcomp
  simpa only [HfIntegrand] using h

theorem contDiff_Hf (L : LagFamily) :
    ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) => Hf L z.1 z.2.1 z.2.2) := by
  have hG := contDiff_HfIntegrand L
  have h := contDiff_param_intervalIntegral (X := ℝ × (ℝ × ℝ)) (F := ℝ) 7
    (fun z σ => HfIntegrand L (z, σ)) hG (0 : ℝ) 1
  have hfun : (fun z : ℝ × (ℝ × ℝ) => Hf L z.1 z.2.1 z.2.2)
      = fun z => -(∫ σ in (0 : ℝ)..1, HfIntegrand L (z, σ)) := rfl
  rw [hfun]
  exact h.neg

/-! ## Elementary algebra of `symp` -/

lemma symp_zero_left (a : PS) : symp 0 a = 0 := by simp [symp]
lemma symp_zero_right (a : PS) : symp a 0 = 0 := by simp [symp]

/-! ## The flux components vanish where the family is constant -/

theorem bxf_btf_van (L : LagFamily) (τ x t : ℝ) (hx : L.X0 ≤ |x|) :
    bxf L τ x t = 0 ∧ btf L τ x t = 0 := by
  have hconst : (fun σ : ℝ => L.ℓ σ (x, t)) = fun _ : ℝ => stdZ x t :=
    funext (fun σ => L.std σ x t hx)
  have hd : deriv (fun σ : ℝ => L.ℓ σ (x, t)) τ = 0 := by
    rw [hconst]
    simp
  constructor
  · simp only [bxf, hd, symp_zero_left]
  · simp only [btf, hd, symp_zero_left]

/-! ## Slices are `C⁷` and differentiable -/

lemma contDiff_slice_fst (L : LagFamily) (x t : ℝ) :
    ContDiff ℝ 7 (fun σ : ℝ => L.ℓ σ (x, t)) := by
  have hmap : ContDiff ℝ 7 (fun σ : ℝ => ((σ, (x, t)) : ℝ × (ℝ × ℝ))) := by fun_prop
  have h1 : ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) => L.ℓ z.1 z.2) :=
    L.smooth.of_le (by norm_num)
  simpa only [Function.comp_def] using h1.comp hmap

lemma contDiff_slice_snd (L : LagFamily) (τ t : ℝ) :
    ContDiff ℝ 7 (fun y : ℝ => L.ℓ τ (y, t)) := by
  have hmap : ContDiff ℝ 7 (fun y : ℝ => ((τ, (y, t)) : ℝ × (ℝ × ℝ))) := by fun_prop
  have h1 : ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) => L.ℓ z.1 z.2) :=
    L.smooth.of_le (by norm_num)
  simpa only [Function.comp_def] using h1.comp hmap

lemma contDiff_slice_trd (L : LagFamily) (τ x : ℝ) :
    ContDiff ℝ 7 (fun s : ℝ => L.ℓ τ (x, s)) := by
  have hmap : ContDiff ℝ 7 (fun s : ℝ => ((τ, (x, s)) : ℝ × (ℝ × ℝ))) := by fun_prop
  have h1 : ContDiff ℝ 7 (fun z : ℝ × (ℝ × ℝ) => L.ℓ z.1 z.2) :=
    L.smooth.of_le (by norm_num)
  simpa only [Function.comp_def] using h1.comp hmap

lemma continuous_slice_snd (L : LagFamily) (τ t : ℝ) :
    Continuous (fun y : ℝ => L.ℓ τ (y, t)) :=
  (contDiff_slice_snd L τ t).continuous

/-! ## The primitive as an integral, and its `x`-derivative -/

theorem Hf_eq_integral (L : LagFamily) (τ x t : ℝ) :
    Hf L τ x t = -∫ u in (-(L.X0))..x, bxf L τ u t := by
  rw [Hf]
  congr 1
  have key : (∫ σ in (0 : ℝ)..1, (x + L.X0) * bxf L τ (-(L.X0) + (x + L.X0) * σ) t)
      = ∫ u in (-(L.X0))..x, bxf L τ u t := by
    by_cases hc : x + L.X0 = 0
    · have hx : x = -(L.X0) := by linarith [hc]
      rw [hc, hx]
      simp
    · rw [intervalIntegral.integral_const_mul]
      have h := intervalIntegral.integral_comp_add_mul
        (f := fun u : ℝ => bxf L τ u t) (a := (0 : ℝ)) (b := 1)
        (d := -(L.X0)) (c := x + L.X0) hc
      rw [h]
      have hlim : -(L.X0) + (x + L.X0) = x := by ring
      simp only [smul_eq_mul, mul_zero, add_zero, mul_one, hlim]
      field_simp
  simpa only [HfIntegrand] using key

theorem deriv_Hf_x (L : LagFamily) (τ x t : ℝ) :
    deriv (fun y => Hf L τ y t) x = -bxf L τ x t := by
  have hcont : Continuous (fun u : ℝ => bxf L τ u t) := by
    have hmap : Continuous (fun u : ℝ => ((τ, (u, t)) : ℝ × (ℝ × ℝ))) := by fun_prop
    have h1 : Continuous (fun z : ℝ × (ℝ × ℝ) => bxf L z.1 z.2.1 z.2.2) :=
      (contDiff_fluxX L).continuous
    exact h1.comp hmap
  have hfun : (fun y => Hf L τ y t) = fun y => -∫ u in (-(L.X0))..y, bxf L τ u t :=
    funext (fun y => Hf_eq_integral L τ y t)
  have hF : HasDerivAt (fun y : ℝ => ∫ u in (-(L.X0))..y, bxf L τ u t) (bxf L τ x t) x :=
    (hcont.integral_hasStrictDerivAt (-(L.X0)) x).hasDerivAt
  rw [hfun]
  exact (hF.neg).deriv

end
end Work.RPA3
