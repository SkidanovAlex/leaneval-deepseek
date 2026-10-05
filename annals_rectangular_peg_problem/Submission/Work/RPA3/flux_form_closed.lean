import Mathlib
import Submission.Work.RPA3.Defs
import Submission.Work.RPA3.Symp
import Submission.Work.RPA3.hasDerivAt_symp
import Submission.Work.RPA3.deriv_deriv_swap

/-!
# RPA3, D1: closedness of the flux form

The flux form of a family `(τ,x,t) ↦ ℓ τ x t` of Lagrangians is `β = ω(∂_τℓ, ·)`.  Along the
family it is closed, i.e. `∂_x β(∂_tℓ) = ∂_t β(∂_xℓ)`; this is the statement proved here, and it is
what makes `β` exact on the strip, giving the flux primitive `FluxPrimitive` (D1).

The proof is the standard one.  Writing `u = ∂_τℓ`, `v = ∂_xℓ`, `w = ∂_tℓ` and using that `ω` is
bilinear (`Work.RPA3.hasDerivAt_symp`),
`∂_x ω(u,w) = ω(∂_x∂_τℓ, w) + ω(u, ∂_x∂_tℓ)` and
`∂_t ω(u,v) = ω(∂_t∂_τℓ, v) + ω(u, ∂_t∂_xℓ)`.
By Clairaut's theorem for the `C²` map `ℓ` (`Work.RPA3.deriv_deriv_swap`) the mixed partials
`∂_τ∂_xℓ`, `∂_τ∂_tℓ` and `∂_x∂_tℓ` may be reordered, so the two expressions differ by
`ω(∂_τ∂_xℓ, w) - ω(∂_τ∂_tℓ, v)`, which (by antisymmetry of `ω`) is
`∂_τ ω(v, w) = ∂_τ ω(∂_xℓ, ∂_tℓ) = 0`, the last step being the Lagrangian hypothesis.  The two
analytic inputs are: the Leibniz rule `hasDerivAt_symp` for the bilinear form `ω` and the
Schwarz/Clairaut theorem `deriv_deriv_swap`; the smoothness facts they need (the partial
derivatives of a `C²` family are again `C¹`) are supplied by `ContDiff.fderiv` below.
-/

namespace Work.RPA3

open scoped ContDiff

set_option autoImplicit false

/-! ## ContDiff-regularity of the partial derivatives of the family

If `(τ,x,t) ↦ ℓ τ x t` is `C²`, then each of the three partial derivative maps obtained by
differentiating one slot at a fixed value, as a function of the remaining two slots, is `C¹`.
This is `ContDiff.fderiv`: the partial derivative in one variable of a jointly `C^{n+1}` map of
two variables is jointly `C^n`. -/

/-- `z ↦ ∂_τℓ(τ, z)` is `C¹`. -/
lemma contDiff_partial_fst (ℓ : ℝ → ℝ → ℝ → PS)
    (hℓ : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ => ℓ z.1 z.2.1 z.2.2)) (τ : ℝ) :
    ContDiff ℝ 1 (fun z : ℝ × ℝ => deriv (fun σ => ℓ σ z.1 z.2) τ) := by
  have hperm : ContDiff ℝ 2 (fun w : (ℝ × ℝ) × ℝ => (w.2, w.1.1, w.1.2)) := by fun_prop
  have hL' : ContDiff ℝ 2 (Function.uncurry (fun (z : ℝ × ℝ) (σ : ℝ) => ℓ σ z.1 z.2)) := by
    show ContDiff ℝ 2 (fun w : (ℝ × ℝ) × ℝ => ℓ w.2 w.1.1 w.1.2)
    exact hℓ.comp hperm
  have h := ContDiff.fderiv (𝕜 := ℝ) (n := (1 : ENat)) (m := (2 : ENat))
      (f := fun (z : ℝ × ℝ) (σ : ℝ) => ℓ σ z.1 z.2) (g := fun _ : ℝ × ℝ => τ)
      hL' contDiff_const (by norm_num)
  have h2 : ContDiff ℝ 1 (fun z : ℝ × ℝ => (fderiv ℝ (fun σ => ℓ σ z.1 z.2) τ) 1) :=
    ContDiff.clm_apply h contDiff_const
  simpa only [fderiv_apply_one_eq_deriv] using h2

/-- `z ↦ ∂_xℓ(x₀, z)` is `C¹`. -/
lemma contDiff_partial_snd (ℓ : ℝ → ℝ → ℝ → PS)
    (hℓ : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ => ℓ z.1 z.2.1 z.2.2)) (x : ℝ) :
    ContDiff ℝ 1 (fun z : ℝ × ℝ => deriv (fun σ => ℓ z.1 σ z.2) x) := by
  have hperm : ContDiff ℝ 2 (fun w : (ℝ × ℝ) × ℝ => (w.1.1, w.2, w.1.2)) := by fun_prop
  have hL' : ContDiff ℝ 2 (Function.uncurry (fun (z : ℝ × ℝ) (σ : ℝ) => ℓ z.1 σ z.2)) := by
    show ContDiff ℝ 2 (fun w : (ℝ × ℝ) × ℝ => ℓ w.1.1 w.2 w.1.2)
    exact hℓ.comp hperm
  have h := ContDiff.fderiv (𝕜 := ℝ) (n := (1 : ENat)) (m := (2 : ENat))
      (f := fun (z : ℝ × ℝ) (σ : ℝ) => ℓ z.1 σ z.2) (g := fun _ : ℝ × ℝ => x)
      hL' contDiff_const (by norm_num)
  have h2 : ContDiff ℝ 1 (fun z : ℝ × ℝ => (fderiv ℝ (fun σ => ℓ z.1 σ z.2) x) 1) :=
    ContDiff.clm_apply h contDiff_const
  simpa only [fderiv_apply_one_eq_deriv] using h2

/-- `z ↦ ∂_tℓ(z, t₀)` is `C¹`. -/
lemma contDiff_partial_trd (ℓ : ℝ → ℝ → ℝ → PS)
    (hℓ : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ => ℓ z.1 z.2.1 z.2.2)) (t : ℝ) :
    ContDiff ℝ 1 (fun z : ℝ × ℝ => deriv (fun σ => ℓ z.1 z.2 σ) t) := by
  have hperm : ContDiff ℝ 2 (fun w : (ℝ × ℝ) × ℝ => (w.1.1, w.1.2, w.2)) := by fun_prop
  have hL' : ContDiff ℝ 2 (Function.uncurry (fun (z : ℝ × ℝ) (σ : ℝ) => ℓ z.1 z.2 σ)) := by
    show ContDiff ℝ 2 (fun w : (ℝ × ℝ) × ℝ => ℓ w.1.1 w.1.2 w.2)
    exact hℓ.comp hperm
  have h := ContDiff.fderiv (𝕜 := ℝ) (n := (1 : ENat)) (m := (2 : ENat))
      (f := fun (z : ℝ × ℝ) (σ : ℝ) => ℓ z.1 z.2 σ) (g := fun _ : ℝ × ℝ => t)
      hL' contDiff_const (by norm_num)
  have h2 : ContDiff ℝ 1 (fun z : ℝ × ℝ => (fderiv ℝ (fun σ => ℓ z.1 z.2 σ) t) 1) :=
    ContDiff.clm_apply h contDiff_const
  simpa only [fderiv_apply_one_eq_deriv] using h2

/-! ## Smoothness of the two-variable maps to which Clairaut is applied -/

/-- `(σ, y) ↦ ℓ σ y t` is `C²` at `(τ, x)`. -/
lemma contDiffAt_pair_thd (ℓ : ℝ → ℝ → ℝ → PS)
    (hℓ : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ => ℓ z.1 z.2.1 z.2.2)) (τ x t : ℝ) :
    ContDiffAt ℝ 2 (fun z : ℝ × ℝ => ℓ z.1 z.2 t) (τ, x) := by
  have : ContDiff ℝ 2 (fun z : ℝ × ℝ => ℓ z.1 z.2 t) := by
    have hperm : ContDiff ℝ 2 (fun w : ℝ × ℝ => (w.1, w.2, t)) := by fun_prop
    exact hℓ.comp hperm
  exact this.contDiffAt

/-- `σ ↦ ℓ σ y t` at fixed `(y, t)` is `C²` at `(x, t)`. -/
lemma contDiffAt_pair_fst (ℓ : ℝ → ℝ → ℝ → PS)
    (hℓ : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ => ℓ z.1 z.2.1 z.2.2)) (τ x t : ℝ) :
    ContDiffAt ℝ 2 (fun z : ℝ × ℝ => ℓ τ z.1 z.2) (x, t) := by
  have : ContDiff ℝ 2 (fun z : ℝ × ℝ => ℓ τ z.1 z.2) := by
    have hperm : ContDiff ℝ 2 (fun w : ℝ × ℝ => (τ, w.1, w.2)) := by fun_prop
    exact hℓ.comp hperm
  exact this.contDiffAt

/-- `(σ, s) ↦ ℓ σ x s` is `C²` at `(τ, t)`. -/
lemma contDiffAt_pair_snd (ℓ : ℝ → ℝ → ℝ → PS)
    (hℓ : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ => ℓ z.1 z.2.1 z.2.2)) (τ x t : ℝ) :
    ContDiffAt ℝ 2 (fun z : ℝ × ℝ => ℓ z.1 x z.2) (τ, t) := by
  have : ContDiff ℝ 2 (fun z : ℝ × ℝ => ℓ z.1 x z.2) := by
    have hperm : ContDiff ℝ 2 (fun w : ℝ × ℝ => (w.1, x, w.2)) := by fun_prop
    exact hℓ.comp hperm
  exact this.contDiffAt

/-- Differentiability of `y ↦ F (y, q)` from `F` being `C¹`. -/
lemma differentiableAt_comp_fst {F : ℝ × ℝ → PS} (hF : ContDiff ℝ 1 F) (p q : ℝ) :
    DifferentiableAt ℝ (fun y => F (y, q)) p :=
  ((hF.differentiable (by norm_num)).differentiableAt).comp p (by fun_prop)

/-- Differentiability of `y ↦ F (q, y)` from `F` being `C¹`. -/
lemma differentiableAt_comp_snd {F : ℝ × ℝ → PS} (hF : ContDiff ℝ 1 F) (p q : ℝ) :
    DifferentiableAt ℝ (fun y => F (q, y)) p :=
  ((hF.differentiable (by norm_num)).differentiableAt).comp p (by fun_prop)

/-- Leibniz rule for `symp`, in `deriv` form. -/
lemma deriv_symp {u v : ℝ → PS} {x : ℝ} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) :
    deriv (fun y => symp (u y) (v y)) x = symp (deriv u x) (v x) + symp (u x) (deriv v x) :=
  (hasDerivAt_symp hu.hasDerivAt hv.hasDerivAt).deriv

/-- **D1, closedness.**  For a Lagrangian family `(τ,x,t) ↦ ℓ τ x t` (Lagrangian for every `τ`), the
flux form `β = ω(∂_τℓ, ·)` is closed: `∂_x β(∂_t) = ∂_t β(∂_x)`.

Proof: expand both sides with the product rule,
`∂_x β(∂_t) = ω(∂_x∂_τℓ, ∂_tℓ) + ω(∂_τℓ, ∂_x∂_tℓ)` and
`∂_t β(∂_x) = ω(∂_t∂_τℓ, ∂_xℓ) + ω(∂_τℓ, ∂_t∂_xℓ)`; the mixed partials `∂_x∂_t = ∂_t∂_x` cancel
(Clairaut for a `C²` map, `ContDiffAt.isSymmSndFDerivAt`), leaving
`∂_x β(∂_t) - ∂_t β(∂_x) = ∂_τ (ω(∂_xℓ, ∂_tℓ)) = 0` by the Lagrangian hypothesis.  `symp` is
bilinear, `Work.RPA3.symp_add_left` etc. in `Submission.Work.RPA3.Symp` provide the bilinearity. -/
theorem flux_form_closed (ℓ : ℝ → ℝ → ℝ → Work.RPA3.PS)
    (hℓ : ContDiff ℝ 2 (fun z : ℝ × ℝ × ℝ => ℓ z.1 z.2.1 z.2.2))
    (hlag : ∀ τ x t, Work.RPA3.symp (deriv (fun y => ℓ τ y t) x) (deriv (fun s => ℓ τ x s) t) = 0)
    (τ x t : ℝ) :
    deriv (fun y => Work.RPA3.symp (deriv (fun σ => ℓ σ y t) τ) (deriv (fun s => ℓ τ y s) t)) x
      = deriv (fun s => Work.RPA3.symp (deriv (fun σ => ℓ σ x s) τ) (deriv (fun y => ℓ τ y s) x)) t := by
  have hFst := contDiff_partial_fst ℓ hℓ τ
  have hSnd := contDiff_partial_snd ℓ hℓ x
  have hTrd := contDiff_partial_trd ℓ hℓ t
  have hA : DifferentiableAt ℝ (fun y => deriv (fun σ => ℓ σ y t) τ) x :=
    differentiableAt_comp_fst hFst x t
  have hB : DifferentiableAt ℝ (fun y => deriv (fun s => ℓ τ y s) t) x :=
    differentiableAt_comp_snd hTrd x τ
  have hC : DifferentiableAt ℝ (fun s => deriv (fun σ => ℓ σ x s) τ) t :=
    differentiableAt_comp_snd hFst t x
  have hD : DifferentiableAt ℝ (fun s => deriv (fun y => ℓ τ y s) x) t :=
    differentiableAt_comp_snd hSnd t τ
  have hE : DifferentiableAt ℝ (fun σ => deriv (fun y => ℓ σ y t) x) τ :=
    differentiableAt_comp_fst hSnd τ t
  have hF : DifferentiableAt ℝ (fun σ => deriv (fun s => ℓ σ x s) t) τ :=
    differentiableAt_comp_fst hTrd τ x
  have hLHS : deriv (fun y => symp (deriv (fun σ => ℓ σ y t) τ) (deriv (fun s => ℓ τ y s) t)) x
      = symp (deriv (fun y => deriv (fun σ => ℓ σ y t) τ) x) (deriv (fun s => ℓ τ x s) t)
        + symp (deriv (fun σ => ℓ σ x t) τ) (deriv (fun y => deriv (fun s => ℓ τ y s) t) x) :=
    deriv_symp hA hB
  have hRHS : deriv (fun s => symp (deriv (fun σ => ℓ σ x s) τ) (deriv (fun y => ℓ τ y s) x)) t
      = symp (deriv (fun s => deriv (fun σ => ℓ σ x s) τ) t) (deriv (fun y => ℓ τ y t) x)
        + symp (deriv (fun σ => ℓ σ x t) τ) (deriv (fun s => deriv (fun y => ℓ τ y s) x) t) :=
    deriv_symp hC hD
  have hS1 : deriv (fun y => deriv (fun σ => ℓ σ y t) τ) x
      = deriv (fun σ => deriv (fun y => ℓ σ y t) x) τ :=
    deriv_deriv_swap (G := fun w : ℝ × ℝ => ℓ w.1 w.2 t) (contDiffAt_pair_thd ℓ hℓ τ x t)
  have hS2 : deriv (fun s => deriv (fun σ => ℓ σ x s) τ) t
      = deriv (fun σ => deriv (fun s => ℓ σ x s) t) τ :=
    deriv_deriv_swap (G := fun w : ℝ × ℝ => ℓ w.1 x w.2) (contDiffAt_pair_snd ℓ hℓ τ x t)
  have hS3 : deriv (fun s => deriv (fun y => ℓ τ y s) x) t
      = deriv (fun y => deriv (fun s => ℓ τ y s) t) x :=
    deriv_deriv_swap (G := fun w : ℝ × ℝ => ℓ τ w.1 w.2) (contDiffAt_pair_fst ℓ hℓ τ x t)
  have hZ0 : (fun σ : ℝ => symp (deriv (fun y => ℓ σ y t) x) (deriv (fun s => ℓ σ x s) t))
      = fun _ : ℝ => (0 : ℝ) := by
    funext σ
    exact hlag σ x t
  have hZ1 : deriv (fun σ : ℝ => symp (deriv (fun y => ℓ σ y t) x)
      (deriv (fun s => ℓ σ x s) t)) τ = 0 := by
    rw [hZ0]
    simp
  have hZ2 : deriv (fun σ : ℝ => symp (deriv (fun y => ℓ σ y t) x)
        (deriv (fun s => ℓ σ x s) t)) τ
      = symp (deriv (fun σ => deriv (fun y => ℓ σ y t) x) τ) (deriv (fun s => ℓ τ x s) t)
        + symp (deriv (fun y => ℓ τ y t) x) (deriv (fun σ => deriv (fun s => ℓ σ x s) t) τ) :=
    deriv_symp hE hF
  have hP : symp (deriv (fun σ => deriv (fun y => ℓ σ y t) x) τ) (deriv (fun s => ℓ τ x s) t)
      = symp (deriv (fun σ => deriv (fun s => ℓ σ x s) t) τ) (deriv (fun y => ℓ τ y t) x) := by
    have hh := hZ2.symm.trans hZ1
    rw [symp_antisymm (deriv (fun y => ℓ τ y t) x)
      (deriv (fun σ => deriv (fun s => ℓ σ x s) t) τ)] at hh
    linarith
  rw [hLHS, hRHS, hS1, hS2, hS3.symm]
  linarith [hP]

end Work.RPA3
