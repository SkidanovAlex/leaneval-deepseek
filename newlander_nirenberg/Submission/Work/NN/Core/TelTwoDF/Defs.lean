/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The parameterised `(0,2)`-telescoping on a polydisc

This file sets up the *parameterised* version of the `(0,2)` `∂̄`-recursion of
`Submission/Work/NN/Final/twoRec.lean`: the cutoffs on the individual coordinates are no longer
the fixed library cutoffs (`openCut`, with the fixed radii `cutIn = 13/16`, `cutOut = 7/8`), but
the parametric cutoffs `Work.NN.Core.sharpCut a b`, equal to `1` on `‖ζ‖ ≤ a` and to `0` for
`b ≤ ‖ζ‖`.  The ratios of the radii can therefore be as close to `1` as needed.

The recursion processes the coordinates one at a time.  Writing

* `κ_s = kappa G s` for the cutoff in the `s`-th coordinate,
* `T_s = TL G s` for the Cauchy-type transform `dbarTransform (G.r s) s`, extended linearly to all
  data (`TL_eq` says that on continuous data it *is* that integral),

the state of the recursion is a family `uD G η m` of `(0,2)`-forms (`uD G η 0 = η`), with

  `uD G η (m+1)_{il} = (1 - κ_m) · uD G η m_{il}`                     for `i = m` or `l = m`,
  `uD G η (m+1)_{il} = (1 - κ_m) · uD G η m_{il} + T_m (κ̄_m · uD G η m_{il})`  otherwise,

where `κ̄_s = kappabar G s` is the `∂̄`-derivative of the cutoff `κ_s` in its own coordinate.  The
`(0,1)`-form produced at stage `s` is `uPsi G η s_l = T_s (κ_s · uD G η s_{sl})` and the solution
operator is `S2 G η_l = ∑_s uPsi G η s_l`.

The `(0,1)`-analogue of this construction (with the fixed cutoff `openCut`) is
`Work.CR.Flat.Cauchy.recU` in `Submission/Work/CR/Flat/Cauchy/openSolRec.lean`; the `(0,2)`
analogue with the fixed cutoff is `Work.NN.Final.uS2`.  The structural lemmas proved there
(`dbarCoord_uStep`, `uStep_closed_zero`, `dbarCoord_uPsi_sub`, `uS2_solves`) are adapted here to
the parametric cutoffs in `Submission/Work/NN/Core/TelTwoDF/Rec.lean` and the companion files.

## The key analytic point

Unlike the fixed-disc fibre potential, the *centred* transform `dbarTransform R s` has a kernel
`1/w` which is independent of the point and locally integrable, with a region of integration fixed
in the fibre variable; hence **all** derivatives pass through the integral sign and the transform
is bounded on `C^{k,α}` *without loss of derivatives*
(`Work.CR.Flat.Cauchy.holderNorm_dbarTransform_le`).  This is what makes the loss-free estimate
for the telescoping possible.

-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.openSolRec
import Submission.Work.CR.Flat.Cauchy.exists_dbar_solution_polydisc
import Submission.Work.NN.Core.sharpCut
import Submission.Work.NN.Final.RecULocal

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core.TelTwoDF

variable {n : ℕ}

/-- The geometric parameters of the parameterised `(0,2)`-telescoping: the inner radius `a` of the
cutoffs (they equal `1` for `‖z s‖ ≤ a s`), their outer radius `b` (they vanish for
`b s ≤ ‖z s‖`), and the radius `r` of the disc over which the Cauchy-type transform in the `s`-th
coordinate is integrated.  The last field `hbr : b s ≤ r s / 2` is exactly the support condition
required by `dbarTransform_dbarCoord_self`. -/
structure Geom (n : ℕ) where
  e : Fin n → ℝ
  a : Fin n → ℝ
  b : Fin n → ℝ
  r : Fin n → ℝ
  he : ∀ s, 0 < e s
  hea : ∀ s, e s < a s
  ha : ∀ s, 0 < a s
  hab : ∀ s, a s < b s
  hr : ∀ s, 0 < r s
  hbr : ∀ s, b s ≤ r s / 2

namespace Geom

variable {n : ℕ} (G : Geom n)

lemma a_nonneg (s : Fin n) : 0 ≤ G.a s := (G.ha s).le

lemma b_pos (s : Fin n) : 0 < G.b s := lt_trans (G.ha s) (G.hab s)

lemma r_pos (s : Fin n) : 0 < G.r s := G.hr s

lemma a_lt_r (s : Fin n) : G.a s < G.r s := by
  have h := G.hbr s
  have h2 := G.hab s
  have h3 := G.hr s
  linarith

lemma e_lt_r (s : Fin n) : G.e s < G.r s := by
  have h := G.hbr s
  have h2 := G.hab s
  have h3 := G.hea s
  have h4 := G.hr s
  linarith

lemma e_lt_b (s : Fin n) : G.e s < G.b s := lt_trans (G.hea s) (G.hab s)

end Geom

/-- The cutoff in the `s`-th coordinate. -/
def kappa {n : ℕ} (G : Geom n) (s : Fin n) : (Fin n → ℂ) → ℂ :=
  fun z => Work.NN.Core.sharpCut (G.a s) (G.b s) (z s)

/-- The `∂̄`-derivative of the cutoff in its own coordinate, as a function of `ℂⁿ`. -/
def kappabar {n : ℕ} (G : Geom n) (s : Fin n) : (Fin n → ℂ) → ℂ :=
  fun z => Work.CR.Flat.dbarC (Work.NN.Core.sharpCut (G.a s) (G.b s)) (z s)

lemma contDiff_kappa (G : Geom n) (s : Fin n) : ContDiff ℝ ∞ (kappa G s) :=
  (Work.NN.Core.contDiff_sharpCut (a := G.a s) (b := G.b s)).comp (contDiff_apply ℝ ℂ s)

lemma kappa_eq_one (G : Geom n) (s : Fin n) {z : Fin n → ℂ} (h : ‖z s‖ ≤ G.a s) :
    kappa G s z = 1 :=
  Work.NN.Core.sharpCut_eq_one (G.a_nonneg s) (G.hab s) h

lemma kappa_eq_zero (G : Geom n) (s : Fin n) {z : Fin n → ℂ} (h : G.b s ≤ ‖z s‖) :
    kappa G s z = 0 :=
  Work.NN.Core.sharpCut_eq_zero (G.a_nonneg s) (G.hab s) h

lemma norm_kappa_le_one (G : Geom n) (s : Fin n) (z : Fin n → ℂ) : ‖kappa G s z‖ ≤ 1 :=
  Work.NN.Core.norm_sharpCut_le_one (G.a s) (G.b s) (z s)

/-- The `∂̄` of the parametric cutoff is smooth. -/
lemma contDiff_dbarC_sharpCut_aux {a b : ℝ} :
    ContDiff ℝ ∞ (Work.CR.Flat.dbarC (Work.NN.Core.sharpCut a b)) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ (Work.NN.Core.sharpCut a b)) :=
    (Work.NN.Core.contDiff_sharpCut (a := a) (b := b)).fderiv_right (m := ∞) le_rfl
  have h1 : ContDiff ℝ ∞ (fun z : ℂ => fderiv ℝ (Work.NN.Core.sharpCut a b) z 1) :=
    hfd.clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ (fun z : ℂ => fderiv ℝ (Work.NN.Core.sharpCut a b) z Complex.I) :=
    hfd.clm_apply contDiff_const
  rw [show Work.CR.Flat.dbarC (Work.NN.Core.sharpCut a b) = fun z => (1 / 2 : ℂ) *
      ((fderiv ℝ (Work.NN.Core.sharpCut a b) z) 1
        + Complex.I * (fderiv ℝ (Work.NN.Core.sharpCut a b) z) Complex.I) from rfl]
  exact contDiff_const.mul (h1.add (contDiff_const.mul hI))

lemma contDiff_kappabar (G : Geom n) (s : Fin n) : ContDiff ℝ ∞ (kappabar G s) :=
  (contDiff_dbarC_sharpCut_aux (a := G.a s) (b := G.b s)).comp (contDiff_apply ℝ ℂ s)


/-! ## The `∂̄`-derivative of the parametric cutoff -/

/-- The radial profile `sharpCutReal a b` is constant on `(-∞, a²]`, so its derivative vanishes
there. -/
lemma deriv_sharpCutReal_eq_zero_of_le {a b s : ℝ} (ha : 0 ≤ a) (hab : a < b) (hs : s ≤ a ^ 2) :
    deriv (Work.NN.Core.sharpCutReal a b) s = 0 := by
  have hdiff : DifferentiableAt ℝ (Work.NN.Core.sharpCutReal a b) s :=
    ((Work.NN.Core.contDiff_sharpCutReal (a := a) (b := b)).differentiable (by simp)) s
  have hu : UniqueDiffWithinAt ℝ (Iic s) s := uniqueDiffWithinAt_Iic s
  have h1 : HasDerivWithinAt (Work.NN.Core.sharpCutReal a b) 0 (Iic s) s :=
    (hasDerivWithinAt_const s (Iic s) (1 : ℝ)).congr
      (fun x hx => Work.NN.Core.sharpCutReal_eq_one ha hab (le_trans hx hs))
      (Work.NN.Core.sharpCutReal_eq_one ha hab hs)
  have h2 : HasDerivWithinAt (Work.NN.Core.sharpCutReal a b)
      (deriv (Work.NN.Core.sharpCutReal a b) s) (Iic s) s :=
    hdiff.hasDerivAt.hasDerivWithinAt
  rw [← h2.derivWithin hu, h1.derivWithin hu]

/-- The radial profile `sharpCutReal a b` is constant on `[b², ∞)`, so its derivative vanishes
there. -/
lemma deriv_sharpCutReal_eq_zero_of_ge {a b s : ℝ} (ha : 0 ≤ a) (hab : a < b) (hs : b ^ 2 ≤ s) :
    deriv (Work.NN.Core.sharpCutReal a b) s = 0 := by
  have hdiff : DifferentiableAt ℝ (Work.NN.Core.sharpCutReal a b) s :=
    ((Work.NN.Core.contDiff_sharpCutReal (a := a) (b := b)).differentiable (by simp)) s
  have hu : UniqueDiffWithinAt ℝ (Ici s) s := uniqueDiffWithinAt_Ici s
  have h1 : HasDerivWithinAt (Work.NN.Core.sharpCutReal a b) 0 (Ici s) s :=
    (hasDerivWithinAt_const s (Ici s) (0 : ℝ)).congr
      (fun x hx => Work.NN.Core.sharpCutReal_eq_zero ha hab (le_trans hs hx))
      (Work.NN.Core.sharpCutReal_eq_zero ha hab hs)
  have h2 : HasDerivWithinAt (Work.NN.Core.sharpCutReal a b)
      (deriv (Work.NN.Core.sharpCutReal a b) s) (Ici s) s :=
    hdiff.hasDerivAt.hasDerivWithinAt
  rw [← h2.derivWithin hu, h1.derivWithin hu]

/-- The `∂̄`-derivative of a radial cutoff in terms of its radial profile:
`∂̄ (sharpCut a b) ζ = profile'(‖ζ‖²) · ζ`. -/
lemma dbarC_sharpCut_eq_aux {a b : ℝ} (ζ : ℂ) :
    Work.CR.Flat.dbarC (Work.NN.Core.sharpCut a b) ζ
      = ((deriv (Work.NN.Core.sharpCutReal a b) (Complex.normSq ζ) : ℝ) : ℂ) * ζ := by
  rw [show Work.NN.Core.sharpCut a b
      = fun w : ℂ => (Work.NN.Core.sharpCutReal a b (Complex.normSq w) : ℂ) from rfl]
  exact Work.CR.Flat.dbarC_comp_normSq_aux (Work.NN.Core.sharpCutReal a b)
    ((Work.NN.Core.contDiff_sharpCutReal (a := a) (b := b)).differentiable (by simp)) ζ

lemma kappabar_eq_zero_of_norm_le (G : Geom n) (s : Fin n) {z : Fin n → ℂ}
    (h : ‖z s‖ ≤ G.a s) : kappabar G s z = 0 := by
  rw [kappabar, dbarC_sharpCut_eq_aux]
  have hs : Complex.normSq (z s) ≤ G.a s ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [deriv_sharpCutReal_eq_zero_of_le (G.a_nonneg s) (G.hab s) hs, Complex.ofReal_zero,
    zero_mul]

lemma kappabar_eq_zero_of_ge (G : Geom n) (s : Fin n) {z : Fin n → ℂ}
    (h : G.b s ≤ ‖z s‖) : kappabar G s z = 0 := by
  rw [kappabar, dbarC_sharpCut_eq_aux]
  have hs : G.b s ^ 2 ≤ Complex.normSq (z s) := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (G.b_pos s).le h 2
  rw [deriv_sharpCutReal_eq_zero_of_ge (G.a_nonneg s) (G.hab s) hs, Complex.ofReal_zero,
    zero_mul]

/-! ## The transform as a linear map -/

/-- The continuous functions on `ℂⁿ`, as a subspace of all functions. -/
def contSub (n : ℕ) : Submodule ℝ ((Fin n → ℂ) → ℂ) where
  carrier := {g | Continuous g}
  zero_mem' := continuous_zero
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c _ hx => hx.const_smul c

/-- The Cauchy-type transform in the `s`-th coordinate, as a linear map on continuous data. -/
noncomputable def TLcont (G : Geom n) (s : Fin n) :
    contSub n →ₗ[ℝ] ((Fin n → ℂ) → ℂ) where
  toFun := fun g => Work.CR.Flat.Cauchy.dbarTransform (G.r s) s g.1
  map_add' := by
    intro g h
    funext z
    exact Work.NN.Final.dbarTransform_add s g.2 h.2 z
  map_smul' := by
    intro c g
    funext z
    exact Work.NN.Final.dbarTransform_smul s c g.2 z

/-- The Cauchy-type transform in the `s`-th coordinate, extended linearly to all data. -/
noncomputable def TL (G : Geom n) (s : Fin n) :
    ((Fin n → ℂ) → ℂ) →ₗ[ℝ] ((Fin n → ℂ) → ℂ) :=
  (LinearMap.exists_extend (TLcont G s)).choose

lemma TL_comp (G : Geom n) (s : Fin n) :
    (TL G s).comp (contSub n).subtype = TLcont G s :=
  (LinearMap.exists_extend (TLcont G s)).choose_spec

/-- On continuous data the linear extension `TL` agrees with the Cauchy-type integral. -/
lemma TL_eq (G : Geom n) (s : Fin n) {g : (Fin n → ℂ) → ℂ} (hg : Continuous g) :
    TL G s g = Work.CR.Flat.Cauchy.dbarTransform (G.r s) s g := by
  have h := DFunLike.congr_fun (TL_comp G s) (⟨g, hg⟩ : contSub n)
  simpa [LinearMap.comp_apply, TLcont] using h

/-! ## The recursion -/

/-- One step of the parameterised `(0,2)`-recursion in the `s`-th coordinate. -/
noncomputable def uStep (G : Geom n) (s : Fin n)
    (D : Fin n → Fin n → (Fin n → ℂ) → ℂ) : Fin n → Fin n → (Fin n → ℂ) → ℂ :=
  fun i l z => (1 - kappa G s z) * D i l z
    + (if i = s ∨ l = s then 0 else TL G s (fun y => kappabar G s y * D i l y) z)

/-- The `(0,2)`-data at stage `m` of the recursion. -/
noncomputable def uD (G : Geom n) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) : ℕ →
    Fin n → Fin n → (Fin n → ℂ) → ℂ
  | 0 => η
  | m + 1 => if h : m < n then uStep G ⟨m, h⟩ (uD G η m) else uD G η m

/-- The `(0,1)`-form produced at stage `s`. -/
noncomputable def uPsi (G : Geom n) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) (s : Fin n) :
    Fin n → (Fin n → ℂ) → ℂ :=
  fun l => TL G s (fun y => kappa G s y * uD G η (s : ℕ) s l y)

/-- The solution operator produced by the recursion. -/
noncomputable def S2 (G : Geom n) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    Fin n → (Fin n → ℂ) → ℂ :=
  fun l => ∑ s : Fin n, uPsi G η s l

@[simp] lemma uStep_apply (G : Geom n) (s : Fin n)
    (D : Fin n → Fin n → (Fin n → ℂ) → ℂ) (i l : Fin n) (z : Fin n → ℂ) :
    uStep G s D i l z = (1 - kappa G s z) * D i l z
      + (if i = s ∨ l = s then 0 else TL G s (fun y => kappabar G s y * D i l y) z) := rfl

@[simp] lemma uD_zero (G : Geom n) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    uD G η 0 = η := rfl

lemma uD_succ (G : Geom n) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) (m : ℕ) :
    uD G η (m + 1) = if h : m < n then uStep G ⟨m, h⟩ (uD G η m) else uD G η m := rfl

lemma uD_succ_of_lt (G : Geom n) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) {m : ℕ}
    (h : m < n) : uD G η (m + 1) = uStep G ⟨m, h⟩ (uD G η m) := by
  rw [uD_succ]; simp [h]

@[simp] lemma uPsi_apply (G : Geom n) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) (s : Fin n)
    (l : Fin n) (z : Fin n → ℂ) :
    uPsi G η s l z = TL G s (fun y => kappa G s y * uD G η (s : ℕ) s l y) z := rfl

@[simp] lemma S2_apply (G : Geom n) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) (l : Fin n)
    (z : Fin n → ℂ) : S2 G η l z = ∑ s : Fin n, uPsi G η s l z := by
  simp only [S2, Finset.sum_apply]

/-! ## Smoothness of one step -/

/-- The data of one step of the recursion are continuous whenever the previous stage is. -/
lemma contDiff_uStep (G : Geom n) {s : Fin n}
    {D : Fin n → Fin n → (Fin n → ℂ) → ℂ} (hD : ∀ i l, ContDiff ℝ 1 (D i l)) (i l : Fin n) :
    ContDiff ℝ 1 (uStep G s D i l) := by
  by_cases hc : i = s ∨ l = s
  · have hfun : uStep G s D i l = fun z => (1 - kappa G s z) * D i l z := by
      funext z; rw [uStep_apply, if_pos hc]; ring
    rw [hfun]
    exact ((contDiff_const.sub (contDiff_kappa G s)).of_le (by exact_mod_cast le_top)).mul (hD i l)
  · have hfun : uStep G s D i l = fun z => (1 - kappa G s z) * D i l z
        + TL G s (fun y => kappabar G s y * D i l y) z := by
      funext z; rw [uStep_apply, if_neg hc]
    rw [hfun]
    have hk : Continuous (fun y : Fin n → ℂ => kappabar G s y * D i l y) :=
      (((contDiff_kappabar G s).of_le (by exact_mod_cast le_top)).mul (hD i l)).continuous
    rw [TL_eq G s hk]
    refine ContDiff.add (((contDiff_const.sub (contDiff_kappa G s)).of_le
      (by exact_mod_cast le_top)).mul (hD i l)) ?_
    exact Work.CR.Flat.Cauchy.contDiff_dbarTransform (b := G.b s) (by
        have := G.hbr s; have := G.hab s; have := G.hr s; linarith) s 1
      (((contDiff_kappabar G s).of_le (by exact_mod_cast le_top)).mul (hD i l))
      (fun y hy => by
        rw [kappabar_eq_zero_of_ge G s hy, zero_mul])

end Work.NN.Core.TelTwoDF
