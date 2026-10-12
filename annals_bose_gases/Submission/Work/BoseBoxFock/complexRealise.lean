import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.BoseDict.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.complexRealise` — the **`ℂ`-linear** realisation, and the real/imaginary
# splitting that resolves the "real vs complex projection" mismatch of BF3c

## Why this module exists

The box → model bridge (`Work.BoseBoxFock.box_to_model`, BF3) has to turn a component of a
*real* box state into a *real* model vector `Ψ : Work.BoseB4.RealFock m`.  The corpus's
selection machinery (`slotProj`, `slotExact`, `fibre`) works with the **complex** orthogonal
projection onto `span_ℂ{e l}` (`PV e x y = Σ_l e l x * conj (e l y)`), so the components it
produces are complex functions lying in `span_ℂ{M_α}` — the *complexification* of the model's
image `span_ℝ{M_α}` (`boxRealise`).

The two are reconciled — with **no** rework of the sector algebra — by

* `boxRealiseC`, the `ℂ`-linear realisation of the complexified Fock space
  `CFock m = (Fin m →₀ ℕ) →₀ ℂ` (the same formula as `boxRealise`, over `ℂ`);
* `castFock`, `realPart`, `imagPart` — the real structure of `CFock m`
  (`Ψ = castFock (realPart Ψ) + I • castFock (imagPart Ψ)`);
* `boxRealiseC_eq_re_add_im` — **the real/imaginary splitting**
  `boxRealiseC e d Ψ = boxRealise e d (realPart Ψ) + I • boxRealise e d (imagPart Ψ)`,
  which produces the *two real* model vectors whose forms sum to the complex form;
* `boxRealiseC_sum_smul_modeProd` — surjectivity onto the `ℂ`-span of the degree-`d` mode
  products, i.e. *every* element of `span_ℂ{M_α : |α| = d}` is `boxRealiseC` of an explicit
  `CFock` vector.

**Consequence for the bridge** (recorded in `FINDING_BF3c_realcomplex_RESOLUTION.md`): if the
`ℂ`-selection produces a component `Θ ∈ span_ℂ{M_α}` of a real state, then `Θ = Θ₁ + i Θ₂`
with `Θ_i = boxRealise Ψ_i` for **real** model vectors `Ψ_i`, and for a **real** operator `A`
(all rows of `H2ndF` have real coefficients)

    re cIPn Θ (A Θ) = re cIPn Θ₁ (A Θ₁) + re cIPn Θ₂ (A Θ₂) ,
    re cIPn Θ Θ     = re cIPn Θ₁ Θ₁     + re cIPn Θ₂ Θ₂     ,

so the dictionary row for each `Ψ_i` gives `bomb Ψ_i (A_H Ψ_i) = re cIPn Θ_i (A Θ_i)` and the
*binary* selection over `i ∈ {1,2}` picks the one whose ratio is at most that of `Θ`.  No
`RealProjDefs`-style rewrite of `PV_algebra` / `slotProj_idem_and_comm` / `slotExact_comp` is
needed; the corpus's complex sector algebra is used verbatim.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

open Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The **complexified real Fock space**: finitely supported coefficient families on the
multi-indices, with complex coefficients.  It is the complexification of
`Work.BoseB4.RealFock m = (Fin m →₀ ℕ) →₀ ℝ`. -/
abbrev CFock (m : ℕ) : Type := (Fin m →₀ ℕ) →₀ ℂ

/-- The `ℝ`-linear embedding of the real Fock space as the "real" part of the complexified
one (coefficientwise coercion). -/
noncomputable def castFock {m : ℕ} (Ψ : Work.BoseB4.RealFock m) : CFock m :=
  Ψ.mapRange (fun r : ℝ => (r : ℂ)) (by simp)

/-- The real part of a complexified Fock vector. -/
noncomputable def realPart {m : ℕ} (Ψ : CFock m) : Work.BoseB4.RealFock m :=
  Ψ.mapRange Complex.re (by simp)

/-- The imaginary part of a complexified Fock vector. -/
noncomputable def imagPart {m : ℕ} (Ψ : CFock m) : Work.BoseB4.RealFock m :=
  Ψ.mapRange Complex.im (by simp)

@[simp] lemma castFock_apply {m : ℕ} (Ψ : Work.BoseB4.RealFock m) (α : Fin m →₀ ℕ) :
    castFock Ψ α = (Ψ α : ℂ) := rfl

@[simp] lemma realPart_apply {m : ℕ} (Ψ : CFock m) (α : Fin m →₀ ℕ) :
    realPart Ψ α = (Ψ α).re := rfl

@[simp] lemma imagPart_apply {m : ℕ} (Ψ : CFock m) (α : Fin m →₀ ℕ) :
    imagPart Ψ α = (Ψ α).im := rfl

/-- **The real structure of `CFock m`**: every complexified Fock vector is the sum of the
"casts" of its real and imaginary parts, with the imaginary one multiplied by `I`. -/
lemma eq_castFock_re_add_I_mul_im {m : ℕ} (Ψ : CFock m) :
    Ψ = castFock (realPart Ψ) + Complex.I • castFock (imagPart Ψ) := by
  ext α
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, castFock_apply,
    realPart_apply, imagPart_apply, smul_eq_mul]
  rw [show Complex.I * (((Ψ α).im : ℝ) : ℂ) = (((Ψ α).im : ℝ) : ℂ) * Complex.I from
    mul_comm _ _]
  exact (Complex.re_add_im (Ψ α)).symm

/-! ## The `ℂ`-linear realisation -/

/-- **The `ℂ`-linear realisation of the complexified Fock space on the box**: the same formula
as `Work.BoseDict.boxRealise`, but `ℂ`-linear in the coefficients.  On the degree-`d` part it
sends the monomial `x^α` to `(α!/√(d!)) • M_α`. -/
noncomputable def boxRealiseC {m : ℕ} (e : Fin m → Sp → ℂ) (d : ℕ) :
    CFock m →ₗ[ℂ] (Xn d → ℂ) :=
  Finsupp.lsum ℂ fun α : Fin m →₀ ℕ =>
    if α.sum (fun _ k => k) = d then
      LinearMap.toSpanSingleton ℂ (Xn d → ℂ)
        (((Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ) : ℝ) : ℂ) • modeProd e d α)
    else 0

/-- The defining value of `boxRealiseC` on a single monomial. -/
@[simp]
lemma boxRealiseC_single {m : ℕ} (e : Fin m → Sp → ℂ) (d : ℕ) (α : Fin m →₀ ℕ) (c : ℂ) :
    boxRealiseC e d (Finsupp.single α c)
      = c • ((if α.sum (fun _ k => k) = d then
          ((Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ) : ℝ) : ℂ) else 0)
        • modeProd e d α) := by
  classical
  rw [boxRealiseC, Finsupp.lsum_single]
  by_cases h : α.sum (fun _ k => k) = d
  · rw [if_pos h, if_pos h, LinearMap.toSpanSingleton_apply]
  · rw [if_neg h, if_neg h, LinearMap.zero_apply]
    simp

/-- `boxRealiseC` restricted to real coefficients is `boxRealise` (as a function). -/
lemma boxRealiseC_castFock {m d : ℕ} (e : Fin m → Sp → ℂ) (Ψ : Work.BoseB4.RealFock m) :
    boxRealiseC e d (castFock Ψ) = boxRealise e d Ψ := by
  classical
  funext x
  rw [boxRealiseC, boxRealise, Finsupp.lsum_apply, Finsupp.lsum_apply]
  rw [Finsupp.sum, Finsupp.sum, Finset.sum_apply, Finset.sum_apply]
  rw [show (castFock Ψ).support = Ψ.support from
    Finsupp.support_mapRange_of_injective (by simp) Ψ Complex.ofReal_injective]
  refine Finset.sum_congr rfl fun α _ => ?_
  by_cases h : α.sum (fun _ k => k) = d
  · rw [if_pos h, if_pos h]
    simp only [LinearMap.toSpanSingleton_apply, Pi.smul_apply, castFock_apply, smul_eq_mul]
    rw [Complex.real_smul, Complex.real_smul]
  · rw [if_neg h, if_neg h]
    simp

/-- **The expansion of `boxRealiseC` on the support of the vector.** -/
lemma boxRealiseC_eq_sum {m d : ℕ} {e : Fin m → Sp → ℂ} (Ψ : CFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) :
    boxRealiseC e d Ψ
      = fun x : Xn d => ∑ α ∈ Ψ.support,
          (Ψ α * ((Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ) : ℝ) : ℂ))
            * modeProd e d α x := by
  funext x
  rw [boxRealiseC, Finsupp.lsum_apply, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [if_pos (hΨ α hα), LinearMap.toSpanSingleton_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **THE REAL/IMAGINARY SPLITTING.**  The `ℂ`-linear realisation of a complexified Fock
vector is the `ℂ`-linear combination of the realisations of its real and imaginary parts. -/
theorem boxRealiseC_eq_re_add_im {m d : ℕ} (e : Fin m → Sp → ℂ) (Ψ : CFock m) :
    boxRealiseC e d Ψ
      = boxRealise e d (realPart Ψ) + Complex.I • boxRealise e d (imagPart Ψ) := by
  conv_lhs => rw [eq_castFock_re_add_I_mul_im (Ψ := Ψ)]
  rw [map_add, map_smul, boxRealiseC_castFock, boxRealiseC_castFock]

/-- **Surjectivity of `boxRealiseC` onto the `ℂ`-span of the degree-`d` mode products.**
A finite `ℂ`-combination `Σ_{α ∈ s} c α • M_α` of mode products of degree `d` (i.e. an element
of `Sym^d(V_ℂ)`, the `ℂ`-span of the model's degree-`d` image) is `boxRealiseC` of an explicit
complexified Fock vector.  Combined with `boxRealiseC_eq_re_add_im` this is the
"complex component ⟹ two real model vectors" step of the bridge. -/
theorem boxRealiseC_sum_smul_modeProd {m d : ℕ} (e : Fin m → Sp → ℂ)
    (s : Finset (Fin m →₀ ℕ)) (c : (Fin m →₀ ℕ) → ℂ)
    (hd : ∀ α ∈ s, α.sum (fun _ k => k) = d) :
    boxRealiseC e d
        (∑ α ∈ s, Finsupp.single α (c α * ((Real.sqrt (d.factorial : ℝ) : ℂ)
          / (Work.BoseB4.mfac α : ℂ))))
      = ∑ α ∈ s, c α • modeProd e d α := by
  classical
  rw [map_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [boxRealiseC_single, if_pos (hd α hα)]
  have hkey : (c α * ((Real.sqrt (d.factorial : ℝ) : ℂ) / (Work.BoseB4.mfac α : ℂ)))
        * (((Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ) : ℝ)) : ℂ) = c α := by
    have hmf : (Work.BoseB4.mfac α : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Work.BoseB4.BombSelf.mfac_pos α)
    have hd0 : (Real.sqrt (d.factorial : ℝ) : ℂ) ≠ 0 := by
      have hpos : (0 : ℝ) < d.factorial := by positivity
      have hne : Real.sqrt (d.factorial : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
      exact_mod_cast hne
    rw [show (((Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ) : ℝ)) : ℂ)
        = (Work.BoseB4.mfac α : ℂ) / (Real.sqrt (d.factorial : ℝ) : ℂ) from by
      push_cast; ring]
    field_simp
  rw [smul_smul, hkey]

end Work.BoseBoxFock
