import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Work.BoseFixB2.Polar.fsT_parallelogram
import Submission.Work.BoseFixB2.Polar.momForm_parallelogram
import Submission.Work.BoseFixB2.Polar.neuFrac_parallelogram
import Submission.Work.BoseFixB2.Recomb.hpol_abstract
import Submission.Work.BoseKinLoc.Word.fsT_const_mul
import Submission.Work.BoseKinLoc.Word.fsT_nonneg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Recomb.fsT_hpol`

**The one-body localised kinetic word of FS `eq:DefT` is homogeneously polarised.**

For every real `t` and smooth one-body states `f, g`,

`fsT ℓ d s ε_T b u (t·f + g) − fsT ℓ d s εT b u (t·f − g)
   = t · (fsT ℓ d s εT b u (f + g) − fsT ℓ d s εT b u (f − g))`.

This is the `hpol` hypothesis of `Work.BoseFixB2.Polar.par_polarisation_hpol`, i.e. the
statement that `fsT` is the diagonal of a real-bilinear form; it is what allows the box word
`boxFormB` to be polarised over a sector family (FS §6).

## Route

`fsT = neuWord + gapWord + momWord + mainWord` (`Work.BoseKinLoc.fsT_eq_sum`), and each summand
is handled separately.  Each of the four is a **nonnegative quadratic form** on smooth states,
so its polar form is `ℝ`-homogeneous by `Work.BoseFixB2.Recomb.hpol_of_par_nonneg_smooth`
(nonnegativity rules out the derivation-of-`ℝ` obstruction recorded in
`Work.BoseFixB2.Polar.par_polarisation`):

* `neuFrac` — parallelogram `Work.BoseFixB2.Polar.neuFrac_parallelogram`, `2`-homogeneity
  `Work.BoseKinLoc.NeuFrac.neuFrac_const_mul`, nonnegativity
  `Work.BoseKinLoc.Word.neuFrac_nonneg_of_integrableSq` (with
  `Work.BoseFixB2.Polar.integrableOn_sq_of_continuous`); the summand `neuWord` is
  `½ε_T(dℓ)⁻²` times `neuFrac` composed with the *linear* projection `Q_u`;
* `gapBare` — `Work.BoseFixB2.Polar.FsTAux.gapBare_parallelogram`,
  `Work.BoseKinLoc.Word.FsTAux.gapBare_const_mul`, `Work.BoseKinLoc.gapBare_nonneg`;
* `momForm` — `Work.BoseFixB2.Polar.momForm_parallelogram`,
  `Work.BoseKinLoc.Word.momForm_const_mul`, `Work.BoseKinLoc.momForm_nonneg`;
* `bsOneBody ℓ (fsKinCoeff c) u` — `Work.BoseFixB2.Polar.FsTAux.bsOneBody_parallelogram_aux`,
  `Work.BoseKinLoc.Word.bsOneBody_const_mul`, `Work.BSKinetic.bsOneBody_nonneg`; the summand
  `mainWord` is the combination `(1−ε_T)·bsOneBody(c₁) + ε_T·bsOneBody(c₂)`.
-/

noncomputable section

open scoped Topology

namespace Work.BoseFixB2.Recomb

open Submission.BoseGases MeasureTheory
open Work.BoseKinLoc

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The four atomic nonnegative quadratic forms -/

/-- `neuFrac ℓ a² u` is a nonnegative quadratic form on smooth states, so its polar form is
`ℝ`-homogeneous. -/
theorem neuFrac_hpol {ℓ a2 t : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2)
    (u : EuclideanSpace ℝ (Fin 3)) {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    neuFrac ℓ a2 u (fun z => t * f z + g z) - neuFrac ℓ a2 u (fun z => t * f z - g z)
      = t * (neuFrac ℓ a2 u (fun z => f z + g z)
        - neuFrac ℓ a2 u (fun z => f z - g z)) :=
  hpol_of_par_nonneg_smooth (fun ψ => neuFrac ℓ a2 u ψ)
    (fun {f g} hf hg => Work.BoseFixB2.Polar.neuFrac_parallelogram hℓ ha2 u hf hg)
    (fun c {f} hf => Work.BoseKinLoc.NeuFrac.neuFrac_const_mul (ℓ := ℓ) (a2 := a2) (c := c)
      ha2.le u f)
    (fun {f} hf => Work.BoseKinLoc.Word.neuFrac_nonneg_of_integrableSq ha2.le u
      (Work.BoseFixB2.Polar.integrableOn_sq_of_continuous hℓ u hf.continuous))
    t hf hg

/-- The mean-free box mass `gapBare ℓ u` is a nonnegative quadratic form (it is a sum of
squares), so its polar form is `ℝ`-homogeneous. -/
theorem gapBare_hpol {ℓ t : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    gapBare ℓ u (fun z => t * f z + g z) - gapBare ℓ u (fun z => t * f z - g z)
      = t * (gapBare ℓ u (fun z => f z + g z) - gapBare ℓ u (fun z => f z - g z)) :=
  hpol_of_par_nonneg_smooth (fun ψ => gapBare ℓ u ψ)
    (fun {f g} hf hg => Work.BoseFixB2.Polar.FsTAux.gapBare_parallelogram hℓ u
      hf.continuous hg.continuous)
    (fun c {f} _ => Work.BoseKinLoc.Word.FsTAux.gapBare_const_mul ℓ u c f)
    (fun {f} _ => Work.BoseKinLoc.gapBare_nonneg ℓ u f)
    t hf hg

/-- The large-momentum word `momForm ℓ d u` is nonnegative (its `p`-integrand is a nonnegative
symbol times a squared Fourier transform), so its polar form is `ℝ`-homogeneous. -/
theorem momForm_hpol {ℓ d t : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    momForm ℓ d u (fun z => t * f z + g z) - momForm ℓ d u (fun z => t * f z - g z)
      = t * (momForm ℓ d u (fun z => f z + g z) - momForm ℓ d u (fun z => f z - g z)) :=
  hpol_of_par_nonneg_smooth (fun ψ => momForm ℓ d u ψ)
    (fun {f g} hf hg => Work.BoseFixB2.Polar.momForm_parallelogram (ℓ := ℓ) (d := d) hℓ u hf hg)
    (fun c {f} _ => Work.BoseKinLoc.Word.momForm_const_mul (ℓ := ℓ) (d := d) u c f)
    (fun {f} _ => Work.BoseKinLoc.momForm_nonneg u f)
    t hf hg

/-- The windowed kinetic form `bsOneBody ℓ (fsKinCoeff c) u` is a nonnegative quadratic form, so
its polar form is `ℝ`-homogeneous. -/
theorem bsOneBody_hpol {ℓ c t : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u (fun z => t * f z + g z)
        - Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u
            (fun z => t * f z - g z)
      = t * (Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u
            (fun z => f z + g z)
        - Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u
            (fun z => f z - g z)) :=
  hpol_of_par_nonneg_smooth
    (fun ψ => Work.BSKinetic.bsOneBody ℓ (Submission.BoseGases.fsKinCoeff c) u ψ)
    (fun {f g} hf hg => Work.BoseFixB2.Polar.FsTAux.bsOneBody_parallelogram_aux (ℓ := ℓ) (c := c)
      hℓ u hf hg)
    (fun c' {f} _ => Work.BoseKinLoc.Word.bsOneBody_const_mul (ℓ := ℓ)
      (Submission.BoseGases.fsKinCoeff c) u c' f)
    (fun {f} _ => Work.BSKinetic.bsOneBody_nonneg (F := Submission.BoseGases.fsKinCoeff c)
      (fun r => Submission.BoseGases.fsKinCoeff_nonneg c r) u f)
    t hf hg

/-! ## 2. The four summands of `fsT` -/

/-- The Neumann word `neuWord = ½ε_T(dℓ)⁻²·neuFrac ∘ Q_u` is homogeneously polarised.  The
projection `Q_u` is linear in the state, so the `Q_u`-arguments of the four `neuFrac`s are
`t·Q_u f ± Q_u g` and `Q_u f ± Q_u g`. -/
theorem neuWord_hpol {ℓ d εT t : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    neuWord ℓ d εT u (fun z => t * f z + g z) - neuWord ℓ d εT u (fun z => t * f z - g z)
      = t * (neuWord ℓ d εT u (fun z => f z + g z)
        - neuWord ℓ d εT u (fun z => f z - g z)) := by
  have ha2pos : 0 < (d * ℓ) ^ (-2 : ℤ) := by positivity
  have hQsm : ∀ {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}, ContDiff ℝ (⊤ : ℕ∞) ψ →
      ContDiff ℝ (⊤ : ℕ∞) (Qfree ℓ u ψ) := by
    intro ψ hψ
    rw [show Qfree ℓ u ψ = fun z => ψ z - Work.BSKinetic.bsMean ℓ u ψ from rfl]
    exact hψ.sub contDiff_const
  have hQtf : Continuous (fun z : EuclideanSpace ℝ (Fin 3) => t * f z) :=
    continuous_const.mul hf.continuous
  have hA : Qfree ℓ u (fun z => t * f z + g z)
      = fun z => t * Qfree ℓ u f z + Qfree ℓ u g z := by
    have h1 := Work.BoseFixB2.Polar.FsTAux.Qfree_add (ℓ := ℓ) hℓ u hQtf hg.continuous
    rw [Work.BoseKinLoc.Word.FsTAux.Qfree_const_mul (ℓ := ℓ) u t f] at h1
    simpa only [Pi.add_apply, smul_eq_mul] using h1
  have hB : Qfree ℓ u (fun z => t * f z - g z)
      = fun z => t * Qfree ℓ u f z - Qfree ℓ u g z := by
    have h1 := Work.BoseFixB2.Polar.FsTAux.Qfree_sub (ℓ := ℓ) hℓ u hQtf hg.continuous
    rw [Work.BoseKinLoc.Word.FsTAux.Qfree_const_mul (ℓ := ℓ) u t f] at h1
    simpa only [Pi.sub_apply, smul_eq_mul] using h1
  have hC : Qfree ℓ u (fun z => f z + g z) = fun z => Qfree ℓ u f z + Qfree ℓ u g z :=
    Work.BoseFixB2.Polar.FsTAux.Qfree_add hℓ u hf.continuous hg.continuous
  have hD : Qfree ℓ u (fun z => f z - g z) = fun z => Qfree ℓ u f z - Qfree ℓ u g z :=
    Work.BoseFixB2.Polar.FsTAux.Qfree_sub hℓ u hf.continuous hg.continuous
  have h := neuFrac_hpol (ℓ := ℓ) (a2 := (d * ℓ) ^ (-2 : ℤ)) (t := t) hℓ ha2pos u (hQsm hf) (hQsm hg)
  unfold neuWord
  rw [hA, hB, hC, hD]
  linear_combination ((1 / 2) * εT * (d * ℓ) ^ (-2 : ℤ)) * h

/-- The gap word `gapWord = bℓ⁻²·gapBare` is homogeneously polarised. -/
theorem gapWord_hpol {ℓ b t : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    gapWord ℓ b u (fun z => t * f z + g z) - gapWord ℓ b u (fun z => t * f z - g z)
      = t * (gapWord ℓ b u (fun z => f z + g z) - gapWord ℓ b u (fun z => f z - g z)) := by
  have h := gapBare_hpol (ℓ := ℓ) (t := t) hℓ u hf hg
  unfold gapWord
  linear_combination (b * ℓ ^ (-2 : ℤ)) * h

/-- The momentum word `momWord = bε_T(dℓ)⁻²·momForm` is homogeneously polarised. -/
theorem momWord_hpol {ℓ d εT b t : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    momWord ℓ d εT b u (fun z => t * f z + g z) - momWord ℓ d εT b u (fun z => t * f z - g z)
      = t * (momWord ℓ d εT b u (fun z => f z + g z)
        - momWord ℓ d εT b u (fun z => f z - g z)) := by
  have h := momForm_hpol (ℓ := ℓ) (d := d) (t := t) hℓ u hf hg
  unfold momWord
  linear_combination (b * εT * (d * ℓ) ^ (-2 : ℤ)) * h

/-- The main word `mainWord = (1−ε_T)·bsOneBody(c₁) + ε_T·bsOneBody(c₂)` is homogeneously
polarised.  Note that no hypothesis `ε_T ≤ 1` is needed: the two `bsOneBody`s are handled
separately. -/
theorem mainWord_hpol {ℓ d s εT t : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    mainWord ℓ d s εT u (fun z => t * f z + g z) - mainWord ℓ d s εT u (fun z => t * f z - g z)
      = t * (mainWord ℓ d s εT u (fun z => f z + g z)
        - mainWord ℓ d s εT u (fun z => f z - g z)) := by
  have h1 := bsOneBody_hpol (ℓ := ℓ) (c := (2 * (s * ℓ))⁻¹) (t := t) hℓ u hf hg
  have h2 := bsOneBody_hpol (ℓ := ℓ) (c := (2 * (d * s * ℓ))⁻¹) (t := t) hℓ u hf hg
  unfold mainWord
  linear_combination (1 - εT) * h1 + εT * h2

/-! ## 3. The word `fsT` -/

/-- **FS `eq:DefT`'s localised kinetic word is homogeneously polarised**: for every real `t`
and smooth `f g`, `fsT ℓ d s εT b u (t·f + g) − fsT ℓ d s εT b u (t·f − g)` is `t` times the
value at `t = 1`.  This is hypothesis `hpol` of `par_polarisation_hpol`. -/
theorem fsT_hpol {ℓ d s εT b t : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hs : 0 < s) (hεT : 0 < εT)
    (hb : 0 < b) (u : EuclideanSpace ℝ (Fin 3)) {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    fsT ℓ d s εT b u (fun z => t * f z + g z) - fsT ℓ d s εT b u (fun z => t * f z - g z)
      = t * (fsT ℓ d s εT b u (fun z => f z + g z)
        - fsT ℓ d s εT b u (fun z => f z - g z)) := by
  have h1 := neuWord_hpol (ℓ := ℓ) (d := d) (εT := εT) (t := t) hℓ hd u hf hg
  have h2 := gapWord_hpol (ℓ := ℓ) (b := b) (t := t) hℓ u hf hg
  have h3 := momWord_hpol (ℓ := ℓ) (d := d) (εT := εT) (b := b) (t := t) hℓ u hf hg
  have h4 := mainWord_hpol (ℓ := ℓ) (d := d) (s := s) (εT := εT) (t := t) hℓ u hf hg
  rw [fsT_eq_sum ℓ d s εT b u (fun z => t * f z + g z),
    fsT_eq_sum ℓ d s εT b u (fun z => t * f z - g z),
    fsT_eq_sum ℓ d s εT b u (fun z => f z + g z),
    fsT_eq_sum ℓ d s εT b u (fun z => f z - g z)]
  linear_combination h1 + h2 + h3 + h4

end Work.BoseFixB2.Recomb
