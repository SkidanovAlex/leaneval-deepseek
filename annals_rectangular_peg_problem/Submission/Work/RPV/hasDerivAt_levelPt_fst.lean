import Mathlib
import Submission.Work.RPV.Defs

/-!
# Derivative of `levelPt` in the first (`σ`) variable (`Work.RPV.hasDerivAt_levelPt_fst`)

`levelPt u σ a = (((e^{-ia} u).im, a), ((e^{-ia} u).re, ‖u‖²/2 - σ - 1))`.  Differentiating
`s ↦ levelPt (Γ s t) s (A s t)` in `s` is a chain rule: with `u s = Γ s t`, `a s = A s t`,
* `(e^{-i a s} u s)' = e^{-i a σ} (Γσ - i Aσ Γ σ t)` (product + `exp` rule);
* the `q₁`/`p₁` coordinates are its imaginary/real parts;
* `q₂ = a s` has derivative `Aσ`;
* `p₂ = ‖u s‖²/2 - s - 1` has derivative `Re(conj (Γ σ t) * Γσ) - 1`.

The two auxiliary lemmas below isolate the two non-trivial derivative computations.
-/

namespace Work.RPV

/-- Derivative of `s ↦ ‖f s‖²/2` along a path `f` with derivative `f'` at `x`:
it is `Re (conj (f x) * f')`. -/
private lemma hasDerivAt_normSq_half (f : ℝ → ℂ) (f' : ℂ) (x : ℝ) (h : HasDerivAt f f' x) :
    HasDerivAt (fun s => ‖f s‖ ^ 2 / 2) ((starRingEnd ℂ) (f x) * f').re x := by
  have hre : HasDerivAt (fun s => (f s).re) f'.re x :=
    HasFDerivAt.comp_hasDerivAt x Complex.reCLM.hasFDerivAt h
  have him : HasDerivAt (fun s => (f s).im) f'.im x :=
    HasFDerivAt.comp_hasDerivAt x Complex.imCLM.hasFDerivAt h
  -- the derivative of `re² + im²` is `2 Re(conj (f x) * f')`
  have hsq : HasDerivAt (fun s => (f s).re * (f s).re + (f s).im * (f s).im)
      (f'.re * (f x).re + (f x).re * f'.re + (f'.im * (f x).im + (f x).im * f'.im)) x := by
    have hh := (hre.mul hre).add (him.mul him)
    rw [show ((fun s => (f s).re) * (fun s => (f s).re))
          + ((fun s => (f s).im) * (fun s => (f s).im))
        = (fun s => (f s).re * (f s).re + (f s).im * (f s).im) from rfl] at hh
    exact hh
  have h2 : f'.re * (f x).re + (f x).re * f'.re + (f'.im * (f x).im + (f x).im * f'.im)
      = 2 * ((starRingEnd ℂ) (f x) * f').re := by
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  have h3 : HasDerivAt (fun s => ‖f s‖ ^ 2) (2 * ((starRingEnd ℂ) (f x) * f').re) x := by
    have hfun : (fun s => ‖f s‖ ^ 2)
        = fun s => (f s).re * (f s).re + (f s).im * (f s).im := by
      funext s; rw [Complex.sq_norm, Complex.normSq_apply]
    rw [hfun]
    exact hsq.congr_deriv h2
  exact (h3.div_const 2).congr_deriv (by ring)

/-- Derivative of `s ↦ e^{-i A s t} · Γ s t`. -/
private lemma hasDerivAt_exp_mul (Γ : ℝ → ℝ → ℂ) (A : ℝ → ℝ → ℝ) (σ t : ℝ) (Γσ : ℂ) (Aσ : ℝ)
    (hΓσ : HasDerivAt (fun s => Γ s t) Γσ σ) (hAσ : HasDerivAt (fun s => A s t) Aσ σ) :
    HasDerivAt (fun s => Complex.exp (-(A s t : ℂ) * Complex.I) * Γ s t)
      (Complex.exp (-(A σ t : ℂ) * Complex.I) * (Γσ - (Aσ : ℂ) * Complex.I * Γ σ t)) σ := by
  have hAc : HasDerivAt (fun s => (A s t : ℂ)) (Aσ : ℂ) σ := hAσ.ofReal_comp
  have hneg : HasDerivAt (fun s => -(A s t : ℂ) * Complex.I) (-(Aσ : ℂ) * Complex.I) σ :=
    hAc.neg.mul_const Complex.I
  have hexp : HasDerivAt (fun s => Complex.exp (-(A s t : ℂ) * Complex.I))
      (Complex.exp (-(A σ t : ℂ) * Complex.I) * (-(Aσ : ℂ) * Complex.I)) σ := hneg.cexp
  have hp := hexp.mul hΓσ
  refine hp.congr_deriv ?_
  ring_nf

theorem hasDerivAt_levelPt_fst (Γ : ℝ → ℝ → ℂ) (A : ℝ → ℝ → ℝ) (σ t : ℝ) (Γσ : ℂ) (Aσ : ℝ)
    (hΓσ : HasDerivAt (fun s => Γ s t) Γσ σ) (hAσ : HasDerivAt (fun s => A s t) Aσ σ) :
    HasDerivAt (fun s => Work.RPV.levelPt (Γ s t) s (A s t))
      (((Complex.exp (-(A σ t : ℂ) * Complex.I) * (Γσ - (Aσ : ℂ) * Complex.I * Γ σ t)).im, Aσ),
       ((Complex.exp (-(A σ t : ℂ) * Complex.I) * (Γσ - (Aσ : ℂ) * Complex.I * Γ σ t)).re,
        ((starRingEnd ℂ) (Γ σ t) * Γσ).re - 1)) σ := by
  -- the exponential factor
  have hprod := hasDerivAt_exp_mul Γ A σ t Γσ Aσ hΓσ hAσ
  -- `q₁` and `p₁` coordinates
  have hq1 : HasDerivAt (fun s => (Complex.exp (-(A s t : ℂ) * Complex.I) * Γ s t).im)
      (Complex.exp (-(A σ t : ℂ) * Complex.I) * (Γσ - (Aσ : ℂ) * Complex.I * Γ σ t)).im σ :=
    HasFDerivAt.comp_hasDerivAt σ Complex.imCLM.hasFDerivAt hprod
  have hp1 : HasDerivAt (fun s => (Complex.exp (-(A s t : ℂ) * Complex.I) * Γ s t).re)
      (Complex.exp (-(A σ t : ℂ) * Complex.I) * (Γσ - (Aσ : ℂ) * Complex.I * Γ σ t)).re σ :=
    HasFDerivAt.comp_hasDerivAt σ Complex.reCLM.hasFDerivAt hprod
  -- `p₂` coordinate
  have hp2 : HasDerivAt (fun s => ‖Γ s t‖ ^ 2 / 2 - s - 1)
      (((starRingEnd ℂ) (Γ σ t) * Γσ).re - 1) σ := by
    have h2 : HasDerivAt (fun s => ‖(fun s => Γ s t) s‖ ^ 2 / 2 - (fun x => x) s)
        (((starRingEnd ℂ) ((fun s => Γ s t) σ) * Γσ).re - 1) σ :=
      (hasDerivAt_normSq_half (fun s => Γ s t) Γσ σ hΓσ).sub (hasDerivAt_id' σ)
    have h3 : HasDerivAt
        (fun s => (‖(fun s => Γ s t) s‖ ^ 2 / 2 - (fun x => x) s) - (fun _ => (1 : ℝ)) s)
        ((((starRingEnd ℂ) ((fun s => Γ s t) σ) * Γσ).re - 1) - 0) σ :=
      h2.sub (hasDerivAt_const σ (1 : ℝ))
    simpa using h3
  -- assemble the product `PS = (ℝ × ℝ) × (ℝ × ℝ)`
  have hq := hq1.prodMk hAσ
  have hp := hp1.prodMk hp2
  have hall := hq.prodMk hp
  simpa only [Work.RPV.levelPt] using hall

end Work.RPV
