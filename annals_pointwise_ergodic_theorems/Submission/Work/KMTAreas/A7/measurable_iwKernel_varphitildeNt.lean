import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface

/-!
# Measurability in `t` of the IW kernel attached to the modulated bump `φ̃_{N,t}`

The model operators of §6/§8 of Krause--Mirek--Tao integrate in `t ∈ [1/2,1]` expressions built
from the Ionescu--Wainger projections `T^{≤l}_{φ̃_{N,t}}`, whose symbol is
`iwSymbolSet (iwArithFreqs ρ l) (periodize (φ̃_{N,t}))`.  For the Fubini-type arguments of the
model-tuple analysis one needs that the individual Fourier coefficients (the "kernel" `iwKernel`)
of that symbol depend *measurably* on the parameter `t`.

The proof is a direct instance of three general measurability facts, proved below in this file:

* `measurable_periodize_uncurry`: if `φ : ℝ → ℝ → ℂ` is jointly measurable, then so is
  `(t, ξ) ↦ periodize (φ t) ξ`.  The periodisation is the `ℤ`-indexed sum of the jointly
  measurable terms `(t, ξ) ↦ φ t (x(ξ) + m)`, where `x(ξ) ∈ [0,1)` is the canonical
  representative of `ξ ∈ ℝ/ℤ`; `Measurable.tsum` applies.
* `measurable_iwSymbolSet_uncurry`: the same for the IW symbol, which is a finite sum of translates
  `ξ ↦ periodize (φ t) (ξ - α)`, `α ∈ A`.
* `measurable_fourierCoeff_iwSymbolSet`: the `j`-th Fourier coefficient `fourierCoeff m j` of the
  symbol is the Bochner integral of the jointly measurable function
  `(t, z) ↦ fourier (-j) z • m t z` against the (finite) Haar measure of the circle, hence
  measurable in `t` by `MeasureTheory.StronglyMeasurable.integral_prod_right`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Polynomial

namespace Work.KMTAreas.A7

/-- **The periodisation of a jointly measurable family is jointly measurable.**  If
`φ : ℝ → ℝ → ℂ` is jointly measurable, then `(t, ξ) ↦ periodize (φ t) ξ` is measurable on
`ℝ × ℝ/ℤ`. -/
lemma measurable_periodize_uncurry {φ : ℝ → ℝ → ℂ}
    (hφ : Measurable (fun q : ℝ × ℝ => φ q.1 q.2)) :
    Measurable (fun p : ℝ × Work.Analysis.IonescuWainger.Circle =>
      Work.Analysis.IonescuWainger.periodize (φ p.1) p.2) := by
  have hx : Measurable (fun ξ : Work.Analysis.IonescuWainger.Circle =>
      (AddCircle.equivIco (1 : ℝ) 0 ξ).val) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  have h1 : (fun p : ℝ × Work.Analysis.IonescuWainger.Circle =>
        Work.Analysis.IonescuWainger.periodize (φ p.1) p.2)
      = fun p => ∑' m : ℤ, φ p.1 ((AddCircle.equivIco (1 : ℝ) 0 p.2).val + (m : ℝ)) := by
    funext p
    rw [Work.Analysis.IonescuWainger.periodize]
  rw [h1]
  refine Measurable.tsum (fun m => ?_)
  exact hφ.comp (measurable_fst.prodMk ((hx.comp measurable_snd).add measurable_const))

/-- **The IW symbol of a jointly measurable family is jointly measurable.**  For a finite set `A` of
arithmetic frequencies and a jointly measurable `φ : ℝ → ℝ → ℂ`, the function
`(t, ξ) ↦ iwSymbolSet A (periodize (φ t)) ξ = ∑_{α ∈ A} periodize (φ t) (ξ - α)` is measurable. -/
lemma measurable_iwSymbolSet_uncurry (A : Finset Work.Analysis.IonescuWainger.Circle)
    {φ : ℝ → ℝ → ℂ} (hφ : Measurable (fun q : ℝ × ℝ => φ q.1 q.2)) :
    Measurable (fun p : ℝ × Work.Analysis.IonescuWainger.Circle =>
      Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize (φ p.1)) p.2) := by
  have h1 : (fun p : ℝ × Work.Analysis.IonescuWainger.Circle =>
      Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize (φ p.1)) p.2)
      = fun p => ∑ α ∈ A, Work.Analysis.IonescuWainger.periodize (φ p.1) (p.2 - α) := by
    funext p; simp only [Work.Analysis.IonescuWainger.iwSymbolSet]
  rw [h1]
  refine Finset.measurable_sum _ (fun α _ => ?_)
  exact (measurable_periodize_uncurry hφ).comp
    (measurable_fst.prodMk (measurable_snd.sub measurable_const))

/-- **The Fourier coefficients of the IW symbol depend measurably on the parameter.**  For a finite
set `A` of arithmetic frequencies and a jointly measurable `φ : ℝ → ℝ → ℂ`, the map
`t ↦ fourierCoeff (iwSymbolSet A (periodize (φ t))) j` is measurable.

Indeed `fourierCoeff m j = ∫ z, fourier (-j) z • m z ∂circleMeasure`, the integrand is jointly
measurable in `(t, z)` by `measurable_iwSymbolSet_uncurry`, and the circle carries a finite
measure, so `MeasureTheory.StronglyMeasurable.integral_prod_right` applies. -/
lemma measurable_fourierCoeff_iwSymbolSet (A : Finset Work.Analysis.IonescuWainger.Circle)
    (j : ℤ) {φ : ℝ → ℝ → ℂ} (hφ : Measurable (fun q : ℝ × ℝ => φ q.1 q.2)) :
    Measurable (fun t : ℝ =>
      fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize (φ t))) j) := by
  have hsym := measurable_iwSymbolSet_uncurry A hφ
  have hprod : Measurable (fun p : ℝ × Work.Analysis.IonescuWainger.Circle =>
      fourier (-j) p.2 • Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize (φ p.1)) p.2) :=
    ((map_continuous (fourier (-j))).measurable.comp measurable_snd).smul hsym
  have hker : (fun t : ℝ =>
        fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet A
          (Work.Analysis.IonescuWainger.periodize (φ t))) j)
      = fun t : ℝ => ∫ z : Work.Analysis.IonescuWainger.Circle, fourier (-j) z •
          Work.Analysis.IonescuWainger.iwSymbolSet A
            (Work.Analysis.IonescuWainger.periodize (φ t)) z
          ∂Work.Analysis.IonescuWainger.circleMeasure := by
    funext t; rw [fourierCoeff, Work.Analysis.IonescuWainger.circleMeasure]
  rw [hker]
  exact (MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := Work.Analysis.IonescuWainger.circleMeasure) hprod.stronglyMeasurable).measurable

/-- **Joint measurability of the modulated bump** `(t, ξ) ↦ φ̃_{N,t}(ξ)`, where
`φ̃_{N,t}(ξ) = φ̃_N(ξ) · e(P(N t) ξ)`. -/
lemma measurable_varphitildeNt_uncurry (P : Polynomial ℤ) (N k : ℕ) :
    Measurable (fun q : ℝ × ℝ => varphitildeNt P P.natDegree N k q.1 q.2) := by
  have hk : Measurable Work.KMTContract.kmtEta := by
    have h : Work.KMTContract.kmtEta
        = fun x : ℝ => ((Work.KMTContract.kmtBump : ℝ → ℝ) x : ℂ) := rfl
    rw [h]
    exact Complex.continuous_ofReal.measurable.comp
      Work.KMTContract.kmtBump.continuous.measurable
  have hvp : Measurable (varphitildeN P.natDegree N k) := by
    unfold varphitildeN
    split_ifs with h0
    · exact hk.comp (measurable_const_mul _)
    · exact (hk.comp (measurable_const_mul _)).sub (hk.comp (measurable_const_mul _))
  have hee : Measurable ee := by
    unfold ee; fun_prop
  have hP : Measurable (fun q : ℝ × ℝ => PevalR P ((N : ℝ) * q.1)) := by
    have hp : Measurable (PevalR P) := by unfold PevalR; fun_prop
    exact hp.comp ((measurable_const_mul (N : ℝ)).comp measurable_fst)
  unfold varphitildeNt
  exact ((hvp.comp measurable_snd).mul (hee.comp (hP.mul measurable_snd)))

theorem measurable_iwKernel_varphitildeNt (P : Polynomial ℤ) (ρ : ℝ) (l : ℕ) (N k : ℕ) (j : ℤ) :
    Measurable (fun t : ℝ => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t))) j) := by
  have h := measurable_fourierCoeff_iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l) j
    (φ := fun t ξ => varphitildeNt P P.natDegree N k t ξ) (measurable_varphitildeNt_uncurry P N k)
  simpa only [Work.Analysis.IWMultiplier.iwKernel] using h

end Work.KMTAreas.A7
