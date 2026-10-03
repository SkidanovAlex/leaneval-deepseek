/-
# Measurability in the modulation parameter of the §7 model slice

The §7 assembly of `Work.KMTAreas.A7.SmallModelVar` integrates the model operator
`smallModelOp` in the modulation parameter `t ∈ [1/2,1]`, so it needs that the *slice*

  `t ↦ smallBtwist ρ P l₁ l₂ m₁ m₂ (T^{l₁}_{φ_{N,t}} f) (T^{l₂}_{φ̃_{N,t}} g) x`

is a measurable function of `t` for every `x ∈ ℤ`.

Since `smallBtwist` is a double unconditional sum over `j₁, j₂ ∈ ℤ` of the fixed arithmetic kernel
times the values `(T^{l₁}_{φ_{N,t}} f)(x-j₁)` and `(T^{l₂}_{φ̃_{N,t}} g)(x-j₂)`, and since an
unconditional sum of measurable functions is measurable (`Measurable.tsum`, the index set `ℤ` being
countable), it suffices to know that for every `y ∈ ℤ` the maps

  `t ↦ Tm ρ l₁ (varphiNt N k₁ t) f y`,      `t ↦ Tm ρ l₂ (varphitildeNt P P.natDegree N k₂ t) g y`

are measurable.  `Tm` is the Ionescu–Wainger convolution `iwConv (diffFreqs ρ l) (periodize φ)`,
whose kernel coefficients are the Fourier coefficients of `iwSymbolSet (diffFreqs ρ l)
(periodize φ)`; the joint measurability of `(t,ξ) ↦ φ t ξ` makes the kernel coefficients of the
symbol — Bochner integrals over the circle — measurable in `t`, and a second unconditional sum
over `j` then gives the measurability of the convolution.

The two files `measurable_iwKernel_varphiNt`/`measurable_iwKernel_varphitildeNt` prove this for the
*full* arithmetic height set `(ℚ/ℤ)_{≤l}`; the exact-height set `diffFreqs ρ l` used by `Tm` is
rather an instance of the same argument for an *arbitrary* finite set `A` of frequencies, which is
what is proved here (`measurable_iwKernel_uncurry_slice`,
`measurable_iwConv_periodize_slice`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.SmallModelDefs
import Submission.Work.KMTAreas.A7.measurable_iwKernel_varphiNt
import Submission.Work.KMTAreas.A7.measurable_iwKernel_varphitildeNt

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## Measurability in `t` of the IW convolution of a jointly measurable bump -/

/-- **The periodisation of a jointly measurable family of symbols is jointly measurable.** -/
private lemma measurable_periodize_uncurry_slice {φ : ℝ → ℝ → ℂ}
    (hφ : Measurable (fun q : ℝ × ℝ => φ q.1 q.2)) :
    Measurable (fun p : ℝ × Work.Analysis.IonescuWainger.Circle => periodize (φ p.1) p.2) := by
  have hx : Measurable (fun ξ : Work.Analysis.IonescuWainger.Circle => (AddCircle.equivIco (1 : ℝ) 0 ξ).val) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  have h1 : (fun p : ℝ × Work.Analysis.IonescuWainger.Circle => periodize (φ p.1) p.2)
      = fun p => ∑' m : ℤ, φ p.1 ((AddCircle.equivIco (1 : ℝ) 0 p.2).val + (m : ℝ)) := by
    funext p; rw [periodize]
  rw [h1]
  exact Measurable.tsum (fun m : ℤ => hφ.comp (measurable_fst.prodMk
    ((hx.comp measurable_snd).add measurable_const)))

/-- **The IW symbol of a jointly measurable family is jointly measurable** — for an arbitrary
finite set `A` of arithmetic frequencies. -/
private lemma measurable_iwSymbolSet_uncurry_slice (A : Finset Work.Analysis.IonescuWainger.Circle) {φ : ℝ → ℝ → ℂ}
    (hφ : Measurable (fun q : ℝ × ℝ => φ q.1 q.2)) :
    Measurable (fun p : ℝ × Work.Analysis.IonescuWainger.Circle => iwSymbolSet A (periodize (φ p.1)) p.2) := by
  have h1 : (fun p : ℝ × Work.Analysis.IonescuWainger.Circle => iwSymbolSet A (periodize (φ p.1)) p.2)
      = fun p => ∑ α ∈ A, periodize (φ p.1) (p.2 - α) := by
    funext p; simp only [iwSymbolSet]
  rw [h1]
  refine Finset.measurable_sum _ (fun α _ => ?_)
  exact (measurable_periodize_uncurry_slice hφ).comp
    (measurable_fst.prodMk (measurable_snd.sub measurable_const))

/-- **The IW kernel coefficients depend measurably on the modulation parameter** — for an arbitrary
finite set `A` of arithmetic frequencies and a jointly measurable family of bumps `φ`. -/
private lemma measurable_iwKernel_uncurry_slice (A : Finset Work.Analysis.IonescuWainger.Circle) {φ : ℝ → ℝ → ℂ}
    (hφ : Measurable (fun q : ℝ × ℝ => φ q.1 q.2)) (j : ℤ) :
    Measurable (fun t : ℝ => iwKernel (iwSymbolSet A (periodize (φ t))) j) := by
  have hsym := measurable_iwSymbolSet_uncurry_slice A hφ
  have hprod : Measurable (fun p : ℝ × Work.Analysis.IonescuWainger.Circle =>
      fourier (-j) p.2 • iwSymbolSet A (periodize (φ p.1)) p.2) :=
    ((map_continuous (fourier (-j))).measurable.comp measurable_snd).smul hsym
  have hker : (fun t : ℝ => iwKernel (iwSymbolSet A (periodize (φ t))) j)
      = fun t : ℝ => ∫ z : Work.Analysis.IonescuWainger.Circle, fourier (-j) z • iwSymbolSet A (periodize (φ t)) z
          ∂Work.Analysis.IonescuWainger.circleMeasure := by
    funext t; rw [iwKernel, fourierCoeff, Work.Analysis.IonescuWainger.circleMeasure]
  rw [hker]
  exact (StronglyMeasurable.integral_prod_right
    (ν := Work.Analysis.IonescuWainger.circleMeasure) hprod.stronglyMeasurable).measurable

/-- **Measurability in `t` of the IW convolution of a jointly measurable bump** — for an arbitrary
finite set `A` of arithmetic frequencies. -/
private lemma measurable_iwConv_periodize_slice (A : Finset Work.Analysis.IonescuWainger.Circle) {φ : ℝ → ℝ → ℂ}
    (hφ : Measurable (fun q : ℝ × ℝ => φ q.1 q.2)) (u : ℤ → ℂ) (y : ℤ) :
    Measurable (fun t : ℝ => iwConv A (periodize (φ t)) u y) := by
  have hfun : (fun t : ℝ => iwConv A (periodize (φ t)) u y)
      = fun t : ℝ => ∑' j : ℤ, iwKernel (iwSymbolSet A (periodize (φ t))) j * u (y - j) := by
    funext t
    rw [iwConv]
    exact tsum_congr (fun j => smul_eq_mul _ _)
  rw [hfun]
  exact Measurable.tsum (fun j : ℤ =>
    (measurable_iwKernel_uncurry_slice A hφ j).mul_const _)

/-! ## Joint measurability of the two modulated bumps -/

/-- Joint measurability of `(t,ξ) ↦ φ_{N,t}(ξ) = φ_N(ξ)·e(Ntξ)`. -/
private lemma measurable_varphiNt_uncurry_slice (N k : ℕ) :
    Measurable (fun q : ℝ × ℝ => varphiNt N k q.1 q.2) := by
  have hk : Measurable Work.KMTContract.kmtEta := by
    have h : Work.KMTContract.kmtEta
        = fun x : ℝ => ((Work.KMTContract.kmtBump : ℝ → ℝ) x : ℂ) := rfl
    rw [h]
    exact Complex.continuous_ofReal.measurable.comp
      Work.KMTContract.kmtBump.continuous.measurable
  have hvp : Measurable (varphiN N k) := by
    unfold varphiN
    split_ifs with h0
    · exact hk.comp (measurable_const_mul _)
    · exact (hk.comp (measurable_const_mul _)).sub (hk.comp (measurable_const_mul _))
  have hee : Measurable ee := by unfold ee; fun_prop
  unfold varphiNt
  exact (hvp.comp measurable_snd).mul
    (hee.comp (((measurable_const.mul measurable_fst).mul measurable_snd)))

/-- Joint measurability of `(t,ξ) ↦ φ̃_{N,t}(ξ) = φ̃_N(ξ)·e(P(Nt)ξ)`. -/
private lemma measurable_varphitildeNt_uncurry_slice (P : Polynomial ℤ) (N k : ℕ) :
    Measurable (fun q : ℝ × ℝ => varphitildeNt P P.natDegree N k q.1 q.2) :=
  measurable_varphitildeNt_uncurry P N k

/-! ## The target -/

theorem measurable_smallBtwist_slice (P : Polynomial ℤ) (ρ : ℝ) (N l₁ l₂ k₁ k₂ : ℕ)
    (f g : ℤ → ℂ) (x : ℤ) :
    Measurable (fun t : ℝ => Work.KMTAreas.A7.smallBtwist ρ P l₁ l₂
        (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂)))
        (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂)))
        (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ t) f)
        (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t) g) x) := by
  simp only [smallBtwist]
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun j₁ => ?_)
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun j₂ => ?_)
  have h₁ : Measurable (fun t : ℝ => Tm ρ l₁ (varphiNt N k₁ t) f (x - j₁)) :=
    measurable_iwConv_periodize_slice (diffFreqs ρ l₁)
      (measurable_varphiNt_uncurry_slice N k₁) f (x - j₁)
  have h₂ : Measurable (fun t : ℝ => Tm ρ l₂ (varphitildeNt P P.natDegree N k₂ t) g (x - j₂)) :=
    measurable_iwConv_periodize_slice (diffFreqs ρ l₂)
      (measurable_varphitildeNt_uncurry_slice P N k₂) g (x - j₂)
  exact (h₁.const_mul _).mul h₂

end

end Work.KMTAreas.A7
