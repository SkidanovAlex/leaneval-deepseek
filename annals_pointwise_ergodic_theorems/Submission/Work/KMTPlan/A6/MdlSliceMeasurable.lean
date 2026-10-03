/-
# Measurability in `t` of the frozen slices `mdlSliceJ` of the §6/§8 model estimate

`Work.KMTPlan.A6.mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x` is the frozen-`t` slice of the
§6/§8 model tuple of Krause--Mirek--Tao: on the admissible large scales `n` in the main regime it
is

  `Btwist_{m_*}(T^{l₁}_{φ_{N,t,j₁}} F, T^{l₂}_{φ̃_{N,t,j₂}} G)(x)`,

with `N = ⌊a n⌋`, `F = mdlF ρ u l₁ f`, `G = mdlG ρ P u l₂ g`, where the *modified* bumps are

  `φ_{N,t,j}(ξ) = (2^{-k}Nξ)^j φ_N(ξ) e(Ntξ)`,   `φ̃_{N,t,j}(ξ) = (2^{-dk}N^dξ)^j φ̃_N(ξ) e(P(Nt)ξ)`

(the paper's modified bumps of the integration-by-parts identity `integ-ident`), and it vanishes
otherwise.  This file proves that, with all other parameters fixed, `mdlSliceJ` is a *measurable*
function of the modulation parameter `t ∈ ℝ` — the measurability input for the Fubini/dominated
convergence arguments of the §8 model analysis.

The strategy is to isolate the `t`-dependence, one layer at a time:

* the modified bumps `(t,ξ) ↦ φ_{N,t,j}(ξ)`, `(t,ξ) ↦ φ̃_{N,t,j}(ξ)` are jointly measurable; the
  only genuine function of `t` is the character `e(Nt·)` / `e(P(Nt)·)`, which is continuous, while
  the prefactor `ξ ↦ (2^{-k}Nξ)^j` is measurable in `ξ` (also for the negative exponents `j < 0`
  used in the integration-by-parts identity, `zpow` being measurable on `ℂ`);
* hence the periodisation `(t,ξ) ↦ periodize (φ_{N,t,j}) ξ = ∑'_m φ_{N,t,j}(x(ξ) + m)` is jointly
  measurable, being a countable sum of jointly measurable terms (`Measurable.tsum`);
* hence the IW symbol `(t,ξ) ↦ ∑_{α ∈ (ℚ/ℤ)_{≤l}} periodize (φ_{N,t,j})(ξ - α)` is jointly
  measurable, and its `j`-th Fourier coefficient — a Bochner integral over the circle, a finite
  measure — is measurable in `t` (`StronglyMeasurable.integral_prod_right`);
* the multiplier `T^{≤l}_φ` is the convolution with the (infinite) sequence of these coefficients,
  so `t ↦ Tle ρ l (φ_{N,t,j}) F y` is measurable for each `y : ℤ` (a countable sum of measurable
  functions);
* finally `Btwist` is a double countable sum in the two convolution indices `j₁, j₂` of products
  of the two multiplier images, hence measurable in `t`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial
open scoped BigOperators
open Work.KMTAreas.A7

/-! ## The elementary measurability inputs -/

/-- The integer powers `z ↦ z^j` on `ℂ` are measurable (this is used for the prefactors
`(2^{-k}Nξ)^j` of the modified bumps, whose exponents `j ∈ {-1,0,1}` may be negative). -/
private lemma measurable_zpow_int (j : ℤ) : Measurable fun z : ℂ => z ^ j := by
  rcases Int.eq_nat_or_neg j with ⟨n, h | h⟩
  · subst h; simpa using (continuous_pow (M := ℂ) n).measurable
  · subst h
    simp only [zpow_neg, zpow_natCast]
    exact ((continuous_pow (M := ℂ) n).measurable).inv

/-- The cutoff `η = kmtEta` is measurable. -/
private lemma measurable_kmtEta : Measurable Work.KMTContract.kmtEta := by
  have h : Work.KMTContract.kmtEta = fun x : ℝ => ((Work.KMTContract.kmtBump : ℝ → ℝ) x : ℂ) := rfl
  rw [h]
  exact Complex.continuous_ofReal.measurable.comp Work.KMTContract.kmtBump.continuous.measurable

/-- The bump `φ_N` is measurable. -/
private lemma measurable_varphiN (N k : ℕ) : Measurable (varphiN N k) := by
  unfold varphiN
  split_ifs with hk
  · exact measurable_kmtEta.comp (measurable_const_mul _)
  · exact (measurable_kmtEta.comp (measurable_const_mul _)).sub
      (measurable_kmtEta.comp (measurable_const_mul _))

/-- The bump `φ̃_N` is measurable. -/
private lemma measurable_varphitildeN (d N k : ℕ) : Measurable (varphitildeN d N k) := by
  unfold varphitildeN
  split_ifs with hk
  · exact measurable_kmtEta.comp (measurable_const_mul _)
  · exact (measurable_kmtEta.comp (measurable_const_mul _)).sub
      (measurable_kmtEta.comp (measurable_const_mul _))

/-- The real evaluation `PevalR P` of an integer polynomial is measurable. -/
private lemma measurable_PevalR (P : Polynomial ℤ) : Measurable (PevalR P) := by
  unfold PevalR
  fun_prop

/-- The character `e(x) = exp (2πix)` is continuous. -/
private lemma continuous_ee : Continuous ee := by
  unfold ee; fun_prop

/-! ## Joint measurability of the modulated bumps -/

/-- `(t,ξ) ↦ φ_{N,t}(ξ) = φ_N(ξ) e(Ntξ)` is jointly measurable. -/
private lemma measurable_varphiNt_uncurry (N k : ℕ) :
    Measurable fun p : ℝ × ℝ => varphiNt N k p.1 p.2 := by
  have h1 : Measurable fun p : ℝ × ℝ => varphiN N k p.2 :=
    (measurable_varphiN N k).comp measurable_snd
  have h2 : Measurable fun p : ℝ × ℝ => ee ((N : ℝ) * p.1 * p.2) :=
    continuous_ee.measurable.comp ((measurable_fst.const_mul (N : ℝ)).mul measurable_snd)
  exact h1.mul h2

/-- `(t,ξ) ↦ φ̃_{N,t}(ξ) = φ̃_N(ξ) e(P(Nt)ξ)` is jointly measurable. -/
private lemma measurable_varphitildeNt_uncurry (P : Polynomial ℤ) (N k : ℕ) :
    Measurable fun q : ℝ × ℝ => varphitildeNt P P.natDegree N k q.1 q.2 := by
  have hvp : Measurable (varphitildeN P.natDegree N k) := measurable_varphitildeN _ N k
  have hP : Measurable fun q : ℝ × ℝ => PevalR P ((N : ℝ) * q.1) :=
    (measurable_PevalR P).comp (measurable_fst.const_mul (N : ℝ))
  exact (hvp.comp measurable_snd).mul (continuous_ee.measurable.comp (hP.mul measurable_snd))

/-- **Joint measurability of the modified bump** `(t,ξ) ↦ φ_{N,t,j}(ξ)`. -/
private lemma measurable_varphiNtj_uncurry (N k : ℕ) (j : ℤ) :
    Measurable fun p : ℝ × ℝ => varphiNtj N k j p.1 p.2 := by
  have hz : Measurable fun p : ℝ × ℝ =>
      ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * p.2 : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp
      (((continuous_const.mul continuous_const).mul continuous_snd).measurable)
  have h1 : Measurable fun p : ℝ × ℝ =>
      ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * p.2 : ℝ)) : ℂ) ^ j :=
    (measurable_zpow_int j).comp hz
  exact h1.mul (measurable_varphiNt_uncurry N k)

/-- **Joint measurability of the modified bump** `(t,ξ) ↦ φ̃_{N,t,j}(ξ)`. -/
private lemma measurable_varphitildeNtj_uncurry (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) :
    Measurable fun p : ℝ × ℝ => varphitildeNtj P N k j p.1 p.2 := by
  have hz : Measurable fun p : ℝ × ℝ =>
      ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * p.2 : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp
      (((continuous_const.mul continuous_const).mul continuous_snd).measurable)
  have h1 : Measurable fun p : ℝ × ℝ =>
      ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * p.2 : ℝ)) : ℂ) ^ j :=
    (measurable_zpow_int j).comp hz
  exact h1.mul (measurable_varphitildeNt_uncurry P N k)

/-! ## From the bump to the kernel of `T^{≤l}_φ`, and to `T^{≤l}_φ` itself -/

/-- If a family of symbols `(t,ξ) ↦ φ t ξ` is jointly measurable, then the `j`-th Fourier
coefficient of the Ionescu--Wainger symbol `∑_{α ∈ A} periodize (φ t)(· - α)` depends measurably on
`t`.  Indeed the coefficient is the Bochner integral over the circle — a finite measure — of the
jointly measurable integrand `(t,z) ↦ e(-jz) · (∑_{α ∈ A} periodize (φ t)(z - α))`. -/
private lemma measurable_iwKernel_periodize (A : Finset Work.Analysis.IonescuWainger.Circle) (j : ℤ)
    {φ : ℝ → ℝ → ℂ} (hφ : Measurable fun p : ℝ × ℝ => φ p.1 p.2) :
    Measurable fun t : ℝ => Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize (φ t))) j := by
  have hx : Measurable fun ξ : Work.Analysis.IonescuWainger.Circle =>
      (AddCircle.equivIco (1 : ℝ) 0 ξ).val :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  have hper : Measurable fun p : ℝ × Work.Analysis.IonescuWainger.Circle =>
      Work.Analysis.IonescuWainger.periodize (φ p.1) p.2 := by
    have h1 : (fun p : ℝ × Work.Analysis.IonescuWainger.Circle =>
          Work.Analysis.IonescuWainger.periodize (φ p.1) p.2)
        = fun p => ∑' m : ℤ, φ p.1 ((AddCircle.equivIco (1 : ℝ) 0 p.2).val + (m : ℝ)) := by
      funext p
      rw [Work.Analysis.IonescuWainger.periodize]
    rw [h1]
    refine Measurable.tsum (fun m : ℤ => ?_)
    exact hφ.comp (measurable_fst.prodMk ((hx.comp measurable_snd).add_const (m : ℝ)))
  have hsym : Measurable fun p : ℝ × Work.Analysis.IonescuWainger.Circle =>
      Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize (φ p.1)) p.2 := by
    have h1 : (fun p : ℝ × Work.Analysis.IonescuWainger.Circle =>
          Work.Analysis.IonescuWainger.iwSymbolSet A
            (Work.Analysis.IonescuWainger.periodize (φ p.1)) p.2)
        = fun p => ∑ α ∈ A, Work.Analysis.IonescuWainger.periodize (φ p.1) (p.2 - α) := by
      funext p; rw [Work.Analysis.IonescuWainger.iwSymbolSet]
    rw [h1]
    refine Finset.measurable_sum _ (fun α _ => ?_)
    exact hper.comp (measurable_fst.prodMk (measurable_snd.sub measurable_const))
  have hprod : Measurable fun p : ℝ × Work.Analysis.IonescuWainger.Circle =>
      fourier (T := 1) (-j) p.2 • Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize (φ p.1)) p.2 :=
    ((map_continuous (fourier (T := 1) (-j))).measurable.comp measurable_snd).smul hsym
  have hker : (fun t : ℝ => Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet A
          (Work.Analysis.IonescuWainger.periodize (φ t))) j)
      = fun t : ℝ => ∫ z : Work.Analysis.IonescuWainger.Circle,
          fourier (T := 1) (-j) z • Work.Analysis.IonescuWainger.iwSymbolSet A
            (Work.Analysis.IonescuWainger.periodize (φ t)) z
          ∂Work.Analysis.IonescuWainger.circleMeasure := by
    funext t
    rw [Work.Analysis.IWMultiplier.iwKernel, fourierCoeff,
      Work.Analysis.IonescuWainger.circleMeasure]
  rw [hker]
  exact (MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := Work.Analysis.IonescuWainger.circleMeasure) hprod.stronglyMeasurable).measurable

/-- **The `f`-side multiplier is measurable in `t`**, for the modified bumps. -/
private lemma measurable_Tle_varphiNtj (ρ : ℝ) (l N k : ℕ) (j : ℤ) (F : ℤ → ℂ) (y : ℤ) :
    Measurable fun t : ℝ => Tle ρ l (varphiNtj N k j t) F y := by
  have hfun : (fun t : ℝ => Tle ρ l (varphiNtj N k j t) F y)
      = fun t : ℝ => ∑' i : ℤ, Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize (varphiNtj N k j t))) i * F (y - i) := by
    funext t; rw [Tle_apply]
  rw [hfun]
  refine Measurable.tsum (fun i : ℤ => ?_)
  exact (measurable_iwKernel_periodize (Work.Analysis.IonescuWainger.iwArithFreqs ρ l) i
    (measurable_varphiNtj_uncurry N k j)).mul_const _

/-- **The `g`-side multiplier is measurable in `t`**, for the modified bumps. -/
private lemma measurable_Tle_varphitildeNtj (P : Polynomial ℤ) (ρ : ℝ) (l N k : ℕ) (j : ℤ)
    (G : ℤ → ℂ) (y : ℤ) :
    Measurable fun t : ℝ => Tle ρ l (varphitildeNtj P N k j t) G y := by
  have hfun : (fun t : ℝ => Tle ρ l (varphitildeNtj P N k j t) G y)
      = fun t : ℝ => ∑' i : ℤ, Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize (varphitildeNtj P N k j t))) i * G (y - i) := by
    funext t; rw [Tle_apply]
  rw [hfun]
  refine Measurable.tsum (fun i : ℤ => ?_)
  exact (measurable_iwKernel_periodize (Work.Analysis.IonescuWainger.iwArithFreqs ρ l) i
    (measurable_varphitildeNtj_uncurry P N k j)).mul_const _

/-- `Btwist` is measurable in `t` as soon as its two arguments are: it is the double countable sum
of the products `K(j₁,j₂) h(x - j₁) k(x - j₂)`. -/
private lemma measurable_Btwist_mdl {ρ : ℝ} {P : Polynomial ℤ} {l₁ l₂ : ℕ} {m₁ m₂ : ℝ → ℂ}
    {h k : ℝ → ℤ → ℂ} {x : ℤ}
    (hh : ∀ y : ℤ, Measurable fun t : ℝ => h t y)
    (hk : ∀ y : ℤ, Measurable fun t : ℝ => k t y) :
    Measurable fun t : ℝ => Btwist ρ P l₁ l₂ m₁ m₂ (h t) (k t) x := by
  simp only [Btwist]
  refine Measurable.tsum (fun j₁ : ℤ => ?_)
  refine Measurable.tsum (fun j₂ : ℤ => ?_)
  exact (measurable_const.mul (hh (x - j₁))).mul (hk (x - j₂))

/-! ## The frozen-`t` slices of the model tuple -/

/-- **The frozen-`t` slice of the modified model tuple is measurable in `t`.**  This is the
measurability input for the Fubini/dominated-convergence arguments of §8: for every fixed
`n : ℕ` and `x : ℤ`, the slice `t ↦ mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x` is a measurable
function of the modulation parameter. -/
theorem MdlSliceMeasurable (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (n : ℕ) (x : ℤ) :
    Measurable (fun t : ℝ => Work.KMTPlan.A6.mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x) := by
  have hfun : (fun t : ℝ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
      = fun t : ℝ =>
          if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
            Btwist ρ P l₁ l₂ (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
              (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
              (Tle ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t)
                (mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f))
              (Tle ρ l₂ (varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
                (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g)) x
          else 0 := by
    funext t
    rw [mdlSliceJ_apply]
  rw [hfun]
  by_cases hc : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · simp only [if_pos hc]
    refine measurable_Btwist_mdl (fun y => ?_) (fun y => ?_)
    · exact measurable_Tle_varphiNtj ρ l₁ (Nat.floor (a n)) k₁ j₁
        (mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f) y
    · exact measurable_Tle_varphitildeNtj P ρ l₂ (Nat.floor (a n)) k₂ j₂
        (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g) y
  · simp only [if_neg hc]
    exact measurable_const

end

end Work.KMTPlan.A6
