import Mathlib
import Submission.Work.KMTAreas.A7.FibreCum
import Submission.Work.KMTAreas.A7.IwLqGeneral
import Submission.Work.KMTAreas.A7.eLpNorm_iwConv_le_of_IWLqBound
import Submission.Work.KMTAreas.A7.cw_tsum_fourier

set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## The modulated cutoff `η_{≤k} · e(c·)` as a Schwartz function

The symbol that the fibre bound needs is not the plain rescaled cutoff `η_{≤k}` but its *modulation*
`ξ ↦ e(c ξ) η_{≤k}(ξ)`; the multiplier bounds for it (and its conjugate) are exactly the hypothesis
`hM` of the main theorem (`Work.KMTAreas.A7.isLqMultiplierBound_modulated_etaCut` produces them).
Since the modulation has modulus one and the cutoff is compactly supported and smooth, the product
is compactly supported and smooth, hence a Schwartz function. -/

/-- The modulated rescaled cutoff `ξ ↦ e(c ξ) η_{≤k}(ξ)`. -/
noncomputable def modEtaCut (c k : ℤ) : ℝ → ℂ :=
  fun ξ => ee ((c : ℝ) * ξ) * Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k ξ

private lemma contDiff_modEtaCut_exp (c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => ee (c * ξ)) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => (ξ : ℂ)) :=
    ContinuousLinearMap.contDiff (n := (⊤ : ℕ∞)) (Complex.ofRealCLM : ℝ →L[ℝ] ℂ)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => (2 * ↑Real.pi * Complex.I * ↑c) * (ξ : ℂ)) :=
    contDiff_const.mul h1
  have h3 : ContDiff ℝ (⊤ : ℕ∞)
      (fun ξ : ℝ => Complex.exp ((2 * ↑Real.pi * Complex.I * ↑c) * (ξ : ℂ))) :=
    ContDiff.cexp h2
  have heq : (fun ξ : ℝ => Complex.exp ((2 * ↑Real.pi * Complex.I * ↑c) * (ξ : ℂ)))
      = (fun ξ : ℝ => ee (c * ξ)) := by
    funext ξ
    simp only [ee]
    congr 1
    push_cast
    ring
  rw [heq] at h3
  exact h3

private lemma contDiff_modEtaCut (c k : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (modEtaCut c k) :=
  (contDiff_modEtaCut_exp (c : ℝ)).mul (Work.KMTAreas.A7.contDiff_etaCut k)

private lemma hasCompactSupport_modEtaCut (c k : ℤ) : HasCompactSupport (modEtaCut c k) :=
  HasCompactSupport.mul_left (f := fun ξ : ℝ => ee ((c : ℝ) * ξ))
    (Work.KMTAreas.A7.hasCompactSupport_etaCut k)

/-- The modulated cutoff as a Schwartz function. -/
noncomputable def modEtaCutSch (c k : ℤ) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_modEtaCut c k).toSchwartzMap (contDiff_modEtaCut c k)

lemma modEtaCutSch_coe (c k : ℤ) :
    ((modEtaCutSch c k : SchwartzMap ℝ ℂ) : ℝ → ℂ) = modEtaCut c k :=
  funext fun ξ => HasCompactSupport.toSchwartzMap_toFun _ _ ξ

/-- A nonzero value of the modulated cutoff lies in the arc `ℝ_{≤k}` (the modulation has modulus
one, the cutoff vanishes off that arc). -/
lemma modEtaCutSch_support (c k : ℤ) {x : ℝ} (h : modEtaCutSch c k x ≠ 0) :
    x ∈ Work.Analysis.IonescuWainger.realArc k := by
  refine Work.KMTAreas.A7.etaCut_ne_zero_mem_realArc k (x := x) ?_
  intro h0
  refine h ?_
  rw [show modEtaCutSch c k x = modEtaCut c k x from
    HasCompactSupport.toSchwartzMap_toFun _ _ x]
  simp [modEtaCut, h0]

/-! ## The Fourier coefficients of a modulated symbol -/

private lemma ee_add_exp (a b : ℝ) : ee (a + b) = ee a * ee b := by
  simp only [ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The Fourier coefficients of a modulated symbol.**  Modulation on the frequency side is a
translation of the coefficients: `cw (e(c·) m) j = ∫_ℝ e(cθ) m(θ) e(-jθ) dθ = cw m (j - c)`. -/
lemma cw_modEtaCut (c k : ℤ) (j : ℤ) :
    cw (modEtaCut c k) j
      = cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) (j - c) := by
  simp only [cw, modEtaCut]
  refine integral_congr_ae ?_
  filter_upwards with θ
  have hkey : ee ((c : ℝ) * θ) * ee (-(j : ℝ) * θ) = ee (-(((j - c : ℤ) : ℝ)) * θ) := by
    rw [← ee_add_exp]
    congr 1
    push_cast
    ring
  rw [show (ee ((c : ℝ) * θ)
        * Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ) * ee (-(j : ℝ) * θ)
      = Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ
        * (ee ((c : ℝ) * θ) * ee (-(j : ℝ) * θ)) by ring, hkey]

/-- **The Fourier coefficient of the Ionescu--Wainger symbol of a modulated cutoff** factors as the
arithmetic character sum times the continuous Fourier transform of the modulated cutoff
(`Work.KMTPlan.A6.IwKernelArithChar`). -/
lemma iwKernel_modEtaCut (A : Finset Work.Analysis.IonescuWainger.Circle) (c k j : ℤ) :
    Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet A
          (Work.Analysis.IonescuWainger.periodize (modEtaCut c k))) j
      = (∑ α ∈ A, fourier (T := 1) (-j) α) * cw (modEtaCut c k) j := by
  have hint : Integrable (modEtaCut c k) volume := by
    rw [← modEtaCutSch_coe c k]
    exact (modEtaCutSch c k).integrable
  exact Work.KMTPlan.A6.IwKernelArithChar A hint j

/-- **The kernel of the cumulative fibre is the `n₀`-shifted kernel of the IW projection with the
modulated cutoff `e(-n₀·) η_{≤-2u}`.**  This is the pointwise form of the factorisation
`σ = e(n₀θ) · iwSymbolSet (iwArithFreqs ρ l) (periodize m̃)`: the `j`-th term of the cumulative
fibre is the `(j - n₀)`-th Fourier coefficient of that projection symbol. -/
lemma fiberOpCum_kernel (ρ : ℝ) (l u : ℕ) (n₀ j : ℤ) :
    (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l, fourier (T := 1) (n₀ - j) α)
        * cw (mStarF u) j
      = Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize
              (((modEtaCutSch (-n₀) (-(2 * (u : ℤ))) : SchwartzMap ℝ ℂ)) : ℝ → ℂ))) (j - n₀) := by
  rw [modEtaCutSch_coe (-n₀) (-(2 * (u : ℤ))),
    iwKernel_modEtaCut (Work.Analysis.IonescuWainger.iwArithFreqs ρ l) (-n₀) (-(2 * (u : ℤ)))
      (j - n₀),
    cw_modEtaCut (-n₀) (-(2 * (u : ℤ))) (j - n₀)]
  have h1 : (j - n₀) - (-n₀) = j := by ring
  rw [h1, show -(j - n₀) = n₀ - j from by ring]
  rfl

/-! ## Invariance of the `ℒᵖ(ℤ)`-norm under translations -/

private lemma eLpNorm_comp_sub_count (P : ENNReal) (t : ℤ) (g : ℤ → ℂ) :
    eLpNorm (fun n : ℤ => g (n - t)) P (Measure.count : Measure ℤ)
      = eLpNorm g P (Measure.count : Measure ℤ) := by
  have hf : MeasurePreserving (fun n : ℤ => n - t) (Measure.count : Measure ℤ)
      (Measure.count : Measure ℤ) := by
    have h := measurePreserving_add_right (Measure.count : Measure ℤ) (-t)
    simpa [sub_eq_add_neg] using h
  have h2 := eLpNorm_comp_measurePreserving (p := P)
    (μ := (Measure.count : Measure ℤ)) (f := fun n : ℤ => n - t) (g := g)
    ((measurable_of_countable g).aestronglyMeasurable) hf
  simpa [Function.comp_def] using h2

/-- Reindexing the convolution sum by the bijection `j ↦ j - n₀`. -/
private lemma tsum_sub_index_eq (k v : ℤ → ℂ) (x n₀ : ℤ) :
    (∑' j : ℤ, k (j - n₀) * v (x - j)) = ∑' t : ℤ, k t * v (x - n₀ - t) := by
  rw [← Equiv.tsum_eq (Equiv.subRight n₀) (fun t : ℤ => k t * v (x - n₀ - t))]
  refine tsum_congr (fun c => ?_)
  simp only [Equiv.subRight_apply]
  rw [show x - n₀ - (c - n₀) = x - c by ring]

/-- **The cumulative fibre is the translate of an Ionescu--Wainger projection.**  The kernel identity
`fiberOpCum_kernel` turns the defining series of `fiberOpCum` into the convolution with the kernel
of `iwSymbolSet (iwArithFreqs ρ l) (periodize (e(-n₀·) η_{≤-2u}))`, evaluated at `x - n₀`. -/
lemma fiberOpCum_eq_iwConv_comp (ρ : ℝ) (l u : ℕ) (n₀ : ℤ) (v : ℤ → ℂ) :
    fiberOpCum ρ l (mStarF u) n₀ v
      = fun x : ℤ => Work.Analysis.IWMultiplier.iwConv
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize
            (((modEtaCutSch (-n₀) (-(2 * (u : ℤ))) : SchwartzMap ℝ ℂ)) : ℝ → ℂ)) v (x - n₀) := by
  funext x
  have hL : fiberOpCum ρ l (mStarF u) n₀ v x
      = ∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize
              (((modEtaCutSch (-n₀) (-(2 * (u : ℤ))) : SchwartzMap ℝ ℂ)) : ℝ → ℂ))) (j - n₀)
          * v (x - j) := by
    rw [fiberOpCum]
    exact tsum_congr (fun j => by rw [fiberOpCum_kernel ρ l u n₀ j])
  have hR : Work.Analysis.IWMultiplier.iwConv
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize
          (((modEtaCutSch (-n₀) (-(2 * (u : ℤ))) : SchwartzMap ℝ ℂ)) : ℝ → ℂ)) v (x - n₀)
      = ∑' t : ℤ, Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize
              (((modEtaCutSch (-n₀) (-(2 * (u : ℤ))) : SchwartzMap ℝ ℂ)) : ℝ → ℂ))) t
          * v (x - n₀ - t) := by
    rw [Work.Analysis.IWMultiplier.iwConv_apply]
    exact tsum_congr (fun t => by rw [smul_eq_mul])
  rw [hL, hR]
  exact tsum_sub_index_eq _ _ x n₀

/-! ## Pointwise vanishing from the vanishing of an `ℒᵖ(ℤ)`-norm

The counting measure gives every singleton mass `1`, so a function whose `ℒᵖ`-norm vanishes is
*pointwise* zero (not merely almost everywhere); this is what lets us read off the vanishing of the
whole IW kernel from an `ℓᵖ` bound with constant `0`. -/

private lemma eq_zero_of_eLpNorm_count_eq_zero {f : ℤ → ℂ} {P : ENNReal} (hP : P ≠ 0)
    (h : eLpNorm f P (Measure.count : Measure ℤ) = 0) (x : ℤ) : f x = 0 := by
  have hmeas : AEStronglyMeasurable f (Measure.count : Measure ℤ) :=
    (measurable_of_countable f).aestronglyMeasurable
  have hae : f =ᵐ[Measure.count] 0 := (eLpNorm_eq_zero_iff hP).mp h
  by_contra hx
  have hnull : (Measure.count : Measure ℤ) {y : ℤ | f y ≠ 0} = 0 := by
    have := MeasureTheory.ae_iff.mp hae
    simpa using this
  have hsub : ({x} : Set ℤ) ⊆ {y : ℤ | f y ≠ 0} := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hx
  have h1 : (Measure.count : Measure ℤ) {x} ≤ (Measure.count : Measure ℤ) {y : ℤ | f y ≠ 0} :=
    measure_mono hsub
  rw [hnull, Measure.count_singleton] at h1
  exact absurd h1 (by simp)

private noncomputable def delta0 : ℤ → ℂ := fun m => if m = 0 then 1 else 0

private lemma support_delta0 : (Function.support delta0).Finite := by
  refine Set.Finite.subset (Set.finite_singleton (0 : ℤ)) ?_
  intro m hm
  rw [Function.mem_support] at hm
  rw [Set.mem_singleton_iff]
  by_contra h
  exact hm (by simp [delta0, h])

/-- The IW convolution of the Kronecker delta is the kernel itself. -/
private lemma iwConv_delta0 (A : Finset Work.Analysis.IonescuWainger.Circle)
    (Ψ : Work.Analysis.IonescuWainger.Circle → ℂ) (n : ℤ) :
    Work.Analysis.IWMultiplier.iwConv A Ψ delta0 n
      = Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet A Ψ) n := by
  rw [Work.Analysis.IWMultiplier.iwConv_apply]
  rw [tsum_eq_single n (fun j hj => by
    rw [smul_eq_mul, delta0]
    have : n - j ≠ 0 := sub_ne_zero.mpr (Ne.symm hj)
    rw [if_neg this, mul_zero])]
  rw [delta0, sub_self, if_pos rfl, smul_eq_mul, mul_one]

/- **The cumulative-height fibre is a linear Ionescu--Wainger multiplier.**

`fiberOpCum ρ l m n₀ v x = ∑'_j (∑_{α ∈ iwArithFreqs ρ l} e(α(n₀-j))) cw m j v(x-j)` is the
convolution with the kernel of the symbol `σ(θ) = ∑_{α ∈ (ℚ/ℤ)_{≤l}} e(α n₀) (periodize m)(θ-α)`
(Poisson summation `Work.KMTAreas.A7.cw_tsum_fourier`), which factorises as
`σ = ee(n₀θ) · iwSymbolSet (iwArithFreqs ρ l) (periodize m̃)`, `m̃(ξ) = ee(-n₀ξ)·m(ξ)`.
The modulation `ee(n₀θ)` is the translation `x ↦ x - n₀` on the physical side (an isometry for
`eLpNorm · p Measure.count`), and `iwSymbolSet A (periodize Φ)` is exactly the Ionescu--Wainger
projection of `Work.KMTAreas.A7.IwLqGeneral`, which (using the area `A1` hypothesis) bounds it on
`ℓ^p` by `C⟨l⟩M` whenever `(l,k)` has good major arcs, `Φ` is supported in `realArc k`, and `M`
bounds the continuous multiplier norms of `Φ` and `star Φ` for all `q > 1`
(`hM` supplies these for the modulated cutoffs, uniformly in `(k,c)`).
The conclusion extends `IWLqBound` from finitely supported inputs to all `v` via
`Work.KMTAreas.A7.eLpNorm_iwConv_le_of_IWLqBound`.
This is the *gain-free* fibre bound of the paper's Lemma `ssu` (arXiv:2008.00857 §8); the point is
that it needs only `2u ≳ 2^{ρl}` (`GoodMajorArcs`), and NOT the narrow condition
`2^{2u} ≳ arithQ ρ l` used by the projection-based `Work.KMTAreas.A7.residueLp_fiberOpD_le`. -/
theorem fiberOpCum_lp_goodArcs (hA1 : Work.KMTContract.AreaA1) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (p : ENNReal) (hp : 1 < p) (htp : p < ⊤) (M : NNReal)
    (hM : ∀ (k c : ℤ) (q : ENNReal), 1 ≤ q →
      Work.Analysis.IWMultiplier.IsLqMultiplierBound q
        (fun ξ : ℝ => Work.KMTAreas.A7.ee ((c : ℝ) * ξ) *
          Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k ξ) M ∧
      Work.Analysis.IWMultiplier.IsLqMultiplierBound q
        (star (fun ξ : ℝ => Work.KMTAreas.A7.ee ((c : ℝ) * ξ) *
          Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k ξ)) M) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
      ∀ (l u : ℕ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(2 * (u : ℤ))) →
        ∀ (n₀ : ℤ) (v : ℤ → ℂ),
          MeasureTheory.eLpNorm
              (fun x : ℤ => Work.KMTAreas.A7.fiberOpCum ρ l (Work.KMTAreas.A7.mStarF u) n₀ v x)
              p MeasureTheory.Measure.count
            ≤ (C * Work.Analysis.IWMultiplier.angleBracket l * M : NNReal) *
                MeasureTheory.eLpNorm v p MeasureTheory.Measure.count := by
  -- the Ionescu--Wainger multiplier theorem at the exponent `p.toReal`
  obtain ⟨Cρ, hCρ, hgen⟩ := IwLqGeneral hA1 ρ hρ hρ1
  have hr : 1 < p.toReal := by
    rw [← ENNReal.toReal_one, ENNReal.toReal_lt_toReal ENNReal.one_ne_top htp.ne]
    exact hp
  obtain ⟨C₁, hC₁pos, hC₁⟩ := hgen p.toReal hr
  refine ⟨Cρ, hCρ, C₁, hC₁pos, ?_⟩
  intro l u hgood n₀ v
  -- the modulated cutoff is supported in `realArc (-(2u))` and its multiplier norms are bounded
  have hsupp : ∀ x : ℝ, modEtaCutSch (-n₀) (-(2 * (u : ℤ))) x ≠ 0 →
      x ∈ Work.Analysis.IonescuWainger.realArc (-(2 * (u : ℤ))) :=
    fun x hx => modEtaCutSch_support _ _ hx
  have hmult₁ : ∀ q : ℝ, 1 < q → Work.Analysis.IWMultiplier.IsLqMultiplierBound
      (ENNReal.ofReal q)
      ((modEtaCutSch (-n₀) (-(2 * (u : ℤ))) : SchwartzMap ℝ ℂ) : ℝ → ℂ) M := by
    intro q hq
    have h1q : (1 : ENNReal) ≤ ENNReal.ofReal q := by
      calc (1 : ENNReal) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        _ ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal hq.le
    have h := (hM (-(2 * (u : ℤ))) (-n₀) (ENNReal.ofReal q) h1q).1
    rw [modEtaCutSch_coe]
    exact h
  have hmult₂ : ∀ q : ℝ, 1 < q → Work.Analysis.IWMultiplier.IsLqMultiplierBound
      (ENNReal.ofReal q)
      (fun x => star ((modEtaCutSch (-n₀) (-(2 * (u : ℤ))) : SchwartzMap ℝ ℂ) x)) M := by
    intro q hq
    have h1q : (1 : ENNReal) ≤ ENNReal.ofReal q := by
      calc (1 : ENNReal) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        _ ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal hq.le
    have h := (hM (-(2 * (u : ℤ))) (-n₀) (ENNReal.ofReal q) h1q).2
    rw [modEtaCutSch_coe]
    exact h
  have hbound := hC₁ l (-(2 * (u : ℤ))) hgood (modEtaCutSch (-n₀) (-(2 * (u : ℤ)))) M
    hsupp hmult₁ hmult₂
  have hkey := fiberOpCum_eq_iwConv_comp ρ l u n₀ v
  rcases eq_or_ne M 0 with hM0 | hM0
  · -- `M = 0`: the `ℓᵖ` bound with constant `0` forces the whole IW kernel to vanish, hence the
    -- fibre itself vanishes pointwise (for *every* input `v`, bounded or not)
    have hzero : C₁ * Work.Analysis.IWMultiplier.angleBracket l * M = 0 := by rw [hM0, mul_zero]
    rw [hzero] at hbound
    have hb := hbound ℂ delta0 support_delta0
    have hb0 : MeasureTheory.eLpNorm
        (Work.Analysis.IWMultiplier.iwConv (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize
            (((modEtaCutSch (-n₀) (-(2 * (u : ℤ))) : SchwartzMap ℝ ℂ)) : ℝ → ℂ)) delta0)
        (ENNReal.ofReal p.toReal) (MeasureTheory.Measure.count : Measure ℤ) = 0 :=
      le_antisymm (by simpa using hb) zero_le
    have hker : ∀ n : ℤ, Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize
            (((modEtaCutSch (-n₀) (-(2 * (u : ℤ))) : SchwartzMap ℝ ℂ)) : ℝ → ℂ))) n = 0 := by
      intro n
      have hP : ENNReal.ofReal p.toReal ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
      have hx := eq_zero_of_eLpNorm_count_eq_zero
        (f := Work.Analysis.IWMultiplier.iwConv (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize
            (((modEtaCutSch (-n₀) (-(2 * (u : ℤ))) : SchwartzMap ℝ ℂ)) : ℝ → ℂ)) delta0)
        (P := ENNReal.ofReal p.toReal) hP hb0 n
      rwa [iwConv_delta0] at hx
    have hF : fiberOpCum ρ l (mStarF u) n₀ v = fun _ : ℤ => 0 := by
      funext x
      rw [fiberOpCum]
      have hz : (fun j : ℤ => (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
            fourier (T := 1) (n₀ - j) α) * cw (mStarF u) j * v (x - j)) = fun _ : ℤ => 0 := by
        funext j
        rw [fiberOpCum_kernel ρ l u n₀ j, hker (j - n₀), zero_mul]
      rw [hz, tsum_zero]
    rw [hF]
    simp [hM0]
  · -- `M ≠ 0`: extend the `IWLqBound` of the IW projection to all of `ℓᵖ`, then translate
    have hCpos : 0 < C₁ * Work.Analysis.IWMultiplier.angleBracket l * M := by
      have h2 : (0 : NNReal) < Work.Analysis.IWMultiplier.angleBracket l :=
        Work.Analysis.IWMultiplier.angleBracket_pos l
      exact mul_pos (mul_pos hC₁pos h2) (lt_of_le_of_ne (zero_le) (Ne.symm hM0))
    have hext := eLpNorm_iwConv_le_of_IWLqBound (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
      (modEtaCutSch (-n₀) (-(2 * (u : ℤ)))) hr hCpos hbound
    rw [show (fun x : ℤ => fiberOpCum ρ l (mStarF u) n₀ v x)
        = fun x : ℤ => Work.Analysis.IWMultiplier.iwConv
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize
              (((modEtaCutSch (-n₀) (-(2 * (u : ℤ))) : SchwartzMap ℝ ℂ)) : ℝ → ℂ)) v (x - n₀)
        from funext (fun x => congrFun hkey x)]
    rw [eLpNorm_comp_sub_count p n₀ _]
    rw [show p = ENNReal.ofReal p.toReal from (ENNReal.ofReal_toReal htp.ne).symm]
    refine (hext v).trans ?_
    rw [ENNReal.ofReal_coe_nnreal]

end

end Work.KMTAreas.A7
