import Mathlib
import Submission.Work.KMTAreas.A7.FiberL2Defs
import Submission.Work.KMTAreas.A7.aliasingSymbolProduct
import Submission.Work.KMTPlan.A6.IwKernelArithChar
import Submission.Work.KMTAreas.A5.fourierCoeff_mul_eq_tsum_conv

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

open MeasureTheory Finset Filter
open scoped BigOperators NNReal ENNReal Topology
open Work.Analysis.IonescuWainger

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

noncomputable section

/-! ## Poisson summation / the Fourier coefficients of the IW symbols -/

/-- **Poisson summation for a single integrable function.**  The `j`-th Fourier coefficient on
the circle of the periodisation of an integrable `m : ℝ → ℂ` is the continuous Fourier transform
`cw m j = ∫ θ, m θ · e(-jθ) dθ`. -/
theorem fourierCoeff_periodize_eq_cw {m : ℝ → ℂ} (hm : MeasureTheory.Integrable m) (j : ℤ) :
    fourierCoeff (periodize m) j = cw m j := by
  have h := Work.KMTPlan.A6.IwKernelArithChar (A := ({(0 : Circ)} : Finset Circ)) hm j
  have hsym : iwSymbolSet ({(0 : Circ)} : Finset Circ) (periodize m) = periodize m := by
    funext ξ; simp [iwSymbolSet]
  have hone : (∑ α ∈ ({(0 : Circ)} : Finset Circ), fourier (T := 1) (-j) α) = 1 := by simp
  rw [hsym, hone, one_mul] at h
  simpa [Work.Analysis.IWMultiplier.iwKernel] using h

/-- **The Fourier coefficients of an IW symbol.**  For a finite set `A` of circle frequencies, an
integrable profile `Ψ` and an integer `j`, the `j`-th Fourier coefficient of
`iwSymbolSet A Ψ = ∑_{α ∈ A} Ψ(· - α)` is the arithmetic character times the coefficient of `Ψ`. -/
theorem fourierCoeff_iwSymbolSet (A : Finset Circ) {Ψ : Circ → ℂ}
    (hΨ : MeasureTheory.Integrable Ψ circleMeasure) (j : ℤ) :
    fourierCoeff (iwSymbolSet A Ψ) j = (∑ α ∈ A, fourier (T := 1) (-j) α) * fourierCoeff Ψ j := by
  have hterm : ∀ α ∈ A, MeasureTheory.Integrable (fun ξ : Circ => Ψ (ξ - α)) circleMeasure :=
    fun α _ => hΨ.comp_sub_right α
  have hsymbol : (∑ α ∈ A, (fun ξ : Circ => Ψ (ξ - α))) = iwSymbolSet A Ψ := by
    funext ξ; simp [iwSymbolSet]
  have hsum := fourierCoeff.sum A (fun α => fun ξ : Circ => Ψ (ξ - α)) hterm
  have hmain : fourierCoeff (iwSymbolSet A Ψ) j
      = ∑ α ∈ A, fourierCoeff (fun ξ : Circ => Ψ (ξ - α)) j := by
    rw [← hsymbol]
    simpa using congrFun hsum j
  rw [hmain]
  refine (Finset.sum_congr rfl fun α _ => fourierCoeff_comp_sub Ψ α j).trans ?_
  rw [Finset.sum_mul]

/-- The IW symbol of an integrable profile is integrable. -/
theorem integrable_iwSymbolSet (A : Finset Circ) {Ψ : Circ → ℂ}
    (hΨ : MeasureTheory.Integrable Ψ circleMeasure) :
    MeasureTheory.Integrable (iwSymbolSet A Ψ) circleMeasure := by
  have hterm : ∀ α ∈ A, MeasureTheory.Integrable (fun ξ : Circ => Ψ (ξ - α)) circleMeasure :=
    fun α _ => hΨ.comp_sub_right α
  have hsymbol : (∑ α ∈ A, (fun ξ : Circ => Ψ (ξ - α))) = iwSymbolSet A Ψ := by
    funext ξ; simp [iwSymbolSet]
  rw [← hsymbol]
  exact integrable_finsetSum' A hterm

/-- If an integrable profile has absolutely summable Fourier coefficients, so does the IW symbol
built from it (the bound is the cardinality of the frequency set). -/
theorem summable_norm_fourierCoeff_iwSymbolSet (A : Finset Circ) {Ψ : Circ → ℂ}
    (hΨ : MeasureTheory.Integrable Ψ circleMeasure)
    (hs : Summable (fun j : ℤ => ‖fourierCoeff Ψ j‖)) :
    Summable (fun j : ℤ => ‖fourierCoeff (iwSymbolSet A Ψ) j‖) := by
  have hbound : Summable (fun j : ℤ => ((A.card : ℕ) : ℝ) * ‖fourierCoeff Ψ j‖) :=
    hs.mul_left _
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hbound
  rw [fourierCoeff_iwSymbolSet A hΨ j, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖∑ α ∈ A, fourier (T := 1) (-j) α‖ ≤ ∑ α ∈ A, ‖fourier (T := 1) (-j) α‖ :=
        norm_sum_le _ _
    _ = ∑ _α ∈ A, (1 : ℝ) :=
        Finset.sum_congr rfl (fun α _ => by rw [fourier_apply]; exact Circle.norm_coe _)
    _ = ((A.card : ℕ) : ℝ) := by simp

/-! ## The aliasing / plateau product identity -/

/-- Two points of two arcs around `a` and `b` bound the distance `‖a - b‖` by the sum of the
radii. -/
theorem norm_sub_le_of_mem_arcSet {a b : Circ} {r₁ r₂ : ℝ} {t : Circ}
    (h₁ : t ∈ Work.BourgainPlan.IonescuWainger.arcSet a r₁)
    (h₂ : t ∈ Work.BourgainPlan.IonescuWainger.arcSet b r₂) : ‖a - b‖ ≤ r₁ + r₂ := by
  obtain ⟨θ₁, hθ₁, hξ₁⟩ := h₁
  obtain ⟨θ₂, hθ₂, hξ₂⟩ := h₂
  have h : a + (θ₁ : Circ) = b + (θ₂ : Circ) := by rw [← hξ₁, ← hξ₂]
  have hEq : a - b = ((θ₂ - θ₁ : ℝ) : Circ) := by
    rw [AddCircle.coe_sub]
    have hkey : a - b
        = (a + (θ₁ : Circ)) - (b + (θ₂ : Circ)) + ((θ₂ : Circ) - (θ₁ : Circ)) := by abel
    rw [hkey, h]; abel
  rw [hEq]
  calc ‖((θ₂ - θ₁ : ℝ) : Circ)‖ ≤ |θ₂ - θ₁| :=
        Work.BourgainPlan.IonescuWainger.norm_circle_coe_le_abs _
    _ ≤ |θ₂| + |θ₁| := abs_sub _ _
    _ ≤ r₂ + r₁ := by linarith
    _ = r₁ + r₂ := by ring

/-- `8δ`-separation of the frequencies makes the arcs of radius `2δ` around them disjoint. -/
theorem arcSet_sep_of_hna {A : Finset Circ} {δ : ℝ} (hδ : 0 < δ)
    (hna : ∀ α ∈ A, ∀ β ∈ A, α ≠ β → 8 * δ ≤ ‖α - β‖) :
    ∀ a ∈ A, ∀ b ∈ A, ∀ t : Circ,
      t ∈ Work.BourgainPlan.IonescuWainger.arcSet a (2 * δ) →
      t ∈ Work.BourgainPlan.IonescuWainger.arcSet b (2 * δ) → a = b := by
  intro a ha b hb t h₁ h₂
  by_contra hne
  have h₁' := norm_sub_le_of_mem_arcSet h₁ h₂
  have h₂' := hna a ha b hb hne
  linarith

/-- **The aliasing product identity.**  If `M` is `1` on the `δ`-arc at `0` and vanishes off the
`2δ`-arc, if `Φ` vanishes off the `δ`-arc at `0`, and if the frequency set `A` is `8δ`-separated,
then `iwSymbolSet A M · iwSymbolSet A Φ = iwSymbolSet A Φ`. -/
theorem iwSymbolSet_plateau_mul {A : Finset Circ} {δ : ℝ} (hδ : 0 < δ)
    {M Φ : Circ → ℂ}
    (hm1 : ∀ ξ : Circ, (∃ θ : ℝ, |θ| ≤ δ ∧ (θ : Circ) = ξ) → M ξ = 1)
    (hms : ∀ ξ : Circ, M ξ ≠ 0 → ∃ θ : ℝ, |θ| ≤ 2 * δ ∧ (θ : Circ) = ξ)
    (hna : ∀ α ∈ A, ∀ β ∈ A, α ≠ β → 8 * δ ≤ ‖α - β‖)
    (hΦ : ∀ ξ : Circ, Φ ξ ≠ 0 → ∃ θ : ℝ, |θ| ≤ δ ∧ (θ : Circ) = ξ) :
    ∀ ζ : Circ, iwSymbolSet A M ζ * iwSymbolSet A Φ ζ = iwSymbolSet A Φ ζ := by
  have hm1' : ∀ th : Circ, th ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ → M th = 1 := by
    intro th hth
    obtain ⟨θ, hθ, hξ⟩ := hth
    exact hm1 th ⟨θ, hθ, by rw [hξ, zero_add]⟩
  have hms' : ∀ th : Circ, M th ≠ 0 →
      th ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 (2 * δ) := by
    intro th hth
    obtain ⟨θ, hθ, hξ⟩ := hms th hth
    exact ⟨θ, hθ, by rw [← hξ, zero_add]⟩
  have hp' : ∀ th : Circ, Φ th ≠ 0 →
      th ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ := by
    intro th hth
    obtain ⟨θ, hθ, hξ⟩ := hΦ th hth
    exact ⟨θ, hθ, by rw [← hξ, zero_add]⟩
  intro ζ
  have hgate := aliasingSymbolProduct A δ hδ (fun _ : Circ => 1) M Φ
    (arcSet_sep_of_hna hδ hna) hm1' hms' hp' ζ
  have hM : (∑ a ∈ A, (1 : ℂ) * M (ζ - a)) = iwSymbolSet A M ζ := by simp [iwSymbolSet]
  have hF : (∑ a ∈ A, Φ (ζ - a)) = iwSymbolSet A Φ ζ := by simp [iwSymbolSet]
  rw [hM, hF] at hgate
  simpa using hgate

/-! ## The circle measure is `volume`; Lebesgue uniqueness of Fourier coefficients -/

/-- For `T = 1` the normalised Haar measure `circleMeasure` is `volume`. -/
theorem circleMeasure_eq_volume :
    (Work.Analysis.IonescuWainger.circleMeasure : Measure Circ) = volume := by
  rw [Work.Analysis.IonescuWainger.circleMeasure, AddCircle.volume_eq_smul_haarAddCircle]
  simp

/-- **Uniqueness of the Fourier coefficients on `L¹(ℝ/ℤ)`.**  An integrable function all of whose
Fourier coefficients vanish is zero almost everywhere. -/
theorem fourierCoeff_eq_zero_ae {u : Circ → ℂ}
    (hu : MeasureTheory.Integrable u circleMeasure)
    (h : ∀ n : ℤ, fourierCoeff u n = 0) : u =ᵐ[circleMeasure] 0 := by
  -- (1) the characters
  have hgen : ∀ n : ℤ, ∫ t : Circ, fourier (T := 1) n t • u t ∂circleMeasure = 0 := by
    intro n
    have hh := h (-n)
    rw [fourierCoeff] at hh
    simpa using hh
  -- (2) finite linear combinations of characters
  have hspan : ∀ Q ∈ Submodule.span ℂ (Set.range (fourier (T := 1) : ℤ → C(Circ, ℂ))),
      ∫ t : Circ, (Q : Circ → ℂ) t * u t ∂circleMeasure = 0 := by
    intro Q hQ
    refine Submodule.span_induction
      (p := fun Q _ => ∫ t : Circ, Q t * u t ∂circleMeasure = 0) ?_ ?_ ?_ ?_ hQ
    · rintro _ ⟨n, rfl⟩
      simpa [smul_eq_mul] using hgen n
    · simp
    · intro x y hx hy hpx hpy
      have hxint : Integrable (fun t : Circ => (x : Circ → ℂ) t * u t) circleMeasure :=
        hu.bdd_mul (c := ‖x‖) x.continuous.aestronglyMeasurable
          (ae_of_all _ fun t => ContinuousMap.norm_coe_le_norm x t)
      have hyint : Integrable (fun t : Circ => (y : Circ → ℂ) t * u t) circleMeasure :=
        hu.bdd_mul (c := ‖y‖) y.continuous.aestronglyMeasurable
          (ae_of_all _ fun t => ContinuousMap.norm_coe_le_norm y t)
      have hfun : (fun t : Circ => ((x + y : C(Circ, ℂ)) : Circ → ℂ) t * u t)
          = fun t => (x : Circ → ℂ) t * u t + (y : Circ → ℂ) t * u t := by
        funext t; simp only [ContinuousMap.add_apply]; ring
      rw [hfun, integral_add hxint hyint, hpx, hpy, add_zero]
    · intro c x hx hpx
      have hfun : (fun t : Circ => ((c • x : C(Circ, ℂ)) : Circ → ℂ) t * u t)
          = fun t => c • ((x : Circ → ℂ) t * u t) := by
        funext t; simp only [ContinuousMap.smul_apply]; ring
      rw [hfun, integral_smul, hpx, smul_zero]
  -- (3) continuous test functions
  have hcont : ∀ ψ : C(Circ, ℂ), ∫ t : Circ, ψ t * u t ∂circleMeasure = 0 := by
    intro ψ
    have hdense : ψ ∈ closure ((Submodule.span ℂ
        (Set.range (fourier (T := 1) : ℤ → C(Circ, ℂ)))) : Set C(Circ, ℂ)) := by
      rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
      exact Submodule.mem_top
    have hK : (0 : ℝ) ≤ ∫ t : Circ, ‖u t‖ ∂circleMeasure := integral_nonneg (fun t => norm_nonneg _)
    have hψint : Integrable (fun t : Circ => ψ t * u t) circleMeasure :=
      hu.bdd_mul (c := ‖ψ‖) ψ.continuous.aestronglyMeasurable
        (ae_of_all _ fun t => ContinuousMap.norm_coe_le_norm ψ t)
    have hbound : ∀ ε > 0,
        ‖∫ t : Circ, ψ t * u t ∂circleMeasure‖ ≤ ε * (∫ t : Circ, ‖u t‖ ∂circleMeasure) := by
      intro ε hε
      obtain ⟨Q, hQ, hdist⟩ := Metric.mem_closure_iff.1 hdense ε hε
      have hQint : Integrable (fun t : Circ => (Q : Circ → ℂ) t * u t) circleMeasure :=
        hu.bdd_mul (c := ‖Q‖) Q.continuous.aestronglyMeasurable
          (ae_of_all _ fun t => ContinuousMap.norm_coe_le_norm Q t)
      have hdiff : (∫ t : Circ, ψ t * u t ∂circleMeasure)
            - (∫ t : Circ, (Q : Circ → ℂ) t * u t ∂circleMeasure)
          = ∫ t : Circ, (ψ t - (Q : Circ → ℂ) t) * u t ∂circleMeasure := by
        rw [← integral_sub hψint hQint]
        exact integral_congr_ae (ae_of_all _ fun t => by ring)
      have hzero : (∫ t : Circ, (Q : Circ → ℂ) t * u t ∂circleMeasure) = 0 := hspan Q hQ
      have hint : Integrable (fun t : Circ => ‖(ψ t - (Q : Circ → ℂ) t) * u t‖) circleMeasure := by
        refine (hψint.sub hQint).norm.congr ?_
        filter_upwards with t
        rw [Pi.sub_apply]
        congr 1
        ring
      have hle : ∫ t : Circ, ‖(ψ t - (Q : Circ → ℂ) t) * u t‖ ∂circleMeasure
          ≤ ε * ∫ t : Circ, ‖u t‖ ∂circleMeasure := by
        have h1 : ∀ t : Circ, ‖(ψ t - (Q : Circ → ℂ) t) * u t‖ ≤ ε * ‖u t‖ := by
          intro t
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          calc ‖ψ t - (Q : Circ → ℂ) t‖ = ‖(ψ - Q : C(Circ, ℂ)) t‖ := by
                rw [ContinuousMap.sub_apply]
            _ ≤ ‖(ψ - Q : C(Circ, ℂ))‖ := ContinuousMap.norm_coe_le_norm _ t
            _ = dist ψ Q := by rw [dist_eq_norm]
            _ ≤ ε := le_of_lt hdist
        calc ∫ t : Circ, ‖(ψ t - (Q : Circ → ℂ) t) * u t‖ ∂circleMeasure
            ≤ ∫ t : Circ, ε * ‖u t‖ ∂circleMeasure :=
              integral_mono hint (hu.norm.const_mul ε) h1
          _ = ε * ∫ t : Circ, ‖u t‖ ∂circleMeasure := integral_const_mul ε _
      calc ‖∫ t : Circ, ψ t * u t ∂circleMeasure‖
          = ‖∫ t : Circ, (ψ t - (Q : Circ → ℂ) t) * u t ∂circleMeasure‖ := by
            rw [← hdiff, hzero, sub_zero]
        _ ≤ ∫ t : Circ, ‖(ψ t - (Q : Circ → ℂ) t) * u t‖ ∂circleMeasure :=
            norm_integral_le_integral_norm _
        _ ≤ ε * ∫ t : Circ, ‖u t‖ ∂circleMeasure := hle
    have hzero : ‖∫ t : Circ, ψ t * u t ∂circleMeasure‖ = 0 := by
      refine le_antisymm ?_ (norm_nonneg _)
      refine le_of_forall_pos_le_add (fun ε hε => ?_)
      have h1 := hbound (ε / (∫ t : Circ, ‖u t‖ ∂circleMeasure + 1)) (by positivity)
      have h2 : (ε / (∫ t : Circ, ‖u t‖ ∂circleMeasure + 1))
          * (∫ t : Circ, ‖u t‖ ∂circleMeasure) ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [hK, hε.le]
      linarith [le_trans h1 h2]
    simpa using hzero
  -- (4) closed sets, via the `HasOuterApproxClosed` approximation
  have hclosed : ∀ F : Set Circ, IsClosed F → ∫ t in F, u t ∂circleMeasure = 0 := by
    intro F hF
    obtain ⟨fs, hfs1, hfsF, hfstend⟩ := HasOuterApproxClosed.exAppr F hF
    have hfs_cont : ∀ n : ℕ, Continuous fun t : Circ => ((fs n t : ℝ≥0) : ℂ) := fun n =>
      Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (fs n).continuous)
    have hfs_int : ∀ n : ℕ, ∫ t : Circ, ((fs n t : ℝ≥0) : ℂ) * u t ∂circleMeasure = 0 := by
      intro n
      have hh := hcont ⟨(fun t : Circ => ((fs n t : ℝ≥0) : ℂ)), hfs_cont n⟩
      simpa using hh
    have hlim : Tendsto (fun n : ℕ => ∫ t : Circ, ((fs n t : ℝ≥0) : ℂ) * u t ∂circleMeasure)
        atTop (𝓝 (∫ t : Circ, (F.indicator (fun _ => (1 : ℂ))) t * u t ∂circleMeasure)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (F := fun n (t : Circ) => ((fs n t : ℝ≥0) : ℂ) * u t)
        (f := fun t : Circ => (F.indicator (fun _ => (1 : ℂ))) t * u t)
        (bound := fun t : Circ => ‖u t‖) ?_ hu.norm ?_ ?_
      · intro n
        exact ((hfs_cont n).aestronglyMeasurable).mul hu.aestronglyMeasurable
      · intro n
        filter_upwards with t
        rw [norm_mul]
        have hb : ‖((fs n t : ℝ≥0) : ℂ)‖ ≤ 1 := by
          have h1 : ‖((((fs n t : ℝ≥0) : ℝ)) : ℂ)‖ = |(((fs n t : ℝ≥0) : ℝ))| := by simp
          rw [h1, abs_of_nonneg (by positivity)]
          exact_mod_cast hfs1 n t
        calc ‖((fs n t : ℝ≥0) : ℂ)‖ * ‖u t‖ ≤ 1 * ‖u t‖ :=
              mul_le_mul_of_nonneg_right hb (norm_nonneg _)
          _ = ‖u t‖ := one_mul _
      · filter_upwards with t
        have hpt : Tendsto (fun n : ℕ => fs n t) atTop
            (𝓝 ((F.indicator (fun _ => (1 : ℝ≥0))) t)) :=
          (tendsto_pi_nhds.mp hfstend) t
        have h2 : Tendsto (fun n : ℕ => ((fs n t : ℝ≥0) : ℂ)) atTop
            (𝓝 ((((F.indicator (fun _ => (1 : ℝ≥0))) t : ℝ≥0) : ℂ))) :=
          ((Complex.continuous_ofReal.comp NNReal.continuous_coe).tendsto _).comp hpt
        have h3 := h2.mul_const (u t)
        have hval : ((((F.indicator (fun _ => (1 : ℝ≥0))) t : ℝ≥0) : ℂ))
            = (F.indicator (fun _ => (1 : ℂ))) t := by
          by_cases ht : t ∈ F
          · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]; simp
          · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]; simp
        rwa [hval] at h3
    have h2 : Tendsto (fun n : ℕ => ∫ t : Circ, ((fs n t : ℝ≥0) : ℂ) * u t ∂circleMeasure)
        atTop (𝓝 0) := by
      rw [show (fun n : ℕ => ∫ t : Circ, ((fs n t : ℝ≥0) : ℂ) * u t ∂circleMeasure)
          = fun _ => 0 from funext hfs_int]
      exact tendsto_const_nhds
    have h3 : (∫ t : Circ, (F.indicator (fun _ => (1 : ℂ))) t * u t ∂circleMeasure) = 0 :=
      tendsto_nhds_unique hlim h2
    have hind : (fun t : Circ => (F.indicator (fun _ => (1 : ℂ))) t * u t) = F.indicator u := by
      funext t
      by_cases ht : t ∈ F
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]; simp
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]; simp
    rw [hind, integral_indicator hF.measurableSet] at h3
    exact h3
  -- (5) almost everywhere, by Lebesgue differentiation
  haveI :=
    show IsUnifLocDoublingMeasure (Work.Analysis.IonescuWainger.circleMeasure) from by
    rw [circleMeasure_eq_volume]
    infer_instance
  have hloc : LocallyIntegrable u circleMeasure := hu.locallyIntegrable
  have hdiff := IsUnifLocDoublingMeasure.ae_tendsto_average (μ := circleMeasure) hloc 1
  filter_upwards [hdiff] with x hx
  have hx' := hx (fun _ : ℝ => x) (fun r : ℝ => r) tendsto_id
    (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
      have h1 : (0 : ℝ) ≤ 1 * r := by rw [one_mul]; exact hr0
      simpa using Metric.mem_closedBall_self (x := x) (ε := 1 * r) h1)
  have hzero : Tendsto (fun r : ℝ => ⨍ y in Metric.closedBall x r, u y ∂circleMeasure)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with r
    rw [setAverage_eq, hclosed _ Metric.isClosed_closedBall, smul_zero]
  exact tendsto_nhds_unique hx' hzero
/-! ## Reassociation of a double `tsum`-convolution -/

/-- The shear `(j, i) ↦ (j + i, j)` of `ℤ × ℤ`. -/
def shearZ : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1 + p.2, p.1)
  invFun p := (p.2, p.1 - p.2)
  left_inv := by rintro ⟨j, i⟩; simp
  right_inv := by rintro ⟨k, j⟩; simp

@[simp] theorem shearZ_fst (p : ℤ × ℤ) : (shearZ p).1 = p.1 + p.2 := rfl
@[simp] theorem shearZ_snd (p : ℤ × ℤ) : (shearZ p).2 = p.1 := rfl

/-- Associativity of `tsum`-convolution over `ℤ`: the double sum of the summable family
`(j,i) ↦ a j · b i · u (n - j - i)` can be grouped either way. -/
theorem tsum_conv_conv {a b u : ℤ → ℂ} {C : ℝ}
    (ha : Summable fun j : ℤ => ‖a j‖) (hb : Summable fun j : ℤ => ‖b j‖)
    (hu : ∀ m : ℤ, ‖u m‖ ≤ C) (n : ℤ) :
    ∑' j : ℤ, a j * (∑' i : ℤ, b i * u (n - j - i))
      = ∑' m : ℤ, (∑' j : ℤ, a j * b (m - j)) * u (n - m) := by
  have hab : Summable fun p : ℤ × ℤ => ‖a p.1‖ * ‖b p.2‖ :=
    Summable.mul_of_nonneg ha hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hbnd : Summable fun p : ℤ × ℤ => ‖a p.1‖ * ‖b p.2‖ * C := hab.mul_right C
  have hF : Summable fun p : ℤ × ℤ => a p.1 * b p.2 * u (n - p.1 - p.2) := by
    refine Summable.of_norm_bounded hbnd (fun p => ?_)
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hu _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hSp : Summable fun p : ℤ × ℤ => a p.1 * (b p.2 * u (n - p.1 - p.2)) :=
    hF.congr (fun p => by ring)
  -- the left-hand side is the double sum of `F`
  have hA : ∑' j : ℤ, a j * (∑' i : ℤ, b i * u (n - j - i))
      = ∑' p : ℤ × ℤ, a p.1 * b p.2 * u (n - p.1 - p.2) := by
    rw [show (∑' j : ℤ, a j * (∑' i : ℤ, b i * u (n - j - i)))
          = ∑' j : ℤ, ∑' i : ℤ, a j * (b i * u (n - j - i)) from
        tsum_congr (fun j =>
          (tsum_mul_left (a := a j) (f := fun i => b i * u (n - j - i))).symm)]
    rw [← hSp.tsum_prod]
    exact tsum_congr (fun p => by ring)
  -- the summands of the right-hand side
  have hG : Summable fun p : ℤ × ℤ => a p.2 * b (p.1 - p.2) * u (n - p.1) := by
    have h1 : Summable ((fun p : ℤ × ℤ => a p.2 * b (p.1 - p.2) * u (n - p.1))
        ∘ shearZ) := by
      rw [show ((fun p : ℤ × ℤ => a p.2 * b (p.1 - p.2) * u (n - p.1))
          ∘ shearZ) = fun p : ℤ × ℤ => a p.1 * b p.2 * u (n - p.1 - p.2) from by
        funext p
        simp only [Function.comp_apply, shearZ_fst, shearZ_snd]
        rw [show p.1 + p.2 - p.1 = p.2 from by ring,
          show n - (p.1 + p.2) = n - p.1 - p.2 from by ring]]
      exact hF
    exact (Equiv.summable_iff shearZ).mp h1
  -- the right-hand side is the double sum of `G`
  have hB : ∑' m : ℤ, (∑' j : ℤ, a j * b (m - j)) * u (n - m)
      = ∑' p : ℤ × ℤ, a p.2 * b (p.1 - p.2) * u (n - p.1) := by
    rw [show (∑' m : ℤ, (∑' j : ℤ, a j * b (m - j)) * u (n - m))
          = ∑' m : ℤ, ∑' j : ℤ, a j * b (m - j) * u (n - m) from
        tsum_congr (fun m => (tsum_mul_right (a := u (n - m))
          (f := fun j : ℤ => a j * b (m - j))).symm)]
    rw [← hG.tsum_prod]
  have hC : (∑' p : ℤ × ℤ, a p.1 * b p.2 * u (n - p.1 - p.2))
      = ∑' p : ℤ × ℤ, a p.2 * b (p.1 - p.2) * u (n - p.1) := by
    rw [show (∑' p : ℤ × ℤ, a p.1 * b p.2 * u (n - p.1 - p.2))
          = ∑' p : ℤ × ℤ, a (shearZ p).2
              * b ((shearZ p).1 - (shearZ p).2) * u (n - (shearZ p).1)
        from tsum_congr (fun p => by
          simp only [shearZ_fst, shearZ_snd]
          rw [show p.1 + p.2 - p.1 = p.2 from by ring,
            show n - (p.1 + p.2) = n - p.1 - p.2 from by ring])]
    exact Equiv.tsum_eq shearZ (fun p : ℤ × ℤ => a p.2 * b (p.1 - p.2) * u (n - p.1))
  calc ∑' j : ℤ, a j * (∑' i : ℤ, b i * u (n - j - i))
      = ∑' p : ℤ × ℤ, a p.1 * b p.2 * u (n - p.1 - p.2) := hA
    _ = ∑' p : ℤ × ℤ, a p.2 * b (p.1 - p.2) * u (n - p.1) := hC
    _ = ∑' m : ℤ, (∑' j : ℤ, a j * b (m - j)) * u (n - m) := hB.symm

/-! ## The product theorem for Fourier coefficients in the `ℓ¹` regime -/

/-- `fourierCoeff` is additive over differences of integrable functions (pointwise form). -/
theorem fourierCoeff_sub_apply {f g : Circ → ℂ} (hf : MeasureTheory.Integrable f circleMeasure)
    (hg : MeasureTheory.Integrable g circleMeasure) (j : ℤ) :
    fourierCoeff (f - g) j = fourierCoeff f j - fourierCoeff g j := by
  have h1 : fourierCoeff (f + -g) j = fourierCoeff f j + fourierCoeff (-g) j :=
    congrFun (fourierCoeff.add hf hg.neg) j
  have h2 : fourierCoeff (-g) j = - fourierCoeff g j := by
    have h3 := fourierCoeff.const_smul g (-1 : ℂ) j
    rw [show ((-1 : ℂ) • g) = -g from by funext ξ; simp, smul_eq_mul] at h3
    simpa using h3
  rw [show (f - g) = f + -g from sub_eq_add_neg f g, h1, h2]
  ring

/-- **The product theorem for Fourier coefficients.**  If `F` and `G` are integrable with
absolutely summable Fourier coefficients, then the Fourier coefficients of the pointwise product
are the convolution of the coefficient sequences. -/
theorem fourierCoeff_mul_l1 {F G : Circ → ℂ}
    (hF : MeasureTheory.Integrable F circleMeasure)
    (hG : MeasureTheory.Integrable G circleMeasure)
    (hFG : MeasureTheory.Integrable (fun ξ => F ξ * G ξ) circleMeasure)
    (hFs : Summable (fun j : ℤ => fourierCoeff F j))
    (hGs : Summable (fun j : ℤ => fourierCoeff G j)) (m : ℤ) :
    fourierCoeff (fun ξ => F ξ * G ξ) m
      = ∑' j : ℤ, fourierCoeff F j * fourierCoeff G (m - j) := by
  have hFnorm : Summable (fun j : ℤ => ‖fourierCoeff F j‖) := hFs.norm
  have hGnorm : Summable (fun j : ℤ => ‖fourierCoeff G j‖) := hGs.norm
  -- the continuous model of `F`
  obtain ⟨Fc, hFc⟩ : ∃ Fc : C(Circ, ℂ),
      ∀ ξ, HasSum (fun j => fourierCoeff F j * fourier (T := 1) j ξ) (Fc ξ) := by
    have hsummC : Summable
        (fun j : ℤ => fourierCoeff F j • (fourier (T := 1) j : C(Circ, ℂ))) := by
      refine Summable.of_norm_bounded hFnorm (fun j => ?_)
      rw [norm_smul, fourier_norm, mul_one]
    refine ⟨∑' j, fourierCoeff F j • (fourier (T := 1) j : C(Circ, ℂ)), fun ξ => ?_⟩
    simpa using (ContinuousMap.evalCLM ℂ ξ).hasSum hsummC.hasSum
  have hFc_coeff : fourierCoeff (⇑Fc) = fun j => fourierCoeff F j :=
    Work.Analysis.Fourier.fourierCoeff_summable_series hFnorm hFc
  have hFc_int : MeasureTheory.Integrable (⇑Fc) circleMeasure :=
    (MeasureTheory.MemLp.of_bound Fc.continuous.aestronglyMeasurable ‖Fc‖
      (ae_of_all _ fun ξ => ContinuousMap.norm_coe_le_norm Fc ξ)).integrable le_rfl
  have hFeq : F =ᵐ[circleMeasure] ⇑Fc := by
    have hz : (F - ⇑Fc) =ᵐ[circleMeasure] 0 :=
      fourierCoeff_eq_zero_ae (hF.sub hFc_int) (fun j => by
        rw [fourierCoeff_sub_apply hF hFc_int j, congrFun hFc_coeff j, sub_self])
    filter_upwards [hz] with ξ hξ
    simpa using sub_eq_zero.mp hξ
  -- the continuous model of `G`
  obtain ⟨Gc, hGc⟩ : ∃ Gc : C(Circ, ℂ),
      ∀ ξ, HasSum (fun j => fourierCoeff G j * fourier (T := 1) j ξ) (Gc ξ) := by
    have hsummC : Summable
        (fun j : ℤ => fourierCoeff G j • (fourier (T := 1) j : C(Circ, ℂ))) := by
      refine Summable.of_norm_bounded hGnorm (fun j => ?_)
      rw [norm_smul, fourier_norm, mul_one]
    refine ⟨∑' j, fourierCoeff G j • (fourier (T := 1) j : C(Circ, ℂ)), fun ξ => ?_⟩
    simpa using (ContinuousMap.evalCLM ℂ ξ).hasSum hsummC.hasSum
  have hGc_coeff : fourierCoeff (⇑Gc) = fun j => fourierCoeff G j :=
    Work.Analysis.Fourier.fourierCoeff_summable_series hGnorm hGc
  have hGc_int : MeasureTheory.Integrable (⇑Gc) circleMeasure :=
    (MeasureTheory.MemLp.of_bound Gc.continuous.aestronglyMeasurable ‖Gc‖
      (ae_of_all _ fun ξ => ContinuousMap.norm_coe_le_norm Gc ξ)).integrable le_rfl
  have hGeq : G =ᵐ[circleMeasure] ⇑Gc := by
    have hz : (G - ⇑Gc) =ᵐ[circleMeasure] 0 :=
      fourierCoeff_eq_zero_ae (hG.sub hGc_int) (fun j => by
        rw [fourierCoeff_sub_apply hG hGc_int j, congrFun hGc_coeff j, sub_self])
    filter_upwards [hz] with ξ hξ
    simpa using sub_eq_zero.mp hξ
  -- the coefficients of the products agree almost everywhere
  have hprod := Work.KMTAreas.A5.fourierCoeff_mul_eq_tsum_conv
    (F := ⇑Fc) (G := ⇑Gc)
    (MeasureTheory.MemLp.of_bound Fc.continuous.aestronglyMeasurable ‖Fc‖
      (ae_of_all _ fun ξ => ContinuousMap.norm_coe_le_norm Fc ξ))
    (MeasureTheory.MemLp.of_bound Gc.continuous.aestronglyMeasurable ‖Gc‖
      (ae_of_all _ fun ξ => ContinuousMap.norm_coe_le_norm Gc ξ))
    (by simpa [hFc_coeff] using hFnorm) m
  have hcongr : fourierCoeff (fun ξ => F ξ * G ξ)
      = fourierCoeff (fun ξ => (⇑Fc) ξ * (⇑Gc) ξ) :=
    fourierCoeff_congr_ae (hFeq.mul hGeq)
  rw [congrFun hcongr m, hprod]
  exact tsum_congr (fun j => by rw [congrFun hFc_coeff j, congrFun hGc_coeff (m - j)])

/-! ## The fibre at residue zero, and the composition with the exact-height projection -/

/-- The IW convolution as the convolution with the Fourier coefficients of its symbol. -/
theorem iwConv_eq_tsum_fourierCoeff (A : Finset Circ) (Ψ : Circ → ℂ) (v : ℤ → ℂ) (n : ℤ) :
    Work.Analysis.IWMultiplier.iwConv A Ψ v n
      = ∑' j : ℤ, fourierCoeff (iwSymbolSet A Ψ) j * v (n - j) := by
  rw [Work.Analysis.IWMultiplier.iwConv_apply]
  exact tsum_congr (fun j => by rw [Work.Analysis.IWMultiplier.iwKernel, smul_eq_mul])

/-- **The fibre at residue `0`.**  For the exact-height frequency set, `fiberOp ρ l m 0` is the
convolution with the Fourier coefficients of `iwSymbolSet (ℚ/ℤ)_l (periodize m)`. -/
theorem fiberOp_zero_eq_tsum (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (hm : MeasureTheory.Integrable m)
    (u : ℤ → ℂ) (x : ℤ) :
    fiberOp ρ l m 0 u x
      = ∑' j : ℤ, fourierCoeff (iwSymbolSet (iwArithFreqsNew ρ l) (periodize m)) j * u (x - j) := by
  rw [fiberOp_eq_kernel_conv]
  refine tsum_congr (fun j => ?_)
  rw [fourierCoeff_iwSymbolSet (iwArithFreqsNew ρ l)
      (Work.KMTPlan.A6.IntegrablePeriodize hm) j, fourierCoeff_periodize_eq_cw hm j]
  simp only [zero_sub]

/-- **The fibre at residue `0` is the IW multiplier of the periodisation of `m`.** -/
theorem fiberOp_zero_eq_iwConv (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (hm : MeasureTheory.Integrable m)
    (u : ℤ → ℂ) :
    fiberOp ρ l m 0 u
      = Work.Analysis.IWMultiplier.iwConv (iwArithFreqsNew ρ l) (periodize m) u := by
  funext x
  rw [fiberOp_zero_eq_tsum ρ l m hm u x,
    iwConv_eq_tsum_fourierCoeff (iwArithFreqsNew ρ l) (periodize m) u x]

/-- **The wide-cut identity.**  Under the plateau/support/separation hypotheses on `m`, `φ` and
the arithmetic frequency set, the fibre at residue `0` of `m` fixes the exact-height projection
`Tex ρ l φ f` of any bounded sequence `f`. -/
theorem iwConv_comp_plateau (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hm : MeasureTheory.Integrable m)
    (hmsum : Summable (fun j : ℤ => cw m j))
    (hm1 : ∀ ξ : Circ, (∃ θ : ℝ, |θ| ≤ δ ∧ (θ : Circ) = ξ) → periodize m ξ = 1)
    (hms : ∀ ξ : Circ, periodize m ξ ≠ 0 → ∃ θ : ℝ, |θ| ≤ 2 * δ ∧ (θ : Circ) = ξ)
    (hna : ∀ α ∈ iwArithFreqsNew ρ l, ∀ β ∈ iwArithFreqsNew ρ l, α ≠ β → 8 * δ ≤ ‖α - β‖)
    (φ : ℝ → ℂ) (hφ : MeasureTheory.Integrable φ)
    (hφsum : Summable (fun j : ℤ => cw φ j))
    (hφpacket : ∀ ξ : Circ, periodize φ ξ ≠ 0 → ∃ θ : ℝ, |θ| ≤ δ ∧ (θ : Circ) = ξ)
    (f : ℤ → ℂ) (hf : ∃ B : ℝ, ∀ y : ℤ, ‖f y‖ ≤ B) :
    Work.Analysis.IWMultiplier.iwConv (iwArithFreqsNew ρ l) (periodize m) (Tex ρ l φ f)
      = Tex ρ l φ f := by
  obtain ⟨B, hB⟩ := hf
  have hMint : MeasureTheory.Integrable (periodize m) circleMeasure :=
    Work.KMTPlan.A6.IntegrablePeriodize hm
  have hPint : MeasureTheory.Integrable (periodize φ) circleMeasure :=
    Work.KMTPlan.A6.IntegrablePeriodize hφ
  have hSint : MeasureTheory.Integrable
      (iwSymbolSet (iwArithFreqsNew ρ l) (periodize m)) circleMeasure :=
    integrable_iwSymbolSet _ hMint
  have hTint : MeasureTheory.Integrable
      (iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ)) circleMeasure :=
    integrable_iwSymbolSet _ hPint
  have hgate : ∀ ζ : Circ, iwSymbolSet (iwArithFreqsNew ρ l) (periodize m) ζ
      * iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ) ζ
      = iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ) ζ :=
    iwSymbolSet_plateau_mul (A := iwArithFreqsNew ρ l) hδ hm1 hms hna hφpacket
  have hFGint : MeasureTheory.Integrable (fun ξ : Circ =>
      iwSymbolSet (iwArithFreqsNew ρ l) (periodize m) ξ
        * iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ) ξ) circleMeasure :=
    hTint.congr (Filter.Eventually.of_forall (fun ξ => (hgate ξ).symm))
  have hMs0 : Summable (fun j : ℤ => ‖fourierCoeff (periodize m) j‖) :=
    hmsum.norm.congr (fun j => by rw [fourierCoeff_periodize_eq_cw hm j])
  have hPs0 : Summable (fun j : ℤ => ‖fourierCoeff (periodize φ) j‖) :=
    hφsum.norm.congr (fun j => by rw [fourierCoeff_periodize_eq_cw hφ j])
  have hMs : Summable (fun j : ℤ => fourierCoeff
      (iwSymbolSet (iwArithFreqsNew ρ l) (periodize m)) j) :=
    (summable_norm_fourierCoeff_iwSymbolSet _ hMint hMs0).of_norm
  have hPs : Summable (fun j : ℤ => fourierCoeff
      (iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ)) j) :=
    (summable_norm_fourierCoeff_iwSymbolSet _ hPint hPs0).of_norm
  have hMs' : Summable (fun j : ℤ => ‖fourierCoeff
      (iwSymbolSet (iwArithFreqsNew ρ l) (periodize m)) j‖) := hMs.norm
  have hPs' : Summable (fun j : ℤ => ‖fourierCoeff
      (iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ)) j‖) := hPs.norm
  have Kaprod : ∀ p : ℤ, ∑' j : ℤ,
        fourierCoeff (iwSymbolSet (iwArithFreqsNew ρ l) (periodize m)) j
          * fourierCoeff (iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ)) (p - j)
      = fourierCoeff (iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ)) p := by
    intro p
    rw [← fourierCoeff_mul_l1 hSint hTint hFGint hMs hPs p]
    exact congrFun (fourierCoeff_congr_ae (Filter.Eventually.of_forall hgate)) p
  have hcomp : Work.Analysis.IWMultiplier.iwConv (iwArithFreqsNew ρ l) (periodize m)
      (Tex ρ l φ f) = Tex ρ l φ f := by
    funext n
    have hR : Tex ρ l φ f n = ∑' j : ℤ,
        fourierCoeff (iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ)) j * f (n - j) := by
      rw [Tex]
      exact iwConv_eq_tsum_fourierCoeff _ _ _ _
    calc Work.Analysis.IWMultiplier.iwConv (iwArithFreqsNew ρ l) (periodize m)
          (Tex ρ l φ f) n
        = ∑' j : ℤ, fourierCoeff (iwSymbolSet (iwArithFreqsNew ρ l) (periodize m)) j
            * (Work.Analysis.IWMultiplier.iwConv (iwArithFreqsNew ρ l) (periodize φ) f)
                (n - j) :=
          iwConv_eq_tsum_fourierCoeff _ _ _ _
      _ = ∑' j : ℤ, fourierCoeff (iwSymbolSet (iwArithFreqsNew ρ l) (periodize m)) j
            * (∑' i : ℤ, fourierCoeff (iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ)) i
                * f (n - j - i)) :=
          tsum_congr (fun j => by rw [iwConv_eq_tsum_fourierCoeff])
      _ = ∑' p : ℤ, (∑' j : ℤ,
              fourierCoeff (iwSymbolSet (iwArithFreqsNew ρ l) (periodize m)) j
                * fourierCoeff (iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ)) (p - j))
            * f (n - p) :=
          tsum_conv_conv
            (a := fun j : ℤ => fourierCoeff (iwSymbolSet (iwArithFreqsNew ρ l) (periodize m)) j)
            (b := fun i : ℤ => fourierCoeff (iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ)) i)
            (u := f) (C := B) hMs' hPs' hB n
      _ = ∑' p : ℤ, fourierCoeff (iwSymbolSet (iwArithFreqsNew ρ l) (periodize φ)) p
            * f (n - p) :=
          tsum_congr (fun p => by rw [Kaprod p])
      _ = Tex ρ l φ f n := hR.symm
  exact hcomp

theorem FiberOpWideCutEqSelf (ρ : ℝ) (hρ : 0 < ρ) (l : ℕ) (m : ℝ → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hm : MeasureTheory.Integrable m)
    (hmsum : Summable (fun j : ℤ => Work.KMTAreas.A7.cw m j))
    (hm1 : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      (∃ θ : ℝ, |θ| ≤ δ ∧ (θ : Work.Analysis.IonescuWainger.Circle) = ξ) →
      Work.Analysis.IonescuWainger.periodize m ξ = 1)
    (hms : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      Work.Analysis.IonescuWainger.periodize m ξ ≠ 0 →
      ∃ θ : ℝ, |θ| ≤ 2 * δ ∧ (θ : Work.Analysis.IonescuWainger.Circle) = ξ)
    (hna : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
      ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l, α ≠ β → 8 * δ ≤ ‖α - β‖)
    (φ : ℝ → ℂ) (hφ : MeasureTheory.Integrable φ)
    (hφsum : Summable (fun j : ℤ => Work.KMTAreas.A7.cw φ j))
    (hφpacket : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      Work.Analysis.IonescuWainger.periodize φ ξ ≠ 0 →
      ∃ θ : ℝ, |θ| ≤ δ ∧ (θ : Work.Analysis.IonescuWainger.Circle) = ξ)
    (f : ℤ → ℂ) (hf : ∃ B : ℝ, ∀ y : ℤ, ‖f y‖ ≤ B) :
    Work.KMTAreas.A7.fiberOp ρ l m 0 (Work.KMTAreas.A7.Tex ρ l φ f)
      = Work.KMTAreas.A7.Tex ρ l φ f := by
  rw [fiberOp_zero_eq_iwConv ρ l m hm (Tex ρ l φ f)]
  exact iwConv_comp_plateau ρ l m δ hδ hm hmsum hm1 hms hna φ hφ hφsum hφpacket f hf

end

end Work.KMTAreas.A7
