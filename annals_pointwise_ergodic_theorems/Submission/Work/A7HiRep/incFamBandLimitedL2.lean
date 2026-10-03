import Mathlib
import Submission.Work.KMTAreas.A7HiRep.incDefs
import Submission.Work.KMTAreas.A7.tex_hasFreqSupport_of_memlp
import Submission.Work.KMTAreas.A7Hi.summable_normSq_incFam
import Submission.Work.KMTAreas.A7.Tle_finsetSum_of_bounded

/-!
# Band-limitation of the increments of the Ionescu--Wainger low-pass family

`Work.KMTAreas.A7HiRep.incFam ρ l₁ m₀ m f x = lpf ρ l₁ m₀ (m+1) f x − lpf ρ l₁ m₀ m f x` is the
difference of the two IW projections `kmtProj ρ l₁ k` at the consecutive heights
`k = -((m₀ + m) + 1)` and `k = -(m₀ + m)`.  In this file we prove that it lies in `ℓ²(ℤ)` whenever
`f` does, and that its Fourier transform is supported in the union of the major arcs
`α + ℝ_{≤ -(m₀+m)}`, `α ∈ (ℚ/ℤ)_{≤l₁}` (`Work.KMTAreas.A7HiRep.incArc`).

The proof route is the `ℓ²(ℤ) ≅ L²(𝕋)` dictionary of
`Submission/Work/BourgainPlan/IonescuWainger/FourierL2Defs.lean`:

* `kmtProj ρ l k` is identified with the Fourier multiplier `opMul Φ f` whose symbol `Φ` is the
  `L^∞` class of the IW symbol `Σ_{α ∈ (ℚ/ℤ)_{≤l}} η((· - α)/2^k)`
  (`Work.KMTPlan.A6.iwConvEqIwOpSetMemlp` together with `fourierZ_multiplier`), and
  `hasFreqSupport_opMul` gives the frequency support of a multiplier inside the support of its
  symbol (this is the argument of `Submission/Work/KMTAreas/A7/hasFreqSupport_iwConv_singleton.lean`,
  re-used here in the form needed for the projections);
* the symbol of each projection is supported in the corresponding union of arcs
  (`iwSymbolSet_etaCut_support_incArc`, from `supportedInArc_periodize` and the elementary support
  of `η_{≤k}`), and *the difference* of the two symbols is supported in the coarser arc, because
  `incArc ρ l k' ⊆ incArc ρ l k` for `k' ≤ k`;
* the passage from `ftLp` to a difference is `ftLp_sub`, and the resulting support statement is
  `hasFreqSupport_sub`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.A7HiRep

open MeasureTheory
open scoped ENNReal NNReal BigOperators

local notation "Circ" => Work.Analysis.IonescuWainger.Circle
local notation "HS" => Work.BourgainPlan.IonescuWainger.HasFreqSupport
local notation "FT" => Work.BourgainPlan.IonescuWainger.ftLp

/-! ## Elementary support lemmas -/

/-- The Ionescu--Wainger symbol of the Littlewood--Paley cutoff `η_{≤k}` vanishes off the union of
the arcs `α + ℝ_{≤k}`, `α ∈ (ℚ/ℤ)_{≤l}`: a nonzero value exhibits such a frequency and a point of
`ℝ_{≤k}` whose sum is it (the support of `periodize (etaCut η k)` is in `ℝ_{≤k}`). -/
theorem iwSymbolSet_etaCut_support_incArc (ρ : ℝ) (l₁ : ℕ) (k : ℤ) (ξ : Circ) :
    Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
        (Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k)) ξ ≠ 0 →
      ξ ∈ Work.KMTAreas.A7HiRep.incArc ρ l₁ k := by
  intro h
  have hsupp := Work.Analysis.IonescuWainger.supportedInArc_periodize
    (k := k) (φ := Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k)
    (fun x hx => Work.KMTAreas.A7.etaCut_ne_zero_mem_realArc k hx)
    (fun x => Work.KMTAreas.A7.summable_etaCut_shift k x)
  rw [Work.Analysis.IonescuWainger.iwSymbolSet_apply] at h
  obtain ⟨α, hα, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨θ, hθ, hθξ⟩ := hsupp _ hne
  exact ⟨α, hα, θ, hθ, sub_eq_iff_eq_add'.mp hθξ.symm⟩

/-- The increment arc is monotone in the height. -/
theorem incArc_mono (ρ : ℝ) (l : ℕ) {k k' : ℤ} (h : k ≤ k') :
    Work.KMTAreas.A7HiRep.incArc ρ l k ⊆ Work.KMTAreas.A7HiRep.incArc ρ l k' := by
  rintro ξ ⟨α, hα, θ, hθ, rfl⟩
  exact ⟨α, hα, θ, Work.Analysis.IonescuWainger.realArc_mono h hθ, rfl⟩

/-- `HasFreqSupport` is monotone in the support set. -/
theorem hasFreqSupport_mono {h : ℤ → ℂ} {hh : Memℓp h 2} {E E' : Set Circ} (hEE : E' ⊆ E)
    (hE : HS h hh E') : HS h hh E := by
  unfold Work.BourgainPlan.IonescuWainger.HasFreqSupport at *
  filter_upwards [hE] with θ hθ hθE
  exact hθ fun hx => hθE (hEE hx)

/-- `ftLp` is additive for the *difference* of two sequences. -/
theorem ftLp_sub {f g : ℤ → ℂ} (hf : Memℓp f 2) (hg : Memℓp g 2) :
    FT (f - g) (hf.sub hg) = FT f hf - FT g hg := by
  unfold Work.BourgainPlan.IonescuWainger.ftLp
  rw [show (⟨f - g, hf.sub hg⟩ : Work.Analysis.IonescuWainger.L2Z)
      = ⟨f, hf⟩ - ⟨g, hg⟩ from rfl]
  exact map_sub _ _ _

/-- The frequency support of a difference of two band-limited sequences is contained in the
support set of either of them. -/
theorem hasFreqSupport_sub {a b : ℤ → ℂ} (ha : Memℓp a 2) (hb : Memℓp b 2) {E : Set Circ}
    (haE : HS a ha E) (hbE : HS b hb E) : HS (a - b) (ha.sub hb) E := by
  unfold Work.BourgainPlan.IonescuWainger.HasFreqSupport at *
  filter_upwards [MeasureTheory.Lp.coeFn_sub (FT a ha) (FT b hb), haE, hbE] with
    θ hcoe haθ hbθ hθE
  rw [ftLp_sub ha hb, hcoe]
  simp only [Pi.sub_apply]
  rw [haθ hθE, hbθ hθE]
  simp

/-- Transfer of a band-limitation statement along an equality of the underlying sequences. -/
theorem exists_hasFreqSupport_congr {h h' : ℤ → ℂ} (hfun : h = h') {E : Set Circ}
    (hEx : ∃ hh : Memℓp h 2, HS h hh E) : ∃ hh' : Memℓp h' 2, HS h' hh' E := by
  obtain ⟨hh, hhE⟩ := hEx
  subst hfun
  exact ⟨hh, hhE⟩

/-! ## Band-limitation of a single Ionescu--Wainger projection -/

/-- **The Fourier transform of the IW projection `kmtProj ρ l k` of an `ℓ²` sequence is supported
in the union of the major arcs `α + ℝ_{≤k}`, `α ∈ (ℚ/ℤ)_{≤l}`.**

Route: `kmtProj ρ l k = opMul Φ` with `Φ` the `L^∞` class of the IW symbol (`iwConvEqIwOpSetMemlp`
and `fourierZ_multiplier` identify the sequence with the multiplier applied to `f`), and
`hasFreqSupport_opMul` bounds the frequency support by the support of the symbol, which is
`incArc ρ l k` by `iwSymbolSet_etaCut_support_incArc`. -/
theorem exists_hasFreqSupport_kmtProj (ρ : ℝ) (l : ℕ) (k : ℤ) (f : ℤ → ℂ) (hf : Memℓp f 2) :
    ∃ h : Memℓp (Work.KMTContract.kmtProj ρ l k f) 2,
      HS (Work.KMTContract.kmtProj ρ l k f) h (Work.KMTAreas.A7HiRep.incArc ρ l k) := by
  set A : Finset Circ := Work.Analysis.IonescuWainger.iwArithFreqs ρ l with hA
  set Ψ : Circ → ℂ := Work.Analysis.IonescuWainger.periodize
      (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) with hΨ
  set σ : Circ → ℂ := Work.Analysis.IonescuWainger.iwSymbolSet A Ψ with hσ
  have hΨm : MeasureTheory.MemLp Ψ ⊤ Work.Analysis.IonescuWainger.circleMeasure :=
    Work.KMTAreas.A7.memLp_periodize_etaCut k
  have hsym : MeasureTheory.MemLp σ ⊤ Work.Analysis.IonescuWainger.circleMeasure :=
    Work.Analysis.IWMultiplier.memLp_iwSymbolSet A hΨm
  set F : Work.Analysis.IonescuWainger.L2Z := ⟨f, hf⟩ with _hF
  -- The kernel form of the projection is the multiplier form.
  have hconvOp : ⇑((Work.Analysis.IonescuWainger.iwOpSet A Ψ hsym) F)
      = Work.KMTContract.kmtProj ρ l k f := by
    rw [← Work.KMTPlan.A6.iwConvEqIwOpSetMemlp hsym F]
    rfl
  have hconv : ⇑((Work.Analysis.IonescuWainger.multiplier (hsym.toLp σ)) F)
      = Work.KMTContract.kmtProj ρ l k f := by
    simpa only [Work.Analysis.IonescuWainger.iwOpSet,
      Work.Analysis.IonescuWainger.multiplierOf, hσ] using hconvOp
  -- The multiplier form is the sequence form `opMul`.
  have hopEq : Work.BourgainPlan.IonescuWainger.opMul (hsym.toLp σ) f hf
      = ⇑((Work.Analysis.IonescuWainger.multiplier (hsym.toLp σ)) F) := by
    have h1 : FT (Work.BourgainPlan.IonescuWainger.opMul (hsym.toLp σ) f hf)
          (Work.BourgainPlan.IonescuWainger.opMul_memℓp (hsym.toLp σ) f hf)
        = (hsym.toLp σ) • FT f hf :=
      Work.BourgainPlan.IonescuWainger.ftLp_opMul (hsym.toLp σ) f hf
    have h2 : FT f hf = Work.Analysis.IonescuWainger.fourierZ F := rfl
    have h3 : Work.Analysis.IonescuWainger.fourierZ
        ((Work.Analysis.IonescuWainger.multiplier (hsym.toLp σ)) F)
        = (hsym.toLp σ) • Work.Analysis.IonescuWainger.fourierZ F :=
      Work.Analysis.IonescuWainger.fourierZ_multiplier (hsym.toLp σ) F
    have key : (⟨Work.BourgainPlan.IonescuWainger.opMul (hsym.toLp σ) f hf,
          Work.BourgainPlan.IonescuWainger.opMul_memℓp (hsym.toLp σ) f hf⟩
            : Work.Analysis.IonescuWainger.L2Z)
        = (Work.Analysis.IonescuWainger.multiplier (hsym.toLp σ)) F := by
      apply Work.Analysis.IonescuWainger.fourierZ.injective
      show FT _ _ = _
      rw [h1, h2, h3]
    exact congrArg (fun x : Work.Analysis.IonescuWainger.L2Z => ⇑x) key
  -- The symbol vanishes off the increment arc.
  have hΦ : ∀ᵐ ξ ∂Work.Analysis.IonescuWainger.circleMeasure,
      ξ ∉ Work.KMTAreas.A7HiRep.incArc ρ l k → ((hsym.toLp σ : Circ → ℂ)) ξ = 0 := by
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp hsym] with ξ hξ hmem
    rw [hξ]
    by_contra hne
    rw [hσ, hA, hΨ] at hne
    exact hmem (iwSymbolSet_etaCut_support_incArc ρ l k ξ hne)
  refine exists_hasFreqSupport_congr (hopEq.trans hconv) ?_
  exact ⟨Work.BourgainPlan.IonescuWainger.opMul_memℓp (hsym.toLp σ) f hf,
    Work.BourgainPlan.IonescuWainger.hasFreqSupport_opMul (hsym.toLp σ) f hf hΦ⟩

/-! ## The increment family -/

theorem incFamBandLimitedL2 (ρ : ℝ) (l₁ m₀ m : ℕ) (f : ℤ → ℂ) (hf : Memℓp f 2) :
    ∃ hg : Memℓp (Work.KMTAreas.A7HiRep.incFam ρ l₁ m₀ m f) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport (Work.KMTAreas.A7HiRep.incFam ρ l₁ m₀ m f) hg
        (Work.KMTAreas.A7HiRep.incArc ρ l₁ (-((m₀ : ℤ) + (m : ℤ)))) := by
  set k : ℤ := -((m₀ : ℤ) + (m : ℤ)) with hk
  obtain ⟨ha, haE⟩ := exists_hasFreqSupport_kmtProj ρ l₁ (-((m₀ : ℤ) + ((m + 1 : ℕ) : ℤ))) f hf
  obtain ⟨hb, hbE⟩ := exists_hasFreqSupport_kmtProj ρ l₁ k f hf
  have hle : -((m₀ : ℤ) + ((m + 1 : ℕ) : ℤ)) ≤ k := by
    rw [hk]
    push_cast
    omega
  have haE' : HS (Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((m + 1 : ℕ) : ℤ))) f) ha
      (Work.KMTAreas.A7HiRep.incArc ρ l₁ k) :=
    hasFreqSupport_mono (incArc_mono ρ l₁ hle) haE
  have hsub : HS (Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((m + 1 : ℕ) : ℤ))) f
      - Work.KMTContract.kmtProj ρ l₁ k f) (ha.sub hb) (Work.KMTAreas.A7HiRep.incArc ρ l₁ k) :=
    hasFreqSupport_sub ha hb haE' hbE
  have hfun : Work.KMTContract.kmtProj ρ l₁ (-((m₀ : ℤ) + ((m + 1 : ℕ) : ℤ))) f
      - Work.KMTContract.kmtProj ρ l₁ k f = Work.KMTAreas.A7HiRep.incFam ρ l₁ m₀ m f := by
    funext x
    simp only [Work.KMTAreas.A7HiRep.incFam, Work.KMTAreas.A7Hi.lpf, hk, Pi.sub_apply]
  exact exists_hasFreqSupport_congr hfun ⟨ha.sub hb, hsub⟩

end Work.A7HiRep
