import Mathlib
import Submission.Work.KMTContract.Areas
import Submission.Work.KMTAreas.A4.multiplierConv
import Submission.Work.KMTAreas.A4.symbolRatio
import Submission.Port.Aesm

/-!
# Monotonicity of the Ionescu–Wainger projections in `(l,k)`

`Work.KMTContract.kmtProj ρ l k` is the paper's projection `Π_{≤l,≤k} = T^{≤l}_{η_{≤k}}`,
realised as convolution with the Fourier coefficients of the Ionescu–Wainger symbol
`σ_{l,k} = ∑_{α ∈ (ℚ/ℤ)_{≤l}} η_{≤k}(· - α)`.  The point of the present lemma is that the
physical-space minor-arc hypothesis `kmtProj ρ l k f = 0` of `ImprovKMT` (area A4) is
**monotone** in `(l,k)`: it survives shrinking both indices.  This is what lets §5 replace the
alternative "`(l, -Log N + l)` is not good" by the *largest* good `l' ≤ l`.

The argument is a factorisation of the symbols: for `l' ≤ l` and `k' ≤ k` one has
`(ℚ/ℤ)_{≤l'} ⊆ (ℚ/ℤ)_{≤l}` and `η_{≤k'} ≤ η_{≤k}` pointwise, so `0 ≤ σ_{l',k'} ≤ σ_{l,k}`, and
`σ_{l',k'} = m · σ_{l,k}` for the bounded measurable ratio `m = σ_{l',k'}/σ_{l,k}`
(`Work.KMTAreas.A4.symbolRatio`).  Hence the corresponding multipliers satisfy
`Π_{≤l',≤k'} = T_m ∘ Π_{≤l,≤k}`, and `Π_{≤l,≤k} f = 0` forces `Π_{≤l',≤k'} f = 0`.
Passing from the operators to the pointwise convolutions uses
`Work.KMTAreas.A4.multiplierConv` (a Fourier multiplier with `L^∞` symbol acts on `ℓ²(ℤ)` by
convolution with the Fourier coefficients of its symbol).

## Main result

* `Work.KMTAreas.A4.kmtProjMono`
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open MeasureTheory Filter Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier
open Work.KMTContract

namespace Work.KMTAreas.A4

noncomputable section

/-- `MemLp` for the counting measure on `ℤ` implies the little-`ℓ²` membership `Memℓp`. -/
private theorem memℓp_of_memLp_count {f : ℤ → ℂ} (hf : MemLp f 2 Measure.count) : Memℓp f 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat]
  have key : (∑' i : ℤ, ‖f i‖ₑ ^ (2 : ℝ)) ≠ ⊤ := by
    rw [← lintegral_count]
    have hlt := hf.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (p := 2) (by norm_num) (by norm_num),
      show (2 : ℝ≥0∞).toReal = 2 from by norm_num] at hlt
    by_contra htop
    rw [htop, ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 1/2)] at hlt
    exact absurd hlt (lt_irrefl _)
  have hs := ENNReal.summable_toReal key
  have h2 : (fun i : ℤ => (‖f i‖ₑ ^ (2 : ℝ)).toReal) = fun i => ‖f i‖ ^ (2 : ℝ) := by
    funext i
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      ENNReal.toReal_ofReal (by positivity)]
  rwa [h2] at hs

/-- The rescaled cutoff `η_{≤k} = θ ↦ η(θ/2^k)` is periodisable: it is compactly supported and
bounded by `1`. -/
private theorem memLp_periodize_etaCut (k : ℤ) :
    MemLp (periodize (etaCut kmtEta k)) ⊤ circleMeasure := by
  refine memLp_periodize (R := (2:ℝ)^k) (C := 1) ?_ (by positivity) ?_ (fun x => norm_kmtEta_le _)
  · have h : Measurable kmtEta :=
      Complex.continuous_ofReal.measurable.comp ((kmtBump.contDiff (n := 1)).continuous.measurable)
    exact h.comp (measurable_id.div_const _)
  · intro x hx
    rw [etaCut]
    refine kmtEta_zero ?_
    rw [abs_div, abs_of_pos (zpow_pos (by norm_num : (0:ℝ) < 2) k)]
    rw [one_le_div (zpow_pos (by norm_num : (0:ℝ) < 2) k)]
    exact le_of_lt hx

/-- **Monotonicity of the Ionescu–Wainger projections.**  If `Π_{≤l,≤k} f` vanishes in physical
space for an `ℓ²` function `f`, then so does `Π_{≤l',≤k'} f` for every `l' ≤ l`, `k' ≤ k`. -/
theorem kmtProjMono (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {l l' : ℕ} (hl : l' ≤ l) {k k' : ℤ} (hk : k' ≤ k) {f : ℤ → ℂ}
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (h : Work.KMTContract.kmtProj ρ l k f = 0) :
    Work.KMTContract.kmtProj ρ l' k' f = 0 := by
  obtain ⟨m, hmmem, _hmbd, hmfac⟩ := symbolRatio ρ hρ hρ1 hl hk
  have hΦ : MemLp (periodize (etaCut kmtEta k)) ⊤ circleMeasure := memLp_periodize_etaCut k
  have hΦ' : MemLp (periodize (etaCut kmtEta k')) ⊤ circleMeasure := memLp_periodize_etaCut k'
  have hσ : MemLp (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))) ⊤ circleMeasure :=
    memLp_iwSymbolSet _ hΦ
  have hσ' : MemLp (iwSymbolSet (iwArithFreqs ρ l') (periodize (etaCut kmtEta k'))) ⊤ circleMeasure :=
    memLp_iwSymbolSet _ hΦ'
  have hfle : Memℓp f 2 := memℓp_of_memLp_count hf
  set F : L2Z := ⟨f, hfle⟩ with hFdef
  have hFcoe : (F : ℤ → ℂ) = f := rfl
  -- the multiplier identity `σ_{l',k'} = m · σ_{l,k}` at the level of `L^∞` elements
  have hmul : hmmem.toLp m • hσ.toLp (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)))
      = hσ'.toLp (iwSymbolSet (iwArithFreqs ρ l') (periodize (etaCut kmtEta k'))) := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := ⊤) (r := ⊤) (hmmem.toLp m)
        (hσ.toLp (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)))),
      MemLp.coeFn_toLp hmmem, MemLp.coeFn_toLp hσ, MemLp.coeFn_toLp hσ'] with ξ h1 h2 h3 h4
    simp only [h1, h2, h3, h4, Pi.smul_apply', smul_eq_mul]
    exact (hmfac ξ).symm
  -- step 1: the projection of `f` at `(l,k)` vanishes
  have hPF : multiplierOf (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))) hσ F = 0 := by
    refine lp.ext (funext fun n => ?_)
    rw [multiplierConv hσ F n, hFcoe, lp.coeFn_zero, ← kmtProj_apply]
    exact congrFun h n
  -- step 2: so does the projection at `(l',k')`, by the multiplier factorisation
  have hPF' : multiplierOf (iwSymbolSet (iwArithFreqs ρ l') (periodize (etaCut kmtEta k'))) hσ' F
      = 0 := by
    have e1 : multiplierOf (iwSymbolSet (iwArithFreqs ρ l') (periodize (etaCut kmtEta k'))) hσ' F
        = multiplier (hσ'.toLp (iwSymbolSet (iwArithFreqs ρ l')
            (periodize (etaCut kmtEta k')))) F := rfl
    rw [e1, ← hmul, ← multiplier_comp (hmmem.toLp m)
      (hσ.toLp (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)))) F]
    rw [show multiplier (hσ.toLp (iwSymbolSet (iwArithFreqs ρ l)
          (periodize (etaCut kmtEta k)))) F
        = multiplierOf (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))) hσ F
        from rfl, hPF, map_zero]
  -- step 3: read off the values of the projection at `(l',k')`
  funext n
  have hval := multiplierConv hσ' F n
  rw [hPF', lp.coeFn_zero, hFcoe] at hval
  rw [kmtProj_apply]
  exact hval.symm

end

end Work.KMTAreas.A4
