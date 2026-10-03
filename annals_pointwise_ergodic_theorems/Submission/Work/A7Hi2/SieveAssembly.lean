/-
# The sieve decomposition of the Ionescu--Wainger walk: the assembly

This module assembles the **sieve (Möbius/Ramanujan) decomposition** of the low-pass Ionescu--Wainger
walk into a variational bound whose constant is the explicit arithmetic quantity `sieveMass ρ l₁`
instead of the `1 + #((ℚ/ℤ)_{≤l₁})` of `Work.KMTAreas.A7Hi.eLpNorm_chainPart_le_uniform`.

The two inputs are the *decomposition* (`SieveDecompHyp`, the conclusion of
`Work.A7Hi2.lpfSieveDecomp`: the walk is a finite combination `Σ_d (d·sieveCoeff d) · decimDilFam d`
of decimated pure dilation families) and the *per-`d` bound* (`DecimDilBound`, the conclusion of
`Work.A7Hi2.decimDilVarUnif`: each decimated family is bounded by `(C/d)‖g‖`, uniformly in `d`,
because on each coset it is a real-scale lacunary dilation family and its kernel has mass `≈ 1/d`).

The content of this file is the assembly: the pointwise subadditivity of the variational norm over
the `Finset` of sieve divisors, the `eLpNorm` bookkeeping, and the arithmetic `‖d · sieveCoeff‖/d =
|sieveCoeff|` that turns the per-`d` constant into the sieve mass.
-/
import Mathlib
import Submission.Work.A7Hi2.decimDilVarUnif
import Submission.Work.A7Hi2.lpfSieveDecomp
import Submission.Work.A7Hi2.dilVarRealScale
import Submission.Work.A7Hi2.sieveCoeff_support_bound

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.A7Hi2

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **The sieve decomposition of the low-pass walk** (the conclusion of
`Work.A7Hi2.lpfSieveDecomp`). -/
def SieveDecompHyp : Prop :=
  ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤)
    (l₁ m₀ m : ℕ) (f : ℤ → ℂ) (hf : Summable (fun n : ℤ => ‖f n‖ ^ p.toReal)) (x : ℤ),
    Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x
      = ∑ d ∈ iwDivs ρ l₁,
          (((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))
            * decimDilFam m₀ Work.KMTAreas.A7Hi.kmtPhiSch d f m x

/-- **The decimated dilation bound, uniform in the decimation `d`** (the conclusion of
`Work.A7Hi2.decimDilVarUnif`). -/
def DecimDilBound : Prop :=
  ∀ (K : SchwartzMap ℝ ℂ) (r : NNReal) (hr : 2 < r) (p : ℝ) (hp : 1 < p),
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (hd : 1 ≤ d) (m₀ : ℕ)
      (hm₀ : d ≤ Work.KMTAreas.A7Hi.lpfScale m₀ 0) (g : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => decimDilFam m₀ K d g m x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C / d) * MeasureTheory.eLpNorm g (ENNReal.ofReal p)
            MeasureTheory.Measure.count

/-- **The variational norm of the low-pass Ionescu--Wainger walk is bounded by the sieve mass.**
For `0 < ρ ≤ 1`, `2 < r`, `1 < p` and any `l₁, m₀` such that every sieve divisor with non-zero
coefficient is at most `2^{m₀}`, the `Vʳ`-variational norm of `m ↦ lpf ρ l₁ m₀ m f` is bounded on
`ℓᵖ(ℤ)` by `C · sieveMass ρ l₁ · ‖f‖`, with `C` free of `l₁, m₀`. -/
theorem eLpNorm_variationalNorm_lpf_le_sieveMass
    (hdec : SieveDecompHyp) (hdecim : DecimDilBound)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ), (∀ d ∈ iwDivs ρ l₁, sieveCoeff ρ l₁ d ≠ 0 →
      d ≤ Work.KMTAreas.A7Hi.lpfScale m₀ 0) → ∀ f : ℤ → ℂ, Summable (fun n : ℤ => ‖f n‖ ^ p) →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * sieveMass ρ l₁) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_of_lt hp)
  have hp0 : (ENNReal.ofReal p) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact lt_trans zero_lt_one hp
  have hflt : 1 < ENNReal.ofReal p := by rw [ENNReal.one_lt_ofReal]; exact hp
  obtain ⟨C₀, hC₀pos, hC₀⟩ := hdecim Work.KMTAreas.A7Hi.kmtPhiSch r hr p hp
  refine ⟨C₀ + 1, by positivity, ?_⟩
  intro l₁ m₀ hlarge f hf
  have hfsum : Summable (fun n : ℤ => ‖f n‖ ^ (ENNReal.ofReal p).toReal) := by
    simpa [ENNReal.toReal_ofReal (le_of_lt (lt_trans zero_lt_one hp))] using hf
  -- the pointwise domination by the sum of the decimated families
  have hptw : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)
      ≤ ∑ d ∈ iwDivs ρ l₁,
          ‖(((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))‖ₑ *
          PointwiseErgodicTheorems.variationalNorm r
            (fun m : ℕ => decimDilFam m₀ Work.KMTAreas.A7Hi.kmtPhiSch d f m x) := by
    intro x
    have hfam : (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)
        = fun m : ℕ => ∑ d ∈ iwDivs ρ l₁,
            (((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ)) •
              (fun m' : ℕ => decimDilFam m₀ Work.KMTAreas.A7Hi.kmtPhiSch d f m' x) m := by
      funext m
      exact hdec ρ hρ hρ1 (ENNReal.ofReal p) hflt ENNReal.ofReal_lt_top l₁ m₀ m f hfsum x
    rw [hfam]
    refine (Work.KMTAreas.A7.variationalNorm_finset_sum_le hr1 (iwDivs ρ l₁) _).trans
      (le_of_eq ?_)
    exact Finset.sum_congr rfl fun d _ =>
      Submission.PointwiseErgodicTheorems.variationalNorm_smul hr1 _ _
  -- the `eLpNorm` of the sum of the decimated families
  have hsum : MeasureTheory.eLpNorm (fun x : ℤ => ∑ d ∈ iwDivs ρ l₁,
        ‖(((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))‖ₑ *
          PointwiseErgodicTheorems.variationalNorm r
            (fun m : ℕ => decimDilFam m₀ Work.KMTAreas.A7Hi.kmtPhiSch d f m x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ∑ d ∈ iwDivs ρ l₁, MeasureTheory.eLpNorm (fun x : ℤ =>
          ‖(((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))‖ₑ *
            PointwiseErgodicTheorems.variationalNorm r
              (fun m : ℕ => decimDilFam m₀ Work.KMTAreas.A7Hi.kmtPhiSch d f m x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count :=
    Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal hp1
      (fun d _ => (measurable_of_countable _).aemeasurable)
  -- the per-divisor bound
  have hper : ∀ d ∈ iwDivs ρ l₁, MeasureTheory.eLpNorm (fun x : ℤ =>
          ‖(((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))‖ₑ *
            PointwiseErgodicTheorems.variationalNorm r
              (fun m : ℕ => decimDilFam m₀ Work.KMTAreas.A7Hi.kmtPhiSch d f m x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (|(sieveCoeff ρ l₁ d : ℝ)| * C₀) *
          MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    intro d hd
    by_cases hz : sieveCoeff ρ l₁ d = 0
    · have hcz : (((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ)) = 0 := by simp [hz]
      have hz0 : (fun x : ℤ => ‖(((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))‖ₑ *
            PointwiseErgodicTheorems.variationalNorm r
              (fun m : ℕ => decimDilFam m₀ Work.KMTAreas.A7Hi.kmtPhiSch d f m x)) = 0 := by
        funext x
        rw [hcz]
        simp
      rw [hz0]
      simp [hz]
    · have hd1 : 1 ≤ d := by
        have hmem := Nat.mem_divisors.mp hd
        exact Nat.pos_of_dvd_of_pos hmem.1 (Nat.pos_of_ne_zero hmem.2)
      have hdle : d ≤ Work.KMTAreas.A7Hi.lpfScale m₀ 0 := hlarge d hd hz
      have hC₁ : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun m : ℕ => decimDilFam m₀ Work.KMTAreas.A7Hi.kmtPhiSch d f m x))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C₀ / d) * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
              MeasureTheory.Measure.count :=
        hC₀ d hd1 m₀ hdle f
      have hnorm : ‖(((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))‖
          = (d : ℝ) * |(sieveCoeff ρ l₁ d : ℝ)| := by
        rw [norm_mul, Complex.norm_intCast, Complex.norm_intCast, Int.cast_natCast,
          Nat.abs_cast]
      have hconst : ‖(((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))‖ₑ
          = ENNReal.ofReal ((d : ℝ) * |(sieveCoeff ρ l₁ d : ℝ)|) := by
        rw [← ofReal_norm (((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ)), hnorm]
      have hcast : ‖(((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))‖ₑ ≠ ⊤ := by
        rw [← ofReal_norm (((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))]
        exact ENNReal.ofReal_ne_top
      have hstep := Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
        (μ := MeasureTheory.Measure.count)
        (V := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun m : ℕ => decimDilFam m₀ Work.KMTAreas.A7Hi.kmtPhiSch d f m x))
        (c := ‖(((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))‖ₑ)
        hcast hp0 ENNReal.ofReal_ne_top
      rw [hstep, hconst]
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      have harg : (d : ℝ) * |(sieveCoeff ρ l₁ d : ℝ)| * (C₀ / (d : ℝ))
          = |(sieveCoeff ρ l₁ d : ℝ)| * C₀ := by
        field_simp
      refine (mul_le_mul_of_nonneg_left hC₁ bot_le).trans ?_
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), harg]
  -- combine
  have hfin : MeasureTheory.eLpNorm (fun x : ℤ => ∑ d ∈ iwDivs ρ l₁,
        ‖(((d : ℤ) : ℂ) * ((sieveCoeff ρ l₁ d : ℤ) : ℂ))‖ₑ *
          PointwiseErgodicTheorems.variationalNorm r
            (fun m : ℕ => decimDilFam m₀ Work.KMTAreas.A7Hi.kmtPhiSch d f m x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C₀ * sieveMass ρ l₁) *
          MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    refine (hsum.trans (Finset.sum_le_sum hper)).trans (le_of_eq ?_)
    rw [← Finset.sum_mul]
    congr 1
    rw [← ENNReal.ofReal_sum_of_nonneg (s := iwDivs ρ l₁)
      (f := fun d => |(sieveCoeff ρ l₁ d : ℝ)| * C₀) (fun d _ => by positivity)]
    rw [sieveMass, Finset.mul_sum]
    exact congrArg ENNReal.ofReal (Finset.sum_congr rfl fun d _ => by ring)
  refine (Work.KMTAreas.A7.eLpNorm_mono_ennreal (μ := MeasureTheory.Measure.count)
    (fun x => hptw x) hp0 ENNReal.ofReal_ne_top).trans ?_
  refine hfin.trans ?_
  have hSM : 0 ≤ sieveMass ρ l₁ := by
    rw [sieveMass]
    exact Finset.sum_nonneg fun d _ => abs_nonneg _
  have hconst2 : ENNReal.ofReal (C₀ * sieveMass ρ l₁)
      ≤ ENNReal.ofReal ((C₀ + 1) * sieveMass ρ l₁) :=
    ENNReal.ofReal_le_ofReal (by nlinarith [hC₀pos, hSM])
  calc ENNReal.ofReal (C₀ * sieveMass ρ l₁) *
        MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count *
          ENNReal.ofReal (C₀ * sieveMass ρ l₁) := mul_comm _ _
    _ ≤ MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count *
          ENNReal.ofReal ((C₀ + 1) * sieveMass ρ l₁) :=
        mul_le_mul_of_nonneg_left hconst2 bot_le
    _ = ENNReal.ofReal ((C₀ + 1) * sieveMass ρ l₁) *
          MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := mul_comm _ _

/-- **The decimated dilation bound from the real-scale JSW estimate** (the proved
`Work.A7Hi2.decimDilVarUnif`). -/
theorem decimDilBound_of_dilVarRealScale (h : DilVarRealScale) : DecimDilBound := by
  intro K r hr p hp
  exact Work.A7Hi2.decimDilVarUnif h K r hr p hp

/-- **The sieve bound, with the whole analytic input reduced to the real-scale JSW estimate.** -/
theorem eLpNorm_variationalNorm_lpf_le_sieveMass_of_dilVarRealScale
    (hDil : DilVarRealScale) (hdec : SieveDecompHyp)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ), (∀ d ∈ iwDivs ρ l₁, sieveCoeff ρ l₁ d ≠ 0 →
      d ≤ Work.KMTAreas.A7Hi.lpfScale m₀ 0) → ∀ f : ℤ → ℂ, Summable (fun n : ℤ => ‖f n‖ ^ p) →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * sieveMass ρ l₁) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count :=
  eLpNorm_variationalNorm_lpf_le_sieveMass hdec (decimDilBound_of_dilVarRealScale hDil)
    ρ hρ hρ1 r hr p hp

/-- **The values-maximal (`supPart`) bound with the sieve constant.**  Same content as
`eLpNorm_variationalNorm_lpf_le_sieveMass`, in the shape of the target `Work.KMTAreas.A7Hi2.SupPiece`
(the values supremum `⨆_m ‖lpf ρ l₁ m₀ m f x‖ₑ`, with an arbitrary `r : ℝ≥0`, since `supPart` does
not depend on `r`).  The only difference from the target is the constant: `sieveMass ρ l₁` here,
`(1 + l₁)²` there. -/
theorem eLpNorm_supPart_lpf_le_sieveMass
    (hDil : DilVarRealScale) (hdec : SieveDecompHyp)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ), (∀ d ∈ iwDivs ρ l₁, sieveCoeff ρ l₁ d ≠ 0 →
      d ≤ Work.KMTAreas.A7Hi.lpfScale m₀ 0) → ∀ f : ℤ → ℂ, Summable (fun n : ℤ => ‖f n‖ ^ p) →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * sieveMass ρ l₁) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  obtain ⟨C, hCpos, hC⟩ := eLpNorm_variationalNorm_lpf_le_sieveMass_of_dilVarRealScale
    hDil hdec ρ hρ hρ1 3 (by norm_num) p hp
  have hp0 : (ENNReal.ofReal p) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact lt_trans zero_lt_one hp
  refine ⟨C, hCpos, ?_⟩
  intro l₁ m₀ hlarge f hf
  refine (Work.KMTAreas.A7.eLpNorm_mono_ennreal (μ := MeasureTheory.Measure.count)
    (fun x => ?_) hp0 ENNReal.ofReal_ne_top).trans (hC l₁ m₀ hlarge f hf)
  rw [Work.KMTAreas.A7Hi.variationalNorm_eq_parts]
  exact le_self_add

end

/-- **The sieve decomposition holds** (it *is* the proved `Work.A7Hi2.lpfSieveDecomp`). -/
theorem sieveDecompHyp_holds : SieveDecompHyp :=
  fun ρ hρ hρ1 p hp hptop l₁ m₀ m f hf x =>
    Work.A7Hi2.lpfSieveDecomp ρ hρ hρ1 p hp hptop l₁ m₀ m f hf x

/-- **The sieve bound with the decomposition discharged**: the only remaining input is the
arithmetic-free real-scale lacunary dilation estimate `DilVarRealScale`. -/
theorem eLpNorm_variationalNorm_lpf_le_sieveMass'
    (hDil : DilVarRealScale)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ), (∀ d ∈ iwDivs ρ l₁, sieveCoeff ρ l₁ d ≠ 0 →
      d ≤ Work.KMTAreas.A7Hi.lpfScale m₀ 0) → ∀ f : ℤ → ℂ, Summable (fun n : ℤ => ‖f n‖ ^ p) →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * sieveMass ρ l₁) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count :=
  eLpNorm_variationalNorm_lpf_le_sieveMass_of_dilVarRealScale hDil sieveDecompHyp_holds
    ρ hρ hρ1 r hr p hp

/-- **The target-shaped (`supPart`) sieve bound with the decomposition discharged.** -/
theorem eLpNorm_supPart_lpf_le_sieveMass'
    (hDil : DilVarRealScale)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ), (∀ d ∈ iwDivs ρ l₁, sieveCoeff ρ l₁ d ≠ 0 →
      d ≤ Work.KMTAreas.A7Hi.lpfScale m₀ 0) → ∀ f : ℤ → ℂ, Summable (fun n : ℤ => ‖f n‖ ^ p) →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * sieveMass ρ l₁) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  obtain ⟨C, hCpos, hC⟩ := eLpNorm_supPart_lpf_le_sieveMass hDil sieveDecompHyp_holds
    ρ hρ hρ1 r p hp
  exact ⟨C, hCpos, hC⟩


/-- **The real-scale lacunary dilation estimate holds** (it *is* the proved
`Work.A7Hi2.dilVarRealScale`, the real-scale form of JSW Theorem 1.1 / `A7Hi.DilVarClean`). -/
theorem dilVarRealScale_holds : DilVarRealScale := Work.A7Hi2.dilVarRealScale

/-- **The sieve bound for the variational norm of the low-pass Ionescu--Wainger walk**
(unconditional: both the sieve decomposition and the real-scale JSW estimate are proved). -/
theorem eLpNorm_variationalNorm_lpf_le_sieveMass''
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ), (∀ d ∈ iwDivs ρ l₁, sieveCoeff ρ l₁ d ≠ 0 →
      d ≤ Work.KMTAreas.A7Hi.lpfScale m₀ 0) → ∀ f : ℤ → ℂ, Summable (fun n : ℤ => ‖f n‖ ^ p) →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * sieveMass ρ l₁) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count :=
  eLpNorm_variationalNorm_lpf_le_sieveMass' dilVarRealScale_holds
    ρ hρ hρ1 r hr p hp

/-- **The values-maximal (`supPart`) sieve bound** (unconditional; the target-shaped statement, with
the constant `C · sieveMass ρ l₁` in place of the target's `C (1+l₁)²`). -/
theorem eLpNorm_supPart_lpf_le_sieveMass''
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ), (∀ d ∈ iwDivs ρ l₁, sieveCoeff ρ l₁ d ≠ 0 →
      d ≤ Work.KMTAreas.A7Hi.lpfScale m₀ 0) → ∀ f : ℤ → ℂ, Summable (fun n : ℤ => ‖f n‖ ^ p) →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * sieveMass ρ l₁) *
            MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count :=
  eLpNorm_supPart_lpf_le_sieveMass' dilVarRealScale_holds
    ρ hρ hρ1 r p hp


/-- **The values-maximal sieve bound on the good major arcs** — the statement of `SupPiece` with the
constant `C · sieveMass ρ l₁` in place of `C (1+l₁)²` (and the harmless extra hypothesis
`Summable (‖f‖ᵖ)`), with the auxiliary hypothesis discharged from `GoodMajorArcs` (with `Cρ` large
enough) and the proved support bound `Work.A7Hi2.sieveCoeff_support_bound` (which rests on
`Work.Analysis.IonescuWainger.iwP_element_le`).  The constant `C` is **uniform in `l₁` and `m₀`**. -/
theorem eLpNorm_supPart_lpf_le_sieveMass_goodMajorArcs
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (p : ℝ) (hp : 1 < p) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) →
      ∀ f : ℤ → ℂ, Summable (fun n : ℤ => ‖f n‖ ^ p) →
        MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * sieveMass ρ l₁) *
              MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  obtain ⟨Cρ₀, hCρ₀pos, hCρ₀⟩ := Work.A7Hi2.sieveCoeff_support_bound ρ hρ hρ1
  obtain ⟨C, hCpos, hC⟩ := eLpNorm_supPart_lpf_le_sieveMass'' ρ hρ hρ1 r p hp
  refine ⟨max Cρ₀ 1, lt_max_of_lt_left hCρ₀pos, C, hCpos, ?_⟩
  intro l₁ m₀ hgood f hf
  have hbound : ∀ d ∈ iwDivs ρ l₁, sieveCoeff ρ l₁ d ≠ 0 →
      d ≤ Work.KMTAreas.A7Hi.lpfScale m₀ 0 := by
    intro d _ hz
    have h1 : (d : ℝ) ≤ (2 : ℝ) ^ (Cρ₀ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) := hCρ₀ l₁ d hz
    have h2 : Cρ₀ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (m₀ : ℝ) := by
      have hg := hgood
      simp only [Work.Analysis.IonescuWainger.GoodMajorArcs] at hg
      push_cast at hg
      have hmono : Cρ₀ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))
          ≤ max Cρ₀ 1 * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      linarith
    have h3 : (2 : ℝ) ^ (Cρ₀ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) ≤ (2 : ℝ) ^ (m₀ : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
    have h4 : ((Work.KMTAreas.A7Hi.lpfScale m₀ 0 : ℕ) : ℝ) = (2 : ℝ) ^ (m₀ : ℝ) := by
      rw [Work.KMTAreas.A7Hi.lpfScale_cast, show m₀ + 0 = m₀ from rfl, ← Real.rpow_natCast]
    have h5 : (d : ℝ) ≤ ((Work.KMTAreas.A7Hi.lpfScale m₀ 0 : ℕ) : ℝ) := by
      rw [h4]
      exact h1.trans h3
    exact_mod_cast h5
  exact hC l₁ m₀ hbound f hf

end Work.A7Hi2
