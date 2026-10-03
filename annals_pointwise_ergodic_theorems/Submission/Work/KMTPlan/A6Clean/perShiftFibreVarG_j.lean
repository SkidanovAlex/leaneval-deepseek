/-
# The per-shift fibre estimate for the `g`-side modified bump

`Work.KMTPlan.A6Clean.perShiftFibreVarG_j` is the per-shift (single shift `M`) strengthening of
`Work.KMTAreas.A7Hi.fiberVarSamplingG_large_bdd` for the *modified* `g`-side bump
`Work.KMTPlan.A6.varphitildeNtj P (N n) k₂ j₂ t` (the bump of the paper's integration-by-parts
identity, `j₂ ∈ {-1,0,1}`).

The route is the route of the proved `Work.A7MixedG.fiberOp_var_shift_largeScales` (which is the
same statement for the *unmodified* bump `varphitildeNt`); only the bump changes:

* `perShiftFibreVarG_of_bump` — the estimate for an *arbitrary* family of narrow bumps `φ`
  satisfying the data hypotheses actually consumed by the argument: integrability, `ℓ¹`-summability
  of the Fourier coefficients `cw (φ n)`, support inside the plateau half-ball `2^{-2dU-1}` of the
  gate `mStargF d U`, and the band-`1/(4q)` continuous extension `kext` of the coefficient kernel.
  Its proof is the proof of `fiberOp_var_shift_largeScales` with the concrete bump abstracted away.
* `jBump_kextFam` — the band-`1/(4q)` integrable continuous extension of the coefficient kernel of
  `varphitildeNtj`, built from the Schwartz packaging `varphitildeNtjSch` (the `g`-side analogue of
  `Work.KMTAreas.A7Hi.exists_kext_cw_mStargF`).
* `perShiftFibreVarG_j` — the instantiation.
-/
import Mathlib
import Submission.Work.A7MixedG.FiberLargeResidueHolds
import Submission.Work.KMTPlan.A6.MdlSliceGband

namespace Work.KMTPlan.A6Clean

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators FourierTransform

noncomputable section

/-! ## §1.  The per-shift fibre sampling estimate for an abstract narrow bump family -/

/-- **The per-shift (per-residue) fibre sampling estimate for an abstract bump family.**

For `ρ ∈ (0,1]`, `p ∈ (1,∞)`, `r > 2` there is a constant `C` such that for every exact height
`l₂`, every cut scale `U ≥ 1`, every family of bumps `φ : ℕ → ℝ → ℂ` and every family of band
extensions `kext` satisfying

* `Integrable (φ n)` and `Summable (fun j => ‖cw (φ n) j‖)`,
* `φ n` is supported in the plateau half-ball `|ξ| ≤ 2^{-2dU-1}` of the gate
  `mStargF P.natDegree U = η_{≤-2dU}` (`d = P.natDegree`),
* `kext n` is integrable, continuous, agrees with `cw (φ n)` at the integers and is band-limited to
  the arc `|ξ| ≤ 1/(4·arithQ ρ l₂)` (the quantitative Shannon hypothesis),

and every shift `M : ℤ`, the twisted fibre of the family
`(if S n then Tex ρ l₂ (φ n) g else 0)` is controlled by the family itself. -/
theorem perShiftFibreVarG_of_bump
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree)
    (p : ENNReal) (hp : 1 < p) (hpt : p < ⊤) (r : NNReal) (hr : 2 < r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (l₂ U : ℕ) (φ : ℕ → ℝ → ℂ) (kext : ℕ → ℝ → ℂ), 1 ≤ U →
        (∀ n : ℕ, MeasureTheory.Integrable (φ n)) →
        (∀ n : ℕ, Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw (φ n) j‖)) →
        (∀ n : ℕ, ∀ ξ : ℝ, φ n ξ ≠ 0 →
          |ξ| ≤ (2 : ℝ) ^ (-(2 * (((P.natDegree * U : ℕ) : ℤ))) - 1)) →
        (∀ n : ℕ, MeasureTheory.Integrable (kext n) ∧ Continuous (kext n) ∧
          (∀ m : ℤ, kext n (m : ℝ) = Work.KMTAreas.A7.cw (φ n) m) ∧
          (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / (4 * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ))))
            (1 / (4 * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ))) →
            FourierTransform.fourier (kext n) ξ = 0)) →
        Work.Analysis.IonescuWainger.NonAliasing (-(2 * (U : ℤ)))
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) →
        ∀ (g : ℤ → ℂ) (Bg : ℝ), (∀ x : ℤ, ‖g x‖ ≤ Bg) →
        ∀ (S : ℕ → Prop) [DecidablePred S] (M : ℤ),
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₂
                (Work.KMTAreas.A7.mStargF P.natDegree U) M
                (if S n then Work.KMTAreas.A7.Tex ρ l₂ (φ n) g else 0) x))
              p MeasureTheory.Measure.count
            ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  (if S n then Work.KMTAreas.A7.Tex ρ l₂ (φ n) g else 0) x))
              p MeasureTheory.Measure.count := by
  classical
  set pR : ℝ := p.toReal with hpR
  have hpR1 : 1 < pR := by
    rw [hpR, ← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hpt)).mpr hp
  have hpR0 : 0 < pR := lt_trans zero_lt_one hpR1
  have hpof : ENNReal.ofReal pR = p := by
    rw [hpR]
    exact ENNReal.ofReal_toReal (ne_of_lt hpt)
  obtain ⟨Ceng, hCengpos, heng⟩ :=
    Work.KMTAreas.A7.convSublatticeCosetCompareBdd pR hpR1 r (le_of_lt (lt_trans (by norm_num) hr))
  refine ⟨Ceng ^ (1 / pR), Real.rpow_pos_of_pos hCengpos _, ?_⟩
  intro l₂ U φ kext hU hφint hφsum hφsupp hkextdata hna g Bg hBg S _ M
  set q : ℕ := Work.KMTAreas.A7.arithQ ρ l₂ with hq
  set A : Finset Work.Analysis.IonescuWainger.Circle :=
    Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂ with hA
  set κ : ℕ → ℤ → ℂ := fun n j => Work.KMTAreas.A7.cw (φ n) j with hκ
  set Hf : ℕ → ℤ → ℤ → ℂ :=
    fun n y z => if S n then Work.KMTAreas.A7.sliceInput A g y z else 0 with hHf
  set F : ℤ → ENNReal := fun y => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
    Work.KMTAreas.A7.fiberOp ρ l₂ (Work.KMTAreas.A7.mStargF P.natDegree U) M
      (if S n then Work.KMTAreas.A7.Tex ρ l₂ (φ n) g else 0) y) with hF
  set W : ℤ → ENNReal := fun x => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
    (if S n then Work.KMTAreas.A7.Tex ρ l₂ (φ n) g else 0) x) with hW
  have hqpos : 0 < q := by
    rw [hq]
    exact Work.KMTAreas.A7.arithQ_pos ρ l₂
  have hnaNew : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (U : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂) :=
    Work.KMTAreas.A7MixedG.NonAliasing_subset hna
      (fun α hα => Work.KMTAreas.A7.mem_iwArithFreqsNew_le hα)
  have hqnsmul : ∀ α ∈ A, q • α = 0 := by
    intro α hα
    have hα' : α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂ := hA ▸ hα
    have h1 : Work.KMTAreas.A7.arithQ ρ l₂ • α = 0 :=
      Work.KMTAreas.A7.arithQ_nsmul_eq_zero (Work.KMTAreas.A7.mem_iwArithFreqsNew_le hα')
    rw [hq]
    exact h1
  have hβ : 0 < 1 / (4 * (q : ℝ)) := by positivity
  have hβq : (1 / (4 * (q : ℝ))) * (q : ℝ) ≤ 1 / 4 := by
    have h : (1 / (4 * (q : ℝ))) * (q : ℝ) = 1 / 4 := by
      have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
      field_simp
    rw [h]
  have hκsum : ∀ n : ℕ, Summable (fun j : ℤ => ‖κ n j‖) := by
    intro n
    rw [hκ]
    exact hφsum n
  have hkextdata' : ∀ n : ℕ, MeasureTheory.Integrable (kext n) ∧ Continuous (kext n) ∧
      (∀ m : ℤ, kext n (m : ℝ) = κ n m) ∧
      (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / (4 * (q : ℝ)))) (1 / (4 * (q : ℝ))) →
        FourierTransform.fourier (kext n) ξ = 0) := by
    intro n
    obtain ⟨h1, h2, h3, h4⟩ := hkextdata n
    refine ⟨h1, h2, ?_, ?_⟩
    · intro m
      rw [hκ]
      exact h3 m
    · intro ξ hξ
      rw [hq] at hξ
      exact h4 ξ hξ
  have hB0 : 0 ≤ Bg := le_trans (norm_nonneg (g 0)) (hBg 0)
  have hHfb : ∀ n : ℕ, ∀ y z : ℤ, ‖Hf n y z‖ ≤ Bg * (A.card : ℝ) := by
    intro n y z
    rw [hHf]
    by_cases hSn : S n
    · simp only [hSn, if_true]
      exact Work.KMTAreas.A7Hi.norm_sliceInput_le A g Bg hBg y z
    · simp only [hSn, if_false, norm_zero]
      exact mul_nonneg hB0 (Nat.cast_nonneg _)
  -- ### the per-coset comparison
  have hpair : ∀ r₀ : ℤ,
      (∑' z : ℤ, (F ((q : ℤ) * z + r₀)) ^ pR)
        ≤ ENNReal.ofReal Ceng *
          (∑' z : ℤ, (W ((q : ℤ) * z + (r₀ - M))) ^ pR) := by
    intro r₀
    have hL : ∀ z : ℤ, F ((q : ℤ) * z + r₀)
        = PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ,
            κ n j * Hf n (M - r₀) ((q : ℤ) * z + r₀ - j)) := by
      intro z
      have hfun : (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₂
            (Work.KMTAreas.A7.mStargF P.natDegree U) M
            (if S n then Work.KMTAreas.A7.Tex ρ l₂ (φ n) g else 0)
            ((q : ℤ) * z + r₀))
          = fun n : ℕ => ∑' j : ℤ, κ n j * Hf n (M - r₀) ((q : ℤ) * z + r₀ - j) := by
        funext n
        rw [hκ, hHf]
        rw [Work.KMTAreas.A7Hi.fiberOp_mStargF_Sclip ρ hρ hρ1 P l₂ U hU hd hnaNew (φ n)
          (hφint n) (hφsum n) (hφsupp n) g Bg hBg (S n) M]
        simp only [ite_apply, Pi.zero_apply]
        rw [Work.KMTAreas.A7.fiberOp_residue_eq_slice ρ l₂ (φ n) q (hφsum n) g Bg hBg hqnsmul
          M r₀ z]
        exact (Work.KMTAreas.A7.sliceSumm_eq_tsum_cw_sliceInput A (φ n) (hφsum n) g Bg hBg
          (M - r₀) ((q : ℤ) * z + r₀) (S n)).symm
      simp only [hF]
      rw [hfun]
    have hR : ∀ z : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ,
          κ n j * Hf n (M - r₀) ((q : ℤ) * z + (r₀ - M) - j))
        = W ((q : ℤ) * z + (r₀ - M)) := by
      intro z
      have hfun : (fun n : ℕ => ∑' j : ℤ, κ n j * Hf n (M - r₀)
              ((q : ℤ) * z + (r₀ - M) - j))
          = fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₂ (φ n) g else 0)
              ((q : ℤ) * z + (r₀ - M)) := by
        funext n
        rw [hκ, hHf]
        rw [Work.KMTAreas.A7.sliceSumm_eq_tsum_cw_sliceInput A (φ n) (hφsum n) g Bg hBg
          (M - r₀) ((q : ℤ) * z + (r₀ - M)) (S n)]
        simp only [ite_apply, Pi.zero_apply]
        by_cases hSn : S n
        · simp only [hSn, if_true]
          rw [← Work.KMTAreas.A7Hi.fiberOp_zero_eq_Tex ρ l₂ (φ n) (hφint n) g]
          have hy : (M - r₀) = 0 - ((r₀ - M)) := by ring
          rw [hy]
          rw [← Work.KMTAreas.A7.fiberOp_residue_eq_slice ρ l₂ (φ n) q (hφsum n) g Bg hBg
            hqnsmul 0 (r₀ - M) z]
        · simp only [hSn, if_false]
      simp only [hW]
      rw [hfun]
    calc (∑' z : ℤ, (F ((q : ℤ) * z + r₀)) ^ pR)
        = ∑' z : ℤ, (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ,
            κ n j * Hf n (M - r₀) ((q : ℤ) * z + r₀ - j))) ^ pR :=
          tsum_congr (fun z => by rw [hL z])
      _ ≤ ENNReal.ofReal Ceng * ∑' z : ℤ, (PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => ∑' j : ℤ, κ n j * Hf n (M - r₀)
              ((q : ℤ) * z + (r₀ - M) - j))) ^ pR :=
          heng (1 / (4 * (q : ℝ))) hβ q hqpos hβq κ kext hkextdata' hκsum Hf
            (Bg * (A.card : ℝ)) hHfb (M - r₀) r₀ (r₀ - M)
      _ = ENNReal.ofReal Ceng *
            (∑' z : ℤ, (W ((q : ℤ) * z + (r₀ - M))) ^ pR) := by
          rw [tsum_congr (fun z => by rw [hR z])]
  -- ### the total-sum bound
  have hkey : (∑' x : ℤ, (F x) ^ pR) ≤ ENNReal.ofReal Ceng * (∑' x : ℤ, (W x) ^ pR) := by
    rw [Work.KMTAreas.A7Hi.periodDecompLocal q hqpos (fun x : ℤ => (F x) ^ pR)]
    calc ∑ r ∈ Finset.range q, ∑' z : ℤ, (F ((q : ℤ) * z + (r : ℤ))) ^ pR
        ≤ ∑ r ∈ Finset.range q, ENNReal.ofReal Ceng *
            (∑' z : ℤ, (W ((q : ℤ) * z + ((r : ℤ) - M))) ^ pR) :=
          Finset.sum_le_sum (fun r _ => hpair (r : ℤ))
      _ = ENNReal.ofReal Ceng * (∑ r ∈ Finset.range q,
            ∑' z : ℤ, (W ((q : ℤ) * z + ((r : ℤ) - M))) ^ pR) := by
          rw [Finset.mul_sum]
      _ = ENNReal.ofReal Ceng * (∑' x : ℤ, (W x) ^ pR) := by
          rw [Work.KMTAreas.A7Hi.cosetShift_decomp q hqpos (fun x : ℤ => (W x) ^ pR) M]
  -- ### the norm comparison
  have hgoal : MeasureTheory.eLpNorm F (ENNReal.ofReal pR) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Ceng ^ (1 / pR)) *
        MeasureTheory.eLpNorm W (ENNReal.ofReal pR) MeasureTheory.Measure.count :=
    Work.A7MixedG.eLpNorm_le_of_tsum_rpow_le hpR0 hCengpos hkey
  rwa [← hpof]

/-! ## §2.  The band-`1/(4q)` extension of the modified bump's coefficient kernel -/

/-- **The band-`1/(4q)` integrable continuous extension of the coefficient kernel of the modified
`g`-side bump** `varphitildeNtj P N k j t`.

Under the Farey hypothesis `8·2^k·q ≤ N` the modified bump is supported in the arc of radius
`1/(4q)` (because its support is that of the unmodified bump, `varphitildeNt_support_le_quarter_g`),
so the Fourier transform of its Schwartz packaging `varphitildeNtjSch` is an integrable continuous
function with the right samples and the right band.  This is the `g`-side analogue of
`Work.KMTAreas.A7Hi.exists_kext_cw_mStargF`. -/
theorem jBump_kextFam (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (ρ : ℝ) (l₂ : ℕ)
    (k₂ : ℕ) (j₂ : ℤ) (t : ℝ) (hk : k₂ ≠ 0 ∨ 0 ≤ j₂) (N : ℕ → ℕ)
    (hfarey : ∀ n : ℕ, 8 * (2 : ℝ) ^ k₂ * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ) ≤ (N n : ℝ)) :
    ∃ kext : ℕ → ℝ → ℂ,
      ∀ n : ℕ, MeasureTheory.Integrable (kext n) ∧ Continuous (kext n) ∧
        (∀ m : ℤ, kext n (m : ℝ) = Work.KMTAreas.A7.cw
          (Work.KMTPlan.A6.varphitildeNtj P (N n) k₂ j₂ t) m) ∧
        (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / (4 * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ))))
          (1 / (4 * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ))) →
          FourierTransform.fourier (kext n) ξ = 0) := by
  have hq1 : 1 ≤ Work.KMTAreas.A7.arithQ ρ l₂ := Work.KMTAreas.A7.arithQ_pos ρ l₂
  have hβ : 0 < 1 / (4 * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ)) := by positivity
  set kextF : ℕ → ℝ → ℂ := fun n s => ∫ θ,
      Work.KMTPlan.A6.varphitildeNtj P (N n) k₂ j₂ t θ
        * Work.KMTAreas.A7.ee (-(s * θ)) with hkextF
  refine ⟨kextF, ?_⟩
  intro n
  have hsuppψ : ∀ ξ : ℝ, Work.KMTAreas.A7.varphitildeNt P P.natDegree (N n) k₂ t ξ ≠ 0 →
      |ξ| ≤ 1 / (4 * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ)) :=
    Work.KMTAreas.A7Hi.varphitildeNt_support_le_quarter_g P hd (Work.KMTAreas.A7.arithQ ρ l₂) hq1
      (N n) k₂ t (hfarey n)
  have hsupp : ∀ ξ : ℝ,
      (Work.KMTPlan.A6.varphitildeNtjSch P (N n) k₂ j₂ t : ℝ → ℂ) ξ ≠ 0 →
      |ξ| ≤ 1 / (4 * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ)) := by
    intro ξ hξ
    rw [Work.KMTPlan.A6.varphitildeNtjSch_apply P (N n) k₂ j₂ t hk] at hξ
    exact hsuppψ ξ
      (Work.KMTPlan.A6.varphitildeNt_ne_zero_of_varphitildeNtj_ne_zero P (N n) k₂ j₂ t hξ)
  have hfun : kextF n = fun s : ℝ => ∫ θ,
      (Work.KMTPlan.A6.varphitildeNtjSch P (N n) k₂ j₂ t : ℝ → ℂ) θ
        * Work.KMTAreas.A7.ee (-(s * θ)) := by
    funext s
    rw [hkextF]
    simp only [Work.KMTPlan.A6.varphitildeNtjSch_coe P (N n) k₂ j₂ t hk]
  have hfun2 : kextF n
      = ⇑(𝓕 (Work.KMTPlan.A6.varphitildeNtjSch P (N n) k₂ j₂ t) : SchwartzMap ℝ ℂ) := by
    rw [hfun]
    funext s
    exact Work.KMTAreas.A7.cwR_eq_fourier _ s
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hfun2]
    exact (𝓕 (Work.KMTPlan.A6.varphitildeNtjSch P (N n) k₂ j₂ t)).integrable
  · rw [hfun2]
    exact (𝓕 (Work.KMTPlan.A6.varphitildeNtjSch P (N n) k₂ j₂ t)).continuous
  · intro m
    rw [hfun]
    have h1 : (∫ θ, (Work.KMTPlan.A6.varphitildeNtjSch P (N n) k₂ j₂ t : ℝ → ℂ) θ
          * Work.KMTAreas.A7.ee (-(((m : ℤ) : ℝ) * θ)))
        = Work.KMTAreas.A7.cw (Work.KMTPlan.A6.varphitildeNtj P (N n) k₂ j₂ t) m := by
      simp only [Work.KMTAreas.A7.cw,
        Work.KMTPlan.A6.varphitildeNtjSch_apply P (N n) k₂ j₂ t hk, neg_mul]
    simpa only [] using h1
  · intro ξ hξ
    rw [hfun]
    exact Work.KMTAreas.A7.fourier_cwR_band (1 / (4 * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ))) hβ
      (Work.KMTPlan.A6.varphitildeNtjSch P (N n) k₂ j₂ t) hsupp ξ hξ

/-! ## §3.  The target -/

theorem perShiftFibreVarG_j (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ)
    (hd : 2 ≤ P.natDegree) (p : ENNReal) (hp : 1 < p) (hpt : p < ⊤) (r : NNReal) (hr : 2 < r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (l₂ k₂ U : ℕ) (j₂ : ℤ) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₂ : k₂ = 0 → j₂ ≠ -1),
      1 ≤ U → ∀ (t : ℝ) (g : ℤ → ℂ) (Bg : ℝ), (∀ x : ℤ, ‖g x‖ ≤ Bg) →
        ∀ (N : ℕ → ℕ) (S : ℕ → Prop) [DecidablePred S],
          (∀ n : ℕ, 8 * (2 : ℝ) ^ k₂ * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ) ≤ (N n : ℝ)) →
          (∀ n : ℕ, (k₂ : ℤ) + 2 * (U : ℤ) + 1 ≤ (Work.Analysis.EndVar.logN (N n)).toNat) →
          Work.Analysis.IonescuWainger.NonAliasing (-(2 * (U : ℤ)))
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) →
          ∀ M : ℤ,
            MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₂
                  (Work.KMTAreas.A7.mStargF P.natDegree U) M
                  (if S n then Work.KMTAreas.A7.Tex ρ l₂
                    (Work.KMTPlan.A6.varphitildeNtj P (N n) k₂ j₂ t) g else 0) x))
              p MeasureTheory.Measure.count
            ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₂
                    (Work.KMTPlan.A6.varphitildeNtj P (N n) k₂ j₂ t) g else 0) x))
              p MeasureTheory.Measure.count := by
  have hd1 : 1 ≤ P.natDegree := le_trans (by norm_num : 1 ≤ 2) hd
  obtain ⟨C, hCpos, hmain⟩ := perShiftFibreVarG_of_bump ρ hρ hρ1 P hd1 p hp hpt r hr
  refine ⟨C, hCpos, ?_⟩
  intro l₂ k₂ U j₂ hj₂ hk₂ hU t g Bg hBg N S hdec hfarey hstrict hna M
  have hkj : k₂ ≠ 0 ∨ 0 ≤ j₂ := by
    by_cases hk0 : k₂ = 0
    · right
      have hjne : j₂ ≠ -1 := hk₂ hk0
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj₂
      rcases hj₂ with h | h | h
      · exact absurd h hjne
      · omega
      · omega
    · exact Or.inl hk0
  obtain ⟨kext, hkext⟩ := jBump_kextFam P hd1 ρ l₂ k₂ j₂ t hkj N hfarey
  have hφint : ∀ n : ℕ, MeasureTheory.Integrable
      (Work.KMTPlan.A6.varphitildeNtj P (N n) k₂ j₂ t) :=
    fun n => Work.KMTPlan.A6.integrable_varphitildeNtj P (N n) k₂ j₂ t hkj
  have hφsum : ∀ n : ℕ, Summable (fun i : ℤ => ‖Work.KMTAreas.A7.cw
      (Work.KMTPlan.A6.varphitildeNtj P (N n) k₂ j₂ t) i‖) :=
    fun n => Work.KMTPlan.A6.summable_cw_varphitildeNtj P (N n) k₂ j₂ t hkj
  have hφsupp : ∀ n : ℕ, ∀ ξ : ℝ, Work.KMTPlan.A6.varphitildeNtj P (N n) k₂ j₂ t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (-(2 * (((P.natDegree * U : ℕ) : ℤ))) - 1) := by
    intro n ξ hξ
    refine Work.KMTAreas.A7Hi.varphitildeNt_support_strict_g P hd1 (N n) k₂ U t ?_ ξ ?_
    · exact_mod_cast hstrict n
    · exact Work.KMTPlan.A6.varphitildeNt_ne_zero_of_varphitildeNtj_ne_zero P (N n) k₂ j₂ t hξ
  exact hmain l₂ U (fun n => Work.KMTPlan.A6.varphitildeNtj P (N n) k₂ j₂ t) kext hU
    hφint hφsum hφsupp hkext hna g Bg hBg S M

end

end Work.KMTPlan.A6Clean
