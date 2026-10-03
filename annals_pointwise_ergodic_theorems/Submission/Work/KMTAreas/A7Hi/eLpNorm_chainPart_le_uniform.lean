import Mathlib
import Submission.Work.KMTAreas.A7Hi2.chainLeFiniteIntegral
import Submission.Work.KMTAreas.A7.lacDevSymBoundAlt
import Submission.Work.KMTAreas.A7.lacDevHormanderAlt
import Submission.Port.Aesm

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- **Axiom-clean form of `Work.KMTAreas.A7Hi.DilVar`.**  The wrapper `Work.KMTAreas.A7Hi.DilVar`
consumes the *stub* `Work.KMTAreas.A7.lacDevHormander`; here we instead consume the proved
re-export `Work.KMTAreas.A7.lacDevHormanderAlt` (from `A7/LoDevHormander.lean`) together with the
proved symbol bound `Work.KMTAreas.A7.lacDevSymBoundAlt`, and feed them to the (proved) assembly
`Work.KMTAreas.A7.lacDilDevSqSum_of_inputs` and the (proved) `lacunaryBumpDilationVar_of_pieces`.
The statement is verbatim that of `DilVar`. -/
theorem DilVarClean (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 2 < r) (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n)
      (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' j : ℤ, (1 / (σ n : ℝ)) * K ((j : ℝ) / (σ n)) * f (x - j)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
  obtain ⟨Csym, hCsympos, hsym⟩ := Work.KMTAreas.A7.lacDevSymBoundAlt K
  obtain ⟨A2, hA2pos, hA2⟩ := Work.KMTAreas.A7.lacDevL2 K Csym hCsympos hsym
  obtain ⟨Ak, hAkpos, hAk⟩ := Work.KMTAreas.A7.lacDevHormanderAlt K
  obtain ⟨Cdev, hCdevpos, hDev⟩ :=
    Work.KMTAreas.A7.lacDilDevSqSum_of_inputs p hp K Csym hCsympos hsym
      ⟨A2, hA2pos, hA2⟩ ⟨Ak, hAkpos, hAk⟩
  exact Work.KMTAreas.A7Hi.lacunaryBumpDilationVar_of_pieces p hp r hr K
    (Work.KMTAreas.A7.lacDilTriVar p hp r hr) ⟨Cdev, hCdevpos, hDev⟩

theorem eLpNorm_chainPart_le_uniform (ρ : ℝ) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (l₁ m₀ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℤ → ℂ, Summable (fun n : ℤ => ‖f n‖ ^ p.toReal) →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  have hp0 : (0 : ℝ) < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one hp)) (ne_of_lt hptop)
  have hp1 : (1 : ℝ) < p.toReal := by
    rw [← ENNReal.ofReal_lt_ofReal_iff hp0, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal (ne_of_lt hptop)]
    exact hp
  obtain ⟨C, hCpos, hC⟩ :=
    DilVarClean p.toReal hp1 r hr Work.KMTAreas.A7Hi.kmtPhiSch
  refine ⟨(1 + ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)) * C,
    by positivity, ?_⟩
  intro f hf
  have hpt := Work.KMTAreas.A7Hi2.chainPart_le_sum_variationalNorm
    ρ l₁ m₀ r hr p hp hptop f hf
  have h1 : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)) p MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
          ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
            PointwiseErgodicTheorems.variationalNorm r
              (fun m : ℕ => Work.KMTAreas.A7Hi.dilFam Work.KMTAreas.A7Hi.kmtPhiSch
                (Work.KMTAreas.A7Hi.lpfScale m₀) (Work.KMTAreas.A7Hi.charMul α f) m x))
        p MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by simpa only [enorm_eq_self] using hpt x)
  have h2 : MeasureTheory.eLpNorm (fun x : ℤ =>
          ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
            PointwiseErgodicTheorems.variationalNorm r
              (fun m : ℕ => Work.KMTAreas.A7Hi.dilFam Work.KMTAreas.A7Hi.kmtPhiSch
                (Work.KMTAreas.A7Hi.lpfScale m₀) (Work.KMTAreas.A7Hi.charMul α f) m x))
        p MeasureTheory.Measure.count
      ≤ ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
          MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun m : ℕ => Work.KMTAreas.A7Hi.dilFam Work.KMTAreas.A7Hi.kmtPhiSch
                (Work.KMTAreas.A7Hi.lpfScale m₀) (Work.KMTAreas.A7Hi.charMul α f) m x))
            p MeasureTheory.Measure.count :=
    Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal (le_of_lt hp)
      (fun α _ => (measurable_of_countable _).aemeasurable)
  have h3 : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
      MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r
            (fun m : ℕ => Work.KMTAreas.A7Hi.dilFam Work.KMTAreas.A7Hi.kmtPhiSch
              (Work.KMTAreas.A7Hi.lpfScale m₀) (Work.KMTAreas.A7Hi.charMul α f) m x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    intro α _
    have hD := hC (Work.KMTAreas.A7Hi.lpfScale m₀)
      (fun m => Work.KMTAreas.A7Hi.lpfScale_pos m₀ m)
      (fun m => Work.KMTAreas.A7Hi.lpfScale_lacunary m₀ m)
      (Work.KMTAreas.A7Hi.charMul α f)
    rw [show p = ENNReal.ofReal p.toReal from (ENNReal.ofReal_toReal (ne_of_lt hptop)).symm]
    refine hD.trans (le_of_eq ?_)
    congr 1
    refine MeasureTheory.eLpNorm_congr_norm_ae (hf := by pw_aesm) (hg := by pw_aesm) (Filter.Eventually.of_forall fun y => ?_)
    exact Work.KMTAreas.A7Hi.norm_charMul α f y
  have hsum : (∑ _α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
        ENNReal.ofReal C * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count)
      = ENNReal.ofReal (((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ) * C)
        * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine (h1.trans (h2.trans (Finset.sum_le_sum h3))).trans ?_
  rw [hsum]
  have hcard : (0 : ℝ) ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ) :=
    Nat.cast_nonneg _
  have hle : ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ) * C
      ≤ (1 + ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)) * C :=
    mul_le_mul_of_nonneg_right (by linarith) hCpos.le
  exact mul_le_mul (ENNReal.ofReal_le_ofReal hle) le_rfl bot_le bot_le

end Work.KMTAreas.A7Hi
