import Mathlib
import Submission.Work.BourgainPlan.Maximal.MtaDefs
import Submission.Work.BourgainPlan.Maximal.marcinkiewicz_two_strong_memLp_uniform

set_option linter.style.haveILetI false

namespace Work.BourgainPlan.Maximal

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! ## Elementary properties of the truncation `mtaTrunc` -/

/-- `mtaTrunc N f` is the indicator of the interval `[-N, N]` times `f`. -/
lemma mtaTrunc_eq_indicator (N : ℕ) (f : ℝ → ℂ) :
    mtaTrunc N f = (Set.Icc (-(N : ℝ)) (N : ℝ)).indicator f := by
  funext x
  by_cases hx : x ∈ Set.Icc (-(N : ℝ)) (N : ℝ)
  · rw [Set.indicator_of_mem hx, mtaTrunc_eq_self_of_mem hx]
  · rw [Set.indicator_of_notMem hx, mtaTrunc_eq_zero_of_notMem hx]

/-- Truncation preserves `MemLp`. -/
lemma memLp_mtaTrunc {p : ℝ≥0∞} (N : ℕ) {f : ℝ → ℂ}
    (hf : MemLp f p (volume : Measure ℝ)) : MemLp (mtaTrunc N f) p (volume : Measure ℝ) := by
  rw [mtaTrunc_eq_indicator]
  exact hf.indicator measurableSet_Icc

/-- The `Lᵖ` norm of a truncation is at most that of the function. -/
lemma eLpNorm_mtaTrunc_le (N : ℕ) (f : ℝ → ℂ) (p : ℝ≥0∞) :
    eLpNorm (mtaTrunc N f) p (volume : Measure ℝ)
      ≤ eLpNorm f p (volume : Measure ℝ) := by
  by_cases hf : AEStronglyMeasurable f (volume : Measure ℝ)
  · refine eLpNorm_mono ?_ (norm_mtaTrunc_apply_le N f)
    unfold mtaTrunc
    exact hf.mul (measurable_const.indicator measurableSet_Icc).aestronglyMeasurable
  · rw [eLpNorm_of_not_aestronglyMeasurable hf]; exact le_top

/-- The truncation of an `L^q` function, `1 ≤ q`, to a bounded interval is integrable: on
`[-N, N]` the measure is finite, so `L^q ⊆ L¹`. -/
lemma integrable_mtaTrunc_of_memLp (N : ℕ) {q : ℝ} (hq : 1 ≤ q) {f : ℝ → ℂ}
    (hf : MemLp f (ENNReal.ofReal q) (volume : Measure ℝ)) :
    Integrable (mtaTrunc N f) (volume : Measure ℝ) := by
  set s : Set ℝ := Set.Icc (-(N : ℝ)) (N : ℝ) with hsdef
  have hs : MeasurableSet s := measurableSet_Icc
  have hvol : (volume : Measure ℝ) s < ⊤ := by
    rw [hsdef, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict s) :=
    ⟨by simpa using hvol⟩
  have hq1 : (1 : ENNReal) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq
  have hint : Integrable f ((volume : Measure ℝ).restrict s) :=
    MemLp.integrable hq1 (hf.restrict s)
  rw [mtaTrunc_eq_indicator]
  exact IntegrableOn.integrable_indicator (show IntegrableOn f s (volume : Measure ℝ) from hint) hs

/-! ## Interpolation between `L²` and `L^{p₁}` for the truncated block operators -/

/-- **Interpolation of the `L²` and `L^{p₁}` bounds of the truncated block operators `mtaBlkOp`.**

The block operator `mtaBlkOp P K ε s` is additive on integrable functions (`hadd`), positively
homogeneous (`hsmul`) and has a.e.-measurable norm on integrable functions (`hmeas`).  Its `L²`
bound decays like `2^{-|s|/deg P}` (`hL₂`) and its `L^{p₁}` bound is uniform in `s` (`hLp₁`).

Marcinkiewicz/Stein interpolation of the two strong bounds, applied to the *truncated* operator
`g ↦ ‖mtaBlkOp P K ε s (mtaTrunc N g)‖`, gives the intermediate exponent `p ∈ (2, p₁)` with the
log-convex constant `c · A^θ · B^{1-θ}`, where `A = C₂ · 2^{-|s|/deg P}`, `θ = 2(p₁-p)/(p(p₁-2))`
and `c` depends only on the exponents.

The truncation is what makes the Marcinkiewicz hypotheses available: an `L^p` function truncated
to the bounded interval `[-N, N]` is integrable, so the pointwise additivity `hadd` (which is only
assumed on integrable functions) applies to the truncated pieces. -/
theorem mtaBlkOp_trunc_interp (P : Polynomial ℤ) (p p₁ : ℝ) (h2 : 2 < p) (hp : p < p₁)
    (C₂ B : ℝ) (hC₂ : 0 < C₂) (hB : 0 < B)
    (hL₂ : ∀ (K : ℕ) (ε : ℕ → ℂ), (∀ k : ℕ, ‖ε k‖ ≤ 1) → ∀ (s : ℤ) (g : ℝ → ℂ),
      MeasureTheory.MemLp g 2 MeasureTheory.volume →
      MeasureTheory.eLpNorm (Work.BourgainPlan.Maximal.mtaBlkOp P K ε s g) 2 MeasureTheory.volume
        ≤ ENNReal.ofReal (C₂ * (2:ℝ) ^ (-(↑(|s|) : ℝ) / (P.natDegree : ℝ)))
          * MeasureTheory.eLpNorm g 2 MeasureTheory.volume)
    (hLp₁ : ∀ (K : ℕ) (ε : ℕ → ℂ), (∀ k : ℕ, ‖ε k‖ ≤ 1) → ∀ (s : ℤ) (g : ℝ → ℂ),
      MeasureTheory.MemLp g (ENNReal.ofReal p₁) MeasureTheory.volume →
      MeasureTheory.eLpNorm (Work.BourgainPlan.Maximal.mtaBlkOp P K ε s g) (ENNReal.ofReal p₁) MeasureTheory.volume
        ≤ ENNReal.ofReal B * MeasureTheory.eLpNorm g (ENNReal.ofReal p₁) MeasureTheory.volume)
    (hadd : ∀ (K : ℕ) (ε : ℕ → ℂ) (s : ℤ) {u v : ℝ → ℂ}, MeasureTheory.Integrable u →
      MeasureTheory.Integrable v → ∀ x : ℝ,
      Work.BourgainPlan.Maximal.mtaBlkOp P K ε s (u + v) x
        = Work.BourgainPlan.Maximal.mtaBlkOp P K ε s u x + Work.BourgainPlan.Maximal.mtaBlkOp P K ε s v x)
    (hsmul : ∀ (K : ℕ) (ε : ℕ → ℂ) (s : ℤ) (c : ℂ) (u : ℝ → ℂ) (x : ℝ),
      Work.BourgainPlan.Maximal.mtaBlkOp P K ε s (c • u) x
        = c * Work.BourgainPlan.Maximal.mtaBlkOp P K ε s u x)
    (hmeas : ∀ (K : ℕ) (ε : ℕ → ℂ) (s : ℤ) {u : ℝ → ℂ}, MeasureTheory.Integrable u →
      AEMeasurable (fun x : ℝ => ‖Work.BourgainPlan.Maximal.mtaBlkOp P K ε s u x‖ₑ) MeasureTheory.volume) :
    ∃ c : ℝ, 0 < c ∧ ∀ (K : ℕ) (ε : ℕ → ℂ), (∀ k : ℕ, ‖ε k‖ ≤ 1) → ∀ (s : ℤ) (N : ℕ) (f : ℝ → ℂ),
      MeasureTheory.MemLp f (ENNReal.ofReal p) MeasureTheory.volume →
      MeasureTheory.eLpNorm (fun x : ℝ =>
          ‖Work.BourgainPlan.Maximal.mtaBlkOp P K ε s
            (Work.BourgainPlan.Maximal.mtaTrunc N f) x‖ₑ) (ENNReal.ofReal p) MeasureTheory.volume
        ≤ ENNReal.ofReal (c * (C₂ * (2:ℝ) ^ (-(↑(|s|) : ℝ) / (P.natDegree : ℝ))) ^ (2 * (p₁ - p) / (p * (p₁ - 2)))
            * B ^ (1 - 2 * (p₁ - p) / (p * (p₁ - 2)))) * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.volume := by
  have hp1 : 2 < p₁ := lt_trans h2 hp
  -- integrability of truncations of `Lᵖ` functions
  have hint : ∀ (N : ℕ) (u : ℝ → ℂ), MemLp u (ENNReal.ofReal p) (volume : Measure ℝ) →
      Integrable (mtaTrunc N u) (volume : Measure ℝ) :=
    fun N u hu => integrable_mtaTrunc_of_memLp N (by linarith) hu
  -- the interpolation with exponents `q = 2`, `p₀ = p₁`, `p = p`
  obtain ⟨C, hCpos, hC⟩ := marcinkiewicz_two_strong_memLp_uniform
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (q := 2) (p₀ := p₁) (p := p) (θ := 2 * (p₁ - p) / (p * (p₁ - 2)))
    (by norm_num) hp1 h2 hp (by
      have hp0' : p ≠ 0 := by linarith
      have hp1' : p₁ ≠ 0 := by linarith
      have hp12 : p₁ - 2 ≠ 0 := by linarith
      field_simp
      ring)
  refine ⟨C, hCpos, ?_⟩
  intro K ε hε s N f hf
  have hKq : 0 < C₂ * (2:ℝ) ^ (-(↑(|s|) : ℝ) / (P.natDegree : ℝ)) :=
    mul_pos hC₂ (Real.rpow_pos_of_pos (by norm_num) _)
  -- the truncated operator
  have hsub : ∀ (u v : ℝ → ℂ), MemLp u (ENNReal.ofReal p) (volume : Measure ℝ) →
      MemLp v (ENNReal.ofReal p) (volume : Measure ℝ) → ∀ y : ℝ,
      ‖mtaBlkOp P K ε s (mtaTrunc N (u + v)) y‖ₑ
        ≤ ‖mtaBlkOp P K ε s (mtaTrunc N u) y‖ₑ
          + ‖mtaBlkOp P K ε s (mtaTrunc N v) y‖ₑ := by
    intro u v hu hv y
    rw [mtaTrunc_add, hadd K ε s (hint N u hu) (hint N v hv) y]
    exact enorm_add_le _ _
  have hhom : ∀ (c : ℂ) (u : ℝ → ℂ),
      (fun g : ℝ → ℂ => fun x : ℝ => ‖mtaBlkOp P K ε s (mtaTrunc N g) x‖ₑ) (c • u)
        = fun y : ℝ => ‖c‖ₑ
            * (fun g : ℝ → ℂ => fun x : ℝ => ‖mtaBlkOp P K ε s (mtaTrunc N g) x‖ₑ) u y := by
    intro c u
    funext y
    show ‖mtaBlkOp P K ε s (mtaTrunc N (c • u)) y‖ₑ
        = ‖c‖ₑ * ‖mtaBlkOp P K ε s (mtaTrunc N u) y‖ₑ
    rw [mtaTrunc_smul, hsmul K ε s c (mtaTrunc N u) y, enorm_mul]
  have hmeas' : ∀ (u : ℝ → ℂ), MemLp u (ENNReal.ofReal p) (volume : Measure ℝ) →
      AEMeasurable (fun x : ℝ => ‖mtaBlkOp P K ε s (mtaTrunc N u) x‖ₑ) (volume : Measure ℝ) :=
    fun u hu => hmeas K ε s (hint N u hu)
  have hqbd : ∀ (u : ℝ → ℂ), MemLp u (ENNReal.ofReal (2:ℝ)) (volume : Measure ℝ) →
      eLpNorm (fun x : ℝ => ‖mtaBlkOp P K ε s (mtaTrunc N u) x‖ₑ)
          (ENNReal.ofReal (2:ℝ)) (volume : Measure ℝ)
        ≤ ENNReal.ofReal (C₂ * (2:ℝ) ^ (-(↑(|s|) : ℝ) / (P.natDegree : ℝ)))
          * eLpNorm u (ENNReal.ofReal (2:ℝ)) (volume : Measure ℝ) := by
    intro u hu
    have hu2 : MemLp u 2 (volume : Measure ℝ) := by
      rwa [show ENNReal.ofReal (2:ℝ) = 2 from by norm_num] at hu
    have htu : MemLp (mtaTrunc N u) 2 (volume : Measure ℝ) := memLp_mtaTrunc N hu2
    have hb := hL₂ K ε hε s (mtaTrunc N u) htu
    calc eLpNorm (fun x : ℝ => ‖mtaBlkOp P K ε s (mtaTrunc N u) x‖ₑ)
            (ENNReal.ofReal (2:ℝ)) (volume : Measure ℝ)
        ≤ eLpNorm (mtaBlkOp P K ε s (mtaTrunc N u)) (ENNReal.ofReal (2:ℝ))
            (volume : Measure ℝ) := by
          by_cases hF : AEStronglyMeasurable (mtaBlkOp P K ε s (mtaTrunc N u)) volume
          · exact (eLpNorm_enorm _ hF).le
          · rw [eLpNorm_of_not_aestronglyMeasurable hF]; exact le_top
      _ = eLpNorm (mtaBlkOp P K ε s (mtaTrunc N u)) 2 (volume : Measure ℝ) := by
            rw [show ENNReal.ofReal (2:ℝ) = 2 from by norm_num]
      _ ≤ ENNReal.ofReal (C₂ * (2:ℝ) ^ (-(↑(|s|) : ℝ) / (P.natDegree : ℝ)))
            * eLpNorm (mtaTrunc N u) 2 (volume : Measure ℝ) := hb
      _ ≤ ENNReal.ofReal (C₂ * (2:ℝ) ^ (-(↑(|s|) : ℝ) / (P.natDegree : ℝ)))
            * eLpNorm u 2 (volume : Measure ℝ) :=
            mul_le_mul_of_nonneg_left (eLpNorm_mtaTrunc_le N u 2) bot_le
      _ = ENNReal.ofReal (C₂ * (2:ℝ) ^ (-(↑(|s|) : ℝ) / (P.natDegree : ℝ)))
            * eLpNorm u (ENNReal.ofReal (2:ℝ)) (volume : Measure ℝ) := by
            rw [show ENNReal.ofReal (2:ℝ) = 2 from by norm_num]
  have hpbd : ∀ (u : ℝ → ℂ), MemLp u (ENNReal.ofReal p₁) (volume : Measure ℝ) →
      eLpNorm (fun x : ℝ => ‖mtaBlkOp P K ε s (mtaTrunc N u) x‖ₑ)
          (ENNReal.ofReal p₁) (volume : Measure ℝ)
        ≤ ENNReal.ofReal B * eLpNorm u (ENNReal.ofReal p₁) (volume : Measure ℝ) := by
    intro u hu
    have htu : MemLp (mtaTrunc N u) (ENNReal.ofReal p₁) (volume : Measure ℝ) :=
      memLp_mtaTrunc N hu
    have hb := hLp₁ K ε hε s (mtaTrunc N u) htu
    calc eLpNorm (fun x : ℝ => ‖mtaBlkOp P K ε s (mtaTrunc N u) x‖ₑ)
            (ENNReal.ofReal p₁) (volume : Measure ℝ)
        ≤ eLpNorm (mtaBlkOp P K ε s (mtaTrunc N u)) (ENNReal.ofReal p₁)
            (volume : Measure ℝ) := by
          by_cases hF : AEStronglyMeasurable (mtaBlkOp P K ε s (mtaTrunc N u)) volume
          · exact (eLpNorm_enorm _ hF).le
          · rw [eLpNorm_of_not_aestronglyMeasurable hF]; exact le_top
      _ ≤ ENNReal.ofReal B * eLpNorm (mtaTrunc N u) (ENNReal.ofReal p₁) (volume : Measure ℝ) := hb
      _ ≤ ENNReal.ofReal B * eLpNorm u (ENNReal.ofReal p₁) (volume : Measure ℝ) :=
            mul_le_mul_of_nonneg_left (eLpNorm_mtaTrunc_le N u (ENNReal.ofReal p₁)) bot_le
  have := hC (T := fun g : ℝ → ℂ => fun x : ℝ =>
      ‖mtaBlkOp P K ε s (mtaTrunc N g) x‖ₑ) hsub hhom hmeas'
    (Kq := C₂ * (2:ℝ) ^ (-(↑(|s|) : ℝ) / (P.natDegree : ℝ))) (Kp := B) hKq hB hqbd hpbd f hf
  simpa using this

end

end Work.BourgainPlan.Maximal
