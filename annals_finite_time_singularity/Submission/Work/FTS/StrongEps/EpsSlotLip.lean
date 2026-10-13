import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.Gdot
import Submission.Work.FTS.StrongEps.epsSol_eq_integral
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.EpsSlotAux
import Submission.Work.FTS.StrongEps.aemeasurable_mixed_family
import Submission.Work.FTS.StrongEps.mixed_sub_of_contDiffOn_four

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

theorem EpsSlotLip {α T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam}
    (hsol : ∀ n : ℕ, Work.FTS.StrongEps.IsEpsSol α ρ (ε n) T Φs E g₀ (G n))
    (hregG : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice (G n) τ))
        Work.FTS.EllipticEst.Q0)
    (hsmooth : ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.StrongEps.epsRHS α ρ (ε n) Φs E (G n) s))
        Work.FTS.EllipticEst.Q0)
    (hcont : ∀ n : ℕ, ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => Work.FTS.StrongEps.epsRHS α ρ (ε n) Φs E (G n) s p.1 p.2)
        (Set.Icc (0 : ℝ) T))
    (hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ (j i : ℕ), j + i ≤ 4 → ∀ s ∈ Set.Icc (0 : ℝ) T,
        ∀ p ∈ K, |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHS α ρ (ε n) Φs E (G n) s) p.1 p.2| ≤ C) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ (j i : ℕ), j + i ≤ 4 → ∀ p ∈ K,
        ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
          |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) τ) p.1 p.2
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) τ') p.1 p.2| ≤ C * |τ - τ'| := by
  intro K hK hKQ
  -- a compact `S ⊆ Q0`, a scale `δ > 0` and, for every `p ∈ K`, a box around `p` inside `S`
  obtain ⟨S, hScomp, hSQ, δ, hδpos, h2δ1, h2δ2, h2δ3, hmemz, hmemθ, hboxmem⟩ :=
    exists_uniform_compact_set K hK hKQ
  obtain ⟨C₀, hC₀nn, hC₀⟩ := hbdd S hScomp hSQ
  refine ⟨C₀, hC₀nn, ?_⟩
  intro n j i hji p hp τ hτ τ' hτ'
  -- the main estimate, for `σ' ≤ σ`
  have key : ∀ σ σ' : ℝ, σ ∈ Set.Icc (0 : ℝ) T → σ' ∈ Set.Icc (0 : ℝ) T → σ' ≤ σ →
      |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) σ) p.1 p.2
        - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) σ') p.1 p.2|
        ≤ C₀ * |σ - σ'| := by
    intro σ σ' hσ hσ' hle
    obtain ⟨hp1, hp2, hp3⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)
    -- the box around `p`
    set z₁ : ℝ := p.1 - δ / 2 with hz₁
    set z₂ : ℝ := p.1 + δ / 2 with hz₂
    set θ₁ : ℝ := p.2 - δ / 2 with hθ₁
    set θ₂ : ℝ := p.2 + δ / 2 with hθ₂
    have hz1lt : z₁ < p.1 := by rw [hz₁]; linarith
    have hz2gt : p.1 < z₂ := by rw [hz₂]; linarith
    have hθ1lt : θ₁ < p.2 := by rw [hθ₁]; linarith
    have hθ2gt : p.2 < θ₂ := by rw [hθ₂]; linarith
    have hz1pos : 0 < z₁ := by rw [hz₁]; linarith [h2δ1 p hp, hδpos]
    have hθ1pos : 0 < θ₁ := by rw [hθ₁]; linarith [h2δ2 p hp, hδpos]
    have hθ2lt : θ₂ < Real.pi / 2 := by rw [hθ₂]; linarith [h2δ3 p hp, hδpos]
    have hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0 := by
      rintro q ⟨hq1, hq2⟩
      exact Work.FTS.EllipticEst.mem_Q0.mpr
        ⟨lt_of_lt_of_le hz1pos hq1.1, lt_of_lt_of_le hθ1pos hq2.1, lt_of_le_of_lt hq2.2 hθ2lt⟩
    have hpbox : p ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ :=
      ⟨⟨le_of_lt hz1lt, le_of_lt hz2gt⟩, ⟨le_of_lt hθ1lt, le_of_lt hθ2gt⟩⟩
    have hpbox' : (p.1, p.2) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂ :=
      ⟨⟨hz1lt, hz2gt⟩, ⟨hθ1lt, hθ2gt⟩⟩
    -- the uniform slot bound on the closed box
    have hbdd' : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ 4 → ∀ q : ℝ × ℝ,
        q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ →
          |Work.Spaces.mixed k l (Work.FTS.StrongEps.epsRHS α ρ (ε n) Φs E (G n) s)
            q.1 q.2| ≤ C₀ := by
      intro s hs k l hkl q hq
      refine hC₀ n k l hkl s hs q (hboxmem p hp q.1 q.2 ?_ ?_)
      · rw [abs_le]
        exact ⟨by linarith [(Set.mem_Icc.mp hq.1).1], by linarith [(Set.mem_Icc.mp hq.1).2]⟩
      · rw [abs_le]
        exact ⟨by linarith [(Set.mem_Icc.mp hq.2).1], by linarith [(Set.mem_Icc.mp hq.2).2]⟩
    -- the pointwise identity on `Q0`, from the integral form of the `ε`-scheme
    have hident : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        Work.FTS.Galerkin.slice (G n) σ z θ - Work.FTS.Galerkin.slice (G n) σ' z θ
          = ∫ s in σ'..σ, Work.FTS.StrongEps.epsRHS α ρ (ε n) Φs E (G n) s z θ := by
      intro z θ hzθ
      have hcg : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
          ContinuousOn (fun s : ℝ =>
            Work.FTS.StrongEps.epsRHS α ρ (ε n) Φs E (G n) s z θ) (Set.Icc (0 : ℝ) T) :=
        fun z θ hzθ => hcont n (z, θ) hzθ
      have h1 := Work.FTS.StrongEps.epsSol_eq_integral (hsol n) hcg z θ σ hzθ hσ
      have h2 := Work.FTS.StrongEps.epsSol_eq_integral (hsol n) hcg z θ σ' hzθ hσ'
      have hcontF : ContinuousOn
          (fun s : ℝ => Work.FTS.StrongEps.epsRHS α ρ (ε n) Φs E (G n) s z θ)
          (Set.Icc (0 : ℝ) T) := hcont n (z, θ) hzθ
      have hi1 : IntervalIntegrable
          (fun s : ℝ => Work.FTS.StrongEps.epsRHS α ρ (ε n) Φs E (G n) s z θ)
          volume 0 σ' :=
        ContinuousOn.intervalIntegrable_of_Icc hσ'.1
          (hcontF.mono (Set.Icc_subset_Icc le_rfl hσ'.2))
      have hi2 : IntervalIntegrable
          (fun s : ℝ => Work.FTS.StrongEps.epsRHS α ρ (ε n) Φs E (G n) s z θ)
          volume σ' σ :=
        ContinuousOn.intervalIntegrable_of_Icc hle
          (hcontF.mono (Set.Icc_subset_Icc hσ'.1 hσ.2))
      have hadj := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
      show (G n) z θ σ - (G n) z θ σ' = _
      rw [h1, h2]
      linarith
    -- smoothness of the profiles `s ↦ epsRHS … s`
    have hsmE : ∀ s ∈ Set.Icc (0 : ℝ) T,
        Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsRHS α ρ (ε n) Φs E (G n) s) :=
      fun s hs => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr
        (fun k => hsmooth n s hs k)
    -- measurability in `s` of the slots
    have hmeas := Work.FTS.StrongEps.aemeasurable_mixed_family
      (H := fun s : ℝ => Work.FTS.StrongEps.epsRHS α ρ (ε n) Φs E (G n) s) hsmE
      (fun z θ hzθ => hcont n (z, θ) hzθ)
    -- the exchange of `mixed j i` with the interval integral
    have hint := mixed_intervalIntegral_eq
      (H := fun s : ℝ => Work.FTS.StrongEps.epsRHS α ρ (ε n) Φs E (G n) s)
      (a := σ') (b := σ) hσ' hσ hle hC₀nn hsmE hmeas hbdd' hboxQ (j := j) (i := i) hji
      p.1 p.2 hpbox'
    -- additivity of `mixed j i` across the (smooth) difference of the two slices
    have hsub := Work.FTS.StrongEps.mixed_sub_of_contDiffOn_four (j := j) (i := i) hji hp1
      ⟨hp2, hp3⟩ (hregG n σ hσ) (hregG n σ' hσ')
    -- locality: the difference of the slices agrees with the integral on `Q0`
    have hloc : Work.Spaces.mixed j i (fun z θ =>
          Work.FTS.Galerkin.slice (G n) σ z θ - Work.FTS.Galerkin.slice (G n) σ' z θ) p.1 p.2
        = Work.Spaces.mixed j i (fun z θ =>
            ∫ s in σ'..σ, Work.FTS.StrongEps.epsRHS α ρ (ε n) Φs E (G n) s z θ) p.1 p.2 := by
      have hEq := mixed_congr_of_isOpen
        (f := fun z θ => Work.FTS.Galerkin.slice (G n) σ z θ
          - Work.FTS.Galerkin.slice (G n) σ' z θ)
        (g := fun z θ => ∫ s in σ'..σ,
          Work.FTS.StrongEps.epsRHS α ρ (ε n) Φs E (G n) s z θ)
        Work.FTS.EllipticEst.isOpen_Q0 (fun q hq => hident q.1 q.2 hq) j i (hKQ hp)
      simpa only [Function.uncurry] using hEq
    -- the estimate
    calc |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) σ) p.1 p.2
            - Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) σ') p.1 p.2|
        = |Work.Spaces.mixed j i (fun z θ => Work.FTS.Galerkin.slice (G n) σ z θ
            - Work.FTS.Galerkin.slice (G n) σ' z θ) p.1 p.2| := by rw [hsub]
      _ = |Work.Spaces.mixed j i (fun z θ =>
            ∫ s in σ'..σ, Work.FTS.StrongEps.epsRHS α ρ (ε n) Φs E (G n) s z θ)
              p.1 p.2| := by rw [hloc]
      _ = |∫ s in σ'..σ, Work.Spaces.mixed j i
            (Work.FTS.StrongEps.epsRHS α ρ (ε n) Φs E (G n) s) p.1 p.2| := by rw [hint]
      _ ≤ ∫ s in σ'..σ, |Work.Spaces.mixed j i
            (Work.FTS.StrongEps.epsRHS α ρ (ε n) Φs E (G n) s) p.1 p.2| :=
            intervalIntegral.abs_integral_le_integral_abs hle
      _ ≤ ∫ s in σ'..σ, C₀ := by
            refine intervalIntegral.integral_mono_on hle ?_ ?_ ?_
            · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
              refine IntegrableOn.of_bound ?_ ?_ C₀ ?_
              · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
              · have h1 := (hmeas j i p.1 p.2 (hKQ hp)).mono_measure
                  (Measure.restrict_mono (s := Set.Ioc σ' σ) (s' := Set.Icc (0 : ℝ) T)
                    (fun t ht => ⟨le_trans hσ'.1 ht.1.le, le_trans ht.2 hσ.2⟩) le_rfl)
                simpa only [Real.norm_eq_abs] using h1.norm
              · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
                rw [Real.norm_eq_abs, abs_abs]
                exact hbdd' s ⟨le_trans hσ'.1 hs.1.le, le_trans hs.2 hσ.2⟩ j i hji p hpbox
            · exact intervalIntegrable_const
            · intro s hs
              exact hbdd' s ⟨le_trans hσ'.1 hs.1, le_trans hs.2 hσ.2⟩ j i hji p hpbox
      _ = C₀ * (σ - σ') := by
            rw [intervalIntegral.integral_const]
            simp only [smul_eq_mul]
            ring
      _ = C₀ * |σ - σ'| := by rw [abs_of_nonneg (sub_nonneg.mpr hle)]
  rcases le_total τ' τ with hle | hle
  · exact key τ τ' hτ hτ' hle
  · have h := key τ' τ hτ' hτ hle
    rw [abs_sub_comm (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) τ) p.1 p.2)
          (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (G n) τ') p.1 p.2),
        abs_sub_comm τ τ']
    exact h

end Work.FTS.StrongEps
