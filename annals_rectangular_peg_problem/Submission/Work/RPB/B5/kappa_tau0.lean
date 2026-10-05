import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B2.chordSurf_lagrangian
import Submission.Work.RPV.levelPt_omega
import Submission.Work.RPB.B5.chartJets_chartLev_slice
import Submission.Work.RPB.B5.circle_chord_data
import Submission.Work.RPB.B5.chordPhase_zero_eq
import Submission.Work.RPB.B5.iteratedDeriv_eq_of_eqOn_Ioo_left
import Submission.Work.RPB.B5.level_inverse_arcsin_sq

namespace Work.RPB.B5

open scoped ContDiff

/-! ## Helpers -/

private lemma kappa_uproj_contDiff : ContDiff ℝ 12 (fun p : Work.RPV.PS => Work.RPV.uproj p) := by
  unfold Work.RPV.uproj
  have h12 : ContDiff ℝ 12 (fun p : Work.RPV.PS => ((p.1.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_id.fst.snd)
  have h11 : ContDiff ℝ 12 (fun p : Work.RPV.PS => ((p.1.1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_id.fst.fst)
  have h21 : ContDiff ℝ 12 (fun p : Work.RPV.PS => ((p.2.1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_id.snd.fst)
  exact ((Complex.contDiff_exp.comp (h12.mul contDiff_const))).mul
    (h21.add (h11.mul contDiff_const))

private lemma kappa_q2_contDiff : ContDiff ℝ 12 (fun p : Work.RPV.PS => p.1.2) := by fun_prop

private lemma kappa_uproj_chordSurf (c : ℝ → ℝ → ℂ) (a : ℝ → ℝ → ℝ → ℝ) (τ t r : ℝ) :
    Work.RPV.uproj (Work.RPB.chordSurf c a τ t r) = Work.RPB.halfChordSum c τ t r := by
  rw [Work.RPB.chordSurf, Work.RPB.halfChordSum, Work.RPV.uproj_chordPS]

/-- The composite `σ ↦ (W 0 t (ρh 0 t σ))` and both of its projections to be used later
(`uproj` and the angle coordinate `q₂`) are `C¹²` at `σ = 0`. -/
private lemma kappa_chart_contDiffAt {ρ₀ κ : ℝ} (hκ : 0 < κ) {W : ℝ → ℝ → ℝ → Work.RPV.PS}
    {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (t : ℝ) :
    ContDiffAt ℝ 12 (fun σ : ℝ => Work.RPV.uproj (W 0 t (ρh 0 t σ))) 0 ∧
    ContDiffAt ℝ 12 (fun σ : ℝ => (W 0 t (ρh 0 t σ)).1.2) 0 := by
  have hsliceρ : ContDiffOn ℝ 12 (fun σ : ℝ => ρh 0 t σ) (Set.Ioo (-κ) κ) :=
    (hρh.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
      (fun σ hσ => ⟨by norm_num, Set.mem_univ _, hσ⟩)).congr (fun _ _ => rfl)
  have hsliceW : ContDiffOn ℝ 12 (fun ρ : ℝ => W 0 t ρ) (Set.Ioo (-ρ₀) ρ₀) :=
    (hW.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
      (fun ρ hρ => ⟨by norm_num, Set.mem_univ _, hρ⟩)).congr (fun _ _ => rfl)
  have hcomp : ContDiffOn ℝ 12 (fun σ : ℝ => W 0 t (ρh 0 t σ)) (Set.Ioo (-κ) κ) :=
    hsliceW.comp hsliceρ (fun σ hσ => hρhv 0 (by norm_num) t σ hσ)
  have hcompAt : ContDiffAt ℝ 12 (fun σ : ℝ => W 0 t (ρh 0 t σ)) 0 :=
    hcomp.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, hκ⟩)
  refine ⟨?_, ?_⟩
  · show ContDiffAt ℝ 12 ((fun p : Work.RPV.PS => Work.RPV.uproj p) ∘
      fun σ : ℝ => W 0 t (ρh 0 t σ)) 0
    exact ContDiffAt.comp 0 kappa_uproj_contDiff.contDiffAt hcompAt
  · show ContDiffAt ℝ 12 ((fun p : Work.RPV.PS => p.1.2) ∘
      fun σ : ℝ => W 0 t (ρh 0 t σ)) 0
    exact ContDiffAt.comp 0 kappa_q2_contDiff.contDiffAt hcompAt

theorem kappa_tau0 (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a)
    (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (κ : ℝ) (hκ : 0 < κ)
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρh0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ρh τ t 0 = 0)
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    (hρhl : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ) :
    ∃ k : ℤ, (∀ t : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) Real.pi,
        a 0 t r = t + Real.pi / 2 + 2 * Real.pi * k) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ κ ∧
        (∀ t : ℝ, ∀ σ ∈ Set.Ioo (-δ) 0,
          Work.RPV.uproj (W 0 t (ρh 0 t σ))
              = (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp (t * Complex.I) ∧
          (W 0 t (ρh 0 t σ)).1.2 = t + Real.pi / 2 + 2 * Real.pi * k) ∧
        (∀ t : ℝ, ∀ j : ℕ, j ≤ 8 →
          iteratedDeriv j (fun σ : ℝ => Work.RPV.uproj (W 0 t (ρh 0 t σ))
              - (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp (t * Complex.I)) 0 = 0) ∧
        (∀ t : ℝ, ∀ j : ℕ, j ≤ 8 →
          iteratedDeriv j (fun σ : ℝ => (W 0 t (ρh 0 t σ)).1.2
              - (t + Real.pi / 2 + 2 * Real.pi * k)) 0 = 0) := by
  obtain ⟨k, hk⟩ := chordPhase_zero_eq CI a ha
  refine ⟨k, ?_, ?_⟩
  · intro t r hr
    exact hk t r ⟨le_of_lt hr.1, le_of_lt hr.2⟩
  · set δ : ℝ := min κ 1 with hδdef
    have hδpos : 0 < δ := by rw [hδdef]; exact lt_min hκ one_pos
    have hδκ : δ ≤ κ := by rw [hδdef]; exact min_le_left _ _
    have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_right _ _
    have hW8 : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) := hW.of_le (by norm_num)
    -- ### the value statement at `τ = 0`
    have hmain : ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-δ) 0,
        Work.RPV.uproj (W 0 t (ρh 0 t σ))
            = (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp (t * Complex.I) ∧
        (W 0 t (ρh 0 t σ)).1.2 = t + Real.pi / 2 + 2 * Real.pi * k := by
      intro t σ hσ
      -- the `ρ`-slice of the level function of the chart at `τ = 0`, and its local facts
      obtain ⟨hlev0, -, ε, hεpos, hmono⟩ :=
        chartJets_chartLev_slice CI a ρ₀ hρ₀ W hW8 hWchord 0 (by norm_num) t
      have hGneg : ∃ ε : ℝ, 0 < ε ∧ ∀ ρ ∈ Set.Ioo (-ε) 0,
          Work.RPV.K0 (W 0 t ρ) + 1 < 0 := by
        refine ⟨ε, hεpos, fun ρ hρ => ?_⟩
        have hmem : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hεpos⟩
        have hρ' : ρ ∈ Set.Ioo (-ε) ε := ⟨hρ.1, by linarith [hρ.2, hεpos]⟩
        have h : Work.RPV.K0 (W 0 t ρ) + 1 < Work.RPV.K0 (W 0 t 0) + 1 :=
          hmono hρ' hmem hρ.2
        rwa [hlev0] at h
      have hGsin : ∀ ρ ∈ Set.Ioc (0 : ℝ) (Real.pi ^ 2 / 4),
          Work.RPV.K0 (W 0 t ρ) + 1 = (Real.sin (Real.sqrt ρ)) ^ 2 := by
        intro ρ hρ
        obtain ⟨hρ0, hρ1⟩ := hρ
        rcases lt_or_eq_of_le hρ0.le with hpos | h0
        · set r : ℝ := Real.sqrt ρ with hrdef
          have hrpos : 0 < r := by rw [hrdef]; exact Real.sqrt_pos.mpr hpos
          have hrsq : r ^ 2 = ρ := by rw [hrdef]; exact Real.sq_sqrt hρ0.le
          have hrle : r ≤ Real.pi / 2 := by
            rw [hrdef]
            calc Real.sqrt ρ ≤ Real.sqrt (Real.pi ^ 2 / 4) := Real.sqrt_le_sqrt hρ1
              _ = Real.pi / 2 := by
                  rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring,
                    Real.sqrt_sq (by positivity)]
          calc Work.RPV.K0 (W 0 t ρ) + 1
              = Work.RPV.K0 (W 0 t (r ^ 2)) + 1 := by rw [hrsq]
            _ = Real.sin r ^ 2 := by
                  rw [hWchord 0 (by norm_num) t r ⟨hrpos, hrle⟩, K0_chordSurf_level,
                    (circle_chord_data CI.c CI.start t r).1]
            _ = (Real.sin (Real.sqrt ρ)) ^ 2 := by rw [hrdef]
        · rw [← h0, hlev0]; simp
      -- the continuity and the level identity for the inverse branch
      have hρhcont : ContinuousOn (fun σ : ℝ => ρh 0 t σ) (Set.Ioo (-κ) κ) :=
        ((hρh.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
          (fun σ hσ => ⟨by norm_num, Set.mem_univ _, hσ⟩)).congr (fun _ _ => rfl)).continuousOn
      have hu0 : ρh 0 t 0 = 0 := hρh0 0 (by norm_num) t
      have hlvl : ∀ σ ∈ Set.Ioo (-κ) κ, Work.RPV.K0 (W 0 t (ρh 0 t σ)) + 1 = -σ :=
        fun σ hσ => hρhl 0 (by norm_num) t σ hσ
      have hσ' : σ ∈ Set.Ioo (-(min κ 1)) 0 := by rw [← hδdef]; exact hσ
      obtain ⟨hσval, hσpos, hσlt⟩ :=
        level_inverse_arcsin_sq hκ hlev0 hGneg hGsin hρhcont hu0 hlvl σ hσ'
      -- the corresponding chord parameter
      set r : ℝ := Real.arcsin (Real.sqrt (-σ)) with hrdef
      have hargneg : 0 < -σ := by linarith [hσ.2]
      have harg1 : -σ < 1 := by linarith [hσ.1, hδ1]
      have hsqrtsq : Real.sqrt (-σ) ^ 2 = -σ := Real.sq_sqrt (le_of_lt hargneg)
      have hsqpos : 0 < Real.sqrt (-σ) := Real.sqrt_pos.mpr hargneg
      have hsqlt : Real.sqrt (-σ) < 1 := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_lt_sqrt (le_of_lt hargneg) harg1
      have hrpos : 0 < r := by rw [hrdef]; exact Real.arcsin_pos.mpr hsqpos
      have hrlt : r < Real.pi / 2 := by
        rw [hrdef]; exact Real.arcsin_lt_pi_div_two.mpr hsqlt
      have hrsin : Real.sin r ^ 2 = -σ := by
        rw [hrdef, Real.sin_arcsin (by linarith) (le_of_lt hsqlt), hsqrtsq]
      have hrsq : r ^ 2 = ρh 0 t σ := by rw [hrdef]; exact hσval.symm
      have hWval : W 0 t (ρh 0 t σ) = Work.RPB.chordSurf CI.c a 0 t r := by
        rw [← hrsq]
        exact hWchord 0 (by norm_num) t r ⟨hrpos, le_of_lt hrlt⟩
      have hcos : 0 < Real.cos r :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hrlt⟩
      have hsqrt2 : Real.sqrt (2 + 2 * σ) = Real.sqrt 2 * Real.cos r := by
        have h2 : 2 + 2 * σ = 2 * Real.cos r ^ 2 := by
          have h := Real.sin_sq_add_cos_sq r
          nlinarith [hrsin, h]
        rw [h2, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        rw [Real.sqrt_sq hcos.le]
      refine ⟨?_, ?_⟩
      · rw [hWval, kappa_uproj_chordSurf, (circle_chord_data CI.c CI.start t r).2, ← hsqrt2]
      · rw [hWval]
        exact hk t r ⟨le_of_lt hrpos, by linarith [hrlt, Real.pi_pos]⟩
    refine ⟨δ, hδpos, hδκ, hmain, ?_, ?_⟩
    · -- the first jet family
      intro t j hj
      have hcd := kappa_chart_contDiffAt (W := W) (ρh := ρh) hκ hW hρh hρhv t
      have hsq : ContDiffAt ℝ 12
          (fun σ : ℝ => (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp (t * Complex.I)) 0 := by
        have h1 : ContDiffAt ℝ 12 (fun σ : ℝ => ((Real.sqrt (2 + 2 * σ) : ℝ) : ℂ)) 0 := by
          have h2 : ContDiffAt ℝ 12 (fun σ : ℝ => Real.sqrt (2 + 2 * σ)) 0 :=
            ContDiffAt.sqrt (by fun_prop) (by norm_num)
          have hkey : (fun σ : ℝ => ((Real.sqrt (2 + 2 * σ) : ℝ) : ℂ))
              = Complex.ofRealCLM ∘ fun σ : ℝ => Real.sqrt (2 + 2 * σ) := by
            funext σ
            rw [Function.comp_apply, Complex.ofRealCLM_apply]
          rw [hkey]
          exact (Complex.ofRealCLM.contDiff (n := 12)).comp_contDiffAt 0 h2
        exact h1.mul contDiffAt_const
      have hf : ContDiffAt ℝ 12
          (fun σ : ℝ => Work.RPV.uproj (W 0 t (ρh 0 t σ))
            - (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp (t * Complex.I)) 0 :=
        hcd.1.sub hsq
      have heq : ∀ σ ∈ Set.Ioo (0 - δ) 0,
          (fun σ : ℝ => Work.RPV.uproj (W 0 t (ρh 0 t σ))
            - (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp (t * Complex.I)) σ
          = (fun _ : ℝ => (0 : ℂ)) σ := by
        intro σ hσ
        have hσ' : σ ∈ Set.Ioo (-δ) 0 := by simpa only [zero_sub] using hσ
        show Work.RPV.uproj (W 0 t (ρh 0 t σ))
          - (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp (t * Complex.I) = 0
        rw [(hmain t σ hσ').1]
        simp
      have key := iteratedDeriv_eq_of_eqOn_Ioo_left (x₀ := 0) hδpos
        (f := fun σ : ℝ => Work.RPV.uproj (W 0 t (ρh 0 t σ))
            - (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp (t * Complex.I))
        (g := fun _ : ℝ => (0 : ℂ)) hf contDiffAt_const heq (show j ≤ 12 by omega)
      rw [key]
      simp
    · -- the second jet family
      intro t j hj
      have hcd := kappa_chart_contDiffAt (W := W) (ρh := ρh) hκ hW hρh hρhv t
      have hf : ContDiffAt ℝ 12
          (fun σ : ℝ => (W 0 t (ρh 0 t σ)).1.2
            - (t + Real.pi / 2 + 2 * Real.pi * k)) 0 :=
        hcd.2.sub contDiffAt_const
      have heq : ∀ σ ∈ Set.Ioo (0 - δ) 0,
          (fun σ : ℝ => (W 0 t (ρh 0 t σ)).1.2
            - (t + Real.pi / 2 + 2 * Real.pi * k)) σ = (fun _ : ℝ => (0 : ℝ)) σ := by
        intro σ hσ
        have hσ' : σ ∈ Set.Ioo (-δ) 0 := by simpa only [zero_sub] using hσ
        show (W 0 t (ρh 0 t σ)).1.2 - (t + Real.pi / 2 + 2 * Real.pi * k) = 0
        rw [(hmain t σ hσ').2]
        simp
      have key := iteratedDeriv_eq_of_eqOn_Ioo_left (x₀ := 0) hδpos
        (f := fun σ : ℝ => (W 0 t (ρh 0 t σ)).1.2
            - (t + Real.pi / 2 + 2 * Real.pi * k))
        (g := fun _ : ℝ => (0 : ℝ)) hf contDiffAt_const heq (show j ≤ 12 by omega)
      rw [key]
      simp

end Work.RPB.B5
