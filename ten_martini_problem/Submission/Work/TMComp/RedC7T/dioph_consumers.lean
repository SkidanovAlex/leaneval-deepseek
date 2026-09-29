import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.RedProj.Extract
import Submission.Work.TMComp.RedProj.Part1
import Submission.Work.TMComp.RedProj.part2_compact

/-!
# The two C11 consumers, with C9 restricted to frequencies Diophantine with some constant

`RedProj/Part1.lean` (`reducible_of_dioph_all`) and `RedProj/part2_compact.lean`
(`part2_compact`) use `P_mAnalytic` only through
`RedProj.Extract.joint_analytic_of_mAnalytic`; this file re-proves both with that input
replaced by `P_mAnalytic_dioph` (C9 at frequencies satisfying `DiophBelow α b₀` for some
`b₀ > 0`), reusing all their helper lemmas by import, and assembles `P_Reducibility`.
-/

open LeanEval.Analysis.TenMartini
open MeasureTheory Filter Topology Set intervalIntegral
open scoped NNReal ENNReal

noncomputable section

namespace Work.TMComp.RedProj

open Work.TMContract

/-- **C9 restricted to frequencies Diophantine with some constant.** -/
def P_mAnalytic_dioph : Prop :=
  ∀ (α lam a b : ℝ) (b₀ : ℝ), Irrational α → 0 < b₀ → DiophBelow α b₀ → 0 < lam → lam ≤ 1 →
    a < b → Ioo a b ⊆ amoSpec α lam →
    ∃ (C : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (φ : ℝ → ℝ → ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun p : ℝ × ℝ => C p.1 p.2 i j) (Ioo a b ×ˢ univ)) ∧
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (Ioo a b ×ˢ univ) ∧
      (∀ E x, C E (x + 1) = C E x) ∧ (∀ E x, φ E (x + 1) = φ E x) ∧
      (∀ E ∈ Ioo a b, ∀ x, (C E x).det = 1) ∧
      (∀ E ∈ Ioo a b, HasDegree (C E) 0) ∧
      (∀ E ∈ Ioo a b, ∀ x, C E (x + α) * tmR lam E x = rot (φ E x) * C E x)

/-- The restricted input supplies the invariant section at a Diophantine frequency. -/
theorem joint_analytic_of_mAnalytic_dioph (h9 : P_mAnalytic_dioph) (α lam a b : ℝ) (b₀ : ℝ)
    (hα : Irrational α) (hb₀ : 0 < b₀) (hD : DiophBelow α b₀) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (hab : a < b) (hspec : Ioo a b ⊆ amoSpec α lam) :
    ∃ (C : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (φ : ℝ → ℝ → ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun p : ℝ × ℝ => C p.1 p.2 i j) (Ioo a b ×ˢ univ)) ∧
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (Ioo a b ×ˢ univ) ∧
      (∀ E x, C E (x + 1) = C E x) ∧ (∀ E x, φ E (x + 1) = φ E x) ∧
      (∀ E ∈ Ioo a b, ∀ x, (C E x).det = 1) ∧
      (∀ E ∈ Ioo a b, HasDegree (C E) 0) ∧
      (∀ E ∈ Ioo a b, ∀ x, C E (x + α) * tmR lam E x = rot (φ E x) * C E x) :=
  h9 α lam a b b₀ hα hb₀ hD h0 h1 hab hspec

theorem reducible_of_dioph_all_dioph (h9 : P_mAnalytic_dioph) (α : ℝ) (hα : Irrational α)
    (hD : ∀ b : ℝ, 0 < b → DiophBelow α b) :
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ a b : ℝ, a < b → Set.Ioo a b ⊆ amoSpec α lam →
      Set.Ioo a b ⊆ RedSet α lam := by
  intro lam h0 h1 a b hab hspec E hE
  obtain ⟨Cj, φj, hCjan, hφjan, hCjp, hφjp, hCjdet, hCjdeg, hCjconj⟩ :=
    joint_analytic_of_mAnalytic_dioph h9 α lam a b 1 hα one_pos (hD 1 one_pos) h0 h1 hab hspec
  -- single-energy data extracted from the joint family
  have hfE : AnalyticOnNhd ℝ (fun x : ℝ => (E, x)) Set.univ :=
    analyticOnNhd_const.prod analyticOnNhd_id
  have hEim : Set.MapsTo (fun x : ℝ => (E, x)) Set.univ (Set.Ioo a b ×ˢ Set.univ) :=
    fun x _ => ⟨hE, trivial⟩
  set C : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun x => Cj E x with hCdef
  set φ : ℝ → ℝ := fun x => φj E x with hφdef
  have hCan : ∀ i j, AnalyticOnNhd ℝ (fun x => C x i j) Set.univ :=
    fun i j => (hCjan i j).comp hfE hEim
  have hCp : ∀ x, C (x + 1) = C x := fun x => hCjp E x
  have hCdet : ∀ x, (C x).det = 1 := fun x => hCjdet E hE x
  have hCdeg : HasDegree C 0 := hCjdeg E hE
  have hconj : ∀ x, C (x + α) * tmR lam E x = rot (φ x) * C x := fun x => hCjconj E hE x
  have hφan : AnalyticOnNhd ℝ φ Set.univ := hφjan.comp hfE hEim
  have hφp : ∀ x, φ (x + 1) = φ x := fun x => hφjp E x
  -- complexify in `x` and read off exponential Fourier decay
  have hjoint : AnalyticOnNhd ℝ (fun p : ℝ × ℝ => ((φj p.1 p.2 : ℝ) : ℂ))
      (Set.Ioo a b ×ˢ Set.univ) :=
    (Complex.ofRealCLM.analyticOnNhd (s := Set.univ)).comp hφjan (fun p _ => trivial)
  have hab' : ∀ E' x, (fun p : ℝ × ℝ => ((φj p.1 p.2 : ℝ) : ℂ)) (E', x + 1)
      = (fun p : ℝ × ℝ => ((φj p.1 p.2 : ℝ) : ℂ)) (E', x) :=
    fun E' x => by
      show ((φj E' (x + 1) : ℝ) : ℂ) = ((φj E' x : ℝ) : ℂ)
      rw [hφjp E' x]
  obtain ⟨Δ, ρ, F, _hΔopen, hΔmem, hρ, hFdiff, hFagree, hFper⟩ :=
    complexify_analyticOn (fun p : ℝ × ℝ => ((φj p.1 p.2 : ℝ) : ℂ)) a b E E hE.1 le_rfl hE.2
      hjoint hab'
  have hEΔ : (E : ℂ) ∈ Δ := hΔmem (Set.mem_Icc.mpr ⟨le_rfl, le_rfl⟩)
  have hΦdiff : DifferentiableOn ℂ (fun w : ℂ => F ((E : ℂ), w)) {w : ℂ | |w.im| < ρ} := by
    have hg : DifferentiableOn ℂ (fun w : ℂ => ((E : ℂ), w)) {w : ℂ | |w.im| < ρ} :=
      DifferentiableOn.prodMk (differentiableOn_const (c := (E : ℂ))) differentiableOn_id
    exact DifferentiableOn.comp hFdiff hg (fun w hw => ⟨hEΔ, hw⟩)
  have hΦper : ∀ w : ℂ, |w.im| < ρ → F ((E : ℂ), w + 1) = F ((E : ℂ), w) := by
    intro w hw
    exact hFper ((E : ℂ), w) ⟨hEΔ, hw⟩
  have hΦagree : ∀ x : ℝ, F ((E : ℂ), (x : ℂ)) = ((φ x : ℝ) : ℂ) := by
    intro x
    have h := hFagree E (Set.mem_Icc.mpr ⟨le_rfl, le_rfl⟩) x
    simpa using h
  obtain ⟨C₁, η₁, hη₁, hbound⟩ :=
    fourierCoeff_decay_of_strip (fun x => ((φ x : ℝ) : ℂ)) (fun w => F ((E : ℂ), w)) ρ hρ
      hΦdiff hΦper hΦagree
  -- the Diophantine lower bound
  obtain ⟨C₂, hC₂, hbound₂⟩ := exp_lower_of_diophBelow α (η₁ / 4) hα (by positivity)
    (hD (η₁ / 4) (by positivity)) (η₁ / 2) (by linarith)
  set C₁' : ℝ := max C₁ 0 + 1 with hC₁'def
  have hC₁'pos : 0 < C₁' := by
    have := le_max_right C₁ 0
    simp only [hC₁'def]
    linarith
  have hC₁'le : C₁ ≤ C₁' := by
    simp only [hC₁'def]
    linarith [le_max_left C₁ 0]
  have hbound' : ∀ k : ℤ, k ≠ 0 →
      ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun x => ((φ x : ℝ) : ℂ)) k‖
        ≤ (C₁' / C₂) * ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖
            * Real.exp (-((η₁ / 2) * |(k : ℝ)|)) := by
    intro k hk
    have h2 : C₂ * Real.exp (-((η₁ / 2) * |(k : ℝ)|))
        ≤ ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖ := hbound₂ k hk
    have he2 : 0 < Real.exp (-((η₁ / 2) * |(k : ℝ)|)) := Real.exp_pos _
    have hsplit : Real.exp (-(η₁ * |(k : ℝ)|))
        = Real.exp (-((η₁ / 2) * |(k : ℝ)|)) * Real.exp (-((η₁ / 2) * |(k : ℝ)|)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h4 : Real.exp (-((η₁ / 2) * |(k : ℝ)|))
        ≤ ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖ / C₂ := by
      rw [le_div_iff₀ hC₂]
      linarith [h2]
    have hC₁'eq : (C₁' / C₂) * C₂ = C₁' := div_mul_cancel₀ _ hC₂.ne'
    calc ‖fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) (fun x => ((φ x : ℝ) : ℂ)) k‖
        ≤ C₁ * Real.exp (-(η₁ * |(k : ℝ)|)) := hbound k
      _ ≤ C₁' * Real.exp (-(η₁ * |(k : ℝ)|)) := by
          nlinarith [hC₁'le, Real.exp_pos (-(η₁ * |(k : ℝ)|))]
      _ = C₁' * (Real.exp (-((η₁ / 2) * |(k : ℝ)|)) * Real.exp (-((η₁ / 2) * |(k : ℝ)|))) := by
          rw [hsplit]
      _ ≤ C₁' * ((‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖ / C₂)
            * Real.exp (-((η₁ / 2) * |(k : ℝ)|))) := by
          apply mul_le_mul_of_nonneg_left _ hC₁'pos.le
          nlinarith [h4, he2]
      _ = (C₁' / C₂) * ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖
            * Real.exp (-((η₁ / 2) * |(k : ℝ)|)) := by ring

  -- solve the cohomological equation by its Fourier series
  have hcont : Continuous fun x => ((φ x : ℝ) : ℂ) := Complex.continuous_ofReal.comp hφan.continuous
  have hper2 : ∀ x, (fun x => ((φ x : ℝ) : ℂ)) (x + 1) = (fun x => ((φ x : ℝ) : ℂ)) x := by
    intro x
    show ((φ (x + 1) : ℝ) : ℂ) = ((φ x : ℝ) : ℂ)
    rw [hφp x]
  obtain ⟨ψC, hψCp, hψCan, hψCeq⟩ :=
    analytic_coboundary_of_decay α hα (fun x => ((φ x : ℝ) : ℂ)) hcont hper2 (η₁ / 2)
      (by positivity) (C₁' / C₂) (by positivity) hbound'
  have hint : ((∫ t in (0 : ℝ)..1, φ t : ℝ) : ℂ) = ∫ t in (0 : ℝ)..1, ((φ t : ℝ) : ℂ) :=
    (ContinuousLinearMap.intervalIntegral_comp_comm Complex.ofRealCLM
      (hφan.continuous.intervalIntegrable _ _)).symm
  obtain ⟨ψ, hψp, hψan, hψeq⟩ :=
    exists_real_coboundary α (∫ t in (0 : ℝ)..1, φ t) (φ := φ) hψCp hψCan
      (fun x => by
        have h := hψCeq x
        rw [← hint] at h
        exact h)
  exact mem_RedSet_of_coboundary α lam E C φ ψ hCan hCp hCdet hCdeg hconj hψan hψp hψeq


theorem part2_compact_dioph
    (hhol : ∀ (F : ℂ × ℂ → ℂ) (Δ : Set ℂ) (ρ : ℝ), IsOpen Δ → 0 < ρ →
      DifferentiableOn ℂ F {p : ℂ × ℂ | p.1 ∈ Δ ∧ |p.2.im| < ρ} → ∀ k : ℤ,
      DifferentiableOn ℂ (fun z : ℂ => ∫ x in (0 : ℝ)..1,
        F (z, (x : ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ)))) Δ)
    (hcob : ∀ (α : ℝ), Irrational α → ∀ (φ : ℝ → ℝ), Continuous φ →
      (∀ x, φ (x + 1) = φ x) → ∀ (O : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun x => O x i j) Set.univ) →
      (∀ x, O (x + 1) = O x) → (∀ x, (O x).det = 1) →
      (∀ x, O (x + α) * Work.TMContract.rot (φ x) = Work.TMContract.rot c * O x) →
      ∃ ψ : ℝ → ℝ, (∀ x, ψ (x + 1) = ψ x) ∧ AnalyticOnNhd ℝ ψ Set.univ ∧
        ∀ x, φ x - (∫ t in (0 : ℝ)..1, φ t) = ψ (x + α) - ψ x)
    (h9 : P_mAnalytic_dioph) (h10 : Work.TMContract.P_RealCartan)
    (α b₀ lam : ℝ) (hα : Irrational α) (hD : Work.TMContract.DiophBelow α b₀)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (a b : ℝ) (hab : a < b)
    (hspec : Set.Ioo a b ⊆ Work.TMContract.amoSpec α lam)
    (c d : ℝ) (hac : a < c) (hcd : c ≤ d) (hdb : d < b) :
    MeasureTheory.volume (Work.TMContract.RedSet α lam ∩ Set.Icc c d) = 0 ∨
      ∃ c' d' : ℝ, c' < d' ∧ Set.Ioo c' d' ⊆ Work.TMContract.RedSet α lam ∩ Set.Ioo a b 
:= by
  classical
  have hb0 : 0 < b₀ := pos_of_diophBelow α b₀ hD
  obtain ⟨Cj, φj, hCjan, hφjan, hCjp, hφjp, hCjdet, hCjdeg, hCjconj⟩ :=
    joint_analytic_of_mAnalytic_dioph h9 α lam a b b₀ hα hb0 hD h0 h1 hab hspec
  set Φ : ℝ × ℝ → ℂ := fun p => ((φj p.1 p.2 : ℝ) : ℂ) with hΦdef
  have hΦan : AnalyticOnNhd ℝ Φ (Set.Ioo a b ×ˢ Set.univ) :=
    (Complex.ofRealCLM.analyticOnNhd (s := Set.univ)).comp hφjan (fun p _ => trivial)
  have hΦper : ∀ E x : ℝ, Φ (E, x + 1) = Φ (E, x) := by
    intro E x
    show ((φj E (x + 1) : ℝ) : ℂ) = ((φj E x : ℝ) : ℂ)
    rw [hφjp E x]
  set ε : ℝ := min ((c - a) / 2) ((b - d) / 2) with hεdef
  have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
  have hC1a : a < c - ε := by
    have h : ε ≤ (c - a) / 2 := by rw [hεdef]; exact min_le_left _ _
    linarith
  have hD1b : d + ε < b := by
    have h : ε ≤ (b - d) / 2 := by rw [hεdef]; exact min_le_right _ _
    linarith
  have hCD : c - ε ≤ d + ε := by linarith
  obtain ⟨Δ₀, ρ₀, F₀, hΔ₀open, hΔ₀mem, hρ₀pos, hF₀diff, hF₀ag, hF₀per⟩ :=
    complexify_analyticOn Φ a b (c - ε) (d + ε) hC1a hCD hD1b hΦan hΦper
  set Δ : Set ℂ := Δ₀ ∩ {z : ℂ | z.re ∈ Set.Ioo (c - ε) (d + ε)} with hΔdef
  have hΔopen : IsOpen Δ := hΔ₀open.inter (isOpen_Ioo.preimage Complex.continuous_re)
  have hΔsub₀ : Δ ⊆ Δ₀ := Set.inter_subset_left
  have hIcc_cd : (Set.Icc c d : Set ℝ) ⊆ Set.Icc (c - ε) (d + ε) :=
    Set.Icc_subset_Icc (by linarith) (by linarith)
  have hcdmem : ∀ E ∈ Set.Icc c d, (E:ℂ) ∈ Δ := by
    intro E hE
    exact ⟨hΔ₀mem (hIcc_cd hE), by
      simp only [Set.mem_setOf_eq, Complex.ofReal_re]
      exact ⟨by linarith [hE.1], by linarith [hE.2]⟩⟩
  have hΔab : ∀ x : ℝ, (x:ℂ) ∈ Δ → x ∈ Set.Ioo a b := by
    intro x hx
    have h : c - ε < x ∧ x < d + ε := by
      simpa only [Set.mem_Ioo, Set.mem_setOf_eq, Complex.ofReal_re] using hx.2
    exact ⟨by linarith [hC1a, h.1], by linarith [hD1b, h.2]⟩
  set fn : ℕ → ℂ → ℂ := fun n z => ∫ x in (0:ℝ)..1,
      F₀ (z, (x:ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((kEnum n : ℤ) : ℂ) * (x : ℂ))) with hfn
  have hfn_diff : ∀ n, DifferentiableOn ℂ (fn n) Δ := by
    intro n
    exact hhol F₀ Δ ρ₀ hΔopen hρ₀pos
      (hF₀diff.mono (fun p hp => ⟨hΔsub₀ hp.1, hp.2⟩)) (kEnum n)
  set w : ℕ → ℝ := fun n => ‖Complex.exp (2 * Real.pi * (kEnum n : ℝ) * α * Complex.I) - 1‖ with hw
  set sd : ℕ → ℝ := fun n => (n : ℝ) + 1 with hsd
  have hwpos : ∀ n, 0 < w n := by
    intro n
    rw [hw]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (exp_two_pi_mul_I_mul_ne_one α hα (kEnum n) (kEnum_ne_zero n)))
  have hspos : ∀ n, 0 < sd n := by intro n; rw [hsd]; positivity
  have hw' : ∀ n : ℕ, w n
      = ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (kEnum n : ℂ) * (α : ℂ)) - 1‖ := by
    intro n
    rw [hw]
    exact congrArg (fun z : ℂ => ‖z - 1‖) (exp_factor_eq α (kEnum n))
  obtain ⟨Cdioph, hCdiophpos, hCdioph⟩ :=
    Part2.ExpLowerDioph α b₀ hα hb0 hD (b₀ + 1) (by linarith)
  have hwlower : ∀ n : ℕ, Cdioph * Real.exp (-((b₀ + 1) * ((n : ℝ) + 1))) ≤ w n := by
    intro n
    rw [hw]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hCdiophpos.le)
      (hCdioph (kEnum n) (kEnum_ne_zero n))
    apply Real.exp_le_exp.mpr
    have h1 : |((kEnum n : ℤ) : ℝ)| = ((n / 2 + 1 : ℕ) : ℝ) := by
      rw [abs_intCast_eq, natAbs_kEnum]
    have h2 : ((n / 2 + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
      have h3 : n / 2 + 1 ≤ n + 1 := by omega
      exact_mod_cast h3
    rw [h1]
    nlinarith [hb0, h2]
  have hbound : ∀ K ⊆ Δ, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K,
      ‖fn n z‖ ≤ w n * Real.exp (M * sd n) := by
    intro K hKΔ hKc
    by_cases hKne : K.Nonempty
    swap
    · exact ⟨0, fun n z hz => absurd ⟨z, hz⟩ hKne⟩
    · have htube : K ×ˢ (Complex.ofReal '' (Set.Icc (0:ℝ) 1)) ⊆
          {p : ℂ × ℂ | p.1 ∈ Δ₀ ∧ |p.2.im| < ρ₀} := by
        intro p hp
        refine ⟨hΔsub₀ (hKΔ hp.1), ?_⟩
        obtain ⟨t, ht, hpt⟩ := hp.2
        rw [← hpt]
        simpa only [Complex.ofReal_im, abs_zero] using hρ₀pos
      obtain ⟨M₀, hM₀⟩ := (hKc.prod (isCompact_Icc.image Complex.continuous_ofReal)).exists_bound_of_continuousOn
        ((hF₀diff.mono htube).continuousOn)
      set M₁ : ℝ := max M₀ 0 with hM₁
      have hM₁nn : 0 ≤ M₁ := le_max_right _ _
      refine ⟨(b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1, fun n z hz => ?_⟩
      have hsup : ∀ x ∈ Set.uIoc (0:ℝ) 1,
          ‖F₀ (z, (x:ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((kEnum n : ℤ) : ℂ) * (x : ℂ)))‖ ≤ M₁ := by
        intro x hx
        have hxI : x ∈ Set.Icc (0:ℝ) 1 := by
          have h := Set.uIoc_subset_uIcc hx
          rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h
        rw [norm_mul]
        have hC : ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((kEnum n : ℤ) : ℂ) * (x : ℂ)))‖ = 1 := by
          rw [show -(2 * (Real.pi : ℂ) * Complex.I * ((kEnum n : ℤ) : ℂ) * (x : ℂ))
                = ((-(2 * Real.pi * (kEnum n : ℝ) * x) : ℝ) : ℂ) * Complex.I by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _
        rw [hC, mul_one]
        exact le_trans (hM₀ _ ⟨hz, x, hxI, rfl⟩) (le_max_left _ _)
      have hnorm : ‖fn n z‖ ≤ M₁ := by
        calc ‖fn n z‖ = ‖∫ x in (0:ℝ)..1, F₀ (z, (x:ℂ)) *
              Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((kEnum n : ℤ) : ℂ) * (x : ℂ)))‖ := rfl
          _ ≤ M₁ * |(1:ℝ) - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hsup
          _ = M₁ := by norm_num
      have hlogle : Real.log (M₁ / Cdioph) ≤ (b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1) := by
        linarith [le_max_right (0:ℝ) (Real.log (M₁ / Cdioph))]
      have hnn : 0 ≤ (b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1) := by
        have := le_max_left (0:ℝ) (Real.log (M₁ / Cdioph)); linarith
      have hargle : Real.log (M₁ / Cdioph)
          ≤ ((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1)) * ((n : ℝ) + 1) := by
        have hn1 : (1:ℝ) ≤ (n : ℝ) + 1 := by
          have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
          linarith
        calc Real.log (M₁ / Cdioph)
            ≤ (b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1) := hlogle
          _ = ((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1)) * 1 := by ring
          _ ≤ ((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1)) * ((n : ℝ) + 1) :=
              mul_le_mul_of_nonneg_left hn1 hnn
      have hfin : M₁ ≤ Cdioph * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1))
          * ((n : ℝ) + 1)) := by
        rcases eq_or_lt_of_le hM₁nn with h0 | hpos
        · rw [← h0]
          exact mul_nonneg hCdiophpos.le (Real.exp_pos _).le
        · have hdiv : 0 < M₁ / Cdioph := div_pos hpos hCdiophpos
          calc M₁ = Cdioph * (M₁ / Cdioph) := by field_simp
            _ ≤ Cdioph * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1))
                  * ((n : ℝ) + 1)) := by
                apply mul_le_mul_of_nonneg_left _ hCdiophpos.le
                have h1 : Real.exp (Real.log (M₁ / Cdioph))
                    ≤ Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1))
                        * ((n : ℝ) + 1)) := Real.exp_le_exp.mpr hargle
                rwa [Real.exp_log hdiv] at h1
      have hstep : Cdioph * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1))
            * ((n : ℝ) + 1))
          ≤ w n * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1) * ((n : ℝ) + 1)) := by
        have hw' := hwlower n
        have hexp : Cdioph * Real.exp (-((b₀ + 1) * ((n : ℝ) + 1)))
              * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1) * ((n : ℝ) + 1))
            = Cdioph * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1))
                * ((n : ℝ) + 1)) := by
          rw [mul_assoc, ← Real.exp_add,
            show -( (b₀ + 1) * ((n : ℝ) + 1))
                + ((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1) * ((n : ℝ) + 1)
              = ((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1)) * ((n : ℝ) + 1) by ring]
        rw [← hexp]
        exact mul_le_mul_of_nonneg_right hw' (Real.exp_pos _).le
      have hfin2 : w n * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1) * ((n : ℝ) + 1))
          = w n * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1) * sd n) := by rw [hsd]
      calc ‖fn n z‖ ≤ M₁ := hnorm
        _ ≤ Cdioph * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1 - (b₀ + 1))
              * ((n : ℝ) + 1)) := hfin
        _ ≤ w n * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1) * ((n : ℝ) + 1)) := hstep
        _ = w n * Real.exp (((b₀ + 1) + max 0 (Real.log (M₁ / Cdioph)) + 1) * sd n) := hfin2
  have hfval : ∀ (x : ℝ) (hx : (x:ℂ) ∈ Δ) (n : ℕ),
      fn n x = fourierCoeffOn (show (0:ℝ) < 1 by norm_num) (fun y : ℝ => ((φj x y : ℝ) : ℂ)) (kEnum n) := by
    intro x hx n
    have hxIcc : x ∈ Set.Icc (c - ε) (d + ε) := by
      have h : c - ε < x ∧ x < d + ε := by
        simpa only [Set.mem_Ioo, Set.mem_setOf_eq, Complex.ofReal_re] using hx.2
      exact ⟨le_of_lt h.1, le_of_lt h.2⟩
    rw [hfn, fcoef_eq_int]
    apply intervalIntegral.integral_congr
    intro t _
    show F₀ ((x:ℂ), (t:ℂ)) * _ = ((φj x t : ℝ) : ℂ) * ek (kEnum n) t
    rw [hF₀ag x hxIcc t]
    rfl
  rcases h10 Δ hΔopen fn w sd hfn_diff hwpos hspos hbound with hA0 | ⟨c', d', hc'd', hAint⟩
  · left
    have hnull : (RedSet α lam ∩ Set.Icc c d : Set ℝ) ⊆
        {x : ℝ | (x:ℂ) ∈ Δ ∧ ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in atTop, ‖fn n x‖ ≤ w n * Real.exp (-(η * sd n))} := by
      intro x hx
      obtain ⟨hxred, hxIcc⟩ := hx
      have hxΔ : (x:ℂ) ∈ Δ := hcdmem x hxIcc
      refine ⟨hxΔ, ?_⟩
      have hxab : x ∈ Set.Ioo a b := ⟨lt_of_lt_of_le hac hxIcc.1, lt_of_le_of_lt hxIcc.2 hdb⟩
      set Cl : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun y => Cj x y with hCldef
      set φl : ℝ → ℝ := fun y => φj x y with hφldef
      have hfE : AnalyticOnNhd ℝ (fun y : ℝ => (x, y)) Set.univ :=
        analyticOnNhd_const.prod analyticOnNhd_id
      have hEim : Set.MapsTo (fun y : ℝ => (x, y)) Set.univ (Set.Ioo a b ×ˢ Set.univ) :=
        fun y _ => ⟨hxab, trivial⟩
      obtain ⟨C₀, η₀, hη₀, hbnd⟩ := fourier_bound_of_mem_RedSet hcob α lam x a b hα hxab
        Cl φl (fun i j => (hCjan i j).comp hfE hEim) (fun y => hCjp x y)
        (fun y => hCjdet x hxab y) (fun y => hCjconj x hxab y)
        (hφjan.comp hfE hEim) (fun y => hφjp x y) hxred
      have hbndc : ∀ k : ℤ, k ≠ 0 →
          ‖fourierCoeffOn (show (0:ℝ) < 1 by norm_num) (fun y : ℝ => ((φl y : ℝ) : ℂ)) k‖
            ≤ max C₀ 0 * ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (α : ℂ)) - 1‖
                * Real.exp (-(η₀ * |(k : ℝ)|)) := by
        intro k hk
        exact (hbnd k hk).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (norm_nonneg _))
          (Real.exp_pos _).le)
      refine ⟨(η₀ / 2) / 2, by positivity, ?_⟩
      filter_upwards [eventually_const_mul_exp_le (max C₀ 0) (η₀ / 2) (by positivity)] with n hn
      have hmain : ‖fn n x‖ ≤ max C₀ 0 * w n * Real.exp (-((η₀ / 2) * ((n : ℝ) + 1))) := by
        have hk := hbndc (kEnum n) (kEnum_ne_zero n)
        rw [← hw' n] at hk
        rw [hfval x hxΔ n]
        refine hk.trans ?_
        have h2 : ((n : ℝ) + 1) / 2 ≤ |((kEnum n : ℤ) : ℝ)| := by
          rw [abs_intCast_eq, natAbs_kEnum]
          have h4 : n + 1 ≤ 2 * (n / 2 + 1) := by omega
          have h5 : (n : ℝ) + 1 ≤ 2 * ((n / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast h4
          linarith
        apply mul_le_mul_of_nonneg_left _ (by have h2' := (hwpos n).le; positivity)
        apply Real.exp_le_exp.mpr
        nlinarith [h2, hη₀]
      calc ‖fn n x‖ ≤ max C₀ 0 * w n * Real.exp (-((η₀ / 2) * ((n : ℝ) + 1))) := hmain
        _ = w n * (max C₀ 0 * Real.exp (-((η₀ / 2) * ((n : ℝ) + 1)))) := by ring
        _ ≤ w n * Real.exp (-(((η₀ / 2) / 2) * ((n : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left hn (le_of_lt (hwpos n))
        _ = w n * Real.exp (-(((η₀ / 2) / 2) * sd n)) := by simp only [hsd]
    refine le_antisymm ?_ (by simp)
    calc MeasureTheory.volume (RedSet α lam ∩ Set.Icc c d)
        ≤ MeasureTheory.volume {x : ℝ | (x:ℂ) ∈ Δ ∧
            ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in atTop, ‖fn n x‖ ≤ w n * Real.exp (-(η * sd n))} :=
          MeasureTheory.measure_mono hnull
      _ = 0 := hA0
  · right
    refine ⟨c', d', hc'd', ?_⟩
    intro x hx
    have hxA : (x:ℂ) ∈ Δ ∧ ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in atTop, ‖fn n x‖ ≤ w n * Real.exp (-(η * sd n)) := hAint hx
    have hxΔ : (x:ℂ) ∈ Δ := hxA.1
    refine ⟨?_, hΔab x hxΔ⟩
    obtain ⟨η, hηpos, hev⟩ := hxA.2
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    have hxab : x ∈ Set.Ioo a b := hΔab x hxΔ
    set C : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun y => Cj x y with hCdef
    set φ : ℝ → ℝ := fun y => φj x y with hφdef
    have hfE : AnalyticOnNhd ℝ (fun y : ℝ => (x, y)) Set.univ :=
      analyticOnNhd_const.prod analyticOnNhd_id
    have hEim : Set.MapsTo (fun y : ℝ => (x, y)) Set.univ (Set.Ioo a b ×ˢ Set.univ) :=
      fun y _ => ⟨hxab, trivial⟩
    have hCan : ∀ i j, AnalyticOnNhd ℝ (fun y => C y i j) Set.univ :=
      fun i j => (hCjan i j).comp hfE hEim
    have hCp : ∀ y, C (y + 1) = C y := by intro y; rw [hCdef]; exact hCjp x y
    have hCdet : ∀ y, (C y).det = 1 := by intro y; rw [hCdef]; exact hCjdet x hxab y
    have hCdeg : HasDegree C 0 := by rw [hCdef]; exact hCjdeg x hxab
    have hconj : ∀ y, C (y + α) * tmR lam x y = rot (φ y) * C y := by
      intro y; rw [hCdef, hφdef]; exact hCjconj x hxab y
    have hφan : AnalyticOnNhd ℝ φ Set.univ := by rw [hφdef]; exact hφjan.comp hfE hEim
    have hφp : ∀ y, φ (y + 1) = φ y := by intro y; rw [hφdef]; exact hφjp x y
    have hbdlarge : ∀ k : ℤ, ((N : ℤ) + 1) ≤ |k| →
        ‖fourierCoeffOn (show (0:ℝ) < 1 by norm_num) (fun y : ℝ => ((φ y : ℝ) : ℂ)) k‖
          ≤ ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖ * Real.exp (-(η * |(k : ℝ)|)) := by
      intro k hk
      have hk0 : k ≠ 0 := by
        intro h; rw [h] at hk; simp at hk; omega
      obtain ⟨n, hn⟩ := kEnum_surj k hk0
      have hnN : N ≤ n := by
        have h1 : (kEnum n).natAbs = n / 2 + 1 := natAbs_kEnum n
        rw [hn] at h1
        have h2 : ((N : ℤ) + 1) ≤ (k.natAbs : ℤ) := by
          have h3 : |k| = (k.natAbs : ℤ) := Int.abs_eq_natAbs k
          rw [h3] at hk; exact hk
        have h4 : (N : ℤ) + 1 ≤ ((n / 2 + 1 : ℕ) : ℤ) := by rw [← h1]; exact h2
        omega
      have h := hN n hnN
      rw [hfval x hxΔ n, hn] at h
      have hw'' : w n = ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖ := by
        simp only [hw, hn, exp_factor_eq]
      simp only [hw'', hsd] at h
      refine h.trans ?_
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      have h2 : |(k : ℝ)| ≤ (n : ℝ) + 1 := by
        have h3 : (k.natAbs : ℝ) = ((n / 2 + 1 : ℕ) : ℝ) := by
          rw [← hn]
          exact_mod_cast (natAbs_kEnum n)
        rw [abs_intCast_eq, h3]
        have h4 : n / 2 + 1 ≤ n + 1 := by omega
        exact_mod_cast h4
      have h3 : η * |(k : ℝ)| ≤ η * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_left h2 hηpos.le
      linarith
    obtain ⟨C₁, hC₁pos, hC₁⟩ := bound_all_of_bound_large
      (fun k : ℤ => ‖fourierCoeffOn (show (0:ℝ) < 1 by norm_num) (fun y : ℝ => ((φ y : ℝ) : ℂ)) k‖)
      (fun k : ℤ => if k = 0 then 1 else ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖)
      η hηpos (fun k => by
        by_cases hk : k = 0
        · simp [hk]
        · simp only [if_neg hk]
          exact norm_pos_iff.mpr (sub_ne_zero.mpr (exp_two_pi_mul_I_mul_ne_one α hα k hk)))
      ((N : ℤ) + 1) (by
        intro k hk
        have hk0 : k ≠ 0 := by intro h; rw [h] at hk; simp at hk; omega
        simpa [if_neg hk0] using hbdlarge k hk)
    have hcont : Continuous (fun y : ℝ => ((φ y : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hφan.continuous
    have hper2 : ∀ y : ℝ, (fun y : ℝ => ((φ y : ℝ) : ℂ)) (y + 1) = (fun y : ℝ => ((φ y : ℝ) : ℂ)) y := by
      intro y
      show ((φ (y + 1) : ℝ) : ℂ) = ((φ y : ℝ) : ℂ)
      rw [hφp y]
    obtain ⟨ψC, hψCp, hψCan, hψCeq⟩ := analytic_coboundary_of_decay α hα
      (fun y : ℝ => ((φ y : ℝ) : ℂ)) hcont hper2 η hηpos C₁ hC₁pos
      (fun k hk => by simpa only [if_neg hk, mul_assoc] using hC₁ k)
    obtain ⟨ψ, hψp, hψan, hψeq⟩ := exists_real_coboundary α (∫ t in (0 : ℝ)..1, φ t) (φ := φ)
      hψCp hψCan (fun y => by
        have h := hψCeq y
        have hint : ((∫ t in (0 : ℝ)..1, φ t : ℝ) : ℂ) = ∫ t in (0 : ℝ)..1, ((φ t : ℝ) : ℂ) :=
          (ContinuousLinearMap.intervalIntegral_comp_comm Complex.ofRealCLM
            (hφan.continuous.intervalIntegrable _ _)).symm
        rw [← hint] at h
        exact h)
    exact mem_RedSet_of_coboundary α lam x C φ ψ hCan hCp hCdet hCdeg hconj hψan hψp hψeq


/-- Part 2 of `P_Reducibility`: the compact dichotomy of `part2_compact_dioph` on all of
`(a,b)`. -/
theorem part2_of_dioph
    (hhol : ∀ (F : ℂ × ℂ → ℂ) (Δ : Set ℂ) (ρ : ℝ), IsOpen Δ → 0 < ρ →
      DifferentiableOn ℂ F {p : ℂ × ℂ | p.1 ∈ Δ ∧ |p.2.im| < ρ} → ∀ k : ℤ,
      DifferentiableOn ℂ (fun z : ℂ => ∫ x in (0 : ℝ)..1,
        F (z, (x : ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ)))) Δ)
    (hcob : ∀ (α : ℝ), Irrational α → ∀ (φ : ℝ → ℝ), Continuous φ →
      (∀ x, φ (x + 1) = φ x) → ∀ (O : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun x => O x i j) Set.univ) →
      (∀ x, O (x + 1) = O x) → (∀ x, (O x).det = 1) →
      (∀ x, O (x + α) * rot (φ x) = rot c * O x) →
      ∃ ψ : ℝ → ℝ, (∀ x, ψ (x + 1) = ψ x) ∧ AnalyticOnNhd ℝ ψ Set.univ ∧
        ∀ x, φ x - (∫ t in (0 : ℝ)..1, φ t) = ψ (x + α) - ψ x)
    (h9 : P_mAnalytic_dioph) (h10 : P_RealCartan) :
    ∀ (α b₀ : ℝ), Irrational α → DiophBelow α b₀ → ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      ∀ a b : ℝ, a < b → Set.Ioo a b ⊆ amoSpec α lam →
        volume (RedSet α lam ∩ Set.Ioo a b) = 0 ∨
          ∃ c d : ℝ, c < d ∧ Set.Ioo c d ⊆ RedSet α lam ∩ Set.Ioo a b := by
  intro α b₀ hα hD lam h0 h1 a b hab hspec
  by_cases hcase : ∃ c d : ℝ, a < c ∧ c ≤ d ∧ d < b ∧
      (∃ c' d' : ℝ, c' < d' ∧ Set.Ioo c' d' ⊆ RedSet α lam ∩ Set.Ioo a b)
  · refine Or.inr ?_
    obtain ⟨c, d, _, _, _, c', d', hlt, hsub⟩ := hcase
    exact ⟨c', d', hlt, hsub⟩
  · refine Or.inl ?_
    refine RedProj.volume_eq_zero_of_compact_null (RedSet α lam) a b hab ?_
    intro c d hac hcd hdb
    rcases part2_compact_dioph hhol hcob h9 h10 α b₀ lam hα hD h0 h1 a b hab hspec
      c d hac hcd hdb with h | ⟨c', d', hlt, hsub⟩
    · exact h
    · exact absurd ⟨c, d, hac, hcd, hdb, ⟨c', d', hlt, hsub⟩⟩ hcase

/-- `P_Reducibility` (Diophantine-restricted C9) and the two isolated analytic facts. -/
theorem prove_Reducibility_of_dioph
    (hhol : ∀ (F : ℂ × ℂ → ℂ) (Δ : Set ℂ) (ρ : ℝ), IsOpen Δ → 0 < ρ →
      DifferentiableOn ℂ F {p : ℂ × ℂ | p.1 ∈ Δ ∧ |p.2.im| < ρ} → ∀ k : ℤ,
      DifferentiableOn ℂ (fun z : ℂ => ∫ x in (0 : ℝ)..1,
        F (z, (x : ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ)))) Δ)
    (hcob : ∀ (α : ℝ), Irrational α → ∀ (φ : ℝ → ℝ), Continuous φ →
      (∀ x, φ (x + 1) = φ x) → ∀ (O : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun x => O x i j) Set.univ) →
      (∀ x, O (x + 1) = O x) → (∀ x, (O x).det = 1) →
      (∀ x, O (x + α) * rot (φ x) = rot c * O x) →
      ∃ ψ : ℝ → ℝ, (∀ x, ψ (x + 1) = ψ x) ∧ AnalyticOnNhd ℝ ψ Set.univ ∧
        ∀ x, φ x - (∫ t in (0 : ℝ)..1, φ t) = ψ (x + α) - ψ x)
    (h9 : P_mAnalytic_dioph) (h10 : P_RealCartan) : P_Reducibility :=
  ⟨fun α hα hD => reducible_of_dioph_all_dioph h9 α hα hD,
    part2_of_dioph hhol hcob h9 h10⟩

end Work.TMComp.RedProj
