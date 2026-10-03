/-
# Clash-free copy of the deviation-sum estimate for the `ssu` assembly

`Submission/Work/KMTPlan/A6/ssuDeviationSum.lean` (proved, sorry-free) declares the public
auxiliary names `Work.KMTPlan.A6.norm_fourier_one` and
`Work.KMTPlan.A6.diffFreqs_subset_iwArithFreqs`, which are *also* declared by
`Submission.Work.KMTPlan.A6.SymSeq_TmKernel_cont` and by several `KMTAreas/A7` modules.  Since the
`ssu` assembly must import both `KMTAreas.A7.coeff_arithSymb_mul_iwSymbol` (through `ssuCollapse`)
and this estimate, the names would collide in the same environment.

This module is a *verbatim copy* of that file with every auxiliary renamed with the prefix
`ssuDev_` (so that it can coexist with the other modules); the main statement is unchanged and is
exported under the name `Work.KMTPlan.A6.ssuDeviationSumSelf`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.SsuDefs

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.KMTAreas.A7

set_option maxHeartbeats 2000000

noncomputable section

/-! ## Elementary facts about the circle characters -/

/-- The circle characters have modulus one. -/
theorem ssuDev_norm_fourier_one (j : ℤ) (β : SsuC) : ‖fourier (T := 1) j β‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

/-- Hölder's inequality in the form `ℓ¹ ⊂ ℓ² · ℓ²` on `ℤ`. -/
theorem ssuDev_eLpNorm_mul_le_two (u v : ℤ → ℂ) :
    eLpNorm (fun x : ℤ => u x * v x) 1 Measure.count
      ≤ eLpNorm u 2 Measure.count * eLpNorm v 2 Measure.count := by
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
    (μ := Measure.count) (f := u) (g := v) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := 1)
    (fun a b : ℂ => a * b) 1 continuous_mul
    (measurable_of_countable u).aestronglyMeasurable
    (measurable_of_countable v).aestronglyMeasurable
    (by filter_upwards with x; rw [norm_mul]; norm_num)
    (hpqr := (inferInstance : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1))
  simpa using h

/-! ## The per-pair deviation of the windowed arithmetic mean -/

/-- `diffFreqs ρ l` is contained in the IW arithmetic frequency set `iwArithFreqs ρ l`. -/
theorem ssuDev_diffFreqs_subset_iwArithFreqs (ρ : ℝ) (l : ℕ) :
    diffFreqs ρ l ⊆ iwArithFreqs ρ l := by
  intro α hα
  rw [diffFreqs] at hα
  by_cases h : l = 0
  · simpa [h] using hα
  · simp only [h, if_false] at hα
    exact (Finset.mem_sdiff.mp hα).1

/-- **Deviation of the band coefficient of the halved average from half the arithmetic mean.**
For `α ∈ diffFreqs ρ l₁`, `β ∈ diffFreqs ρ l₂` with killing denominators `q₁, q₂` whose product is
bounded by `Qb`, the windowed mean `ssuCoeff` differs from `(1/2) mZ` by at most `3 Qb / N`. -/
theorem ssuDev_ssuCoeff_deviation
    (P : Polynomial ℤ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (l₁ l₂ N : ℕ) (α β : SsuC)
    (Qb : ℝ) (hN : 1 ≤ N) (hQb : 0 ≤ Qb)
    (hα : α ∈ diffFreqs ρ l₁) (hβ : β ∈ diffFreqs ρ l₂)
    (hper : ∀ (q₁ q₂ : ℕ), q₁ ∈ iwP ρ l₁ → q₂ ∈ iwP ρ l₂ →
      q₁ • α = 0 → q₂ • β = 0 → ((q₁ * q₂ : ℕ) : ℝ) ≤ Qb) :
    ‖ssuCoeff P N α β
        - (2 : ℂ)⁻¹ * mZ P (arithQ ρ (max l₁ l₂)) α β‖
      ≤ 3 * Qb / (N : ℝ) := by
  obtain ⟨q₁, hq₁, hq₁α⟩ := mem_iwArithFreqs.mp (ssuDev_diffFreqs_subset_iwArithFreqs ρ l₁ hα)
  obtain ⟨q₂, hq₂, hq₂β⟩ := mem_iwArithFreqs.mp (ssuDev_diffFreqs_subset_iwArithFreqs ρ l₂ hβ)
  have hq₁0 : 0 < q₁ := pos_of_mem_iwP hq₁
  have hq₂0 : 0 < q₂ := pos_of_mem_iwP hq₂
  have hQ : 0 < q₁ * q₂ := Nat.mul_pos hq₁0 hq₂0
  have hQα : (q₁ * q₂) • α = 0 := by
    rw [mul_smul, smul_comm q₁ q₂ α, hq₁α, smul_zero]
  have hQβ : (q₁ * q₂) • β = 0 := by
    rw [mul_smul, hq₂β, smul_zero]
  have hperw : ∀ n : ℤ, Work.A7.arithW P α β (n + ((q₁ * q₂ : ℕ) : ℤ))
      = Work.A7.arithW P α β n := by
    intro n
    exact Work.A7.arithW_period P (q₁ * q₂) α β hQα hQβ n
  have hw1 : ∀ n : ℤ, ‖Work.A7.arithW P α β n‖ ≤ 1 := by
    intro n
    rw [Work.A7.arithW, norm_mul, ssuDev_norm_fourier_one, ssuDev_norm_fourier_one, one_mul]
  have hdev := periodic_window_deviation (fun n : ℤ => Work.A7.arithW P α β n)
    (q₁ * q₂) N hQ hN hperw hw1
  have hssu : ssuCoeff P N α β
      = (N : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, Work.A7.arithW P α β (n : ℤ) := rfl
  have hkey : (2 : ℂ)⁻¹ * mZ P (arithQ ρ (max l₁ l₂)) α β
      = (2 * (((q₁ * q₂ : ℕ) : ℂ)))⁻¹
          * ∑ z ∈ Finset.range (q₁ * q₂), Work.A7.arithW P α β (z : ℤ) := by
    have harithQ : arithQ ρ (max l₁ l₂) = iwQl ρ (max l₁ l₂) := by
      rw [arithQ]
      refine max_eq_right (Nat.succ_le_of_lt ?_)
      simpa only [iwQl] using iwQl_pos (ρ := ρ) (l := max l₁ l₂)
    have hαmax : α ∈ iwArithFreqs ρ (max l₁ l₂) :=
      iwArithFreqs_mono hρ hρ1 (le_max_left l₁ l₂) (ssuDev_diffFreqs_subset_iwArithFreqs ρ l₁ hα)
    have hβmax : β ∈ iwArithFreqs ρ (max l₁ l₂) :=
      iwArithFreqs_mono hρ hρ1 (le_max_right l₁ l₂) (ssuDev_diffFreqs_subset_iwArithFreqs ρ l₂ hβ)
    have harithQα : arithQ ρ (max l₁ l₂) • α = 0 := by
      rw [harithQ]; exact iwQl_nsmul_eq_zero hαmax
    have harithQβ : arithQ ρ (max l₁ l₂) • β = 0 := by
      rw [harithQ]; exact iwQl_nsmul_eq_zero hβmax
    have hmZeq : mZ P (q₁ * q₂) α β = mZ P (arithQ ρ (max l₁ l₂)) α β :=
      mZ_period_eq P hQ (arithQ_pos ρ (max l₁ l₂)) hQα hQβ harithQα harithQβ
    have h2Q : (2 : ℂ)⁻¹ * (((q₁ * q₂ : ℕ) : ℂ))⁻¹
        = (2 * (((q₁ * q₂ : ℕ) : ℂ)))⁻¹ := by
      rw [mul_inv]
    rw [← hmZeq, mZ]
    simp only [Work.A7.arithW]
    rw [← h2Q]
    ring
  have hQb' : ((q₁ * q₂ : ℕ) : ℝ) ≤ Qb := hper q₁ q₂ hq₁ hq₂ hq₁α hq₂β
  have hle : 3 * ((q₁ * q₂ : ℕ) : ℝ) / (N : ℝ) ≤ 3 * Qb / (N : ℝ) := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    gcongr
  rw [hssu, hkey]
  exact hdev.trans hle

/-! ## Domination of a band by the full IW symbol -/

/-- Pointwise domination of a single band by the whole IW symbol, under non-aliasing. -/
theorem ssuDev_iwSymbolSet_singleton_le {A : Finset SsuC} {k : ℤ} {Φ : SsuC → ℂ} {α : SsuC}
    (hα : α ∈ A) (hNA : NonAliasing k A) (hSupp : SupportedInArc k Φ) :
    ∀ ξ : SsuC, ‖iwSymbolSet {α} Φ ξ‖ ≤ ‖iwSymbolSet A Φ ξ‖ := by
  intro ξ
  by_cases h0 : Φ (ξ - α) = 0
  · have hz : iwSymbolSet {α} Φ ξ = 0 := by
      simp [iwSymbolSet, h0]
    rw [hz, norm_zero]
    positivity
  · have hothers : ∀ β ∈ A, β ≠ α → Φ (ξ - β) = 0 := by
      intro β hβ hne
      by_contra hb
      obtain ⟨θ, hθ, hθeq⟩ := hSupp (ξ - β) hb
      obtain ⟨θ', hθ', hθ'eq⟩ := hSupp (ξ - α) h0
      have heq : α + (θ' : SsuC) = β + (θ : SsuC) := by
        rw [hθ'eq, hθeq]; abel
      exact hne (hNA α hα β hβ θ' hθ' θ hθ heq).1.symm
    have hsum : iwSymbolSet A Φ ξ = Φ (ξ - α) := by
      simp only [iwSymbolSet]
      exact Finset.sum_eq_single α (fun β hβ hne => hothers β hβ hne)
        (fun hna => absurd hα hna)
    have hsing : iwSymbolSet {α} Φ ξ = Φ (ξ - α) := by simp [iwSymbolSet]
    have heq : ‖iwSymbolSet {α} Φ ξ‖ = ‖iwSymbolSet A Φ ξ‖ := by rw [hsing, hsum]
    exact heq.le

/-! ## The band bound -/

/-- **A single band is dominated in `ℓ²` by the whole IW multiplier.**  If the translates
`Φ(· - α)`, `α ∈ A`, have pairwise disjoint supports (which follows from `NonAliasing k A` and
`SupportedInArc k Φ`), then the `ℓ²` norm of the single band `iwConv {α} Φ f` is at most that of
`iwConv A Φ f`. -/
theorem ssuDev_iwConv_singleton_eLpNorm_two_le
    {A : Finset SsuC} {k : ℤ} {Φ : SsuC → ℂ} {α : SsuC}
    (hα : α ∈ A) (hNA : NonAliasing k A) (hSupp : SupportedInArc k Φ)
    (hΦ : MemLp Φ ⊤ circleMeasure) (f : ℤ → ℂ) (hf : MemLp f 2 Measure.count) :
    eLpNorm (iwConv {α} Φ f) 2 Measure.count ≤ eLpNorm (iwConv A Φ f) 2 Measure.count := by
  have hdom := ssuDev_iwSymbolSet_singleton_le hα hNA hSupp
  have hAtop : MemLp (iwSymbolSet A Φ) ⊤ circleMeasure := memLp_iwSymbolSet A hΦ
  have hstop : MemLp (iwSymbolSet {α} Φ) ⊤ circleMeasure := memLp_iwSymbolSet {α} hΦ
  let F : L2Z := ⟨f, memlpOfMemLpCount (p := 2) (by norm_num) (by norm_num) hf⟩
  have h1 : iwConv {α} Φ f = ⇑(multiplierOf (iwSymbolSet {α} Φ) hstop F) := by
    have h := iwConvEqIwOpSetMemlp (A := {α}) (Φ := Φ) hstop F
    simp only [iwOpSet] at h
    rw [← h]
  have h2 : iwConv A Φ f = ⇑(multiplierOf (iwSymbolSet A Φ) hAtop F) := by
    have h := iwConvEqIwOpSetMemlp (A := A) (Φ := Φ) hAtop F
    simp only [iwOpSet] at h
    rw [← h]
  rw [h1, h2]
  refine (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp ?_
  rw [multiplierOfPlancherel (iwSymbolSet {α} Φ) hstop F,
      multiplierOfPlancherel (iwSymbolSet A Φ) hAtop F]
  refine lintegral_mono fun ξ => ?_
  refine mul_le_mul ?_ (le_refl _) (by positivity) (by positivity)
  refine ENNReal.pow_le_pow_left ?_
  simp only [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hdom ξ)

/-! ## The deviation sum -/

theorem ssuDeviationSumSelf (P : Polynomial ℤ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (l₁ l₂ u N : ℕ) (φ ψ : ℝ → ℂ) (f g : ℤ → ℂ)
    (Qb Nb : ℝ) (hQb : 0 ≤ Qb) (hNb : 0 ≤ Nb) (hN : 1 ≤ N)
    (hΦ : MemLp (periodize φ) ⊤ circleMeasure)
    (hΨ : MemLp (periodize ψ) ⊤ circleMeasure)
    (hSupp₁ : SupportedInArc (-(3 * (u : ℤ))) (periodize φ))
    (hSupp₂ : SupportedInArc (-(3 * ((P.natDegree : ℤ) * (u : ℤ)))) (periodize ψ))
    (hNA₁ : NonAliasing (-(3 * (u : ℤ))) (Work.KMTAreas.A7.diffFreqs ρ l₁))
    (hNA₂ : NonAliasing (-(3 * ((P.natDegree : ℤ) * (u : ℤ)))) (Work.KMTAreas.A7.diffFreqs ρ l₂))
    (hper : ∀ (α : Work.KMTPlan.A6.SsuC) (β : Work.KMTPlan.A6.SsuC) (q₁ q₂ : ℕ),
      α ∈ Work.KMTAreas.A7.diffFreqs ρ l₁ → β ∈ Work.KMTAreas.A7.diffFreqs ρ l₂ →
      q₁ ∈ iwP ρ l₁ → q₂ ∈ iwP ρ l₂ → q₁ • α = 0 → q₂ • β = 0 →
      ((q₁ * q₂ : ℕ) : ℝ) ≤ Qb)
    (hcard : ((Work.KMTAreas.A7.diffFreqs ρ l₁).card : ℝ)
      * ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ) ≤ Nb)
    (hf : MemLp f 2 Measure.count) (hg : MemLp g 2 Measure.count) :
    eLpNorm (fun x : ℤ =>
        ∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₁,
          ∑ β ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
            (Work.KMTPlan.A6.ssuCoeff P N α β
                - (2 : ℂ)⁻¹ * Work.KMTAreas.A7.mZ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) α β)
              * iwConv {α} (periodize φ) f x * iwConv {β} (periodize ψ) g x)
      1 Measure.count
      ≤ ENNReal.ofReal (3 * Qb * Nb / (N : ℝ))
          * eLpNorm (Work.KMTAreas.A7.Tm ρ l₁ φ f) 2 Measure.count
          * eLpNorm (Work.KMTAreas.A7.Tm ρ l₂ ψ g) 2 Measure.count := by
  classical
  let gg : SsuC → SsuC → ℤ → ℂ := fun α β x =>
    (ssuCoeff P N α β
        - (2 : ℂ)⁻¹ * mZ P (arithQ ρ (max l₁ l₂)) α β)
      * iwConv {α} (periodize φ) f x * iwConv {β} (periodize ψ) g x
  change eLpNorm (fun x : ℤ => ∑ α ∈ diffFreqs ρ l₁, ∑ β ∈ diffFreqs ρ l₂, gg α β x)
      1 Measure.count
      ≤ ENNReal.ofReal (3 * Qb * Nb / (N : ℝ))
          * eLpNorm (Tm ρ l₁ φ f) 2 Measure.count
          * eLpNorm (Tm ρ l₂ ψ g) 2 Measure.count
  set ZZ : ℝ≥0∞ := eLpNorm (Tm ρ l₁ φ f) 2 Measure.count
      * eLpNorm (Tm ρ l₂ ψ g) 2 Measure.count with hZZdef
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hband₁ : ∀ α ∈ diffFreqs ρ l₁,
      eLpNorm (iwConv {α} (periodize φ) f) 2 Measure.count
        ≤ eLpNorm (Tm ρ l₁ φ f) 2 Measure.count :=
    fun α hα => ssuDev_iwConv_singleton_eLpNorm_two_le hα hNA₁ hSupp₁ hΦ f hf
  have hband₂ : ∀ β ∈ diffFreqs ρ l₂,
      eLpNorm (iwConv {β} (periodize ψ) g) 2 Measure.count
        ≤ eLpNorm (Tm ρ l₂ ψ g) 2 Measure.count :=
    fun β hβ => ssuDev_iwConv_singleton_eLpNorm_two_le hβ hNA₂ hSupp₂ hΨ g hg
  have hdev : ∀ α ∈ diffFreqs ρ l₁, ∀ β ∈ diffFreqs ρ l₂,
      ‖ssuCoeff P N α β - (2 : ℂ)⁻¹ * mZ P (arithQ ρ (max l₁ l₂)) α β‖
        ≤ 3 * Qb / (N : ℝ) :=
    fun α hα β hβ => ssuDev_ssuCoeff_deviation P ρ hρ hρ1 l₁ l₂ N α β Qb hN hQb hα hβ
      (fun q₁ q₂ hq₁ hq₂ h₁ h₂ => hper α β q₁ q₂ hα hβ hq₁ hq₂ h₁ h₂)
  have hterm : ∀ α ∈ diffFreqs ρ l₁, ∀ β ∈ diffFreqs ρ l₂,
      eLpNorm (gg α β) 1 Measure.count
        ≤ ENNReal.ofReal (3 * Qb / (N : ℝ)) * ZZ := by
    intro α hα β hβ
    have hc : ‖ssuCoeff P N α β
        - (2 : ℂ)⁻¹ * mZ P (arithQ ρ (max l₁ l₂)) α β‖ ≤ 3 * Qb / (N : ℝ) :=
      hdev α hα β hβ
    have hHolder : eLpNorm (fun x : ℤ => iwConv {α} (periodize φ) f x
        * iwConv {β} (periodize ψ) g x) 1 Measure.count
        ≤ eLpNorm (iwConv {α} (periodize φ) f) 2 Measure.count
          * eLpNorm (iwConv {β} (periodize ψ) g) 2 Measure.count :=
      ssuDev_eLpNorm_mul_le_two _ _
    have hcENN : ‖ssuCoeff P N α β
        - (2 : ℂ)⁻¹ * mZ P (arithQ ρ (max l₁ l₂)) α β‖ₑ
        ≤ ENNReal.ofReal (3 * Qb / (N : ℝ)) := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hc
    have hbridge : gg α β = fun x : ℤ => (ssuCoeff P N α β
          - (2 : ℂ)⁻¹ * mZ P (arithQ ρ (max l₁ l₂)) α β)
        * (iwConv {α} (periodize φ) f x * iwConv {β} (periodize ψ) g x) := by
      funext x
      show (ssuCoeff P N α β - (2 : ℂ)⁻¹ * mZ P (arithQ ρ (max l₁ l₂)) α β)
            * iwConv {α} (periodize φ) f x * iwConv {β} (periodize ψ) g x
          = (ssuCoeff P N α β - (2 : ℂ)⁻¹ * mZ P (arithQ ρ (max l₁ l₂)) α β)
            * (iwConv {α} (periodize φ) f x * iwConv {β} (periodize ψ) g x)
      ring
    calc eLpNorm (gg α β) 1 Measure.count
        = eLpNorm (fun x : ℤ => (ssuCoeff P N α β
              - (2 : ℂ)⁻¹ * mZ P (arithQ ρ (max l₁ l₂)) α β)
            * (iwConv {α} (periodize φ) f x * iwConv {β} (periodize ψ) g x))
            1 Measure.count := by rw [hbridge]
      _ = ‖ssuCoeff P N α β - (2 : ℂ)⁻¹ * mZ P (arithQ ρ (max l₁ l₂)) α β‖ₑ
            * eLpNorm (fun x : ℤ => iwConv {α} (periodize φ) f x
                * iwConv {β} (periodize ψ) g x) 1 Measure.count :=
          eLpNorm_const_smul (ssuCoeff P N α β
              - (2 : ℂ)⁻¹ * mZ P (arithQ ρ (max l₁ l₂)) α β)
            (fun x : ℤ => iwConv {α} (periodize φ) f x * iwConv {β} (periodize ψ) g x)
            1 Measure.count
      _ ≤ ‖ssuCoeff P N α β - (2 : ℂ)⁻¹ * mZ P (arithQ ρ (max l₁ l₂)) α β‖ₑ
            * (eLpNorm (iwConv {α} (periodize φ) f) 2 Measure.count
                * eLpNorm (iwConv {β} (periodize ψ) g) 2 Measure.count) :=
          mul_le_mul (le_refl _) hHolder (by positivity) (by positivity)
      _ ≤ ENNReal.ofReal (3 * Qb / (N : ℝ))
            * (eLpNorm (iwConv {α} (periodize φ) f) 2 Measure.count
                * eLpNorm (iwConv {β} (periodize ψ) g) 2 Measure.count) :=
          mul_le_mul hcENN (le_refl _) (by positivity) (by positivity)
      _ ≤ ENNReal.ofReal (3 * Qb / (N : ℝ))
            * (eLpNorm (Tm ρ l₁ φ f) 2 Measure.count
                * eLpNorm (Tm ρ l₂ ψ g) 2 Measure.count) :=
          mul_le_mul (le_refl _) (mul_le_mul (hband₁ α hα) (hband₂ β hβ)
            (by positivity) (by positivity)) (by positivity) (by positivity)
      _ = ENNReal.ofReal (3 * Qb / (N : ℝ)) * ZZ := by rw [hZZdef]
  have hinner : ∀ α ∈ diffFreqs ρ l₁,
      eLpNorm (fun x : ℤ => ∑ β ∈ diffFreqs ρ l₂, gg α β x) 1 Measure.count
        ≤ ∑ β ∈ diffFreqs ρ l₂, ENNReal.ofReal (3 * Qb / (N : ℝ)) * ZZ := by
    intro α hα
    have h1 : eLpNorm (∑ b ∈ diffFreqs ρ l₂, fun x : ℤ => gg α b x) 1 Measure.count
        ≤ ∑ b ∈ diffFreqs ρ l₂, eLpNorm (fun x : ℤ => gg α b x) 1 Measure.count :=
      eLpNorm_sum_le le_rfl
    have h2 : eLpNorm (∑ b ∈ diffFreqs ρ l₂, fun x : ℤ => gg α b x) 1 Measure.count
        = eLpNorm (fun x : ℤ => ∑ b ∈ diffFreqs ρ l₂, gg α b x) 1 Measure.count :=
      congrArg (fun F : ℤ → ℂ => eLpNorm F 1 Measure.count)
        (Finset.sum_fn (diffFreqs ρ l₂) (fun b (x : ℤ) => gg α b x))
    rw [h2] at h1
    exact h1.trans (Finset.sum_le_sum fun b hb => hterm α hα b hb)
  have hmain : eLpNorm (fun x : ℤ => ∑ α ∈ diffFreqs ρ l₁, ∑ β ∈ diffFreqs ρ l₂, gg α β x)
        1 Measure.count
      ≤ ∑ α ∈ diffFreqs ρ l₁, ∑ β ∈ diffFreqs ρ l₂, ENNReal.ofReal (3 * Qb / (N : ℝ)) * ZZ := by
    have h1 : eLpNorm (∑ a ∈ diffFreqs ρ l₁,
          fun x : ℤ => ∑ β ∈ diffFreqs ρ l₂, gg a β x) 1 Measure.count
        ≤ ∑ a ∈ diffFreqs ρ l₁,
            eLpNorm (fun x : ℤ => ∑ β ∈ diffFreqs ρ l₂, gg a β x) 1 Measure.count :=
      eLpNorm_sum_le
        le_rfl
    have h2 : eLpNorm (∑ a ∈ diffFreqs ρ l₁,
          fun x : ℤ => ∑ β ∈ diffFreqs ρ l₂, gg a β x) 1 Measure.count
        = eLpNorm (fun x : ℤ => ∑ a ∈ diffFreqs ρ l₁,
            ∑ β ∈ diffFreqs ρ l₂, gg a β x) 1 Measure.count :=
      congrArg (fun F : ℤ → ℂ => eLpNorm F 1 Measure.count)
        (Finset.sum_fn (diffFreqs ρ l₁) (fun a (x : ℤ) => ∑ β ∈ diffFreqs ρ l₂, gg a β x))
    rw [h2] at h1
    exact h1.trans (Finset.sum_le_sum hinner)
  have hconst : ∑ α ∈ diffFreqs ρ l₁, ∑ β ∈ diffFreqs ρ l₂,
        ENNReal.ofReal (3 * Qb / (N : ℝ)) * ZZ
      = (((diffFreqs ρ l₁).card : ℕ) : ℝ≥0∞) * (((diffFreqs ρ l₂).card : ℕ) : ℝ≥0∞)
          * (ENNReal.ofReal (3 * Qb / (N : ℝ)) * ZZ) := by
    rw [Finset.sum_const, Finset.sum_const]
    simp only [nsmul_eq_mul]
    ring
  have hle : (((diffFreqs ρ l₁).card : ℕ) : ℝ≥0∞) * (((diffFreqs ρ l₂).card : ℕ) : ℝ≥0∞)
        * (ENNReal.ofReal (3 * Qb / (N : ℝ)) * ZZ)
      ≤ ENNReal.ofReal (3 * Qb * Nb / (N : ℝ)) * ZZ := by
    have hpos : (0 : ℝ) ≤ 3 * Qb / (N : ℝ) := by positivity
    have hcardC' : (((diffFreqs ρ l₁).card : ℕ) : ℝ≥0∞) * (((diffFreqs ρ l₂).card : ℕ) : ℝ≥0∞)
          * ENNReal.ofReal (3 * Qb / (N : ℝ))
        ≤ ENNReal.ofReal (3 * Qb * Nb / (N : ℝ)) := by
      rw [← ENNReal.ofReal_natCast ((diffFreqs ρ l₁).card),
          ← ENNReal.ofReal_natCast ((diffFreqs ρ l₂).card),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) * (3 * Qb / (N : ℝ))
          ≤ Nb * (3 * Qb / (N : ℝ)) := mul_le_mul_of_nonneg_right hcard hpos
        _ = 3 * Qb * Nb / (N : ℝ) := by ring
    calc (((diffFreqs ρ l₁).card : ℕ) : ℝ≥0∞) * (((diffFreqs ρ l₂).card : ℕ) : ℝ≥0∞)
            * (ENNReal.ofReal (3 * Qb / (N : ℝ)) * ZZ)
        = ((((diffFreqs ρ l₁).card : ℕ) : ℝ≥0∞) * (((diffFreqs ρ l₂).card : ℕ) : ℝ≥0∞)
            * ENNReal.ofReal (3 * Qb / (N : ℝ))) * ZZ := by ring
      _ ≤ ENNReal.ofReal (3 * Qb * Nb / (N : ℝ)) * ZZ :=
          mul_le_mul hcardC' (le_refl ZZ) (by positivity) (by positivity)
  calc eLpNorm (fun x : ℤ => ∑ α ∈ diffFreqs ρ l₁, ∑ β ∈ diffFreqs ρ l₂, gg α β x)
        1 Measure.count
      ≤ ∑ α ∈ diffFreqs ρ l₁, ∑ β ∈ diffFreqs ρ l₂,
          ENNReal.ofReal (3 * Qb / (N : ℝ)) * ZZ := hmain
    _ = (((diffFreqs ρ l₁).card : ℕ) : ℝ≥0∞) * (((diffFreqs ρ l₂).card : ℕ) : ℝ≥0∞)
          * (ENNReal.ofReal (3 * Qb / (N : ℝ)) * ZZ) := hconst
    _ ≤ ENNReal.ofReal (3 * Qb * Nb / (N : ℝ)) * ZZ := hle
    _ = ENNReal.ofReal (3 * Qb * Nb / (N : ℝ)) * eLpNorm (Tm ρ l₁ φ f) 2 Measure.count
          * eLpNorm (Tm ρ l₂ ψ g) 2 Measure.count := by rw [hZZdef]; ring

end

end Work.KMTPlan.A6
