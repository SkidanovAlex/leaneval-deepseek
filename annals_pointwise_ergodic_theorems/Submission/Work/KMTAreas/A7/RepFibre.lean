/-
# The fibre form of the repaired §6 model kernel `hiKmodNU` (Area A7)

This module proves `Work.KMTAreas.A7.hiKmodNU_fibre`: for an **arbitrary** window parameter `U`,
the §6 model kernel `hiKmodNU ρ P U N l₁ l₂ k₁ k₂` (the `t`-integral of the composition of the
twisted kernel `hiTwKernel` with the two exact-height kernels of the modulated bumps) equals the
double fibre sum `hiFibreKer ρ P U N l₁ l₂ k₁ k₂` over the arithmetic fibres
`(ℚ/ℤ)_{l₁} × (ℚ/ℤ)_{l₂}`.

It is the statement `Work.KMTAreas.A7.hiKmodN_fibre` (proved in
`Submission/Work/KMTAreas/A7/hiKmodN_fibre.lean` for the pinned window `uScale ρ L`) with the
window `U` left free, so that it applies to the *repaired* window
`uRep ρ l₁ l₂ k₁ k₂ = max (uScale ρ L) (max l₁ l₂ + 3)` of `modelTupleRep`.

The proof is the proof of `hiKmodN_fibre` verbatim: the only place where the pinned window was used
is the definitional unfolding of `hiKmodN`, which is replaced by the definitional unfolding of
`hiKmodNU`; all the mathematical inputs (non-aliasing at the arc `ℝ_{≤1-2U}` of the two frequency
sets, and the containment of the bump supports in `ℝ_{≤-2U}`) are hypotheses about `U` in both
versions.
-/import Mathlib
import Submission.Work.KMTAreas.A7.periodizeEqSelfOfMemRealArc
import Submission.Work.KMTAreas.A7.HiKmodNAux
import Submission.Work.KMTAreas.A7.fubini_model_bump
import Submission.Work.KMTAreas.A7.RepDefs


set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.EndVar Work.Analysis.IWMultiplier

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## Support and periodisation lemmas -/

/-- The arcs grow with their scale. -/
private lemma realArc_subset_of_le {k K : ℤ} (h : k ≤ K) :
    Work.Analysis.IonescuWainger.realArc k ⊆ Work.Analysis.IonescuWainger.realArc K := by
  intro x hx
  rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc] at hx ⊢
  have hle : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ K := zpow_le_zpow_right₀ (by norm_num) h
  exact ⟨by linarith [hx.1, hle], by linarith [hx.2, hle]⟩

/-- **A non-vanishing periodisation detects a real representative in the support.** -/
private theorem exists_coe_of_periodize_ne_zero {m : ℝ → ℂ} {ξ : Circ}
    (h : Work.Analysis.IonescuWainger.periodize m ξ ≠ 0) :
    ∃ x : ℝ, m x ≠ 0 ∧ ((x : ℝ) : Circ) = ξ := by
  set y : ℝ := (AddCircle.equivIco (1 : ℝ) 0 ξ).val with hydef
  have hyξ : ((y : ℝ) : Circ) = ξ := by
    rw [hydef]; exact AddCircle.coe_equivIco
  have hper : Work.Analysis.IonescuWainger.periodize m ξ = ∑' k : ℤ, m (y + (k : ℝ)) := by
    rw [← hyξ, Work.KMTContract.periodizeCoeEqTsum]
  have hne : ∃ k : ℤ, m (y + (k : ℝ)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact h (by rw [hper]; simp [hcon])
  obtain ⟨k, hk⟩ := hne
  refine ⟨y + (k : ℝ), hk, ?_⟩
  rw [AddCircle.coe_add, hyξ]
  have hk0 : (((k : ℝ)) : Circ) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k, by simp⟩
  rw [hk0, add_zero]

/-- `fourier (T := 1) n` at a real point is the character `e(n·)`. -/
private lemma fourier_coe_eq_ee (n : ℤ) (y : ℝ) :
    fourier (T := 1) n ((y : ℝ) : Circ) = Work.KMTAreas.A7.ee ((n : ℝ) * y) := by
  rw [fourier_coe_apply, Work.KMTAreas.A7.ee]
  congr 1
  push_cast
  ring

/-- `fourier (T := 1) (-n)` at a real point is the character `e(-n·)`. -/
private lemma fourier_coe_eq_ee_neg (n : ℤ) (y : ℝ) :
    fourier (T := 1) (-n) ((y : ℝ) : Circ) = Work.KMTAreas.A7.ee (-(n : ℝ) * y) := by
  rw [fourier_coe_eq_ee]
  congr 1
  push_cast
  ring

/-- **The aliasing vanishing of the periodisation.**  If `m` is supported in the arc `ℝ_{≤k}`, if
`α ≠ α₁` are two frequencies of a set which is non-aliasing at the coarser scale `K ≥ k`, then
`periodize m` vanishes on the translate `ℝ_{≤k} - (α - α₁)`. -/
private theorem periodize_eq_zero_of_aliasing {m : ℝ → ℂ} {k K : ℤ} (hkK : k ≤ K)
    {A : Finset Circ} (hNA : Work.Analysis.IonescuWainger.NonAliasing K A)
    (hmk : ∀ x : ℝ, m x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k)
    {α α₁ : Circ} (hα : α ∈ A) (hα₁ : α₁ ∈ A) (h : α ≠ α₁) {y : ℝ}
    (hyk : y ∈ Work.Analysis.IonescuWainger.realArc k) :
    Work.Analysis.IonescuWainger.periodize m (((y : ℝ) : Circ) - (α - α₁)) = 0 := by
  by_contra hne
  obtain ⟨x, hxne, hxc⟩ := exists_coe_of_periodize_ne_zero hne
  have hxK := realArc_subset_of_le hkK (hmk x hxne)
  have hyK := realArc_subset_of_le hkK hyk
  have heq : α + ((x : ℝ) : Circ) = α₁ + ((y : ℝ) : Circ) := by
    rw [hxc]; abel
  exact h (hNA α hα α₁ hα₁ x hxK y hyK heq).1

/-! ## The one-variable collapse, from the master identity -/

/-- The one-variable collapse `tsum_cw_collapse`, derived from the master identity
`tsum_cw_fourier_eq_integral`. -/
private theorem tsum_cw_collapse_derived {m f : ℝ → ℂ} (hm : ContDiff ℝ 2 m)
    (hcs : HasCompactSupport m) (hf : MeasureTheory.Integrable f) {k K : ℤ} (hkK : k ≤ K)
    {A : Finset Circ} (hNA : Work.Analysis.IonescuWainger.NonAliasing K A)
    (hmk : ∀ x : ℝ, m x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k)
    (hfk : ∀ y : ℝ, f y ≠ 0 → y ∈ Work.Analysis.IonescuWainger.realArc k)
    (hk4 : (2 : ℝ) ^ k ≤ 1 / 4) {α α₁ : Circ} (hα : α ∈ A) (hα₁ : α₁ ∈ A) (a : ℤ) :
    (∑' j : ℤ, Work.KMTAreas.A7.cw m j
        * fourier (T := 1) (-j) (α - α₁) * Work.KMTAreas.A7.cw f (a - j))
      = if α = α₁ then Work.KMTAreas.A7.cw (fun x => m x * f x) a else 0 := by
  by_cases h : α = α₁
  · subst h
    rw [tsum_cw_fourier_eq_integral_aux hm hcs hf (α - α) a, if_pos rfl, sub_self]
    rw [show (fun y : ℝ => f y * fourier (T := 1) (-a) ((y : ℝ) : Circ)
          * Work.Analysis.IonescuWainger.periodize m (((y : ℝ) : Circ) - 0))
        = fun y : ℝ => (m y * f y) * Work.KMTAreas.A7.ee (-(a : ℝ) * y) from by
      funext y
      rw [sub_zero, fourier_coe_eq_ee_neg]
      by_cases hy : f y = 0
      · rw [hy]; ring
      · rw [periodizeEqSelfOfMemRealArc hk4 hmk (hfk y hy)]
        ring]
    rfl
  · rw [tsum_cw_fourier_eq_integral_aux hm hcs hf (α - α₁) a, if_neg h]
    rw [show (fun y : ℝ => f y * fourier (T := 1) (-a) ((y : ℝ) : Circ)
          * Work.Analysis.IonescuWainger.periodize m (((y : ℝ) : Circ) - (α - α₁)))
        = fun _ => 0 from by
      funext y
      by_cases hy : f y = 0
      · rw [hy]; ring
      · rw [periodize_eq_zero_of_aliasing hkK hNA hmk hα hα₁ h (hfk y hy)]
        ring]
    simp

/-! ## The two-variable collapse, from the factorisation -/

/-- The two-variable collapse `kernComp_arith_collapse`, derived from the factorisation
`kernComp_arith_factor` together with the two one-variable collapse identities. -/
private theorem kernComp_arith_collapse_derived {A₁ A₂ : Finset Circ}
    (W : Circ → Circ → ℂ) (m₁ m₂ f g : ℝ → ℂ) (a b : ℤ)
    (hs₁ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₁ j‖)
    (hs₂ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₂ j‖)
    (hf : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw f j‖)
    (hg : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw g j‖)
    (hcol₁ : ∀ α ∈ A₁, ∀ α₁ ∈ A₁,
      (∑' j : ℤ, Work.KMTAreas.A7.cw m₁ j
          * fourier (T := 1) (-j) (α - α₁) * Work.KMTAreas.A7.cw f (a - j))
        = if α = α₁ then Work.KMTAreas.A7.cw (fun x => m₁ x * f x) a else 0)
    (hcol₂ : ∀ β ∈ A₂, ∀ β₁ ∈ A₂,
      (∑' j : ℤ, Work.KMTAreas.A7.cw m₂ j
          * fourier (T := 1) (-j) (β - β₁) * Work.KMTAreas.A7.cw g (b - j))
        = if β = β₁ then Work.KMTAreas.A7.cw (fun x => m₂ x * g x) b else 0) :
    Work.KMTAreas.A7.kernComp
        (fun j₁ j₂ => (∑ α ∈ A₁, ∑ β ∈ A₂,
              W α β * fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β)
            * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂)
        (fun j => (∑ α ∈ A₁, fourier (T := 1) (-j) α) * Work.KMTAreas.A7.cw f j)
        (fun j => (∑ β ∈ A₂, fourier (T := 1) (-j) β) * Work.KMTAreas.A7.cw g j) a b
      = ∑ α ∈ A₁, ∑ β ∈ A₂, W α β * fourier (T := 1) (-a) α * fourier (T := 1) (-b) β
          * Work.KMTAreas.A7.cw (fun x => m₁ x * f x) a
          * Work.KMTAreas.A7.cw (fun x => m₂ x * g x) b := by
  rw [kernComp_arith_factor_aux W m₁ m₂ f g a b hs₁ hs₂ hf hg]
  refine Finset.sum_congr rfl (fun α hα => Finset.sum_congr rfl (fun β hβ => ?_))
  have hstep : (∑ α₁ ∈ A₁, ∑ β₁ ∈ A₂,
        fourier (T := 1) (-a) α₁ * fourier (T := 1) (-b) β₁
          * (∑' j : ℤ, Work.KMTAreas.A7.cw m₁ j * fourier (T := 1) (-j) (α - α₁)
              * Work.KMTAreas.A7.cw f (a - j))
          * (∑' j : ℤ, Work.KMTAreas.A7.cw m₂ j * fourier (T := 1) (-j) (β - β₁)
              * Work.KMTAreas.A7.cw g (b - j)))
      = (∑ α₁ ∈ A₁, fourier (T := 1) (-a) α₁
          * (if α = α₁ then Work.KMTAreas.A7.cw (fun x => m₁ x * f x) a else (0 : ℂ)))
        * (∑ β₁ ∈ A₂, fourier (T := 1) (-b) β₁
          * (if β = β₁ then Work.KMTAreas.A7.cw (fun x => m₂ x * g x) b else (0 : ℂ))) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun α₁ hα₁ => Finset.sum_congr rfl (fun β₁ hβ₁ => ?_))
    rw [hcol₁ α hα α₁ hα₁, hcol₂ β hβ β₁ hβ₁]
    ring_nf
  have h1 : (∑ α₁ ∈ A₁, fourier (T := 1) (-a) α₁
        * (if α = α₁ then Work.KMTAreas.A7.cw (fun x => m₁ x * f x) a else (0 : ℂ)))
      = fourier (T := 1) (-a) α * Work.KMTAreas.A7.cw (fun x => m₁ x * f x) a := by
    rw [show (∑ α₁ ∈ A₁, fourier (T := 1) (-a) α₁
          * (if α = α₁ then Work.KMTAreas.A7.cw (fun x => m₁ x * f x) a else (0 : ℂ)))
        = ∑ α₁ ∈ A₁, (if α = α₁ then fourier (T := 1) (-a) α₁
            * Work.KMTAreas.A7.cw (fun x => m₁ x * f x) a else (0 : ℂ)) from
        Finset.sum_congr rfl (fun x hx => by split_ifs <;> ring)]
    rw [Finset.sum_ite_eq, if_pos hα]
  have h2 : (∑ β₁ ∈ A₂, fourier (T := 1) (-b) β₁
        * (if β = β₁ then Work.KMTAreas.A7.cw (fun x => m₂ x * g x) b else (0 : ℂ)))
      = fourier (T := 1) (-b) β * Work.KMTAreas.A7.cw (fun x => m₂ x * g x) b := by
    rw [show (∑ β₁ ∈ A₂, fourier (T := 1) (-b) β₁
          * (if β = β₁ then Work.KMTAreas.A7.cw (fun x => m₂ x * g x) b else (0 : ℂ)))
        = ∑ β₁ ∈ A₂, (if β = β₁ then fourier (T := 1) (-b) β₁
            * Work.KMTAreas.A7.cw (fun x => m₂ x * g x) b else (0 : ℂ)) from
        Finset.sum_congr rfl (fun x hx => by split_ifs <;> ring)]
    rw [Finset.sum_ite_eq, if_pos hβ]
  rw [hstep, h1, h2]
  ring_nf

theorem hiKmodNU_fibre (ρ : ℝ) (P : Polynomial ℤ) (U N : ℕ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ)
    (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂)
    (hna₁ : Work.Analysis.IonescuWainger.NonAliasing (1 - 2 * (U : ℤ))
      (Work.KMTAreas.A7.diffFreqs ρ l₁))
    (hna₂ : Work.Analysis.IonescuWainger.NonAliasing (1 - 2 * (U : ℤ))
      (Work.KMTAreas.A7.diffFreqs ρ l₂))
    (hs₁ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ θ : ℝ,
      Work.KMTAreas.A7.varphiNt N k₁ t θ ≠ 0 →
        θ ∈ Work.Analysis.IonescuWainger.realArc (-(2 * (U : ℤ))))
    (hs₂ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ θ : ℝ,
      Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t θ ≠ 0 →
        θ ∈ Work.Analysis.IonescuWainger.realArc (-(2 * (U : ℤ)))) :
    Work.KMTAreas.A7.hiKmodNU ρ P U N l₁ l₂ k₁ k₂ j₁ j₂
      = Work.KMTAreas.A7.hiFibreKer ρ P U N l₁ l₂ k₁ k₂ j₁ j₂ := by
  classical
  rw [Work.KMTAreas.A7.hiFibreKer]
  have hunfold : Work.KMTAreas.A7.hiKmodNU ρ P U N l₁ l₂ k₁ k₂ j₁ j₂
      = ∫ t in (1/2 : ℝ)..1,
          Work.KMTAreas.A7.kernComp
            (Work.KMTAreas.A7.hiTwKernel ρ P l₁ l₂ (Work.KMTAreas.A7.mStarF U)
              (Work.KMTAreas.A7.mStargF P.natDegree U))
            (Work.KMTAreas.A7.hiKer ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ t))
            (Work.KMTAreas.A7.hiKer ρ l₂
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t)) j₁ j₂ := rfl
  have hna₁' : Work.Analysis.IonescuWainger.NonAliasing (1 - 2 * (U : ℤ))
      (Work.KMTAreas.A7.diffFreqs ρ l₁) := hna₁
  have hna₂' : Work.Analysis.IonescuWainger.NonAliasing (1 - 2 * (U : ℤ))
      (Work.KMTAreas.A7.diffFreqs ρ l₂) := hna₂
  have hs₁' : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ θ : ℝ,
      Work.KMTAreas.A7.varphiNt N k₁ t θ ≠ 0 →
        θ ∈ Work.Analysis.IonescuWainger.realArc (-(2 * (U : ℤ))) := hs₁
  have hs₂' : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ θ : ℝ,
      Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t θ ≠ 0 →
        θ ∈ Work.Analysis.IonescuWainger.realArc (-(2 * (U : ℤ))) := hs₂

  -- the `C²` regularity of the two window cutoffs
  have hm₁ : ContDiff ℝ 2 (Work.KMTAreas.A7.mStarF U) :=
    (contDiff_infty.mp (Work.KMTAreas.A7.contDiff_etaCut (-(2 * (U : ℤ))))) 2
  have hm₂ : ContDiff ℝ 2 (Work.KMTAreas.A7.mStargF P.natDegree U) :=
    (contDiff_infty.mp
      (Work.KMTAreas.A7.contDiff_etaCut (-((P.natDegree : ℤ) * 2 * (U : ℤ))))) 2
  by_cases hF₁ : Work.KMTAreas.A7.diffFreqs ρ l₁ = ∅
  · -- no arithmetic frequencies in the first variable: both sides vanish
    have hAK : Work.KMTAreas.A7.arithKernelExact ρ P
        (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) l₁ l₂ = fun _ _ => 0 := by
      funext a b
      rw [Work.KMTAreas.A7.arithKernelExact,
        Work.KMTAreas.A7.iwArithFreqsNew_eq_diffFreqs ρ hl₁, hF₁]
      simp
    have hK0 : Work.KMTAreas.A7.hiTwKernel ρ P l₁ l₂ (Work.KMTAreas.A7.mStarF U)
        (Work.KMTAreas.A7.mStargF P.natDegree U) = fun _ _ => 0 := by
      funext a b
      simp only [Work.KMTAreas.A7.hiTwKernel, hAK, zero_mul]
    have hLHS : Work.KMTAreas.A7.hiKmodNU ρ P U N l₁ l₂ k₁ k₂ j₁ j₂ = 0 := by
      rw [hunfold, hK0]
      simp only [Work.KMTAreas.A7.kernComp, zero_mul, tsum_zero]
      exact intervalIntegral.integral_zero
    rw [hLHS, hF₁]
    simp
  · by_cases hF₂ : Work.KMTAreas.A7.diffFreqs ρ l₂ = ∅
    · have hAK : Work.KMTAreas.A7.arithKernelExact ρ P
          (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) l₁ l₂ = fun _ _ => 0 := by
        funext a b
        rw [Work.KMTAreas.A7.arithKernelExact,
          Work.KMTAreas.A7.iwArithFreqsNew_eq_diffFreqs ρ hl₂, hF₂]
        simp
      have hK0 : Work.KMTAreas.A7.hiTwKernel ρ P l₁ l₂ (Work.KMTAreas.A7.mStarF U)
          (Work.KMTAreas.A7.mStargF P.natDegree U) = fun _ _ => 0 := by
        funext a b
        simp only [Work.KMTAreas.A7.hiTwKernel, hAK, zero_mul]
      have hLHS : Work.KMTAreas.A7.hiKmodNU ρ P U N l₁ l₂ k₁ k₂ j₁ j₂ = 0 := by
        rw [hunfold, hK0]
        simp only [Work.KMTAreas.A7.kernComp, zero_mul, tsum_zero]
        exact intervalIntegral.integral_zero
      rw [hLHS, hF₂]
      simp
    · -- both arithmetic frequency sets are non-empty
      -- non-aliasing forces the auxiliary scale to be at least one
      have hu1 : 1 ≤ U := by
        by_contra hlt
        push_neg at hlt
        have hu0 : U = 0 := by omega
        obtain ⟨α, hα⟩ := Finset.nonempty_iff_ne_empty.mpr hF₁
        have h00 : ((0 : ℝ) : Circ) = 0 := by
          rw [AddCircle.coe_eq_zero_iff]; exact ⟨0, by simp⟩
        have h11 : ((1 : ℝ) : Circ) = 0 := by
          rw [AddCircle.coe_eq_zero_iff]; exact ⟨1, by norm_num⟩
        have hmem0 : (0 : ℝ) ∈ Work.Analysis.IonescuWainger.realArc (1 - 2 * (U : ℤ)) := by
          rw [hu0, Work.Analysis.IonescuWainger.realArc]
          norm_num
        have hmem1 : (1 : ℝ) ∈ Work.Analysis.IonescuWainger.realArc (1 - 2 * (U : ℤ)) := by
          rw [hu0, Work.Analysis.IonescuWainger.realArc]
          norm_num
        have heq : α + ((0 : ℝ) : Circ) = α + ((1 : ℝ) : Circ) := by rw [h00, h11]
        have hres : α = α ∧ (0 : ℝ) = 1 := hna₁' α hα α hα 0 hmem0 1 hmem1 heq
        exact absurd hres.2 (by norm_num)
      have hk4 : (2 : ℝ) ^ (-(2 * (U : ℤ))) ≤ 1 / 4 := by
        have hUZ : (1 : ℤ) ≤ (U : ℤ) := by exact_mod_cast hu1
        calc (2 : ℝ) ^ (-(2 * (U : ℤ))) ≤ (2 : ℝ) ^ (-2 : ℤ) :=
              zpow_le_zpow_right₀ (by norm_num) (by omega)
          _ = 1 / 4 := by norm_num
      have hkK : -(2 * (U : ℤ)) ≤ 1 - 2 * (U : ℤ) := by omega
      -- the one-variable collapse in the first variable, for every `t`
      have hcol₁ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₁,
          ∀ α₁ ∈ Work.KMTAreas.A7.diffFreqs ρ l₁,
          (∑' j : ℤ, Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j
              * fourier (T := 1) (-j) (α - α₁)
              * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiNt N k₁ t) (j₁ - j))
            = if α = α₁ then Work.KMTAreas.A7.cw
                (fun x => Work.KMTAreas.A7.mStarF U x
                  * Work.KMTAreas.A7.varphiNt N k₁ t x) j₁ else 0 := by
        intro t ht α hα α₁ hα₁
        exact tsum_cw_collapse_derived hm₁ (Work.KMTAreas.A7.hasCompactSupport_etaCut _)
          (Work.KMTAreas.A7.integrable_varphiNt N k₁ t)
          hkK hna₁' (fun x hx => Work.KMTAreas.A7.etaCut_ne_zero_mem_realArc _ hx)
          (fun y hy => hs₁' t ht y hy) hk4 hα hα₁ j₁
      by_cases hd0 : P.natDegree = 0
      · -- the polynomial is constant
        by_cases hk20 : k₂ = 0
        · -- the second bump has support of radius `1`, contradicting `hs₂`
          exfalso
          have hvar0 : Work.KMTAreas.A7.varphitildeN 0 N 0 = Work.KMTContract.kmtEta := by
            funext ξ
            rw [Work.KMTAreas.A7.varphitildeN, if_pos rfl]
            norm_num
          have hval : Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ (1/2) (1/2) ≠ 0 := by
            rw [hd0, hk20, Work.KMTAreas.A7.varphitildeNt, hvar0]
            simp only [Work.KMTAreas.A7.varphitildeNt, Work.KMTContract.kmtEta_one (by norm_num :
              |(1/2 : ℝ)| ≤ 1/2)]
            exact mul_ne_zero one_ne_zero (Complex.exp_ne_zero _)
          have hmem := hs₂' (1/2) (by norm_num) (1/2) hval
          rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc] at hmem
          linarith [hmem.2, hk4]
        · -- `φ̃` vanishes identically, hence both sides vanish
          have hvar : ∀ ξ : ℝ, Work.KMTAreas.A7.varphitildeN 0 N k₂ ξ = 0 := by
            intro ξ
            rw [Work.KMTAreas.A7.varphitildeN, if_neg hk20]
            norm_num
          have hvarP : Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ = fun _ => 0 := by
            funext ξ
            rw [hd0]; exact hvar ξ
          have hker : ∀ t : ℝ, Work.KMTAreas.A7.hiKer ρ l₂
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t) = fun _ => 0 := by
            intro t
            have hper : Work.Analysis.IonescuWainger.periodize (fun _ : ℝ => (0 : ℂ))
                = fun _ => 0 := by
              funext ξ
              simp [Work.Analysis.IonescuWainger.periodize]
            have ht0 : Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t = fun _ => 0 := by
              funext ξ
              simp only [Work.KMTAreas.A7.varphitildeNt, hvarP, Pi.zero_apply, zero_mul]
            funext j
            simp only [Work.KMTAreas.A7.hiKer, ht0, hper,
              Work.Analysis.IonescuWainger.iwSymbolSet_zero]
            simp [Work.Analysis.IWMultiplier.iwKernel, fourierCoeff]
          have hLHS : Work.KMTAreas.A7.hiKmodNU ρ P U N l₁ l₂ k₁ k₂ j₁ j₂ = 0 := by
            rw [hunfold]
            simp only [hker, Work.KMTAreas.A7.kernComp, mul_zero, tsum_zero]
            exact intervalIntegral.integral_zero
          have hRHS : (∑ p ∈ (Work.KMTAreas.A7.diffFreqs ρ l₁).product
                (Work.KMTAreas.A7.diffFreqs ρ l₂),
              fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2
                * Work.KMTAreas.A7.mZ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) p.1 p.2
                * (∫ θ₁ : ℝ, ∫ θ₂ : ℝ,
                    Work.KMTAreas.A7.mStarF U θ₁
                    * Work.KMTAreas.A7.mStargF P.natDegree U θ₂
                    * Work.KMTAreas.A7.varphiN N k₁ θ₁
                    * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ θ₂
                    * Work.KMTAreas.A7.mTilde P N θ₁ θ₂
                    * Work.KMTAreas.A7.ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂)))) = 0 := by
            refine Finset.sum_eq_zero (fun p hp => ?_)
            have hzero : (∫ θ₁ : ℝ, ∫ θ₂ : ℝ,
                Work.KMTAreas.A7.mStarF U θ₁
                  * Work.KMTAreas.A7.mStargF P.natDegree U θ₂
                  * Work.KMTAreas.A7.varphiN N k₁ θ₁
                  * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ θ₂
                  * Work.KMTAreas.A7.mTilde P N θ₁ θ₂
                  * Work.KMTAreas.A7.ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂))) = 0 := by
              simp only [hvarP, mul_zero, zero_mul]
              simp
            rw [hzero, mul_zero]
          rw [hLHS, hRHS]
      · -- the polynomial has positive degree
        have hd1 : 1 ≤ P.natDegree := Nat.one_le_iff_ne_zero.mpr hd0
        have hArcSub : Work.Analysis.IonescuWainger.realArc
              (-((P.natDegree : ℤ) * 2 * (U : ℤ)))
            ⊆ Work.Analysis.IonescuWainger.realArc (-(2 * (U : ℤ))) := by
          intro x hx
          rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc] at hx ⊢
          have hd2 : (2 : ℤ) ≤ (P.natDegree : ℤ) * 2 := by
            have h1 : (1 : ℤ) ≤ (P.natDegree : ℤ) := by exact_mod_cast hd1
            linarith
          have hU0 : (0 : ℤ) ≤ (U : ℤ) := Int.natCast_nonneg _
          have hle : (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (U : ℤ)))
              ≤ (2 : ℝ) ^ (-(2 * (U : ℤ))) := by
            refine zpow_le_zpow_right₀ (by norm_num) ?_
            have h3 := mul_le_mul_of_nonneg_right hd2 hU0
            linarith
          exact ⟨by linarith [hx.1, hle], by linarith [hx.2, hle]⟩
        have hcol₂ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ β ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
            ∀ β₁ ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
            (∑' j : ℤ, Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree U) j
                * fourier (T := 1) (-j) (β - β₁)
                * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t)
                    (j₂ - j))
              = if β = β₁ then Work.KMTAreas.A7.cw
                  (fun x => Work.KMTAreas.A7.mStargF P.natDegree U x
                    * Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t x) j₂ else 0 := by
          intro t ht β hβ β₁ hβ₁
          exact tsum_cw_collapse_derived hm₂ (Work.KMTAreas.A7.hasCompactSupport_etaCut _)
            (Work.KMTAreas.A7.integrable_varphitildeNt_aux P P.natDegree N k₂ t)
            hkK hna₂'
            (fun x hx => hArcSub (Work.KMTAreas.A7.etaCut_ne_zero_mem_realArc _ hx))
            (fun y hy => hs₂' t ht y hy) hk4 hβ hβ₁ j₂
        -- the two-variable collapse, for every `t`
        have hpt : ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
            Work.KMTAreas.A7.kernComp
              (Work.KMTAreas.A7.hiTwKernel ρ P l₁ l₂ (Work.KMTAreas.A7.mStarF U)
                (Work.KMTAreas.A7.mStargF P.natDegree U))
              (Work.KMTAreas.A7.hiKer ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ t))
              (Work.KMTAreas.A7.hiKer ρ l₂
                (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t)) j₁ j₂
            = ∑ p ∈ (Work.KMTAreas.A7.diffFreqs ρ l₁).product
                (Work.KMTAreas.A7.diffFreqs ρ l₂),
                fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2
                  * Work.KMTAreas.A7.mZ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) p.1 p.2
                  * (Work.KMTAreas.A7.cw (fun x => Work.KMTAreas.A7.mStarF U x
                        * Work.KMTAreas.A7.varphiNt N k₁ t x) j₁
                     * Work.KMTAreas.A7.cw (fun x => Work.KMTAreas.A7.mStargF P.natDegree U x
                        * Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t x) j₂) := by
          intro t ht
          have hκ : Work.KMTAreas.A7.hiKer ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ t)
              = fun j => (∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₁, fourier (T := 1) (-j) α)
                  * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiNt N k₁ t) j := by
            funext j
            rw [Work.KMTAreas.A7.hiKer_fourier ρ l₁
              (Work.KMTAreas.A7.integrable_varphiNt N k₁ t)]
          have hκ' : Work.KMTAreas.A7.hiKer ρ l₂
                (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t)
              = fun j => (∑ β ∈ Work.KMTAreas.A7.diffFreqs ρ l₂, fourier (T := 1) (-j) β)
                  * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t) j := by
            funext j
            rw [Work.KMTAreas.A7.hiKer_fourier ρ l₂
              (Work.KMTAreas.A7.integrable_varphitildeNt_aux P P.natDegree N k₂ t)]
          have hK : Work.KMTAreas.A7.hiTwKernel ρ P l₁ l₂ (Work.KMTAreas.A7.mStarF U)
                (Work.KMTAreas.A7.mStargF P.natDegree U)
              = fun j₁ j₂ => (∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₁,
                    ∑ β ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
                    Work.KMTAreas.A7.mZ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) α β
                      * fourier (T := 1) (-j₁) α * fourier (T := 1) (-j₂) β)
                  * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j₁
                  * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree U) j₂ := by
            funext j₁ j₂
            simp only [Work.KMTAreas.A7.hiTwKernel, Work.KMTAreas.A7.arithKernelExact,
              Work.KMTAreas.A7.iwArithFreqsNew_eq_diffFreqs ρ hl₁,
              Work.KMTAreas.A7.iwArithFreqsNew_eq_diffFreqs ρ hl₂]
          rw [hK, hκ, hκ']
          rw [kernComp_arith_collapse_derived (A₁ := Work.KMTAreas.A7.diffFreqs ρ l₁)
            (A₂ := Work.KMTAreas.A7.diffFreqs ρ l₂)
            (W := fun α β => Work.KMTAreas.A7.mZ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) α β)
            (m₁ := Work.KMTAreas.A7.mStarF U)
            (m₂ := Work.KMTAreas.A7.mStargF P.natDegree U)
            (f := Work.KMTAreas.A7.varphiNt N k₁ t)
            (g := Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t)
            (a := j₁) (b := j₂)
            (Work.KMTAreas.A7.summable_cw_mStarF U)
            (Work.KMTAreas.A7.summable_cw_mStargF P.natDegree U)
            (Work.KMTAreas.A7.summable_cw_varphiNt N k₁ t)
            (Work.KMTAreas.A7.summable_cw_varphitildeNt P P.natDegree N k₂ t)
            (hcol₁ t ht) (hcol₂ t ht)]
          rw [Finset.product_eq_sprod, Finset.sum_product]
          refine Finset.sum_congr rfl (fun α hα => Finset.sum_congr rfl (fun β hβ => ?_))
          ring
        -- integrate in `t` and apply the Fubini identity
        rw [hunfold]
        trans ∫ t in (1/2 : ℝ)..1, ∑ p ∈ (Work.KMTAreas.A7.diffFreqs ρ l₁).product
              (Work.KMTAreas.A7.diffFreqs ρ l₂),
              fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2
                * Work.KMTAreas.A7.mZ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) p.1 p.2
                * (Work.KMTAreas.A7.cw (fun x => Work.KMTAreas.A7.mStarF U x
                      * Work.KMTAreas.A7.varphiNt N k₁ t x) j₁
                   * Work.KMTAreas.A7.cw (fun x => Work.KMTAreas.A7.mStargF P.natDegree U x
                      * Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t x) j₂)
        · refine intervalIntegral.integral_congr (fun t ht => ?_)
          exact hpt t (by rwa [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht)
        · trans ∫ t in (1/2 : ℝ)..1, (∑ p ∈ (Work.KMTAreas.A7.diffFreqs ρ l₁).product
                (Work.KMTAreas.A7.diffFreqs ρ l₂),
                fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2
                  * Work.KMTAreas.A7.mZ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) p.1 p.2)
              * (Work.KMTAreas.A7.cw (fun x => Work.KMTAreas.A7.mStarF U x
                    * Work.KMTAreas.A7.varphiNt N k₁ t x) j₁
                 * Work.KMTAreas.A7.cw (fun x => Work.KMTAreas.A7.mStargF P.natDegree U x
                    * Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t x) j₂)
          · refine intervalIntegral.integral_congr (fun t _ => ?_)
            rw [Finset.sum_mul]
          · rw [intervalIntegral.integral_const_mul,
              fubini_model_bump P N k₁ k₂ U j₁ j₂, Finset.sum_mul]
end

end Work.KMTAreas.A7
