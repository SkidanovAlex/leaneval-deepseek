/-
# The `l₂ = 0` case of the single-scale `ℓ¹(ℤ²)` mass bound of §6

Target `Work.KMTAreas.A7.LoMixedRMass (P : ℤ[X]) : LoMixedRMassStatement P`
(`Submission/Work/KMTAreas/A7/LoMixedRMassDefs.lean`).

The model kernel vanishes at `l₂ = 0` (`hiKmod_lo2`), so the target is a mass bound for the
concrete kernel `hiKconc ρ P a l₁ 0 k₁ k₂ n`, which on the guard is `hiKconcN ρ P ⌊a n⌋ l₁ 0 k₁ k₂`
(`hiKconc_eq`).  The fibre form `hiKconcN_fibre` expands it into the double Fourier coefficients of
the bump product against the discrete average `weylAvg P N α 0`, summed over the exact-height
arithmetic frequencies `α ∈ (ℚ/ℤ)_{l₁}`.  The per-fibre mass bound is the analytic core of §6
(isolated as `FibreMassStatement`); the arithmetic factors `#(ℚ/ℤ)_{l₁}` and the period `q` of `α`
are absorbed by `modelWeight` (`AbsorbStatement`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedRMassDefs
import Submission.Work.KMTAreas.A7.hiKconcN_fibre
import Submission.Work.KMTAreas.A7.LoFibreMass
import Submission.Work.KMTAreas.A7.exp_dominates_poly_half
import Submission.Work.KMTAreas.A7.sval_term_bound
import Submission.Work.KMTPlan.A6.iwP_element_le_sharp

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.KMTContract
open Work.Analysis.IonescuWainger

/-- The characters of the circle have modulus one. -/
theorem fourier_norm_one (n : ℤ) (ξ : Work.Analysis.IonescuWainger.Circle) :
    ‖fourier (T := 1) n ξ‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- The IW arithmetic frequency set of height `≤ 1` is `{0}`. -/
theorem iwArithFreqs_zero (ρ : ℝ) : iwArithFreqs ρ 0 = {0} := by
  ext x
  rw [mem_iwArithFreqs]
  constructor
  · rintro ⟨q, hq, hqα⟩
    have hP : iwP ρ 0 = {1} := by
      rw [iwP, if_pos (Nat.zero_le _)]
      norm_num
    rw [hP] at hq
    have hq1 : q = 1 := by simpa using hq
    subst hq1
    simpa using hqα
  · intro hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact ⟨1, by rw [iwP, if_pos (Nat.zero_le _)]; norm_num, by simp⟩

/-- The exact-height frequency set at `l = 0` is `{0}`. -/
theorem diffFreqs_zero (ρ : ℝ) : diffFreqs ρ 0 = {0} := by
  rw [diffFreqs, if_pos rfl, iwArithFreqs_zero]

/-- `0` is an IW arithmetic frequency of every height. -/
theorem zero_mem_iwArithFreqs (ρ : ℝ) (m : ℕ) :
    (0 : Work.Analysis.IonescuWainger.Circle) ∈ iwArithFreqs ρ m :=
  mem_iwArithFreqs.mpr ⟨1, one_mem_iwP ρ m, by simp⟩

/-- `0` is not an exact-height frequency at a positive height. -/
theorem zero_not_mem_diffFreqs (ρ : ℝ) {l : ℕ} (hl : 1 ≤ l) :
    (0 : Work.Analysis.IonescuWainger.Circle) ∉ diffFreqs ρ l := by
  rw [diffFreqs, if_neg (by omega : ¬ l = 0)]
  intro h
  exact (Finset.mem_sdiff.mp h).2 (zero_mem_iwArithFreqs ρ (l - 1))

/-- The exact-height frequency set is contained in the IW arithmetic frequency set. -/
theorem diffFreqs_subset_iwArithFreqs (ρ : ℝ) (l : ℕ) :
    diffFreqs ρ l ⊆ iwArithFreqs ρ l := by
  rcases eq_or_ne l 0 with h | h
  · subst h; rw [diffFreqs, if_pos rfl]
  · rw [diffFreqs, if_neg h]; exact Finset.sdiff_subset

/-- The twisted kernel at `l₂ = 0` vanishes: the inner arithmetic sum is empty. -/
theorem hiTwKernel_lo2 (ρ : ℝ) (P : ℤ[X]) (l₁ : ℕ) (m₁ m₂ : ℝ → ℂ) :
    hiTwKernel ρ P l₁ 0 m₁ m₂ = 0 := by
  funext j₁ j₂
  simp only [hiTwKernel, arithKernelExact, iwArithFreqsNew_zero]
  simp

/-- The model kernel at `l₂ = 0` vanishes. -/
theorem hiKmod_lo2 (ρ : ℝ) (P : ℤ[X]) (a : ℕ → NNReal) (l₁ k₁ k₂ n : ℕ) :
    hiKmod ρ P a l₁ 0 k₁ k₂ n = 0 := by
  funext j₁ j₂
  rw [hiKmod]
  simp only [hiTwKernel_lo2, kernComp, Pi.zero_apply, zero_mul, tsum_zero,
    intervalIntegral.integral_zero]

/-- The per-fibre integrand of the concrete column at `l₂ = 0`: the double Fourier coefficient
of the bump product against the discrete average `weylAvg P N α 0`. -/
noncomputable def fibreInt (P : Polynomial ℤ) (N k₁ k₂ : ℕ)
    (α : Work.Analysis.IonescuWainger.Circle) (j₁ j₂ : ℤ) : ℂ :=
  ∫ θ₁ : ℝ, ∫ θ₂ : ℝ,
    varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
      * weylAvg P N α 0 θ₁ θ₂ * ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂))

/-- **The `l₂ = 0` fibre expansion of the concrete kernel**: `hiKconcN` is dominated by the sum
over the exact-height frequencies `α ∈ (ℚ/ℤ)_{l₁}` of the absolute values of the fibre integrands. -/
theorem hiKconcN_fibre_lo2 (ρ : ℝ) (P : Polynomial ℤ) (N l₁ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) :
    ‖hiKconcN ρ P N l₁ 0 k₁ k₂ j₁ j₂‖
      ≤ ∑ α ∈ diffFreqs ρ l₁, ‖fibreInt P N k₁ k₂ α j₁ j₂‖ := by
  rw [hiKconcN_fibre ρ P N l₁ 0 k₁ k₂ j₁ j₂, diffFreqs_zero, Finset.product_eq_sprod,
    Finset.sum_product]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun α _ => ?_)
  rw [Finset.sum_singleton]
  simp only [norm_mul, fourier_norm_one, one_mul]
  rw [fibreInt]

/-- **The per-fibre mass bound of the `l₂ = 0` column** (the analytic core of §6 for the mixed
right case, isolated): for `N ≥ 1`, a period `q` of the non-zero arithmetic frequency `α₁`, the
`ℓ¹(ℤ²)` mass of the Fourier coefficients of `φ_N ⊗ φ̃_N · weylAvg(α₁,0)` is at most
`C·q²(1+S²/N)·2^{k₁+dk₂}/N`. -/
def FibreMassStatement (P : Polynomial ℤ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N q k₁ k₂ : ℕ) (α₁ : Work.Analysis.IonescuWainger.Circle),
      1 ≤ N → 0 < q → q • α₁ = 0 → α₁ ≠ 0 →
      Summable (fun p : ℤ × ℤ => ‖fibreInt P N k₁ k₂ α₁ p.1 p.2‖)
      ∧ (∑' p : ℤ × ℤ, ‖fibreInt P N k₁ k₂ α₁ p.1 p.2‖)
        ≤ C * (q : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
            * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) / (N : ℝ)

/-- **The absorption of the arithmetic factors of the mass bound into `modelWeight`.** -/
def AbsorbStatement (P : Polynomial ℤ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : ℝ, 0 < C ∧
    ∀ (l₁ q k₁ k₂ : ℕ), q ∈ Work.Analysis.IonescuWainger.iwP ρ l₁ →
      ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ) * (q : ℝ) ^ 2
        * (1 + (Work.A7.Sval P k₁ k₂) ^ 2) * (2 : ℝ) ^ (k₁ + P.natDegree * k₂)
      ≤ C * Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂

/-- **The `l₂ = 0` mass bound, conditional on the two analytic inputs.** -/
theorem loMixedRMass_of (P : Polynomial ℤ) (hF : FibreMassStatement P)
    (hAbs : AbsorbStatement P) : LoMixedRMassStatement P := by
  classical
  obtain ⟨Cf, hCfpos, hFb⟩ := hF
  obtain ⟨A, hA0, ρ₀, hρ₀pos, hAb⟩ := hAbs
  have hCf0 : 0 ≤ Cf := hCfpos.le
  refine ⟨A, hA0, min ρ₀ 1, lt_min hρ₀pos one_pos, fun ρ hρ hρmin => ?_⟩
  have hρρ₀ : ρ ≤ ρ₀ := le_trans hρmin (min_le_left _ _)
  have hρ1 : ρ ≤ 1 := le_trans hρmin (min_le_right _ _)
  obtain ⟨Ca, hCapos, hCab⟩ := hAb ρ hρ hρρ₀
  have hCa0 : 0 ≤ Ca := hCapos.le
  refine ⟨fun _ => ⟨Cf * Ca * 100, by positivity⟩, ?_, ?_⟩
  · intro C₀ a l₁ k₁ k₂ n _
    have hz : hiKmod ρ P a l₁ 0 k₁ k₂ n = 0 := hiKmod_lo2 ρ P a l₁ k₁ k₂ n
    rw [hz]
    simp only [Pi.zero_apply, sub_zero]
    exact summable_hiKconc ρ P a l₁ 0 k₁ k₂ n
  · intro C₀ a Λ l₁ k₁ k₂ _ _ ha1 hl₁ n _
    have hz : hiKmod ρ P a l₁ 0 k₁ k₂ n = 0 := hiKmod_lo2 ρ P a l₁ k₁ k₂ n
    have hc : hiKconc ρ P a l₁ 0 k₁ k₂ n = hiKconcN ρ P (Nat.floor (a n)) l₁ 0 k₁ k₂ :=
      hiKconc_eq ρ hρ hρ1 P a l₁ 0 k₁ k₂ n
    rw [hz, hc]
    simp only [Pi.zero_apply, sub_zero]
    set N : ℕ := Nat.floor (a n) with hNdef
    have hNpos : 0 < N := by
      rw [hNdef]
      exact Nat.floor_pos.mpr (by exact_mod_cast ha1 n)
    have hN1 : 1 ≤ N := by omega
    have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    set Γ : Finset Work.Analysis.IonescuWainger.Circle := diffFreqs ρ l₁ with hΓdef
    have hΓsub : ∀ α ∈ Γ, α ∈ iwArithFreqs ρ l₁ :=
      fun α hα => diffFreqs_subset_iwArithFreqs ρ l₁ hα
    have hne : ∀ α ∈ Γ, α ≠ (0 : Work.Analysis.IonescuWainger.Circle) := by
      intro α hα h0
      exact (hΓdef ▸ zero_not_mem_diffFreqs ρ hl₁) (h0 ▸ hα)
    have hqspec : ∀ α ∈ Γ, ∃ q : ℕ, q ∈ iwP ρ l₁ ∧ q • α = 0 :=
      fun α hα => mem_iwArithFreqs.mp (hΓsub α hα)
    let qα : Work.Analysis.IonescuWainger.Circle → ℕ :=
      fun α => if h : α ∈ Γ then (hqspec α h).choose else 1
    have hqα_mem : ∀ α (h : α ∈ Γ), qα α ∈ iwP ρ l₁ := by
      intro α h
      dsimp only [qα]
      rw [dif_pos h]
      exact (hqspec α h).choose_spec.1
    have hqα_smul : ∀ α (h : α ∈ Γ), qα α • α = 0 := by
      intro α h
      dsimp only [qα]
      rw [dif_pos h]
      exact (hqspec α h).choose_spec.2
    set Qmax : ℕ := (iwP ρ l₁).max' ⟨1, one_mem_iwP ρ l₁⟩ with hQmaxdef
    have hqα_le : ∀ α ∈ Γ, qα α ≤ Qmax := by
      intro α hα
      rw [hQmaxdef]
      exact Finset.le_max' _ _ (hqα_mem α hα)
    have hfibMass : ∀ α ∈ Γ,
        Summable (fun p : ℤ × ℤ => ‖fibreInt P N k₁ k₂ α p.1 p.2‖)
        ∧ (∑' p : ℤ × ℤ, ‖fibreInt P N k₁ k₂ α p.1 p.2‖)
          ≤ Cf * (qα α : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
              * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) / (N : ℝ) :=
      fun α hα => hFb N (qα α) k₁ k₂ α hN1 (pos_of_mem_iwP (hqα_mem α hα))
        (hqα_smul α hα) (hne α hα)
    have hstep1 : ∀ α ∈ Γ, (∑' p : ℤ × ℤ, ‖fibreInt P N k₁ k₂ α p.1 p.2‖)
        ≤ Cf * (Qmax : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
            * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) / (N : ℝ) := by
      intro α hα
      refine (hfibMass α hα).2.trans ?_
      have hsq : (qα α : ℝ) ^ 2 ≤ (Qmax : ℝ) ^ 2 := by
        have h : (qα α : ℝ) ≤ (Qmax : ℝ) := by exact_mod_cast hqα_le α hα
        have h0 : (0 : ℝ) ≤ (qα α : ℝ) := by positivity
        nlinarith [h, h0]
      have hK0 : 0 ≤ (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ)) := by positivity
      have h20 : 0 ≤ (2 : ℝ) ^ (k₁ + P.natDegree * k₂) := by positivity
      have hA1 : Cf * (qα α : ℝ) ^ 2 ≤ Cf * (Qmax : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hCf0
      have hA2 : Cf * (qα α : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
          ≤ Cf * (Qmax : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hA1 hK0
      have hA3 : Cf * (qα α : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
            * (2 : ℝ) ^ (k₁ + P.natDegree * k₂)
          ≤ Cf * (Qmax : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
            * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) :=
        mul_le_mul_of_nonneg_right hA2 h20
      exact div_le_div_of_nonneg_right hA3 hNposR.le
    have hstep2 : (∑ α ∈ Γ, Cf * (Qmax : ℝ) ^ 2
          * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
          * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) / (N : ℝ))
        = (Γ.card : ℝ) * (Cf * (Qmax : ℝ) ^ 2
          * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
          * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) / (N : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hQmax_mem : Qmax ∈ iwP ρ l₁ := by
      rw [hQmaxdef]
      exact Finset.max'_mem _ _
    have hstep3 : (Γ.card : ℝ) * (Cf * (Qmax : ℝ) ^ 2
          * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
          * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) / (N : ℝ))
        ≤ Cf * Ca * 100 * Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂ * (N : ℝ)⁻¹ := by
      have hmod0 : 0 ≤ Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂ :=
        Work.KMTAreas.A7.modelWeight_nonneg A ρ hA0 l₁ 0 k₁ k₂
      have hQ0 : 0 ≤ (Qmax : ℝ) ^ 2 := sq_nonneg _
      have hP20 : 0 ≤ (2 : ℝ) ^ (k₁ + P.natDegree * k₂) := by positivity
      have hS20 : 0 ≤ (Work.A7.Sval P k₁ k₂) ^ 2 := sq_nonneg _
      have hS2div : (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ) ≤ (Work.A7.Sval P k₁ k₂) ^ 2 := by
        rw [div_le_iff₀ hNposR]
        nlinarith [hS20, hN1R]
      have h1SN : (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
          ≤ (1 + (Work.A7.Sval P k₁ k₂) ^ 2) := by linarith
      have hGc : (Γ.card : ℝ) ≤ ((iwArithFreqs ρ l₁).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hΓsub
      have hGc0 : (0 : ℝ) ≤ (Γ.card : ℝ) := Nat.cast_nonneg _
      have hIc0 : (0 : ℝ) ≤ ((iwArithFreqs ρ l₁).card : ℝ) := Nat.cast_nonneg _
      have hkey : (Γ.card : ℝ) * (Cf * (Qmax : ℝ) ^ 2
            * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
            * (2 : ℝ) ^ (k₁ + P.natDegree * k₂))
          ≤ Cf * (Ca * Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂) := by
        have hg : (Γ.card : ℝ) * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
            ≤ ((iwArithFreqs ρ l₁).card : ℝ) * (1 + (Work.A7.Sval P k₁ k₂) ^ 2) :=
          mul_le_mul hGc h1SN (by positivity) hIc0
        have e1 : (Γ.card : ℝ) * (Cf * (Qmax : ℝ) ^ 2
              * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
              * (2 : ℝ) ^ (k₁ + P.natDegree * k₂))
            ≤ Cf * ((iwArithFreqs ρ l₁).card : ℝ) * (Qmax : ℝ) ^ 2
              * (1 + (Work.A7.Sval P k₁ k₂) ^ 2)
              * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) := by
          calc (Γ.card : ℝ) * (Cf * (Qmax : ℝ) ^ 2
                * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
                * (2 : ℝ) ^ (k₁ + P.natDegree * k₂))
              = Cf * (Qmax : ℝ) ^ 2 * (2 : ℝ) ^ (k₁ + P.natDegree * k₂)
                * ((Γ.card : ℝ) * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))) := by ring
            _ ≤ Cf * (Qmax : ℝ) ^ 2 * (2 : ℝ) ^ (k₁ + P.natDegree * k₂)
                * (((iwArithFreqs ρ l₁).card : ℝ) * (1 + (Work.A7.Sval P k₁ k₂) ^ 2)) :=
                mul_le_mul_of_nonneg_left hg (by positivity)
            _ = Cf * ((iwArithFreqs ρ l₁).card : ℝ) * (Qmax : ℝ) ^ 2
                * (1 + (Work.A7.Sval P k₁ k₂) ^ 2)
                * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) := by ring
        have e2 : Cf * ((iwArithFreqs ρ l₁).card : ℝ) * (Qmax : ℝ) ^ 2
              * (1 + (Work.A7.Sval P k₁ k₂) ^ 2)
              * (2 : ℝ) ^ (k₁ + P.natDegree * k₂)
            ≤ Cf * (Ca * Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂) := by
          have h := hCab l₁ Qmax k₁ k₂ hQmax_mem
          refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left h hCf0)
          ring
        exact e1.trans e2
      calc (Γ.card : ℝ) * (Cf * (Qmax : ℝ) ^ 2
            * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
            * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) / (N : ℝ))
          = ((Γ.card : ℝ) * (Cf * (Qmax : ℝ) ^ 2
            * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
            * (2 : ℝ) ^ (k₁ + P.natDegree * k₂))) / (N : ℝ) := by ring
        _ ≤ (Cf * (Ca * Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂) * 100) / (N : ℝ) :=
            div_le_div_of_nonneg_right
              (hkey.trans (by
                have h0 : 0 ≤ Cf * (Ca * Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂) :=
                  mul_nonneg hCf0 (mul_nonneg hCa0 hmod0)
                nlinarith [h0])) hNposR.le
        _ = Cf * Ca * 100 * Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂ * (N : ℝ)⁻¹ := by
            rw [div_eq_mul_inv]; ring
    have hstepC : ∀ α ∈ Γ, (∑' p : ℤ × ℤ, ENNReal.ofReal ‖fibreInt P N k₁ k₂ α p.1 p.2‖)
        = ENNReal.ofReal (∑' p : ℤ × ℤ, ‖fibreInt P N k₁ k₂ α p.1 p.2‖) :=
      fun α hα => (ENNReal.ofReal_tsum_of_nonneg (fun p => norm_nonneg _) (hfibMass α hα).1).symm
    have hstepB : (∑' p : ℤ × ℤ, ∑ α ∈ Γ, ENNReal.ofReal ‖fibreInt P N k₁ k₂ α p.1 p.2‖)
        = ∑ α ∈ Γ, ∑' p : ℤ × ℤ, ENNReal.ofReal ‖fibreInt P N k₁ k₂ α p.1 p.2‖ :=
      Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
    have hbig : (∑' p : ℤ × ℤ, ENNReal.ofReal ‖hiKconcN ρ P N l₁ 0 k₁ k₂ p.1 p.2‖)
        ≤ ENNReal.ofReal (Cf * Ca * 100 * Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂
            * (N : ℝ)⁻¹) := by
      calc (∑' p : ℤ × ℤ, ENNReal.ofReal ‖hiKconcN ρ P N l₁ 0 k₁ k₂ p.1 p.2‖)
          ≤ ∑' p : ℤ × ℤ, ∑ α ∈ Γ, ENNReal.ofReal ‖fibreInt P N k₁ k₂ α p.1 p.2‖ := by
            refine ENNReal.tsum_le_tsum (fun p => ?_)
            refine le_trans (ENNReal.ofReal_le_ofReal
              (hiKconcN_fibre_lo2 ρ P N l₁ k₁ k₂ p.1 p.2)) ?_
            rw [ENNReal.ofReal_sum_of_nonneg (fun α _ => norm_nonneg _)]
        _ = ∑ α ∈ Γ, ∑' p : ℤ × ℤ, ENNReal.ofReal ‖fibreInt P N k₁ k₂ α p.1 p.2‖ := hstepB
        _ = ∑ α ∈ Γ, ENNReal.ofReal (∑' p : ℤ × ℤ, ‖fibreInt P N k₁ k₂ α p.1 p.2‖) :=
            Finset.sum_congr rfl (fun α hα => hstepC α hα)
        _ = ENNReal.ofReal (∑ α ∈ Γ, ∑' p : ℤ × ℤ, ‖fibreInt P N k₁ k₂ α p.1 p.2‖) :=
            (ENNReal.ofReal_sum_of_nonneg (fun α _ =>
              tsum_nonneg (fun p => norm_nonneg _))).symm
        _ ≤ ENNReal.ofReal (Cf * Ca * 100 * Work.KMTAreas.A7.modelWeight A ρ l₁ 0 k₁ k₂
              * (N : ℝ)⁻¹) := by
            refine ENNReal.ofReal_le_ofReal ?_
            exact (Finset.sum_le_sum hstep1).trans (hstep2.le.trans hstep3)
    have hsumKc : Summable (fun p : ℤ × ℤ => ‖hiKconcN ρ P N l₁ 0 k₁ k₂ p.1 p.2‖) := by
      have hne : (∑' p : ℤ × ℤ, ENNReal.ofReal ‖hiKconcN ρ P N l₁ 0 k₁ k₂ p.1 p.2‖) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbig
      have h1 := ENNReal.summable_toReal (f := fun p : ℤ × ℤ =>
        ENNReal.ofReal ‖hiKconcN ρ P N l₁ 0 k₁ k₂ p.1 p.2‖) hne
      simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using h1
    refine (ENNReal.ofReal_le_ofReal_iff ?_).mp ?_
    · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCf0 hCa0)
        (by norm_num)) (Work.KMTAreas.A7.modelWeight_nonneg A ρ hA0 l₁ 0 k₁ k₂))
        (inv_nonneg.mpr hNposR.le)
    · rw [ENNReal.ofReal_tsum_of_nonneg (fun p => norm_nonneg _) hsumKc]
      exact hbig

end
end Work.KMTAreas.A7
