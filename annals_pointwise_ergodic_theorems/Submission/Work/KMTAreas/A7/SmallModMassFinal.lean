import Mathlib
import Submission.Work.KMTAreas.A5.fourierCoeff_mul_eq_tsum_conv
import Submission.Work.KMTAreas.A7.SmallModReduction
import Submission.Work.KMTAreas.A7.arithSymbMeasBdd
import Submission.Work.KMTAreas.A7.goodRegime
import Submission.Work.KMTAreas.A7.integrable_iwSymbolSet_varphiN
import Submission.Work.KMTAreas.A7.m0_period_indep
import Submission.Work.KMTAreas.A7.mass_fourier_le
import Submission.Work.KMTAreas.A7.smallCond_bad_bounded
import Submission.Work.KMTAreas.A7.spikeSymbMeasBdd
import Submission.Work.KMTAreas.A7.spike_profile_bounds_q
import Submission.Work.KMTAreas.A7.spike_sum_weight
import Submission.Work.KMTAreas.A7c.SpikeCollapse
import Submission.Work.KMTPlan.A6.vpc_exists_cw_mStarF_tsum_le
import Submission.Work.KMTAreas.A7.fold_lift_prod

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7z

open Work.KMTAreas.A7 Work.Analysis.IonescuWainger

theorem diffFreqs_subset_iwArithFreqs {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l L : ℕ}
    (hl : l ≤ L) : diffFreqs ρ l ⊆ iwArithFreqs ρ L :=
  Work.KMTAreas.A7.diffFreqs_subset_iwArithFreqs_le hρ hρ1 hl

end Work.KMTAreas.A7z

namespace Work.KMTAreas.A7z
open Work.KMTAreas.A7 Work.KMTAreas.A7.Cpy

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

/-- **The coefficients of the exact-height Ionescu--Wainger kernel `tmKernel`.**

For an integrable symbol `φ`, the `j`-th Fourier coefficient of the exact-height IW kernel
`tmKernel ρ l φ = iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize φ))` factors as the arithmetic
character sum `∑_{α ∈ (ℚ/ℤ)_l} e(-jα)` times the continuous Fourier transform `cw φ j`.  This is
`Work.KMTPlan.A6.IwKernelArithChar` specialised to the exact-height frequency set `diffFreqs ρ l`. -/
lemma tmKernel_coeff {φ : ℝ → ℂ} (hφ : Integrable φ) (ρ : ℝ) (l : ℕ) (j : ℤ) :
    tmKernel ρ l φ j = (∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α) * cw φ j := by
  simpa only [tmKernel] using
    Work.KMTPlan.A6.IwKernelArithChar (diffFreqs ρ l) hφ j

/-- **The composition of the halved-average kernel with two convolution kernels.**

The bilinear kernel `kernComp (khalf m P) κ κ'` has the `b`-sum collapsing to the single value
`b' = b - P.eval (a - a')` (because `khalf m P x y = 0` unless `y = P.eval x`), and then the
`a`-sum to the finite set of shifts `a - n`, `n ∈ Ioc (m/2) m`, on which `khalf` equals `m⁻¹`. -/
lemma kernComp_khalf (m : ℕ) (P : ℤ[X]) (κ κ' : ℤ → ℂ) (a b : ℤ) :
    kernComp (khalf m P) κ κ' a b
      = ((m : ℂ))⁻¹ * ∑ n ∈ Finset.Ioc (m / 2) m,
          κ (a - (n : ℤ)) * κ' (b - P.eval (n : ℤ)) := by
  rw [kernComp]
  -- collapse the inner `b`-sum to the single shift `b' = b - P.eval (a - a')`
  have hinner : ∀ a' : ℤ,
      (∑' b' : ℤ, khalf m P (a - a') (b - b') * κ a' * κ' b')
        = khalf m P (a - a') (P.eval (a - a')) * κ a' * κ' (b - P.eval (a - a')) := by
    intro a'
    refine (tsum_eq_single (b - P.eval (a - a')) ?_).trans ?_
    · intro b' hb'
      have hne : ¬ (b - b' = P.eval (a - a')) := fun h => hb' (by omega)
      rw [khalf, if_neg (fun hc => hne hc.2.2)]
      ring
    · have h : b - (b - P.eval (a - a')) = P.eval (a - a') := by omega
      rw [h]
  simp_rw [hinner]
  -- reindex the outer sum by the shift `z = a - a'`
  have hreindex :
      (∑' a' : ℤ, khalf m P (a - a') (P.eval (a - a')) * κ a' * κ' (b - P.eval (a - a')))
        = ∑' z : ℤ, khalf m P z (P.eval z) * κ (a - z) * κ' (b - P.eval z) := by
    rw [(Equiv.tsum_eq (Equiv.subLeft a)
      (fun a' : ℤ => khalf m P (a - a') (P.eval (a - a')) * κ a' * κ' (b - P.eval (a - a')))).symm]
    refine tsum_congr (fun z => ?_)
    have h : a - (a - z) = z := by omega
    simp only [Equiv.subLeft_apply, h]
  rw [hreindex]
  -- the resulting family is supported on `{a - n : n ∈ Ioc (m/2) m}`
  rw [tsum_eq_sum (s := (Finset.Ioc (m / 2) m).map ⟨(↑· : ℕ → ℤ), Nat.cast_injective⟩)]
  · rw [Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn' : m / 2 < n ∧ n ≤ m := Finset.mem_Ioc.mp hn
    have hk : khalf m P (n : ℤ) (P.eval (n : ℤ)) = ((m : ℂ))⁻¹ := by
      have hc : (↑m : ℤ) / 2 < (↑n : ℤ) ∧ (↑n : ℤ) ≤ (↑m : ℤ)
          ∧ P.eval (↑n) = P.eval (↑n) := by
        refine ⟨?_, ?_, rfl⟩
        · have h1 : (↑m : ℤ) / 2 = ((m / 2 : ℕ) : ℤ) := by
            rw [eq_comm, Int.natCast_div]; norm_num
          rw [h1]; exact_mod_cast hn'.1
        · exact_mod_cast hn'.2
      rw [khalf, if_pos hc]
    change khalf m P (n : ℤ) (P.eval (n : ℤ)) * κ (a - (n : ℤ)) * κ' (b - P.eval (n : ℤ))
        = ((m : ℂ))⁻¹ * (κ (a - (n : ℤ)) * κ' (b - P.eval (n : ℤ)))
    rw [hk]
    ring
  · intro z hz
    by_cases h : (↑m : ℤ) / 2 < z ∧ z ≤ (↑m : ℤ)
    · exfalso
      apply hz
      refine Finset.mem_map.mpr ⟨z.toNat, ?_, ?_⟩
      · rw [Finset.mem_Ioc, Int.lt_toNat, Int.natCast_div, Int.toNat_le]
        exact h
      · have h0 : (0 : ℤ) ≤ z :=
          le_of_lt (lt_of_le_of_lt (Int.ediv_nonneg (Int.natCast_nonneg m) (by norm_num)) h.1)
        exact Int.toNat_of_nonneg h0
    · rw [khalf, if_neg (fun hc => h ⟨hc.1, hc.2.1⟩)]
      ring

theorem smallKconc_coeff (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) (a b : ℤ) :
    Work.KMTAreas.A7.smallKconc ρ P l₁ l₂ k₁ k₂ N a b
      = ((N : ℂ))⁻¹ * ∑ m ∈ Finset.Ioc (N / 2) N,
          ((∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₁, fourier (T := 1) (-(a - (m : ℤ))) α)
              * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiN N k₁) (a - (m : ℤ)))
          * ((∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₂, fourier (T := 1) (-(b - P.eval (m : ℤ))) α)
              * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeN P.natDegree N k₂) (b - P.eval (m : ℤ))) := by
  rw [smallKconc, kernComp_khalf]
  refine congrArg (fun z : ℂ => ((N : ℂ))⁻¹ * z) ?_
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have h1 : tmKernel ρ l₁ (varphiN N k₁) (a - (m : ℤ))
      = (∑ α ∈ diffFreqs ρ l₁, fourier (T := 1) (-(a - (m : ℤ))) α)
          * cw (varphiN N k₁) (a - (m : ℤ)) :=
    tmKernel_coeff (integrable_varphiN N k₁) ρ l₁ (a - (m : ℤ))
  have h2 : tmKernel ρ l₂ (varphitildeN P.natDegree N k₂) (b - P.eval (m : ℤ))
      = (∑ α ∈ diffFreqs ρ l₂, fourier (T := 1) (-(b - P.eval (m : ℤ))) α)
          * cw (varphitildeN P.natDegree N k₂) (b - P.eval (m : ℤ)) :=
    tmKernel_coeff (integrable_varphitildeN_aux P.natDegree N k₂) ρ l₂ (b - P.eval (m : ℤ))
  rw [h1, h2]

end

end Work.KMTAreas.A7z

namespace Work.KMTAreas.A7z
open Work.KMTAreas.A7 Work.KMTAreas.A7.Cpy

open MeasureTheory

/-- **The composed kernel as an iterated sum in "translated" form.**  Reindexing the defining
iterated sum `∑' a', ∑' b', K (a - a') (b - b') * κ a' * κ' b'` of `kernComp` by the bijections
`j₁ ↦ a - j₁`, `j₂ ↦ b - j₂` of `ℤ` gives

`kernComp K κ κ' a b = ∑' j₁, ∑' j₂, K j₁ j₂ * κ (a - j₁) * κ' (b - j₂)`.

(The reindexing is *unconditional*: `Equiv.tsum_eq` requires no summability hypothesis.) -/
theorem kernComp_eq_iter (K : ℤ → ℤ → ℂ) (κ κ' : ℤ → ℂ) (a b : ℤ) :
    kernComp K κ κ' a b = ∑' j₁ : ℤ, ∑' j₂ : ℤ, K j₁ j₂ * κ (a - j₁) * κ' (b - j₂) := by
  rw [kernComp]
  rw [← Equiv.tsum_eq (Equiv.subLeft a)
    (fun a' => ∑' b' : ℤ, K (a - a') (b - b') * κ a' * κ' b')]
  refine tsum_congr (fun j₁ => ?_)
  simp only [Equiv.subLeft_apply, sub_sub_self]
  rw [← Equiv.tsum_eq (Equiv.subLeft b)
    (fun b' => K j₁ (b - b') * κ (a - j₁) * κ' b')]
  refine tsum_congr (fun j₂ => ?_)
  simp only [Equiv.subLeft_apply, sub_sub_self]

/-- The arithmetic-character identity `Work.KMTPlan.A6.IwKernelArithChar` in the form of the
exact-height Ionescu--Wainger kernel `tmKernel` used in §6: for an integrable symbol `φ`,

`tmKernel ρ l φ j = (∑_{α ∈ (ℚ/ℤ)_l} e(-jα)) · cw φ j`. -/
theorem tmKernel_eq (ρ : ℝ) (l : ℕ) {φ : ℝ → ℂ} (hφ : Integrable φ) (j : ℤ) :
    tmKernel ρ l φ j = (∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α) * cw φ j :=
  Work.KMTPlan.A6.IwKernelArithChar (diffFreqs ρ l) hφ j

/-- The instance of `tmKernel_eq` for the modulated bump `φ_{N,t}`. -/
theorem tmKernel_varphiNt (ρ : ℝ) (l N k : ℕ) (t : ℝ) (j : ℤ) :
    tmKernel ρ l (varphiNt N k t) j
      = (∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α) * cw (varphiNt N k t) j :=
  tmKernel_eq ρ l (integrable_varphiNt N k t) j

/-- The instance of `tmKernel_eq` for the modulated bump `φ̃_{N,t}`. -/
theorem tmKernel_varphitildeNt (ρ : ℝ) (P : Polynomial ℤ) (l N k : ℕ) (t : ℝ) (j : ℤ) :
    tmKernel ρ l (varphitildeNt P P.natDegree N k t) j
      = (∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α)
          * cw (varphitildeNt P P.natDegree N k t) j :=
  tmKernel_eq ρ l (integrable_varphitildeNt_aux P P.natDegree N k t) j

theorem smallKmod_coeff (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) (a b : ℤ) :
    Work.KMTAreas.A7.smallKmod ρ P l₁ l₂ k₁ k₂ N a b
      = ∫ t in (1 / 2 : ℝ)..1, ∑' j₁ : ℤ, ∑' j₂ : ℤ,
          (Work.KMTAreas.A7.smallArithKernel ρ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂
            * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂))) j₁
            * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂))) j₂)
          * ((∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₁, fourier (T := 1) (-(a - j₁)) α)
              * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiNt N k₁ t) (a - j₁))
          * ((∑ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₂, fourier (T := 1) (-(b - j₂)) α)
              * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t) (b - j₂)) := by
  rw [smallKmod]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [kernComp_eq_iter]
  refine tsum_congr (fun j₁ => ?_)
  refine tsum_congr (fun j₂ => ?_)
  rw [tmKernel_varphiNt ρ l₁ N k₁ t (a - j₁),
      tmKernel_varphitildeNt ρ P l₂ N k₂ t (b - j₂)]

end Work.KMTAreas.A7z

namespace Work.KMTAreas.A7.Cpz
open Work.KMTAreas.A7 Work.KMTAreas.A7z Work.KMTAreas.A7.Cpy

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

local notation "Circ" => AddCircle (1 : ℝ)

/-- The characters of the circle have modulus one. -/
lemma fourier_norm_eq_one (n : ℤ) (θ : Circ) : ‖fourier (T := 1) n θ‖ = 1 := by
  rw [fourier_apply]
  exact _root_.Circle.norm_coe _

/-- The `n`-th Fourier coefficient of `Ψ`, as an integral against `fourier n`. -/
lemma integral_mul_fourier (Ψ : Circ → ℂ) (n : ℤ) :
    ∫ θ : Circ, Ψ θ * fourier (T := 1) n θ ∂circleMeasure = iwKernel Ψ (-n) := by
  rw [iwKernel, fourierCoeff]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only [smul_eq_mul, neg_neg]
  exact mul_comm _ _

/-- Integrability of `Ψ · fourier n` for an integrable `Ψ`. -/
lemma integrable_mul_fourier {Ψ : Circ → ℂ} (hΨ : Integrable Ψ circleMeasure) (n : ℤ) :
    Integrable (fun θ : Circ => Ψ θ * fourier (T := 1) n θ) circleMeasure := by
  have hb : ∀ᵐ θ ∂circleMeasure, ‖fourier (T := 1) n θ‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall fun θ => le_of_eq (fourier_norm_eq_one n θ)
  refine (hΨ.bdd_mul (fourier (T := 1) n).continuous.aestronglyMeasurable hb).congr ?_
  filter_upwards with θ
  exact mul_comm _ _

/-- Integrability of `Ψ · fourier n · fourier k` for an integrable `Ψ`. -/
lemma integrable_mul_fourier_mul_fourier {Ψ : Circ → ℂ} (hΨ : Integrable Ψ circleMeasure)
    (n k : ℤ) :
    Integrable (fun θ : Circ => Ψ θ * fourier (T := 1) n θ * fourier (T := 1) k θ)
      circleMeasure := by
  refine (integrable_mul_fourier hΨ (n + k)).congr (Filter.Eventually.of_forall fun θ => ?_)
  beta_reduce
  rw [fourier_add, mul_assoc]

private lemma norm_varphitildeN_le_two (d N k : ℕ) (x : ℝ) : ‖varphitildeN d N k x‖ ≤ 2 := by
  rw [varphitildeN]
  split_ifs with hk
  · exact le_trans (Work.KMTContract.norm_kmtEta_le _) (by norm_num)
  · calc ‖Work.KMTContract.kmtEta
              ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * x)
            - Work.KMTContract.kmtEta
              ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * x)‖
        ≤ ‖Work.KMTContract.kmtEta
              ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * x)‖
          + ‖Work.KMTContract.kmtEta
              ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * x)‖ :=
          norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (Work.KMTContract.norm_kmtEta_le _)
          (Work.KMTContract.norm_kmtEta_le _)
      _ = 2 := by norm_num

private lemma integrable_varphitildeN_symb (ρ : ℝ) (P : Polynomial ℤ) (l N k : ℕ) :
    Integrable (iwSymbolSet (diffFreqs ρ l) (periodize (varphitildeN P.natDegree N k)))
      circleMeasure := by
  obtain ⟨R₀, hR₀⟩ :=
    exists_abs_le_of_hasCompactSupport (hasCompactSupport_varphitildeN P.natDegree N k)
  refine (memLp_iwSymbolSet (diffFreqs ρ l)
    (memLp_periodize (φ := varphitildeN P.natDegree N k) (R := max R₀ 0) (C := 2)
      (contDiff_varphitildeN P.natDegree N k).continuous.measurable (le_max_right R₀ 0) ?_ ?_)
    ).integrable le_top
  · intro x hx
    exact hR₀ x (le_of_lt (lt_of_le_of_lt (le_max_left R₀ 0) hx))
  · intro x
    exact norm_varphitildeN_le_two P.natDegree N k x

/-- `∫ θ, Ψ θ · e(nθ) · e(-aθ)` for `Ψ` the `varphiN`-symbol. -/
lemma integral_symb_fourier_varphiN (ρ : ℝ) (l N k : ℕ) (n a : ℤ) :
    (∫ θ : Circ, iwSymbolSet (diffFreqs ρ l) (periodize (varphiN N k)) θ
        * fourier (T := 1) n θ * fourier (T := 1) (-a) θ ∂circleMeasure)
      = (∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-(a - n)) α) * cw (varphiN N k) (a - n) := by
  have h1 : (∫ θ : Circ, iwSymbolSet (diffFreqs ρ l) (periodize (varphiN N k)) θ
        * fourier (T := 1) n θ * fourier (T := 1) (-a) θ ∂circleMeasure)
      = ∫ θ : Circ, iwSymbolSet (diffFreqs ρ l) (periodize (varphiN N k)) θ
          * fourier (T := 1) (n - a) θ ∂circleMeasure := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    have h2 : fourier (T := 1) (n - a) θ
        = fourier (T := 1) n θ * fourier (T := 1) (-a) θ := by
      rw [show n - a = n + (-a) from by ring, fourier_add]
    beta_reduce
    rw [h2]; ring
  rw [h1, integral_mul_fourier]
  rw [show -(n - a) = a - n from by ring]
  exact tmKernel_coeff (integrable_varphiN N k) ρ l (a - n)

/-- `∫ θ, Ψ θ · e(nθ) · e(-bθ)` for `Ψ` the `varphitildeN`-symbol. -/
lemma integral_symb_fourier_varphitildeN (ρ : ℝ) (P : Polynomial ℤ) (l N k : ℕ) (n b : ℤ) :
    (∫ θ : Circ, iwSymbolSet (diffFreqs ρ l) (periodize (varphitildeN P.natDegree N k)) θ
        * fourier (T := 1) n θ * fourier (T := 1) (-b) θ ∂circleMeasure)
      = (∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-(b - n)) α)
          * cw (varphitildeN P.natDegree N k) (b - n) := by
  have h1 : (∫ θ : Circ, iwSymbolSet (diffFreqs ρ l) (periodize (varphitildeN P.natDegree N k)) θ
        * fourier (T := 1) n θ * fourier (T := 1) (-b) θ ∂circleMeasure)
      = ∫ θ : Circ, iwSymbolSet (diffFreqs ρ l) (periodize (varphitildeN P.natDegree N k)) θ
          * fourier (T := 1) (n - b) θ ∂circleMeasure := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    have h2 : fourier (T := 1) (n - b) θ
        = fourier (T := 1) n θ * fourier (T := 1) (-b) θ := by
      rw [show n - b = n + (-b) from by ring, fourier_add]
    beta_reduce
    rw [h2]; ring
  rw [h1, integral_mul_fourier]
  rw [show -(n - b) = b - n from by ring]
  exact tmKernel_coeff (integrable_varphitildeN_aux P.natDegree N k) ρ l (b - n)

/-- The scalar-prefactored `varphiN`-integral. -/
lemma integral_const_symb_varphiN (ρ : ℝ) (l N k : ℕ) (n a : ℤ) :
    (∫ θ : Circ, ((N : ℂ))⁻¹ * (iwSymbolSet (diffFreqs ρ l) (periodize (varphiN N k)) θ
        * fourier (T := 1) n θ) * fourier (T := 1) (-a) θ ∂circleMeasure)
      = ((N : ℂ))⁻¹ * ((∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-(a - n)) α)
          * cw (varphiN N k) (a - n)) := by
  rw [show (∫ θ : Circ, ((N : ℂ))⁻¹ * (iwSymbolSet (diffFreqs ρ l) (periodize (varphiN N k)) θ
        * fourier (T := 1) n θ) * fourier (T := 1) (-a) θ ∂circleMeasure)
      = ∫ θ : Circ, ((N : ℂ))⁻¹ * (iwSymbolSet (diffFreqs ρ l) (periodize (varphiN N k)) θ
        * fourier (T := 1) n θ * fourier (T := 1) (-a) θ) ∂circleMeasure from
    integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)]
  rw [integral_const_mul]
  congr 1
  exact integral_symb_fourier_varphiN ρ l N k n a

/-- **`coeff` of a finite sum of rank-one symbols.** -/
lemma coeff_finset_sum_sep {ι : Type*} (s : Finset ι) (A B : ι → Circ → ℂ) (a b : ℤ)
    (hA : ∀ m ∈ s, Integrable (fun θ : Circ => A m θ * fourier (T := 1) (-a) θ) circleMeasure)
    (hB : ∀ m ∈ s, Integrable (fun θ : Circ => B m θ * fourier (T := 1) (-b) θ) circleMeasure) :
    coeff (fun θ₁ θ₂ => ∑ m ∈ s, A m θ₁ * B m θ₂) a b
      = ∑ m ∈ s, (∫ θ : Circ, A m θ * fourier (T := 1) (-a) θ ∂circleMeasure)
          * (∫ θ : Circ, B m θ * fourier (T := 1) (-b) θ ∂circleMeasure) := by
  rw [coeff]
  trans ∫ θ₁ : Circ, ∑ m ∈ s, (A m θ₁ * fourier (T := 1) (-a) θ₁)
      * (∫ θ₂ : Circ, B m θ₂ * fourier (T := 1) (-b) θ₂ ∂circleMeasure) ∂circleMeasure
  · refine integral_congr_ae (Filter.Eventually.of_forall fun θ₁ => ?_)
    trans ∫ θ₂ : Circ, ∑ m ∈ s, (A m θ₁ * fourier (T := 1) (-a) θ₁)
        * (B m θ₂ * fourier (T := 1) (-b) θ₂) ∂circleMeasure
    · refine integral_congr_ae (Filter.Eventually.of_forall fun θ₂ => ?_)
      beta_reduce
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by ring
    · rw [MeasureTheory.integral_finsetSum s (fun m hm => (hB m hm).const_mul _)]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [integral_const_mul]
  · rw [MeasureTheory.integral_finsetSum s (fun m hm => (hA m hm).mul_const _)]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [integral_mul_const]

/-- The symbol `concSymb` of the concrete kernel as a finite rank-one sum. -/
lemma concSymb_eq_sum (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) :
    concSymb ρ P l₁ l₂ k₁ k₂ N
      = fun θ₁ θ₂ : Circ => ∑ m ∈ Finset.Ioc (N / 2) N,
          (((N : ℂ))⁻¹ * (iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiN N k₁)) θ₁
              * fourier (T := 1) (m : ℤ) θ₁))
            * (iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeN P.natDegree N k₂)) θ₂
                * fourier (T := 1) (P.eval (m : ℤ)) θ₂) := by
  funext θ₁ θ₂
  simp only [concSymb, avgSymb]
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- **The concrete kernel is the double Fourier coefficient of its symbol.** -/
lemma coeff_concSymb (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) (a b : ℤ) :
    coeff (concSymb ρ P l₁ l₂ k₁ k₂ N) a b
      = ((N : ℂ))⁻¹ * ∑ m ∈ Finset.Ioc (N / 2) N,
          ((∑ α ∈ diffFreqs ρ l₁, fourier (T := 1) (-(a - (m : ℤ))) α)
              * cw (varphiN N k₁) (a - (m : ℤ)))
          * ((∑ α ∈ diffFreqs ρ l₂, fourier (T := 1) (-(b - P.eval (m : ℤ))) α)
              * cw (varphitildeN P.natDegree N k₂) (b - P.eval (m : ℤ))) := by
  rw [concSymb_eq_sum]
  rw [coeff_finset_sum_sep (Finset.Ioc (N / 2) N)
    (fun m θ => ((N : ℂ))⁻¹ * (iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiN N k₁)) θ
        * fourier (T := 1) (m : ℤ) θ))
    (fun m θ => iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeN P.natDegree N k₂)) θ
        * fourier (T := 1) (P.eval (m : ℤ)) θ) a b ?_ ?_]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_const_symb_varphiN ρ l₁ N k₁ (m : ℤ) a,
      integral_symb_fourier_varphitildeN ρ P l₂ N k₂ (P.eval (m : ℤ)) b]
    ring
  · intro m hm
    refine ((integrable_mul_fourier_mul_fourier
      (integrable_iwSymbolSet_varphiN ρ l₁ N k₁) (m : ℤ) (-a)).const_mul
        ((N : ℂ))⁻¹).congr (Filter.Eventually.of_forall fun θ => ?_)
    ring
  · intro m hm
    exact integrable_mul_fourier_mul_fourier (integrable_varphitildeN_symb ρ P l₂ N k₂)
      (P.eval (m : ℤ)) (-b)

end

theorem smallKconc_eq_coeff (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) (a b : ℤ) :
    Work.KMTAreas.A7.smallKconc ρ P l₁ l₂ k₁ k₂ N a b
      = Work.KMTAreas.A7.coeff (Work.KMTAreas.A7.concSymb ρ P l₁ l₂ k₁ k₂ N) a b := by
  rw [smallKconc_coeff]
  exact (coeff_concSymb ρ P l₁ l₂ k₁ k₂ N a b).symm

end Work.KMTAreas.A7.Cpz


namespace Work.KMTAreas.A7.Cpz
open Work.KMTAreas.A7 Work.KMTAreas.A7z Work.KMTAreas.A7.Cpy

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## 1. Finiteness criteria for the kernel mass -/

/-- **Finiteness criterion.** The extended-real `ℓ¹(ℤ²)`-mass `smKernMass K` is finite precisely
when the real-valued `ℓ¹`-norm of `K` is summable. -/
theorem smKernMass_ne_top_iff_summable (K : ℤ → ℤ → ℂ) :
    smKernMass K ≠ ⊤ ↔ Summable (fun p : ℤ × ℤ => ‖K p.1 p.2‖) := by
  have h1 : smKernMass K = ∑' p : ℤ × ℤ, ((‖K p.1 p.2‖₊ : ℝ≥0) : ℝ≥0∞) := rfl
  rw [h1, ENNReal.tsum_coe_ne_top_iff_summable]
  constructor
  · intro h
    have h' : Summable fun p : ℤ × ℤ => ((‖K p.1 p.2‖₊ : ℝ≥0) : ℝ) := NNReal.summable_coe.mpr h
    simpa using h'
  · intro h
    have h' : Summable fun p : ℤ × ℤ => ((‖K p.1 p.2‖₊ : ℝ≥0) : ℝ) := by simpa using h
    exact NNReal.summable_coe.mp h'

/-- The finite-mass statement in the form in which the §6 estimates produce it. -/
theorem smKernMass_ne_top_of_summable {K : ℤ → ℤ → ℂ}
    (h : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) : smKernMass K ≠ ⊤ :=
  (smKernMass_ne_top_iff_summable K).mpr h

/-- The extended-real mass of a summable kernel is the coercion of its real `ℓ¹`-norm. -/
theorem smKernMass_eq_ofReal_tsum {K : ℤ → ℤ → ℂ}
    (h : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) :
    smKernMass K = ENNReal.ofReal (∑' p : ℤ × ℤ, ‖K p.1 p.2‖) := by
  have hnn : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖₊ :=
    NNReal.summable_coe.mp (by simpa using h)
  have hcoe : ((∑' p : ℤ × ℤ, ‖K p.1 p.2‖₊ : ℝ≥0) : ℝ) = ∑' p : ℤ × ℤ, ‖K p.1 p.2‖ := by
    rw [NNReal.coe_tsum]
    exact tsum_congr fun p => by simp
  calc smKernMass K = (↑(∑' p : ℤ × ℤ, ‖K p.1 p.2‖₊) : ℝ≥0∞) := by
        rw [show smKernMass K = ∑' p : ℤ × ℤ, ((‖K p.1 p.2‖₊ : ℝ≥0) : ℝ≥0∞) from rfl,
          ENNReal.coe_tsum hnn]
    _ = ENNReal.ofReal (∑' p : ℤ × ℤ, ‖K p.1 p.2‖) := by
        rw [← hcoe, ENNReal.ofReal_coe_nnreal]

/-- A bound on the real `ℓ¹`-norm gives a bound on the extended-real mass. -/
theorem smKernMass_le_ofReal_tsum {K : ℤ → ℤ → ℂ} {B : ℝ}
    (h : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖)
    (hB : (∑' p : ℤ × ℤ, ‖K p.1 p.2‖) ≤ B) :
    smKernMass K ≤ ENNReal.ofReal B :=
  (le_of_eq (smKernMass_eq_ofReal_tsum h)).trans (ENNReal.ofReal_le_ofReal hB)

/-- **The mass of a product kernel.** -/
theorem smKernMass_prod_le {f g : ℤ → ℂ}
    (hf : Summable fun x : ℤ => ‖f x‖) (hg : Summable fun y : ℤ => ‖g y‖) :
    smKernMass (fun a b : ℤ => f a * g b)
      ≤ ENNReal.ofReal ((∑' x : ℤ, ‖f x‖) * (∑' y : ℤ, ‖g y‖)) := by
  have hsum : Summable fun p : ℤ × ℤ => ‖f p.1 * g p.2‖ := hf.mul_norm hg
  have hfg : Summable fun p : ℤ × ℤ => ‖f p.1‖ * ‖g p.2‖ :=
    hf.mul_of_nonneg hg (fun x => norm_nonneg _) (fun y => norm_nonneg _)
  refine smKernMass_le_ofReal_tsum hsum ?_
  calc (∑' p : ℤ × ℤ, ‖f p.1 * g p.2‖) ≤ ∑' p : ℤ × ℤ, ‖f p.1‖ * ‖g p.2‖ :=
        Summable.tsum_le_tsum (fun p => norm_mul_le _ _) hsum hfg
    _ = (∑' x : ℤ, ‖f x‖) * (∑' y : ℤ, ‖g y‖) :=
        (tsum_mul_tsum_of_summable_norm (f := fun x : ℤ => ‖f x‖)
          (g := fun y : ℤ => ‖g y‖) (by simpa using hf) (by simpa using hg)).symm

/-- Interchange of an `ℝ≥0∞`-valued sum with a finite sum. -/
theorem tsum_finset_sum_enorm {ι α : Type*} (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    (∑' a, ∑ i ∈ s, f i a) = ∑ i ∈ s, ∑' a, f i a := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, ← ih, ← ENNReal.tsum_add]
      exact tsum_congr fun a => Finset.sum_insert hi

/-- **The mass of a finite sum of kernels.** -/
theorem smKernMass_finset_sum_le {ι : Type*} (s : Finset ι) (F : ι → ℤ → ℤ → ℂ) (B : ι → ℝ)
    (hB : ∀ i ∈ s, 0 ≤ B i) (h : ∀ i ∈ s, smKernMass (F i) ≤ ENNReal.ofReal (B i)) :
    smKernMass (fun a b => ∑ i ∈ s, F i a b) ≤ ENNReal.ofReal (∑ i ∈ s, B i) := by
  rw [smKernMass]
  calc (∑' p : ℤ × ℤ, ‖∑ i ∈ s, F i p.1 p.2‖ₑ)
      ≤ ∑' p : ℤ × ℤ, ∑ i ∈ s, ‖F i p.1 p.2‖ₑ :=
        ENNReal.tsum_le_tsum fun p : ℤ × ℤ => enorm_sum_le s fun i => F i p.1 p.2
    _ = ∑ i ∈ s, ∑' p : ℤ × ℤ, ‖F i p.1 p.2‖ₑ :=
        tsum_finset_sum_enorm s fun i (p : ℤ × ℤ) => ‖F i p.1 p.2‖ₑ
    _ = ∑ i ∈ s, smKernMass (F i) := rfl
    _ ≤ ∑ i ∈ s, ENNReal.ofReal (B i) := Finset.sum_le_sum h
    _ = ENNReal.ofReal (∑ i ∈ s, B i) := (ENNReal.ofReal_sum_of_nonneg hB).symm

/-- **Finiteness of the mass of a `cw`-dominated kernel.**  If `‖K j₁ j₂‖` is dominated by
`B · ‖cw m₁ j₁‖ · ‖cw m₂ j₂‖` with the two coefficient families `ℓ¹`, then the mass of `K` is
bounded by `B (∑_j ‖cw m₁ j‖)(∑_j ‖cw m₂ j‖)`. -/
theorem smKernMass_le_of_cw_dominated {K : ℤ → ℤ → ℂ} {m₁ m₂ : ℝ → ℂ} {B : ℝ}
    (h : ∀ j₁ j₂ : ℤ, ‖K j₁ j₂‖ ≤ B * ‖cw m₁ j₁‖ * ‖cw m₂ j₂‖)
    (h₁ : Summable fun j : ℤ => ‖cw m₁ j‖) (h₂ : Summable fun j : ℤ => ‖cw m₂ j‖) :
    smKernMass K ≤ ENNReal.ofReal (B * (∑' j : ℤ, ‖cw m₁ j‖) * (∑' j : ℤ, ‖cw m₂ j‖)) := by
  have hsum : Summable fun p : ℤ × ℤ => ‖cw m₁ p.1‖ * ‖cw m₂ p.2‖ :=
    h₁.mul_of_nonneg h₂ (fun x => norm_nonneg _) (fun y => norm_nonneg _)
  have hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖ := by
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
      (hsum.mul_left B)
    calc ‖K p.1 p.2‖ ≤ B * ‖cw m₁ p.1‖ * ‖cw m₂ p.2‖ := h p.1 p.2
      _ = B * (‖cw m₁ p.1‖ * ‖cw m₂ p.2‖) := mul_assoc _ _ _
  refine smKernMass_le_ofReal_tsum hK ?_
  calc (∑' p : ℤ × ℤ, ‖K p.1 p.2‖)
      ≤ ∑' p : ℤ × ℤ, B * (‖cw m₁ p.1‖ * ‖cw m₂ p.2‖) :=
        Summable.tsum_le_tsum (fun p => le_of_le_of_eq (h p.1 p.2) (mul_assoc _ _ _)) hK
          (hsum.mul_left B)
    _ = B * ∑' p : ℤ × ℤ, ‖cw m₁ p.1‖ * ‖cw m₂ p.2‖ := tsum_mul_left
    _ = B * ((∑' j : ℤ, ‖cw m₁ j‖) * (∑' j : ℤ, ‖cw m₂ j‖)) := by
        rw [show (∑' p : ℤ × ℤ, ‖cw m₁ p.1‖ * ‖cw m₂ p.2‖)
              = (∑' j : ℤ, ‖cw m₁ j‖) * (∑' j : ℤ, ‖cw m₂ j‖) from
            (tsum_mul_tsum_of_summable_norm (f := fun j : ℤ => ‖cw m₁ j‖)
              (g := fun j : ℤ => ‖cw m₂ j‖) (by simpa using h₁) (by simpa using h₂)).symm]
    _ = B * (∑' j : ℤ, ‖cw m₁ j‖) * (∑' j : ℤ, ‖cw m₂ j‖) := (mul_assoc _ _ _).symm

/-- **Finiteness of a single `ℓ¹(ℤ)`-sum of extended norms.** -/
theorem tsum_enorm_ne_top_of_summable {ι : Type*} {E : Type*} [SeminormedAddCommGroup E]
    {f : ι → E} (h : Summable fun i => ‖f i‖) : (∑' i, ‖f i‖ₑ) ≠ ⊤ := by
  rw [show (∑' i, ‖f i‖ₑ) = ∑' i, ((‖f i‖₊ : ℝ≥0) : ℝ≥0∞) from rfl,
    ENNReal.tsum_coe_ne_top_iff_summable]
  exact NNReal.summable_coe.mp (by simpa using h)

/-! ## 2. The Fourier coefficients `cw` of a `C²` compactly supported bump -/

/-- **Absolute summability of the coefficients `cw m` of a `C²` compactly supported bump.** -/
theorem summable_cw_of_contDiff_hasCompactSupport {m : ℝ → ℂ} (hcd : ContDiff ℝ 2 m)
    (hcs : HasCompactSupport m) : Summable fun j : ℤ => ‖cw m j‖ := by
  have h := FourierDecayExplicit hcd hcs
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_kmtKernWeight.mul_left
      (4 * max (∫ y, ‖m y‖) (∫ y, ‖iteratedDeriv 2 m y‖) + 1))
  rw [cw_eq_fourierTransform, norm_kmtKernWeight, mul_one_div]
  exact h (j : ℝ)

/-- **The explicit `ℓ¹`-bound for `cw m`** in terms of a bound `S` on `∫‖m‖` and `∫‖m''‖`. -/
theorem tsum_cw_le {m : ℝ → ℂ} (hcd : ContDiff ℝ 2 m) (hcs : HasCompactSupport m) {S : ℝ}
    (hS : 0 ≤ S) (h1 : (∫ y, ‖m y‖) ≤ S) (h2 : (∫ y, ‖iteratedDeriv 2 m y‖) ≤ S) :
    (∑' j : ℤ, ‖cw m j‖) ≤ (4 * S + 1) * (∑' j : ℤ, ‖kmtKernWeight j‖) := by
  have hbase : Summable fun j : ℤ => ‖cw m j‖ :=
    summable_cw_of_contDiff_hasCompactSupport hcd hcs
  have hC : (4 * max (∫ y, ‖m y‖) (∫ y, ‖iteratedDeriv 2 m y‖) + 1) ≤ 4 * S + 1 := by
    have := max_le h1 h2; linarith
  have hbound : ∀ j : ℤ, ‖cw m j‖ ≤ (4 * S + 1) * ‖kmtKernWeight j‖ := by
    intro j
    calc ‖cw m j‖
        ≤ (4 * max (∫ y, ‖m y‖) (∫ y, ‖iteratedDeriv 2 m y‖) + 1) * ‖kmtKernWeight j‖ := by
          rw [cw_eq_fourierTransform, norm_kmtKernWeight, mul_one_div]
          exact FourierDecayExplicit hcd hcs (j : ℝ)
      _ ≤ (4 * S + 1) * ‖kmtKernWeight j‖ :=
          mul_le_mul_of_nonneg_right hC (norm_nonneg _)
  calc (∑' j : ℤ, ‖cw m j‖)
      ≤ ∑' j : ℤ, (4 * S + 1) * ‖kmtKernWeight j‖ :=
        Summable.tsum_le_tsum hbound hbase (summable_kmtKernWeight.mul_left _)
    _ = (4 * S + 1) * (∑' j : ℤ, ‖kmtKernWeight j‖) := tsum_mul_left

/-! ## 3. The bumps of §6 -/

/-- `C²` with compact support for the modulated `φ̃`. -/
theorem contDiff_varphitildeNt_aux (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    ContDiff ℝ 2 (varphitildeNt P d N k t) := by
  rw [show varphitildeNt P d N k t
      = fun ξ : ℝ => varphitildeN d N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ) from rfl]
  exact (contDiff_varphitildeN d N k).mul (contDiff_ee_const_mul 2 _)

/-- Compact support for the modulated `φ̃`. -/
theorem hasCompactSupport_varphitildeNt_aux (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    HasCompactSupport (varphitildeNt P d N k t) := by
  rw [show varphitildeNt P d N k t
      = fun ξ : ℝ => varphitildeN d N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ) from rfl]
  exact (hasCompactSupport_varphitildeN d N k).mul_right

theorem summable_cw_varphiN (N k : ℕ) :
    Summable fun j : ℤ => ‖cw (varphiN N k) j‖ :=
  summable_cw_of_contDiff_hasCompactSupport (contDiff_varphiN N k) (hasCompactSupport_varphiN N k)

theorem summable_cw_varphitildeN (d N k : ℕ) :
    Summable fun j : ℤ => ‖cw (varphitildeN d N k) j‖ :=
  summable_cw_of_contDiff_hasCompactSupport (contDiff_varphitildeN d N k)
    (hasCompactSupport_varphitildeN d N k)

theorem summable_cw_varphiNt (N k : ℕ) (t : ℝ) :
    Summable fun j : ℤ => ‖cw (varphiNt N k t) j‖ :=
  summable_cw_of_contDiff_hasCompactSupport (contDiff_varphiNt N k t)
    (hasCompactSupport_varphiNt N k t)

theorem summable_cw_varphitildeNt (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    Summable fun j : ℤ => ‖cw (varphitildeNt P d N k t) j‖ :=
  summable_cw_of_contDiff_hasCompactSupport (contDiff_varphitildeNt_aux P d N k t)
    (hasCompactSupport_varphitildeNt_aux P d N k t)

/-- The coefficients of the tensor factor `m_* = η_{≤-2u}` are `ℓ¹`. -/
theorem summable_cw_mStarF (u : ℕ) : Summable fun j : ℤ => ‖cw (mStarF u) j‖ := by
  obtain ⟨C, hCpos, hC⟩ := cw_etaCut_decay (-(2 * (u : ℤ)))
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_kmtKernWeight.mul_left C)
  rw [norm_kmtKernWeight, mul_one_div]
  simpa only [mStarF] using hC j

/-- The coefficients of the tensor factor `η_{≤-2du}` are `ℓ¹`. -/
theorem summable_cw_mStargF (d u : ℕ) : Summable fun j : ℤ => ‖cw (mStargF d u) j‖ := by
  obtain ⟨C, hCpos, hC⟩ := cw_etaCut_decay (-((d : ℤ) * 2 * (u : ℤ)))
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_kmtKernWeight.mul_left C)
  rw [norm_kmtKernWeight, mul_one_div]
  simpa only [mStargF] using hC j

/-! ## 4. The Ionescu--Wainger kernel `tmKernel` of a bump -/

/-- **Quadratic decay of the exact-height IW kernel of a `C²` bump.**  This is
`Work.KMTAreas.A7.iwKernel_decay_of_bump` for the exact-height frequency set `diffFreqs ρ l`. -/
theorem tmKernel_decay_of_bump (ρ : ℝ) (l : ℕ) {F : ℝ → ℂ} (hFcd : ContDiff ℝ 2 F)
    (hFcs : HasCompactSupport F) {S : ℝ} (hSnn : 0 ≤ S) (h1 : (∫ y, ‖F y‖) ≤ S)
    (h2 : (∫ y, ‖iteratedDeriv 2 F y‖) ≤ S) :
    ∀ j : ℤ, ‖tmKernel ρ l F j‖ ≤ (4 * ((diffFreqs ρ l).card * S) + 1) * ‖kmtKernWeight j‖ :=
  iwKernel_decay_of_bump (diffFreqs ρ l) hFcd hFcs hSnn h1 h2

/-- Absolute summability of the exact-height IW kernel of a `C²` compactly supported bump. -/
theorem summable_tmKernel_of_bump (ρ : ℝ) (l : ℕ) {F : ℝ → ℂ} (hFcd : ContDiff ℝ 2 F)
    (hFcs : HasCompactSupport F) {S : ℝ} (hSnn : 0 ≤ S) (h1 : (∫ y, ‖F y‖) ≤ S)
    (h2 : (∫ y, ‖iteratedDeriv 2 F y‖) ≤ S) :
    Summable fun j : ℤ => ‖tmKernel ρ l F j‖ :=
  Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (tmKernel_decay_of_bump ρ l hFcd hFcs hSnn h1 h2)
    (summable_kmtKernWeight.mul_left (4 * ((diffFreqs ρ l).card * S) + 1))

theorem summable_tmKernel_varphiN (ρ : ℝ) (l N k : ℕ) :
    Summable fun j : ℤ => ‖tmKernel ρ l (varphiN N k) j‖ := by
  refine summable_tmKernel_of_bump ρ l (contDiff_varphiN N k) (hasCompactSupport_varphiN N k)
    (S := max (∫ y, ‖varphiN N k y‖) (∫ y, ‖iteratedDeriv 2 (varphiN N k) y‖)) ?_ ?_ ?_
  · exact le_max_of_le_left (integral_nonneg fun y => norm_nonneg _)
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem summable_tmKernel_varphitildeN (ρ : ℝ) (l d N k : ℕ) :
    Summable fun j : ℤ => ‖tmKernel ρ l (varphitildeN d N k) j‖ := by
  refine summable_tmKernel_of_bump ρ l (contDiff_varphitildeN d N k)
    (hasCompactSupport_varphitildeN d N k)
    (S := max (∫ y, ‖varphitildeN d N k y‖)
      (∫ y, ‖iteratedDeriv 2 (varphitildeN d N k) y‖)) ?_ ?_ ?_
  · exact le_max_of_le_left (integral_nonneg fun y => norm_nonneg _)
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- **The `t`-uniform quadratic decay of `tmKernel ρ l φ_{N,t}`** (the `φ`-side of §6). -/
theorem tmKernel_varphiNt_decay (ρ : ℝ) (l N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ j : ℤ,
      ‖tmKernel ρ l (varphiNt N k t) j‖ ≤ C * ‖kmtKernWeight j‖ := by
  obtain ⟨R, S, hSnn, hB⟩ := varphiNt_bounds N k
  refine ⟨4 * ((diffFreqs ρ l).card * S) + 1, ?_, ?_⟩
  · have : (0 : ℝ) ≤ ((diffFreqs ρ l).card : ℝ) * S := mul_nonneg (Nat.cast_nonneg _) hSnn
    linarith
  · intro t ht j
    obtain ⟨_, hcd, hcs, h1, h2⟩ := hB t ht
    exact tmKernel_decay_of_bump ρ l hcd hcs hSnn h1 h2 j

/-- **The `t`-uniform quadratic decay of `tmKernel ρ l φ̃_{N,t}`** (the `ψ`-side of §6).  The
modulation shifts the Fourier transform of `φ̃_N` by `c_t = P(Nt)`, which is bounded uniformly in
`t ∈ [1/2,1]`; the shifted decay is dominated by the unshifted one with the extra factor
`(2M+1)²` (`Work.KMTAreas.A7.one_div_sq_le_of_abs_sub_le`). -/
theorem tmKernel_varphitildeNt_decay_rho_first (ρ : ℝ) (P : Polynomial ℤ) (l d N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ j : ℤ,
      ‖tmKernel ρ l (varphitildeNt P d N k t) j‖ ≤ C * ‖kmtKernWeight j‖ := by
  obtain ⟨Cf, hCfpos, hCfdec⟩ := fourierDecay_varphitildeN d N k
  set Mv : ℝ := max 1 ((∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) *
    (1 + (N : ℝ)) ^ P.natDegree) with hMv
  set K : ℝ := (2 * Mv + 1) ^ 2 with hK
  have hMnonneg : 0 ≤ Mv := le_trans zero_le_one (le_max_left 1 _)
  refine ⟨((diffFreqs ρ l).card : ℝ) * Cf * K, ?_, ?_⟩
  · have hcard : (0 : ℝ) ≤ ((diffFreqs ρ l).card : ℝ) := Nat.cast_nonneg _
    have hKpos : 0 < K := by rw [hK]; positivity
    exact mul_nonneg (mul_nonneg hcard hCfpos.le) hKpos.le
  · intro t ht j
    have ht1 : |t| ≤ 1 := by
      obtain ⟨h1, h2⟩ := ht
      rw [abs_le]
      exact ⟨by linarith, h2⟩
    have hc : |PevalR P ((N : ℝ) * t)| ≤ Mv :=
      le_trans (abs_PevalR_mul_le P N ht1) (le_max_right 1 _)
    have hid : tmKernel ρ l (varphitildeNt P d N k t) j
        = (∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α)
          * FourierTransform.fourier (varphitildeN d N k)
              ((j : ℝ) - PevalR P ((N : ℝ) * t)) := by
      rw [tmKernel, Work.KMTPlan.A6.IwKernelArithChar (diffFreqs ρ l)
        (integrable_varphitildeNt_aux P d N k t) j, cw_eq_fourierTransform,
        fourier_varphitildeNt_eq P d N k t (j : ℝ)]
    rw [hid, norm_mul]
    have h1 : ‖∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α‖ ≤ ((diffFreqs ρ l).card : ℝ) := by
      calc ‖∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α‖
          ≤ ∑ α ∈ diffFreqs ρ l, ‖fourier (T := 1) (-j) α‖ := norm_sum_le _ _
        _ = ∑ _α ∈ diffFreqs ρ l, (1 : ℝ) := by
            refine Finset.sum_congr rfl (fun α _ => ?_)
            rw [fourier_apply]
            exact _root_.Circle.norm_coe _
        _ = ((diffFreqs ρ l).card : ℝ) := by simp
    have h2 : ‖FourierTransform.fourier (varphitildeN d N k)
          ((j : ℝ) - PevalR P ((N : ℝ) * t))‖ ≤ Cf * K / (1 + |(j : ℝ)|) ^ 2 := by
      refine le_trans (hCfdec _) ?_
      calc Cf / (1 + |(j : ℝ) - PevalR P ((N : ℝ) * t)|) ^ 2
          = Cf * (1 / (1 + |(j : ℝ) - PevalR P ((N : ℝ) * t)|) ^ 2) := div_eq_mul_one_div _ _
        _ ≤ Cf * (K / (1 + |(j : ℝ)|) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hCfpos.le
            rw [hK]
            exact one_div_sq_le_of_abs_sub_le hMnonneg hc j
        _ = Cf * K / (1 + |(j : ℝ)|) ^ 2 := (mul_div_assoc _ _ _).symm
    calc ‖∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α‖ *
            ‖FourierTransform.fourier (varphitildeN d N k)
              ((j : ℝ) - PevalR P ((N : ℝ) * t))‖
        ≤ ((diffFreqs ρ l).card : ℝ) * (Cf * K / (1 + |(j : ℝ)|) ^ 2) :=
          mul_le_mul h1 h2 (norm_nonneg _) (Nat.cast_nonneg _)
      _ = (((diffFreqs ρ l).card : ℝ) * Cf * K) * ‖kmtKernWeight j‖ := by
          rw [norm_kmtKernWeight]
          ring

/-! ## 5. The mass of the halved-average kernel -/

/-- **The halved-average kernel has finite `ℓ¹(ℤ²)`-mass**: its support is the graph of
`n ↦ P(n)` over the finite window `n ∈ (m/2, m]`. -/
theorem summable_khalf (m : ℕ) (P : Polynomial ℤ) :
    Summable fun p : ℤ × ℤ => ‖khalf m P p.1 p.2‖ := by
  let T : Finset (ℤ × ℤ) :=
    (Finset.range (m + 1)).image fun n : ℕ => ((n : ℤ), P.eval (n : ℤ))
  refine summable_of_hasFiniteSupport (T.finite_toSet.subset ?_)
  intro p hp
  have hne : khalf m P p.1 p.2 ≠ 0 := by
    simpa [Function.mem_support, norm_eq_zero] using hp
  have hcond : (m : ℤ) / 2 < p.1 ∧ p.1 ≤ (m : ℤ) ∧ p.2 = P.eval p.1 := by
    by_contra hc
    exact hne (by rw [khalf]; exact if_neg hc)
  obtain ⟨h1, h2, h3⟩ := hcond
  have hmnn : (0 : ℤ) ≤ (m : ℤ) / 2 := Int.ediv_nonneg (Int.natCast_nonneg m) (by norm_num)
  have hnn : 0 ≤ p.1 := le_of_lt (lt_of_le_of_lt hmnn h1)
  have hcast : ((p.1.toNat : ℕ) : ℤ) = p.1 := Int.toNat_of_nonneg hnn
  refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨p.1.toNat, ?_, ?_⟩)
  · rw [Finset.mem_range]
    omega
  · rw [Prod.mk.injEq]
    exact ⟨hcast, by rw [hcast]; exact h3.symm⟩

theorem smKernMass_khalf_ne_top (m : ℕ) (P : Polynomial ℤ) : smKernMass (khalf m P) ≠ ⊤ :=
  smKernMass_ne_top_of_summable (summable_khalf m P)


/-! ## 6. The arithmetic kernel is a bounded kernel; the concrete column has finite mass -/

/-- The arithmetic symbol `m_Ẑ` is an average of `q` numbers of modulus one. -/
theorem norm_mZ_le_one (P : Polynomial ℤ) (q : ℕ) (hq : 0 < q)
    (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) : ‖mZ P q α₁ α₂‖ ≤ 1 := by
  rw [mZ, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ n ∈ Finset.range q,
      fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ ≤ (q : ℝ) := by
    calc ‖∑ n ∈ Finset.range q,
          fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
        ≤ ∑ n ∈ Finset.range q,
            ‖fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ :=
          norm_sum_le _ _
      _ = ∑ _n ∈ Finset.range q, (1 : ℝ) := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe, mul_one]
      _ = (q : ℝ) := by simp
  calc ((q : ℝ))⁻¹ * ‖∑ n ∈ Finset.range q,
        fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
      ≤ ((q : ℝ))⁻¹ * (q : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg q))
    _ = 1 := by rw [inv_mul_cancel₀ (by exact_mod_cast hq.ne')]

/-- **The exact-height arithmetic kernel is bounded** by the product of the two exact-height
frequency cardinalities. -/
theorem smallArithKernel_norm_le (ρ : ℝ) (P : Polynomial ℤ) (q l₁ l₂ : ℕ) (hq : 0 < q)
    (j₁ j₂ : ℤ) :
    ‖smallArithKernel ρ P q l₁ l₂ j₁ j₂‖
      ≤ ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) := by
  unfold smallArithKernel
  calc ‖∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
        mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖
      ≤ ∑ α₁ ∈ diffFreqs ρ l₁, ‖∑ α₂ ∈ diffFreqs ρ l₂,
          mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖ :=
        norm_sum_le _ _
    _ ≤ ∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
          ‖mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖ :=
        Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ _α₁ ∈ diffFreqs ρ l₁, ∑ _α₂ ∈ diffFreqs ρ l₂, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun α₁ _ => Finset.sum_le_sum (fun α₂ _ => ?_))
        rw [norm_mul, norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe,
          mul_one, mul_one]
        exact norm_mZ_le_one P q hq α₁ α₂
    _ = ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- The kernel of the exact-height twisted bilinear multiplier `smallBtwist`, as a function of the
two summation variables. -/
theorem smallBtwistK_norm_le (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (j₁ j₂ : ℤ) :
    ‖smallArithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂ * cw m₁ j₁ * cw m₂ j₂‖
      ≤ (((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ)) * ‖cw m₁ j₁‖
        * ‖cw m₂ j₂‖ := by
  have hk := smallArithKernel_norm_le ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂
    (arithQ_pos ρ (max l₁ l₂)) j₁ j₂
  have hKB : 0 ≤ ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul hk le_rfl (norm_nonneg _) hKB) le_rfl (norm_nonneg _)
    (mul_nonneg hKB (norm_nonneg _))

/-- **The concrete §6 column has finite `ℓ¹(ℤ²)`-mass.**  It is the composition (`kernComp`) of the
finitely supported halved-average kernel with the two exact-height IW kernels, whose coefficient
families are `ℓ¹` (quadratic decay of a `C²` bump); the composition is summable by Young's
inequality (`Work.A7.ModelApproxCore_aux.summable_kernComp`). -/
theorem smallKconc_mass_ne_top (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) :
    smKernMass (smallKconc ρ P l₁ l₂ k₁ k₂ N) ≠ ⊤ :=
  smKernMass_ne_top_of_summable
    (Work.A7.ModelApproxCore_aux.summable_kernComp (summable_khalf N P)
      (summable_tmKernel_varphiN ρ l₁ N k₁)
      (summable_tmKernel_varphitildeN ρ l₂ P.natDegree N k₂))


end

end Work.KMTAreas.A7.Cpz


namespace Work.KMTAreas.A7.Cpz
open Work.KMTAreas.A7 Work.KMTAreas.A7z Work.KMTAreas.A7.Cpy

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

local notation "Circ" => AddCircle (1 : ℝ)

/-! ## Auxiliary lemmas for `coeff_arithSymb_mul_iwSymbol` -/

lemma kmt_integral_mul_fourier_eq_fourierCoeff (Ψ : Circ → ℂ) (a : ℤ) :
    (∫ θ : Circ, Ψ θ * fourier (T := 1) (-a) θ ∂circleMeasure) = fourierCoeff Ψ a := by
  rw [fourierCoeff]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only [smul_eq_mul]
  ring

lemma kmt_fourierCoeff_mul_periodize_sub {Ψ : Circ → ℂ} {m : ℝ → ℂ}
    (hΨ2 : MemLp Ψ 2 circleMeasure) (hm2 : MemLp (periodize m) 2 circleMeasure)
    (hΨs : Summable (fun n : ℤ => ‖fourierCoeff Ψ n‖)) (hm : Integrable m)
    (α : Circ) (a : ℤ) :
    fourierCoeff (fun θ : Circ => Ψ θ * periodize m (θ - α)) a
      = ∑' j : ℤ, fourierCoeff Ψ (a - j) * fourier (T := 1) (-j) α * cw m j := by
  have hm2' : MemLp (fun θ : Circ => periodize m (θ - α)) 2 circleMeasure := by
    have hmp := MeasureTheory.measurePreserving_add_right circleMeasure (-α)
    have h := hm2.comp_measurePreserving hmp
    rwa [show (periodize m ∘ fun x : Circ => x + -α)
        = (fun θ : Circ => periodize m (θ - α)) from by
          funext θ; simp [sub_eq_add_neg]] at h
  have hkey := Work.KMTAreas.A5.fourierCoeff_mul_eq_tsum_conv hΨ2 hm2' hΨs a
  rw [hkey]
  simp only [Work.KMTAreas.A7.fourierCoeff_comp_sub,
    Work.KMTPlan.A6.fourierCoeff_periodize_eq_cw hm]
  rw [← Equiv.tsum_eq (Equiv.subLeft a)
    (fun j : ℤ => fourierCoeff Ψ (a - j) * fourier (T := 1) (-j) α * cw m j)]
  refine tsum_congr (fun n => ?_)
  have h : a - (a - n) = n := by ring
  rw [Equiv.subLeft_apply, h]
  ring

lemma kmt_memLp_mul_fourier {f : Circ → ℂ} (hf : MemLp f ⊤ circleMeasure) (n : ℤ) :
    MemLp (fun θ : Circ => f θ * fourier (T := 1) n θ) ⊤ circleMeasure := by
  haveI : IsFiniteMeasure circleMeasure := inferInstance
  have hfou : MemLp (fun θ : Circ => fourier (T := 1) n θ) ⊤ circleMeasure :=
    MemLp.of_bound (fourier n).continuous.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun θ => by
        rw [fourier_apply]
        exact le_of_eq (_root_.Circle.norm_coe _))
  have h : MemLp (fun θ : Circ => f θ * fourier (T := 1) n θ) ⊤ circleMeasure := hf.mul hfou
  simpa only [Pi.mul_apply] using h

lemma kmt_MemLp_shift {F : Circ → ℂ} (hF : MemLp F ⊤ circleMeasure) (α : Circ) :
    MemLp (fun θ : Circ => F (θ - α)) ⊤ circleMeasure := by
  have h := hF.comp_measurePreserving
    (MeasureTheory.measurePreserving_add_right circleMeasure (-α))
  rwa [show (F ∘ fun x : Circ => x + -α) = (fun θ : Circ => F (θ - α)) from by
    funext θ; simp [sub_eq_add_neg]] at h

lemma kmt_norm_varphitildeN_le_two (d N k : ℕ) (x : ℝ) : ‖varphitildeN d N k x‖ ≤ 2 := by
  rw [varphitildeN]
  split_ifs with hk
  · exact le_trans (Work.KMTContract.norm_kmtEta_le _) (by norm_num)
  · calc ‖Work.KMTContract.kmtEta
            ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * x)
          - Work.KMTContract.kmtEta
            ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * x)‖
        ≤ ‖Work.KMTContract.kmtEta
              ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * x)‖
          + ‖Work.KMTContract.kmtEta
              ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * x)‖ :=
          norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (Work.KMTContract.norm_kmtEta_le _)
          (Work.KMTContract.norm_kmtEta_le _)
      _ = 2 := by norm_num

lemma kmt_MemLp_periodize_mStarF (u : ℕ) : MemLp (periodize (mStarF u)) ⊤ circleMeasure := by
  simpa only [mStarF] using memLp_periodize_etaCut (-(2 * (u : ℤ)))

lemma kmt_MemLp_periodize_mStargF (d u : ℕ) :
    MemLp (periodize (mStargF d u)) ⊤ circleMeasure := by
  simpa only [mStargF] using memLp_periodize_etaCut (-((d : ℤ) * 2 * (u : ℤ)))

lemma kmt_MemLp_periodize_varphiNt (N k : ℕ) (t : ℝ) :
    MemLp (periodize (varphiNt N k t)) ⊤ circleMeasure := by
  refine memLp_periodize (contDiff_varphiNt N k t).continuous.measurable
    (R := (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) (C := 2)
    (Real.rpow_nonneg (by norm_num) _) ?_ ?_
  · intro x hx
    by_contra hne
    exact absurd (varphiNt_support N k t x hne) (not_le.mpr hx)
  · intro x
    rw [varphiNt, norm_mul, norm_ee, mul_one]
    exact norm_varphiN_le_two N k x

lemma kmt_MemLp_periodize_varphitildeNt (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    MemLp (periodize (varphitildeNt P d N k t)) ⊤ circleMeasure := by
  obtain ⟨R, hR⟩ :=
    exists_abs_le_of_hasCompactSupport (hasCompactSupport_varphitildeNt_aux P d N k t)
  refine memLp_periodize (contDiff_varphitildeNt_aux P d N k t).continuous.measurable
    (R := max R 0) (C := 2) (le_max_right _ _) ?_ ?_
  · intro x hx
    exact hR x (le_of_lt (lt_of_le_of_lt (le_max_left R 0) hx))
  · intro x
    rw [varphitildeNt, norm_mul, norm_ee, mul_one]
    exact kmt_norm_varphitildeN_le_two d N k x

lemma kmt_integrable_mStarF (u : ℕ) : Integrable (mStarF u) := by
  simpa only [mStarF] using
    (contDiff_etaCut (-(2 * (u : ℤ)))).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_etaCut (-(2 * (u : ℤ))))

lemma kmt_integrable_mStargF (d u : ℕ) : Integrable (mStargF d u) := by
  have h : mStargF d u = mStarF (d * u) := by
    unfold mStargF mStarF
    congr 1
    push_cast
    ring
  rw [h]
  exact kmt_integrable_mStarF (d * u)

lemma kmt_summable_tmKernel_varphiNt (ρ : ℝ) (l N k : ℕ) (t : ℝ) :
    Summable (fun j : ℤ => ‖tmKernel ρ l (varphiNt N k t) j‖) := by
  refine summable_tmKernel_of_bump ρ l (contDiff_varphiNt N k t) (hasCompactSupport_varphiNt N k t)
    (S := max (∫ y, ‖varphiNt N k t y‖) (∫ y, ‖iteratedDeriv 2 (varphiNt N k t) y‖)) ?_ ?_ ?_
  · exact le_max_of_le_left (integral_nonneg fun y => norm_nonneg _)
  · exact le_max_left _ _
  · exact le_max_right _ _

lemma kmt_summable_tmKernel_varphitildeNt (ρ : ℝ) (P : Polynomial ℤ) (l N k : ℕ) (t : ℝ) :
    Summable (fun j : ℤ => ‖tmKernel ρ l (varphitildeNt P P.natDegree N k t) j‖) := by
  refine summable_tmKernel_of_bump ρ l (contDiff_varphitildeNt_aux P P.natDegree N k t)
    (hasCompactSupport_varphitildeNt_aux P P.natDegree N k t)
    (S := max (∫ y, ‖varphitildeNt P P.natDegree N k t y‖)
      (∫ y, ‖iteratedDeriv 2 (varphitildeNt P P.natDegree N k t) y‖)) ?_ ?_ ?_
  · exact le_max_of_le_left (integral_nonneg fun y => norm_nonneg _)
  · exact le_max_left _ _
  · exact le_max_right _ _

lemma kmt_fourierCoeff_varphiNt_mul_mStarF (ρ : ℝ) (l N k : ℕ) (t : ℝ) (u : ℕ)
    (α : Circ) (a : ℤ) :
    fourierCoeff (fun θ : Circ => iwSymbolSet (diffFreqs ρ l) (periodize (varphiNt N k t)) θ
        * periodize (mStarF u) (θ - α)) a
      = ∑' j : ℤ, tmKernel ρ l (varphiNt N k t) (a - j) * fourier (T := 1) (-j) α
          * cw (mStarF u) j := by
  have h := kmt_fourierCoeff_mul_periodize_sub
    (Ψ := iwSymbolSet (diffFreqs ρ l) (periodize (varphiNt N k t))) (m := mStarF u)
    ((Work.Analysis.IWMultiplier.memLp_iwSymbolSet _ (kmt_MemLp_periodize_varphiNt N k t)).mono_exponent
      (by norm_num : (2 : ℝ≥0∞) ≤ ⊤))
    ((kmt_MemLp_periodize_mStarF u).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ ⊤))
    (by simpa only [tmKernel, Work.Analysis.IWMultiplier.iwKernel] using
      kmt_summable_tmKernel_varphiNt ρ l N k t)
    (kmt_integrable_mStarF u) α a
  simpa only [tmKernel, Work.Analysis.IWMultiplier.iwKernel] using h

lemma kmt_fourierCoeff_varphitildeNt_mul_mStargF (ρ : ℝ) (P : Polynomial ℤ) (l N k : ℕ)
    (t : ℝ) (u : ℕ) (α : Circ) (b : ℤ) :
    fourierCoeff (fun θ : Circ =>
        iwSymbolSet (diffFreqs ρ l) (periodize (varphitildeNt P P.natDegree N k t)) θ
        * periodize (mStargF P.natDegree u) (θ - α)) b
      = ∑' j : ℤ, tmKernel ρ l (varphitildeNt P P.natDegree N k t) (b - j)
          * fourier (T := 1) (-j) α * cw (mStargF P.natDegree u) j := by
  have h := kmt_fourierCoeff_mul_periodize_sub
    (Ψ := iwSymbolSet (diffFreqs ρ l) (periodize (varphitildeNt P P.natDegree N k t)))
    (m := mStargF P.natDegree u)
    ((Work.Analysis.IWMultiplier.memLp_iwSymbolSet _ (kmt_MemLp_periodize_varphitildeNt P P.natDegree N k t)).mono_exponent
      (by norm_num : (2 : ℝ≥0∞) ≤ ⊤))
    ((kmt_MemLp_periodize_mStargF P.natDegree u).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ ⊤))
    (by simpa only [tmKernel, Work.Analysis.IWMultiplier.iwKernel] using
      kmt_summable_tmKernel_varphitildeNt ρ P l N k t)
    (kmt_integrable_mStargF P.natDegree u) α b
  simpa only [tmKernel, Work.Analysis.IWMultiplier.iwKernel] using h

lemma kmt_summable_shift_mul {f g : ℤ → ℝ} (hf : Summable f) (hg : Summable g)
    (hf0 : 0 ≤ f) (hg0 : 0 ≤ g) (a : ℤ) : Summable (fun j : ℤ => f (a - j) * g j) := by
  have h := (hf.mul_of_nonneg hg hf0 hg0).comp_injective (i := fun j : ℤ => (a - j, j))
    (fun x y hxy => congrArg Prod.snd hxy)
  exact h

lemma kmt_summable_X (ρ : ℝ) (l : ℕ) {φ m : ℝ → ℂ}
    (hφ : Summable (fun j : ℤ => ‖tmKernel ρ l φ j‖)) (hm : Summable (fun j : ℤ => ‖cw m j‖))
    (α : Circ) (a : ℤ) :
    Summable (fun j : ℤ => tmKernel ρ l φ (a - j) * fourier (T := 1) (-j) α * cw m j) := by
  have h1 : Summable (fun j : ℤ => ‖tmKernel ρ l φ (a - j)‖ * ‖cw m j‖) :=
    kmt_summable_shift_mul hφ hm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) a
  refine Summable.of_norm ?_
  refine h1.congr (fun j => ?_)
  rw [norm_mul, norm_mul, fourier_norm_eq_one, mul_one]

lemma kmt_finset_mul_tsum_tsum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (X Y : ι → ℤ → ℂ)
    (hX : ∀ p ∈ s, Summable (fun j : ℤ => X p j)) (hY : ∀ p ∈ s, Summable (fun j : ℤ => Y p j)) :
    ∑ p ∈ s, c p * (∑' j : ℤ, X p j) * (∑' j : ℤ, Y p j)
      = ∑' j₁ : ℤ, ∑' j₂ : ℤ, ∑ p ∈ s, c p * X p j₁ * Y p j₂ := by
  have h1 : ∀ j₁ : ℤ, (∑' j₂ : ℤ, ∑ p ∈ s, c p * X p j₁ * Y p j₂)
      = ∑ p ∈ s, c p * X p j₁ * (∑' j₂ : ℤ, Y p j₂) := by
    intro j₁
    rw [Summable.tsum_finsetSum (f := fun p (j₂ : ℤ) => c p * X p j₁ * Y p j₂)
      (fun p hp => (hY p hp).mul_left (c p * X p j₁))]
    exact Finset.sum_congr rfl (fun p hp => by rw [tsum_mul_left])
  have h2 : (∑' j₁ : ℤ, ∑ p ∈ s, c p * X p j₁ * (∑' j₂ : ℤ, Y p j₂))
      = ∑ p ∈ s, c p * (∑' j₁ : ℤ, X p j₁) * (∑' j₂ : ℤ, Y p j₂) := by
    rw [Summable.tsum_finsetSum (f := fun p (j₁ : ℤ) => c p * X p j₁ * (∑' j₂ : ℤ, Y p j₂))
      (fun p hp => ((hX p hp).mul_left (c p)).mul_right (∑' j₂ : ℤ, Y p j₂))]
    exact Finset.sum_congr rfl (fun p hp => by rw [tsum_mul_right, tsum_mul_left])
  rw [tsum_congr h1, h2]

theorem coeff_arithSymb_mul_iwSymbol (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) (t : ℝ) (a b : ℤ) :
    Work.KMTAreas.A7.coeff
        (fun θ₁ θ₂ : AddCircle (1 : ℝ) =>
          Work.KMTAreas.A7.arithSymb ρ P l₁ l₂
              (Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂)) θ₁ θ₂
            * Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l₁)
                (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.varphiNt N k₁ t)) θ₁
            * Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l₂)
                (Work.Analysis.IonescuWainger.periodize
                  (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t)) θ₂) a b
      = ∑' j₁ : ℤ, ∑' j₂ : ℤ,
          (Work.KMTAreas.A7.smallArithKernel ρ P
              (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂
            * Work.KMTAreas.A7.cw
                (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂))) j₁
            * Work.KMTAreas.A7.cw
                (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂))) j₂)
          * Work.KMTAreas.A7.tmKernel ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ t) (a - j₁)
          * Work.KMTAreas.A7.tmKernel ρ l₂ (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t) (b - j₂) := by
  classical
  set u₀ : ℕ := uScale ρ (smallL l₁ l₂ k₁ k₂) with hu₀
  set Ψ₁ : Circ → ℂ := iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ t)) with hΨ₁
  set Ψ₂ : Circ → ℂ := iwSymbolSet (diffFreqs ρ l₂)
    (periodize (varphitildeNt P P.natDegree N k₂ t)) with hΨ₂
  haveI : IsFiniteMeasure circleMeasure := inferInstance
  have hΨ₁Lp : MemLp Ψ₁ ⊤ circleMeasure := by
    rw [hΨ₁]
    exact Work.Analysis.IWMultiplier.memLp_iwSymbolSet _ (kmt_MemLp_periodize_varphiNt N k₁ t)
  have hΨ₂Lp : MemLp Ψ₂ ⊤ circleMeasure := by
    rw [hΨ₂]
    exact Work.Analysis.IWMultiplier.memLp_iwSymbolSet _ (kmt_MemLp_periodize_varphitildeNt P P.natDegree N k₂ t)
  have hΦ₁Lp : MemLp (periodize (mStarF u₀)) ⊤ circleMeasure := kmt_MemLp_periodize_mStarF u₀
  have hΦ₂Lp : MemLp (periodize (mStargF P.natDegree u₀)) ⊤ circleMeasure :=
    kmt_MemLp_periodize_mStargF P.natDegree u₀
  -- the rank-one decomposition of the symbol
  have hF : (fun θ₁ θ₂ : Circ => arithSymb ρ P l₁ l₂ u₀ θ₁ θ₂ * Ψ₁ θ₁ * Ψ₂ θ₂)
      = fun θ₁ θ₂ : Circ =>
          ∑ p ∈ (diffFreqs ρ l₁).product (diffFreqs ρ l₂),
            (mZ P (arithQ ρ (max l₁ l₂)) p.1 p.2
                * (Ψ₁ θ₁ * periodize (mStarF u₀) (θ₁ - p.1)))
              * (Ψ₂ θ₂ * periodize (mStargF P.natDegree u₀) (θ₂ - p.2)) := by
    funext θ₁ θ₂
    rw [arithSymb]
    have hsp := Finset.sum_product (diffFreqs ρ l₁) (diffFreqs ρ l₂)
      (fun p : Circ × Circ => mZ P (arithQ ρ (max l₁ l₂)) p.1 p.2
        * periodize (mStarF u₀) (θ₁ - p.1) * periodize (mStargF P.natDegree u₀) (θ₂ - p.2))
    rw [← hsp, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    ring
  -- integrability of the two families of integrands
  have hA : ∀ p ∈ (diffFreqs ρ l₁).product (diffFreqs ρ l₂),
      Integrable (fun θ : Circ =>
        (mZ P (arithQ ρ (max l₁ l₂)) p.1 p.2
            * (Ψ₁ θ * periodize (mStarF u₀) (θ - p.1)))
          * fourier (T := 1) (-a) θ) circleMeasure := by
    intro p hp
    have h1 : MemLp (fun θ : Circ => Ψ₁ θ * periodize (mStarF u₀) (θ - p.1)) ⊤ circleMeasure :=
      hΨ₁Lp.mul (kmt_MemLp_shift hΦ₁Lp p.1)
    exact (kmt_memLp_mul_fourier (h1.const_mul (mZ P (arithQ ρ (max l₁ l₂)) p.1 p.2)) (-a)).integrable
      le_top
  have hB : ∀ p ∈ (diffFreqs ρ l₁).product (diffFreqs ρ l₂),
      Integrable (fun θ : Circ =>
        (Ψ₂ θ * periodize (mStargF P.natDegree u₀) (θ - p.2)) * fourier (T := 1) (-b) θ)
        circleMeasure := by
    intro p hp
    have h1 : MemLp (fun θ : Circ => Ψ₂ θ * periodize (mStargF P.natDegree u₀) (θ - p.2))
        ⊤ circleMeasure := hΨ₂Lp.mul (kmt_MemLp_shift hΦ₂Lp p.2)
    exact (kmt_memLp_mul_fourier h1 (-b)).integrable le_top
  have hsep := coeff_finset_sum_sep ((diffFreqs ρ l₁).product (diffFreqs ρ l₂))
      (fun p θ => mZ P (arithQ ρ (max l₁ l₂)) p.1 p.2
        * (Ψ₁ θ * periodize (mStarF u₀) (θ - p.1)))
      (fun p θ => Ψ₂ θ * periodize (mStargF P.natDegree u₀) (θ - p.2)) a b hA hB
  rw [hF, hsep]
  -- the two families of one-dimensional integrals
  have hI₁ : ∀ p ∈ (diffFreqs ρ l₁).product (diffFreqs ρ l₂),
      (∫ θ : Circ, (mZ P (arithQ ρ (max l₁ l₂)) p.1 p.2
          * (Ψ₁ θ * periodize (mStarF u₀) (θ - p.1))) * fourier (T := 1) (-a) θ ∂circleMeasure)
        = mZ P (arithQ ρ (max l₁ l₂)) p.1 p.2
            * (∑' j : ℤ, tmKernel ρ l₁ (varphiNt N k₁ t) (a - j) * fourier (T := 1) (-j) p.1
                * cw (mStarF u₀) j) := by
    intro p hp
    have h1 : (∫ θ : Circ, (mZ P (arithQ ρ (max l₁ l₂)) p.1 p.2
          * (Ψ₁ θ * periodize (mStarF u₀) (θ - p.1))) * fourier (T := 1) (-a) θ ∂circleMeasure)
        = mZ P (arithQ ρ (max l₁ l₂)) p.1 p.2
            * ∫ θ : Circ, (Ψ₁ θ * periodize (mStarF u₀) (θ - p.1)) * fourier (T := 1) (-a) θ
                ∂circleMeasure := by
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
    rw [h1]
    congr 1
    rw [kmt_integral_mul_fourier_eq_fourierCoeff
      (fun θ : Circ => Ψ₁ θ * periodize (mStarF u₀) (θ - p.1)) a]
    have hc := kmt_fourierCoeff_varphiNt_mul_mStarF ρ l₁ N k₁ t u₀ p.1 a
    rw [← hΨ₁] at hc
    exact hc
  have hI₂ : ∀ p ∈ (diffFreqs ρ l₁).product (diffFreqs ρ l₂),
      (∫ θ : Circ, (Ψ₂ θ * periodize (mStargF P.natDegree u₀) (θ - p.2))
          * fourier (T := 1) (-b) θ ∂circleMeasure)
        = ∑' j : ℤ, tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t) (b - j)
            * fourier (T := 1) (-j) p.2 * cw (mStargF P.natDegree u₀) j := by
    intro p hp
    rw [kmt_integral_mul_fourier_eq_fourierCoeff
      (fun θ : Circ => Ψ₂ θ * periodize (mStargF P.natDegree u₀) (θ - p.2)) b]
    have hc := kmt_fourierCoeff_varphitildeNt_mul_mStargF ρ P l₂ N k₂ t u₀ p.2 b
    rw [← hΨ₂] at hc
    exact hc
  have hgoal1 : (∑ p ∈ (diffFreqs ρ l₁).product (diffFreqs ρ l₂),
        (∫ θ : Circ, (mZ P (arithQ ρ (max l₁ l₂)) p.1 p.2
            * (Ψ₁ θ * periodize (mStarF u₀) (θ - p.1))) * fourier (T := 1) (-a) θ ∂circleMeasure)
          * (∫ θ : Circ, (Ψ₂ θ * periodize (mStargF P.natDegree u₀) (θ - p.2))
              * fourier (T := 1) (-b) θ ∂circleMeasure))
      = ∑ p ∈ (diffFreqs ρ l₁).product (diffFreqs ρ l₂),
          (mZ P (arithQ ρ (max l₁ l₂)) p.1 p.2
              * (∑' j : ℤ, tmKernel ρ l₁ (varphiNt N k₁ t) (a - j)
                  * fourier (T := 1) (-j) p.1 * cw (mStarF u₀) j))
            * (∑' j : ℤ, tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t) (b - j)
                * fourier (T := 1) (-j) p.2 * cw (mStargF P.natDegree u₀) j) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hI₁ p hp, hI₂ p hp]
  rw [hgoal1]
  -- summability of the two inner families
  have hX : ∀ p ∈ (diffFreqs ρ l₁).product (diffFreqs ρ l₂),
      Summable (fun j : ℤ => tmKernel ρ l₁ (varphiNt N k₁ t) (a - j)
        * fourier (T := 1) (-j) p.1 * cw (mStarF u₀) j) :=
    fun p hp => kmt_summable_X ρ l₁ (kmt_summable_tmKernel_varphiNt ρ l₁ N k₁ t)
      (summable_cw_mStarF u₀) p.1 a
  have hY : ∀ p ∈ (diffFreqs ρ l₁).product (diffFreqs ρ l₂),
      Summable (fun j : ℤ => tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t) (b - j)
        * fourier (T := 1) (-j) p.2 * cw (mStargF P.natDegree u₀) j) :=
    fun p hp => kmt_summable_X ρ l₂ (kmt_summable_tmKernel_varphitildeNt ρ P l₂ N k₂ t)
      (summable_cw_mStargF P.natDegree u₀) p.2 b
  -- unfolding the arithmetic kernel
  have hR : (∑' j₁ : ℤ, ∑' j₂ : ℤ,
        (smallArithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂ * cw (mStarF u₀) j₁
            * cw (mStargF P.natDegree u₀) j₂)
          * tmKernel ρ l₁ (varphiNt N k₁ t) (a - j₁)
          * tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t) (b - j₂))
      = ∑' j₁ : ℤ, ∑' j₂ : ℤ, ∑ p ∈ (diffFreqs ρ l₁).product (diffFreqs ρ l₂),
          mZ P (arithQ ρ (max l₁ l₂)) p.1 p.2
            * (tmKernel ρ l₁ (varphiNt N k₁ t) (a - j₁) * fourier (T := 1) (-j₁) p.1
                * cw (mStarF u₀) j₁)
            * (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t) (b - j₂)
                * fourier (T := 1) (-j₂) p.2 * cw (mStargF P.natDegree u₀) j₂) := by
    refine tsum_congr (fun j₁ => tsum_congr (fun j₂ => ?_))
    rw [smallArithKernel]
    have hsp := Finset.sum_product (diffFreqs ρ l₁) (diffFreqs ρ l₂)
      (fun p : Circ × Circ => mZ P (arithQ ρ (max l₁ l₂)) p.1 p.2
        * fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2)
    rw [← hsp, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    ring
  have hswap := kmt_finset_mul_tsum_tsum ((diffFreqs ρ l₁).product (diffFreqs ρ l₂))
      (fun p => mZ P (arithQ ρ (max l₁ l₂)) p.1 p.2)
      (fun p (j : ℤ) => tmKernel ρ l₁ (varphiNt N k₁ t) (a - j) * fourier (T := 1) (-j) p.1
        * cw (mStarF u₀) j)
      (fun p (j : ℤ) => tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t) (b - j)
        * fourier (T := 1) (-j) p.2 * cw (mStargF P.natDegree u₀) j) hX hY
  rw [hR]
  exact hswap


end

end Work.KMTAreas.A7.Cpz


namespace Work.KMTAreas.A7.Cpz
open Work.KMTAreas.A7 Work.KMTAreas.A7z Work.KMTAreas.A7.Cpy

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-- **The model kernel `smallKmod` in `tmKernel` form.**

`smallKmod` is by definition the `t`-integral of the composition (`kernComp`) of the arithmetic
kernel `smallArithKernel · cw m_* · cw m̃_*` with the two exact-height Ionescu--Wainger kernels
`tmKernel ρ lᵢ (…^t)`.  Reindexing the composition (`kernComp_eq_iter`) and expanding the two
`tmKernel`s into their arithmetic-character sums (`tmKernel_varphiNt`, `tmKernel_varphitildeNt`)
gives the displayed iterated sum, which is the form in which the `(a,b)`-coefficient of
`modSymbC` presents itself. -/
lemma smallKmod_eq_integral_tmKernel (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) (a b : ℤ) :
    smallKmod ρ P l₁ l₂ k₁ k₂ N a b
      = ∫ t in (1 / 2 : ℝ)..1, ∑' j₁ : ℤ, ∑' j₂ : ℤ,
          (smallArithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂
            * cw (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂))) j₁
            * cw (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂))) j₂)
          * tmKernel ρ l₁ (varphiNt N k₁ t) (a - j₁)
          * tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t) (b - j₂) := by
  rw [smallKmod_coeff]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  refine tsum_congr (fun j₁ => ?_)
  refine tsum_congr (fun j₂ => ?_)
  rw [← tmKernel_varphiNt ρ l₁ N k₁ t (a - j₁),
    ← tmKernel_varphitildeNt ρ P l₂ N k₂ t (b - j₂)]

end

theorem smallKmod_eq_coeff_modSymbC (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) (a b : ℤ) :
    Work.KMTAreas.A7.smallKmod ρ P l₁ l₂ k₁ k₂ N a b
      = Work.KMTAreas.A7.coeff (Work.KMTAreas.A7.modSymbC ρ P l₁ l₂ k₁ k₂ N) a b := by
  rw [coeff_modSymbC_eq_integral_coeff]
  rw [smallKmod_eq_integral_tmKernel]
  exact intervalIntegral.integral_congr
    (fun t _ => (coeff_arithSymb_mul_iwSymbol ρ P l₁ l₂ k₁ k₂ N t a b).symm)

end Work.KMTAreas.A7.Cpz


namespace Work.KMTAreas.A7.Cpz
open Work.KMTAreas.A7 Work.KMTAreas.A7z Work.KMTAreas.A7.Cpy

noncomputable section

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators

/-- The `ℓ¹(ℤ²)`-mass is subadditive. -/
theorem smKernMass_sub_le {K L : ℤ → ℤ → ℂ} :
    smKernMass (fun a b => K a b - L a b) ≤ smKernMass K + smKernMass L := by
  rw [smKernMass, smKernMass, smKernMass]
  calc ∑' p : ℤ × ℤ, ‖K p.1 p.2 - L p.1 p.2‖ₑ
      ≤ ∑' p : ℤ × ℤ, (‖K p.1 p.2‖ₑ + ‖L p.1 p.2‖ₑ) :=
        ENNReal.tsum_le_tsum fun p => by
          simpa only [enorm_eq_nnnorm, ← ENNReal.coe_add] using
            ENNReal.coe_le_coe.mpr (nnnorm_sub_le (K p.1 p.2) (L p.1 p.2))
    _ = (∑' p : ℤ × ℤ, ‖K p.1 p.2‖ₑ) + (∑' p : ℤ × ℤ, ‖L p.1 p.2‖ₑ) :=
        ENNReal.tsum_add

/-- **The crude bound on the bounded-parameter box.** -/
theorem crude_mass_bound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (D : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (l₁ l₂ k₁ k₂ N : ℕ),
      max (max l₁ l₂) (max k₁ k₂) ≤ D → N ≤ D →
      smKernMass (fun a b : ℤ => smallKconc ρ P l₁ l₂ k₁ k₂ N a b
        - smallKmod ρ P l₁ l₂ k₁ k₂ N a b) ≤ ENNReal.ofReal B := by
  classical
  have hne : ∀ l₁ l₂ k₁ k₂ N : ℕ,
      smKernMass (fun a b : ℤ => smallKconc ρ P l₁ l₂ k₁ k₂ N a b
        - smallKmod ρ P l₁ l₂ k₁ k₂ N a b) ≠ ⊤ := by
    intro l₁ l₂ k₁ k₂ N
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨?_, ?_⟩) smKernMass_sub_le
    · exact smKernMass_ne_top_of_summable (smr_summable_smallKconc ρ P l₁ l₂ k₁ k₂ N)
    · exact smKernMass_ne_top_of_summable (smr_summable_smallKmod ρ hρ hρ1 P l₁ l₂ k₁ k₂ N)
  let f : Fin (D + 1) × Fin (D + 1) × Fin (D + 1) × Fin (D + 1) × Fin (D + 1) → ℝ≥0∞ :=
    fun x => smKernMass (fun a b : ℤ =>
      smallKconc ρ P x.1.val x.2.1.val x.2.2.1.val x.2.2.2.1.val x.2.2.2.2.val a b
        - smallKmod ρ P x.1.val x.2.1.val x.2.2.1.val x.2.2.2.1.val x.2.2.2.2.val a b)
  refine ⟨∑ x : Fin (D + 1) × Fin (D + 1) × Fin (D + 1) × Fin (D + 1) × Fin (D + 1),
      (f x).toReal, Finset.sum_nonneg fun x _ => ENNReal.toReal_nonneg, ?_⟩
  intro l₁ l₂ k₁ k₂ N h1 h2
  have hl₁ : l₁ < D + 1 := by omega
  have hl₂ : l₂ < D + 1 := by omega
  have hk₁ : k₁ < D + 1 := by omega
  have hk₂ : k₂ < D + 1 := by omega
  have hN : N < D + 1 := by omega
  let xt : Fin (D + 1) × Fin (D + 1) × Fin (D + 1) × Fin (D + 1) × Fin (D + 1) :=
    (⟨l₁, hl₁⟩, ⟨l₂, hl₂⟩, ⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩, ⟨N, hN⟩)
  have hle : (f xt).toReal ≤ ∑ x, (f x).toReal :=
    Finset.single_le_sum (fun x _ => ENNReal.toReal_nonneg) (Finset.mem_univ xt)
  calc smKernMass (fun a b : ℤ => smallKconc ρ P l₁ l₂ k₁ k₂ N a b
          - smallKmod ρ P l₁ l₂ k₁ k₂ N a b)
      = ENNReal.ofReal ((f xt).toReal) :=
        (ENNReal.ofReal_toReal (hne l₁ l₂ k₁ k₂ N)).symm
    _ ≤ ENNReal.ofReal (∑ x, (f x).toReal) := ENNReal.ofReal_le_ofReal hle

end

end Work.KMTAreas.A7.Cpz

namespace Work.KMTAreas.A7.Cpz
open Work.KMTAreas.A7 Work.KMTAreas.A7z Work.KMTAreas.A7.Cpy

noncomputable section

open MeasureTheory Finset
open scoped BigOperators
open Work.Analysis.IonescuWainger

/-- **The §6 collapse in mass form.**  On the main regime of §6 — the two bumps narrow enough that
the windows `m_*` are `1` on their support (the hypotheses `hw₁u`, `hw₂u`, with `hu`) and the
exact-height arithmetic frequency sets non-aliasing at the arc radius `2^{-2u}` (the hypotheses
`hNA₁`, `hNA₂`) — the difference of the two kernels is the sum of the spikes. -/
theorem smallKconc_sub_smallKmod_eq_sum_spike (ρ : ℝ) (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree)
    (l₁ l₂ k₁ k₂ N : ℕ) (hN : 1 ≤ N)
    {w₁ w₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw₁2 : w₁ < 1 / 2) (hw₂2 : w₂ < 1 / 2)
    (hsup₁ : ∀ x : ℝ, varphiN N k₁ x ≠ 0 → |x| ≤ w₁)
    (hsup₂ : ∀ x : ℝ, varphitildeN P.natDegree N k₂ x ≠ 0 → |x| ≤ w₂)
    (hw₁u : w₁ ≤ (2 : ℝ) ^ (-(2 * ((uScale ρ (smallL l₁ l₂ k₁ k₂)) : ℤ)) - 1))
    (hw₂u : w₂ ≤ (2 : ℝ) ^
      (-((P.natDegree : ℤ) * 2 * ((uScale ρ (smallL l₁ l₂ k₁ k₂)) : ℤ)) - 1))
    (hu : 1 ≤ uScale ρ (smallL l₁ l₂ k₁ k₂))
    (hNA₁ : NonAliasing (-(2 * ((uScale ρ (smallL l₁ l₂ k₁ k₂)) : ℤ))) (diffFreqs ρ l₁))
    (hNA₂ : NonAliasing (-(2 * ((uScale ρ (smallL l₁ l₂ k₁ k₂)) : ℤ))) (diffFreqs ρ l₂)) :
    (fun a b : ℤ => smallKconc ρ P l₁ l₂ k₁ k₂ N a b - smallKmod ρ P l₁ l₂ k₁ k₂ N a b)
      = fun a b : ℤ => ∑ p ∈ (diffFreqs ρ l₁) ×ˢ (diffFreqs ρ l₂),
          coeff (spikeSymb ρ P l₁ l₂ k₁ k₂ N p.1 p.2) a b := by
  funext a b
  obtain ⟨⟨hmeasc, Cc, hCcnn, hCcb⟩, hmeasm, Cm, hCmnn, hCmb⟩ :=
    arithSymbMeasBdd ρ P l₁ l₂ k₁ k₂ N
  have hIc : Integrable (fun p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
      concSymb ρ P l₁ l₂ k₁ k₂ N p.1 p.2
        * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2)
      (circleMeasure.prod circleMeasure) :=
    integrable_coeff_integrand hmeasc hCcb a b
  have hIm : Integrable (fun p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
      modSymbC ρ P l₁ l₂ k₁ k₂ N p.1 p.2
        * fourier (T := 1) (-a) p.1 * fourier (T := 1) (-b) p.2)
      (circleMeasure.prod circleMeasure) :=
    integrable_coeff_integrand hmeasm hCmb a b
  have hSp : ∀ p ∈ (diffFreqs ρ l₁) ×ˢ (diffFreqs ρ l₂), Integrable
      (fun q : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) =>
        spikeSymb ρ P l₁ l₂ k₁ k₂ N p.1 p.2 q.1 q.2
          * fourier (T := 1) (-a) q.1 * fourier (T := 1) (-b) q.2)
      (circleMeasure.prod circleMeasure) := by
    intro p hp
    obtain ⟨hms, Cs, hCsnn, hCsb⟩ :=
      spikeSymbMeasBdd ρ P l₁ l₂ k₁ k₂ N hw₁2 hw₂2 hsup₁ hsup₂ p.1 p.2
    exact integrable_coeff_integrand hms hCsb a b
  have hK : smallKconc ρ P l₁ l₂ k₁ k₂ N a b - smallKmod ρ P l₁ l₂ k₁ k₂ N a b
      = coeff (concSymb ρ P l₁ l₂ k₁ k₂ N) a b
        - coeff (modSymbC ρ P l₁ l₂ k₁ k₂ N) a b := by
    rw [smallKconc_eq_coeff ρ P l₁ l₂ k₁ k₂ N a b,
      smallKmod_eq_coeff_modSymbC ρ P l₁ l₂ k₁ k₂ N a b]
  rw [hK]
  have hsub : (fun θ₁ θ₂ : AddCircle (1 : ℝ) =>
        concSymb ρ P l₁ l₂ k₁ k₂ N θ₁ θ₂ - modSymbC ρ P l₁ l₂ k₁ k₂ N θ₁ θ₂)
      = concSymb ρ P l₁ l₂ k₁ k₂ N - modSymbC ρ P l₁ l₂ k₁ k₂ N := rfl
  have hcol : (fun θ₁ θ₂ : AddCircle (1 : ℝ) =>
        concSymb ρ P l₁ l₂ k₁ k₂ N θ₁ θ₂ - modSymbC ρ P l₁ l₂ k₁ k₂ N θ₁ θ₂)
      = fun θ₁ θ₂ : AddCircle (1 : ℝ) =>
          ∑ β₁ ∈ diffFreqs ρ l₁, ∑ β₂ ∈ diffFreqs ρ l₂,
            spikeSymb ρ P l₁ l₂ k₁ k₂ N β₁ β₂ θ₁ θ₂ := by
    rw [hsub]
    exact concSymb_sub_modSymbC_eq_sum_spikeSymb ρ P l₁ l₂ k₁ k₂ N
      (le_trans (by norm_num) hdeg) hw₁2 hw₂2 hsup₁ hsup₂ hw₁u hw₂u hu hNA₁ hNA₂
  have hsumfun : (fun θ₁ θ₂ : AddCircle (1 : ℝ) =>
        ∑ β₁ ∈ diffFreqs ρ l₁, ∑ β₂ ∈ diffFreqs ρ l₂,
          spikeSymb ρ P l₁ l₂ k₁ k₂ N β₁ β₂ θ₁ θ₂)
      = fun θ₁ θ₂ : AddCircle (1 : ℝ) =>
          ∑ p ∈ (diffFreqs ρ l₁) ×ˢ (diffFreqs ρ l₂),
            spikeSymb ρ P l₁ l₂ k₁ k₂ N p.1 p.2 θ₁ θ₂ := by
    funext θ₁ θ₂
    rw [Finset.sum_product]
  calc coeff (concSymb ρ P l₁ l₂ k₁ k₂ N) a b - coeff (modSymbC ρ P l₁ l₂ k₁ k₂ N) a b
      = coeff (fun θ₁ θ₂ : AddCircle (1 : ℝ) =>
          concSymb ρ P l₁ l₂ k₁ k₂ N θ₁ θ₂ - modSymbC ρ P l₁ l₂ k₁ k₂ N θ₁ θ₂) a b :=
        (coeff_sub (concSymb ρ P l₁ l₂ k₁ k₂ N) (modSymbC ρ P l₁ l₂ k₁ k₂ N) a b
          hIc hIm).symm
    _ = coeff (fun θ₁ θ₂ : AddCircle (1 : ℝ) =>
          ∑ p ∈ (diffFreqs ρ l₁) ×ˢ (diffFreqs ρ l₂),
            spikeSymb ρ P l₁ l₂ k₁ k₂ N p.1 p.2 θ₁ θ₂) a b := by rw [hcol, hsumfun]
    _ = ∑ p ∈ (diffFreqs ρ l₁) ×ˢ (diffFreqs ρ l₂),
          coeff (spikeSymb ρ P l₁ l₂ k₁ k₂ N p.1 p.2) a b :=
        coeff_finset_sum ((diffFreqs ρ l₁) ×ˢ (diffFreqs ρ l₂))
          (fun p θ₁ θ₂ => spikeSymb ρ P l₁ l₂ k₁ k₂ N p.1 p.2 θ₁ θ₂) a b hSp

end

end Work.KMTAreas.A7.Cpz

namespace Work.KMTAreas.A7.Cpz
open Work.KMTAreas.A7 Work.KMTAreas.A7z Work.KMTAreas.A7.Cpy

noncomputable section

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators

/-- The torus `𝕋 = ℝ/ℤ`, under a local name (the workspace's `Circle`, which clashes with the
root `Circle` of `ℂ`). -/
local notation "Torus" => Work.Analysis.IonescuWainger.Circle

/-! ## Auxiliary lemmas for `spikeFinsetMassBound` -/

/-- A bump supported in `|x| ≤ 1/4` vanishes off the closed quarter-interval. -/
theorem spikeAux_zero_of_not_mem_Icc_quarter {h : ℝ → ℂ}
    (hh : ∀ x : ℝ, h x ≠ 0 → |x| ≤ 1 / 4) :
    ∀ x : ℝ, x ∉ Set.Icc (-(1 / 4) : ℝ) (1 / 4) → h x = 0 := by
  intro x hx
  by_contra hne
  exact hx (by rw [Set.mem_Icc]; exact abs_le.mp (hh x hne))

/-- The canonical lift of the class of `a` is `a` when `-(1/2) < a < 1/2`. -/
theorem spikeAux_lift_coe_of_lt {a : ℝ} (ha : a < 1 / 2) (ha' : -(1 / 2) < a) :
    lift ((a : ℝ) : Torus) = a := by
  have hmem : a ∈ Set.Ico (-(1 / 2) : ℝ) (-(1 / 2) + 1) := by
    rw [Set.mem_Ico, show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num]
    exact ⟨le_of_lt ha', ha⟩
  have h1 : lift ((a : ℝ) : Torus) ∈ Set.Ico (-(1 / 2) : ℝ) (-(1 / 2) + 1) := by
    rw [Set.mem_Ico, show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num]
    exact Set.mem_Ico.mp (lift_mem ((a : ℝ) : Torus))
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := -(1 / 2)) h1 hmem).mp
    (by rw [lift_coe])

/-- The canonical lift of the class of `1/2` is `-1/2`. -/
theorem spikeAux_lift_coe_half : lift (((1 / 2 : ℝ)) : Torus) = -(1 / 2) := by
  have hmem : (-(1 / 2) : ℝ) ∈ Set.Ico (-(1 / 2)) (-(1 / 2) + 1) := by
    rw [Set.mem_Ico, show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num]
    exact ⟨le_rfl, by norm_num⟩
  have h1 : lift (((1 / 2 : ℝ)) : Torus) ∈ Set.Ico (-(1 / 2) : ℝ) (-(1 / 2) + 1) := by
    rw [Set.mem_Ico, show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num]
    exact Set.mem_Ico.mp (lift_mem (((1 / 2 : ℝ)) : Torus))
  have hcoe : (((1 / 2 : ℝ)) : Torus) = ((-(1 / 2) : ℝ) : Torus) := by
    rw [← AddCircle.coe_add_period (x := (-(1 / 2) : ℝ))]
    congr 1
    norm_num
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := -(1 / 2)) h1 hmem).mp
    (by rw [lift_coe, hcoe])

/-- **The one-dimensional fold.**  A function `h` of `ℝ` supported in `[-1/4,1/4]`, composed with
the canonical lift `lift : 𝕋 → [-1/2,1/2)`, has the same integral against Haar measure on `𝕋` as
`h` itself has against Lebesgue measure on `ℝ`. -/
theorem spikeAux_integral_lift_mul_eq (h : ℝ → ℂ) (c : Torus → ℂ)
    (hh : ∀ x : ℝ, h x ≠ 0 → |x| ≤ 1 / 4) :
    (∫ θ : Torus, h (lift θ) * c θ ∂AddCircle.haarAddCircle)
      = ∫ x : ℝ, h x * c ((x : ℝ) : Torus) := by
  have hzero := spikeAux_zero_of_not_mem_Icc_quarter hh
  have hmain : (∫ θ : Torus, h (lift θ) * c θ)
      = ∫ x : ℝ, h x * c ((x : ℝ) : Torus) := by
    have hpre := AddCircle.integral_preimage (T := (1 : ℝ)) (-(1 / 2))
      (fun θ : Torus => h (lift θ) * c θ)
    rw [← hpre]
    rw [show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num]
    have hcongr : (∫ x in Set.Ioc (-(1 / 2)) (1 / 2), h (lift ((x : ℝ) : Torus))
          * c ((x : ℝ) : Torus))
        = ∫ x in Set.Ioc (-(1 / 2)) (1 / 2), h x * c ((x : ℝ) : Torus) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      rw [Set.mem_Ioc] at hx
      rcases lt_or_eq_of_le hx.2 with hlt | heq
      · rw [spikeAux_lift_coe_of_lt hlt hx.1]
      · subst heq
        rw [spikeAux_lift_coe_half,
          hzero (-(1 / 2)) (by rw [Set.mem_Icc]; norm_num),
          hzero (1 / 2) (by rw [Set.mem_Icc]; norm_num)]
    rw [hcongr]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hx0 : h x = 0 := hzero x fun hmem => by
      rw [Set.mem_Icc] at hmem
      exact hx (Set.mem_Ioc.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩)
    rw [hx0, zero_mul]
  rw [AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  exact hmain

/-- The character `fourier (-n)` at a real point is the exponential `kE n`. -/
theorem spikeAux_fourier_neg_coe_eq_kE (n : ℤ) (x : ℝ) :
    fourier (T := 1) (-n) ((x : ℝ) : Torus) = kE (n : ℝ) x := by
  rw [fourier_coe_apply]
  simp only [kE]
  congr 1
  push_cast
  ring_nf

/-- A character of the circle is additive in its argument. -/
theorem spikeAux_fourier_add_arg (n : ℤ) (x y : Torus) :
    fourier (T := 1) n (x + y) = fourier (T := 1) n x * fourier (T := 1) n y := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

/-- A character has modulus one. -/
theorem spikeAux_norm_fourier (n : ℤ) (θ : Torus) : ‖fourier (T := 1) n θ‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- **The one-dimensional fold, translated and against a character.** -/
theorem spikeAux_fold_shift (h : ℝ → ℂ) (c : Torus → ℂ) (α : Torus)
    (hh : ∀ x : ℝ, h x ≠ 0 → |x| ≤ 1 / 4) :
    (∫ θ : Torus, h (lift (θ - α)) * c θ ∂AddCircle.haarAddCircle)
      = ∫ x : ℝ, h x * c (((x : ℝ) : Torus) + α) := by
  have h1 : (∫ θ : Torus, h (lift (θ - α)) * c θ ∂AddCircle.haarAddCircle)
      = ∫ u : Torus, h (lift u) * c (u + α) ∂AddCircle.haarAddCircle := by
    have hshift := MeasureTheory.integral_add_right_eq_self (μ := AddCircle.haarAddCircle)
      (fun u : Torus => h (lift u) * c (u + α)) (-α)
    rw [← hshift]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    show h (lift (θ - α)) * c θ = h (lift (θ + -α)) * c (θ + -α + α)
    simp only [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]
  rw [h1]
  exact spikeAux_integral_lift_mul_eq h (fun u : Torus => c (u + α)) hh

/-- **The one-dimensional fold, translated, against a character, with the shift extracted.** -/
theorem spikeAux_fold_fourier (h : ℝ → ℂ) (n : ℤ) (α : Torus)
    (hh : ∀ x : ℝ, h x ≠ 0 → |x| ≤ 1 / 4) :
    (∫ θ : Torus, h (lift (θ - α)) * fourier (T := 1) n θ ∂AddCircle.haarAddCircle)
      = fourier (T := 1) n α * ∫ x : ℝ, h x * fourier (T := 1) n ((x : ℝ) : Torus) := by
  rw [spikeAux_fold_shift h (fourier (T := 1) n) α hh]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show h x * fourier (T := 1) n (((x : ℝ) : Torus) + α)
      = fourier (T := 1) n α * (h x * fourier (T := 1) n ((x : ℝ) : Torus))
  rw [spikeAux_fourier_add_arg]
  ring

/-- The two-dimensional Fourier integral in the vocabulary of `mass_fourier_le`. -/
theorem spikeAux_coeff_fold (G : ℝ → ℝ → ℂ) (a b : ℤ) :
    (∫ x₁ : ℝ, ∫ x₂ : ℝ, G x₁ x₂ * fourier (T := 1) (-a) ((x₁ : ℝ) : Torus)
        * fourier (T := 1) (-b) ((x₂ : ℝ) : Torus)) = kInt G (a, b) := by
  show (∫ x₁ : ℝ, ∫ x₂ : ℝ, G x₁ x₂ * fourier (T := 1) (-a) ((x₁ : ℝ) : Torus)
        * fourier (T := 1) (-b) ((x₂ : ℝ) : Torus))
      = ∫ x₁ : ℝ, ∫ x₂ : ℝ, G x₁ x₂ * kE (a : ℝ) x₁ * kE (b : ℝ) x₂
  simp only [spikeAux_fourier_neg_coe_eq_kE]

/-- **The two-dimensional fold with translation.**  The Fourier coefficients of the spike
`(θ₁,θ₂) ↦ G (lift (θ₁-α₁)) (lift (θ₂-α₂))` are, up to the unimodular factors
`fourier(-a) α₁ · fourier(-b) α₂`, the two-dimensional Fourier integrals of `G`. -/
theorem spikeAux_coeff_shift_fold (G : ℝ → ℝ → ℂ) (α₁ α₂ : Torus) (a b : ℤ)
    (hG₁ : ∀ x₁ x₂ : ℝ, G x₁ x₂ ≠ 0 → |x₁| ≤ 1 / 4)
    (hG₂ : ∀ x₁ x₂ : ℝ, G x₁ x₂ ≠ 0 → |x₂| ≤ 1 / 4) :
    coeff (fun θ₁ θ₂ : Torus => G (lift (θ₁ - α₁)) (lift (θ₂ - α₂))) a b
      = fourier (T := 1) (-a) α₁ * fourier (T := 1) (-b) α₂ * kInt G (a, b) := by
  have hH : ∀ x₁ : ℝ, (∫ x₂ : ℝ, G x₁ x₂ * fourier (T := 1) (-b) ((x₂ : ℝ) : Torus)) ≠ 0 →
      |x₁| ≤ 1 / 4 := by
    intro x₁ hne
    by_contra hlt
    push_neg at hlt
    have hz : ∀ x₂ : ℝ, G x₁ x₂ = 0 := by
      intro x₂
      by_contra hne2
      exact absurd (hG₁ x₁ x₂ hne2) (not_le.mpr hlt)
    exact hne (by simp only [hz, zero_mul, integral_zero])
  have hinner : ∀ θ₁ : Torus,
      (∫ θ₂ : Torus, G (lift (θ₁ - α₁)) (lift (θ₂ - α₂)) * fourier (T := 1) (-a) θ₁
          * fourier (T := 1) (-b) θ₂ ∂AddCircle.haarAddCircle)
        = fourier (T := 1) (-a) θ₁ * (fourier (T := 1) (-b) α₂
            * ∫ x₂ : ℝ, G (lift (θ₁ - α₁)) x₂
              * fourier (T := 1) (-b) ((x₂ : ℝ) : Torus)) := by
    intro θ₁
    have h1 : (∫ θ₂ : Torus, G (lift (θ₁ - α₁)) (lift (θ₂ - α₂)) * fourier (T := 1) (-a) θ₁
          * fourier (T := 1) (-b) θ₂ ∂AddCircle.haarAddCircle)
        = fourier (T := 1) (-a) θ₁
          * ∫ θ₂ : Torus, G (lift (θ₁ - α₁)) (lift (θ₂ - α₂))
              * fourier (T := 1) (-b) θ₂ ∂AddCircle.haarAddCircle := by
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ₂ => by ring)
    have h2 : (∫ θ₂ : Torus, G (lift (θ₁ - α₁)) (lift (θ₂ - α₂))
          * fourier (T := 1) (-b) θ₂ ∂AddCircle.haarAddCircle)
        = fourier (T := 1) (-b) α₂ * ∫ x₂ : ℝ, G (lift (θ₁ - α₁)) x₂
              * fourier (T := 1) (-b) ((x₂ : ℝ) : Torus) :=
      spikeAux_fold_fourier (fun x₂ : ℝ => G (lift (θ₁ - α₁)) x₂) (-b) α₂
        (fun x₂ hx => hG₂ (lift (θ₁ - α₁)) x₂ hx)
    rw [h1, h2]
  have hstep : (∫ θ₁ : Torus, (∫ x₂ : ℝ, G (lift (θ₁ - α₁)) x₂
        * fourier (T := 1) (-b) ((x₂ : ℝ) : Torus)) * fourier (T := 1) (-a) θ₁
        ∂AddCircle.haarAddCircle)
      = fourier (T := 1) (-a) α₁ * ∫ x₁ : ℝ, (∫ x₂ : ℝ, G x₁ x₂
            * fourier (T := 1) (-b) ((x₂ : ℝ) : Torus))
          * fourier (T := 1) (-a) ((x₁ : ℝ) : Torus) :=
    spikeAux_fold_fourier
      (fun x₁ : ℝ => ∫ x₂ : ℝ, G x₁ x₂ * fourier (T := 1) (-b) ((x₂ : ℝ) : Torus))
      (-a) α₁ (fun x₁ => hH x₁)
  have hstep2 : (∫ x₁ : ℝ, (∫ x₂ : ℝ, G x₁ x₂
        * fourier (T := 1) (-b) ((x₂ : ℝ) : Torus))
        * fourier (T := 1) (-a) ((x₁ : ℝ) : Torus)) = kInt G (a, b) := by
    have h3 : (∫ x₁ : ℝ, (∫ x₂ : ℝ, G x₁ x₂
          * fourier (T := 1) (-b) ((x₂ : ℝ) : Torus))
          * fourier (T := 1) (-a) ((x₁ : ℝ) : Torus))
        = ∫ x₁ : ℝ, ∫ x₂ : ℝ, G x₁ x₂ * fourier (T := 1) (-a) ((x₁ : ℝ) : Torus)
            * fourier (T := 1) (-b) ((x₂ : ℝ) : Torus) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x₁ => by
        show (∫ x₂ : ℝ, G x₁ x₂ * fourier (T := 1) (-b) ((x₂ : ℝ) : Torus))
            * fourier (T := 1) (-a) ((x₁ : ℝ) : Torus)
          = ∫ x₂ : ℝ, G x₁ x₂ * fourier (T := 1) (-a) ((x₁ : ℝ) : Torus)
              * fourier (T := 1) (-b) ((x₂ : ℝ) : Torus)
        rw [← MeasureTheory.integral_mul_const]
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x₂ => by ring))
    rw [h3]
    exact spikeAux_coeff_fold G a b
  simp only [coeff]
  trans (∫ θ₁ : Torus, fourier (T := 1) (-a) θ₁ * (fourier (T := 1) (-b) α₂
      * ∫ x₂ : ℝ, G (lift (θ₁ - α₁)) x₂ * fourier (T := 1) (-b) ((x₂ : ℝ) : Torus))
      ∂AddCircle.haarAddCircle)
  · exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner)
  trans (fourier (T := 1) (-b) α₂ * ∫ θ₁ : Torus, (∫ x₂ : ℝ, G (lift (θ₁ - α₁)) x₂
      * fourier (T := 1) (-b) ((x₂ : ℝ) : Torus)) * fourier (T := 1) (-a) θ₁
      ∂AddCircle.haarAddCircle)
  · rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ₁ => by ring)
  trans (fourier (T := 1) (-b) α₂ * (fourier (T := 1) (-a) α₁ * ∫ x₁ : ℝ,
      (∫ x₂ : ℝ, G x₁ x₂ * fourier (T := 1) (-b) ((x₂ : ℝ) : Torus))
        * fourier (T := 1) (-a) ((x₁ : ℝ) : Torus)))
  · rw [hstep]
  trans (fourier (T := 1) (-b) α₂ * (fourier (T := 1) (-a) α₁ * kInt G (a, b)))
  · rw [hstep2]
  ring

/-- **The per-spike estimate.**  For a `C⁴` symbol `G` supported in the box
`[-w₁,w₁] × [-w₂,w₂]` with `‖G‖ ≤ B`, `‖∂₁²G‖ ≤ B/w₁²`, `‖∂₂²G‖ ≤ B/w₂²` and
`‖∂₁²∂₂²G‖ ≤ B/(w₁²w₂²)`, the `ℓ¹(ℤ²)`-mass of the Fourier coefficients of *any* translate
`G (lift (·-α₁)) (lift (·-α₂))` of `G` is at most `200 B`. -/
theorem spikeAux_mass_le (G : ℝ → ℝ → ℂ) {w₁ w₂ B : ℝ}
    (hcd : ContDiff ℝ 4 (fun x : ℝ × ℝ => G x.1 x.2))
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw₁2 : w₁ ≤ 1 / 4) (hw₂2 : w₂ ≤ 1 / 4) (hB : 0 ≤ B)
    (hsupp : ∀ x₁ x₂ : ℝ, G x₁ x₂ ≠ 0 → |x₁| ≤ w₁ ∧ |x₂| ≤ w₂)
    (h00 : ∀ x₁ x₂ : ℝ, ‖G x₁ x₂‖ ≤ B)
    (h20 : ∀ x₁ x₂ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ => G y x₂) x₁‖ ≤ B / w₁ ^ 2)
    (h02 : ∀ x₁ x₂ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ => G x₁ y) x₂‖ ≤ B / w₂ ^ 2)
    (h22 : ∀ x₁ x₂ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ =>
        iteratedDeriv 2 (fun z : ℝ => G z y) x₁) x₂‖ ≤ B / (w₁ ^ 2 * w₂ ^ 2))
    (α₁ α₂ : Torus) :
    smKernMass (fun a b : ℤ => coeff (fun θ₁ θ₂ : Torus =>
        G (lift (θ₁ - α₁)) (lift (θ₂ - α₂))) a b) ≤ ENNReal.ofReal (200 * B) := by
  have hsp₁ : ∀ x₁ x₂ : ℝ, G x₁ x₂ ≠ 0 → |x₁| ≤ 1 / 4 :=
    fun x₁ x₂ h => le_trans (hsupp x₁ x₂ h).1 hw₁2
  have hsp₂ : ∀ x₁ x₂ : ℝ, G x₁ x₂ ≠ 0 → |x₂| ≤ 1 / 4 :=
    fun x₁ x₂ h => le_trans (hsupp x₁ x₂ h).2 hw₂2
  obtain ⟨hsum, hbound⟩ := massF_summ_and_bound G w₁ w₂ B hcd hw₁ hw₂
    (le_trans hw₁2 (by norm_num)) (le_trans hw₂2 (by norm_num)) hB hsupp h00 h20 h02 h22
  have hkey : ∀ a b : ℤ, ‖coeff (fun θ₁ θ₂ : Torus =>
      G (lift (θ₁ - α₁)) (lift (θ₂ - α₂))) a b‖ = ‖kInt G (a, b)‖ := by
    intro a b
    rw [spikeAux_coeff_shift_fold G α₁ α₂ a b hsp₁ hsp₂, norm_mul, norm_mul,
      spikeAux_norm_fourier, spikeAux_norm_fourier, one_mul, one_mul]
  have hsumK : Summable fun p : ℤ × ℤ => ‖coeff (fun θ₁ θ₂ : Torus =>
      G (lift (θ₁ - α₁)) (lift (θ₂ - α₂))) p.1 p.2‖ :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => (hkey p.1 p.2).le) hsum
  rw [smKernMass_eq_ofReal_tsum hsumK]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (∑' p : ℤ × ℤ, ‖coeff (fun θ₁ θ₂ : Torus =>
        G (lift (θ₁ - α₁)) (lift (θ₂ - α₂))) p.1 p.2‖)
      = ∑' p : ℤ × ℤ, ‖kInt G p‖ := tsum_congr fun p => hkey p.1 p.2
    _ ≤ 200 * B := hbound

theorem spikeFinsetMassBound (ρ : ℝ) (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree)
    (l₁ l₂ k₁ k₂ N : ℕ) {w₁ w₂ B : ℝ}
    (hN : 1 ≤ N)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw₁2 : w₁ ≤ 1 / 4) (hw₂2 : w₂ ≤ 1 / 4) (hB : 0 ≤ B)
    (hsup₁ : ∀ x : ℝ, Work.KMTAreas.A7.varphiN N k₁ x ≠ 0 → |x| ≤ w₁)
    (hsup₂ : ∀ x : ℝ, Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ x ≠ 0 → |x| ≤ w₂)
    (hspike : ∀ β₁ ∈ Work.KMTAreas.A7.diffFreqs ρ l₁, ∀ β₂ ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
      ContDiff ℝ 4 (fun p : ℝ × ℝ =>
          Work.KMTAreas.A7.spikeProfile P N k₁ k₂ (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) β₁ β₂ p.1 p.2) ∧
      (∀ x₁ x₂ : ℝ, Work.KMTAreas.A7.spikeProfile P N k₁ k₂ (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) β₁ β₂ x₁ x₂ ≠ 0 →
        |x₁| ≤ w₁ ∧ |x₂| ≤ w₂) ∧
      (∀ x₁ x₂ : ℝ, ‖Work.KMTAreas.A7.spikeProfile P N k₁ k₂ (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) β₁ β₂ x₁ x₂‖ ≤ B) ∧
      (∀ x₁ x₂ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ =>
          Work.KMTAreas.A7.spikeProfile P N k₁ k₂ (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) β₁ β₂ y x₂) x₁‖ ≤ B / w₁ ^ 2) ∧
      (∀ x₁ x₂ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ =>
          Work.KMTAreas.A7.spikeProfile P N k₁ k₂ (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) β₁ β₂ x₁ y) x₂‖ ≤ B / w₂ ^ 2) ∧
      (∀ x₁ x₂ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ => iteratedDeriv 2 (fun z : ℝ =>
          Work.KMTAreas.A7.spikeProfile P N k₁ k₂ (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) β₁ β₂ z y) x₁) x₂‖
            ≤ B / (w₁ ^ 2 * w₂ ^ 2))) :
    Work.KMTAreas.A7.smKernMass (fun a b : ℤ =>
        ∑ p ∈ (Work.KMTAreas.A7.diffFreqs ρ l₁) ×ˢ (Work.KMTAreas.A7.diffFreqs ρ l₂),
          Work.KMTAreas.A7.coeff (Work.KMTAreas.A7.spikeSymb ρ P l₁ l₂ k₁ k₂ N p.1 p.2) a b)
      ≤ ENNReal.ofReal (200 * (((Work.KMTAreas.A7.diffFreqs ρ l₁).card : ℝ)
          * ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ)) * B) := by
  classical
  have hper : ∀ p ∈ (diffFreqs ρ l₁) ×ˢ (diffFreqs ρ l₂),
      smKernMass (fun a b : ℤ => coeff (spikeSymb ρ P l₁ l₂ k₁ k₂ N p.1 p.2) a b)
        ≤ ENNReal.ofReal (200 * B) := by
    intro p hp
    obtain ⟨hβ₁, hβ₂⟩ := Finset.mem_product.mp hp
    obtain ⟨hcd, hsupp, h00, h20, h02, h22⟩ := hspike p.1 hβ₁ p.2 hβ₂
    have hw₁' : w₁ < 1 / 2 := by linarith
    have hw₂' : w₂ < 1 / 2 := by linarith
    have hkey : spikeSymb ρ P l₁ l₂ k₁ k₂ N p.1 p.2
        = fun θ₁ θ₂ : Torus => spikeProfile P N k₁ k₂ (arithQ ρ (max l₁ l₂)) p.1 p.2
            (lift (θ₁ - p.1)) (lift (θ₂ - p.2)) := by
      funext θ₁ θ₂
      unfold spikeSymb bumpSymb spikeProfile
      rw [periodize_eq_lift hw₁' (fun x hx => hsup₁ x hx) (θ₁ - p.1),
          periodize_eq_lift hw₂' (fun x hx => hsup₂ x hx) (θ₂ - p.2)]
    rw [hkey]
    exact spikeAux_mass_le
      (fun x₁ x₂ : ℝ => spikeProfile P N k₁ k₂ (arithQ ρ (max l₁ l₂)) p.1 p.2 x₁ x₂)
      hcd hw₁ hw₂ hw₁2 hw₂2 hB hsupp h00 h20 h02 h22 p.1 p.2
  have hmain := smKernMass_finset_sum_le ((diffFreqs ρ l₁) ×ˢ (diffFreqs ρ l₂))
    (fun p a b => coeff (spikeSymb ρ P l₁ l₂ k₁ k₂ N p.1 p.2) a b) (fun _ => 200 * B)
    (fun i _ => by positivity) hper
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hcard : (∑ i ∈ (diffFreqs ρ l₁) ×ˢ (diffFreqs ρ l₂), 200 * B)
      = 200 * (((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ)) * B := by
    rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]
    push_cast
    ring
  exact hcard.le


end

end Work.KMTAreas.A7.Cpz


namespace Work.KMTAreas.A7z
open Work.KMTAreas.A7 Work.KMTAreas.A7.Cpy

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-! ## An elementary structural lemma about `smKernMass` -/

/-- The `ℓ¹(ℤ²)`-mass is subadditive. -/
theorem smKernMass_sub_le {K L : ℤ → ℤ → ℂ} :
    smKernMass (fun a b => K a b - L a b) ≤ smKernMass K + smKernMass L := by
  rw [smKernMass, smKernMass, smKernMass]
  calc ∑' p : ℤ × ℤ, ‖K p.1 p.2 - L p.1 p.2‖ₑ
      ≤ ∑' p : ℤ × ℤ, (‖K p.1 p.2‖ₑ + ‖L p.1 p.2‖ₑ) :=
        ENNReal.tsum_le_tsum fun p => by
          simpa only [enorm_eq_nnnorm, ← ENNReal.coe_add] using
            ENNReal.coe_le_coe.mpr (nnnorm_sub_le (K p.1 p.2) (L p.1 p.2))
    _ = (∑' p : ℤ × ℤ, ‖K p.1 p.2‖ₑ) + (∑' p : ℤ × ℤ, ‖L p.1 p.2‖ₑ) :=
        ENNReal.tsum_add

end

end Work.KMTAreas.A7z

namespace Work.KMTAreas.A7z
open Work.KMTAreas.A7 Work.KMTAreas.A7.Cpy

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.EndVar

/-! ## Elementary reductions used by the regime split -/

/-- **A period of an exact-height arithmetic frequency.**  Every frequency `β` of exact height
`≤ 2^l` is killed by some `q` in the Ionescu--Wainger denominator set `P_{≤l}`, and every such `q`
is at most `2^{C·2^{ρl}}` (`iwP_element_le`). -/
theorem exists_period_diffFreqs (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l : ℕ) (β : Work.Analysis.IonescuWainger.Circle),
      β ∈ diffFreqs ρ l →
      ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ (2 : ℝ) ^ (C * (2 : ℝ) ^ (ρ * (l : ℝ))) ∧ q • β = 0 := by
  obtain ⟨C, hC, hCb⟩ := iwP_element_le hρ
  refine ⟨C, hC, fun l β hβ => ?_⟩
  have hβ' : β ∈ iwArithFreqs ρ l := diffFreqs_subset_iwArithFreqs hρ hρ1 (le_refl l) hβ
  obtain ⟨q, hq, hqβ⟩ := mem_iwArithFreqs.mp hβ'
  exact ⟨q, Nat.one_le_iff_ne_zero.mpr (ne_zero_of_mem_iwP hq), hCb l q hq, hqβ⟩

/-- The auxiliary scale `uScale ρ L = ⌊2^{2ρL}⌋` is at least `1`. -/
theorem one_le_uScale (ρ : ℝ) (hρ : 0 ≤ ρ) (L : ℕ) : 1 ≤ uScale ρ L := by
  have h : ((1 : ℤ) : ℝ) ≤ (1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
    push_cast
    rw [one_mul]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have h2 : (1 : ℤ) ≤ ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ := Int.le_floor.mpr h
  have h3 : (0 : ℤ) ≤ ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ := le_trans (by norm_num) h2
  have h4 : (1 : ℤ) ≤ (⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋.toNat : ℤ) := by
    rw [Int.toNat_of_nonneg h3]; exact h2
  have h5 : uScale ρ L = ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋.toNat := by
    unfold uScale scaleCount
    norm_num
  rw [h5]
  exact_mod_cast h4

/-- `smallCond` is monotone in the constant `C₀` of the index set. -/
theorem smallCond_mono_C₀ {ρ : ℝ} {C₀ C₀' : ℕ} {a : ℕ → NNReal} {l₁ l₂ k₁ k₂ n : ℕ}
    (h : C₀ ≤ C₀') (hc : smallCond ρ C₀ a l₁ l₂ k₁ k₂ n) :
    smallCond ρ C₀' a l₁ l₂ k₁ k₂ n := by
  obtain ⟨h1, h2, h3⟩ := hc
  obtain ⟨h4, h5, h6⟩ := h1
  have hhs : (heightScale C₀ (Nat.floor (a n)) : ℤ)
      ≤ (heightScale C₀' (Nat.floor (a n)) : ℤ) := by
    have : heightScale C₀ (Nat.floor (a n)) ≤ heightScale C₀' (Nat.floor (a n)) := by
      unfold heightScale
      exact Nat.mul_le_mul_right _ h
    exact_mod_cast this
  exact ⟨⟨le_trans h4 hhs, le_trans h5 hhs, le_trans h6 hhs⟩, h2, h3⟩

/-- The integer logarithm `logN N` agrees with its `toNat` as a real number. -/
theorem logN_toNat_cast (N : ℕ) :
    ((logN N : ℤ) : ℝ) = (((logN N).toNat : ℕ) : ℝ) := by
  have h1 : (((logN N : ℤ)) : ℝ) = (((logN N).toNat : ℤ) : ℝ) := by
    rw [Int.toNat_of_nonneg (logN_nonneg N)]
  have h2 : (((logN N).toNat : ℤ) : ℝ) = (((logN N).toNat : ℕ) : ℝ) := by push_cast; ring
  rw [h1, h2]

end

end Work.KMTAreas.A7z

namespace Work.KMTAreas.A7z
open Work.KMTAreas.A7 Work.KMTAreas.A7.Cpy

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.EndVar

/-- The maximum height of the small-scale parameters is `smallL`, as a real. -/
lemma lmaxR_eq_smallL (l₁ l₂ k₁ k₂ : ℕ) :
    lmaxR l₁ l₂ k₁ k₂ = ((smallL l₁ l₂ k₁ k₂ : ℕ) : ℝ) := by
  simp only [lmaxR, smallL, Work.Analysis.EndVar.lmax]
  push_cast
  rfl

theorem smallKernelMass_le (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) :
    ∀ (C₀ : ℕ), ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ n : ℕ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
          Work.KMTAreas.A7.smallCond ρ C₀ a l₁ l₂ k₁ k₂ n →
          Work.KMTAreas.A7.smKernMass
              (fun x y : ℤ =>
                Work.KMTAreas.A7.smallKconc ρ P l₁ l₂ k₁ k₂ (Nat.floor (a n)) x y
                  - Work.KMTAreas.A7.smallKmod ρ P l₁ l₂ k₁ k₂ (Nat.floor (a n)) x y)
            ≤ (K Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.smallScaleWeight C ρ l₁ l₂ k₁ k₂)
                * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) := by
  intro C₀
  set C₀' : ℕ := max C₀ 1 with hC₀'def
  have hC₀'1 : 1 ≤ C₀' := le_max_right _ _
  have hC₀'max : C₀ ≤ C₀' := le_max_left _ _
  refine ⟨min 1 (1 / (8 * (C₀' : ℝ))), lt_min one_pos (by positivity), ?_⟩
  intro ρ hρ hρρ
  have hρ1 : ρ ≤ 1 := le_trans hρρ (min_le_left _ _)
  have hρC : ρ ≤ 1 / (8 * (C₀' : ℝ)) := le_trans hρρ (min_le_right _ _)
  obtain ⟨Ccard, hCcardpos, hCcard⟩ := iw_height_card_le (ρ := ρ) hρ
  obtain ⟨Cper, hCperpos, hCper⟩ := exists_period_diffFreqs ρ hρ hρ1
  obtain ⟨Csp, Asp, hCsppos, hAspnn, hspb⟩ := spike_profile_bounds_q P hdeg
  obtain ⟨C, hCnn, hweight⟩ :=
    spike_sum_weight ρ hρ Ccard (2 * Cper + 1) Csp Asp hCcardpos (by linarith) hCsppos hAspnn
  obtain ⟨D₀, hD₀⟩ := smallCond_bad_bounded C₀' hC₀'1 ρ hρ hρC
  obtain ⟨D₁, hD₁⟩ := smallL_le_of_not_nonAliasing ρ hρ hρ1
  set D : ℕ := max D₀ (max D₁ (splitCut ρ D₁)) with hDdef
  have hD₀D : D₀ ≤ D := by rw [hDdef]; exact le_max_left _ _
  have hD₁D : D₁ ≤ D := by
    rw [hDdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hDcut : splitCut ρ D₁ ≤ D := by
    rw [hDdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨Bc, hBcnn, hBc⟩ := Work.KMTAreas.A7.Cpz.crude_mass_bound ρ hρ hρ1 P D
  set Dfin : ℝ := max (Bc * (D : ℝ) + 1) 1 with hDfindef
  have hDfinnn : 0 ≤ Dfin := le_trans zero_le_one (le_max_right _ _)
  have hDfin1 : 1 ≤ Dfin := le_max_right _ _
  let K : NNReal → NNReal := fun _ => Real.toNNReal Dfin
  refine ⟨C, hCnn, K, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ n hΛ ha ha1 hcond
  set N : ℕ := Nat.floor (a n) with hNdef
  have hN1 : 1 ≤ N := by
    rw [hNdef]
    exact Nat.succ_le_of_lt (Nat.floor_pos.mpr (ha1 n))
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  set u : ℕ := uScale ρ (smallL l₁ l₂ k₁ k₂) with hudef
  set R : ℕ := (logN N).toNat with hRdef
  have hlogNcast : ((logN N : ℤ) : ℝ) = (R : ℝ) := logN_toNat_cast N
  have hhu : 1 ≤ u := by rw [hudef]; exact one_le_uScale ρ hρ.le _
  set w₁ : ℝ := (2 : ℝ) ^ ((k₁ : ℝ) - (logN N : ℝ)) with hw₁def
  set w₂ : ℝ := (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (logN N : ℝ))) with hw₂def
  have hw₁pos : 0 < w₁ := by rw [hw₁def]; positivity
  have hw₂pos : 0 < w₂ := by rw [hw₂def]; positivity
  have hsupp₁ : ∀ x : ℝ, varphiN N k₁ x ≠ 0 → |x| ≤ w₁ := by
    intro x hx
    rw [hw₁def]
    exact Work.KMTAreas.A7.Cpy.varphiN_ne_zero_abs_le N k₁ hx
  have hsupp₂ : ∀ x : ℝ, varphitildeN P.natDegree N k₂ x ≠ 0 → |x| ≤ w₂ := by
    intro x hx
    rw [hw₂def]
    exact Work.KMTAreas.A7.Cpy.varphitildeN_ne_zero_abs_le P.natDegree N k₂ (le_trans (by norm_num) hdeg) hx
  by_cases hgood : k₁ + 2 * u + 1 ≤ R ∧ k₂ + 2 * u + 1 ≤ R ∧
      NonAliasing (-(2 * (u : ℤ))) (diffFreqs ρ l₁) ∧
      NonAliasing (-(2 * (u : ℤ))) (diffFreqs ρ l₂)
  · obtain ⟨hW₁, hW₂, hNA₁, hNA₂⟩ := hgood
    have huu : ((u : ℤ) : ℝ) = (u : ℝ) := by simp
    have h1u : (1 : ℝ) ≤ (u : ℝ) := by
      have h : (1 : ℤ) ≤ (u : ℤ) := by omega
      exact_mod_cast h
    have hd1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by
      have h : 1 ≤ P.natDegree := le_trans (by norm_num) hdeg
      exact_mod_cast h
    have hR₁ : (k₁ : ℝ) + 2 * (u : ℝ) + 1 ≤ (R : ℝ) := by
      have h : ((k₁ + 2 * u + 1 : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hW₁
      push_cast at h
      linarith
    have hR₂ : (k₂ : ℝ) + 2 * (u : ℝ) + 1 ≤ (R : ℝ) := by
      have h : ((k₂ + 2 * u + 1 : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hW₂
      push_cast at h
      linarith
    have hexp₁ : (k₁ : ℝ) - (logN N : ℝ) ≤ -3 := by
      rw [hlogNcast]; linarith
    have hexp₂ : (P.natDegree : ℝ) * ((k₂ : ℝ) - (logN N : ℝ)) ≤ -3 := by
      rw [hlogNcast]
      have hkR : (k₂ : ℝ) - (R : ℝ) ≤ -3 := by linarith
      have hstep : (P.natDegree : ℝ) * ((k₂ : ℝ) - (R : ℝ)) ≤ 1 * ((k₂ : ℝ) - (R : ℝ)) :=
        mul_le_mul_of_nonpos_right hd1 (by linarith)
      linarith
    have hle₁ : (k₁ : ℝ) - (logN N : ℝ) ≤ ((-(2 * (u : ℤ)) - 1 : ℤ) : ℝ) := by
      rw [hlogNcast]; push_cast; linarith
    have hle₂ : (P.natDegree : ℝ) * ((k₂ : ℝ) - (logN N : ℝ))
        ≤ ((-((P.natDegree : ℤ) * 2 * (u : ℤ)) - 1 : ℤ) : ℝ) := by
      rw [hlogNcast]; push_cast
      nlinarith [hR₂, hd1, h1u]
    have hw₁u : w₁ ≤ (2 : ℝ) ^ (-(2 * (u : ℤ)) - 1) := by
      rw [hw₁def]
      rw [show (2 : ℝ) ^ (-(2 * (u : ℤ)) - 1)
          = (2 : ℝ) ^ (((-(2 * (u : ℤ)) - 1 : ℤ)) : ℝ) from
        (Real.rpow_intCast (2 : ℝ) (-(2 * (u : ℤ)) - 1)).symm]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hle₁
    have hw₂u : w₂ ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (u : ℤ)) - 1) := by
      rw [hw₂def]
      rw [show (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (u : ℤ)) - 1)
          = (2 : ℝ) ^ (((-((P.natDegree : ℤ) * 2 * (u : ℤ)) - 1 : ℤ)) : ℝ) from
        (Real.rpow_intCast (2 : ℝ) (-((P.natDegree : ℤ) * 2 * (u : ℤ)) - 1)).symm]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hle₂
    have h8 : (2 : ℝ) ^ (-3 : ℝ) = 1 / 8 := by
      have hcast : (-3 : ℝ) = ((-3 : ℤ) : ℝ) := by norm_num
      rw [hcast, Real.rpow_intCast]
      norm_num
    have hw₁4 : w₁ ≤ 1 / 4 := by
      rw [hw₁def]
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp₁
      rw [h8] at h
      linarith
    have hw₂4 : w₂ ≤ 1 / 4 := by
      rw [hw₂def]
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp₂
      rw [h8] at h
      linarith
    have hw₁half : w₁ < 1 / 2 := by linarith
    have hw₂half : w₂ < 1 / 2 := by linarith
    set X : ℝ := (2 : ℝ) ^ ((2 * Cper + 1) * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂)) with hXdef
    set Q : ℕ := Nat.floor X with hQdef
    set B : ℝ := Csp * (Q : ℝ) * (2 : ℝ) ^ (Asp * ((k₁ : ℝ) + (k₂ : ℝ))) / (N : ℝ) with hBdef
    have hBnn : 0 ≤ B := by rw [hBdef]; positivity
    have hXml' : (0 : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
      rw [lmaxR_eq_smallL]; positivity
    have hpowpos : (0 : ℝ) < (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hXpos : (0 : ℝ) < X := by
      rw [hXdef]
      exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
    have hQle : (Q : ℝ) ≤ X := by
      rw [hQdef]
      exact Nat.floor_le hXpos.le
    have hQpos : 1 ≤ Q := by
      rw [hQdef]
      exact Nat.succ_le_of_lt (Nat.floor_pos.mpr (Real.one_le_rpow (by norm_num)
        (mul_nonneg (by linarith) hpowpos.le)))
    have hQlow : (2 : ℝ) ^ ((2 * Cper) * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂)) ≤ (Q : ℝ) := by
      set Y : ℝ := (2 : ℝ) ^ ((2 * Cper) * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂)) with hYdef
      have hY1 : 1 ≤ Y := Real.one_le_rpow (by norm_num)
        (mul_nonneg (by linarith) hpowpos.le)
      have hsplit : (2 * Cper + 1) * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂)
          = (2 * Cper) * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂)
            + (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂) := by ring
      have hXeq : X = Y * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂)) := by
        rw [hXdef, hYdef, hsplit, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      have h2le : (2 : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂)) := by
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂) :=
          Real.one_le_rpow (by norm_num) (mul_nonneg hρ.le hXml')
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h1
      have h2Y : 2 * Y ≤ X := by
        rw [hXeq]
        calc 2 * Y = Y * 2 := by ring
          _ ≤ Y * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂)) :=
              mul_le_mul_of_nonneg_left h2le (by linarith)
      have hfloor : X < (Q : ℝ) + 1 := by rw [hQdef]; exact Nat.lt_floor_add_one X
      linarith
    have hspike : ∀ β₁ ∈ diffFreqs ρ l₁, ∀ β₂ ∈ diffFreqs ρ l₂,
        ContDiff ℝ 4 (fun p : ℝ × ℝ =>
          spikeProfile P N k₁ k₂ (arithQ ρ (max l₁ l₂)) β₁ β₂ p.1 p.2) ∧
        (∀ x₁ x₂ : ℝ, spikeProfile P N k₁ k₂ (arithQ ρ (max l₁ l₂)) β₁ β₂ x₁ x₂ ≠ 0 →
          |x₁| ≤ w₁ ∧ |x₂| ≤ w₂) ∧
        (∀ x₁ x₂ : ℝ, ‖spikeProfile P N k₁ k₂ (arithQ ρ (max l₁ l₂)) β₁ β₂ x₁ x₂‖ ≤ B) ∧
        (∀ x₁ x₂ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ =>
            spikeProfile P N k₁ k₂ (arithQ ρ (max l₁ l₂)) β₁ β₂ y x₂) x₁‖ ≤ B / w₁ ^ 2) ∧
        (∀ x₁ x₂ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ =>
            spikeProfile P N k₁ k₂ (arithQ ρ (max l₁ l₂)) β₁ β₂ x₁ y) x₂‖ ≤ B / w₂ ^ 2) ∧
        (∀ x₁ x₂ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ => iteratedDeriv 2 (fun z : ℝ =>
            spikeProfile P N k₁ k₂ (arithQ ρ (max l₁ l₂)) β₁ β₂ z y) x₁) x₂‖
              ≤ B / (w₁ ^ 2 * w₂ ^ 2)) := by
      intro β₁ hβ₁ β₂ hβ₂
      obtain ⟨q₁, hq₁1, hq₁le, hq₁per⟩ :=
        hCper l₁ β₁ hβ₁
      obtain ⟨q₂, hq₂1, hq₂le, hq₂per⟩ :=
        hCper l₂ β₂ hβ₂
      have hq1 : 1 ≤ q₁ * q₂ := Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by omega) (by omega))
      have hqper₁ : (q₁ * q₂) • β₁ = 0 := by
        rw [mul_nsmul, hq₁per, smul_zero]
      have hqper₂ : (q₁ * q₂) • β₂ = 0 := by
        rw [mul_comm q₁ q₂, mul_nsmul, hq₂per, smul_zero]
      have harith₁ : (arithQ ρ (max l₁ l₂)) • β₁ = 0 :=
        arithQ_nsmul_eq_zero ((diffFreqs_subset_iwArithFreqs hρ hρ1 (le_max_left l₁ l₂)) hβ₁)
      have harith₂ : (arithQ ρ (max l₁ l₂)) • β₂ = 0 :=
        arithQ_nsmul_eq_zero ((diffFreqs_subset_iwArithFreqs hρ hρ1 (le_max_right l₁ l₂)) hβ₂)
      have hcardarith : 1 ≤ arithQ ρ (max l₁ l₂) := arithQ_pos ρ (max l₁ l₂)
      have hl₁L : l₁ ≤ smallL l₁ l₂ k₁ k₂ := by
        rw [smallL]; exact le_trans (le_max_left _ _) (le_max_left _ _)
      have hl₂L : l₂ ≤ smallL l₁ l₂ k₁ k₂ := by
        rw [smallL]; exact le_trans (le_max_right _ _) (le_max_left _ _)
      have hρl₁ : (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (smallL l₁ l₂ k₁ k₂ : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by have h : (l₁ : ℝ) ≤ (smallL l₁ l₂ k₁ k₂ : ℝ) := by exact_mod_cast hl₁L
              nlinarith [hρ.le, h])
      have hρl₂ : (2 : ℝ) ^ (ρ * (l₂ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (smallL l₁ l₂ k₁ k₂ : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by have h : (l₂ : ℝ) ≤ (smallL l₁ l₂ k₁ k₂ : ℝ) := by exact_mod_cast hl₂L
              nlinarith [hρ.le, h])
      have hprod : ((q₁ * q₂ : ℕ) : ℝ) ≤
          (2 : ℝ) ^ (Cper * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))
            * (2 : ℝ) ^ (Cper * (2 : ℝ) ^ (ρ * (l₂ : ℝ))) := by
        rw [Nat.cast_mul]
        exact mul_le_mul hq₁le hq₂le (by positivity) (by positivity)
      have hstep : (2 : ℝ) ^ (Cper * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))
            * (2 : ℝ) ^ (Cper * (2 : ℝ) ^ (ρ * (l₂ : ℝ)))
          ≤ (2 : ℝ) ^ ((2 * Cper) * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have h1' : Cper * (2 : ℝ) ^ (ρ * (l₁ : ℝ))
            ≤ Cper * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂) := by
          rw [lmaxR_eq_smallL l₁ l₂ k₁ k₂]
          exact mul_le_mul_of_nonneg_left hρl₁ hCperpos.le
        have h2' : Cper * (2 : ℝ) ^ (ρ * (l₂ : ℝ))
            ≤ Cper * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂) := by
          rw [lmaxR_eq_smallL l₁ l₂ k₁ k₂]
          exact mul_le_mul_of_nonneg_left hρl₂ hCperpos.le
        linarith
      have hqQ : ((q₁ * q₂ : ℕ) : ℝ) ≤ (Q : ℝ) := le_trans (le_trans hprod hstep) hQlow
      have hprof : ∀ x₁ x₂ : ℝ,
          spikeProfile P N k₁ k₂ (arithQ ρ (max l₁ l₂)) β₁ β₂ x₁ x₂
            = spikeProfile P N k₁ k₂ (q₁ * q₂) β₁ β₂ x₁ x₂ := by
        intro x₁ x₂
        simp only [spikeProfile]
        rw [m0_period_indep P N (q := arithQ ρ (max l₁ l₂)) (q' := q₁ * q₂)
          hcardarith hq1 harith₁ harith₂ hqper₁ hqper₂ x₁ x₂]
      obtain ⟨hcd, hsupp, h00, h20, h02, h22⟩ := hspb N k₁ k₂ (q₁ * q₂) β₁ β₂ hN1 hq1 hqper₁ hqper₂
      have hqbound : Csp * ((q₁ * q₂ : ℕ) : ℝ) * (2 : ℝ) ^ (Asp * ((k₁ : ℝ) + (k₂ : ℝ)))
            / (N : ℝ) ≤ B := by
        rw [hBdef]
        have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ (Asp * ((k₁ : ℝ) + (k₂ : ℝ))) := by positivity
        refine div_le_div_of_nonneg_right ?_ hNpos.le
        calc Csp * ((q₁ * q₂ : ℕ) : ℝ) * (2 : ℝ) ^ (Asp * ((k₁ : ℝ) + (k₂ : ℝ)))
            = Csp * (2 : ℝ) ^ (Asp * ((k₁ : ℝ) + (k₂ : ℝ))) * ((q₁ * q₂ : ℕ) : ℝ) := by ring
          _ ≤ Csp * (2 : ℝ) ^ (Asp * ((k₁ : ℝ) + (k₂ : ℝ))) * (Q : ℝ) :=
              mul_le_mul_of_nonneg_left hqQ (mul_nonneg hCsppos.le hpow)
          _ = Csp * (Q : ℝ) * (2 : ℝ) ^ (Asp * ((k₁ : ℝ) + (k₂ : ℝ))) := by ring
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hfun : (fun p : ℝ × ℝ =>
            spikeProfile P N k₁ k₂ (arithQ ρ (max l₁ l₂)) β₁ β₂ p.1 p.2)
            = fun p : ℝ × ℝ => spikeProfile P N k₁ k₂ (q₁ * q₂) β₁ β₂ p.1 p.2 := by
          funext p; exact hprof p.1 p.2
        rw [hfun]; exact hcd
      · intro x₁ x₂ hx
        refine hsupp x₁ x₂ ?_
        rw [← hprof x₁ x₂]; exact hx
      · intro x₁ x₂
        rw [hprof x₁ x₂]
        exact le_trans (h00 x₁ x₂) hqbound
      · intro x₁ x₂
        have hfun : (fun y : ℝ => spikeProfile P N k₁ k₂ (arithQ ρ (max l₁ l₂)) β₁ β₂ y x₂)
            = fun y : ℝ => spikeProfile P N k₁ k₂ (q₁ * q₂) β₁ β₂ y x₂ := by
          funext y; exact hprof y x₂
        rw [hfun]
        refine le_trans (h20 x₁ x₂) ?_
        rw [div_le_div_iff_of_pos_right (by positivity)]
        exact hqbound
      · intro x₁ x₂
        have hfun : (fun y : ℝ => spikeProfile P N k₁ k₂ (arithQ ρ (max l₁ l₂)) β₁ β₂ x₁ y)
            = fun y : ℝ => spikeProfile P N k₁ k₂ (q₁ * q₂) β₁ β₂ x₁ y := by
          funext y; exact hprof x₁ y
        rw [hfun]
        refine le_trans (h02 x₁ x₂) ?_
        rw [div_le_div_iff_of_pos_right (by positivity)]
        exact hqbound
      · intro x₁ x₂
        have hfun : (fun y : ℝ => iteratedDeriv 2 (fun z : ℝ =>
              spikeProfile P N k₁ k₂ (arithQ ρ (max l₁ l₂)) β₁ β₂ z y) x₁)
            = fun y : ℝ => iteratedDeriv 2 (fun z : ℝ =>
              spikeProfile P N k₁ k₂ (q₁ * q₂) β₁ β₂ z y) x₁ := by
          funext y
          congr 1
          funext z
          exact hprof z y
        rw [hfun]
        refine le_trans (h22 x₁ x₂) ?_
        rw [div_le_div_iff_of_pos_right (by positivity)]
        exact hqbound
    have hmass := Work.KMTAreas.A7.Cpz.spikeFinsetMassBound ρ P hdeg l₁ l₂ k₁ k₂ N hN1 hw₁pos hw₂pos
      hw₁4 hw₂4 hBnn hsupp₁ hsupp₂ hspike
    have hcollapse := Work.KMTAreas.A7.Cpz.smallKconc_sub_smallKmod_eq_sum_spike ρ P hdeg l₁ l₂ k₁ k₂ N hN1
      hw₁pos hw₂pos hw₁half hw₂half hsupp₁ hsupp₂ hw₁u hw₂u hhu hNA₁ hNA₂
    have hcard₁ : ((diffFreqs ρ l₁).card : ℝ)
        ≤ Ccard * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₁ : ℝ))) := by
      refine le_trans ?_ (hCcard l₁)
      exact_mod_cast Finset.card_le_card (diffFreqs_subset_iwArithFreqs hρ hρ1 (le_refl l₁))
    have hcard₂ : ((diffFreqs ρ l₂).card : ℝ)
        ≤ Ccard * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l₂ : ℝ))) := by
      refine le_trans ?_ (hCcard l₂)
      exact_mod_cast Finset.card_le_card (diffFreqs_subset_iwArithFreqs hρ hρ1 (le_refl l₂))
    have hwt := hweight l₁ l₂ k₁ k₂ N Q hN1 hQpos hcard₁ hcard₂ hQle
    have hfinal : 200 * (((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ)) * B
        ≤ smallScaleWeight C ρ l₁ l₂ k₁ k₂ * ((N : ℝ))⁻¹ := by
      simp only [hBdef, smallScaleWeight, div_eq_mul_inv] at hwt ⊢
      exact hwt
    calc smKernMass (fun x y : ℤ =>
            smallKconc ρ P l₁ l₂ k₁ k₂ (Nat.floor (a n)) x y
              - smallKmod ρ P l₁ l₂ k₁ k₂ (Nat.floor (a n)) x y)
        = smKernMass (fun a b : ℤ => ∑ p ∈ (diffFreqs ρ l₁) ×ˢ (diffFreqs ρ l₂),
            coeff (spikeSymb ρ P l₁ l₂ k₁ k₂ N p.1 p.2) a b) := by
          rw [hNdef] at hcollapse ⊢
          rw [hcollapse]
      _ ≤ ENNReal.ofReal (200 * (((diffFreqs ρ l₁).card : ℝ)
            * ((diffFreqs ρ l₂).card : ℝ)) * B) := hmass
      _ ≤ (K Λ) * ENNReal.ofReal (smallScaleWeight C ρ l₁ l₂ k₁ k₂)
            * ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹) := by
          have hone : (1 : ℝ) ≤ Dfin := hDfin1
          have hstep1 : ENNReal.ofReal (200 * (((diffFreqs ρ l₁).card : ℝ)
                * ((diffFreqs ρ l₂).card : ℝ)) * B)
              ≤ ENNReal.ofReal (smallScaleWeight C ρ l₁ l₂ k₁ k₂ * ((N : ℝ))⁻¹) :=
            ENNReal.ofReal_le_ofReal hfinal
          have hstep2 : ENNReal.ofReal (smallScaleWeight C ρ l₁ l₂ k₁ k₂ * ((N : ℝ))⁻¹)
              = ENNReal.ofReal (smallScaleWeight C ρ l₁ l₂ k₁ k₂)
                * ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹) :=
            ENNReal.ofReal_mul (smallScaleWeight_nonneg C ρ l₁ l₂ k₁ k₂)
          have hstep3 : ENNReal.ofReal (smallScaleWeight C ρ l₁ l₂ k₁ k₂)
                * ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹)
              ≤ ENNReal.ofReal Dfin
                * ENNReal.ofReal (smallScaleWeight C ρ l₁ l₂ k₁ k₂)
                * ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹) := by
            exact mul_le_mul_of_nonneg_right
              (le_mul_of_one_le_left (by positivity)
                (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hone))
              (by positivity)
          exact le_trans hstep1 (le_trans (le_of_eq hstep2) hstep3)
  · have hbad : ¬ (max k₁ k₂ + 2 * u + 1 ≤ R) ∨
        ¬ NonAliasing (-(2 * (u : ℤ))) (diffFreqs ρ l₁) ∨
        ¬ NonAliasing (-(2 * (u : ℤ))) (diffFreqs ρ l₂) := by
      by_contra hcon
      push_neg at hcon
      refine hgood ⟨?_, ?_, hcon.2.1, hcon.2.2⟩
      · have h1 : k₁ + 2 * u + 1 ≤ max k₁ k₂ + 2 * u + 1 := by
          have h := Nat.add_le_add_right (Nat.le_max_left k₁ k₂) (2 * u + 1)
          omega
        exact le_trans h1 hcon.1
      · have h1 : k₂ + 2 * u + 1 ≤ max k₁ k₂ + 2 * u + 1 := by
          have h := Nat.add_le_add_right (Nat.le_max_right k₁ k₂) (2 * u + 1)
          omega
        exact le_trans h1 hcon.1
    have hDb : N ≤ D ∧ smallL l₁ l₂ k₁ k₂ ≤ D := by
      rcases hbad with hmax | hNA | hNA
      · have hcond' := smallCond_mono_C₀ hC₀'max hcond
        obtain ⟨h1, h2⟩ := hD₀ a l₁ l₂ k₁ k₂ n hcond' hmax
        exact ⟨le_trans h1 hD₀D, le_trans h2 hD₀D⟩
      · have h1 : smallL l₁ l₂ k₁ k₂ ≤ D₁ := hD₁ l₁ l₂ k₁ k₂ (Or.inl hNA)
        exact ⟨le_trans (le_trans hcond.2.1 (splitCut_mono ρ hρ.le h1)) hDcut,
          le_trans h1 hD₁D⟩
      · have h1 : smallL l₁ l₂ k₁ k₂ ≤ D₁ := hD₁ l₁ l₂ k₁ k₂ (Or.inr hNA)
        exact ⟨le_trans (le_trans hcond.2.1 (splitCut_mono ρ hρ.le h1)) hDcut,
          le_trans h1 hD₁D⟩
    refine le_trans (hBc l₁ l₂ k₁ k₂ N hDb.2 hDb.1) ?_
    have hw1 : 1 ≤ smallScaleWeight C ρ l₁ l₂ k₁ k₂ := by
      rw [smallScaleWeight]
      refine Real.one_le_rpow (by norm_num) ?_
      exact mul_nonneg hCnn (le_max_of_le_left (by positivity))
    have hDN : (N : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDb.1
    have hDinv : 1 ≤ (D : ℝ) * ((N : ℝ))⁻¹ := by
      have h : (N : ℝ) * ((N : ℝ))⁻¹ ≤ (D : ℝ) * ((N : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right hDN (by positivity)
      rwa [mul_inv_cancel₀ (ne_of_gt hNpos)] at h
    have hreal : Bc ≤ Dfin * smallScaleWeight C ρ l₁ l₂ k₁ k₂ * ((N : ℝ))⁻¹ := by
      have h1 : Bc * (D : ℝ) ≤ Dfin := by
        rw [hDfindef]
        exact le_trans (by linarith) (le_max_left _ _)
      calc Bc = Bc * 1 * 1 := by ring
        _ ≤ Bc * ((D : ℝ) * ((N : ℝ))⁻¹) * 1 := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hDinv hBcnn) (by norm_num)
        _ = Bc * (D : ℝ) * ((N : ℝ))⁻¹ := by ring
        _ ≤ Dfin * ((N : ℝ))⁻¹ := by
              exact mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ Dfin * smallScaleWeight C ρ l₁ l₂ k₁ k₂ * ((N : ℝ))⁻¹ := by
              exact mul_le_mul_of_nonneg_right
                (le_mul_of_one_le_right hDfinnn hw1) (by positivity)
    calc ENNReal.ofReal Bc
        ≤ ENNReal.ofReal (Dfin * smallScaleWeight C ρ l₁ l₂ k₁ k₂ * ((N : ℝ))⁻¹) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal Dfin * ENNReal.ofReal (smallScaleWeight C ρ l₁ l₂ k₁ k₂)
            * ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹) := by
          have h1 : ENNReal.ofReal ((Dfin * smallScaleWeight C ρ l₁ l₂ k₁ k₂) * ((N : ℕ) : ℝ)⁻¹)
              = ENNReal.ofReal (Dfin * smallScaleWeight C ρ l₁ l₂ k₁ k₂)
                * ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹) :=
            ENNReal.ofReal_mul (mul_nonneg hDfinnn (smallScaleWeight_nonneg C ρ l₁ l₂ k₁ k₂))
          have h2 : ENNReal.ofReal (Dfin * smallScaleWeight C ρ l₁ l₂ k₁ k₂)
              = ENNReal.ofReal Dfin * ENNReal.ofReal (smallScaleWeight C ρ l₁ l₂ k₁ k₂) :=
            ENNReal.ofReal_mul hDfinnn
          rw [h1, h2]
      _ = ENNReal.ofReal Dfin * ENNReal.ofReal (smallScaleWeight C ρ l₁ l₂ k₁ k₂)
            * ENNReal.ofReal (((N : ℕ) : ℝ)⁻¹) := by
          rfl

end

end Work.KMTAreas.A7z
