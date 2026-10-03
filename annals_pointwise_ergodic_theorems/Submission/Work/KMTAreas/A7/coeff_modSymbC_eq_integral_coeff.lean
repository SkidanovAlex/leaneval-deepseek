import Mathlib
import Submission.Work.KMTAreas.A7.symbolDefs
import Submission.Work.KMTAreas.A7.measurable_iwKernel_varphitildeNt
import Submission.Work.KMTAreas.A7.varphiNt_bounds
import Submission.Work.KMTAreas.A7.varphitildeNt_support_all

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

noncomputable section

local notation "Circ" => AddCircle (1 : ℝ)

/-! ## §1  Elementary bounds

The target `coeff_modSymbC_eq_integral_coeff` is a Fubini statement: the coefficient
`coeff (modSymbC …) a b` is the double Haar integral of the `t`-integral defining `modSymbC`, and
the claim is that the `t`-integral can be moved outside.  Fubini needs integrability, which we
obtain from pointwise bounds; this section provides them. -/

/-- The characters of the circle have modulus one. -/
private lemma norm_fourier_one (n : ℤ) (θ : Circ) : ‖(fourier (T := 1) n) θ‖ = 1 := by
  rw [fourier_apply]; exact _root_.Circle.norm_coe _

/-- The modulation `e(x) = exp (2πi x)` has modulus one. -/
private lemma norm_ee_one (x : ℝ) : ‖ee x‖ = 1 := by
  rw [ee, show (2 : ℂ) * ↑Real.pi * Complex.I * ↑x = ↑(2 * Real.pi * x) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-! ### §1.1  Pointwise bounds for the periodisation

`periodize φ ξ = ∑'_k φ (x(ξ) + k)` is, at every point `ξ`, a finite sum as soon as `φ` is
supported in `[-R, R]`. -/

private lemma periodize_term_eq_zero_nat {φ : ℝ → ℂ} {R : ℝ} (n : ℕ) (hRn : R ≤ (n : ℝ))
    (hφ0 : ∀ x, R < |x| → φ x = 0) (ξ : Circ) {k : ℤ}
    (hk : k ∉ Finset.Icc (-(n : ℤ) - 2) ((n : ℤ) + 1)) :
    φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k) = 0 := by
  by_contra hne
  have hx := (AddCircle.equivIco (1 : ℝ) 0 ξ).prop
  rw [Set.mem_Ico] at hx
  have hle : |(AddCircle.equivIco (1 : ℝ) 0 ξ).val + k| ≤ R := by
    by_contra h
    exact hne (hφ0 _ (lt_of_not_ge h))
  rw [abs_le] at hle
  have h1 : k ≤ (n : ℤ) + 1 := by
    have h2 : (k : ℝ) ≤ (n : ℝ) := by
      have : (k : ℝ) ≤ (AddCircle.equivIco (1 : ℝ) 0 ξ).val + k := by linarith [hx.1]
      linarith [hle.2, this, hRn]
    have h3 : k ≤ (n : ℤ) := by exact_mod_cast h2
    omega
  have h2 : -(n : ℤ) - 2 ≤ k := by
    have h3 : (-k : ℝ) ≤ (n : ℝ) + 1 := by linarith [hle.1, hx.2, hRn]
    have h4 : (-k : ℤ) ≤ (n : ℤ) + 1 := by exact_mod_cast h3
    omega
  exact hk (by rw [Finset.mem_Icc]; exact ⟨h2, h1⟩)

/-- **The periodisation of a function supported in `[-R, R]` and bounded by `C` is bounded by
`(2n + 4) C` for any integer `n ≥ R`.** -/
private lemma norm_periodize_le_of_support {φ : ℝ → ℂ} {R C : ℝ} (n : ℕ) (hRn : R ≤ (n : ℝ))
    (hφ0 : ∀ x, R < |x| → φ x = 0) (hC : ∀ x, ‖φ x‖ ≤ C) (ξ : Circ) :
    ‖periodize φ ξ‖ ≤ (2 * (n : ℝ) + 4) * C := by
  set s : Finset ℤ := Finset.Icc (-(n : ℤ) - 2) ((n : ℤ) + 1) with hs
  have hkey : periodize φ ξ = ∑ k ∈ s, φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k) := by
    change (∑' k : ℤ, φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k)) = _
    exact tsum_eq_sum fun k hk => periodize_term_eq_zero_nat n hRn hφ0 ξ (by simpa [hs] using hk)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hcard : (s.card : ℝ) ≤ 2 * (n : ℝ) + 4 := by
    have h : (s.card : ℤ) = 2 * (n : ℤ) + 4 := by
      rw [hs, Int.card_Icc_of_le (-(n : ℤ) - 2) ((n : ℤ) + 1) (by omega)]
      ring
    have h2 : (s.card : ℝ) = ((2 * (n : ℤ) + 4 : ℤ) : ℝ) := by exact_mod_cast h
    rw [h2]
    exact le_of_eq (by push_cast; ring)
  rw [hkey]
  calc ‖∑ k ∈ s, φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k)‖
      ≤ ∑ k ∈ s, ‖φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ s, C := Finset.sum_le_sum fun k _ => hC _
    _ = (s.card : ℝ) * C := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (n : ℝ) + 4) * C := mul_le_mul_of_nonneg_right hcard hC0

/-! ### §1.2  Bounds for the factors of `arithSymb` -/

/-- `η_{≤k}` vanishes away from `[-2^k, 2^k]`; in particular for `k ≤ 0` it vanishes off `[-1,1]`. -/
private lemma etaCut_kmtEta_zero_of_neg (k : ℤ) (hk : k ≤ 0) {θ : ℝ} (hθ : 1 < |θ|) :
    etaCut Work.KMTContract.kmtEta k θ = 0 := by
  unfold etaCut
  refine Work.KMTContract.kmtEta_zero ?_
  have hpk1 : (2 : ℝ) ^ k ≤ 1 := by
    have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
    simpa using h
  have hpkpos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  rw [abs_div, abs_of_pos hpkpos]
  have h2 : |θ| ≤ |θ| / (2 : ℝ) ^ k := by
    rw [le_div_iff₀ hpkpos]
    calc |θ| * (2 : ℝ) ^ k ≤ |θ| * 1 := mul_le_mul_of_nonneg_left hpk1 (abs_nonneg θ)
      _ = |θ| := mul_one _
  exact le_trans (le_of_lt hθ) h2

/-- The periodisation of the narrow cutoff `mStarF u = η_{≤-2u}` is bounded. -/
private lemma norm_periodize_mStarF_le (u : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : Circ, ‖periodize (mStarF u) θ‖ ≤ C := by
  have h0 : ∀ x : ℝ, (1 : ℝ) < |x| → mStarF u x = 0 :=
    fun x hx => etaCut_kmtEta_zero_of_neg (-(2 * (u : ℤ))) (by omega) hx
  have hb : ∀ x : ℝ, ‖mStarF u x‖ ≤ 1 := fun x => Work.KMTContract.norm_kmtEta_le _
  refine ⟨6, by norm_num, fun θ => ?_⟩
  have h := norm_periodize_le_of_support (φ := mStarF u) (R := 1) (C := 1) 1
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)) h0 hb θ
  norm_num at h
  linarith [h]

/-- The periodisation of the narrow cutoff `mStargF d u = η_{≤-2du}` is bounded. -/
private lemma norm_periodize_mStargF_le (d u : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : Circ, ‖periodize (mStargF d u) θ‖ ≤ C := by
  have h0 : ∀ x : ℝ, (1 : ℝ) < |x| → mStargF d u x = 0 := by
    intro x hx
    refine etaCut_kmtEta_zero_of_neg (-((d : ℤ) * 2 * (u : ℤ))) ?_ hx
    have h : (0 : ℤ) ≤ (d : ℤ) * 2 * (u : ℤ) :=
      mul_nonneg (mul_nonneg (Int.natCast_nonneg d) (by norm_num)) (Int.natCast_nonneg u)
    omega
  have hb : ∀ x : ℝ, ‖mStargF d u x‖ ≤ 1 := fun x => Work.KMTContract.norm_kmtEta_le _
  refine ⟨6, by norm_num, fun θ => ?_⟩
  have h := norm_periodize_le_of_support (φ := mStargF d u) (R := 1) (C := 1) 1
    (by norm_num : (1 : ℝ) ≤ ((1 : ℕ) : ℝ)) h0 hb θ
  norm_num at h
  linarith [h]

/-- **The arithmetic symbol `arithSymb` is bounded.**  It is a finite sum of products of the
bounded periodised cutoffs `mStarF u`, `mStargF d u` with the constants `m_Ẑ`. -/
private lemma norm_arithSymb_le (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ u : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ₁ θ₂ : Circ, ‖arithSymb ρ P l₁ l₂ u θ₁ θ₂‖ ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := norm_periodize_mStarF_le u
  obtain ⟨C₂, hC₂0, hC₂⟩ := norm_periodize_mStargF_le P.natDegree u
  refine ⟨∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
      ‖mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂‖ * C₁ * C₂, ?_, ?_⟩
  · exact Finset.sum_nonneg fun α₁ _ => Finset.sum_nonneg fun α₂ _ =>
      mul_nonneg (mul_nonneg (norm_nonneg _) hC₁0) hC₂0
  · intro θ₁ θ₂
    unfold arithSymb
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun α₁ _ => (norm_sum_le _ _).trans ?_)
    refine Finset.sum_le_sum fun α₂ _ => ?_
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hC₁ (θ₁ - α₁)) (norm_nonneg _))
      (hC₂ (θ₂ - α₂)) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hC₁0)

/-- The modulated bump `varphiNt N k t` is bounded by `2`, uniformly in `t`. -/
private lemma norm_varphiN_le_two_aux (N k : ℕ) (ξ : ℝ) : ‖varphiN N k ξ‖ ≤ 2 := by
  by_cases hk : k = 0
  · simp only [varphiN, if_pos hk]
    exact le_trans (Work.KMTContract.norm_kmtEta_le _) (by norm_num)
  · simp only [varphiN, if_neg hk]
    calc ‖Work.KMTContract.kmtEta
            (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ)
          - Work.KMTContract.kmtEta
            (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ)‖
        ≤ ‖Work.KMTContract.kmtEta
            (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ)‖
          + ‖Work.KMTContract.kmtEta
            (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ)‖ :=
          norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (Work.KMTContract.norm_kmtEta_le _)
          (Work.KMTContract.norm_kmtEta_le _)
      _ = 2 := by norm_num

private lemma norm_varphiNt_le_two (N k : ℕ) (t : ℝ) (ξ : ℝ) : ‖varphiNt N k t ξ‖ ≤ 2 := by
  have h : varphiNt N k t ξ = varphiN N k ξ * ee ((N : ℝ) * t * ξ) := rfl
  rw [h, norm_mul, norm_ee_one, mul_one]
  exact norm_varphiN_le_two_aux N k ξ

private lemma norm_varphitildeN_le_two_aux (d N k : ℕ) (x : ℝ) :
    ‖varphitildeN d N k x‖ ≤ 2 := by
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

private lemma norm_varphitildeNt_le_two (P : Polynomial ℤ) (N k : ℕ) (t : ℝ) (ξ : ℝ) :
    ‖varphitildeNt P P.natDegree N k t ξ‖ ≤ 2 := by
  have h : varphitildeNt P P.natDegree N k t ξ
      = varphitildeN P.natDegree N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ) := rfl
  rw [h, norm_mul, norm_ee_one, mul_one]
  exact norm_varphitildeN_le_two_aux P.natDegree N k ξ

/-! ### §1.3  The periodisation of the modulated bumps is bounded uniformly in `t` -/

private lemma varphiNt_support_aux (N k : ℕ) (t : ℝ) (ξ : ℝ) (h : varphiNt N k t ξ ≠ 0) :
    |ξ| ≤ (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by
  have h' : varphiN N k ξ ≠ 0 := by
    intro hc
    exact h (by rw [varphiNt, hc, zero_mul])
  exact varphiN_support N k ξ h'

private lemma norm_periodize_varphiNt_le (N k : ℕ) (t : ℝ) (ξ : Circ) :
    ‖periodize (varphiNt N k t) ξ‖
      ≤ (2 * (Nat.ceil ((2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) : ℝ) + 4) * 2 := by
  set R : ℝ := (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) with hR
  have h0 : ∀ x : ℝ, R < |x| → varphiNt N k t x = 0 := by
    intro x hx
    by_contra hne
    rw [hR] at hx
    exact absurd (varphiNt_support_aux N k t x hne) (not_le.mpr hx)
  exact norm_periodize_le_of_support (Nat.ceil R) (Nat.le_ceil R) h0
    (fun x => norm_varphiNt_le_two N k t x) ξ

private lemma norm_periodize_varphitildeNt_le (P : Polynomial ℤ) (N k : ℕ) (t : ℝ) (ξ : Circ) :
    ‖periodize (varphitildeNt P P.natDegree N k t) ξ‖
      ≤ (2 * (Nat.ceil ((2 : ℝ) ^ ((P.natDegree : ℝ) *
          ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) : ℝ) + 4) * 2 := by
  set R : ℝ := (2 : ℝ) ^ ((P.natDegree : ℝ) *
    ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) with hR
  have h0 : ∀ x : ℝ, R < |x| → varphitildeNt P P.natDegree N k t x = 0 := by
    intro x hx
    by_contra hne
    have hle := varphitildeNt_support_all P P.natDegree N k t x hne
    rw [← hR] at hle
    exact absurd hx (not_lt.mpr hle)
  exact norm_periodize_le_of_support (Nat.ceil R) (Nat.le_ceil R) h0
    (fun x => norm_varphitildeNt_le_two P N k t x) ξ

/-- **The IW symbol of the modulated bump `φ_{N,t}` is bounded uniformly in `t`.** -/
private lemma norm_iwSymbolSet_varphiNt_le_aux (ρ : ℝ) (l N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (θ : Circ),
      ‖iwSymbolSet (diffFreqs ρ l) (periodize (varphiNt N k t)) θ‖ ≤ C := by
  refine ⟨((diffFreqs ρ l).card : ℝ) *
      ((2 * (Nat.ceil ((2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) : ℝ) + 4) * 2),
    by positivity, ?_⟩
  intro t θ
  exact norm_iwSymbolSet_le (diffFreqs ρ l) (fun ξ => norm_periodize_varphiNt_le N k t ξ) θ

/-- **The IW symbol of the modulated bump `φ̃_{N,t}` is bounded uniformly in `t`.** -/
private lemma norm_iwSymbolSet_varphitildeNt_le_aux (ρ : ℝ) (P : Polynomial ℤ) (l N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (θ : Circ),
      ‖iwSymbolSet (diffFreqs ρ l) (periodize (varphitildeNt P P.natDegree N k t)) θ‖ ≤ C := by
  refine ⟨((diffFreqs ρ l).card : ℝ) *
      ((2 * (Nat.ceil ((2 : ℝ) ^ ((P.natDegree : ℝ) *
        ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) : ℝ) + 4) * 2), by positivity, ?_⟩
  intro t θ
  exact norm_iwSymbolSet_le (diffFreqs ρ l)
    (fun ξ => norm_periodize_varphitildeNt_le P N k t ξ) θ

/-! ## §2  Measurability

Measurability of the integrand of Fubini's theorem. -/

private lemma measurable_periodize_aux {φ : ℝ → ℂ} (hφ : Measurable φ) :
    Measurable (periodize φ) := by
  have hx : Measurable fun ξ : Circ => (AddCircle.equivIco (1 : ℝ) 0 ξ).val :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  have h1 : periodize φ = fun ξ : Circ =>
      ∑' m : ℤ, φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + (m : ℝ)) := by
    funext ξ; rw [periodize]
  rw [h1]
  exact Measurable.tsum (L := SummationFilter.unconditional ℤ)
    (fun m => hφ.comp (hx.add_const (m : ℝ)))

private lemma measurable_kmtEta : Measurable Work.KMTContract.kmtEta := by
  have h : Work.KMTContract.kmtEta
      = fun x : ℝ => ((Work.KMTContract.kmtBump : ℝ → ℝ) x : ℂ) := rfl
  rw [h]
  exact Complex.continuous_ofReal.measurable.comp
    (ContDiffBump.continuous _).measurable

private lemma measurable_etaCut_aux (k : ℤ) : Measurable (etaCut Work.KMTContract.kmtEta k) := by
  unfold etaCut
  exact measurable_kmtEta.comp (measurable_id.div_const _)

private lemma measurable_arithSymb_aux (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ u : ℕ) :
    Measurable (fun p : Circ × Circ => arithSymb ρ P l₁ l₂ u p.1 p.2) := by
  have h1 : Measurable (periodize (mStarF u)) :=
    measurable_periodize_aux (measurable_etaCut_aux _)
  have h2 : Measurable (periodize (mStargF P.natDegree u)) :=
    measurable_periodize_aux (measurable_etaCut_aux _)
  unfold arithSymb
  refine Finset.measurable_sum _ fun α₁ _ => Finset.measurable_sum _ fun α₂ _ => ?_
  have hc : Measurable (fun _ : Circ × Circ => mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂) :=
    measurable_const
  exact (hc.mul (h1.comp (measurable_fst.sub measurable_const))).mul
    (h2.comp (measurable_snd.sub measurable_const))

private lemma measurable_varphiNt_uncurry_aux (N k : ℕ) :
    Measurable (fun q : ℝ × ℝ => varphiNt N k q.1 q.2) := by
  have h1 : Measurable fun q : ℝ × ℝ => varphiN N k q.2 :=
    (contDiff_varphiN N k).continuous.measurable.comp measurable_snd
  have hee : Measurable ee := by unfold ee; fun_prop
  have h2 : Measurable fun q : ℝ × ℝ => ee ((N : ℝ) * q.1 * q.2) :=
    hee.comp ((measurable_const.mul measurable_fst).mul measurable_snd)
  unfold varphiNt
  exact h1.mul h2

private lemma measurable_sym_varphiNt (ρ : ℝ) (l N k : ℕ) :
    Measurable (fun p : ℝ × Circ =>
      iwSymbolSet (diffFreqs ρ l) (periodize (varphiNt N k p.1)) p.2) :=
  measurable_iwSymbolSet_uncurry _ (measurable_varphiNt_uncurry_aux N k)

private lemma measurable_sym_varphitildeNt (ρ : ℝ) (P : Polynomial ℤ) (l N k : ℕ) :
    Measurable (fun p : ℝ × Circ =>
      iwSymbolSet (diffFreqs ρ l)
        (periodize (varphitildeNt P P.natDegree N k p.1)) p.2) :=
  measurable_iwSymbolSet_uncurry _ (measurable_varphitildeNt_uncurry P N k)

/-! ## §3  The Fubini step

The identity `coeff (∫_t F_t) = ∫_t coeff F_t`: both sides are the triple integral of the same
integrand, and the two applications of Fubini's theorem move the `t`-integral to the outside. -/

private lemma coeff_swap_core (K : ℝ → Circ → Circ → ℂ)
    (hmeas : Measurable (fun p : ℝ × Circ × Circ => K p.1 p.2.1 p.2.2))
    {C : ℝ} (hC : ∀ p : ℝ × Circ × Circ, ‖K p.1 p.2.1 p.2.2‖ ≤ C) :
    (∫ θ₁, ∫ θ₂, ∫ t, K t θ₁ θ₂ ∂(volume.restrict (Set.Ioc (1/2 : ℝ) 1))
        ∂(AddCircle.haarAddCircle (T := 1)) ∂(AddCircle.haarAddCircle (T := 1)))
      = ∫ t, ∫ θ₁, ∫ θ₂, K t θ₁ θ₂ ∂(AddCircle.haarAddCircle (T := 1))
          ∂(AddCircle.haarAddCircle (T := 1)) ∂(volume.restrict (Set.Ioc (1/2 : ℝ) 1)) := by
  have hμuniv : (AddCircle.haarAddCircle (T := 1)).real Set.univ = 1 := by
    simp [MeasureTheory.Measure.real]
  have hA : ∀ θ₁ : Circ,
      (∫ θ₂, ∫ t, K t θ₁ θ₂ ∂(volume.restrict (Set.Ioc (1/2 : ℝ) 1))
        ∂(AddCircle.haarAddCircle (T := 1)))
      = ∫ t, ∫ θ₂, K t θ₁ θ₂ ∂(AddCircle.haarAddCircle (T := 1))
        ∂(volume.restrict (Set.Ioc (1/2 : ℝ) 1)) := by
    intro θ₁
    refine MeasureTheory.integral_integral_swap ?_
    refine MeasureTheory.Integrable.of_bound ?_ C ?_
    · exact (hmeas.comp (measurable_snd.prodMk
        ((measurable_const : Measurable fun _ : Circ × ℝ => θ₁).prodMk
          measurable_fst))).aestronglyMeasurable
    · filter_upwards with z
      exact hC ⟨z.2, θ₁, z.1⟩
  have hC' : (∫ θ₁, ∫ t, (∫ θ₂, K t θ₁ θ₂ ∂(AddCircle.haarAddCircle (T := 1)))
        ∂(volume.restrict (Set.Ioc (1/2 : ℝ) 1)) ∂(AddCircle.haarAddCircle (T := 1)))
      = ∫ t, ∫ θ₁, (∫ θ₂, K t θ₁ θ₂ ∂(AddCircle.haarAddCircle (T := 1)))
          ∂(AddCircle.haarAddCircle (T := 1)) ∂(volume.restrict (Set.Ioc (1/2 : ℝ) 1)) := by
    refine MeasureTheory.integral_integral_swap ?_
    refine MeasureTheory.Integrable.of_bound ?_ C ?_
    · have hsm : StronglyMeasurable (fun q : (Circ × ℝ) × Circ => K q.1.2 q.1.1 q.2) :=
        (hmeas.comp ((measurable_fst.snd).prodMk
          ((measurable_fst.fst).prodMk measurable_snd))).stronglyMeasurable
      exact (MeasureTheory.StronglyMeasurable.integral_prod_right
        (ν := AddCircle.haarAddCircle (T := 1)) hsm).aestronglyMeasurable
    · filter_upwards with z
      calc ‖∫ θ₂, K z.2 z.1 θ₂ ∂(AddCircle.haarAddCircle (T := 1))‖
          ≤ C * (AddCircle.haarAddCircle (T := 1)).real Set.univ :=
            MeasureTheory.norm_integral_le_of_norm_le_const (by
              filter_upwards with θ₂; exact hC ⟨z.2, z.1, θ₂⟩)
        _ = C := by rw [hμuniv, mul_one]
  calc ∫ θ₁, ∫ θ₂, ∫ t, K t θ₁ θ₂ ∂(volume.restrict (Set.Ioc (1/2 : ℝ) 1))
        ∂(AddCircle.haarAddCircle (T := 1)) ∂(AddCircle.haarAddCircle (T := 1))
      = ∫ θ₁, (∫ t, ∫ θ₂, K t θ₁ θ₂ ∂(AddCircle.haarAddCircle (T := 1))
          ∂(volume.restrict (Set.Ioc (1/2 : ℝ) 1))) ∂(AddCircle.haarAddCircle (T := 1)) := by
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ₁ => hA θ₁)
    _ = ∫ t, ∫ θ₁, (∫ θ₂, K t θ₁ θ₂ ∂(AddCircle.haarAddCircle (T := 1)))
          ∂(AddCircle.haarAddCircle (T := 1)) ∂(volume.restrict (Set.Ioc (1/2 : ℝ) 1)) := hC'

/-- The `t`-integral of a pointwise multiple of a one-variable function, in measure form. -/
private lemma interval_integral_mul_const_aux (f : ℝ → ℂ) (c d : ℂ) :
    (∫ t in (1/2 : ℝ)..1, f t) * c * d
      = ∫ t, f t * c * d ∂(volume.restrict (Set.Ioc (1/2 : ℝ) 1)) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (1/2 : ℝ) ≤ 1)]
  rw [← MeasureTheory.integral_mul_const c f]
  rw [← MeasureTheory.integral_mul_const d (fun t => f t * c)]

private lemma coeff_interval_integral_eq (K : ℝ → Circ → Circ → ℂ) (a b : ℤ) :
    coeff (fun θ₁ θ₂ => ∫ t in (1/2 : ℝ)..1, K t θ₁ θ₂) a b
      = ∫ θ₁, ∫ θ₂, ∫ t, K t θ₁ θ₂ * (fourier (T := 1) (-a)) θ₁
          * (fourier (T := 1) (-b)) θ₂
          ∂(volume.restrict (Set.Ioc (1/2 : ℝ) 1))
          ∂(AddCircle.haarAddCircle (T := 1)) ∂(AddCircle.haarAddCircle (T := 1)) := by
  rw [coeff]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ₁ => ?_)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ₂ => ?_)
  exact interval_integral_mul_const_aux (fun t => K t θ₁ θ₂)
    ((fourier (T := 1) (-a)) θ₁) ((fourier (T := 1) (-b)) θ₂)

private lemma integral_coeff_eq (K : ℝ → Circ → Circ → ℂ) (a b : ℤ) :
    (∫ t in (1/2 : ℝ)..1, coeff (fun θ₁ θ₂ => K t θ₁ θ₂) a b)
      = ∫ t, ∫ θ₁, ∫ θ₂, K t θ₁ θ₂ * (fourier (T := 1) (-a)) θ₁
          * (fourier (T := 1) (-b)) θ₂
          ∂(AddCircle.haarAddCircle (T := 1)) ∂(AddCircle.haarAddCircle (T := 1))
          ∂(volume.restrict (Set.Ioc (1/2 : ℝ) 1)) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (1/2 : ℝ) ≤ 1)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show coeff (fun θ₁ θ₂ => K t θ₁ θ₂) a b = _
  unfold coeff
  rfl

/-! ## §4  The integrand of the Fubini step -/

/-- Measurability of the full integrand of the Fubini step. -/
private lemma measurable_integrand (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) (a b : ℤ) :
    Measurable (fun p : ℝ × Circ × Circ =>
      arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) p.2.1 p.2.2
        * iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ p.1)) p.2.1
        * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ p.1)) p.2.2
        * (fourier (T := 1) (-a)) p.2.1 * (fourier (T := 1) (-b)) p.2.2) := by
  refine Measurable.mul ?_ ?_
  · refine Measurable.mul ?_ ?_
    · refine Measurable.mul ?_ ?_
      · refine Measurable.mul ?_ ?_
        · exact (measurable_arithSymb_aux ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂))).comp
            (f := fun p : ℝ × Circ × Circ => (p.2.1, p.2.2))
            (measurable_snd.fst.prodMk measurable_snd.snd)
        · exact (measurable_sym_varphiNt ρ l₁ N k₁).comp
            (f := fun p : ℝ × Circ × Circ => (p.1, p.2.1))
            (measurable_fst.prodMk measurable_snd.fst)
      · exact (measurable_sym_varphitildeNt ρ P l₂ N k₂).comp
          (f := fun p : ℝ × Circ × Circ => (p.1, p.2.2))
          (measurable_fst.prodMk measurable_snd.snd)
    · exact ((fourier (T := 1) (-a)).continuous.measurable).comp
        (f := fun p : ℝ × Circ × Circ => p.2.1) measurable_snd.fst
  · exact ((fourier (T := 1) (-b)).continuous.measurable).comp
      (f := fun p : ℝ × Circ × Circ => p.2.2) measurable_snd.snd

/-- A uniform bound for the full integrand of the Fubini step. -/
private lemma norm_integrand_le (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) (a b : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × Circ × Circ,
      ‖arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) p.2.1 p.2.2
        * iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ p.1)) p.2.1
        * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ p.1)) p.2.2
        * (fourier (T := 1) (-a)) p.2.1 * (fourier (T := 1) (-b)) p.2.2‖ ≤ C := by
  obtain ⟨Ca, hCa0, hCa⟩ := norm_arithSymb_le ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂))
  obtain ⟨C₁, hC₁0, hC₁⟩ := norm_iwSymbolSet_varphiNt_le_aux ρ l₁ N k₁
  obtain ⟨C₂, hC₂0, hC₂⟩ := norm_iwSymbolSet_varphitildeNt_le_aux ρ P l₂ N k₂
  refine ⟨Ca * C₁ * C₂, by positivity, fun p => ?_⟩
  have h1 : ‖arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) p.2.1 p.2.2‖ ≤ Ca := hCa _ _
  have h2 : ‖iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ p.1)) p.2.1‖ ≤ C₁ := hC₁ _ _
  have h3 : ‖iwSymbolSet (diffFreqs ρ l₂)
      (periodize (varphitildeNt P P.natDegree N k₂ p.1)) p.2.2‖ ≤ C₂ := hC₂ _ _
  calc ‖arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) p.2.1 p.2.2
        * iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ p.1)) p.2.1
        * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ p.1)) p.2.2
        * (fourier (T := 1) (-a)) p.2.1 * (fourier (T := 1) (-b)) p.2.2‖
      = ‖arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) p.2.1 p.2.2‖
        * ‖iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ p.1)) p.2.1‖
        * ‖iwSymbolSet (diffFreqs ρ l₂)
            (periodize (varphitildeNt P P.natDegree N k₂ p.1)) p.2.2‖ := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_fourier_one, norm_fourier_one]
        ring
    _ ≤ Ca * C₁ * C₂ := by
        refine mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hCa0) h3 (norm_nonneg _)
          (mul_nonneg hCa0 hC₁0)

/-! ## §5  The target -/

theorem coeff_modSymbC_eq_integral_coeff (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) (a b : ℤ) :
    Work.KMTAreas.A7.coeff (Work.KMTAreas.A7.modSymbC ρ P l₁ l₂ k₁ k₂ N) a b
      = ∫ t in (1 / 2 : ℝ)..1, Work.KMTAreas.A7.coeff
          (fun θ₁ θ₂ : AddCircle (1 : ℝ) =>
            Work.KMTAreas.A7.arithSymb ρ P l₁ l₂
                (Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂)) θ₁ θ₂
              * Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l₁)
                  (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.varphiNt N k₁ t)) θ₁
              * Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l₂)
                  (Work.Analysis.IonescuWainger.periodize
                    (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t)) θ₂) a b := by
  have hmod : modSymbC ρ P l₁ l₂ k₁ k₂ N = fun θ₁ θ₂ : Circ =>
      ∫ t in (1 / 2 : ℝ)..1,
        arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) θ₁ θ₂
          * iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ t)) θ₁
          * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ t)) θ₂ := by
    funext θ₁ θ₂; rfl
  rw [hmod]
  rw [coeff_interval_integral_eq (fun t θ₁ θ₂ =>
        arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) θ₁ θ₂
          * iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ t)) θ₁
          * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ t)) θ₂) a b]
  rw [integral_coeff_eq (fun t θ₁ θ₂ =>
        arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) θ₁ θ₂
          * iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ t)) θ₁
          * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ t)) θ₂) a b]
  obtain ⟨C, -, hC⟩ := norm_integrand_le ρ P l₁ l₂ k₁ k₂ N a b
  exact coeff_swap_core (fun t θ₁ θ₂ =>
        arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) θ₁ θ₂
          * iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ t)) θ₁
          * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ t)) θ₂
        * (fourier (T := 1) (-a)) θ₁ * (fourier (T := 1) (-b)) θ₂)
    (measurable_integrand ρ P l₁ l₂ k₁ k₂ N a b)
    hC

end

end Work.KMTAreas.A7
