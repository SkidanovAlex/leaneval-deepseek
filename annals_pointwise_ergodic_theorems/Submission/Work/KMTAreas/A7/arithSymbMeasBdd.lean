/-
# Measurability and uniform boundedness of the §6 symbols `concSymb`, `modSymbC`

The two symbols of the §6 model approximation,

* `concSymb = Ψ₁ · Ψ₂ · avg` (the symbol of the concrete kernel `smallKconc`), and
* `modSymbC = ∫_{t ∈ (1/2,1)} Arith · Ψ₁^t · Ψ₂^t` (the symbol of the model kernel `smallKmod`),

are measurable on `𝕋²` and uniformly bounded.  Both facts are elementary:

* `average symbol`: a finite sum of products of continuous characters, bounded by `1`;
* `IwSymbolSet A Φ = ∑_{α ∈ A} Φ(· - α)`: a finite sum of translates of `Φ`, so measurable and
  bounded by `#A · ‖Φ‖_∞`;
* `periodize φ`: measurable as soon as `φ` is (`Measurable.tsum`), and bounded when `φ` is
  supported in `[-R,R]` and bounded by `C` (only the finitely many integers `k ∈ [-⌊R⌋-2, ⌊R⌋+1]`
  contribute);
* the parametric `t`-integral of a jointly measurable, uniformly bounded family is measurable
  (`StronglyMeasurable.integral_prod_right`) and bounded
  (`intervalIntegral.norm_integral_le_of_norm_le_const`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.coeffLinear
import Submission.Work.KMTAreas.A7.coeff_modSymbC_eq_integral_coeff
import Submission.Work.KMTAreas.A7.SmallModDefs

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

local notation "Circ" => AddCircle (1 : ℝ)

/-! ## 1. The KMT bumps: measurability, sup bounds, support -/

private lemma measurable_kmtEta_aux : Measurable Work.KMTContract.kmtEta := by
  have h : Work.KMTContract.kmtEta =
      fun x : ℝ => ((Work.KMTContract.kmtBump : ℝ → ℝ) x : ℂ) := rfl
  rw [h]
  exact Complex.continuous_ofReal.measurable.comp
    Work.KMTContract.kmtBump.continuous.measurable

private lemma measurable_varphiN_aux (N k : ℕ) : Measurable (varphiN N k) := by
  by_cases hk : k = 0
  · simp only [varphiN, if_pos hk]
    exact measurable_kmtEta_aux.comp (measurable_const_mul _)
  · simp only [varphiN, if_neg hk]
    exact (measurable_kmtEta_aux.comp (measurable_const_mul _)).sub
      (measurable_kmtEta_aux.comp (measurable_const_mul _))

private lemma measurable_varphitildeN_aux (d N k : ℕ) : Measurable (varphitildeN d N k) := by
  by_cases hk : k = 0
  · simp only [varphitildeN, if_pos hk]
    exact measurable_kmtEta_aux.comp (measurable_const_mul _)
  · simp only [varphitildeN, if_neg hk]
    exact (measurable_kmtEta_aux.comp (measurable_const_mul _)).sub
      (measurable_kmtEta_aux.comp (measurable_const_mul _))

private lemma ee_zero_aux : ee (0 : ℝ) = 1 := by simp [ee]

private lemma norm_ee_aux (x : ℝ) : ‖ee x‖ = 1 := by
  rw [ee, show (2 : ℂ) * ↑Real.pi * Complex.I * ↑x = ↑(2 * Real.pi * x) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma norm_fourier_one_aux (n : ℤ) (θ : Circ) : ‖(fourier (T := 1) n) θ‖ = 1 := by
  rw [fourier_apply]; exact _root_.Circle.norm_coe _

private lemma norm_varphiN_le_two_aux (N k : ℕ) (ξ : ℝ) : ‖varphiN N k ξ‖ ≤ 2 := by
  by_cases hk : k = 0
  · simp only [varphiN, if_pos hk]
    exact le_trans (Work.KMTContract.norm_kmtEta_le _) (by norm_num)
  · simp only [varphiN, if_neg hk]
    refine le_trans (norm_sub_le _ _) ?_
    have h1 := Work.KMTContract.norm_kmtEta_le
      (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ)
    have h2 := Work.KMTContract.norm_kmtEta_le
      (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ)
    linarith

private lemma norm_varphitildeN_le_two_aux (d N k : ℕ) (ξ : ℝ) :
    ‖varphitildeN d N k ξ‖ ≤ 2 := by
  by_cases hk : k = 0
  · simp only [varphitildeN, if_pos hk]
    exact le_trans (Work.KMTContract.norm_kmtEta_le _) (by norm_num)
  · simp only [varphitildeN, if_neg hk]
    refine le_trans (norm_sub_le _ _) ?_
    have h1 := Work.KMTContract.norm_kmtEta_le
      (((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))) * ξ)
    have h2 := Work.KMTContract.norm_kmtEta_le
      (((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1))) * ξ)
    linarith

private lemma varphiNt_zero_aux (N k : ℕ) : varphiNt N k 0 = varphiN N k := by
  funext ξ
  show varphiN N k ξ * ee ((N : ℝ) * 0 * ξ) = varphiN N k ξ
  simp [ee]

private lemma varphiN_support_aux (N k : ℕ) {x : ℝ} (hne : varphiN N k x ≠ 0) :
    |x| ≤ (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by
  have h0 : varphiNt N k 0 x ≠ 0 := by
    intro hz
    rw [varphiNt_zero_aux N k] at hz
    exact hne hz
  exact varphiNt_support N k 0 x h0

private lemma norm_varphitildeNt_eq_aux (P : Polynomial ℤ) (d N k : ℕ) (t ξ : ℝ) :
    ‖varphitildeNt P d N k t ξ‖ = ‖varphitildeN d N k ξ‖ := by
  show ‖varphitildeN d N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ)‖ = ‖varphitildeN d N k ξ‖
  rw [norm_mul, norm_ee_aux, mul_one]

private lemma varphitildeN_support_aux (d N k : ℕ) {x : ℝ} (hne : varphitildeN d N k x ≠ 0) :
    |x| ≤ (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := by
  have h0 : varphitildeNt (0 : Polynomial ℤ) d N k 0 x ≠ 0 := by
    intro hz
    apply hne
    have h := norm_varphitildeNt_eq_aux (0 : Polynomial ℤ) d N k 0 x
    rw [hz, norm_zero] at h
    exact norm_eq_zero.mp h.symm
  exact varphitildeNt_support_all (0 : Polynomial ℤ) d N k 0 x h0

/-! ## 2. The periodisation of a compactly supported bounded function -/

private lemma measurable_equivIco_val_aux :
    Measurable (fun ξ : Circ => (AddCircle.equivIco (1 : ℝ) 0 ξ).val) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

private lemma periodize_term_eq_zero_aux {φ : ℝ → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hφ0 : ∀ x, R < |x| → φ x = 0) (ξ : Circ) {k : ℤ}
    (hk : k ∉ Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1)) :
    φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k) = 0 := by
  by_contra hne
  have hx := (AddCircle.equivIco (1 : ℝ) 0 ξ).prop
  rw [Set.mem_Ico] at hx
  have hle : |(AddCircle.equivIco (1 : ℝ) 0 ξ).val + k| ≤ R := by
    by_contra h
    exact hne (hφ0 _ (lt_of_not_ge h))
  rw [abs_le] at hle
  have h1 : k ≤ ⌊R⌋ + 1 := by
    have hkx : (k : ℝ) ≤ R := by linarith [hle.2, hx.1]
    have := Int.le_floor.mpr hkx
    linarith
  have h2 : -(⌊R⌋ + 2) ≤ k := by
    have hk2 : ((-k - 2 : ℤ) : ℝ) ≤ R := by
      push_cast
      linarith [hle.1, hx.2, hR]
    have := Int.le_floor.mpr hk2
    linarith
  exact hk (by rw [Finset.mem_Icc]; exact ⟨h2, h1⟩)

private lemma measurable_periodize_aux {φ : ℝ → ℂ} (hφ : Measurable φ) :
    Measurable (periodize φ) := by
  have h1 : periodize φ = fun ξ : Circ =>
      ∑' m : ℤ, φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + (m : ℝ)) := by
    funext ξ; rw [periodize]
  rw [h1]
  exact Measurable.tsum (L := SummationFilter.unconditional ℤ)
    (fun m => hφ.comp (measurable_equivIco_val_aux.add_const (m : ℝ)))

private lemma norm_periodize_le_aux {φ : ℝ → ℂ} {R C : ℝ} (hR : 0 ≤ R)
    (hφ0 : ∀ x, R < |x| → φ x = 0) (hφC : ∀ x, ‖φ x‖ ≤ C) (ξ : Circ) :
    ‖periodize φ ξ‖ ≤ ((Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1)).card : ℝ) * C := by
  have hkey : periodize φ ξ = ∑ k ∈ Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1),
      φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k) := by
    change (∑' k : ℤ, φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k)) = _
    exact tsum_eq_sum fun k hk => periodize_term_eq_zero_aux hR hφ0 ξ hk
  rw [hkey]
  calc ‖∑ k ∈ Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1),
        φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k)‖
      ≤ ∑ k ∈ Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1),
        ‖φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1), C := Finset.sum_le_sum fun k _ => hφC _
    _ = ((Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1)).card : ℝ) * C := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-! ## 3. Measurability and bounds of the individual symbols -/

private lemma measurable_avgSymb_aux (P : Polynomial ℤ) (N : ℕ) :
    Measurable (fun p : Circ × Circ => avgSymb P N p.1 p.2) := by
  simp only [avgSymb]
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun m _ => ?_
  exact (((fourier (T := 1) ((m : ℕ) : ℤ)).continuous.measurable).comp measurable_fst).mul
    (((fourier (T := 1) (P.eval ((m : ℕ) : ℤ))).continuous.measurable).comp measurable_snd)

private lemma norm_avgSymb_le_one_aux (P : Polynomial ℤ) (N : ℕ) (θ₁ θ₂ : Circ) :
    ‖avgSymb P N θ₁ θ₂‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [avgSymb]
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    have hsum : ‖∑ m ∈ Finset.Ioc (N / 2) N,
        (fourier (T := 1) (m : ℤ)) θ₁ * (fourier (T := 1) (P.eval (m : ℤ))) θ₂‖
        ≤ ((Finset.Ioc (N / 2) N).card : ℝ) := by
      calc ‖∑ m ∈ Finset.Ioc (N / 2) N,
            (fourier (T := 1) (m : ℤ)) θ₁ * (fourier (T := 1) (P.eval (m : ℤ))) θ₂‖
          ≤ ∑ m ∈ Finset.Ioc (N / 2) N,
            ‖(fourier (T := 1) (m : ℤ)) θ₁ * (fourier (T := 1) (P.eval (m : ℤ))) θ₂‖ :=
              norm_sum_le _ _
        _ ≤ ∑ _m ∈ Finset.Ioc (N / 2) N, (1 : ℝ) := Finset.sum_le_sum fun m _ => by
              rw [norm_mul, norm_fourier_one_aux, norm_fourier_one_aux, one_mul]
        _ = ((Finset.Ioc (N / 2) N).card : ℝ) := by simp
    have hcard : ((Finset.Ioc (N / 2) N).card : ℝ) ≤ (N : ℝ) := by
      have h : (Finset.Ioc (N / 2) N).card ≤ N := by
        have h2 : (Finset.Ioc (N / 2) N).card = N - N / 2 := by simp
        omega
      exact_mod_cast h
    simp only [avgSymb]
    calc ‖((N : ℂ))⁻¹ * ∑ m ∈ Finset.Ioc (N / 2) N,
            (fourier (T := 1) (m : ℤ)) θ₁ * (fourier (T := 1) (P.eval (m : ℤ))) θ₂‖
        = ‖((N : ℂ))⁻¹‖ * ‖∑ m ∈ Finset.Ioc (N / 2) N,
            (fourier (T := 1) (m : ℤ)) θ₁ * (fourier (T := 1) (P.eval (m : ℤ))) θ₂‖ :=
              norm_mul _ _
      _ ≤ ((N : ℝ))⁻¹ * ((Finset.Ioc (N / 2) N).card : ℝ) := by
          rw [norm_inv, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg N))
      _ ≤ ((N : ℝ))⁻¹ * (N : ℝ) :=
          mul_le_mul_of_nonneg_left hcard (inv_nonneg.mpr (Nat.cast_nonneg N))
      _ = 1 := by rw [inv_mul_cancel₀ hN0]

private lemma periodize_varphiN_meas_bound (N k : ℕ) :
    Measurable (periodize (varphiN N k)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Circ, ‖periodize (varphiN N k) ξ‖ ≤ C := by
  set R : ℝ := (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) with hRdef
  have hR0 : 0 ≤ R := le_of_lt (by rw [hRdef]; exact Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨measurable_periodize_aux (measurable_varphiN_aux N k), ?_⟩
  refine ⟨((Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1)).card : ℝ) * 2,
    mul_nonneg (Nat.cast_nonneg _) (by norm_num), fun ξ => ?_⟩
  exact norm_periodize_le_aux hR0 (fun x hx => by
      by_contra hne
      have hs : |x| ≤ R := by rw [hRdef]; exact varphiN_support_aux N k hne
      exact absurd hs (not_le.mpr hx)) (fun x => norm_varphiN_le_two_aux N k x) ξ

private lemma periodize_varphitildeN_meas_bound (d N k : ℕ) :
    Measurable (periodize (varphitildeN d N k)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Circ, ‖periodize (varphitildeN d N k) ξ‖ ≤ C := by
  set R : ℝ := (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) with hRdef
  have hR0 : 0 ≤ R := le_of_lt (by rw [hRdef]; exact Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨measurable_periodize_aux (measurable_varphitildeN_aux d N k), ?_⟩
  refine ⟨((Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1)).card : ℝ) * 2,
    mul_nonneg (Nat.cast_nonneg _) (by norm_num), fun ξ => ?_⟩
  exact norm_periodize_le_aux hR0 (fun x hx => by
      by_contra hne
      have hs : |x| ≤ R := by rw [hRdef]; exact varphitildeN_support_aux d N k hne
      exact absurd hs (not_le.mpr hx)) (fun x => norm_varphitildeN_le_two_aux d N k x) ξ

private lemma periodize_etaCut_meas_bound (c : ℤ) :
    Measurable (periodize (etaCut Work.KMTContract.kmtEta c)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Circ, ‖periodize (etaCut Work.KMTContract.kmtEta c) ξ‖ ≤ C := by
  refine ⟨measurable_periodize_aux (contDiff_etaCut c).continuous.measurable, ?_⟩
  refine ⟨((Finset.Icc (-(⌊(2 : ℝ) ^ c⌋ + 2)) (⌊(2 : ℝ) ^ c⌋ + 1)).card : ℝ) * 1,
    mul_nonneg (Nat.cast_nonneg _) (by norm_num), fun ξ => ?_⟩
  refine norm_periodize_le_aux (C := 1) (le_of_lt (zpow_pos (by norm_num) c)) (fun x hx => ?_)
    (fun x => norm_etaCut_le_one c x) ξ
  exact etaCut_eq_zero_of_le (le_of_lt hx)

private lemma exists_bound_iwSymbol_varphiNt (ρ : ℝ) (l N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (θ : Circ),
      ‖iwSymbolSet (diffFreqs ρ l) (periodize (varphiNt N k t)) θ‖ ≤ C := by
  set R : ℝ := (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) with hRdef
  have hR0 : 0 ≤ R := le_of_lt (by rw [hRdef]; exact Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨((diffFreqs ρ l).card : ℝ) *
      (((Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1)).card : ℝ) * 2),
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (by norm_num)),
    fun t θ => ?_⟩
  refine norm_iwSymbolSet_le (diffFreqs ρ l) (fun ξ => ?_) θ
  refine norm_periodize_le_aux hR0 (fun x hx => ?_) (fun x => ?_) ξ
  · by_contra hne
    have hs : |x| ≤ R := by rw [hRdef]; exact varphiNt_support N k t x hne
    exact absurd hs (not_le.mpr hx)
  · show ‖varphiN N k x * ee ((N : ℝ) * t * x)‖ ≤ 2
    rw [norm_mul, norm_ee_aux, mul_one]
    exact norm_varphiN_le_two_aux N k x

private lemma exists_bound_iwSymbol_varphitildeNt (ρ : ℝ) (P : Polynomial ℤ) (l N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (θ : Circ),
      ‖iwSymbolSet (diffFreqs ρ l) (periodize (varphitildeNt P P.natDegree N k t)) θ‖ ≤ C := by
  set R : ℝ := (2 : ℝ) ^ ((P.natDegree : ℝ) *
    ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) with hRdef
  have hR0 : 0 ≤ R := le_of_lt (by rw [hRdef]; exact Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨((diffFreqs ρ l).card : ℝ) *
      (((Finset.Icc (-(⌊R⌋ + 2)) (⌊R⌋ + 1)).card : ℝ) * 2),
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (by norm_num)),
    fun t θ => ?_⟩
  refine norm_iwSymbolSet_le (diffFreqs ρ l) (fun ξ => ?_) θ
  refine norm_periodize_le_aux hR0 (fun x hx => ?_) (fun x => ?_) ξ
  · by_contra hne
    have hs : |x| ≤ R := by
      rw [hRdef]; exact varphitildeNt_support_all P P.natDegree N k t x hne
    exact absurd hs (not_le.mpr hx)
  · show ‖varphitildeN P.natDegree N k x * ee (PevalR P ((N : ℝ) * t) * x)‖ ≤ 2
    rw [norm_mul, norm_ee_aux, mul_one]
    exact norm_varphitildeN_le_two_aux P.natDegree N k x

private lemma measurable_arithSymb_aux (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ u : ℕ) :
    Measurable (fun p : Circ × Circ => arithSymb ρ P l₁ l₂ u p.1 p.2) := by
  have h1 : Measurable (periodize (mStarF u)) :=
    (periodize_etaCut_meas_bound (-(2 * (u : ℤ)))).1
  have h2 : Measurable (periodize (mStargF P.natDegree u)) :=
    (periodize_etaCut_meas_bound (-((P.natDegree : ℤ) * 2 * (u : ℤ)))).1
  simp only [arithSymb]
  refine Finset.measurable_sum _ fun α₁ _ => Finset.measurable_sum _ fun α₂ _ => ?_
  refine (measurable_const.mul ?_).mul ?_
  · exact h1.comp (measurable_fst.sub measurable_const)
  · exact h2.comp (measurable_snd.sub measurable_const)

private lemma exists_bound_arithSymb_aux (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ u : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ₁ θ₂ : Circ, ‖arithSymb ρ P l₁ l₂ u θ₁ θ₂‖ ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := (periodize_etaCut_meas_bound (-(2 * (u : ℤ)))).2
  obtain ⟨C₂, hC₂0, hC₂⟩ :=
    (periodize_etaCut_meas_bound (-((P.natDegree : ℤ) * 2 * (u : ℤ)))).2
  refine ⟨∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
      ‖mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂‖ * C₁ * C₂, ?_, ?_⟩
  · refine Finset.sum_nonneg fun α₁ _ => Finset.sum_nonneg fun α₂ _ => ?_
    exact mul_nonneg (mul_nonneg (norm_nonneg _) hC₁0) hC₂0
  · intro θ₁ θ₂
    simp only [arithSymb]
    calc ‖∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
          mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * periodize (mStarF u) (θ₁ - α₁)
            * periodize (mStargF P.natDegree u) (θ₂ - α₂)‖
        ≤ ∑ α₁ ∈ diffFreqs ρ l₁, ‖∑ α₂ ∈ diffFreqs ρ l₂,
          mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * periodize (mStarF u) (θ₁ - α₁)
            * periodize (mStargF P.natDegree u) (θ₂ - α₂)‖ := norm_sum_le _ _
      _ ≤ ∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
          ‖mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * periodize (mStarF u) (θ₁ - α₁)
            * periodize (mStargF P.natDegree u) (θ₂ - α₂)‖ :=
          Finset.sum_le_sum fun α₁ _ => norm_sum_le _ _
      _ ≤ ∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
          ‖mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂‖ * C₁ * C₂ := by
        refine Finset.sum_le_sum fun α₁ _ => Finset.sum_le_sum fun α₂ _ => ?_
        rw [norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hC₁ _) (norm_nonneg _)) (hC₂ _)
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) hC₁0)

private lemma measurable_concSymb_aux (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) :
    Measurable (fun p : Circ × Circ => concSymb ρ P l₁ l₂ k₁ k₂ N p.1 p.2) := by
  have h1 : Measurable (fun θ : Circ =>
      iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiN N k₁)) θ) := by
    simp only [iwSymbolSet]
    exact Finset.measurable_sum _ fun α _ =>
      (periodize_varphiN_meas_bound N k₁).1.comp (measurable_id.sub measurable_const)
  have h2 : Measurable (fun θ : Circ =>
      iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeN P.natDegree N k₂)) θ) := by
    simp only [iwSymbolSet]
    exact Finset.measurable_sum _ fun α _ =>
      (periodize_varphitildeN_meas_bound P.natDegree N k₂).1.comp
        (measurable_id.sub measurable_const)
  have h3 : Measurable (fun p : Circ × Circ => avgSymb P N p.1 p.2) :=
    measurable_avgSymb_aux P N
  simp only [concSymb]
  exact ((h1.comp measurable_fst).mul (h2.comp measurable_snd)).mul h3

private lemma exists_bound_concSymb_aux (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ₁ θ₂ : Circ,
      ‖concSymb ρ P l₁ l₂ k₁ k₂ N θ₁ θ₂‖ ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := (periodize_varphiN_meas_bound N k₁).2
  obtain ⟨C₂, hC₂0, hC₂⟩ := (periodize_varphitildeN_meas_bound P.natDegree N k₂).2
  have hb1 : ∀ θ : Circ, ‖iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiN N k₁)) θ‖
      ≤ ((diffFreqs ρ l₁).card : ℝ) * C₁ := fun θ => norm_iwSymbolSet_le _ hC₁ θ
  have hb2 : ∀ θ : Circ,
      ‖iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeN P.natDegree N k₂)) θ‖
      ≤ ((diffFreqs ρ l₂).card : ℝ) * C₂ := fun θ => norm_iwSymbolSet_le _ hC₂ θ
  have hpos1 : 0 ≤ ((diffFreqs ρ l₁).card : ℝ) * C₁ := mul_nonneg (Nat.cast_nonneg _) hC₁0
  have hpos2 : 0 ≤ ((diffFreqs ρ l₂).card : ℝ) * C₂ := mul_nonneg (Nat.cast_nonneg _) hC₂0
  refine ⟨((diffFreqs ρ l₁).card : ℝ) * C₁ * (((diffFreqs ρ l₂).card : ℝ) * C₂) * 1, ?_,
    fun θ₁ θ₂ => ?_⟩
  · exact mul_nonneg (mul_nonneg hpos1 hpos2) zero_le_one
  · simp only [concSymb]
    calc ‖iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiN N k₁)) θ₁
            * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeN P.natDegree N k₂)) θ₂
            * avgSymb P N θ₁ θ₂‖
        = ‖iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiN N k₁)) θ₁‖
            * ‖iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeN P.natDegree N k₂)) θ₂‖
            * ‖avgSymb P N θ₁ θ₂‖ := by rw [norm_mul, norm_mul]
      _ ≤ ((diffFreqs ρ l₁).card : ℝ) * C₁ * (((diffFreqs ρ l₂).card : ℝ) * C₂) * 1 :=
          mul_le_mul (mul_le_mul (hb1 θ₁) (hb2 θ₂) (norm_nonneg _) hpos1)
            (norm_avgSymb_le_one_aux P N θ₁ θ₂) (norm_nonneg _) (mul_nonneg hpos1 hpos2)

private lemma measurable_varphiNt_uncurry_aux (N k : ℕ) :
    Measurable (fun q : ℝ × ℝ => varphiNt N k q.1 q.2) := by
  have h1 : Measurable fun q : ℝ × ℝ => varphiN N k q.2 :=
    (measurable_varphiN_aux N k).comp measurable_snd
  have hee : Measurable ee := by unfold ee; fun_prop
  have h2 : Measurable fun q : ℝ × ℝ => ee ((N : ℝ) * q.1 * q.2) :=
    hee.comp ((measurable_const.mul measurable_fst).mul measurable_snd)
  show Measurable (fun q : ℝ × ℝ => varphiN N k q.2 * ee ((N : ℝ) * q.1 * q.2))
  exact h1.mul h2

private lemma measurable_integrand_modSymbC (ρ : ℝ) (P : Polynomial ℤ)
    (l₁ l₂ k₁ k₂ N : ℕ) :
    Measurable (fun q : ℝ × (Circ × Circ) =>
      arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) q.2.1 q.2.2
        * iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ q.1)) q.2.1
        * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ q.1)) q.2.2) := by
  have hA : Measurable (fun q : ℝ × (Circ × Circ) =>
      arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) q.2.1 q.2.2) :=
    (measurable_arithSymb_aux ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂))).comp measurable_snd
  have hM1 : Measurable (fun q : ℝ × (Circ × Circ) =>
      iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ q.1)) q.2.1) := by
    simp only [iwSymbolSet]
    exact Finset.measurable_sum _ fun α _ =>
      (measurable_periodize_uncurry (φ := fun t ξ => varphiNt N k₁ t ξ)
        (measurable_varphiNt_uncurry_aux N k₁)).comp
          (measurable_fst.prodMk (measurable_snd.fst.sub measurable_const))
  have hM2 : Measurable (fun q : ℝ × (Circ × Circ) =>
      iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ q.1)) q.2.2) := by
    simp only [iwSymbolSet]
    exact Finset.measurable_sum _ fun α _ =>
      (measurable_periodize_uncurry (φ := fun t ξ => varphitildeNt P P.natDegree N k₂ t ξ)
        (measurable_varphitildeNt_uncurry P N k₂)).comp
          (measurable_fst.prodMk (measurable_snd.snd.sub measurable_const))
  exact (hA.mul hM1).mul hM2

private lemma measurable_modSymbC_aux (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) :
    Measurable (fun p : Circ × Circ => modSymbC ρ P l₁ l₂ k₁ k₂ N p.1 p.2) := by
  have hjoint := measurable_integrand_modSymbC ρ P l₁ l₂ k₁ k₂ N
  have hstrong : StronglyMeasurable (fun p : Circ × Circ =>
      ∫ t, (arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) p.1 p.2
        * iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ t)) p.1
        * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ t)) p.2)
        ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) :=
    StronglyMeasurable.integral_prod_left (μ := volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))
      (f := fun (t : ℝ) (p : Circ × Circ) =>
        arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) p.1 p.2
          * iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ t)) p.1
          * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ t)) p.2)
      hjoint.stronglyMeasurable
  have hfun : (fun p : Circ × Circ => modSymbC ρ P l₁ l₂ k₁ k₂ N p.1 p.2) =
      fun p : Circ × Circ => ∫ t, (arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) p.1 p.2
        * iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ t)) p.1
        * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ t)) p.2)
        ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
    funext p
    show (∫ t in (1 / 2 : ℝ)..1,
        arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) p.1 p.2
          * iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ t)) p.1
          * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ t)) p.2)
      = ∫ t, (arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) p.1 p.2
          * iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ t)) p.1
          * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ t)) p.2)
          ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))
    rw [intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  rw [hfun]
  exact hstrong.measurable

private lemma exists_bound_modSymbC_aux (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ₁ θ₂ : Circ, ‖modSymbC ρ P l₁ l₂ k₁ k₂ N θ₁ θ₂‖ ≤ C := by
  obtain ⟨Ca, hCa0, hCa⟩ :=
    exists_bound_arithSymb_aux ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂))
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_iwSymbol_varphiNt ρ l₁ N k₁
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_bound_iwSymbol_varphitildeNt ρ P l₂ N k₂
  refine ⟨Ca * C₁ * C₂ * |(1 : ℝ) - 1 / 2|, ?_, fun θ₁ θ₂ => ?_⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg hCa0 hC₁0) hC₂0) (abs_nonneg _)
  · show ‖(∫ t in (1 / 2 : ℝ)..1,
        arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) θ₁ θ₂
          * iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ t)) θ₁
          * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ t)) θ₂)‖
      ≤ Ca * C₁ * C₂ * |1 - 1 / 2|
    exact intervalIntegral.norm_integral_le_of_norm_le_const (C := Ca * C₁ * C₂)
      (f := fun t : ℝ => arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) θ₁ θ₂
        * iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ t)) θ₁
        * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ t)) θ₂)
      (fun t _ => by
        rw [norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul (hCa θ₁ θ₂) (hC₁ t θ₁) (norm_nonneg _) hCa0)
          (hC₂ t θ₂) (norm_nonneg _) (mul_nonneg hCa0 hC₁0))

/-! ## 4. The target -/

theorem arithSymbMeasBdd (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) :
    (Measurable (fun p : Work.Analysis.IonescuWainger.Circle × Work.Analysis.IonescuWainger.Circle =>
        Work.KMTAreas.A7.concSymb ρ P l₁ l₂ k₁ k₂ N p.1 p.2) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ θ₁ θ₂ : Work.Analysis.IonescuWainger.Circle,
        ‖Work.KMTAreas.A7.concSymb ρ P l₁ l₂ k₁ k₂ N θ₁ θ₂‖ ≤ C)) ∧
    (Measurable (fun p : Work.Analysis.IonescuWainger.Circle × Work.Analysis.IonescuWainger.Circle =>
        Work.KMTAreas.A7.modSymbC ρ P l₁ l₂ k₁ k₂ N p.1 p.2) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ θ₁ θ₂ : Work.Analysis.IonescuWainger.Circle,
        ‖Work.KMTAreas.A7.modSymbC ρ P l₁ l₂ k₁ k₂ N θ₁ θ₂‖ ≤ C)) := by
  refine ⟨⟨measurable_concSymb_aux ρ P l₁ l₂ k₁ k₂ N, ?_⟩,
    ⟨measurable_modSymbC_aux ρ P l₁ l₂ k₁ k₂ N, ?_⟩⟩
  · obtain ⟨C, hC0, hC⟩ := exists_bound_concSymb_aux ρ P l₁ l₂ k₁ k₂ N
    exact ⟨C, hC0, hC⟩
  · obtain ⟨C, hC0, hC⟩ := exists_bound_modSymbC_aux ρ P l₁ l₂ k₁ k₂ N
    exact ⟨C, hC0, hC⟩

end

end Work.KMTAreas.A7
