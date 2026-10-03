import Mathlib
import Submission.Work.KMTAreas.A7.BadPartBound
import Submission.Work.KMTAreas.A7Hi.Gblock
import Submission.Work.KMTAreas.A7Hi.Gsingle

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7Hi

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.KMTContract Work.Analysis.EndVar
open Work.KMTAreas.A7

/-! ## §1.  The coarse (non-Farey) part of the `g`-side linear estimate -/

/-- **The multi-index is bounded on the `g`-side bad scales.**  (This is the `g`-side analogue of
`Work.KMTAreas.A7.exists_Lnat_le_of_bad`, whose proof is copied here with the Farey predicate
`Farey Cρc ρ l₁ k₁` replaced by the `g`-side one `Farey Cρc ρ l₂ k₂`.) -/
theorem badG_Lnat_bound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hρC : ρ ≤ 1 / (2 * (C₀ : ℝ))) (Cρc : ℝ) (hCρc : 3 ≤ Cρc) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ B : ℕ, ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
      (l₁ l₂ k₁ k₂ : ℕ),
      (∃ n, core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n) →
      Lnat l₁ l₂ k₁ k₂ ≤ B := by
  obtain ⟨M₀, hM₀⟩ := exists_sqrt_logb_lt Cρc (C₀ : ℝ)
  have hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 2 := by
    have hC₀pos : (0 : ℝ) < (C₀ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC₀)
    have h2 : (0 : ℝ) < 2 * (C₀ : ℝ) := by linarith
    have h := (le_div_iff₀ h2).mp hρC
    linarith
  refine ⟨Nat.ceil (C₀ * Real.logb 2 ((M₀ : ℝ) + 2)), ?_⟩
  intro a ha ha1 l₁ l₂ k₁ k₂ hbad
  obtain ⟨n, hn⟩ := hbad
  set N : ℕ := Nat.floor (a n) with hNdef
  set M : ℕ := Nat.log 2 (max N 2) with hMdef
  obtain ⟨hin, hcut, hmain⟩ := hn.1
  obtain ⟨hlmax, hk₁, hk₂⟩ := hin
  have hLle : Lnat l₁ l₂ k₁ k₂ ≤ heightScale C₀ N := by
    have h1 : l₁ ≤ heightScale C₀ N := by exact_mod_cast (le_trans (le_max_left _ _) hlmax)
    have h2 : l₂ ≤ heightScale C₀ N := by exact_mod_cast (le_trans (le_max_right _ _) hlmax)
    have h3 : k₁ ≤ heightScale C₀ N := by exact_mod_cast hk₁
    have h4 : k₂ ≤ heightScale C₀ N := by exact_mod_cast hk₂
    exact max_le (max_le h1 h2) (max_le h3 h4)
  have hlogN : logN N = (M : ℤ) := by simp only [logN, hMdef]
  have hnotF : fareyK Cρc ρ l₂ < (k₂ : ℤ) - logN N := by
    have h : ¬ ((k₂ : ℤ) - logN N ≤ fareyK Cρc ρ l₂) := by simpa only [Farey] using hn.2
    exact not_le.mp h
  have hfloor : -(Cρc * (2 : ℝ) ^ (ρ * (l₂ : ℝ))) - 1
      < ((fareyK Cρc ρ l₂ : ℤ) : ℝ) := by
    have h := Int.lt_floor_add_one (-(Cρc * (2 : ℝ) ^ (ρ * (l₂ : ℝ))))
    simp only [fareyK]
    linarith
  have hcast : ((fareyK Cρc ρ l₂ : ℤ) : ℝ) < (k₂ : ℝ) - (M : ℝ) := by
    have h := hnotF
    rw [hlogN] at h
    exact_mod_cast h
  have hM_lt : (M : ℝ) < Cρc * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) + 1 + (k₂ : ℝ) := by linarith
  have hl₂h : (l₂ : ℝ) ≤ (heightScale C₀ N : ℝ) := by
    exact_mod_cast (le_trans (le_max_right _ _) hlmax)
  have hk₂h : (k₂ : ℝ) ≤ (heightScale C₀ N : ℝ) := by exact_mod_cast hk₂
  have hrpow_mono : (2 : ℝ) ^ (ρ * (l₂ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (heightScale C₀ N : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hρ, hl₂h])
  have hrpow_h : (2 : ℝ) ^ (ρ * (heightScale C₀ N : ℝ)) ≤ Real.sqrt ((M : ℝ) + 2) := by
    have h := two_rpow_heightScale_le_sqrt hρ hρC₀ N
    rw [← hMdef] at h
    exact h
  have hsqrt : Cρc * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) ≤ Cρc * Real.sqrt ((M : ℝ) + 2) :=
    mul_le_mul_of_nonneg_left (hrpow_mono.trans hrpow_h) (by linarith)
  have hlogLog : ((logLogN N : ℕ) : ℝ) ≤ Real.logb 2 ((M : ℝ) + 2) := by
    have h1 : logLogN N = Nat.log 2 (M + 2) := by simp only [logLogN, hMdef]
    rw [h1]
    exact elb_natlog_add_two_le_logb M
  have hk₂_le : (k₂ : ℝ) ≤ (C₀ : ℝ) * Real.logb 2 ((M : ℝ) + 2) := by
    have hh : ((heightScale C₀ N : ℕ) : ℝ) = (C₀ : ℝ) * ((logLogN N : ℕ) : ℝ) := by
      simp only [heightScale, Nat.cast_mul]
    calc (k₂ : ℝ) ≤ (heightScale C₀ N : ℝ) := hk₂h
      _ = (C₀ : ℝ) * ((logLogN N : ℕ) : ℝ) := hh
      _ ≤ (C₀ : ℝ) * Real.logb 2 ((M : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hlogLog (by positivity)
  have hMbound : (M : ℝ) < Cρc * Real.sqrt ((M : ℝ) + 2)
      + (C₀ : ℝ) * Real.logb 2 ((M : ℝ) + 2) + 1 := by linarith
  have hMlt : M < M₀ := by
    by_contra hcon
    push Not at hcon
    have h := hM₀ M hcon
    linarith
  have hfin : ((Lnat l₁ l₂ k₁ k₂ : ℕ) : ℝ)
      ≤ (Nat.ceil (C₀ * Real.logb 2 ((M₀ : ℝ) + 2)) : ℝ) := by
    have h1 : ((Lnat l₁ l₂ k₁ k₂ : ℕ) : ℝ) ≤ ((heightScale C₀ N : ℕ) : ℝ) := by
      exact_mod_cast hLle
    have h2 : ((heightScale C₀ N : ℕ) : ℝ) ≤ (C₀ : ℝ) * Real.logb 2 ((M : ℝ) + 2) := by
      have hh : ((heightScale C₀ N : ℕ) : ℝ) = (C₀ : ℝ) * ((logLogN N : ℕ) : ℝ) := by
        simp only [heightScale, Nat.cast_mul]
      rw [hh]
      exact mul_le_mul_of_nonneg_left hlogLog (by positivity)
    have h3 : (M : ℝ) + 2 ≤ (M₀ : ℝ) + 2 := by
      have : (M : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast (le_of_lt hMlt)
      linarith
    have h4 : Real.logb 2 ((M : ℝ) + 2) ≤ Real.logb 2 ((M₀ : ℝ) + 2) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) h3
    have h6 : (C₀ : ℝ) * Real.logb 2 ((M : ℝ) + 2)
        ≤ (C₀ : ℝ) * Real.logb 2 ((M₀ : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have h5 : (C₀ : ℝ) * Real.logb 2 ((M₀ : ℝ) + 2)
        ≤ (Nat.ceil (C₀ * Real.logb 2 ((M₀ : ℝ) + 2)) : ℝ) := Nat.le_ceil _
    linarith
  exact_mod_cast hfin

/-- On the core scales the `g`-side height satisfies `2 ^ k₂ ≤ ⌊a n⌋`. -/
theorem badPartG_two_pow_le_floor_of_core {ρ : ℝ} {C₀ : ℕ} {l₁ l₂ k₁ k₂ : ℕ} {a : ℕ → NNReal}
    {n : ℕ} (h : core ρ C₀ l₁ l₂ k₁ k₂ a n) : 2 ^ k₂ ≤ Nat.floor (a n) := by
  obtain ⟨hin, hcut, hmain⟩ := h
  have hN : 2 < Nat.floor (a n) := lt_of_le_of_lt (badPart_two_le_splitCut ρ _) hcut
  have hk : k₂ ≤ (logN (Nat.floor (a n))).toNat := le_trans (Nat.le_add_right k₂ _) hmain.2
  have hlog : (logN (Nat.floor (a n))).toNat = Nat.log 2 (max (Nat.floor (a n)) 2) := by
    simp [logN]
  have hne : max (Nat.floor (a n)) 2 ≠ 0 := by
    have : 2 ≤ max (Nat.floor (a n)) 2 := le_max_right _ _
    omega
  have hpow : 2 ^ Nat.log 2 (max (Nat.floor (a n)) 2) ≤ max (Nat.floor (a n)) 2 :=
    Nat.pow_log_le_self 2 hne
  have hmax : max (Nat.floor (a n)) 2 = Nat.floor (a n) := max_eq_left (le_of_lt hN)
  calc 2 ^ k₂ ≤ 2 ^ (logN (Nat.floor (a n))).toNat :=
        pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hk
    _ = 2 ^ Nat.log 2 (max (Nat.floor (a n)) 2) := by rw [hlog]
    _ ≤ max (Nat.floor (a n)) 2 := hpow
    _ = Nat.floor (a n) := hmax

/-- The modulated `d`-fold bump is `C²`. -/
lemma contDiff2_varphitildeNt_g (P : Polynomial ℤ) (d N k₂ : ℕ) (t : ℝ) :
    ContDiff ℝ 2 (varphitildeNt P d N k₂ t) := by
  rw [show varphitildeNt P d N k₂ t
      = fun ξ : ℝ => varphitildeN d N k₂ ξ * ee (PevalR P ((N : ℝ) * t) * ξ) from rfl]
  exact (contDiff_varphitildeN d N k₂).mul (contDiff_ee_const_mul 2 _)

/-- The single-scale bound for `Tle ρ l (φ̃_{N,t})` is uniform over `l ≤ B`, `N ≤ Nmax` and
`k₂ ≤ B`. -/
theorem badPartG_Tle_single_scale_uniform (P : Polynomial ℤ) (ρ : ℝ) (p : ENNReal) (hp : 1 < p)
    (hptop : p < ⊤) (B Nmax : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l : ℕ), l ≤ B → ∀ (N k₂ : ℕ), N ≤ Nmax → k₂ ≤ B → ∀ (t : ℝ),
      t ∈ Set.Icc (1 / 2 : ℝ) 1 → ∀ g : ℤ → ℂ,
      MeasureTheory.eLpNorm (Tle ρ l (varphitildeNt P P.natDegree N k₂ t) g) p
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal C *
            MeasureTheory.eLpNorm g p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  choose Cl hCl using fun l : ℕ => Tle_varphitildeNt_single_scale P ρ l p hp hptop
  set box : Finset (ℕ × (ℕ × ℕ)) :=
    (Finset.range (B + 1)).product
      ((Finset.range (Nmax + 1)).product (Finset.range (B + 1))) with hbox
  have hboxnn : ∀ t ∈ box, (0 : ℝ) ≤ Cl t.1 t.2.1 t.2.2 :=
    fun t _ => le_of_lt ((hCl t.1).1 t.2.1 t.2.2)
  refine ⟨(∑ t ∈ box, Cl t.1 t.2.1 t.2.2) + 1, by
    have := Finset.sum_nonneg hboxnn
    linarith, ?_⟩
  intro l hl N k₂ hN hk t ht g
  have hl' : l < B + 1 := by omega
  have hN' : N < Nmax + 1 := by omega
  have hk' : k₂ < B + 1 := by omega
  have hmem : (l, (N, k₂)) ∈ box := by
    rw [hbox]
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hl',
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr hN', Finset.mem_range.mpr hk'⟩⟩
  have hle : Cl l N k₂ ≤ ∑ t ∈ box, Cl t.1 t.2.1 t.2.2 :=
    Finset.single_le_sum hboxnn hmem
  refine ((hCl l).2 N k₂ t ht g).trans ?_
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
  linarith

/-- **The bad (coarse, non-narrow) part of the `g`-side linear lacunary variational estimate.** -/
theorem lacunaryBumpBadPartBoundG (P : Polynomial ℤ) (d : ℕ) (hd : 2 ≤ d) (hdP : P.natDegree ≤ d)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hρC : ρ ≤ 1 / (2 * (C₀ : ℝ))) (Cρc : ℝ) (hCρc : 3 ≤ Cρc) (Λ : NNReal) (hΛ : 1 < Λ)
    (r : NNReal) (hr : 2 < r) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
      (ha1 : ∀ n, 1 ≤ a n) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
      (g : ℤ → ℂ) (Bg : ℝ) (hBg : ∀ m : ℤ, ‖g m‖ ≤ Bg),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n
          then Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
  classical
  obtain ⟨B, hB⟩ := badG_Lnat_bound ρ hρ hρ1 C₀ hC₀ hρC Cρc hCρc Λ hΛ
  set X : ℝ := (2 : ℝ) ^ ((B : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) + 2) + 1 with hXdef
  have hX1 : (1 : ℝ) ≤ X := by
    have h1 : (0 : ℝ) < (2 : ℝ) ^ ((B : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) + 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rw [hXdef]; linarith
  set Nmax : ℕ := Nat.ceil X with hNmaxdef
  have hNleX : ∀ N : ℕ, (N : ℝ) < X → N ≤ Nmax := by
    intro N hN
    rw [hNmaxdef]
    exact_mod_cast (le_trans (le_of_lt hN) (Nat.le_ceil X))
  obtain ⟨Cs, hCspos, hCs⟩ := badPartG_Tle_single_scale_uniform P ρ p hp hptop B Nmax
  have hCspos' : (0 : ℝ) < 2 * Cs := by linarith
  set K₀ : ℕ := Nat.ceil (Real.log X / Real.log (Λ : ℝ) + 2) with hK₀def
  have hK₀le : Real.log X / Real.log (Λ : ℝ) + 2 ≤ (K₀ : ℝ) := by
    rw [hK₀def]; exact Nat.le_ceil _
  refine ⟨4 * (2 * Cs) * (K₀ : ℝ) + 1, by positivity, ?_⟩
  intro a ha ha1 l₁ l₂ k₁ k₂ t ht g Bg hBg
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) hr.le
  have hp1 : (1 : ENNReal) ≤ p := le_of_lt hp
  set u : ℕ → ℤ → ℂ := fun n x =>
    if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n then
      Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0 with hudef
  have hg : (fun x : ℤ => variationalNorm r (fun n : ℕ =>
        if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n then
          Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0))
      = fun x : ℤ => variationalNorm r (fun n : ℕ => u n x) := by
    funext x
    simp only [hudef]
  rw [hg]
  by_cases hbad : ∃ n, core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n
  · have hL : Lnat l₁ l₂ k₁ k₂ ≤ B := hB a ha ha1 l₁ l₂ k₁ k₂ hbad
    have hl₂B : l₂ ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
    have hl₂B' : l₂ - 1 ≤ B := by omega
    have hk₂B : k₂ ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
    -- the value of the scale at a bad index is bounded by `X`
    have hltX : ∀ n : ℕ, (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n) →
        (Nat.floor (a n) : ℝ) + 1 < X := by
      intro n hn
      obtain ⟨⟨hin, hcut, _⟩, hnf⟩ := hn
      obtain ⟨hlmax, hk₁c, hk₂c⟩ := hin
      have hfarey : fareyK Cρc ρ l₂ < (k₂ : ℤ) - logN (Nat.floor (a n)) :=
        not_le.mp (by simpa only [Farey] using hnf)
      have hfloor : -(Cρc * (2 : ℝ) ^ (ρ * (l₂ : ℝ))) - 1
          < ((fareyK Cρc ρ l₂ : ℤ) : ℝ) := by
        have h := Int.lt_floor_add_one (-(Cρc * (2 : ℝ) ^ (ρ * (l₂ : ℝ))))
        simp only [fareyK]
        linarith
      have hcast : ((fareyK Cρc ρ l₂ : ℤ) : ℝ)
          < (k₂ : ℝ) - (logN (Nat.floor (a n)) : ℝ) := by exact_mod_cast hfarey
      have hMlt : (logN (Nat.floor (a n)) : ℝ)
          < (k₂ : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) + 1 := by linarith
      have hrpow : (2 : ℝ) ^ (ρ * (l₂ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (B : ℝ)) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have h1 : (l₂ : ℝ) ≤ (B : ℝ) := by exact_mod_cast hl₂B
        nlinarith [hρ]
      have h2 : Cρc * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) ≤ Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) :=
        mul_le_mul_of_nonneg_left hrpow (by linarith)
      have hexp : (logN (Nat.floor (a n)) : ℝ) + 1
          < (B : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) + 2 := by
        have h1 : (k₂ : ℝ) ≤ (B : ℝ) := by exact_mod_cast hk₂B
        linarith
      have hfloor_le : Nat.floor (a n) < 2 ^ ((logN (Nat.floor (a n))).toNat + 1) := by
        rcases Nat.eq_zero_or_pos (Nat.floor (a n)) with h | h
        · rw [h]; exact Nat.one_le_two_pow
        · have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num)
            (max (Nat.floor (a n)) 2)
          rw [show Nat.log 2 (max (Nat.floor (a n)) 2)
              = (logN (Nat.floor (a n))).toNat from by simp [logN]] at h2
          exact lt_of_le_of_lt (le_max_left _ _) h2
      have hcast2 : (Nat.floor (a n) : ℝ)
          < (2 : ℝ) ^ (((logN (Nat.floor (a n))).toNat : ℝ) + 1) := by
        have h : ((Nat.floor (a n) : ℕ) : ℝ)
            < (((2 : ℕ) ^ ((logN (Nat.floor (a n))).toNat + 1) : ℕ) : ℝ) := by
          exact_mod_cast hfloor_le
        rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast] at h
        rw [show (((logN (Nat.floor (a n))).toNat + 1 : ℕ) : ℝ)
            = ((logN (Nat.floor (a n))).toNat : ℝ) + 1 by push_cast; ring] at h
        exact h
      have hexp2 : ((logN (Nat.floor (a n))).toNat : ℝ) + 1
          ≤ (B : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) + 2 := by
        have h1 : ((logN (Nat.floor (a n))).toNat : ℝ) ≤ (logN (Nat.floor (a n)) : ℝ) := by
          have h2 : (0 : ℤ) ≤ logN (Nat.floor (a n)) := Int.natCast_nonneg _
          have h3 : ((logN (Nat.floor (a n))).toNat : ℤ) ≤ logN (Nat.floor (a n)) := by
            rw [Int.toNat_of_nonneg h2]
          exact_mod_cast h3
        linarith
      have h3 : (2 : ℝ) ^ (((logN (Nat.floor (a n))).toNat : ℝ) + 1)
          ≤ (2 : ℝ) ^ ((B : ℝ) + Cρc * (2 : ℝ) ^ (ρ * (B : ℝ)) + 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp2
      have hfin : (Nat.floor (a n) : ℝ) + 1 < X := by
        rw [hXdef]
        linarith [lt_of_lt_of_le hcast2 h3]
      exact hfin
    have hmem : ∀ n : ℕ, (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n) → n < K₀ := by
      intro n hn
      obtain ⟨K, hKle, hKbd⟩ := lacunary_index_bound Λ hΛ a ha ha1 X hX1
      have haX : (a n : ℝ) < X := by
        have hlt : (a n : ℝ) < (Nat.floor (a n) : ℝ) + 1 := Nat.lt_floor_add_one _
        linarith [hltX n hn, hlt]
      have hKK₀ : K ≤ K₀ := by exact_mod_cast (le_trans hKle hK₀le)
      exact lt_of_lt_of_le (hKbd n haX) hKK₀
    have hsupp : ∀ n, n ∉ Finset.range K₀ → u n = 0 := by
      intro n hn
      funext x
      simp only [hudef, Pi.zero_apply]
      by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n
      · exact absurd hc (fun hc' => hn (Finset.mem_range.mpr (hmem n hc')))
      · rw [if_neg hc]
    have hNpos : ∀ n : ℕ, (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n) →
        Nat.floor (a n) ≤ Nmax := fun n hn => hNleX _ (by linarith [hltX n hn])
    have hscale : ∀ n ∈ Finset.range K₀, MeasureTheory.eLpNorm (fun x : ℤ => u n x) p
        (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal (2 * Cs) *
            MeasureTheory.eLpNorm g p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
      intro n hn
      by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n
      · have hu_eq : u n = Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g := by
          funext x
          rw [hudef]
          exact if_pos hc
        rw [hu_eq]
        have hNk : Nat.floor (a n) ≤ Nmax := hNpos n hc
        have hAdm : Adm (iwArithFreqs ρ l₂)
            (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) :=
          adm_of_bump (contDiff2_varphitildeNt_g P P.natDegree _ k₂ t)
            (hasCompactSupport_varphitildeNt_g P P.natDegree _ k₂ t)
        have hAdm' : Adm (iwArithFreqs ρ (l₂ - 1))
            (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) :=
          adm_of_bump (contDiff2_varphitildeNt_g P P.natDegree _ k₂ t)
            (hasCompactSupport_varphitildeNt_g P P.natDegree _ k₂ t)
        rw [badPart_Tex_eq_Tle_sub ρ hρ hρ1 l₂ hAdm hAdm' hBg]
        have hA : MeasureTheory.eLpNorm (Tle ρ l₂
              (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) p
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
            ≤ ENNReal.ofReal Cs *
                MeasureTheory.eLpNorm g p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) :=
          hCs l₂ hl₂B (Nat.floor (a n)) k₂ hNk hk₂B t ht g
        have hB' : MeasureTheory.eLpNorm (Tle ρ (l₂ - 1)
              (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) p
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
            ≤ ENNReal.ofReal Cs *
                MeasureTheory.eLpNorm g p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) :=
          hCs (l₂ - 1) hl₂B' (Nat.floor (a n)) k₂ hNk hk₂B t ht g
        have hsub : MeasureTheory.eLpNorm (Tle ρ l₂
                (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g
              - Tle ρ (l₂ - 1)
                (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) p
              (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
            ≤ MeasureTheory.eLpNorm (Tle ρ l₂
                  (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) p
                (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
              + MeasureTheory.eLpNorm (Tle ρ (l₂ - 1)
                  (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) p
                (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
          rw [sub_eq_add_neg]
          refine (MeasureTheory.eLpNorm_add_le hp1).trans (le_of_eq ?_)
          rw [MeasureTheory.eLpNorm_neg]
        calc MeasureTheory.eLpNorm (Tle ρ l₂
                (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g
              - Tle ρ (l₂ - 1)
                (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) p
              (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
            ≤ MeasureTheory.eLpNorm (Tle ρ l₂
                  (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) p
                (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
              + MeasureTheory.eLpNorm (Tle ρ (l₂ - 1)
                  (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) p
                (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := hsub
          _ ≤ ENNReal.ofReal Cs *
                MeasureTheory.eLpNorm g p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
              + ENNReal.ofReal Cs *
                MeasureTheory.eLpNorm g p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) :=
              add_le_add hA hB'
          _ = ENNReal.ofReal (2 * Cs) *
                MeasureTheory.eLpNorm g p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
              rw [← add_mul, ← ENNReal.ofReal_add (by linarith) (by linarith)]
              congr 1
              ring
      · have hu_eq : u n = 0 := by
          funext x
          simp only [hudef]
          exact if_neg hc
        rw [hu_eq, MeasureTheory.eLpNorm_zero]
        exact bot_le
    have h1 := eLpNorm_variationalNorm_le_sum (r := r) (p := p)
      (μ := MeasureTheory.Measure.count) hr1 hp1 (u := u) (s := Finset.range K₀) hsupp
      (fun n _ => (measurable_of_countable (u n)).aestronglyMeasurable)
    refine h1.trans ?_
    have hsum : (∑ n ∈ Finset.range K₀, (4 : ENNReal) * MeasureTheory.eLpNorm (fun x : ℤ => u n x)
          p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ))
        ≤ ∑ _n ∈ Finset.range K₀, (4 : ENNReal) * (ENNReal.ofReal (2 * Cs) *
            MeasureTheory.eLpNorm g p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)) :=
      Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hscale n hn) bot_le
    refine hsum.trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hcard' : ((K₀ : ℕ) : ENNReal) ≤ ENNReal.ofReal (K₀ : ℝ) := by
      rw [ENNReal.ofReal_natCast]
    have hfin : ENNReal.ofReal (K₀ : ℝ) * ((4 : ENNReal) *
          (ENNReal.ofReal (2 * Cs) *
            MeasureTheory.eLpNorm g p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)))
        ≤ ENNReal.ofReal (4 * (2 * Cs) * (K₀ : ℝ) + 1) *
            MeasureTheory.eLpNorm g p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
      have hK₀0 : (0 : ℝ) ≤ (K₀ : ℝ) := Nat.cast_nonneg _
      have hCs2 : (0 : ℝ) ≤ 2 * Cs := le_of_lt hCspos'
      have h4 : ENNReal.ofReal (K₀ : ℝ) * ((4 : ENNReal) * ENNReal.ofReal (2 * Cs))
          = ENNReal.ofReal ((K₀ : ℝ) * (4 * (2 * Cs))) := by
        rw [show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),
          ← ENNReal.ofReal_mul hK₀0]
      rw [show ENNReal.ofReal (K₀ : ℝ) * ((4 : ENNReal) *
            (ENNReal.ofReal (2 * Cs) *
              MeasureTheory.eLpNorm g p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)))
          = (ENNReal.ofReal (K₀ : ℝ) * ((4 : ENNReal) * ENNReal.ofReal (2 * Cs))) *
              MeasureTheory.eLpNorm g p (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) by
        ring,
        h4]
      refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
      nlinarith [hK₀0, hCs2]
    refine (mul_le_mul_of_nonneg_right hcard' bot_le).trans ?_
    refine le_trans (le_of_eq (by ring)) hfin
  · have hzero : (fun x : ℤ => variationalNorm r (fun n : ℕ => u n x)) = fun _ : ℤ => 0 := by
      funext x
      have hz : (fun n : ℕ => u n x) = fun _ : ℕ => (0 : ℂ) := by
        funext n
        simp only [hudef]
        exact if_neg (fun hc => hbad ⟨n, hc⟩)
      rw [hz]
      exact badPart_variationalNorm_zero r hr1
    rw [hzero, badPart_eLpNorm_zero_fun]
    exact bot_le

end

end Work.KMTAreas.A7Hi
