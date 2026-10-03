/-
# The bad (non-Farey) part of the `g`-side low-pass variational estimate

`Work.KMTAreas.A7.LoGBadPartVar` is the `g`-side twin of `Work.KMTAreas.A7.LoBadPartF`: the
`ℓ^p` estimate for the variational norm of the family of *low-pass* (`l = 0`) Ionescu--Wainger
projections of the modulated `d`-fold bump,

  `n ↦ Tle ρ 0 (varphitildeNt P P.natDegree (⌊a n⌋) k₂ t) g`,

restricted to the scales `n` which are **core but not narrow** (`¬ Farey Cρc ρ l₂ k₂ a n`).  The
bound is *uniform* in the height parameters `l₁ l₂ k₁ k₂`: on the bad scales `¬ Farey` forces
`Lnat l₁ l₂ k₁ k₂ ≤ B` (`Work.KMTAreas.A7Hi.badG_Lnat_bound`), the scale `⌊a n⌋` is bounded by a
constant `X` depending only on `ρ, C₀, Cρc, B`, and the number of bad scales is at most
`K₀ = ⌈log X / log Λ + 2⌉` (`lacunary_index_bound`); each of them is controlled by the single-scale
bound `Tle_varphitildeNt_single_scale` at height `l = 0`, uniformly in the (finitely many) allowed
`N, k₂` (`Work.KMTAreas.A7Hi.badPartG_Tle_single_scale_uniform`).

This is the `Tle ρ 0` (low-pass) analogue of `Work.KMTAreas.A7Hi.lacunaryBumpBadPartBoundG`
(which is stated for `Tex ρ l₂` and needs the `ℓ^∞` bound of `g`); the proof below is the same
argument with the single-scale input at height `0`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7Hi.Gbad

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.KMTContract Work.Analysis.EndVar
open Work.KMTAreas.A7Hi

theorem LoGBadPartVar (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρC : ρ ≤ 1 / (2 * (C₀ : ℝ)))
    (Cρc : ℝ) (hCρc : 3 ≤ Cρc) (Λ : NNReal) (hΛ : 1 < Λ)
    (r : NNReal) (hr : 2 < r) (p : ENNReal) (hp : 1 < p) (htp : p < ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
      (ha1 : ∀ n, 1 ≤ a n) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
      (g : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
            ¬ Work.KMTAreas.A7.Farey Cρc ρ l₂ k₂ a n
          then Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphitildeNt P P.natDegree
            (Nat.floor (a n)) k₂ t) g x else 0))
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
  obtain ⟨Cs, hCspos, hCs⟩ := badPartG_Tle_single_scale_uniform P ρ p hp htp B Nmax
  have hCspos' : (0 : ℝ) < 2 * Cs := by linarith
  set K₀ : ℕ := Nat.ceil (Real.log X / Real.log (Λ : ℝ) + 2) with hK₀def
  have hK₀le : Real.log X / Real.log (Λ : ℝ) + 2 ≤ (K₀ : ℝ) := by
    rw [hK₀def]; exact Nat.le_ceil _
  refine ⟨4 * (2 * Cs) * (K₀ : ℝ) + 1, by positivity, ?_⟩
  intro a ha ha1 l₁ l₂ k₁ k₂ t ht g
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) hr.le
  have hp1 : (1 : ENNReal) ≤ p := le_of_lt hp
  set u : ℕ → ℤ → ℂ := fun n x =>
    if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n then
      Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0 with hudef
  have hg : (fun x : ℤ => variationalNorm r (fun n : ℕ =>
        if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n then
          Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0))
      = fun x : ℤ => variationalNorm r (fun n : ℕ => u n x) := by
    funext x
    simp only [hudef]
  rw [hg]
  by_cases hbad : ∃ n, core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey Cρc ρ l₂ k₂ a n
  · have hL : Lnat l₁ l₂ k₁ k₂ ≤ B := hB a ha ha1 l₁ l₂ k₁ k₂ hbad
    have hl₂B : l₂ ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
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
      · have hu_eq : u n = Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g := by
          funext x
          rw [hudef]
          exact if_pos hc
        rw [hu_eq]
        have hNk : Nat.floor (a n) ≤ Nmax := hNpos n hc
        refine (hCs 0 (Nat.zero_le B) (Nat.floor (a n)) k₂ hNk hk₂B t ht g).trans ?_
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le
        linarith
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

end Work.KMTAreas.A7
